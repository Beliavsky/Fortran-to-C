#!/usr/bin/env python3
"""xf2c_driver.py: CLI/build driver for xf2c."""

from __future__ import annotations

import argparse
import glob
import importlib.util
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import fortran_scan as fscan
from xc_post import postprocess_c_text

from xf2c_core import transpile_fortran_to_c

REPO_ROOT = Path(__file__).resolve().parent
RUNTIME_C_PATH = REPO_ROOT / "fortran_runtime.c"
XNORMALIZE_CANDIDATES = [
    REPO_ROOT / "xnormalize.py",
    Path(r"c:\python\code\xnormalize.py"),
]
INTRINSIC_MODULES = {
    "iso_fortran_env",
    "iso_c_binding",
    "ieee_arithmetic",
    "ieee_exceptions",
    "ieee_features",
}


def _load_normalize_text():
    for path in XNORMALIZE_CANDIDATES:
        if not path.exists():
            continue
        spec = importlib.util.spec_from_file_location("xnormalize_local", path)
        if spec is None or spec.loader is None:
            continue
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        normalize = getattr(mod, "normalize_text", None)
        if normalize is not None:
            return normalize
    return None


_NORMALIZE_TEXT = _load_normalize_text()


def _embed_runtime_c(c_src: str) -> str:
    include_line = '#include "fortran_runtime.h"'
    if include_line not in c_src:
        return c_src
    runtime_src = RUNTIME_C_PATH.read_text(encoding="utf-8", errors="replace")
    runtime_lines = []
    for ln in runtime_src.splitlines():
        if ln.strip() == '#include "fortran_runtime.h"':
            continue
        runtime_lines.append(ln)
    runtime_src = "\n".join(runtime_lines).strip()
    lines = c_src.splitlines(keepends=True)
    insert_at = 0
    while insert_at < len(lines) and lines[insert_at].startswith("#include"):
        insert_at += 1
    while insert_at < len(lines) and lines[insert_at].strip() == "":
        insert_at += 1
    filtered = [ln for ln in lines if ln.strip() != include_line]
    runtime_block = runtime_src.rstrip() + "\n\n"
    filtered.insert(insert_at, runtime_block)
    return "".join(filtered)


def _print_summary_table(rows: List[Dict[str, object]]) -> None:
    if not rows:
        print("No files processed.")
        return

    def _btxt(v: object) -> str:
        if v is True:
            return "True"
        if v is False:
            return "False"
        return ""

    headers = ["source", "c_source", "compile_f90", "compile_c"]
    rendered: List[List[str]] = []
    for r in rows:
        rendered.append([
            str(r.get("source", "")),
            str(r.get("c_source", "")),
            _btxt(r.get("compile_f90")),
            _btxt(r.get("compile_c")),
        ])

    widths = [len(h) for h in headers]
    for vals in rendered:
        for i, v in enumerate(vals):
            if len(v) > widths[i]:
                widths[i] = len(v)

    print("")
    print("--summary:")
    print("  ".join(h.ljust(widths[i]) for i, h in enumerate(headers)))
    for vals in rendered:
        print("  ".join(vals[i].ljust(widths[i]) for i in range(len(headers))))


def _header_guard_for(path: Path) -> str:
    safe = re.sub(r"[^A-Za-z0-9]+", "_", path.name).upper().strip("_")
    return f"{safe}_INCLUDED" if safe else "XF2C_GENERATED_H_INCLUDED"


def _extract_public_prototypes(c_src: str) -> List[str]:
    protos: List[str] = []
    for ln in c_src.splitlines():
        s = ln.strip()
        if not s or s.startswith("#") or s.startswith("static "):
            continue
        if ";" not in s:
            continue
        if "(" not in s or ")" not in s:
            continue
        if re.match(r"^(?:return|if|while|for|switch)\b", s):
            continue
        if "=" in s and "(*" not in s:
            continue
        if "{" in s or "}" in s:
            continue
        if re.match(r"^[A-Za-z_][A-Za-z0-9_\s\*]*\s+\**[A-Za-z_]\w*\s*\([^;]*\)\s*;(?:\s*/\*.*\*/)?$", s):
            protos.append(s)
    return protos


def _build_header_text(c_src: str, header_name: str) -> str:
    protos = _extract_public_prototypes(c_src)
    if not protos:
        return ""
    guard = _header_guard_for(Path(header_name))
    lines = [
        f"#ifndef {guard}",
        f"#define {guard}",
        "",
    ]
    lines.extend(protos)
    lines.extend(
        [
            "",
            f"#endif /* {guard} */",
            "",
        ]
    )
    return "\n".join(lines)


def _extract_used_modules(src_text: str) -> List[str]:
    mods: List[str] = []
    seen: Set[str] = set()
    for raw in src_text.splitlines():
        code = raw.split("!", 1)[0].strip()
        if not code:
            continue
        m = re.match(r"(?i)^use\s*(?:,\s*intrinsic\s*)?(?:::)?\s*([a-z_]\w*)", code)
        if not m:
            continue
        mod = m.group(1).lower()
        if mod in INTRINSIC_MODULES or mod in seen:
            continue
        seen.add(mod)
        mods.append(mod)
    return mods


def _module_names_in_text(text: str) -> Set[str]:
    names: Set[str] = set()
    for raw in text.splitlines():
        code = raw.split("!", 1)[0].strip().lower()
        m = re.match(r"^module\s+([a-z_]\w*)\b", code)
        if m and not code.startswith("module procedure"):
            names.add(m.group(1))
    return names


def _module_names_in_file(path: Path) -> Set[str]:
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return set()
    return _module_names_in_text(text)


def _find_module_source(module_name: str, search_roots: List[Path], cache: Dict[str, Optional[Path]]) -> Optional[Path]:
    key = module_name.lower()
    if key in cache:
        return cache[key]
    for root in search_roots:
        if not root.exists():
            continue
        for path in root.glob("*.f90"):
            if key in _module_names_in_file(path):
                cache[key] = path
                return path
    cache[key] = None
    return None


def _resolve_fortran_support_sources(src_path: Path, src_text: str) -> List[Path]:
    search_roots = [src_path.parent, REPO_ROOT]
    cache: Dict[str, Optional[Path]] = {}
    ordered: List[Path] = []
    seen_files: Set[str] = set()

    def visit(path: Path, text: str) -> None:
        local_modules = _module_names_in_text(text)
        for mod in _extract_used_modules(text):
            if mod in local_modules:
                continue
            dep = _find_module_source(mod, search_roots, cache)
            if dep is None:
                continue
            dep_key = str(dep.resolve()).lower()
            src_key = str(src_path.resolve()).lower()
            if dep_key == src_key or dep_key in seen_files:
                continue
            seen_files.add(dep_key)
            dep_text = dep.read_text(encoding="utf-8", errors="ignore")
            visit(dep, dep_text)
            ordered.append(dep)

    visit(src_path, src_text)
    return ordered


def _selected_c_compiler(args: argparse.Namespace) -> str:
    if getattr(args, "msvc", False):
        return "msvc"
    if getattr(args, "clang", False):
        return "clang"
    return "gcc"


def _c_obj_path_for(out_path: Path, compiler: str) -> Path:
    return out_path.with_suffix(".obj" if compiler == "msvc" else ".o")


def _build_c_command(
    compiler: str,
    repo_root: Path,
    runtime_c_path: Path,
    out_path: Path,
    single_file: bool,
    has_program_unit: bool,
    compile_only: bool,
) -> Tuple[List[str], Optional[Path]]:
    if compiler == "msvc":
        include_flag = f"/I{repo_root}"
        if has_program_unit and not compile_only:
            exe = out_path.with_suffix(".exe")
            cmd = ["cl", "/nologo", include_flag, str(out_path)]
            if not single_file:
                cmd.append(str(runtime_c_path))
            cmd.append(f"/Fe:{exe}")
            return cmd, exe
        obj = _c_obj_path_for(out_path, compiler)
        return ["cl", "/nologo", include_flag, "/c", str(out_path), f"/Fo:{obj}"], None

    cc = "clang" if compiler == "clang" else "gcc"
    if has_program_unit and not compile_only:
        exe = out_path.with_suffix(".exe")
        cmd = [cc, "-I", str(repo_root), str(out_path), "-lm", "-o", str(exe)]
        if not single_file:
            cmd.insert(-2, str(runtime_c_path))
        return cmd, exe
    obj = _c_obj_path_for(out_path, compiler)
    return [cc, "-I", str(repo_root), "-c", str(out_path), "-o", str(obj)], None


def main() -> int:
    ap = argparse.ArgumentParser(description="Small Fortran-to-C transpiler.")
    ap.add_argument("fortran_files", nargs="+", help="Input free-form Fortran source file(s) or glob pattern(s).")
    ap.add_argument("--out", default="", help="Output C file (default: temp_<stem>.c).")
    ap.add_argument("--out-dir", default="", help="Output directory used with --mode-each.")
    ap.add_argument("--tee", action="store_true", help="Print generated C source.")
    ap.add_argument("--compile", action="store_true", help="Compile generated C source (no run).")
    ap.add_argument("--compile-c", action="store_true", help="Compile generated C source with -c only (no link).")
    ap.add_argument("--run", action="store_true", help="Compile/run generated C source.")
    ap.add_argument("--run-both", action="store_true", help="Build/run original Fortran source and generated C source.")
    ap.add_argument("--compile-both", action="store_true", help="Build (without running) original Fortran source and generated C source.")
    ap.add_argument("--compile-both-c", action="store_true", help="Compile original Fortran and generated C with -c only (no link).")
    ap.add_argument("--one-line", action="store_true", help="Collapse simple one-statement for/if blocks to one line.")
    ap.add_argument("--annotate", action="store_true", help="Insert C comments with original Fortran statements before translated code.")
    pp_group = ap.add_mutually_exclusive_group()
    pp_group.add_argument("--postprocess", action="store_true", help="Run conservative C readability cleanup before writing/compiling (default behavior).")
    pp_group.add_argument("--raw", action="store_true", help="Write raw transpiler output without C postprocessing.")
    ap.add_argument("--single-file", action="store_true", help="Embed the shared runtime into the generated C file.")
    cc_group = ap.add_mutually_exclusive_group()
    cc_group.add_argument("--clang", action="store_true", help="Compile generated C with clang instead of gcc.")
    cc_group.add_argument("--msvc", action="store_true", help="Compile generated C with Microsoft cl.exe instead of gcc.")
    ap.add_argument("--mode-each", action="store_true", help="Process each input file independently (required for multiple inputs).")
    ap.add_argument("--summary", action="store_true", help="Print tabular per-file build summary.")
    ap.add_argument("--pretty", action="store_true", help="Normalize printed program output for display only.")
    ap.add_argument("--no-validate", action="store_true", help="Skip Fortran pre-validation checks before transpilation.")
    args = ap.parse_args()
    if args.run_both:
        args.run = True
    do_postprocess = not args.raw

    def _expand_inputs(raws: List[str]) -> List[Path]:
        out: List[Path] = []
        seen: set[str] = set()
        for raw in raws:
            has_glob = any(ch in raw for ch in "*?[]")
            matches = sorted(glob.glob(raw))
            if has_glob:
                if not matches:
                    print(f"Missing file: {raw}")
                    continue
                for m in matches:
                    p = Path(m)
                    if not p.is_file():
                        continue
                    k = str(p.resolve()).lower()
                    if k in seen:
                        continue
                    seen.add(k)
                    out.append(p)
                continue
            p = Path(raw)
            if not p.exists() or not p.is_file():
                print(f"Missing file: {p}")
                continue
            k = str(p.resolve()).lower()
            if k in seen:
                continue
            seen.add(k)
            out.append(p)
        return out

    src_paths = _expand_inputs(args.fortran_files)
    if not src_paths:
        return 1
    if len(src_paths) > 1 and not args.mode_each:
        print("Multiple input files require --mode-each.")
        return 1

    do_build_fortran = bool(args.compile_both or args.compile_both_c or args.run_both)
    do_build_c = bool(args.run or args.compile_both or args.compile_both_c or args.compile or args.compile_c)
    do_run_fortran = bool(args.run_both)
    do_run_c = bool(args.run)
    force_f_compile_only = bool(args.compile_both_c)
    force_c_compile_only = bool(args.compile_c or args.compile_both_c)
    c_compiler = _selected_c_compiler(args)

    def _render_stdout(text: str) -> str:
        if not text.strip():
            return ""
        if args.pretty and _NORMALIZE_TEXT is not None:
            return _NORMALIZE_TEXT(text, 1e-5, 4).rstrip()
        return text.rstrip()

    def _build_and_run(label: str, build_cmd: List[str], exe_path: Path) -> int:
        print(f"Build ({label}):", " ".join(build_cmd))
        cp = subprocess.run(build_cmd, capture_output=True, text=True)
        if cp.returncode != 0:
            print(f"Build ({label}): FAIL")
            if cp.stdout.strip():
                print(cp.stdout.rstrip())
            if cp.stderr.strip():
                print(cp.stderr.rstrip())
            return 1
        print(f"Build ({label}): PASS")
        rp = subprocess.run([str(exe_path.resolve())], capture_output=True, text=True)
        if rp.returncode != 0:
            print(f"Run ({label}): FAIL (exit {rp.returncode})")
            if rp.stdout.strip():
                print(_render_stdout(rp.stdout))
            if rp.stderr.strip():
                print(rp.stderr.rstrip())
            return 1
        print(f"Run ({label}): PASS")
        if rp.stdout.strip():
            print(_render_stdout(rp.stdout))
        if rp.stderr.strip():
            print(rp.stderr.rstrip())
        return 0

    def _build_only(label: str, build_cmd: List[str]) -> int:
        print(f"Build ({label}):", " ".join(build_cmd))
        cp = subprocess.run(build_cmd, capture_output=True, text=True)
        if cp.returncode != 0:
            print(f"Build ({label}): FAIL")
            if cp.stdout.strip():
                print(cp.stdout.rstrip())
            if cp.stderr.strip():
                print(cp.stderr.rstrip())
            return 1
        print(f"Build ({label}): PASS")
        return 0

    out_dir = Path(args.out_dir) if args.out_dir else None
    if out_dir is not None:
        out_dir.mkdir(parents=True, exist_ok=True)

    def _safe_stem(src_path: Path) -> str:
        stem = src_path.stem or "temp"
        safe = re.sub(r"[^A-Za-z0-9_]+", "_", stem).strip("_")
        return safe or "temp"

    def _out_path_for(src_path: Path, multi_mode: bool) -> Path:
        default_name = f"temp_{_safe_stem(src_path)}.c"
        if multi_mode:
            if out_dir is not None:
                return out_dir / default_name
            return Path(default_name)
        if args.out:
            out_name = Path(args.out).name
        else:
            out_name = default_name
        if out_dir is not None:
            return out_dir / out_name
        return Path(out_name)

    had_error = False
    summary_rows: List[Dict[str, object]] = []
    multi_mode = args.mode_each and len(src_paths) >= 1
    for src_path in src_paths:
        row: Dict[str, object] = {
            "source": str(src_path),
            "c_source": "",
            "compile_f90": (False if do_build_fortran else None),
            "compile_c": (False if do_build_c else None),
        }
        src_text = src_path.read_text(encoding="utf-8", errors="ignore")
        src_units = fscan.split_fortran_units_simple(src_text)
        dep_srcs = _resolve_fortran_support_sources(src_path, src_text)
        has_program_unit = any(u.get("kind") == "program" for u in src_units)

        if do_build_fortran:
            f_sources = [str(p) for p in dep_srcs] + [str(src_path)]
            if has_program_unit and not force_f_compile_only:
                f_exe = src_path.with_suffix(".orig.exe")
                f_build_cmd = ["gfortran", *f_sources, "-o", str(f_exe)]
            else:
                if dep_srcs:
                    f_build_cmd = ["gfortran", "-c", *f_sources]
                else:
                    f_obj = src_path.with_suffix(".orig.o")
                    f_build_cmd = ["gfortran", "-c", str(src_path), "-o", str(f_obj)]
            if do_run_fortran and has_program_unit:
                rc = _build_and_run("original-fortran", f_build_cmd, f_exe)
            else:
                rc = _build_only("original-fortran", f_build_cmd)
            row["compile_f90"] = (rc == 0)
            if rc != 0:
                had_error = True
                summary_rows.append(row)
                if not multi_mode:
                    if args.summary:
                        _print_summary_table(summary_rows)
                    return rc
                continue

        try:
            c_src = transpile_fortran_to_c(
                src_text,
                one_line=args.one_line,
                validate=(not args.no_validate),
                annotate=args.annotate,
            )
            if do_postprocess:
                c_src = postprocess_c_text(c_src)
            if args.single_file:
                c_src = _embed_runtime_c(c_src)
        except ValueError as e:
            print(f"{src_path}: {e}")
            row["compile_c"] = False if do_build_c else row["compile_c"]
            summary_rows.append(row)
            had_error = True
            if not multi_mode:
                if args.summary:
                    _print_summary_table(summary_rows)
                return 1
            continue
        out_path = _out_path_for(src_path, multi_mode=(len(src_paths) > 1 or args.mode_each))
        out_path.write_text(c_src, encoding="utf-8")
        print(f"Wrote {out_path}")
        row["c_source"] = str(out_path)
        if not has_program_unit:
            header_path = out_path.with_suffix(".h")
            header_src = _build_header_text(c_src, header_path.name)
            if header_src:
                header_path.write_text(header_src, encoding="utf-8")
                print(f"Wrote {header_path}")
        if args.tee:
            print(c_src, end="")

        if do_build_c:
            c_build_cmd, exe = _build_c_command(
                c_compiler,
                REPO_ROOT,
                RUNTIME_C_PATH,
                out_path,
                args.single_file,
                has_program_unit,
                force_c_compile_only,
            )
            if do_run_c and has_program_unit:
                assert exe is not None
                rc = _build_and_run("transformed-c", c_build_cmd, exe)
            else:
                rc = _build_only("transformed-c", c_build_cmd)
            row["compile_c"] = (rc == 0)
            if rc != 0:
                had_error = True
                summary_rows.append(row)
                if not multi_mode:
                    if args.summary:
                        _print_summary_table(summary_rows)
                    return rc
                continue
        summary_rows.append(row)

    if args.summary:
        _print_summary_table(summary_rows)
    return 1 if had_error else 0



__all__ = ["main", "_selected_c_compiler", "_build_c_command"]
