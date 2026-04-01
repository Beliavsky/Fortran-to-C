#!/usr/bin/env python3
"""xf2c_driver.py: CLI/build driver for xf2c."""

from __future__ import annotations

import argparse
import glob
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import fortran_scan as fscan
from xc_post import postprocess_c_text

from xf2c_core import transpile_fortran_to_c

REPO_ROOT = Path(__file__).resolve().parent
PARENT_ROOT = REPO_ROOT.parent
RUNTIME_C_PATH = REPO_ROOT / "fortran_runtime.c"
XNORMALIZE_CANDIDATES = [
    REPO_ROOT / "xnormalize.py",
    Path(r"c:\python\code\xnormalize.py"),
]
XFREE_CANDIDATES = [
    PARENT_ROOT / "xfree.py",
]
XCOMMON_CANDIDATES = [
    PARENT_ROOT / "xcommon.py",
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


def _load_xfree_convert_text():
    if str(PARENT_ROOT) not in sys.path:
        sys.path.insert(0, str(PARENT_ROOT))
    for path in XFREE_CANDIDATES:
        if not path.exists():
            continue
        spec = importlib.util.spec_from_file_location("xfree_local", path)
        if spec is None or spec.loader is None:
            continue
        mod = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = mod
        spec.loader.exec_module(mod)
        convert = getattr(mod, "convert_text", None)
        if convert is not None:
            return convert
    return None


_XFREE_CONVERT_TEXT = _load_xfree_convert_text()


def _load_xcommon_rewrite_text():
    if str(PARENT_ROOT) not in sys.path:
        sys.path.insert(0, str(PARENT_ROOT))
    for path in XCOMMON_CANDIDATES:
        if not path.exists():
            continue
        spec = importlib.util.spec_from_file_location("xcommon_local", path)
        if spec is None or spec.loader is None:
            continue
        mod = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = mod
        spec.loader.exec_module(mod)
        rewrite = getattr(mod, "_rewrite_common_text", None)
        if rewrite is not None:
            return rewrite
    return None


_XCOMMON_REWRITE_TEXT = _load_xcommon_rewrite_text()


def _unique_free_form_path(src_path: Path) -> Path:
    cand = src_path.with_suffix(".f90")
    if not cand.exists():
        return cand
    i = 1
    while True:
        cand = src_path.with_name(f"{src_path.stem}_{i}.f90")
        if not cand.exists():
            return cand
        i += 1


def _unique_suffix_path(src_path: Path, suffix: str) -> Path:
    cand = src_path.with_name(f"{src_path.stem}{suffix}{src_path.suffix}")
    if not cand.exists():
        return cand
    i = 1
    while True:
        cand = src_path.with_name(f"{src_path.stem}{suffix}_{i}{src_path.suffix}")
        if not cand.exists():
            return cand
        i += 1


def _prepare_fixed_form_source(src_path: Path, text: Optional[str] = None) -> Path:
    if _XFREE_CONVERT_TEXT is None:
        raise ValueError("fixed-form .f input requires xfree.py, but it was not found")
    src_text = text if text is not None else src_path.read_text(encoding="utf-8", errors="ignore")
    out_path = _unique_free_form_path(src_path)
    out_path.write_text(_XFREE_CONVERT_TEXT(src_text), encoding="utf-8", newline="\n")
    return out_path


def _fortran_form_flag(form: Optional[str]) -> List[str]:
    if form == "free":
        return ["-ffree-form"]
    if form == "fixed":
        return ["-ffixed-form"]
    return []


def _prepared_transpile_source(src_path: Path, text: str, form: Optional[str]) -> Tuple[Path, str]:
    if form == "fixed":
        out_path = _prepare_fixed_form_source(src_path, text)
        src_path = out_path
        text = out_path.read_text(encoding="utf-8", errors="ignore")
    elif form == "free":
        pass
    elif src_path.suffix.lower() == ".f":
        out_path = _prepare_fixed_form_source(src_path, text)
        src_path = out_path
        text = out_path.read_text(encoding="utf-8", errors="ignore")
    if _XCOMMON_REWRITE_TEXT is not None:
        rewritten = _XCOMMON_REWRITE_TEXT(text)
        if rewritten != text:
            out_path = _unique_suffix_path(src_path, "_nocommon")
            out_path.write_text(rewritten, encoding="utf-8", newline="\n")
            return out_path, rewritten
    return src_path, text


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


def _count_fortran_code_lines(text: str) -> int:
    count = 0
    for raw in text.splitlines():
        if fscan.strip_comment(raw).strip():
            count += 1
    return count


def _count_c_code_lines(text: str) -> int:
    count = 0
    in_block = False
    for raw in text.splitlines():
        i = 0
        out: list[str] = []
        in_single = False
        in_double = False
        while i < len(raw):
            ch = raw[i]
            nxt = raw[i + 1] if i + 1 < len(raw) else ""
            if in_block:
                if ch == "*" and nxt == "/":
                    in_block = False
                    i += 2
                    continue
                i += 1
                continue
            if not in_double and ch == "'" and (i == 0 or raw[i - 1] != "\\"):
                in_single = not in_single
                out.append(ch)
                i += 1
                continue
            if not in_single and ch == '"' and (i == 0 or raw[i - 1] != "\\"):
                in_double = not in_double
                out.append(ch)
                i += 1
                continue
            if not in_single and not in_double:
                if ch == "/" and nxt == "*":
                    in_block = True
                    i += 2
                    continue
                if ch == "/" and nxt == "/":
                    break
            out.append(ch)
            i += 1
        if "".join(out).strip():
            count += 1
    return count


def _generated_banner(src_path: Path) -> str:
    return f"/* Generated by xf2c.py from {src_path.name} */\n\n"


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
    if path.suffix.lower() == ".f" and _XFREE_CONVERT_TEXT is not None:
        text = _XFREE_CONVERT_TEXT(text)
    return _module_names_in_text(text)


def _find_module_source(module_name: str, search_roots: List[Path], cache: Dict[str, Optional[Path]]) -> Optional[Path]:
    key = module_name.lower()
    if key in cache:
        return cache[key]
    for root in search_roots:
        if not root.exists():
            continue
        for pat in ("*.f90", "*.f"):
            for path in root.glob(pat):
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
            dep_visit_text = _XFREE_CONVERT_TEXT(dep_text) if dep.suffix.lower() == ".f" and _XFREE_CONVERT_TEXT is not None else dep_text
            visit(dep, dep_visit_text)
            ordered.append(_prepare_fixed_form_source(dep, dep_text) if dep.suffix.lower() == ".f" else dep)

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


def _fortran_obj_path(path: Path, index: int) -> Path:
    return path.with_name(f"{path.stem}.orig_{index}.o")


def main() -> int:
    ap = argparse.ArgumentParser(description="Small Fortran-to-C transpiler.")
    ap.add_argument("fortran_files", nargs="+", help="Input Fortran source file(s) (.f90 or fixed-form .f) or glob pattern(s).")
    ap.add_argument("--out", default="", help="Output C file (default: temp_<stem>.c).")
    ap.add_argument("--out-dir", default="", help="Output directory used with --mode-each.")
    ap.add_argument("--tee", action="store_true", help="Print generated C source.")
    ap.add_argument("--compile", action="store_true", help="Compile generated C source (no run).")
    ap.add_argument("--compile-c", action="store_true", help="Compile generated C source with -c only (no link).")
    ap.add_argument("--run", action="store_true", help="Compile/run generated C source.")
    ap.add_argument("--run-both", action="store_true", help="Build/run original Fortran source and generated C source.")
    ap.add_argument("--run-diff", action="store_true", help="With --run-both, compare original Fortran and generated C outputs.")
    ap.add_argument("--compile-both", action="store_true", help="Build (without running) original Fortran source and generated C source.")
    ap.add_argument("--compile-both-c", action="store_true", help="Compile original Fortran and generated C with -c only (no link).")
    ap.add_argument("--one-line", action="store_true", help="Collapse simple one-statement for/if blocks to one line.")
    ap.add_argument("--annotate", action="store_true", help="Insert C comments with original Fortran statements before translated code.")
    pp_group = ap.add_mutually_exclusive_group()
    pp_group.add_argument("--postprocess", action="store_true", help="Run conservative C readability cleanup before writing/compiling (default behavior).")
    pp_group.add_argument("--raw", action="store_true", help="Write raw transpiler output without C postprocessing.")
    ap.add_argument("--no-banner", action="store_true", help="Omit the generated-by provenance comment at the top of emitted C.")
    ap.add_argument("--single-file", action="store_true", help="Embed the shared runtime into the generated C file.")
    cc_group = ap.add_mutually_exclusive_group()
    cc_group.add_argument("--clang", action="store_true", help="Compile generated C with clang instead of gcc.")
    cc_group.add_argument("--msvc", action="store_true", help="Compile generated C with Microsoft cl.exe instead of gcc.")
    ap.add_argument("--mode-each", action="store_true", help="Process each input file independently (required for multiple inputs).")
    ap.add_argument("--summary", action="store_true", help="Print tabular per-file build summary.")
    ap.add_argument("--pretty", action="store_true", help="Normalize printed program output for display only.")
    ap.add_argument("--no-validate", action="store_true", help="Skip Fortran pre-validation checks before transpilation.")
    ap.add_argument("--max-errors", type=int, default=20, help="Maximum number of diagnostics to show for transpilation/validation errors; 0 means unlimited.")
    ap.add_argument("--std", default="", help="Language mode for xf2c validation, for example --std=f2023.")
    form_group = ap.add_mutually_exclusive_group()
    form_group.add_argument("--free-form", action="store_true", help="Treat the main input source as free-form Fortran regardless of extension.")
    form_group.add_argument("--fixed-form", action="store_true", help="Treat the main input source as fixed-form Fortran regardless of extension.")
    args = ap.parse_args()
    timing_report_path = os.environ.get("XF2C_TIMINGS_JSON", "").strip()
    phase_timings = {"compile_f90": 0.0, "transpile": 0.0, "compile_c": 0.0}

    def _write_phase_timings() -> None:
        if not timing_report_path:
            return
        try:
            Path(timing_report_path).write_text(json.dumps(phase_timings), encoding="utf-8")
        except OSError:
            pass
    if args.run_diff:
        args.run_both = True
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
        _write_phase_timings()
        return 1
    if len(src_paths) > 1 and not args.mode_each:
        print("Multiple input files require --mode-each.")
        _write_phase_timings()
        return 1

    do_build_fortran = bool(args.compile_both or args.compile_both_c or args.run_both)
    do_build_c = bool(args.run or args.compile_both or args.compile_both_c or args.compile or args.compile_c)
    do_run_fortran = bool(args.run_both)
    do_run_c = bool(args.run)
    force_f_compile_only = bool(args.compile_both_c)
    force_c_compile_only = bool(args.compile_c or args.compile_both_c)
    c_compiler = _selected_c_compiler(args)
    max_errors = max(0, int(args.max_errors))
    forced_form: Optional[str] = "free" if args.free_form else ("fixed" if args.fixed_form else None)

    def _render_stdout(text: str) -> str:
        if not text.strip():
            return ""
        if args.pretty and _NORMALIZE_TEXT is not None:
            return _NORMALIZE_TEXT(text, 1e-5, 4).rstrip()
        return text.rstrip()

    def _normalize_exe_name_diff(text: str, src_path: Path) -> str:
        if not text:
            return text
        stem = src_path.stem
        out = text
        out = re.sub(rf"(?i)\b{re.escape(stem)}\.orig\.exe\b", f"{stem}.exe", out)
        out = re.sub(rf"(?i)\btemp_{re.escape(stem)}\.exe\b", f"{stem}.exe", out)
        while "\\\\" in out:
            out = out.replace("\\\\", "\\")
        return out

    def _render_limited(text: str) -> str:
        stripped = text.rstrip()
        if not stripped:
            return ""
        if max_errors == 0:
            return stripped
        lines = stripped.splitlines()
        if len(lines) <= max_errors:
            return stripped
        return "\n".join(lines[:max_errors] + [f"... and {len(lines) - max_errors} more lines"])

    def _build_and_run(label: str, build_cmd: List[str], exe_path: Path) -> Tuple[int, str, str]:
        print(f"Build ({label}):", " ".join(build_cmd))
        cp = subprocess.run(build_cmd, capture_output=True, text=True)
        if cp.returncode != 0:
            print(f"Build ({label}): FAIL")
            if cp.stdout.strip():
                print(_render_limited(cp.stdout))
            if cp.stderr.strip():
                print(_render_limited(cp.stderr))
            return 1, cp.stdout or "", cp.stderr or ""
        print(f"Build ({label}): PASS")
        rp = subprocess.run([str(exe_path.resolve())], capture_output=True, text=True)
        if rp.returncode != 0:
            print(f"Run ({label}): FAIL (exit {rp.returncode})")
            if rp.stdout.strip():
                print(_render_limited(_render_stdout(rp.stdout)))
            if rp.stderr.strip():
                print(_render_limited(rp.stderr))
            return 1, rp.stdout or "", rp.stderr or ""
        print(f"Run ({label}): PASS")
        if rp.stdout.strip():
            print(_render_stdout(rp.stdout))
        if rp.stderr.strip():
            print(rp.stderr.rstrip())
        return 0, rp.stdout or "", rp.stderr or ""

    def _build_only(label: str, build_cmd: List[str]) -> int:
        print(f"Build ({label}):", " ".join(build_cmd))
        cp = subprocess.run(build_cmd, capture_output=True, text=True)
        if cp.returncode != 0:
            print(f"Build ({label}): FAIL")
            if cp.stdout.strip():
                print(_render_limited(cp.stdout))
            if cp.stderr.strip():
                print(_render_limited(cp.stderr))
            return 1
        print(f"Build ({label}): PASS")
        return 0

    def _build_fortran_pipeline(
        label: str,
        sources: List[Path],
        main_source: Path,
        main_form: Optional[str],
        link_exe: Optional[Path],
        run_after: bool,
    ) -> Tuple[int, str, str]:
        objs: List[Path] = []
        for idx, fsrc in enumerate(sources):
            obj = _fortran_obj_path(fsrc, idx)
            form_flag = _fortran_form_flag(main_form if str(fsrc.resolve()).lower() == str(main_source.resolve()).lower() else None)
            compile_cmd = ["gfortran", *form_flag, "-c", str(fsrc), "-o", str(obj)]
            print(f"Build ({label}):", " ".join(compile_cmd))
            cp = subprocess.run(compile_cmd, capture_output=True, text=True)
            if cp.returncode != 0:
                print(f"Build ({label}): FAIL")
                if cp.stdout.strip():
                    print(_render_limited(cp.stdout))
                if cp.stderr.strip():
                    print(_render_limited(cp.stderr))
                return 1, cp.stdout or "", cp.stderr or ""
            objs.append(obj)
        if link_exe is None:
            print(f"Build ({label}): PASS")
            return 0, "", ""
        link_cmd = ["gfortran", *[str(obj) for obj in objs], "-o", str(link_exe)]
        print(f"Build ({label}):", " ".join(link_cmd))
        cp = subprocess.run(link_cmd, capture_output=True, text=True)
        if cp.returncode != 0:
            print(f"Build ({label}): FAIL")
            if cp.stdout.strip():
                print(_render_limited(cp.stdout))
            if cp.stderr.strip():
                print(_render_limited(cp.stderr))
            return 1, cp.stdout or "", cp.stderr or ""
        print(f"Build ({label}): PASS")
        if not run_after:
            return 0, "", ""
        rp = subprocess.run([str(link_exe.resolve())], capture_output=True, text=True)
        if rp.returncode != 0:
            print(f"Run ({label}): FAIL (exit {rp.returncode})")
            if rp.stdout.strip():
                print(_render_limited(_render_stdout(rp.stdout)))
            if rp.stderr.strip():
                print(_render_limited(rp.stderr))
            return 1, rp.stdout or "", rp.stderr or ""
        print(f"Run ({label}): PASS")
        if rp.stdout.strip():
            print(_render_stdout(rp.stdout))
        if rp.stderr.strip():
            print(rp.stderr.rstrip())
        return 0, rp.stdout or "", rp.stderr or ""

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
        original_src_path = src_path
        src_text_raw = src_path.read_text(encoding="utf-8", errors="ignore")
        src_path, src_text = _prepared_transpile_source(src_path, src_text_raw, forced_form)
        fortran_run_out = ""
        fortran_run_err = ""
        row: Dict[str, object] = {
            "source": str(original_src_path),
            "c_source": "",
            "compile_f90": (False if do_build_fortran else None),
            "compile_c": (False if do_build_c else None),
        }
        src_units = fscan.split_fortran_units_simple(src_text)
        dep_srcs = _resolve_fortran_support_sources(src_path, src_text)
        has_program_unit = any(u.get("kind") == "program" for u in src_units)

        if do_build_fortran:
            f_sources = [str(p) for p in dep_srcs] + [str(src_path)]
            f_exe = src_path.with_suffix(".orig.exe") if has_program_unit and not force_f_compile_only else None
            t_compile_f90 = time.perf_counter()
            rc, f_run_out, f_run_err = _build_fortran_pipeline(
                "original-fortran",
                dep_srcs + [original_src_path],
                original_src_path,
                forced_form,
                f_exe,
                do_run_fortran and has_program_unit,
            )
            phase_timings["compile_f90"] += time.perf_counter() - t_compile_f90
            fortran_run_out, fortran_run_err = f_run_out, f_run_err
            row["compile_f90"] = (rc == 0)
            if rc != 0:
                had_error = True
                summary_rows.append(row)
                if not multi_mode:
                    if args.summary:
                        _print_summary_table(summary_rows)
                    _write_phase_timings()
                    return rc
                continue

        try:
            t_transpile = time.perf_counter()
            c_src = transpile_fortran_to_c(
                src_text,
                one_line=args.one_line,
                validate=(not args.no_validate),
                annotate=args.annotate,
                max_errors=args.max_errors,
                std=args.std,
            )
            if do_postprocess:
                c_src = postprocess_c_text(c_src)
            if args.single_file:
                c_src = _embed_runtime_c(c_src)
            if not args.no_banner:
                c_src = _generated_banner(src_path) + c_src
            phase_timings["transpile"] += time.perf_counter() - t_transpile
        except ValueError as e:
            print(f"{src_path}: {e}")
            row["compile_c"] = False if do_build_c else row["compile_c"]
            summary_rows.append(row)
            had_error = True
            if not multi_mode:
                if args.summary:
                    _print_summary_table(summary_rows)
                _write_phase_timings()
                return 1
            continue
        out_path = _out_path_for(src_path, multi_mode=(len(src_paths) > 1 or args.mode_each))
        out_path.write_text(c_src, encoding="utf-8")
        f90_loc = _count_fortran_code_lines(src_text)
        c_loc = _count_c_code_lines(c_src)
        print("")
        print(f"Wrote {out_path} ({c_loc} C lines from {f90_loc} Fortran lines)")
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
            t_compile_c = time.perf_counter()
            if do_run_c and has_program_unit:
                assert exe is not None
                rc, c_run_out, c_run_err = _build_and_run("transformed-c", c_build_cmd, exe)
            else:
                rc = _build_only("transformed-c", c_build_cmd)
                c_run_out, c_run_err = "", ""
            phase_timings["compile_c"] += time.perf_counter() - t_compile_c
            row["compile_c"] = (rc == 0)
            if rc != 0:
                had_error = True
                summary_rows.append(row)
                if not multi_mode:
                    if args.summary:
                        _print_summary_table(summary_rows)
                    _write_phase_timings()
                    return rc
                continue
            if args.run_diff and do_run_fortran and do_run_c:
                f_cmp_out = _normalize_exe_name_diff(_render_stdout(fortran_run_out), src_path)
                c_cmp_out = _normalize_exe_name_diff(_render_stdout(c_run_out), src_path)
                f_cmp_err = fortran_run_err.rstrip()
                c_cmp_err = c_run_err.rstrip()
                if f_cmp_out == c_cmp_out and f_cmp_err == c_cmp_err:
                    print("Run diff: MATCH")
                else:
                    print("Run diff: DIFFER")
                    if f_cmp_out:
                        print("--- original-fortran stdout ---")
                        print(_render_limited(f_cmp_out))
                    if c_cmp_out:
                        print("--- transformed-c stdout ---")
                        print(_render_limited(c_cmp_out))
                    if f_cmp_err:
                        print("--- original-fortran stderr ---")
                        print(_render_limited(f_cmp_err))
                    if c_cmp_err:
                        print("--- transformed-c stderr ---")
                        print(_render_limited(c_cmp_err))
                    had_error = True
                    summary_rows.append(row)
                    if not multi_mode:
                        if args.summary:
                            _print_summary_table(summary_rows)
                        _write_phase_timings()
                        return 1
                    continue
        summary_rows.append(row)

    if args.summary:
        _print_summary_table(summary_rows)
    _write_phase_timings()
    return 1 if had_error else 0



__all__ = ["main", "_selected_c_compiler", "_build_c_command"]


if __name__ == "__main__":
    raise SystemExit(main())
