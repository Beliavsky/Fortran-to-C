#!/usr/bin/env python3
"""xf2c_driver.py: CLI/build driver for xf2c."""

from __future__ import annotations

import argparse
import glob
import subprocess
from pathlib import Path
from typing import Dict, List

import fortran_scan as fscan

from xf2c_core import transpile_fortran_to_c

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



def main() -> int:
    ap = argparse.ArgumentParser(description="Small Fortran-to-C transpiler.")
    ap.add_argument("fortran_files", nargs="+", help="Input free-form Fortran source file(s) or glob pattern(s).")
    ap.add_argument("--out", default="temp.c", help="Output C file (default: temp.c).")
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
    ap.add_argument("--mode-each", action="store_true", help="Process each input file independently (required for multiple inputs).")
    ap.add_argument("--summary", action="store_true", help="Print tabular per-file build summary.")
    ap.add_argument("--no-validate", action="store_true", help="Skip Fortran pre-validation checks before transpilation.")
    args = ap.parse_args()
    if args.run_both:
        args.run = True

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
        rp = subprocess.run([str(exe_path)], capture_output=True, text=True)
        if rp.returncode != 0:
            print(f"Run ({label}): FAIL (exit {rp.returncode})")
            if rp.stdout.strip():
                print(rp.stdout.rstrip())
            if rp.stderr.strip():
                print(rp.stderr.rstrip())
            return 1
        print(f"Run ({label}): PASS")
        if rp.stdout.strip():
            print(rp.stdout.rstrip())
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

    def _out_path_for(src_path: Path, multi_mode: bool) -> Path:
        if multi_mode:
            if out_dir is not None:
                return out_dir / f"{src_path.stem}.c"
            return Path(f"{src_path.stem}.c")
        if out_dir is not None:
            return out_dir / Path(args.out).name
        return Path(args.out)

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
        has_program_unit = any(u.get("kind") == "program" for u in src_units)

        if do_build_fortran:
            if has_program_unit and not force_f_compile_only:
                f_exe = src_path.with_suffix(".orig.exe")
                f_build_cmd = ["gfortran", str(src_path), "-o", str(f_exe)]
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
        if args.tee:
            print(c_src, end="")

        if do_build_c:
            if has_program_unit and not force_c_compile_only:
                exe = out_path.with_suffix(".exe")
                c_build_cmd = ["gcc", str(out_path), "-lm", "-o", str(exe)]
            else:
                c_obj = out_path.with_suffix(".o")
                c_build_cmd = ["gcc", "-c", str(out_path), "-o", str(c_obj)]
            if do_run_c and has_program_unit:
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



__all__ = ["main"]
