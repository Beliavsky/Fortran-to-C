"""Batch-run xf2c over many Fortran source files.

The default workflow reads file names from `fortran_files.txt`, invokes
`xf2c.py` for each source, and summarizes pass/fail results. This is the
project's quick regression runner for many small example programs.
"""

from __future__ import annotations

import argparse
import glob
import re
import shlex
import subprocess
import sys
from pathlib import Path


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run xf2c.py over many Fortran files and summarize pass/fail results."
    )
    parser.add_argument(
        "files",
        nargs="*",
        help="Fortran source files to process. If omitted, --file-list is used.",
    )
    parser.add_argument(
        "--file-list",
        default="fortran_files.txt",
        help="Text file listing .f90 files to process when no positional files are given.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=None,
        help="Process at most this many files.",
    )
    parser.add_argument(
        "--xf2c",
        default="xf2c.py",
        help="Path to xf2c.py.",
    )
    parser.add_argument(
        "--python",
        dest="python_cmd",
        default=sys.executable,
        help="Python executable to use when invoking xf2c.py.",
    )
    parser.add_argument(
        "--opts",
        default="--run-both --tee",
        help="Extra options passed to xf2c.py. Default: '--run-both --tee'.",
    )
    parser.add_argument(
        "--show-source",
        action="store_true",
        help="Print each Fortran source file before running xf2c.py.",
    )
    parser.add_argument(
        "--quiet-runs",
        action="store_true",
        help="Hide successful Fortran/C program stdout while still running them.",
    )
    return parser.parse_args()


def _load_sources(args: argparse.Namespace) -> list[str]:
    if args.files:
        sources: list[str] = []
        for pattern in args.files:
            if glob.has_magic(pattern):
                matches = sorted(glob.glob(pattern))
                if matches:
                    sources.extend(matches)
                else:
                    sources.append(pattern)
            else:
                sources.append(pattern)
        return sources

    file_list = Path(args.file_list)
    if not file_list.is_file():
        raise FileNotFoundError(f"{file_list} not found")

    return [
        line.strip()
        for line in file_list.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]


def _suppress_successful_run_output(text: str) -> str:
    kept: list[str] = []
    suppress = False
    top_level = re.compile(
        r"^(?:Build \([^)]+\):|Run \([^)]+\):|Wrote\s+\S+|--summary:|\[PASS\]|\[FAIL\]|=+|TOTAL=|FAILED \.f90 FILES:)"
    )
    run_pass = re.compile(r"^Run \([^)]+\): PASS$")
    for line in text.splitlines():
        if run_pass.match(line):
            kept.append(line)
            suppress = True
            continue
        if suppress:
            if top_level.match(line):
                suppress = False
                kept.append(line)
            continue
        kept.append(line)
    tail = "\n" if text.endswith("\n") else ""
    return "\n".join(kept) + tail


def main() -> int:
    args = _parse_args()
    xf2c_path = Path(args.xf2c)
    if not xf2c_path.is_file():
        print(f"[ERROR] {xf2c_path} not found.", file=sys.stderr)
        return 1

    try:
        sources = _load_sources(args)
    except FileNotFoundError as exc:
        print(f"[ERROR] {exc}", file=sys.stderr)
        return 1

    if args.limit is not None:
        if args.limit < 0:
            print("[ERROR] --limit must be nonnegative.", file=sys.stderr)
            return 1
        sources = sources[: args.limit]

    xf2c_opts = shlex.split(args.opts)
    total = 0
    passed = 0
    failed = 0
    skipped = 0
    failed_list: list[str] = []

    for src_name in sources:
        src_path = Path(src_name)
        if not src_path.is_file():
            print("------------------------------------------------------------")
            print(f"[SKIP] {src_name} not found")
            skipped += 1
            continue

        total += 1
        print("------------------------------------------------------------")
        print(f"[TEST] {src_name}")
        if args.show_source:
            try:
                print(src_path.read_text(encoding="utf-8", errors="replace"))
            except OSError as exc:
                print(f"[WARN] could not read {src_name}: {exc}")
            print()

        cmd = [args.python_cmd, str(xf2c_path), src_name, *xf2c_opts]
        proc = subprocess.run(
            cmd,
            check=False,
            capture_output=args.quiet_runs,
            text=args.quiet_runs,
        )
        if args.quiet_runs:
            if proc.returncode == 0:
                filtered = _suppress_successful_run_output(proc.stdout)
                if filtered:
                    print(filtered, end="" if filtered.endswith("\n") else "\n")
                if proc.stderr:
                    print(proc.stderr, end="" if proc.stderr.endswith("\n") else "\n", file=sys.stderr)
            else:
                if proc.stdout:
                    print(proc.stdout, end="" if proc.stdout.endswith("\n") else "\n")
                if proc.stderr:
                    print(proc.stderr, end="" if proc.stderr.endswith("\n") else "\n", file=sys.stderr)
        if proc.returncode == 0:
            print(f"[PASS] {src_name}")
            passed += 1
        else:
            print(f"[FAIL] {src_name} (exit {proc.returncode})")
            failed += 1
            failed_list.append(src_name)
        print()

    print("============================================================")
    print(f"TOTAL={total} PASS={passed} FAIL={failed} SKIP={skipped}")
    if failed_list:
        print("FAILED .f90 FILES:")
        for src_name in failed_list:
            print(f"  {src_name}")
    print("============================================================")
    return failed


if __name__ == "__main__":
    raise SystemExit(main())
