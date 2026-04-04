#!/usr/bin/env python3
"""Reduce the first xf2c compile failure to a same-file procedure slice.

This helper runs ``xf2c.py <source> --compile``, parses the first hard C
compiler error, identifies the generated C function that failed, and then
extracts the corresponding Fortran procedure plus same-file dependencies into a
small slice using ``xextract_fortran_slice.py``.

First version scope:
- compile-only workflow
- same-file procedure extraction
- C function name is assumed to match the Fortran procedure name
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
if str(PARENT) not in sys.path:
    sys.path.insert(0, str(PARENT))

from xextract_fortran_slice import build_slice
from fortran_scan import indent_fortran_blocks


_FUNC_RE = re.compile(r"^[^:\n]+: In function '([^']+)':\s*$")
_ERROR_RE = re.compile(r"^[^:\n]+:\d+:\d+:\s+error:\s+(.*)$", re.IGNORECASE)
_MODULE_RE = re.compile(r"^\s*module\s+([a-z][a-z0-9_]*)\b", re.IGNORECASE)
_PROGRAM_RE = re.compile(r"^\s*program\s+([a-z][a-z0-9_]*)\b", re.IGNORECASE)


@dataclass
class CompileFailure:
    function_name: Optional[str]
    error_line: str
    error_message: str
    output: str
    returncode: int


def _default_xf2c_path() -> Path:
    here = Path(__file__).resolve().parent
    if (here / "xf2c.py").exists():
        return here / "xf2c.py"
    return here / "f2c" / "xf2c.py"


def _run_xf2c_compile(source: Path, xf2c_path: Path, extra_args: List[str]) -> subprocess.CompletedProcess[str]:
    cmd = [sys.executable, str(xf2c_path), str(source), "--compile", *extra_args]
    return subprocess.run(
        cmd,
        cwd=str(source.parent),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )


def _first_compile_failure(output: str, returncode: int) -> Optional[CompileFailure]:
    current_func: Optional[str] = None
    for raw in output.splitlines():
        m_func = _FUNC_RE.match(raw)
        if m_func:
            current_func = m_func.group(1)
            continue
        m_err = _ERROR_RE.match(raw)
        if m_err:
            return CompileFailure(
                function_name=current_func,
                error_line=raw,
                error_message=m_err.group(1).strip(),
                output=output,
                returncode=returncode,
            )
    return None


def _normalize_proc_name(name: str) -> str:
    return name.strip().lower()


def _source_has_program(source: Path) -> bool:
    for raw in source.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.split("!", 1)[0].strip()
        low = line.lower()
        if not low:
            continue
        if _PROGRAM_RE.match(low) and not low.startswith("end program"):
            return True
    return False


def _first_module_name(text: str) -> Optional[str]:
    for raw in text.splitlines():
        line = raw.split("!", 1)[0].strip()
        if not line:
            continue
        m = _MODULE_RE.match(line)
        if m and not line.lower().startswith("module procedure"):
            return m.group(1)
    return None


def _append_stub_program(text: str, source: Path) -> str:
    if not _source_has_program(source):
        return text
    mod_name = _first_module_name(text)
    out = text.rstrip() + "\n\nprogram reduced_slice_main\n"
    if mod_name:
        out += f"use {mod_name}\n"
    out += "implicit none\n"
    out += "print *, 'reduced slice'\n"
    out += "end program reduced_slice_main\n"
    return out


def parse_args(argv: Optional[Iterable[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="Fortran source file")
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="Output reduced .f90 path (default: <proc>_slice.f90 next to source)",
    )
    parser.add_argument(
        "--proc",
        help="Override the inferred failing procedure name",
    )
    parser.add_argument(
        "--xf2c",
        type=Path,
        default=_default_xf2c_path(),
        help="Path to xf2c.py (default: sibling f2c/xf2c.py)",
    )
    parser.add_argument(
        "--print-log",
        action="store_true",
        help="Print the full xf2c/compile output after the summary",
    )
    parser.add_argument(
        "xf2c_args",
        nargs="*",
        help="Extra arguments passed through to xf2c.py before --compile",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Iterable[str]] = None) -> int:
    args = parse_args(argv)
    source = args.source.resolve()
    xf2c_path = args.xf2c.resolve()

    if not source.exists():
        print(f"source not found: {source}", file=sys.stderr)
        return 2
    if not xf2c_path.exists():
        print(f"xf2c.py not found: {xf2c_path}", file=sys.stderr)
        return 2

    proc = _run_xf2c_compile(source, xf2c_path, list(args.xf2c_args))
    failure = _first_compile_failure(proc.stdout, proc.returncode)
    if failure is None:
        if proc.returncode == 0:
            print("No compile failure found.")
            return 0
        print("Compile failed, but no GCC-style error line was found.", file=sys.stderr)
        if args.print_log:
            sys.stdout.write(proc.stdout)
        return 1

    proc_name = _normalize_proc_name(args.proc or failure.function_name or "")
    if not proc_name:
        print("Found a compile error, but could not infer the failing procedure name.", file=sys.stderr)
        print(failure.error_line, file=sys.stderr)
        if args.print_log:
            sys.stdout.write(proc.stdout)
        return 1

    output = args.output or source.with_name(f"{proc_name}_slice.f90")
    try:
        text, notes = build_slice(source, proc_name)
    except Exception as exc:
        print(f"First failing generated C function: {failure.function_name or '<unknown>'}")
        print(f"First hard compiler error: {failure.error_message}")
        print(f"Could not extract procedure '{proc_name}': {exc}", file=sys.stderr)
        if args.print_log:
            sys.stdout.write(proc.stdout)
        return 1

    rendered = indent_fortran_blocks(_append_stub_program(text, source))
    output.write_text(rendered, encoding="utf-8")
    print(f"First failing generated C function: {failure.function_name or '<unknown>'}")
    print(f"First hard compiler error: {failure.error_message}")
    print(f"Reduced procedure: {proc_name}")
    print(f"Wrote {output}")
    if notes:
        print("Notes:")
        for note in notes:
            print(note)
    if args.print_log:
        print("")
        sys.stdout.write(proc.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
