#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


def _extract_run_output(stdout: str, label: str, stop_markers: list[str]) -> str:
    start_marker = f"Run ({label}): PASS"
    start = stdout.find(start_marker)
    if start < 0:
        raise ValueError(f"missing run marker: {start_marker}")
    text = stdout[start + len(start_marker):]
    if text.startswith("\r\n"):
        text = text[2:]
    elif text.startswith("\n"):
        text = text[1:]
    stops = [text.find(marker) for marker in stop_markers if text.find(marker) >= 0]
    if stops:
        text = text[: min(stops)]
    return text.rstrip()


def _extract_generated_c_path(stdout: str) -> Path:
    matches = re.findall(r"^Wrote\s+(.+?\.c)\s*$", stdout, flags=re.MULTILINE)
    if not matches:
        raise ValueError("could not find generated C path in xf2c output")
    return Path(matches[-1].strip())


def _markdown_block(lang: str, text: str) -> str:
    return f"```{lang}\n{text.rstrip()}\n```\n"


def _parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Run xf2c.py on one example and export Fortran/C source and outputs to Markdown."
    )
    ap.add_argument("source", help="Fortran source file")
    ap.add_argument("--out", default="", help="Markdown output path (default: <stem>.md)")
    ap.add_argument("--pretty", action="store_true", help="Pass --pretty to xf2c.py")
    ap.add_argument("--annotate", action="store_true", help="Pass --annotate to xf2c.py")
    ap.add_argument("--raw", action="store_true", help="Pass --raw to xf2c.py")
    ap.add_argument("--xf2c", default="xf2c.py", help="Path to xf2c.py")
    return ap.parse_args()


def main() -> int:
    args = _parse_args()
    src_path = Path(args.source)
    if not src_path.is_file():
        print(f"[ERROR] source file not found: {src_path}", file=sys.stderr)
        return 1

    xf2c_path = Path(args.xf2c)
    if not xf2c_path.is_file():
        print(f"[ERROR] xf2c.py not found: {xf2c_path}", file=sys.stderr)
        return 1

    cmd = [sys.executable, str(xf2c_path), str(src_path), "--run-both"]
    if args.pretty:
        cmd.append("--pretty")
    if args.annotate:
        cmd.append("--annotate")
    if args.raw:
        cmd.append("--raw")

    proc = subprocess.run(
        cmd,
        cwd=Path.cwd(),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stdout.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        return proc.returncode

    c_path = _extract_generated_c_path(proc.stdout)
    if not c_path.is_file():
        raise FileNotFoundError(f"generated C file not found: {c_path}")

    f_src = src_path.read_text(encoding="utf-8", errors="replace")
    c_src = c_path.read_text(encoding="utf-8", errors="replace")
    f_out = _extract_run_output(proc.stdout, "original-fortran", ["Build (transformed-c):"])
    f_out = re.sub(r"\n?Wrote\s+\S+\.c\s*$", "", f_out, flags=re.IGNORECASE)
    c_out = _extract_run_output(proc.stdout, "transformed-c", [])

    out_path = Path(args.out) if args.out else src_path.with_suffix(".md")
    md = []
    md.append(f"# {src_path.stem}\n")
    md.append(f"`{' '.join(cmd)}`\n")
    md.append("\n## Fortran\n\n")
    md.append(_markdown_block("fortran", f_src))
    md.append("\n## Fortran Output\n\n")
    md.append(_markdown_block("text", f_out))
    md.append("\n## Generated C\n\n")
    md.append(_markdown_block("c", c_src))
    md.append("\n## C Output\n\n")
    md.append(_markdown_block("text", c_out))
    out_path.write_text("".join(md), encoding="utf-8")
    print(f"Wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
