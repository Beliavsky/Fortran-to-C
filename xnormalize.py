#!/usr/bin/env python3
"""
Normalize program output for display and comparison.

Normalization:
- strip leading/trailing spaces on each line
- compress repeated whitespace to one space
- convert floats very close to integers to integers
- optionally round noninteger floats to a fixed number of decimals
- remove trailing .000... from numeric output
"""

from __future__ import annotations

import argparse
import math
import re
import subprocess
import sys


NUMBER_RE = re.compile(
    r"""
    (?<![a-zA-Z_])
    [+-]?
    (?:
        (?:\d+\.\d*|\.\d+|\d+)
        (?:[eEdD][+-]?\d+)?
    )
    """,
    re.VERBOSE,
)


def normalize_number(token: str, int_tol: float, decimals: int | None) -> str:
    t = token.replace("d", "e").replace("D", "E")
    try:
        x = float(t)
    except ValueError:
        return token

    if not math.isfinite(x):
        return token.lower()

    if abs(x) <= int_tol:
        return "0"

    xr = round(x)
    if abs(x - xr) <= int_tol:
        return str(int(xr))

    if decimals is not None:
        s = f"{x:.{decimals}f}"
        s = s.rstrip("0").rstrip(".")
        if s == "-0":
            s = "0"
        return s

    s = f"{x:.12g}".lower()
    if "e" not in s and "." in s:
        s = s.rstrip("0").rstrip(".")
    if s == "-0":
        s = "0"
    return s


def normalize_line(line: str, int_tol: float, decimals: int | None) -> str:
    line = line.strip()
    line = re.sub(r"\s+", " ", line)
    line = NUMBER_RE.sub(
        lambda m: normalize_number(m.group(0), int_tol, decimals),
        line,
    )
    line = re.sub(r"\s+", " ", line).strip()
    return line


def normalize_text(text: str, int_tol: float, decimals: int | None) -> str:
    return "\n".join(
        normalize_line(line, int_tol, decimals) for line in text.splitlines()
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run a program, normalize its stdout, and print it."
    )
    parser.add_argument(
        "--int-tol",
        type=float,
        default=1e-5,
        help="Tolerance for rounding floats to integers",
    )
    parser.add_argument(
        "--decimals",
        type=int,
        default=None,
        help="Round noninteger floats to this many decimal places",
    )
    parser.add_argument(
        "command",
        nargs="+",
        help="Program to run, followed by any arguments for that program",
    )
    args = parser.parse_args()

    if args.decimals is not None and args.decimals < 0:
        parser.error("--decimals must be nonnegative")

    proc = subprocess.run(
        args.command,
        capture_output=True,
        text=True,
        errors="replace",
        check=False,
    )

    normalized = normalize_text(proc.stdout, args.int_tol, args.decimals)
    if normalized:
        sys.stdout.write(normalized)
        if not normalized.endswith("\n"):
            sys.stdout.write("\n")

    if proc.stderr:
        sys.stderr.write(proc.stderr)

    raise SystemExit(proc.returncode)


if __name__ == "__main__":
    main()
