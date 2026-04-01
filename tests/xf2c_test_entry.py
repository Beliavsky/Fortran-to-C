from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
REAL_XF2C_PATH = REPO_ROOT / "xf2c.py"


def main() -> int:
    cmd = [sys.executable, str(REAL_XF2C_PATH), *sys.argv[1:]]
    compiler = os.environ.get("XF2C_TEST_C_COMPILER", "gcc").strip().lower()
    if compiler == "clang":
        cmd.append("--clang")
    elif compiler == "msvc":
        cmd.append("--msvc")
    elif compiler not in {"", "gcc"}:
        print(f"unsupported XF2C_TEST_C_COMPILER={compiler}", file=sys.stderr)
        return 2

    cp = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True, check=False)
    if cp.stdout:
        sys.stdout.write(cp.stdout)
    if cp.stderr:
        sys.stderr.write(cp.stderr)
    return cp.returncode


if __name__ == "__main__":
    raise SystemExit(main())
