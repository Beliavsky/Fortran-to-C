from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
UPSTREAM_MT = Path(r"c:\fortran\public_domain\github\mersenne-twister-fortran\src\mt19937-64.f90")
WRAPPER = REPO_ROOT / "mt19937_runif.f90"


def test_mt19937_runif_wrapper_reseeds_reproducibly() -> None:
    if not UPSTREAM_MT.exists():
        raise AssertionError(f"Missing upstream source: {UPSTREAM_MT}")

    program_text = "\n".join(
        [
            "program test_mt19937_runif",
            "use, intrinsic :: iso_fortran_env, only : int64, real64",
            "use mt19937_runif, only : rng_seed, runif, runif_1d, fill_runif_1d",
            "implicit none",
            "real(real64) :: a, b",
            "real(real64), allocatable :: x(:), y(:), z(:)",
            "",
            "call rng_seed(42_int64)",
            "a = runif()",
            "x = runif_1d(3)",
            "",
            "call rng_seed(42_int64)",
            "b = runif()",
            "y = runif_1d(3)",
            "allocate(z(3))",
            "call fill_runif_1d(z)",
            "",
            "if (a /= b) error stop 'scalar reseed mismatch'",
            "if (any(x /= y)) error stop 'vector reseed mismatch'",
            "if (all(z == y)) error stop 'fill routine did not advance stream'",
            "print '(f0.16)', a",
            "print '(3(1x,f0.16))', x",
            "end program test_mt19937_runif",
            "",
        ]
    )

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src_path = td_path / "test_mt19937_runif.f90"
        exe_path = td_path / "test_mt19937_runif.exe"
        src_path.write_text(program_text, encoding="utf-8")

        build = subprocess.run(
            [
                "gfortran",
                str(UPSTREAM_MT),
                str(WRAPPER),
                str(src_path),
                "-o",
                str(exe_path),
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        assert build.returncode == 0, build.stdout + build.stderr

        run = subprocess.run(
            [str(exe_path)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        assert run.returncode == 0, run.stdout + run.stderr
        assert run.stdout.strip()
