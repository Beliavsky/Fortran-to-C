from __future__ import annotations

import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def test_program_batch_reads_manifest_and_targets_last_source(tmp_path: Path) -> None:
    manifest_dir = tmp_path / "corpus"
    manifest_dir.mkdir()
    (manifest_dir / "kind.f90").write_text("module kind_mod\nimplicit none\nend module kind_mod\n")
    (manifest_dir / "helper.f90").write_text("module helper_mod\nimplicit none\nend module helper_mod\n")
    (manifest_dir / "xdemo.f90").write_text("program demo\nimplicit none\nprint *, 'ok'\nend program demo\n")
    (manifest_dir / "demo_files.txt").write_text("kind.f90\nhelper.f90\nxdemo.f90\n")

    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "xf2c_program_batch.py"),
            str(manifest_dir / "demo_files.txt"),
            "--xf2c",
            str(REPO_ROOT / "xf2c.py"),
            "--opts=--compile",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[TARGET] xdemo.f90" in proc.stdout
    assert "[BUILD] gfortran kind.f90 helper.f90 xdemo.f90" in proc.stdout
    assert "TOTAL=1 PASS=1 FAIL=0 SKIP=0" in proc.stdout
    assert "Total time:" in proc.stdout
    assert "Time compiling Fortran:" in proc.stdout
    assert "Time transpiling:" in proc.stdout
    assert "Time compiling C:" in proc.stdout


def test_program_batch_combines_manifest_sources_for_xf2c(tmp_path: Path) -> None:
    manifest_dir = tmp_path / "corpus"
    manifest_dir.mkdir()
    (manifest_dir / "m.f90").write_text(
        "module m\nimplicit none\ncontains\nfunction thrice(x) result(y)\nreal, intent(in) :: x\nreal :: y\ny = 3*x\nend function thrice\nend module m\n"
    )
    (manifest_dir / "xthrice.f90").write_text(
        "program xthrice\nuse m\nimplicit none\nprint *, thrice(10.0)\nend program xthrice\n"
    )
    (manifest_dir / "demo_files.txt").write_text("m.f90\nxthrice.f90\n")

    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "xf2c_program_batch.py"),
            str(manifest_dir / "demo_files.txt"),
            "--xf2c",
            str(REPO_ROOT / "xf2c.py"),
            "--opts=--compile",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[BUILD] gfortran m.f90 xthrice.f90" in proc.stdout
    assert "[PASS] demo_files.txt" in proc.stdout


def test_program_batch_shows_failure_output_by_default_and_can_hide_it(tmp_path: Path) -> None:
    manifest_dir = tmp_path / "corpus"
    manifest_dir.mkdir()
    (manifest_dir / "xbroken.f90").write_text("program broken\nimplicit none\nprint *, missing\nend program broken\n")
    (manifest_dir / "broken_files.txt").write_text("xbroken.f90\n")

    proc_show = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "xf2c_program_batch.py"),
            str(manifest_dir / "broken_files.txt"),
            "--xf2c",
            str(REPO_ROOT / "xf2c.py"),
            "--opts=--compile --max-errors 3",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc_show.returncode != 0
    shown = proc_show.stdout + proc_show.stderr
    assert "[FAIL] broken_files.txt" in shown
    assert "undeclared identifier 'missing'" in shown

    proc_hide = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "xf2c_program_batch.py"),
            str(manifest_dir / "broken_files.txt"),
            "--xf2c",
            str(REPO_ROOT / "xf2c.py"),
            "--opts=--compile --max-errors 3",
            "--no-fail-output",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc_hide.returncode != 0
    hidden = proc_hide.stdout + proc_hide.stderr
    assert "[FAIL] broken_files.txt" in hidden
    assert "undeclared identifier 'missing'" not in hidden
