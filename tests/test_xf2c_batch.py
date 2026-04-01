from __future__ import annotations

import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
BATCH_PATH = REPO_ROOT / "xf2c_batch.py"


def test_xf2c_batch_uses_manifest_and_limit(tmp_path: Path) -> None:
    xf2c_stub = tmp_path / "xf2c.py"
    xf2c_stub.write_text(
        "\n".join(
            [
                "import sys",
                "print('stub xf2c', sys.argv[1])",
                "raise SystemExit(0)",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (tmp_path / "a.f90").write_text("program a\nend program a\n", encoding="utf-8")
    (tmp_path / "b.f90").write_text("program b\nend program b\n", encoding="utf-8")
    (tmp_path / "manifest.txt").write_text("a.f90\nb.f90\n", encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(BATCH_PATH),
            "--xf2c",
            str(xf2c_stub),
            "--file-list",
            "manifest.txt",
            "--limit",
            "1",
        ],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[TEST] a.f90" in proc.stdout
    assert "[TEST] b.f90" not in proc.stdout
    assert "TOTAL=1 PASS=1 FAIL=0 SKIP=0" in proc.stdout


def test_xf2c_batch_positional_files_override_manifest(tmp_path: Path) -> None:
    xf2c_stub = tmp_path / "xf2c.py"
    xf2c_stub.write_text(
        "\n".join(
            [
                "import sys",
                "print('stub xf2c', sys.argv[1])",
                "raise SystemExit(0)",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (tmp_path / "a.f90").write_text("program a\nend program a\n", encoding="utf-8")
    (tmp_path / "b.f90").write_text("program b\nend program b\n", encoding="utf-8")
    (tmp_path / "manifest.txt").write_text("a.f90\n", encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(BATCH_PATH),
            "--xf2c",
            str(xf2c_stub),
            "--file-list",
            "manifest.txt",
            "b.f90",
        ],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[TEST] b.f90" in proc.stdout
    assert "[TEST] a.f90" not in proc.stdout
    assert "TOTAL=1 PASS=1 FAIL=0 SKIP=0" in proc.stdout


def test_xf2c_batch_expands_windows_style_glob_patterns(tmp_path: Path) -> None:
    xf2c_stub = tmp_path / "xf2c.py"
    xf2c_stub.write_text(
        "\n".join(
            [
                "import sys",
                "print('stub xf2c', sys.argv[1])",
                "raise SystemExit(0)",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (tmp_path / "a.f90").write_text("program a\nend program a\n", encoding="utf-8")
    (tmp_path / "b.f90").write_text("program b\nend program b\n", encoding="utf-8")
    (tmp_path / "note.txt").write_text("ignore me\n", encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(BATCH_PATH),
            "--xf2c",
            str(xf2c_stub),
            "*.f90",
        ],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[TEST] a.f90" in proc.stdout
    assert "[TEST] b.f90" in proc.stdout
    assert "[TEST] note.txt" not in proc.stdout
    assert "TOTAL=2 PASS=2 FAIL=0 SKIP=0" in proc.stdout


def test_xf2c_batch_quiet_runs_hides_successful_program_stdout(tmp_path: Path) -> None:
    xf2c_stub = tmp_path / "xf2c.py"
    xf2c_stub.write_text(
        "\n".join(
            [
                "print('Build (original-fortran): PASS')",
                "print('Run (original-fortran): PASS')",
                "print('fortran output line')",
                "print('Wrote temp_demo.c')",
                "print('Build (transformed-c): PASS')",
                "print('Run (transformed-c): PASS')",
                "print('c output line')",
                "raise SystemExit(0)",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (tmp_path / "a.f90").write_text("program a\nend program a\n", encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(BATCH_PATH),
            "--xf2c",
            str(xf2c_stub),
            "--quiet-runs",
            "a.f90",
        ],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "Wrote temp_demo.c" in proc.stdout
    assert "fortran output line" not in proc.stdout
    assert "c output line" not in proc.stdout


def test_xf2c_batch_quiet_runs_preserves_failure_output(tmp_path: Path) -> None:
    xf2c_stub = tmp_path / "xf2c.py"
    xf2c_stub.write_text(
        "\n".join(
            [
                "print('Build (original-fortran): PASS')",
                "print('Run (original-fortran): FAIL (exit 1)')",
                "print('debug line')",
                "raise SystemExit(1)",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (tmp_path / "a.f90").write_text("program a\nend program a\n", encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(BATCH_PATH),
            "--xf2c",
            str(xf2c_stub),
            "--quiet-runs",
            "a.f90",
        ],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "Run (original-fortran): FAIL (exit 1)" in proc.stdout
    assert "debug line" in proc.stdout
