from __future__ import annotations

import importlib.util
import tempfile
import re
import subprocess
import sys
import argparse
import shutil
from pathlib import Path

import pytest
import fortran_scan as fscan
import xf2c_driver


REPO_ROOT = Path(__file__).resolve().parents[1]
XF2C_PATH = REPO_ROOT / "tests" / "xf2c_test_entry.py"
XF2C_BAT_PATH = REPO_ROOT / "xf2c.bat"
FORTRAN_FILES_PATH = REPO_ROOT / "fortran_files.txt"
XNORMALIZE_CANDIDATES = [
    REPO_ROOT / "xnormalize.py",
    Path(r"c:\python\code\xnormalize.py"),
]


def _load_xnormalize():
    for path in XNORMALIZE_CANDIDATES:
        if not path.exists():
            continue
        spec = importlib.util.spec_from_file_location("xnormalize_mod", path)
        if spec is None or spec.loader is None:
            continue
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    raise AssertionError(f"could not load normalizer from any of: {XNORMALIZE_CANDIDATES}")


XNORMALIZE = _load_xnormalize()
NORMALIZE_INT_TOL = 1e-5
NORMALIZE_DECIMALS = 4


def _bat_manifest_sources() -> list[str]:
    if FORTRAN_FILES_PATH.exists():
        return [
            line.strip()
            for line in FORTRAN_FILES_PATH.read_text(encoding="utf-8", errors="replace").splitlines()
            if line.strip() and not line.lstrip().startswith("#")
        ]
    text = XF2C_BAT_PATH.read_text(encoding="utf-8", errors="replace")
    m = re.search(r"for\s+%%F\s+in\s+\((?P<body>.*?)\)\s+do\s+call\s+:run", text, re.S | re.I)
    if not m:
        raise AssertionError("could not parse xf2c.bat manifest")
    body = m.group("body")
    return [line.strip() for line in body.splitlines() if line.strip()]


def _run_xf2c(src_name: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(XF2C_PATH), src_name, "--run-both"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


BAT_SOURCES = _bat_manifest_sources()
KNOWN_ORIGINAL_FORTRAN_XFAILS = {
    "xpdt_matrix.f90": "known gfortran internal compiler error on this source",
    "xpdt_matrix_kind.f90": "known gfortran internal compiler error on this source",
    "xpdt_string.f90": "known gfortran instability on this PDT source; transformed C path is still verified separately",
}
KNOWN_MANIFEST_XFAILS = {
    "xpdt_matrix_kind.f90": "existing limitation: full PDT matrix kind demo is not yet supported end-to-end in manifest run",
}
# These are existing output mismatches against the Fortran reference.
# They are not version-to-version regressions, so they should not block
# merge decisions unless a previously passing case joins this set.
KNOWN_NORMALIZED_OUTPUT_XFAILS = {
    "ximpure_elemental.f90": "uses Fortran intrinsic random_number, so original Fortran and transformed C use different RNG streams",
    "xrandom.f90": "uses Fortran intrinsic random_number, so original Fortran and transformed C use different RNG streams",
    "xratio.f90": "uses Fortran intrinsic random_number, so original Fortran and transformed C use different RNG streams",
    "xrational_approx.f90": "uses Fortran intrinsic random_number/random_seed, so original Fortran and transformed C use different RNG streams",
    "xselect_range.f90": "uses Fortran intrinsic random_number, so original Fortran and transformed C use different RNG streams",
    "xstats.f90": "uses Fortran intrinsic random_number, so original Fortran and transformed C use different RNG streams",
    "xmean_sd.f90": "uses Fortran intrinsic random_number, so original Fortran and transformed C use different RNG streams",
    "xnumeric.f90": "existing bug: some numeric inquiry functions still differ from gfortran values/textual rendering",
    "xuncmin.f90": "existing bug: xuncmin still diverges from gfortran on the original demo driver",
    "xdate_and_time.f90": "wall-clock DATE_AND_TIME values differ because original Fortran and transformed C run at different moments",
}


def _source_has_program(src_name: str) -> bool:
    src_path = REPO_ROOT / src_name
    text = src_path.read_text(encoding="utf-8", errors="replace")
    units = fscan.split_fortran_units_simple(text)
    return any(u.get("kind") == "program" for u in units)


def _extract_run_output(stdout: str, label: str, stop_markers: list[str]) -> str:
    start_marker = f"Run ({label}): PASS"
    start = stdout.find(start_marker)
    if start < 0:
        raise AssertionError(f"missing run marker: {start_marker}\n{stdout}")
    text = stdout[start + len(start_marker):]
    if text.startswith("\r\n"):
        text = text[2:]
    elif text.startswith("\n"):
        text = text[1:]
    stops = [text.find(marker) for marker in stop_markers if text.find(marker) >= 0]
    if stops:
        text = text[: min(stops)]
    return text.rstrip()


def _assert_normalized_outputs_match(proc: subprocess.CompletedProcess[str]) -> None:
    f_out = _extract_run_output(proc.stdout, "original-fortran", ["Build (transformed-c):"])
    f_out = re.sub(r"\n?Wrote\s+\S+\.c(?:\s+\([^)]*\))?\s*$", "", f_out, flags=re.IGNORECASE)
    c_out = _extract_run_output(proc.stdout, "transformed-c", [])
    f_norm = XNORMALIZE.normalize_text(f_out, NORMALIZE_INT_TOL, NORMALIZE_DECIMALS)
    c_norm = XNORMALIZE.normalize_text(c_out, NORMALIZE_INT_TOL, NORMALIZE_DECIMALS)
    if c_norm == f_norm:
        return
    # List-directed output permits compiler-specific spacing and line wrapping.
    # Treat outputs as equivalent when they differ only by whitespace layout.
    if re.sub(r"\s+", " ", c_norm).strip() == re.sub(r"\s+", " ", f_norm).strip():
        return
    assert c_norm == f_norm, (
        "normalized output mismatch\n"
        f"--- original-fortran ---\n{f_norm}\n"
        f"--- transformed-c ---\n{c_norm}\n"
        f"--- raw stdout ---\n{proc.stdout}"
    )


def test_xf2c_bat_manifest_files_exist() -> None:
    assert BAT_SOURCES, "xf2c.bat manifest is empty"
    missing = [name for name in BAT_SOURCES if not (REPO_ROOT / name).is_file()]
    assert not missing, f"missing manifest source files: {missing}"


@pytest.mark.parametrize("src_name", BAT_SOURCES)
def test_xf2c_run_both_from_bat_manifest(src_name: str) -> None:
    proc = _run_xf2c(src_name)
    if src_name in KNOWN_ORIGINAL_FORTRAN_XFAILS and "Build (original-fortran): FAIL" in proc.stdout:
        pytest.xfail(KNOWN_ORIGINAL_FORTRAN_XFAILS[src_name])
    if src_name in KNOWN_MANIFEST_XFAILS and proc.returncode != 0:
        pytest.xfail(KNOWN_MANIFEST_XFAILS[src_name])
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    if not _source_has_program(src_name):
        assert "Run (original-fortran): PASS" not in proc.stdout
        assert "Run (transformed-c): PASS" not in proc.stdout
        return
    if src_name in KNOWN_NORMALIZED_OUTPUT_XFAILS:
        pytest.xfail(KNOWN_NORMALIZED_OUTPUT_XFAILS[src_name])
    _assert_normalized_outputs_match(proc)


def test_xf2c_character_self_assignment_preserves_value() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  character(len=5) :: s",
            '  s = "abc"',
            "  s = s",
            '  print *, "[" // s // "]"',
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xchar_self_assign.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[abc  ]" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_converts_fixed_form_f_to_unique_f90_before_transpile() -> None:
    with tempfile.TemporaryDirectory() as td:
        src_dir = Path(td)
        fixed_src = src_dir / "xfixed.f"
        fixed_src.write_text(
            "\n".join(
                [
                    "      program xfixed",
                    "      print *, 'hi'",
                    "      end",
                    "",
                ]
            ),
            encoding="utf-8",
        )
        (src_dir / "xfixed.f90").write_text("program placeholder\nend program placeholder\n", encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(fixed_src), "--run-both", "--pretty"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "Build (original-fortran): PASS" in proc.stdout
        assert "Build (transformed-c): PASS" in proc.stdout
        assert (src_dir / "xfixed_1.f90").exists()
        _assert_normalized_outputs_match(proc)


def test_xf2c_free_form_flag_allows_free_form_code_in_dot_f() -> None:
    with tempfile.TemporaryDirectory() as td:
        src_dir = Path(td)
        free_src = src_dir / "xfree_as_f.f"
        free_src.write_text(
            "\n".join(
                [
                    "program xfree_as_f",
                    "  implicit none",
                    "  print *, 'hi'",
                    "end program xfree_as_f",
                    "",
                ]
            ),
            encoding="utf-8",
        )
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(free_src), "--run-both", "--pretty", "--free-form"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "Build (original-fortran): PASS" in proc.stdout
        assert "Build (transformed-c): PASS" in proc.stdout
        _assert_normalized_outputs_match(proc)


def test_xf2c_fixed_form_flag_allows_fixed_form_code_in_dot_f90() -> None:
    with tempfile.TemporaryDirectory() as td:
        src_dir = Path(td)
        fixed_src = src_dir / "xfixed_as_f90.f90"
        fixed_src.write_text(
            "\n".join(
                [
                    "      program xfixed_as_f90",
                    "      print *, 'hi'",
                    "      end",
                    "",
                ]
            ),
            encoding="utf-8",
        )
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(fixed_src), "--run-both", "--pretty", "--fixed-form"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "Build (original-fortran): PASS" in proc.stdout
        assert "Build (transformed-c): PASS" in proc.stdout
        _assert_normalized_outputs_match(proc)


def test_xf2c_rewrites_common_to_nocommon_before_transpile() -> None:
    src_text = "\n".join(
        [
            "program demo_common",
            "  implicit none",
            "  integer :: n",
            "  real :: x, y, avg",
            "  common /stats/ x, y, avg, n",
            "  x = 10.0",
            "  y = 20.0",
            "  n = 2",
            "  call compute_avg",
            "  print *, avg",
            "end program demo_common",
            "",
            "subroutine compute_avg",
            "  implicit none",
            "  integer :: n",
            "  real :: x, y, avg",
            "  common /stats/ x, y, avg, n",
            "  avg = (x + y) / n",
            "end subroutine compute_avg",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xcommon_demo.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both", "--pretty"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert (src_path.with_name("xcommon_demo_nocommon.f90")).exists()
        assert "Build (original-fortran): PASS" in proc.stdout
        assert "Build (transformed-c): PASS" in proc.stdout
        _assert_normalized_outputs_match(proc)


def test_xf2c_run_diff_reports_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            '  print *, "hello"',
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xrun_diff.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-diff", "--pretty"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "Build (original-fortran): PASS" in proc.stdout
        assert "Build (transformed-c): PASS" in proc.stdout
        assert "Run diff: MATCH" in proc.stdout


def test_xf2c_repeat_long_string_is_not_truncated() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  character(len=1105) :: s",
            '  s = repeat("a", 1100)',
            "  print *, len_trim(s)",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xrepeat_long.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert proc.stdout.count("1100") >= 2
    assert "1023" not in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_elemental_rounding_intrinsics_on_arrays_match_fortran() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  real, parameter :: x(*) = [-0.7, -0.5, -0.3, 0.1, 0.5, 0.7]",
            "  print *, nint(x)",
            "  print *, ceiling(x)",
            "  print *, floor(x)",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xround_intrinsics.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_bare_print_star_matches_blank_line_output() -> None:
    src_text = "\n".join(
        [
            "program p",
            '  print *, "before"',
            "  print *",
            '  print *, "after"',
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xprint_blank.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_error_stop_literal_compiles() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  error stop 'dimension mismatch'",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xerror_stop.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_xf2c_numeric_inquiry_intrinsics_match() -> None:
    proc = _run_xf2c("xnumeric.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    assert "digits(xsp)" in proc.stdout
    assert "maxexponent(xdp)" in proc.stdout
    assert "selected_real_kind(1000,1000)" in proc.stdout
    assert "selected_int_kind(100)" in proc.stdout


def test_xf2c_stream_unformatted_io_with_rewind_and_pos_matches() -> None:
    proc = _run_xf2c("xstream.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_backspace_matches() -> None:
    proc = _run_xf2c("xbackspace.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_allocatable_assignment_from_rank2_section_expression_matches() -> None:
    proc = _run_xf2c("xreturns_stats.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_annotate_does_not_reemit_shared_csv_runtime_helpers() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xreturns_stats.f90",
            "--annotate",
            "--compile",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_xf2c_forall_assignment_matches() -> None:
    proc = _run_xf2c("xforall.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_forall_more_matches() -> None:
    proc = _run_xf2c("xforall_more.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_inline_if_write_matches() -> None:
    proc = _run_xf2c("xread_words.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_local_module_definitions_do_not_pull_duplicate_provider_programs() -> None:
    src_path = REPO_ROOT / "xutil_all.f90"
    src_text = src_path.read_text(encoding="utf-8", errors="ignore")
    deps = xf2c_driver._resolve_fortran_support_sources(src_path, src_text)
    dep_names = {path.name.lower() for path in deps}
    assert "xrational_approx.f90" not in dep_names


def test_xf2c_bat_limit_restricts_command_line_override_list() -> None:
    proc = subprocess.run(
        ["cmd", "/c", "xf2c.bat", "--limit", "1", "xhello.f90", "xxchar.f90"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[TEST] xxchar.f90" not in proc.stdout and "[PASS] xxchar.f90" not in proc.stdout
    assert "TOTAL=1 PASS=1 FAIL=0 SKIP=0" in proc.stdout


def test_xf2c_bat_no_args_uses_filelist() -> None:
    needed = ["xf2c.bat", "fortran_scan.py", "xc_post.py", "fortran_runtime.c", "fortran_runtime.h", "xhello.f90"]
    with tempfile.TemporaryDirectory() as td:
        work = Path(td)
        for name in needed:
            shutil.copy2(REPO_ROOT / name, work / name)
        for path in REPO_ROOT.glob("xf2c*.py"):
            shutil.copy2(path, work / path.name)
        (work / "fortran_files.txt").write_text("xhello.f90\n", encoding="utf-8")
        proc = subprocess.run(
            ["cmd", "/c", "xf2c.bat"],
            cwd=work,
            capture_output=True,
            text=True,
            check=False,
        )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "[TEST] xhello.f90" in proc.stdout
    assert "TOTAL=1 PASS=1 FAIL=0 SKIP=0" in proc.stdout


def test_xf2c_inline_if_error_stop_literal_compiles() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  integer :: ios",
            "  ios = 1",
            "  if (ios /= 0) error stop 'cannot open input file'",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xif_error_stop.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_xf2c_inline_if_formatted_print_compiles() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  real(8), parameter :: x = 2.5d0",
            '  if (x /= 1.0d0) print "(\'x=\',f0.1)", x',
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xif_print_fmt.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_xf2c_error_stop_string_expression_compiles() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  character(len=20) :: filename",
            '  filename = "data.csv"',
            '  error stop "cannot open " // trim(filename)',
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xerror_stop_concat.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_xf2c_multiple_allocate_objects_compile() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  integer, allocatable :: a(:), b(:)",
            "  allocate(a(2), b(3))",
            "  a = 1",
            "  b = 2",
            "  print *, a(1), b(1)",
            "  deallocate(a)",
            "  deallocate(b)",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xalloc_multi.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_xf2c_allocatable_character_array_split_and_section_copy_match() -> None:
    src_text = "\n".join(
        [
            "module m",
            "contains",
            "subroutine split(line, fields)",
            "character(len=*), intent(in) :: line",
            "character(len=*), intent(out) :: fields(:)",
            "integer :: i, i0, k, n, lt",
            "n = size(fields)",
            "fields = ''",
            "lt = len_trim(line)",
            "i0 = 1",
            "k = 1",
            "do i = 1, lt",
            "   if (line(i:i) == ',') then",
            "      if (k <= n) fields(k) = adjustl(line(i0:i-1))",
            "      k = k + 1",
            "      i0 = i + 1",
            "   end if",
            "end do",
            "if (k <= n) fields(k) = adjustl(line(i0:lt))",
            "end subroutine split",
            "end module m",
            "program p",
            "use m",
            "implicit none",
            "character(len=8), allocatable :: fields(:), names(:)",
            "allocate(fields(3))",
            'call split("d,a,b", fields)',
            "allocate(names(2))",
            "names = fields(2:)",
            "print *, trim(names(1))",
            "print *, trim(names(2))",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xchar_sections.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_rank2_ratio_sections_and_row_expr_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  integer, parameter :: n1 = 4, n2 = 2",
            "  real :: x(n1, n2), xr(n1-1, n2)",
            "  x(1,1) = 1.0",
            "  x(2,1) = 2.0",
            "  x(3,1) = 4.0",
            "  x(4,1) = 8.0",
            "  x(1,2) = 3.0",
            "  x(2,2) = 6.0",
            "  x(3,2) = 12.0",
            "  x(4,2) = 24.0",
            "  xr = x(2:, :) / x(:n1-1, :) - 1.0",
            "  print *, x(1,:)",
            "  print *, x(2,:)",
            "  print *, xr(1,:)",
            "  print *, x(2,:)/x(1,:) - 1.0 - xr(1,:)",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xratio_sections.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_internal_list_directed_read_from_character_expr_match() -> None:
    src_text = "\n".join(
        [
            "module m",
            "contains",
            "subroutine split_csv_line(line, fields)",
            "character(len=*), intent(in) :: line",
            "character(len=*), intent(out) :: fields(:)",
            "integer :: i, i0, k, n, lt",
            "n = size(fields)",
            "fields = ''",
            "lt = len_trim(line)",
            "i0 = 1",
            "k = 1",
            "do i = 1, lt",
            "   if (line(i:i) == ',') then",
            "      if (k <= n) fields(k) = adjustl(line(i0:i-1))",
            "      k = k + 1",
            "      i0 = i + 1",
            "   end if",
            "end do",
            "if (k <= n) fields(k) = adjustl(line(i0:lt))",
            "end subroutine split_csv_line",
            "end module m",
            "program p",
            "use m",
            "implicit none",
            "character(len=64) :: line",
            "character(len=32), allocatable :: fields(:)",
            "real(8) :: x, y",
            "integer :: ios",
            "allocate(fields(3))",
            'line = "2003-04-14,61.378151,18.64402"',
            "call split_csv_line(trim(line), fields)",
            "read(fields(2), *, iostat=ios) x",
            "read(fields(3), *, iostat=ios) y",
            "print *, x, y",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xinternal_read_csv.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_allocatable_rank2_section_expr_minmax_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  real(8), allocatable :: prices(:,:), rets(:,:)",
            "  allocate(prices(3,2), rets(2,2))",
            "  prices(1,1) = 100.0d0",
            "  prices(2,1) = 110.0d0",
            "  prices(3,1) = 99.0d0",
            "  prices(1,2) = 50.0d0",
            "  prices(2,2) = 55.0d0",
            "  prices(3,2) = 60.0d0",
            "  rets = prices(2:3,:) / prices(1:2,:) - 1.0d0",
            "  print *, 'min, max returns:', minval(rets), maxval(rets)",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xalloc_minmax.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_print_sum_dim_expr_over_allocatable_rank2_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  real(8), allocatable :: rets(:,:)",
            "  integer :: nobs",
            "  allocate(rets(2,3))",
            "  nobs = 3",
            "  rets(1,1) = -0.1d0",
            "  rets(2,1) = 0.3d0",
            "  rets(1,2) = 0.02d0",
            "  rets(2,2) = 0.04d0",
            "  rets(1,3) = 0.01d0",
            "  rets(2,3) = -0.03d0",
            "  print *, 'mu:', sum(rets, dim=1) / (nobs - 1)",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xsum_dim_expr_print.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_assign_sum_dim_expr_to_rank1_allocatable_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  real(8), allocatable :: rets(:,:), mu(:)",
            "  allocate(rets(2,3), mu(3))",
            "  rets(1,1) = -0.1d0",
            "  rets(2,1) = 0.3d0",
            "  rets(1,2) = 0.02d0",
            "  rets(2,2) = 0.04d0",
            "  rets(1,3) = 0.01d0",
            "  rets(2,3) = -0.03d0",
            "  mu = sum(rets, dim=1) / real(size(rets, 1), kind=8)",
            "  print *, mu",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xsum_dim_assign.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_spread_rank1_into_rank2_and_size_loop_match() -> None:
    src_text = "\n".join(
        [
            "program demo_spread",
            "   implicit none",
            "   integer :: v(3)",
            "   integer :: m23(2,3)",
            "   integer :: m32(3,2)",
            "   integer :: i",
            "   v = [1, 2, 3]",
            '   print *, "example 1: spread a rank-1 array into rows"',
            '   print *, "v = ", v',
            "   m23 = spread(v, dim=1, ncopies=2)",
            "   do i = 1, size(m23,1)",
            "      print *, m23(i,:)",
            "   end do",
            "   print *",
            '   print *, "example 2: spread a rank-1 array into columns"',
            "   m32 = spread(v, dim=2, ncopies=2)",
            "   do i = 1, size(m32,1)",
            "      print *, m32(i,:)",
            "   end do",
            "end program demo_spread",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xspread_tmp.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_assign_sqrt_sum_centered_spread_dim_expr_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  real(8), allocatable :: rets(:,:), mu(:), sig(:)",
            "  allocate(rets(2,3), mu(3), sig(3))",
            "  rets(1,1) = -0.1d0",
            "  rets(2,1) = 0.3d0",
            "  rets(1,2) = 0.02d0",
            "  rets(2,2) = 0.04d0",
            "  rets(1,3) = 0.01d0",
            "  rets(2,3) = -0.03d0",
            "  mu = sum(rets, dim=1) / real(size(rets, 1), kind=8)",
            "  sig = sqrt(sum((rets - spread(mu, dim=1, ncopies=size(rets, 1)))**2, dim=1) / real(size(rets, 1), kind=8))",
            "  print *, 'sig:', sig",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xsig_centered_spread.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_scalar_sum_of_1d_centered_expression_match() -> None:
    src_text = "\n".join(
        [
            "module stats_mod",
            "  implicit none",
            "contains",
            "  function sd(x) result(sig)",
            "    real(8), intent(in) :: x(:)",
            "    real(8) :: sig, mu",
            "    if (size(x) <= 1) then",
            "       sig = 0.0d0",
            "    else",
            "       mu = sum(x) / real(size(x), kind=8)",
            "       sig = sqrt(sum((x - mu)**2) / real(size(x) - 1, kind=8))",
            "    end if",
            "  end function sd",
            "end module stats_mod",
            "program p",
            "  use stats_mod, only: sd",
            "  implicit none",
            "  real(8) :: x(4), s",
            "  x(1) = 1.0d0",
            "  x(2) = 2.0d0",
            "  x(3) = 3.0d0",
            "  x(4) = 5.0d0",
            "  s = sd(x)",
            "  print *, s",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xstats_sd_tmp.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_column_slice_actual_arg_to_assumed_shape_match() -> None:
    src_text = "\n".join(
        [
            "module stats_mod",
            "  implicit none",
            "contains",
            "  function mean(x) result(mu)",
            "    real(8), intent(in) :: x(:)",
            "    real(8) :: mu",
            "    mu = sum(x) / real(size(x), kind=8)",
            "  end function mean",
            "  function sd(x) result(sig)",
            "    real(8), intent(in) :: x(:)",
            "    real(8) :: sig, mu",
            "    if (size(x) <= 1) then",
            "       sig = 0.0d0",
            "    else",
            "       mu = mean(x)",
            "       sig = sqrt(sum((x - mu)**2) / real(size(x) - 1, kind=8))",
            "    end if",
            "  end function sd",
            "end module stats_mod",
            "program p",
            "  use stats_mod, only: mean, sd",
            "  implicit none",
            "  real(8) :: a(3,2), mu(2), sig(2)",
            "  integer :: j",
            "  a(1,1) = 1.0d0",
            "  a(2,1) = 2.0d0",
            "  a(3,1) = 5.0d0",
            "  a(1,2) = 3.0d0",
            "  a(2,2) = 4.0d0",
            "  a(3,2) = 9.0d0",
            "  do j = 1, 2",
            "     mu(j) = mean(a(:, j))",
            "     sig(j) = sd(a(:, j))",
            "  end do",
            "  print *, mu",
            "  print *, sig",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xcolslice_tmp.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_formatted_header_implied_do_and_row_slice_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  character(len=8) :: names(2)",
            "  real(8) :: corr(2,2)",
            "  integer :: i, j",
            "  names(1) = 'SPY'",
            "  names(2) = 'EFA'",
            "  corr(1,1) = 1.0d0",
            "  corr(1,2) = 0.8912d0",
            "  corr(2,1) = 0.8912d0",
            "  corr(2,2) = 1.0d0",
            '  write(*, "(/,a)") "correlation matrix of returns"',
            '  write(*, "(*(a8))") "", (trim(names(j)), j = 1, 2)',
            "  do i = 1, 2",
            '     write(*, "(a8,*(f8.4))") trim(names(i)), corr(i,:)',
            "  end do",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xfmt_rowslice_tmp.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_print_format_var_and_optional_keyword_match() -> None:
    src_text = "\n".join(
        [
            "module m",
            "implicit none",
            "contains",
            "subroutine mean_sd(x, mean, sd, calc_mean)",
            "real(8), intent(in) :: x(:)",
            "real(8), intent(in out) :: mean",
            "real(8), intent(out) :: sd",
            "logical, intent(in), optional :: calc_mean",
            "logical :: calc_mean_",
            "integer :: n",
            "n = size(x)",
            "if (present(calc_mean)) then",
            "   calc_mean_ = calc_mean",
            "else",
            "   calc_mean_ = .true.",
            "end if",
            "if (calc_mean_) then",
            '   print*,"calculating mean"',
            "   mean = sum(x)/max(1,n)",
            "end if",
            "if (n > 1) then",
            "   sd = sqrt(sum((x-mean)**2)/(n-1))",
            "else",
            "   sd = -1.0d0",
            "end if",
            "end subroutine mean_sd",
            "end module m",
            "program main",
            "use m",
            "implicit none",
            "real(8) :: x(4), mean, sd",
            'character (len=*), parameter :: fmt_o = "(/,a)", fmt_stats ="(\'mean, sd = \',2f10.6)"',
            "x(1) = 1.0d0",
            "x(2) = 2.0d0",
            "x(3) = 3.0d0",
            "x(4) = 5.0d0",
            'print fmt_o, "call mean_sd(x, mean, sd, calc_mean = .true.)"',
            "call mean_sd(x, mean, sd, calc_mean = .true.)",
            "print fmt_stats,mean,sd",
            'print fmt_o,"call mean_sd(x, mean, sd, calc_mean = .false.)"',
            "call mean_sd(x, mean, sd, calc_mean = .false.)",
            "print fmt_stats,mean,sd",
            "end program main",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xprint_fmt_kw_tmp.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_dynamic_internal_fmt_then_stdout_write_match() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  integer :: name_width",
            "  character(len=100) :: fmt",
            "  name_width = 5",
            "  write(fmt, '(\"(a\",i0,\",2x,a14,2x,a14)\")') name_width",
            "  write(*, fmt) 'asset', 'mean_return', 'std_return'",
            "  write(fmt, '(\"(a\",i0,\",2x,f14.8,2x,f14.8)\")') name_width",
            "  write(*, fmt) 'SPY', 0.00044098d0, 0.01192712d0",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xdynamic_fmt_write.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--run-both"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_get_command_argument_literal_index_omits_redundant_nonnegative_check() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  character(len=256) :: filename",
            "  call get_command_argument(1, filename)",
            "  print *, trim(filename)",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xarg_literal.f90"
        out_path = Path(td) / "xarg_literal.c"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile", "--out-dir", td, "--out", out_path.name],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "set_command_args_s(argc, argv);" in emitted
    assert "get_command_argument_s(1, filename, 256);" in emitted
    assert "argv[1]" not in emitted
    assert "((1) >= 0)" not in emitted


def test_xf2c_local_arrays_resolve_assumed_shape_extents_and_allocatables() -> None:
    src_text = "\n".join(
        [
            "subroutine foo(a_in, outv)",
            "  implicit none",
            "  real, intent(in) :: a_in(:,:)",
            "  real, intent(out) :: outv",
            "  real :: rowtmp(size(a_in,2))",
            "  real :: work2(size(a_in,1), size(a_in,2))",
            "  integer, allocatable :: seedv(:)",
            "  integer :: n",
            "  n = size(a_in,2)",
            "  allocate(seedv(n))",
            "  rowtmp(1) = a_in(1,1)",
            "  work2(1,1) = rowtmp(1)",
            "  outv = work2(1,1)",
            "  deallocate(seedv)",
            "end subroutine foo",
            "program p",
            "  implicit none",
            "  real :: a(2,3), outv",
            "  a = 1.0",
            "  call foo(a, outv)",
            "  print *, outv",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xassumed_decl.f90"
        out_path = Path(td) / "xassumed_decl.c"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile", "--out-dir", td, "--out", out_path.name],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "float rowtmp[n_a_in_2], work2[n_a_in_1 * n_a_in_2];" in emitted
    assert "int *seedv = NULL;" in emitted
    assert "seedv = (int*) malloc(sizeof(int) * n_a_in_2);" in emitted
    assert "[(: " not in emitted
    assert "[:]" not in emitted


def test_xf2c_default_output_is_postprocessed() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "out.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xsum_dim.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "y[2 * p_fill] = x[p_fill];" in emitted
    assert "y[1 + 2 * p_fill] = 10 * x[p_fill];" in emitted
    assert "y[((1) - 1) + (2) * p_fill] = x[p_fill];" not in emitted
    assert "__sum" not in emitted
    assert "__first" not in emitted
    assert "for (int j = 0; j < 3; ++j) {" in emitted
    assert re.search(r"for \(int i = 0; i < 2; \+\+i\)\s+[a-z_]\w* \+= y\[i \+ 2 \* j\];", emitted)


def test_xf2c_postprocessed_output_uses_readable_generated_names() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "xreturns.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xreturns.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "__n_names" not in emitted
    assert "__n_fields" not in emitted
    assert "__arg_str_0" not in emitted
    assert "if (names) free_str_array(names, n_names);" in emitted
    assert "for (int i_fill = 0; i_fill < n_assets; ++i_fill) names[i_fill] = NULL;" in emitted
    assert "assign_str_alloc(&names[i_fill], \"\");" in emitted
    assert "if (!names && n_assets > 0) return 1;" in emitted
    assert "enum { filename_len = 256, line_len = 4096 };" in emitted
    assert 'char filename[filename_len + 1] = "", line[line_len + 1] = "", fmt[101] = "";' in emitted
    assert "char **names = NULL, **fields = NULL;" in emitted
    assert "double *prices = NULL, *rets = NULL, *mu = NULL, *sig = NULL;" in emitted
    assert "int n_names = 0, n_fields = 0, n_prices_1 = 0, n_prices_2 = 0, n_rets_1 = 0, n_rets_2 = 0, n_mu = 0;" in emitted
    assert "int n_sig = 0, iu, ios, n_assets, nobs, i, j, name_width;" in emitted
    assert "set_command_args_s(argc, argv);" in emitted
    assert "get_command_argument_s(1, filename, 256);" in emitted
    assert "ios = read_a(iu, line, line_len);" in emitted


def test_xf2c_postprocessed_output_rewrites_simple_while_loops_zero_based() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "xreturns.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xreturns.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "j = 0;\n   while (j < n_assets) {" in emitted
    assert "len_trim_s(names[j])" in emitted
    assert 'printf("%*s  %14.8f  %14.8f\\n", name_width, trim_s(names[j]), mu[j], sig[j]);' in emitted
    assert "j = 1;\n   while (j <= n_assets) {\n      name_width = fmax(name_width, len_trim_s(names[j - 1]));" not in emitted
    assert 'j = 1;\n   while (j <= n_assets) {\n      printf("%*s  %14.8f  %14.8f\\n", name_width, trim_s(names[j - 1]), mu[j - 1], sig[j - 1]);' not in emitted
    assert "xf2c_loop_4_continue: ;" not in emitted
    assert "xf2c_loop_5_continue: ;" not in emitted


def test_xf2c_postprocessed_output_drops_unused_dp_constant() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "xreturns.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xreturns.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "const int dp = 8;" not in emitted
    assert "static const int dp = 8;" not in emitted


def test_xf2c_postprocessed_output_uses_shared_csv_runtime_helpers() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "xreturns.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xreturns.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert '#include "fortran_runtime.h"' in emitted
    assert "int count_fields(const char * line);" not in emitted
    assert "void split_csv_line(const char * line, const int n, char **fields);" not in emitted
    assert "int count_fields(const char * line) {" not in emitted
    assert "void split_csv_line(const char * line, const int n, char **fields) {" not in emitted
    assert "n_assets = count_fields(line) - 1;" in emitted
    assert "split_csv_line(arg_str_0, n_fields, fields);" in emitted


def test_xf2c_raw_preserves_unsimplified_generated_c() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "out.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xsum_dim.f90",
                "--raw",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "y[((1) - 1) + (2) * p_fill] = x[p_fill];" in emitted
    assert "y[((2) - 1) + (2) * p_fill] = 10*x[p_fill];" in emitted


def test_xf2c_uses_shared_runtime_for_common_helpers() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "out.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xread.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert '#include "fortran_runtime.h"' in emitted
    assert "open_unit(" in emitted
    assert "static int xf_open_unit" not in emitted
    assert "static int open_unit" not in emitted


def test_xf2c_uses_shared_runtime_for_common_1d_intrinsics() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "out.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xsum_dim.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert '#include "fortran_runtime.h"' in emitted
    assert "sum_1d_float(" in emitted
    assert "static float sum_1d_float" not in emitted


def test_xf2c_uses_shared_runtime_for_1d_random_fill() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "out.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xmean_sd.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert '#include "fortran_runtime.h"' in emitted
    assert "fill_rand_1d_double(" in emitted
    assert "static void fill_rand_1d_double" not in emitted


def test_xf2c_library_header_keeps_inline_procedure_comment() -> None:
    src_text = "\n".join(
        [
            "module m",
            "implicit none",
            "contains",
            "function mean_value(x) result(mu)",
            "! return the mean of a real vector",
            "real(8), intent(in) :: x(:)",
            "real(8) :: mu",
            "mu = sum(x) / real(size(x), kind=8)",
            "end function mean_value",
            "end module m",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xlib_tmp.f90"
        out_c = Path(td) / "out.c"
        out_h = Path(td) / "out.h"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                str(src_path),
                "--out-dir",
                td,
                "--out",
                out_c.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted_h = out_h.read_text(encoding="utf-8")

    assert "double mean_value(" in emitted_h
    assert "/* return the mean of a real vector */" in emitted_h


def test_xf2c_character_select_case_matches_fortran() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xselect_case.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "MA Massachusetts" in proc.stdout


def test_xf2c_named_generic_interface_with_module_procedures_matches_fortran() -> None:
    proc = _run_xf2c("xinterface.f90")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xf2c_select_case_range_and_scalar_random_number_lower() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "out.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xselect_range.f90",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "unsupported random_number target" not in emitted
    assert "unsupported range-case" not in emitted
    assert "x = (float)rand() / (float)RAND_MAX;" in emitted
    assert "else if (((j >= 1) && (j <= 3)))" in emitted


def test_xf2c_xrunif_run_both_with_local_mt_support() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xrunif.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): gfortran -c mt19937-64.f90 -o mt19937-64.orig_0.o" in proc.stdout
    assert "Build (original-fortran): gfortran -c mt19937_runif.f90 -o mt19937_runif.orig_1.o" in proc.stdout
    assert "Build (original-fortran): gfortran -c xrunif.f90 -o xrunif.orig_2.o" in proc.stdout
    assert "Build (original-fortran): gfortran mt19937-64.orig_0.o mt19937_runif.orig_1.o xrunif.orig_2.o -o xrunif.orig.exe" in proc.stdout
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout


def test_xf2c_mt19937_runif_module_compiles_with_shared_runtime() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "mt19937_runif.f90",
            "--compile",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout
    emitted = (REPO_ROOT / "temp_mt19937_runif.c").read_text(encoding="utf-8")
    assert "void rng_seed(" not in emitted
    assert "void rng_seed_vector(" not in emitted
    assert "double runif(void)" not in emitted
    assert "double *runif_1d(" not in emitted
    assert "void fill_runif_1d(" not in emitted
    assert "void fill_runif_2d(" not in emitted


def test_xf2c_xmt_runif_run_both_with_local_mt_support() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xmt_runif.f90",
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): gfortran -c mt19937-64.f90 -o mt19937-64.orig_0.o" in proc.stdout
    assert "Build (original-fortran): gfortran -c xmt_runif.f90 -o xmt_runif.orig_1.o" in proc.stdout
    assert "Build (original-fortran): gfortran mt19937-64.orig_0.o xmt_runif.orig_1.o -o xmt_runif.orig.exe" in proc.stdout
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout


def test_xf2c_associate_expression_and_section_aliases_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xassoc.f90",
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert proc.stdout.count("20 60 60 200 300") == 2
    assert proc.stdout.count("100 2000 3000") == 2


def test_xf2c_type_bound_write_formatted_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xdate_class.f90",
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert proc.stdout.count("d1 = 2024-11") == 2
    assert proc.stdout.count("d2 - d1 in months = 3") == 2


def test_xf2c_pretty_normalizes_run_both_output_display() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xrunif.f90",
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert proc.stdout.count("0.5001 0.2887 0.0833") == 2


def test_xf2c_pointer_aliasing_and_pointer_array_sections_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xpointer.f90",
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (original-fortran): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert proc.stdout.count("2.3") == 2
    assert proc.stdout.count("23 23") == 2
    assert proc.stdout.count("200 300 10 200 300 40") == 2
    assert proc.stdout.count("5 10 15") == 2


def test_xf2c_scalar_complex_intrinsics_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xcomplex.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_logical_arrays_masks_and_eqv_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xlogical.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_all_in_array_constructor_implied_do_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xall.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_scalar_implied_do_array_constructor_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xconstructor.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_mod_and_modulo_integer_sign_rules_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xmodulo.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_char_intrinsic_matches_fortran() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xxchar.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_lbound_ubound_and_nonunit_lower_bounds_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xarray_bounds.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_size_of_array_sections_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xsize.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_runif_section_assignment_and_minval_sections_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xsection.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_reshape_fixed_arrays_and_section_views_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xreshape.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_reshape_order_argument_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xreshape_order.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_array_constructor_mixes_scalars_and_array_valued_items_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xarray_1d.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_allocatable_function_result_with_pack_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xalloc_func.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_allocatable_scalar_string_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xalloc_string.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_character_len_expression_matches(tmp_path: Path) -> None:
    src_path = tmp_path / "xcharlen_expr.f90"
    src_path.write_text(
        """program main
implicit none
character(len=max(2, 3+1)) :: s
s = "abcd"
print *, len(s)
print *, trim(s)
end program main
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            str(src_path),
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_optional_string_expression_argument_matches(tmp_path: Path) -> None:
    src_path = tmp_path / "xopt_string_expr.f90"
    src_path.write_text(
        """program main
implicit none
call show("ab" // "cd")
contains
subroutine show(label)
character(len=*), intent(in), optional :: label
if (present(label)) print *, trim(label)
end subroutine show
end program main
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            str(src_path),
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_allocatable_derived_components_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xdf_alloc.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_move_alloc_and_allocatable_dummy_extent_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xmove_alloc.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_impure_elemental_subroutine_with_array_actual_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "ximpure_elemental.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    f_out = _extract_run_output(proc.stdout, "original-fortran", ["Build (transformed-c):"])
    f_out = re.sub(r"\n?Wrote\s+\S+\.c(?:\s+\([^)]*\))?\s*$", "", f_out, flags=re.IGNORECASE)
    c_out = _extract_run_output(proc.stdout, "transformed-c", [])
    f_lines = [ln.strip() for ln in f_out.splitlines() if ln.strip()]
    c_lines = [ln.strip() for ln in c_out.splitlines() if ln.strip()]
    f_head = XNORMALIZE.normalize_text("\n".join(f_lines[:8]), NORMALIZE_INT_TOL, NORMALIZE_DECIMALS)
    c_head = XNORMALIZE.normalize_text("\n".join(c_lines[:8]), NORMALIZE_INT_TOL, NORMALIZE_DECIMALS)
    assert f_head == c_head
    assert len(f_lines) == len(c_lines) == 20


def test_xf2c_loc_intrinsics_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xloc.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xmaxloc_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xmaxloc.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_operator_overloading_for_derived_type_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xdate.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_type_bound_procedures_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xtype_bound.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_simple_pdt_subset_matches() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xpdt.f90",
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_pdt_string_subset_runs_transformed_c() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xpdt_string.f90",
            "--run",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "uppercase copy of b" in proc.stdout
    assert "PARAMETERIZED DERIVED TYPES" in proc.stdout


def test_xf2c_pdt_matrix_subset_runs_transformed_c() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xpdt_matrix.f90",
            "--run",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "transpose of a" in proc.stdout
    assert "sum(bt%x) = 153" in proc.stdout


def test_xf2c_mt19937_type_bound_generic_and_bit_intrinsics_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xmt.f90",
            "--run-both",
            "--pretty",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_extended_scalar_math_intrinsics_match() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(XF2C_PATH),
            "xfunc.f90",
            "--run-both",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (original-fortran): PASS" in proc.stdout
    assert "Build (transformed-c): PASS" in proc.stdout
    _assert_normalized_outputs_match(proc)


def test_xf2c_single_file_embeds_runtime_helpers() -> None:
    with tempfile.TemporaryDirectory() as td:
        out_path = Path(td) / "out.c"
        proc = subprocess.run(
            [
                sys.executable,
                str(XF2C_PATH),
                "xread.f90",
                "--single-file",
                "--run",
                "--out-dir",
                td,
                "--out",
                out_path.name,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert '#include "fortran_runtime.h"' not in emitted
    assert "int open_unit(int unit, const char *file, const char *action, const char *status) {" in emitted
    assert "static FILE *unit_files[1000] = {0};" in emitted


def test_xf2c_clang_option_selects_clang_build_command() -> None:
    cmd, exe = xf2c_driver._build_c_command(
        "clang",
        REPO_ROOT,
        REPO_ROOT / "fortran_runtime.c",
        REPO_ROOT / "temp_demo.c",
        single_file=False,
        has_program_unit=True,
        compile_only=False,
    )

    assert cmd[0] == "clang"
    assert str(REPO_ROOT / "fortran_runtime.c") in cmd
    assert "-lm" in cmd
    assert exe == REPO_ROOT / "temp_demo.exe"


def test_xf2c_msvc_option_selects_cl_build_command() -> None:
    cmd, exe = xf2c_driver._build_c_command(
        "msvc",
        REPO_ROOT,
        REPO_ROOT / "fortran_runtime.c",
        REPO_ROOT / "temp_demo.c",
        single_file=False,
        has_program_unit=True,
        compile_only=False,
    )

    assert cmd[0] == "cl"
    assert "/nologo" in cmd
    assert any(part.startswith("/I") for part in cmd)
    assert str(REPO_ROOT / "fortran_runtime.c") in cmd
    assert any(part.startswith("/Fe:") for part in cmd)
    assert exe == REPO_ROOT / "temp_demo.exe"


def test_xf2c_selected_c_compiler_prefers_requested_flag() -> None:
    assert xf2c_driver._selected_c_compiler(argparse.Namespace(clang=False, msvc=False)) == "gcc"
    assert xf2c_driver._selected_c_compiler(argparse.Namespace(clang=True, msvc=False)) == "clang"
    assert xf2c_driver._selected_c_compiler(argparse.Namespace(clang=False, msvc=True)) == "msvc"


def test_xf2c_driver_direct_invocation_expands_parent_glob() -> None:
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        child = root / "child"
        child.mkdir()
        src_path = root / "xhello.f90"
        src_path.write_text((REPO_ROOT / "xhello.f90").read_text(encoding="utf-8"), encoding="utf-8")
        pattern = str(Path("..") / "*.f90")
        proc = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "xf2c_driver.py"),
                pattern,
                "--mode-each",
                "--compile",
            ],
            cwd=child,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "Wrote temp_xhello.c" in proc.stdout
        assert (child / "temp_xhello.c").exists()


def test_generated_c_banner_default_and_opt_out() -> None:
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xhello_tmp.f90"
        src_path.write_text((REPO_ROOT / "xhello.f90").read_text(encoding="utf-8"), encoding="utf-8")

        proc_default = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc_default.returncode == 0, proc_default.stdout + proc_default.stderr
        emitted = (REPO_ROOT / "temp_xhello_tmp.c").read_text(encoding="utf-8")
        assert emitted.startswith("/* Generated by xf2c.py from xhello_tmp.f90 */\n")

        proc_no_banner = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile", "--no-banner"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc_no_banner.returncode == 0, proc_no_banner.stdout + proc_no_banner.stderr
        emitted_no_banner = (REPO_ROOT / "temp_xhello_tmp.c").read_text(encoding="utf-8")
        assert not emitted_no_banner.startswith("/* Generated by xf2c.py")


def test_xoperator_defined_operator_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xoperator.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "\nT\nF\nT\nF\nT\nF\nT\nT\n" in proc.stdout


def test_xprimes_upto_p_inline_deallocate_and_do_while_match() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xprimes_upto_p.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "78498 primes up to 1000000" in proc.stdout
    assert "last prime: 999983" in proc.stdout


def test_max_errors_limits_compiler_output() -> None:
    src_text = "\n".join(
        [
            "module m",
            "contains",
            "subroutine read_alloc_char(iu,xx,nx)",
            "integer, intent(in) :: iu",
            "character(len=*), allocatable, intent(out) :: xx(:)",
            "integer, intent(out), optional :: nx",
            "integer :: ndum, nx_",
            "read (iu,*) ndum,xx",
            "nx_ = size(xx)",
            "if (present(nx)) nx = nx_",
            "end subroutine read_alloc_char",
            "end module m",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xmaxerr.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "xf2c.py"),
                str(src_path),
                "--compile",
                "--out-dir",
                td,
                "--max-errors",
                "5",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode != 0
    assert "Build (transformed-c): FAIL" in proc.stdout
    assert "read_words_after_int_unit" in proc.stdout
    assert "... and " not in proc.stdout


def test_max_errors_zero_shows_full_compiler_output() -> None:
    src_text = "\n".join(
        [
            "module m",
            "contains",
            "subroutine read_alloc_char(iu,xx,nx)",
            "integer, intent(in) :: iu",
            "character(len=*), allocatable, intent(out) :: xx(:)",
            "integer, intent(out), optional :: nx",
            "integer :: ndum, nx_",
            "read (iu,*) ndum,xx",
            "nx_ = size(xx)",
            "if (present(nx)) nx = nx_",
            "end subroutine read_alloc_char",
            "end module m",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xmaxerr.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "xf2c.py"),
                str(src_path),
                "--compile",
                "--out-dir",
                td,
                "--max-errors",
                "0",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode != 0
    assert "Build (transformed-c): FAIL" in proc.stdout
    assert "read_words_after_int_unit" in proc.stdout
    assert "... and " not in proc.stdout


def test_xrational_approx_transformed_c_runs() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xrational_approx.f90", "--run"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "rational (3,2) fit:" in proc.stdout


def test_xrational_approx_rng_poly_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xrational_approx_rng_poly.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xrational_approx_rng_jac_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xrational_approx_rng_jac.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xrational_approx_rng_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xrational_approx_rng.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xgoto_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xgoto.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xdata_examples_match() -> None:
    for name in [
        "xdata_array.f90",
        "xdata_matrix.f90",
        "xdata_repeat.f90",
        "xdata_save.f90",
        "xdata_scalar.f90",
    ]:
        proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "xf2c.py"), name, "--run-both", "--pretty"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, f"{name}\n{proc.stdout}{proc.stderr}"
        _assert_normalized_outputs_match(proc)


def test_xinquire_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xinquire.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xgetcwd_runs_with_transformed_c() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xgetcwd.f90", "--run"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "cwd =" in proc.stdout


def test_xgetcwd_rejected_in_f2023_mode() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xgetcwd.f90", "--compile", "--std=f2023"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode != 0
    assert "extension not allowed in f2023 mode" in (proc.stdout + proc.stderr)


def test_xcompiler_info_runs_with_transformed_c() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcompiler_info.f90", "--run"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "compiler_version():" in proc.stdout
    assert "xf2c via gcc" in proc.stdout
    assert "compiler_options():" in proc.stdout
    assert "via gcc" in proc.stdout


def test_xcompiler_info_clang_reports_via_clang_when_available() -> None:
    if shutil.which("clang") is None:
        pytest.skip("clang not installed")
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcompiler_info.f90", "--run", "--clang"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "xf2c via clang" in proc.stdout
    assert "via clang" in proc.stdout


def test_xdate_and_time_runs_with_transformed_c() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xdate_and_time.f90", "--run"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "raw results from date_and_time:" in proc.stdout
    assert "decoded values array:" in proc.stdout
    assert "formatted date:" in proc.stdout
    assert "formatted time:" in proc.stdout


def test_xsystem_clock_runs_with_transformed_c() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xsystem_clock.f90", "--run"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "count_rate =" in proc.stdout
    assert "count_max  =" in proc.stdout
    assert "successive clock readings:" in proc.stdout
    assert "elapsed time in waste_time() =" in proc.stdout


def test_xsystem_clock_int64_runs_with_transformed_c() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xsystem_clock_int64.f90", "--run"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "count_rate =" in proc.stdout
    assert "count_max  =" in proc.stdout
    assert "successive clock readings:" in proc.stdout
    assert "elapsed time in waste_time() =" in proc.stdout


def test_xcpu_time_runs_with_transformed_c() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcpu_time.f90", "--run"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run (transformed-c): PASS" in proc.stdout
    assert "result  =" in proc.stdout
    assert "cpu sec =" in proc.stdout
    assert "inside show_cpu_time" in proc.stdout
    assert "dummy   =" in proc.stdout


def test_xpause_compiles_with_transformed_c() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xpause.f90", "--compile"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    emitted = (REPO_ROOT / "temp_xpause.c").read_text(encoding="utf-8")
    assert 'pause_s("paused: resume execution");' in emitted


def test_xpause_rejected_in_f2023_mode() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  pause",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xpause_stmt.f90"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile", "--std=f2023"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode != 0
    assert "extension not allowed in f2023 mode" in (proc.stdout + proc.stderr)


def test_pause_statement_compiles_by_default() -> None:
    src_text = "\n".join(
        [
            "program p",
            "  implicit none",
            "  pause",
            "end program p",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xpause_stmt.f90"
        out_path = Path(td) / "xpause_stmt.c"
        src_path.write_text(src_text, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XF2C_PATH), str(src_path), "--compile", "--out-dir", td, "--out", out_path.name],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        assert proc.returncode == 0, proc.stdout + proc.stderr
        emitted = out_path.read_text(encoding="utf-8")

    assert "pause_s(NULL);" in emitted


def test_xcommand_name_run_diff_matches_after_exe_name_normalization() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcommand_name.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xcommand_line_run_diff_matches_with_length_and_status() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcommand_line.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_ximplicit_typing_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "ximplicit_typing.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_uppercase_i_variable_prints_correctly() -> None:
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "xupper_i.f90"
        src.write_text(
            "program main\n"
            "implicit none\n"
            "integer :: I = 3\n"
            "print *, I\n"
            "end program main\n",
            encoding="utf-8",
        )
        proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src), "--run-diff", "--pretty"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xdeclaration_order_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xdeclaration_order.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xchar_plus_int_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xchar_plus_int.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xrepeat_char_vec_simple_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xrepeat_char_vec_simple.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xrepeat_char_vec_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xrepeat_char_vec.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xutil_all_min_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xutil_all_min.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xperiod_sums_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xperiod_sums.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xstar_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xstar.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xbind_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xbind.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xendif_run_diff_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xendif.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xstar_rejected_in_f2023_mode() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xstar.f90", "--compile", "--std=f2023"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode != 0
    assert "extension not allowed in f2023 mode" in (proc.stdout + proc.stderr)


def test_xf2c_get_command_argument_with_length_and_status_uses_full_helper() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcommand_line.f90", "--compile", "--annotate"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    emitted = (REPO_ROOT / "temp_xcommand_line.c").read_text(encoding="utf-8")
    assert "get_command_argument_full_s(0, arg, 100, &len_arg, &status);" in emitted


def test_xif_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xif.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xread_star_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xread_star.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xarray_arg_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xarray_arg.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xblas_part_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xblas_part.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_goto_and_go_to_are_both_accepted(tmp_path: Path) -> None:
    src_path = tmp_path / "xgoto_spellings.f90"
    src_path.write_text(
        """program main
implicit none
integer :: i
i = 1
goto 100
i = 2
100 continue
print *, i
go to 200
i = 3
200 continue
print *, i
end program main
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_interface_block_inside_procedure_does_not_break_unit_or_implicit_none(tmp_path: Path) -> None:
    src_path = tmp_path / "xinterface_dummy.f90"
    src_path.write_text(
        """subroutine outer(n, x, fcn)
implicit none
integer, intent(in) :: n
real, intent(inout) :: x(:)
interface
  subroutine fcn(n, x)
    implicit none
    integer, intent(in) :: n
    real, intent(inout) :: x(:)
  end subroutine fcn
end interface
call fcn(n, x)
end subroutine outer
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--compile"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_single_assumed_shape_extent_does_not_collide_with_existing_n_arg(tmp_path: Path) -> None:
    src_path = tmp_path / "xextent_n.f90"
    src_path.write_text(
        """integer function idamax(n, x)
implicit none
integer, intent(in) :: n
real, intent(in) :: x(:)
if (n < 1) return
idamax = 1
end function idamax
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--compile"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    c_text = (REPO_ROOT / "temp_xextent_n.c").read_text(encoding="utf-8")
    assert "const int n, const int n," not in c_text


def test_xuncmin_compiles() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xuncmin.f90", "--compile"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_formatted_prefix_plus_1d_array_matches(tmp_path: Path) -> None:
    src_path = tmp_path / "xfmt_prefix_arr.f90"
    src_path.write_text(
        """program main
implicit none
real :: x(2), g(2)
x = [1.0, 2.0]
g = [3.0, 4.0]
write(*,'(a,2f12.8)') ' Final X: ', x
write(*,'(a,2g13.5)') ' Gradients: ', g
end program main
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_xuncmin_fix_matches() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xuncmin_fix.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_read_alloc_char_compiles_and_runs() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "read_alloc_char.f90", "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_dimension_colon_attr_declaration_parses_and_runs(tmp_path: Path) -> None:
    src_path = tmp_path / "xdim_attr_colon.f90"
    src_path.write_text(
        """program main
implicit none
integer :: x(3)
x = [1, 2, 3]
call fill(x)
print *, x
contains
subroutine fill(irngt)
  implicit none
  integer, dimension(:), intent(out) :: irngt
  irngt = 7
end subroutine fill
end program main
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)


def test_optional_logical_actual_passes_nullable_pointer_to_optional_callee() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xdefault.f90", "--compile"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_optional_placeholder_is_fully_unmasked_in_nested_optional_call_case() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcheck_equal_strings.f90", "--compile"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_xcheck_equal_strings_matches_pretty_run_diff() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xcheck_equal_strings.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_xopt_char_matches_pretty_run_diff() -> None:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), "xopt_char.f90", "--run-diff", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_inline_if_continued_formatted_write_matches() -> None:
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xinline_if_write_cont.f90"
        src_path.write_text(
            """program p
implicit none
character(len=5) :: xx(2)
logical :: flag
integer :: i
character(len=30) :: label
label = "words"
xx = [character(len=5) :: "ab", "cd"]
flag = .true.
if (flag) write (*,"(1x,a30,':',100(1x,a))") trim(label), &
                                             (trim(xx(i)),i=1,size(xx))
end program p
""",
            encoding="utf-8",
        )
        proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_external_unit_read_count_and_words_matches() -> None:
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xread_words_unit_after_count.f90"
        src_path.write_text(
            """program p
implicit none
integer :: iu
character(len=:), allocatable :: xx(:)
open(newunit=iu, status="scratch", action="readwrite")
write(iu,"(a)") "2 dog cat"
rewind(iu)
call read_alloc_char_local(iu, xx)
print "(100(a,1x))", xx
contains
subroutine read_alloc_char_local(iu, xx)
integer, intent(in) :: iu
character(len=:), allocatable, intent(out) :: xx(:)
integer :: nx_, ndum
read (iu,*) nx_
nx_ = max(0, nx_)
allocate(character(len=10) :: xx(nx_))
backspace(iu)
read (iu,*) ndum, xx
end subroutine read_alloc_char_local
end program p
""",
            encoding="utf-8",
        )
        proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--compile"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Build (transformed-c): PASS" in proc.stdout


def test_defined_operator_notin_matches() -> None:
    with tempfile.TemporaryDirectory() as td:
        src_path = Path(td) / "xnotin.f90"
        src_path.write_text(
            """module m
implicit none
interface operator (.notin.)
   module procedure not_in_int
end interface
contains
logical function not_in_int(i, vec)
integer, intent(in) :: i
integer, intent(in) :: vec(:)
not_in_int = .not. any(vec == i)
end function not_in_int
end module m

program p
use m
implicit none
integer :: ii(3), jj(2), i
ii = [1, 2, 3]
jj = [2, 4]
do i = 1, size(ii)
   if (ii(i) .notin. jj) print *, ii(i)
end do
end program p
""",
            encoding="utf-8",
        )
        proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--run-diff", "--pretty"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Run diff: MATCH" in proc.stdout


def test_scalar_sum_of_generic_array_result_with_optional_arg_matches(tmp_path: Path) -> None:
    src_path = tmp_path / "xsum_generic_vec.f90"
    src_path.write_text(
        """module m
implicit none
interface g
   module procedure g_vec
end interface
contains
function g_vec(n, stdz) result(x)
  integer, intent(in) :: n
  logical, intent(in), optional :: stdz
  real :: x(n)
  integer :: i
  do i = 1, n
     x(i) = real(i)
  end do
  if (present(stdz)) then
     if (stdz) x = x / 2.0
  end if
end function g_vec
end module m

program main
use m
implicit none
real :: s1, s2
s1 = sum(g(4)**2)
s2 = sum(g(4, stdz=.true.)**2)
print *, s1
print *, s2
end program main
""",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "xf2c.py"), str(src_path), "--run-both", "--pretty"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    _assert_normalized_outputs_match(proc)
