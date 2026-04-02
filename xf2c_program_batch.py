"""Batch-run xf2c over complete Fortran programs listed in manifest files.

Each manifest is a `*_files.txt` file containing one Fortran source path per
line in the order needed to build the original program with gfortran. The
script combines the listed sources, runs `xf2c.py` on the target program file,
and reports pass/fail plus optional timing and failure output.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import shlex
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run xf2c.py over complete Fortran programs described by *_files.txt manifests."
    )
    parser.add_argument(
        "manifests",
        nargs="*",
        help="Manifest files to process. If omitted, --manifest-glob is used from --root.",
    )
    parser.add_argument(
        "--root",
        default=".",
        help="Root directory containing the manifest files. Default: current directory.",
    )
    parser.add_argument(
        "--manifest-glob",
        default="*_files.txt",
        help="Glob used under --root when no manifest files are given.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=None,
        help="Process at most this many manifests.",
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
        help="Python executable used to invoke xf2c.py.",
    )
    parser.add_argument(
        "--opts",
        default="--compile",
        help="Extra options passed to xf2c.py. Default: '--compile'.",
    )
    parser.add_argument(
        "--show-fail-output",
        dest="show_fail_output",
        action="store_true",
        default=True,
        help="Print captured stdout/stderr for failed manifests. Default: on.",
    )
    parser.add_argument(
        "--no-fail-output",
        dest="show_fail_output",
        action="store_false",
        help="Hide captured stdout/stderr for failed manifests.",
    )
    return parser.parse_args()


def _resolve_manifests(args: argparse.Namespace) -> list[Path]:
    if args.manifests:
        return [Path(p) for p in args.manifests]
    root = Path(args.root)
    return [Path(p) for p in sorted(glob.glob(str(root / args.manifest_glob)))]


def _read_manifest_sources(path: Path) -> list[str]:
    return [
        line.strip()
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]


def _write_combined_source(manifest: Path, sources: list[str]) -> Path:
    parts: list[str] = []
    for src in sources:
        src_path = manifest.parent / src
        text = src_path.read_text(encoding="utf-8", errors="replace")
        parts.append(f"! xf2c_program_batch source: {src_path.name}\n{text.rstrip()}\n")
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".f90",
        prefix=f"{manifest.stem}_xf2c_",
        dir=manifest.parent,
        delete=False,
    ) as tmp:
        tmp.write("\n".join(parts))
        return Path(tmp.name)


def _format_seconds(value: float) -> str:
    return f"{value:.2f}s"


def main() -> int:
    args = _parse_args()
    manifests = _resolve_manifests(args)
    if args.limit is not None:
        if args.limit < 0:
            print("[ERROR] --limit must be nonnegative.", file=sys.stderr)
            return 1
        manifests = manifests[: args.limit]
    if not manifests:
        print("[ERROR] no manifest files found.", file=sys.stderr)
        return 1

    xf2c_path = Path(args.xf2c)
    if not xf2c_path.is_file():
        print(f"[ERROR] {xf2c_path} not found.", file=sys.stderr)
        return 1

    opts = shlex.split(args.opts)
    total = 0
    passed = 0
    failed = 0
    skipped = 0
    failed_list: list[str] = []
    total_start = time.perf_counter()
    total_compile_fortran = 0.0
    total_transpile = 0.0
    total_compile_c = 0.0

    for manifest in manifests:
        print("------------------------------------------------------------")
        print(f"[MANIFEST] {manifest}")
        if not manifest.is_file():
            print(f"[SKIP] manifest not found: {manifest}")
            skipped += 1
            continue
        try:
            sources = _read_manifest_sources(manifest)
        except OSError as exc:
            print(f"[SKIP] could not read {manifest}: {exc}")
            skipped += 1
            continue
        if not sources:
            print(f"[SKIP] empty manifest: {manifest}")
            skipped += 1
            continue

        target = manifest.parent / sources[-1]
        total += 1
        print(f"[TARGET] {target.name}")
        compile_cmd = "gfortran " + " ".join(Path(src).name for src in sources)
        print(f"[BUILD] {compile_cmd}")
        combined_path: Path | None = None
        timings_path: Path | None = None
        f_exe = manifest.parent / f"__xf2c_program_batch_{manifest.stem}.exe"
        try:
            t_compile_fortran = time.perf_counter()
            f_proc = subprocess.run(
                ["gfortran", *sources, "-o", f_exe.name],
                cwd=manifest.parent,
                capture_output=True,
                text=True,
                check=False,
            )
            total_compile_fortran += time.perf_counter() - t_compile_fortran
            combined_path = _write_combined_source(manifest, sources)
            with tempfile.NamedTemporaryFile(
                mode="w",
                encoding="utf-8",
                suffix=".json",
                prefix=f"{manifest.stem}_xf2c_timings_",
                dir=manifest.parent,
                delete=False,
            ) as tmp_json:
                timings_path = Path(tmp_json.name)
            env = dict(os.environ)
            env["XF2C_TIMINGS_JSON"] = str(timings_path)
            cmd = [args.python_cmd, str(xf2c_path), str(combined_path), *opts]
            proc = subprocess.run(
                cmd,
                cwd=manifest.parent,
                capture_output=True,
                text=True,
                check=False,
                env=env,
            )
            if timings_path.is_file():
                try:
                    phase_data = json.loads(timings_path.read_text(encoding="utf-8"))
                    total_transpile += float(phase_data.get("transpile", 0.0) or 0.0)
                    total_compile_c += float(phase_data.get("compile_c", 0.0) or 0.0)
                except (OSError, ValueError, TypeError):
                    pass
        finally:
            if combined_path is not None:
                try:
                    combined_path.unlink()
                except OSError:
                    pass
            if timings_path is not None:
                try:
                    timings_path.unlink()
                except OSError:
                    pass
            try:
                if f_exe.exists():
                    f_exe.unlink()
            except OSError:
                pass
        if proc.returncode == 0:
            print(f"[PASS] {manifest.name}")
            passed += 1
        else:
            print(f"[FAIL] {manifest.name} (exit {proc.returncode})")
            failed += 1
            failed_list.append(manifest.name)
            if args.show_fail_output:
                if proc.stdout:
                    print(proc.stdout, end="" if proc.stdout.endswith("\n") else "\n")
                if proc.stderr:
                    print(proc.stderr, end="" if proc.stderr.endswith("\n") else "\n", file=sys.stderr)
        print()

    print("============================================================")
    print(f"TOTAL={total} PASS={passed} FAIL={failed} SKIP={skipped}")
    total_elapsed = time.perf_counter() - total_start
    print(f"Total time: {_format_seconds(total_elapsed)}")
    print(f"Time compiling Fortran: {_format_seconds(total_compile_fortran)}")
    print(f"Time transpiling: {_format_seconds(total_transpile)}")
    print(f"Time compiling C: {_format_seconds(total_compile_c)}")
    if failed_list:
        print("FAILED MANIFESTS:")
        for name in failed_list:
            print(f"  {name}")
    print("============================================================")
    return failed


if __name__ == "__main__":
    raise SystemExit(main())
