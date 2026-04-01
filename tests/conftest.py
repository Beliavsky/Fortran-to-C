from __future__ import annotations

import os
import re
import time

import pytest


def pytest_addoption(parser) -> None:
    parser.addoption(
        "--c-compiler",
        action="store",
        default="gcc",
        choices=["gcc", "clang", "msvc"],
        help="Select the C compiler used by xf2c subprocess tests.",
    )
    parser.addoption(
        "--limit",
        action="store",
        type=int,
        default=0,
        help="Run at most the first N collected tests (0 means no limit).",
    )
    parser.addoption(
        "--time",
        action="store_true",
        help="Print elapsed time after each test and a final per-code timing summary.",
    )


def pytest_configure(config) -> None:
    os.environ["XF2C_TEST_C_COMPILER"] = config.getoption("--c-compiler")
    config._xf2c_time_enabled = bool(config.getoption("--time"))
    config._xf2c_time_start = time.perf_counter()
    config._xf2c_test_durations = []
    config._xf2c_code_durations = {}


def pytest_collection_modifyitems(config, items) -> None:
    limit = int(config.getoption("--limit") or 0)
    if limit <= 0 or len(items) <= limit:
        return
    del items[limit:]


def _time_label_from_nodeid(nodeid: str) -> str:
    m = re.search(r"\[([^\]]+\.(?:f90|f))\]", nodeid, re.IGNORECASE)
    if m:
        return m.group(1)
    return nodeid


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item, call):
    outcome = yield
    report = outcome.get_result()
    if report.when != "call":
        return
    config = item.config
    if not getattr(config, "_xf2c_time_enabled", False):
        return
    label = _time_label_from_nodeid(report.nodeid)
    elapsed = time.perf_counter() - config._xf2c_time_start
    duration = float(report.duration)
    config._xf2c_test_durations.append((report.nodeid, label, duration))
    config._xf2c_code_durations[label] = config._xf2c_code_durations.get(label, 0.0) + duration
    tr = config.pluginmanager.get_plugin("terminalreporter")
    if tr is not None:
        tr.write_line(f"[{elapsed:8.2f}s] {label} (+{duration:.2f}s)")


def pytest_terminal_summary(terminalreporter, exitstatus, config) -> None:
    if not getattr(config, "_xf2c_time_enabled", False):
        return
    code_durations = getattr(config, "_xf2c_code_durations", {})
    if not code_durations:
        return
    terminalreporter.write_sep("=", "Per-Code Times (Descending)")
    for label, duration in sorted(code_durations.items(), key=lambda kv: kv[1], reverse=True):
        terminalreporter.write_line(f"{duration:8.2f}s  {label}")
