#!/usr/bin/env python3
"""xf2c.py: thin wrapper preserving `python xf2c.py foo.f90`."""

from __future__ import annotations

from xf2c_driver import main


if __name__ == "__main__":
    raise SystemExit(main())
