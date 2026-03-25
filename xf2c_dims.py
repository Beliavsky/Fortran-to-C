#!/usr/bin/env python3
"""xf2c_dims.py: shared dimension helpers for xf2c."""

from __future__ import annotations

import re
from typing import List, Optional

from xf2c_textutil import _split_args_top_level

def _dim_parts(dim: Optional[str]) -> List[str]:
    if not dim:
        return []
    return [p.strip() for p in _split_args_top_level(dim) if p.strip()]

def _array_constructor_items(init: Optional[str]) -> Optional[List[str]]:
    if init is None:
        return None
    s = init.strip()
    m = re.match(r"^\[\s*(.*)\s*\]$", s, re.DOTALL)
    if not m:
        return None
    inner = m.group(1).strip()
    if not inner:
        return []
    return [x.strip() for x in _split_args_top_level(inner) if x.strip()]

def _infer_array_dim_from_init(dim: Optional[str], init: Optional[str]) -> Optional[str]:
    if dim is None:
        return dim
    if dim.strip() != "*":
        return dim
    items = _array_constructor_items(init)
    if items is None:
        return dim
    return str(len(items))

def _is_assumed_shape(dim: Optional[str]) -> bool:
    return any(p == ":" for p in _dim_parts(dim))

def _extent_param_names(
    arg_name: str,
    rank: int,
    *,
    use_simple_n: bool = False,
) -> List[str]:
    if rank <= 0:
        return []
    if rank == 1:
        return ["n"] if use_simple_n else [f"n_{arg_name}"]
    return [f"n_{arg_name}_{k+1}" for k in range(rank)]

def _alloc_len_name(name: str) -> str:
    return f"__n_{name.lower()}"

def _alloc_extent_names(name: str, rank: int) -> List[str]:
    if rank <= 1:
        return [_alloc_len_name(name)]
    base = name.lower()
    return [f"__n_{base}_{k+1}" for k in range(rank)]
