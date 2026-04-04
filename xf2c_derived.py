#!/usr/bin/env python3
"""xf2c_derived.py: derived-type parsing and emission helpers for xf2c."""

from __future__ import annotations

import re
from typing import Dict, List, Optional

from xf2c_textutil import _split_args_top_level, _strip_comment

def _replace_param_names(expr: str, param_exprs: Optional[Dict[str, str]]) -> str:
    if not param_exprs:
        return expr
    out = expr
    changed = True
    while changed:
        changed = False
        for nm, rhs in sorted(param_exprs.items(), key=lambda kv: len(kv[0]), reverse=True):
            new_out = re.sub(rf"(?i)\b{re.escape(nm)}\b", f"({rhs})", out)
            if new_out != out:
                out = new_out
                changed = True
    out = re.sub(
        r"(?i)\b(([0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[ed][+\-]?[0-9]+)?)_(?:[a-z_]\w*|\d+)\b",
        r"\1",
        out,
    )
    return out


def _local_derived_type_index_ranges(unit: Dict[str, object]) -> List[tuple[int, int]]:
    ranges: List[tuple[int, int]] = []
    in_type = False
    start_idx = -1
    for idx, raw in enumerate(unit.get("body_lines", [])):
        code = _strip_comment(str(raw)).strip()
        if not code:
            continue
        if not in_type:
            m_type = re.match(r"^type(?:\s*,\s*[^:]*)?\s*(?:::)?\s*([a-z_]\w*)\s*$", code, re.IGNORECASE)
            if m_type:
                in_type = True
                start_idx = idx
            continue
        if re.match(r"^end\s+type(?:\s+[a-z_]\w*)?\s*$", code, re.IGNORECASE):
            ranges.append((start_idx, idx))
            in_type = False
            start_idx = -1
    return ranges


def _index_in_ranges(idx: int, ranges: List[tuple[int, int]]) -> bool:
    for lo, hi in ranges:
        if lo <= idx <= hi:
            return True
    return False


def _parse_derived_field_decl(
    code: str,
    real_type: str,
    kind_ctype_map: Optional[Dict[str, str]] = None,
    param_exprs: Optional[Dict[str, str]] = None,
) -> List[tuple[str, str]]:
    out: List[tuple[str, str]] = []
    base: Optional[str] = None
    rhs: Optional[str] = None
    attrs = ""
    m = re.match(r"^integer\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|\d+)\s*\)(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
    if m:
        kind_tok = m.group(1).lower()
        base = kind_ctype_map.get(kind_tok, 'long long' if (kind_tok.isdigit() and int(kind_tok) >= 8) else 'int') if kind_ctype_map else ('long long' if (kind_tok.isdigit() and int(kind_tok) >= 8) else 'int')
        base, attrs, rhs = base, (m.group(2) or ''), m.group(3)
    if base is None:
        m = re.match(r"^integer(?:\s*\([^)]*\))?(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            base, attrs, rhs = 'int', (m.group(1) or ''), m.group(2)
    if base is None:
        m = re.match(r"^real\s*\(\s*kind\s*=\s*([a-z_]\w*|\d+)\s*\)(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            kind_tok = m.group(1).lower()
            base = kind_ctype_map.get(kind_tok, real_type) if kind_ctype_map else real_type
            if kind_tok.isdigit():
                base = 'double' if int(kind_tok) >= 8 else 'float'
            attrs, rhs = (m.group(2) or ''), m.group(3)
    if base is None:
        m = re.match(r"^real\s*\(\s*([a-z_]\w*|\d+)\s*\)(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            kind_tok = m.group(1).lower()
            base = kind_ctype_map.get(kind_tok, real_type) if kind_ctype_map else real_type
            if kind_tok.isdigit():
                base = 'double' if int(kind_tok) >= 8 else 'float'
            attrs, rhs = (m.group(2) or ''), m.group(3)
    if base is None:
        m = re.match(r"^real(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            base, attrs, rhs = real_type, (m.group(1) or ''), m.group(2)
    if base is None:
        m = re.match(r"^double\s+precision(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            base, attrs, rhs = 'double', (m.group(1) or ''), m.group(2)
    if base is None:
        m = re.match(r"^logical(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            base, attrs, rhs = 'logical', (m.group(1) or ''), m.group(2)
    if base is None:
        m = re.match(r"^character(?:\s*\([^)]*\))?(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            base, attrs, rhs = 'char *', (m.group(1) or ''), m.group(2)
    if base is None:
        m = re.match(r"^type\s*\(\s*([a-z_]\w*)\s*\)(?:\s*,\s*([^:]+))?\s*::\s*(.+)$", code, re.IGNORECASE)
        if m:
            base, attrs, rhs = m.group(1).lower(), (m.group(2) or ''), m.group(3)
    if base is None or rhs is None:
        return out
    attrs_low = attrs.lower()
    is_alloc = 'allocatable' in attrs_low
    dim_attr = None
    m_dim = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
    if m_dim:
        dim_attr = m_dim.group(1).strip()
    for ent in [x.strip() for x in _split_args_top_level(rhs) if x.strip()]:
        ent0 = ent.split('=',1)[0].strip() if '=' in ent and '=>' not in ent else ent
        name = ent0
        dim = dim_attr
        m_arr = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", ent0, re.IGNORECASE)
        if m_arr:
            name = m_arr.group(1)
            dim = _replace_param_names(m_arr.group(2).strip(), param_exprs)
        nm = name.lower()
        if is_alloc and dim:
            out.append((nm, f"{base} allocatable[{dim}]"))
        elif dim:
            out.append((nm, f"{base}[{dim}]"))
        else:
            out.append((nm, base))
    return out


def _parse_local_derived_types(
    unit: Dict[str, object],
    real_type: str,
    kind_ctype_map: Optional[Dict[str, str]] = None,
    param_exprs: Optional[Dict[str, str]] = None,
) -> Dict[str, List[tuple[str, str]]]:
    out: Dict[str, List[tuple[str, str]]] = {}
    current: Optional[str] = None
    fields: List[tuple[str, str]] = []
    for raw in unit.get("body_lines", []):
        code = _strip_comment(str(raw)).strip()
        if not code:
            continue
        if current is None:
            m_type = re.match(r"^type(?:\s*,\s*[^:]*)?\s*(?:::)?\s*([a-z_]\w*)\s*$", code, re.IGNORECASE)
            if m_type:
                current = m_type.group(1).lower()
                fields = []
            continue
        if re.match(r"^end\s+type(?:\s+[a-z_]\w*)?\s*$", code, re.IGNORECASE):
            out[current] = list(fields)
            current = None
            fields = []
            continue
        fields.extend(_parse_derived_field_decl(code, real_type, kind_ctype_map, param_exprs))
    return out


def emit_local_derived_type_typedefs(
    out: List[str],
    indent: int,
    local_derived_types: Dict[str, List[tuple[str, str]]],
) -> None:
    for dt_name, dt_fields in local_derived_types.items():
        out.append(" " * indent + "typedef struct {")
        for fld_name, fld_ctype in dt_fields:
            if ' allocatable[' in fld_ctype:
                base, dims = fld_ctype.split(' allocatable[',1)
                dims = dims[:-1]
                rank = len([x for x in _split_args_top_level(dims) if x.strip()])
                if base.strip() == 'char *':
                    out.append(" " * (indent + 3) + f"char **{fld_name};")
                else:
                    out.append(" " * (indent + 3) + f"{base.strip()} *{fld_name};")
                if rank == 1:
                    out.append(" " * (indent + 3) + f"int __n_{fld_name};")
                else:
                    for k in range(rank):
                        out.append(" " * (indent + 3) + f"int __n_{fld_name}_{k+1};")
            else:
                m_arr = re.match(r"^(.+)\[([^\[\]]+)\]$", fld_ctype)
                if m_arr:
                    base = m_arr.group(1).strip()
                    if base == "logical":
                        base = "int"
                    dim = m_arr.group(2).strip()
                    out.append(" " * (indent + 3) + f"{base} {fld_name}[{dim}];")
                else:
                    cty = "int" if fld_ctype == "logical" else fld_ctype
                    out.append(" " * (indent + 3) + f"{cty} {fld_name};")
        out.append(" " * indent + f"}} {dt_name};")
