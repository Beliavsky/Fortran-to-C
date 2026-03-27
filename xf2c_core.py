#!/usr/bin/env python3
"""xf2c_core.py: core Fortran-to-C transpilation logic."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, List, Optional

import fortran_scan as fscan
from xf2c_derived import _local_derived_type_index_ranges, _index_in_ranges, _parse_local_derived_types, emit_local_derived_type_typedefs

@dataclass
class Var:
    ctype: str
    is_array: bool = False
    dim: Optional[str] = None
    is_logical: bool = False
    is_allocatable: bool = False
    is_pointer: bool = False
    is_target: bool = False
    intent: Optional[str] = None
    is_external: bool = False
    is_save: bool = False
    optional: bool = False
    is_param: bool = False
    init: Optional[str] = None
    ptr_init: Optional[str] = None
    comment: Optional[str] = None
    char_len: Optional[str] = None


_ACTIVE_DERIVED_TYPES: Dict[str, List[tuple[str, str]]] = {}
_ACTIVE_PROC_RESULTS: Dict[str, Var] = {}
_ACTIVE_GENERIC_BINDINGS: Dict[str, List[str]] = {}
_ACTIVE_OPERATOR_BINDINGS: Dict[str, List[str]] = {}
_ACTIVE_TYPE_BOUND_BINDINGS: Dict[str, Dict[str, str]] = {}
_ACTIVE_PROC_ARG_CTYPES: Dict[str, List[str]] = {}
_ACTIVE_PROC_ARG_IS_ARRAY: Dict[str, List[bool]] = {}
_ACTIVE_PROC_ARG_ASSUMED_RANKS: Dict[str, List[int]] = {}
_ACTIVE_PROC_IS_ELEMENTAL: Dict[str, bool] = {}


def _complex_ctype(real_type: str) -> str:
    return "double complex" if real_type == "double" else "float complex"


def _is_complex_ctype(ctype: Optional[str]) -> bool:
    return "complex" in (ctype or "").lower()


def _complex_real_expr(expr: str, real_type: str) -> str:
    return f"({'creal' if real_type == 'double' else 'crealf'}({expr}))"


def _complex_imag_expr(expr: str, real_type: str) -> str:
    return f"({'cimag' if real_type == 'double' else 'cimagf'}({expr}))"


def _complex_abs_expr(expr: str, real_type: str) -> str:
    return f"({'cabs' if real_type == 'double' else 'cabsf'}({expr}))"


def _complex_conj_expr(expr: str, real_type: str) -> str:
    return f"({'conj' if real_type == 'double' else 'conjf'}({expr}))"


def _complex_sqrt_expr(expr: str, real_type: str) -> str:
    return f"({'csqrt' if real_type == 'double' else 'csqrtf'}({expr}))"


def _parse_complex_literal(expr: str) -> Optional[tuple[str, str]]:
    s = expr.strip()
    if not (s.startswith("(") and s.endswith(")")):
        return None
    inner = s[1:-1].strip()
    parts = [x.strip() for x in _split_args_top_level(inner) if x.strip()]
    if len(parts) != 2:
        return None
    if any(_is_fortran_string_literal(p) for p in parts):
        return None
    return parts[0], parts[1]


def _proc_result_var(name: str) -> Optional[Var]:
    return _ACTIVE_PROC_RESULTS.get(name.lower())


def _extract_type_bound_bindings(text: str) -> Dict[str, Dict[str, str]]:
    bindings: Dict[str, Dict[str, str]] = {}
    current_type: Optional[str] = None
    type_contains = False
    for raw in text.splitlines():
        code = _strip_comment(raw).strip()
        if not code:
            continue
        if current_type is None:
            m_type = re.match(
                r"^type(?:\s*,\s*[^:]*)?\s*(?:::)?\s*([a-z_]\w*)\s*$",
                code,
                re.IGNORECASE,
            )
            if m_type and not re.match(r"^type\s*\(", code, re.IGNORECASE):
                current_type = m_type.group(1).lower()
                bindings.setdefault(current_type, {})
                type_contains = False
            continue
        if re.match(r"^end\s+type(?:\s+[a-z_]\w*)?\s*$", code, re.IGNORECASE):
            current_type = None
            type_contains = False
            continue
        if re.match(r"^contains\b", code, re.IGNORECASE):
            type_contains = True
            continue
        if not type_contains:
            continue
        m_proc = re.match(
            r"^procedure(?:\s*\([^)]*\))?(?:\s*,\s*[^:]*)*\s*::\s*(.+)$",
            code,
            re.IGNORECASE,
        )
        if not m_proc:
            continue
        for item in _split_args_top_level(m_proc.group(1)):
            it = item.strip()
            if not it:
                continue
            m_rename = re.match(r"^([a-z_]\w*)\s*=>\s*([a-z_]\w*)$", it, re.IGNORECASE)
            if m_rename:
                bind_name = m_rename.group(1).lower()
                proc_name = m_rename.group(2).lower()
            else:
                bind_name = it.lower()
                proc_name = bind_name
            bindings[current_type][bind_name] = proc_name
    return {k: v for k, v in bindings.items() if v}


def _infer_actual_signature(expr: str, vars_map: Dict[str, Var], real_type: str) -> tuple[str, bool, int]:
    s = _rewrite_type_bound_calls(expr.strip(), vars_map, real_type)
    ctor_items = _array_constructor_items(s)
    if ctor_items is not None:
        return (_array_constructor_ctype(ctor_items, vars_map, real_type), True, 1)
    if _is_fortran_string_literal(s):
        return ("string", False, 0)
    if _parse_complex_literal(s) is not None:
        return ("complex", False, 0)
    if re.fullmatch(r"[+\-]?\d+", s):
        return ("int", False, 0)
    if re.fullmatch(r"[+\-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eEdD][+\-]?\d+)?(?:_[a-z_]\w*)?", s):
        return (real_type.lower(), False, 0)
    m_name = re.fullmatch(r"([a-z_]\w*)", s, re.IGNORECASE)
    if m_name:
        vv = vars_map.get(m_name.group(1).lower())
        if vv is not None:
            rank = len(_dim_parts(vv.dim)) if vv.is_array else 0
            if vv.is_logical:
                return ("logical", bool(vv.is_array), rank)
            return ((vv.ctype or real_type).lower(), bool(vv.is_array), rank)
    m_call = re.fullmatch(r"([a-z_]\w*)\s*\((.*)\)", s, re.IGNORECASE)
    if m_call:
        callee = m_call.group(1).lower()
        rv = _proc_result_var(callee)
        if rv is not None:
            rank = len(_dim_parts(rv.dim)) if rv.is_array else 0
            if rv.is_logical:
                return ("logical", bool(rv.is_array), rank)
            return ((rv.ctype or real_type).lower(), bool(rv.is_array), rank)
    cty = _format_item_ctype(s, vars_map, real_type)
    return (cty, False, 0)


def _compatible_actual_for_dummy(actual_ctype: str, expected_ctype: str) -> bool:
    a = (actual_ctype or "").lower()
    e = (expected_ctype or "").lower()
    if e == "char *":
        return a in {"char *", "string"}
    if e == "int":
        return a == "int"
    if e in {"float", "double"}:
        return a in {"float", "double", "int"}
    return a == e


def _resolve_generic_proc_name(
    name: str,
    args: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
) -> str:
    nm = name.lower()
    cands = _ACTIVE_GENERIC_BINDINGS.get(nm, [])
    if not cands:
        return nm
    actuals = [_infer_actual_signature(a, vars_map, real_type) for a in args]
    for cand in cands:
        exp_ctys = _ACTIVE_PROC_ARG_CTYPES.get(cand, [])
        exp_is_array = _ACTIVE_PROC_ARG_IS_ARRAY.get(cand, [])
        exp_ranks = _ACTIVE_PROC_ARG_ASSUMED_RANKS.get(cand, [])
        if len(exp_ctys) != len(actuals):
            continue
        ok = True
        for i, (act_cty, act_is_array, act_rank) in enumerate(actuals):
            if i < len(exp_is_array) and bool(exp_is_array[i]) != bool(act_is_array):
                ok = False
                break
            if bool(act_is_array):
                exp_rank = exp_ranks[i] if i < len(exp_ranks) else 0
                if exp_rank and act_rank and exp_rank != act_rank:
                    ok = False
                    break
            if not _compatible_actual_for_dummy(act_cty, exp_ctys[i] if i < len(exp_ctys) else ""):
                ok = False
                break
        if ok:
            return cand
    return cands[0] if len(cands) == 1 else nm


def _resolve_operator_proc_name(
    symbol: str,
    lhs: str,
    rhs: str,
    vars_map: Dict[str, Var],
    real_type: str,
) -> Optional[str]:
    cands = _ACTIVE_OPERATOR_BINDINGS.get(symbol, [])
    if not cands:
        return None
    actuals = [
        _infer_actual_signature(lhs, vars_map, real_type),
        _infer_actual_signature(rhs, vars_map, real_type),
    ]
    matches: List[str] = []
    for cand in cands:
        exp_ctys = _ACTIVE_PROC_ARG_CTYPES.get(cand, [])
        exp_is_array = _ACTIVE_PROC_ARG_IS_ARRAY.get(cand, [])
        exp_ranks = _ACTIVE_PROC_ARG_ASSUMED_RANKS.get(cand, [])
        if len(exp_ctys) != 2:
            continue
        ok = True
        for i, (act_cty, act_is_array, act_rank) in enumerate(actuals):
            if i < len(exp_is_array) and bool(exp_is_array[i]) != bool(act_is_array):
                ok = False
                break
            if act_is_array:
                exp_rank = exp_ranks[i] if i < len(exp_ranks) else 0
                if exp_rank and exp_rank != act_rank:
                    ok = False
                    break
            if not _compatible_actual_for_dummy(act_cty, exp_ctys[i] if i < len(exp_ctys) else ""):
                ok = False
                break
        if ok:
            matches.append(cand)
    if len(matches) == 1:
        return matches[0]
    return None


def _fallback_function_result_var(
    unit: Dict[str, object],
    real_type: str,
    kind_ctype_map: Dict[str, str],
) -> Optional[Var]:
    if unit.get("kind") != "function":
        return None
    scan_lines: List[str] = []
    header_ln = int(unit.get("header_line_no", 0) or 0)
    source_lines: List[str] = list(unit.get("source_lines", []))
    if header_ln and 1 <= header_ln <= len(source_lines):
        scan_lines.append(source_lines[header_ln - 1])
    scan_lines.extend([str(x) for x in unit.get("body_lines", [])])
    for raw in scan_lines:
        code = _strip_comment(str(raw)).strip()
        if not code:
            continue
        m_type = re.match(r"^type\s*\(\s*([a-z_]\w*)\s*\)\s+function\b", code, re.IGNORECASE)
        if m_type:
            return Var(m_type.group(1).lower())
        m_int = re.match(r"^integer(?:\s*\([^)]*\))?\s+function\b", code, re.IGNORECASE)
        if m_int:
            return Var("int")
        m_real = re.match(r"^real\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|\d+)\s*\)\s+function\b", code, re.IGNORECASE)
        if m_real:
            kind_tok = m_real.group(1).lower()
            cty = kind_ctype_map.get(kind_tok, real_type)
            if kind_tok.isdigit():
                cty = "double" if int(kind_tok) >= 8 else "float"
            return Var(cty)
        if re.match(r"^real(?!\s*\()\s+function\b", code, re.IGNORECASE):
            return Var(real_type)
        if re.match(r"^double\s+precision\s+function\b", code, re.IGNORECASE):
            return Var("double")
        if re.match(r"^logical\s+function\b", code, re.IGNORECASE):
            return Var("int", is_logical=True)
        if re.match(r"^complex(?:\s*\([^)]*\))?\s+function\b", code, re.IGNORECASE):
            return Var(_complex_ctype(real_type))
        break
    return None


def _array_result_call_info(expr: str, vars_map: Dict[str, Var], real_type: str) -> Optional[tuple[str, Var, str]]:
    m_call = re.fullmatch(r"\s*([a-z_]\w*)\s*\((.*)\)\s*", expr, re.IGNORECASE)
    if not m_call:
        return None
    raw_args = [x.strip() for x in _split_args_top_level(m_call.group(2)) if x.strip()]
    callee = _resolve_generic_proc_name(m_call.group(1), raw_args, vars_map, real_type)
    rv = _proc_result_var(callee)
    if rv is None or not rv.is_array:
        return None
    return callee, rv, ", ".join(raw_args)


def _strip_comment(line: str) -> str:
    # Use shared quote-aware Fortran comment stripping.
    try:
        return fscan.strip_comment(line)
    except Exception:
        i = line.find("!")
        return line[:i] if i >= 0 else line


def _split_leading_paren_group(stmt: str, keyword: str) -> Optional[tuple[str, str]]:
    """Split `keyword(<group>)<rest>` with quote-aware balanced parens."""
    m = re.match(rf"^\s*{re.escape(keyword)}\s*\(", stmt, re.IGNORECASE)
    if not m:
        return None
    i = m.end() - 1  # points at '('
    depth = 0
    in_single = False
    in_double = False
    start = i + 1
    j = i
    while j < len(stmt):
        ch = stmt[j]
        if ch == "'" and not in_double:
            if in_single and j + 1 < len(stmt) and stmt[j + 1] == "'":
                j += 2
                continue
            in_single = not in_single
            j += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            j += 1
            continue
        if not in_single and not in_double:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    inner = stmt[start:j]
                    rest = stmt[j + 1 :]
                    return inner, rest
        j += 1
    return None


def _extract_fortran_comment(line: str) -> Optional[str]:
    in_single = False
    in_double = False
    for i, ch in enumerate(line):
        if ch == "'" and not in_double:
            in_single = not in_single
        elif ch == '"' and not in_single:
            in_double = not in_double
        elif ch == "!" and not in_single and not in_double:
            txt = line[i + 1 :].strip()
            return txt or None
    return None


def _first_unit_doc_comment(unit: Dict[str, object]) -> Optional[str]:
    body_line_nos: List[int] = list(unit.get("body_line_nos", []))
    source_lines: List[str] = list(unit.get("source_lines", []))
    if not body_line_nos or not source_lines:
        return None
    # Prefer standalone comment lines between header and first body statement.
    header_ln = int(unit.get("header_line_no", 1))
    body_start_ln = int(unit.get("body_start_line_no", body_line_nos[0]))
    for ln in range(max(1, header_ln + 1), min(body_start_ln, len(source_lines) + 1)):
        raw = source_lines[ln - 1].strip()
        if not raw:
            continue
        if raw.startswith("!"):
            txt = raw[1:].strip()
            if txt:
                return txt
            continue
        break
    for ln in body_line_nos:
        if not (1 <= ln <= len(source_lines)):
            continue
        raw = source_lines[ln - 1]
        cmt = _extract_fortran_comment(raw)
        if cmt:
            return cmt
        if _strip_comment(raw).strip():
            # Stop at first real statement/declaration if no leading comment.
            break
    return None


def _as_c_inline_comment(text: Optional[str]) -> str:
    if not text:
        return ""
    safe = text.replace("*/", "* /").strip()
    if not safe:
        return ""
    return f" /* {safe} */"


def _fortran_to_c_real_type(text: str) -> str:
    # If code defines dp from kind(1.0d0), use double.
    if re.search(r"kind\s*\(\s*1\.0d0\s*\)", text, re.IGNORECASE):
        return "double"
    return "float"


def _extract_kind_alias_c_types(text: str) -> Dict[str, str]:
    """Extract simple Fortran kind aliases and map to C scalar types.

    Examples:
    - integer, parameter :: sp = kind(1.0), dp = kind(1.0d0)
    - integer, parameter :: i8 = selected_int_kind(18)
    - integer, parameter :: qp = dp
    """
    out: Dict[str, str] = {}
    lines = text.splitlines()
    decl_re = re.compile(r"^\s*integer\s*,\s*parameter\s*::\s*(.+)$", re.IGNORECASE)
    k_single = re.compile(r"(?i)^\s*kind\s*\(\s*1(?:\.0*)?(?:e[+\-]?\d+)?\s*\)\s*$")
    k_double = re.compile(r"(?i)^\s*kind\s*\(\s*1(?:\.0*)?d[+\-]?\d+\s*\)\s*$")

    pending_alias: Dict[str, str] = {}
    for raw in lines:
        code = _strip_comment(raw).strip()
        if not code:
            continue
        m = decl_re.match(code)
        if not m:
            continue
        rhs_all = m.group(1).strip()
        for ent in [x.strip() for x in _split_args_top_level(rhs_all) if x.strip()]:
            if "=" not in ent:
                continue
            lhs, rhs = [x.strip() for x in ent.split("=", 1)]
            key = lhs.lower()
            rl = rhs.lower()
            if k_single.match(rl):
                out[key] = "float"
            elif k_double.match(rl):
                out[key] = "double"
            elif rl in {"int8", "int16", "int32"}:
                out[key] = "int"
            elif rl == "int64":
                out[key] = "long long"
            elif re.match(r"(?i)^selected_real_kind\s*\(", rl):
                p_val: Optional[int] = None
                r_val: Optional[int] = None
                inner = rl[rl.find("(") + 1 : rl.rfind(")")]
                for idx, arg in enumerate([x.strip() for x in _split_args_top_level(inner) if x.strip()]):
                    m_kw = re.match(r"(?i)^([pr])\s*=\s*([0-9]+)$", arg)
                    if m_kw:
                        if m_kw.group(1).lower() == "p":
                            p_val = int(m_kw.group(2))
                        else:
                            r_val = int(m_kw.group(2))
                        continue
                    if re.fullmatch(r"[0-9]+", arg):
                        if idx == 0:
                            p_val = int(arg)
                        elif idx == 1:
                            r_val = int(arg)
                p_eff = 0 if p_val is None else p_val
                r_eff = 0 if r_val is None else r_val
                if p_eff <= 6 and r_eff <= 37:
                    out[key] = "float"
                elif p_eff <= 15 and r_eff <= 307:
                    out[key] = "double"
            elif re.match(r"(?i)^selected_int_kind\s*\(\s*([0-9]+)\s*\)$", rl):
                m_digits = re.match(r"(?i)^selected_int_kind\s*\(\s*([0-9]+)\s*\)$", rl)
                assert m_digits is not None
                out[key] = "int" if int(m_digits.group(1)) <= 9 else "long long"
            elif re.match(r"^[a-z_]\w*$", rl, re.IGNORECASE):
                pending_alias[key] = rl

    # Resolve simple alias chains.
    changed = True
    while changed and pending_alias:
        changed = False
        for k, alias in list(pending_alias.items()):
            if alias in out:
                out[k] = out[alias]
                del pending_alias[k]
                changed = True
    return out


def _eval_int_expr(expr: str) -> Optional[int]:
    s = expr.strip()
    if not re.fullmatch(r"[0-9+\-*/() \t*]+", s):
        return None
    try:
        v = eval(s, {"__builtins__": None}, {})
    except Exception:
        return None
    if isinstance(v, int):
        return v
    return None


def _simplify_int_expr_text(expr: str) -> str:
    v = _eval_int_expr(expr)
    return str(v) if v is not None else expr


def _eval_int_expr_with_params(expr: str, vars_map: Dict[str, Var]) -> Optional[int]:
    s = expr.strip()
    if not s:
        return None
    pat = re.compile(r"\b[a-z_]\w*\b", re.IGNORECASE)
    prev = None
    while s != prev:
        prev = s
        changed = False
        def repl(m: re.Match[str]) -> str:
            nonlocal changed
            name = m.group(0).lower()
            v = vars_map.get(name)
            if v is None or not v.is_param or v.is_array or v.init is None:
                return m.group(0)
            raw = v.init.replace("_dp", "").replace("_DP", "")
            iv = _eval_int_expr(raw)
            if iv is None:
                return m.group(0)
            changed = True
            return str(iv)
        s = pat.sub(repl, s)
        if not changed:
            break
    return _eval_int_expr(s)



def _is_fortran_string_literal(text: str) -> bool:
    t = text.strip()
    return (len(t) >= 2 and ((t[0] == "'" and t[-1] == "'") or (t[0] == '"' and t[-1] == '"')))


def _unquote_fortran_string_literal(text: str) -> str:
    t = text.strip()
    if len(t) >= 2 and t[0] == "'" and t[-1] == "'":
        return t[1:-1].replace("''", "'")
    if len(t) >= 2 and t[0] == '"' and t[-1] == '"':
        return t[1:-1].replace('""', '"')
    return t


def _parse_basic_format_tokens(fmt_text: str) -> List[Dict[str, object]]:
    """Parse a small subset of Fortran character format strings.

    Supports literals, x/nx spacing, a, iw/i0, fw.d, ew.d, esw.d, gw.d,
    repeated descriptors like 2f7.2, and repeated groups like 3(i0,1x).
    """
    if not _is_fortran_string_literal(fmt_text):
        return []
    body = _unquote_fortran_string_literal(fmt_text).strip()
    if body.startswith('(') and body.endswith(')'):
        body = body[1:-1].strip()

    def parse_list(src: str) -> List[Dict[str, object]]:
        toks: List[Dict[str, object]] = []
        for raw in _split_args_top_level(src):
            item = raw.strip()
            if not item:
                continue
            toks.extend(parse_item(item))
        return toks

    def parse_item(item: str) -> List[Dict[str, object]]:
        item = item.strip()
        if not item:
            return []
        mstar = re.match(r'^\*\s*\((.*)\)$', item, re.IGNORECASE)
        if mstar:
            inner = parse_list(mstar.group(1).strip())
            return [{"kind": "repeat_group", "tokens": inner}]
        mgrp = re.match(r'^([0-9]+)\s*\((.*)\)$', item, re.IGNORECASE)
        if mgrp:
            rep = int(mgrp.group(1))
            inner = parse_list(mgrp.group(2).strip())
            return inner * rep
        if _is_fortran_string_literal(item):
            return [{"kind": "literal", "text": _unquote_fortran_string_literal(item)}]
        mrep = re.match(r'^([0-9]+)\s*(.*)$', item, re.IGNORECASE)
        rep = 1
        desc = item
        if mrep:
            cand = (mrep.group(2) or '').strip()
            if cand:
                rep = int(mrep.group(1))
                desc = cand
        dl = desc.lower().strip()
        if re.fullmatch(r'[0-9]*x', dl):
            nsp = int(dl[:-1] or '1')
            return [{"kind": "space", "count": nsp}] * rep
        if re.fullmatch(r'[0-9]*/', dl):
            nlb = int(dl[:-1] or '1')
            return [{"kind": "newline", "count": nlb}] * rep
        if dl.startswith('es'):
            m = re.match(r'^es([0-9]+)(?:\.([0-9]+))?$', dl)
            if m:
                w = int(m.group(1))
                p = int(m.group(2) or '6')
                return [{"kind": "data", "desc": "es", "width": w, "prec": p}] * rep
        for pref in ('i', 'f', 'e', 'g', 'a', 'l'):
            if dl.startswith(pref):
                if pref == 'a':
                    m = re.match(r'^a([0-9]+)?$', dl)
                    if m:
                        w = m.group(1)
                        return [{"kind": "data", "desc": 'a', "width": int(w) if w else None}] * rep
                elif pref == 'i':
                    m = re.match(r'^i([0-9]+)$', dl)
                    if m:
                        w = int(m.group(1))
                        return [{"kind": "data", "desc": 'i', "width": w}] * rep
                elif pref == 'l':
                    m = re.match(r'^l([0-9]+)?$', dl)
                    if m:
                        w = m.group(1)
                        return [{"kind": "data", "desc": 'l', "width": int(w) if w else None}] * rep
                else:
                    m = re.match(rf'^{pref}([0-9]+)(?:\.([0-9]+))?$', dl)
                    if m:
                        w = int(m.group(1))
                        p = int(m.group(2) or '6')
                        return [{"kind": "data", "desc": pref, "width": w, "prec": p}] * rep
        return []

    return parse_list(body)


def _printf_fmt_for_basic_format_token(tok: Dict[str, object], ctype: str) -> str:
    desc = str(tok.get('desc', '')).lower()
    width = tok.get('width')
    prec = tok.get('prec')
    if desc == 'i':
        return f"%{width}d" if width not in {None, 0} else "%d"
    if desc in {'f'}:
        w = int(width) if width is not None else 0
        p = int(prec) if prec is not None else 6
        return f"%{w}.{p}f" if w > 0 else f"%.{p}f"
    if desc in {'e', 'es'}:
        w = int(width) if width is not None else 0
        p = int(prec) if prec is not None else 6
        return f"%{w}.{p}e" if w > 0 else f"%.{p}e"
    if desc == 'g':
        w = int(width) if width is not None else 0
        p = int(prec) if prec is not None else 6
        return f"%{w}.{p}g" if w > 0 else f"%.{p}g"
    if desc == 'a':
        w = int(width) if width is not None else 0
        return f"%{w}s" if w > 0 else "%s"
    if desc == 'l':
        return "%d"
    return "%g" if (ctype or '').lower() != 'int' else "%d"


def _list_directed_scalar_fmt(ctype: str) -> str:
    cty = (ctype or '').lower()
    if cty == 'int':
        return "%12d"
    if cty in {'long long', 'long long int'}:
        return "%12lld"
    if cty == 'logical':
        return "%s"
    if cty == 'string':
        return "%s"
    if cty == 'complex':
        return "%s"
    return "%13.6f"


def _prefer_general_real_scalar_fmt(expr: str, ctype: str) -> bool:
    cty = (ctype or "").lower()
    if cty not in {"float", "double"}:
        return False
    return bool(
        re.search(
            r"\b(?:FLT_|DBL_|nextafterf?|scalbnf?|ilogbf?|fabsf?|HUGE_VALF?)\b",
            expr,
            re.IGNORECASE,
        )
    )


def _complex_expr_real_type(expr: str, vars_map: Dict[str, Var], real_type: str) -> str:
    s = expr.strip()
    m_name = re.fullmatch(r'([a-z_]\w*)', s, re.IGNORECASE)
    if m_name:
        vv = vars_map.get(m_name.group(1).lower())
        if vv is not None and _is_complex_ctype(vv.ctype):
            return 'double' if 'double' in (vv.ctype or '').lower() else 'float'
    m_call = re.fullmatch(r'([a-z_]\w*)\s*\((.*)\)$', s, re.IGNORECASE)
    if m_call:
        callee = _resolve_generic_proc_name(
            m_call.group(1),
            [x.strip() for x in _split_args_top_level(m_call.group(2)) if x.strip()],
            vars_map,
            real_type,
        )
        rv = _proc_result_var(callee)
        if rv is not None and _is_complex_ctype(rv.ctype):
            return 'double' if 'double' in (rv.ctype or '').lower() else 'float'
    toks = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", s, flags=re.IGNORECASE)}
    for tok in toks:
        vv = vars_map.get(tok)
        if vv is not None and _is_complex_ctype(vv.ctype):
            return 'double' if 'double' in (vv.ctype or '').lower() else 'float'
    return real_type


def _emit_list_directed_scalar_printf(
    out: List[str],
    indent: int,
    expr: str,
    ctype: str,
    vars_map: Dict[str, Var],
    real_type: str,
    prefix_expr: Optional[str] = None,
    newline: bool = False,
) -> None:
    cty = (ctype or '').lower()
    prefix = prefix_expr or '""'
    if cty == "string":
        suffix = '\\n' if newline else ''
        out.append(" " * indent + f'printf("%s%s{suffix}", {prefix}, {expr});')
        return
    if cty == "trim_string":
        suffix = '\\n' if newline else ''
        out.append(" " * indent + f'printf("%s%.*s{suffix}", {prefix}, len_trim_s({expr}), {expr});')
        return
    if cty == "int":
        suffix = '\\n' if newline else ''
        out.append(" " * indent + f'printf("%s%d{suffix}", {prefix}, {expr});')
        return
    if cty in {"long long", "long long int"}:
        suffix = '\\n' if newline else ''
        out.append(" " * indent + f'printf("%s%lld{suffix}", {prefix}, {expr});')
        return
    if cty == "logical":
        suffix = '\\n' if newline else ''
        out.append(" " * indent + f'printf("%s%s{suffix}", {prefix}, ({expr}) ? "T" : "F");')
        return
    if cty == "complex":
        c_real_type = _complex_expr_real_type(expr, vars_map, real_type)
        if c_real_type not in {"float", "double"}:
            c_real_type = real_type
        real_expr = _complex_real_expr(expr, c_real_type)
        imag_expr = _complex_imag_expr(expr, c_real_type)
        suffix = '\\n' if newline else ''
        out.append(" " * indent + f'printf("%s(%g,%g){suffix}", {prefix}, {real_expr}, {imag_expr});')
        return
    if cty in {"float", "double"} and _prefer_general_real_scalar_fmt(expr, cty):
        suffix = '\\n' if newline else ''
        trail = '    ' if newline and _list_directed_has_trailing_real([cty]) else ''
        fmt = "%s%.9g" if cty == "float" else "%s%.17g"
        out.append(" " * indent + f'printf("{fmt}{trail}{suffix}", {prefix}, {expr});')
        return
    suffix = '\\n' if newline else ''
    trail = '    ' if newline and _list_directed_has_trailing_real([cty]) else ''
    out.append(" " * indent + f'printf("%s{_list_directed_scalar_fmt(cty)}{trail}{suffix}", {prefix}, {expr});')


def _list_directed_has_trailing_real(ctypes: List[str]) -> bool:
    return any((ct or '').lower() not in {'int', 'logical', 'string'} for ct in ctypes)


def _emit_list_directed_1d_value_stream(
    out: List[str],
    indent: int,
    value_expr: str,
    ctype: str,
    loop_header: str,
    vars_map: Optional[Dict[str, Var]] = None,
) -> None:
    cty = (ctype or '').lower()
    if cty == 'int' and vars_map is not None:
        m_base = re.match(r'^\s*([a-z_]\w*)\s*\[', value_expr, re.IGNORECASE)
        if m_base:
            vv = vars_map.get(m_base.group(1).lower())
            if vv is not None and vv.is_logical:
                cty = 'logical'
    out.append(' ' * indent + '{')
    if cty == 'int':
        out.append(' ' * (indent + 3) + loop_header + ' {')
        out.append(' ' * (indent + 6) + f'printf("%12d", {value_expr});')
        out.append(' ' * (indent + 3) + '}')
        out.append(' ' * (indent + 3) + 'printf("\\n");')
    elif cty == 'logical':
        out.append(' ' * (indent + 3) + 'int __first = 1;')
        out.append(' ' * (indent + 3) + loop_header + ' {')
        out.append(' ' * (indent + 6) + f'printf("%s%s", __first ? "" : " ", ({value_expr}) ? "T" : "F");')
        out.append(' ' * (indent + 6) + '__first = 0;')
        out.append(' ' * (indent + 3) + '}')
        out.append(' ' * (indent + 3) + 'printf("\\n");')
    elif cty == 'string':
        out.append(' ' * (indent + 3) + 'int __first = 1;')
        out.append(' ' * (indent + 3) + loop_header + ' {')
        out.append(' ' * (indent + 6) + f'printf("%s%s", __first ? "" : " ", {value_expr});')
        out.append(' ' * (indent + 6) + '__first = 0;')
        out.append(' ' * (indent + 3) + '}')
        out.append(' ' * (indent + 3) + 'printf("\\n");')
    else:
        out.append(' ' * (indent + 3) + 'int __first = 1;')
        out.append(' ' * (indent + 3) + loop_header + ' {')
        out.append(' ' * (indent + 6) + f'if (__first) printf("%13.6f", {value_expr});')
        out.append(' ' * (indent + 6) + f'else printf("    %13.6f", {value_expr});')
        out.append(' ' * (indent + 6) + '__first = 0;')
        out.append(' ' * (indent + 3) + '}')
        out.append(' ' * (indent + 3) + 'printf("    \\n");')
    out.append(' ' * indent + '}')


def _var_render_ctype(v: Var, real_type: str) -> str:
    if (v.ctype or '').lower() == 'char *':
        return 'string'
    if v.is_logical:
        return 'logical'
    if _is_complex_ctype(v.ctype):
        return 'complex'
    return (v.ctype or real_type).lower()



def _find_array_constructor_spans(expr: str) -> List[tuple[int, int, List[str]]]:
    spans: List[tuple[int, int, List[str]]] = []
    in_single = False
    in_double = False
    depth = 0
    start: Optional[int] = None
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch == "'" and not in_double:
            if in_single and i + 1 < len(expr) and expr[i + 1] == "'":
                i += 2
                continue
            in_single = not in_single
            i += 1
            continue
        if ch == '"' and not in_single:
            if in_double and i + 1 < len(expr) and expr[i + 1] == '"':
                i += 2
                continue
            in_double = not in_double
            i += 1
            continue
        if not in_single and not in_double:
            if ch == '[':
                if depth == 0:
                    start = i
                depth += 1
            elif ch == ']' and depth > 0:
                depth -= 1
                if depth == 0 and start is not None:
                    ctor_text = expr[start : i + 1]
                    items = _array_constructor_items(ctor_text)
                    if items is not None:
                        spans.append((start, i + 1, items))
                    start = None
        i += 1
    return spans


def _merge_numeric_ctypes(ctypes: List[str], real_type: str) -> str:
    merged = 'int'
    for ct in ctypes:
        cty = (ct or '').lower()
        if cty == 'string':
            return 'string'
        if cty != 'int':
            merged = real_type.lower()
    return merged


def _array_constructor_ctype(items: List[str], vars_map: Dict[str, Var], real_type: str) -> str:
    if not items:
        return real_type.lower()
    ctypes = [_format_item_ctype(it, vars_map, real_type) for it in items]
    return _merge_numeric_ctypes(ctypes, real_type)


def _broadcast_expr_ctype(
    expr: str,
    ctor_spans: List[tuple[int, int, List[str]]],
    vars_map: Dict[str, Var],
    real_type: str,
) -> str:
    ctypes: List[str] = []
    for _, _, items in ctor_spans:
        ctypes.append(_array_constructor_ctype(items, vars_map, real_type))
    toks = {t.lower() for t in re.findall(r'\b[a-z_]\w*\b', _strip_comment(expr), flags=re.IGNORECASE)}
    for tok in sorted(toks):
        vv = vars_map.get(tok)
        if vv is None:
            continue
        if (vv.ctype or '').lower() == 'char *':
            ctypes.append('string')
        else:
            ctypes.append((vv.ctype or real_type).lower())
    if re.search(r'(?i)(?:[0-9]\.[0-9]*|\.[0-9]+|[0-9][eEdD][+\-]?[0-9])', expr):
        ctypes.append(real_type.lower())
    if re.search(r'(?i)\b(?:real|dble|anint|abs|sqrt|sin|cos|tan|asin|acos|atan|exp|log|log10)\s*\(', expr):
        ctypes.append(real_type.lower())
    if not ctypes:
        return real_type.lower()
    return _merge_numeric_ctypes(ctypes, real_type)


def _emit_list_directed_ctor_broadcast_expr(
    out: List[str],
    indent: int,
    expr_raw: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
) -> bool:
    ctor_spans = _find_array_constructor_spans(expr_raw)
    if not ctor_spans:
        return False
    if any(_parse_implied_do_item(it) is not None for _, _, items in ctor_spans for it in items):
        return False
    if re.match(r'^\s*[a-z_]\w*\s*\(.*\)\s*$', expr_raw, re.IGNORECASE):
        return False
    ctor_lens = [len(items) for _, _, items in ctor_spans]
    if ctor_lens and any(n != ctor_lens[0] for n in ctor_lens):
        return False
    toks0 = {t.lower() for t in re.findall(r'\b[a-z_]\w*\b', _strip_comment(expr_raw), flags=re.IGNORECASE)}
    arrs0 = [t for t in sorted(toks0) if t in vars_map and vars_map[t].is_array]
    if any(re.search(rf'\b{re.escape(a)}\s*\(', expr_raw, flags=re.IGNORECASE) for a in arrs0):
        return False
    npr_expr: Optional[str] = str(ctor_lens[0]) if ctor_lens else None
    if arrs0:
        base = vars_map.get(arrs0[0])
        if base is None:
            return False
        compatible = all((vars_map.get(a) is not None and vars_map.get(a).dim == base.dim) for a in arrs0)
        if not compatible:
            return False
        if base.is_allocatable and len(_dim_parts(base.dim)) == 1:
            arr_npr = _alloc_len_name(arrs0[0])
        else:
            arr_npr = _dim_product_expr(base.dim or '1', vars_map, real_type, byref_scalars, assumed_extents)
        if npr_expr is None:
            npr_expr = arr_npr
    if npr_expr is None:
        return False
    expr_i_parts: List[str] = []
    ctor_decls: List[str] = []
    pos = 0
    for idx, (start, stop, items) in enumerate(ctor_spans):
        expr_i_parts.append(expr_raw[pos:start])
        cty = _array_constructor_ctype(items, vars_map, real_type)
        cname = f'__ctor_{idx}'
        cdecl = 'char *' if cty == 'string' else ('int' if cty == 'int' else real_type)
        cinit = ', '.join(_convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for it in items)
        ctor_decls.append(f'{cdecl} {cname}[] = {{{cinit}}};')
        expr_i_parts.append(f'{cname}[i_pr]')
        pos = stop
    expr_i_parts.append(expr_raw[pos:])
    expr_i = ''.join(expr_i_parts)
    for a in sorted(arrs0, key=len, reverse=True):
        expr_i = re.sub(rf'\b{re.escape(a)}\b', f'{a}[i_pr]', expr_i, flags=re.IGNORECASE)
    cit = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
    expr_cty = _broadcast_expr_ctype(expr_raw, ctor_spans, vars_map, real_type)
    out.append(' ' * indent + '{')
    for decl in ctor_decls:
        out.append(' ' * (indent + 3) + decl)
    if expr_cty == 'int':
        out.append(' ' * (indent + 3) + f'for (int i_pr = 0; i_pr < {npr_expr}; ++i_pr) {{')
        out.append(' ' * (indent + 6) + f'printf("%12d", {cit});')
        out.append(' ' * (indent + 3) + '}')
        out.append(' ' * (indent + 3) + 'printf("\\n");')
    elif expr_cty == 'string':
        out.append(' ' * (indent + 3) + 'int __first = 1;')
        out.append(' ' * (indent + 3) + f'for (int i_pr = 0; i_pr < {npr_expr}; ++i_pr) {{')
        out.append(' ' * (indent + 6) + f'printf("%s%s", __first ? "" : " ", {cit});')
        out.append(' ' * (indent + 6) + '__first = 0;')
        out.append(' ' * (indent + 3) + '}')
        out.append(' ' * (indent + 3) + 'printf("\\n");')
    else:
        out.append(' ' * (indent + 3) + 'int __first = 1;')
        out.append(' ' * (indent + 3) + f'for (int i_pr = 0; i_pr < {npr_expr}; ++i_pr) {{')
        out.append(' ' * (indent + 6) + f'if (__first) printf("%13.6f", {cit});')
        out.append(' ' * (indent + 6) + f'else printf("    %13.6f", {cit});')
        out.append(' ' * (indent + 6) + '__first = 0;')
        out.append(' ' * (indent + 3) + '}')
        out.append(' ' * (indent + 3) + 'printf("    \\n");')
    out.append(' ' * indent + '}')
    return True


def _emit_formatted_1d_array_output(
    out: List[str],
    indent: int,
    arr_name: str,
    arr_var: Var,
    fmt_text: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: set[str],
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    toks = _parse_basic_format_tokens(fmt_text)
    if not toks:
        return False
    if not any(tok.get('kind') == 'data' for tok in toks):
        return False
    if arr_var.is_allocatable:
        npr = _dim_product_from_parts(
            _resolved_dim_parts(arr_var, arr_name, assumed_extents),
            vars_map,
            real_type,
            byref_scalars,
            assumed_extents,
        )
    else:
        npr = _dim_product_expr(arr_var.dim or '1', vars_map, real_type, byref_scalars, assumed_extents)
    ctype = (arr_var.ctype or real_type).lower()
    out.append(' ' * indent + '{')
    out.append(' ' * (indent + 3) + 'int __idx_fmt = 0;')
    out.append(' ' * (indent + 3) + f'while (__idx_fmt < {npr}) {{')
    for tok in toks:
        kind = tok.get('kind')
        if kind == 'space':
            nsp = int(tok.get('count', 1))
            lit = (' ' * nsp).replace('\\', '\\\\').replace('\"', '\\\"')
            out.append(' ' * (indent + 6) + f'printf("%s", "{lit}");')
        elif kind == 'newline':
            nlb = int(tok.get('count', 1))
            for _ in range(nlb):
                out.append(' ' * (indent + 6) + 'printf("\\n");')
        elif kind == 'literal':
            lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('\"', '\\\"')
            out.append(' ' * (indent + 6) + f'printf("%s", "{lit}");')
        elif kind == 'data':
            pf = _printf_fmt_for_basic_format_token(tok, ctype).replace('\\', '\\\\').replace('\"', '\\\"')
            out.append(' ' * (indent + 6) + f'if (__idx_fmt < {npr}) printf("{pf}", {arr_name}[__idx_fmt++]);')
    out.append(' ' * (indent + 6) + 'printf("\\n");')
    out.append(' ' * (indent + 3) + '}')
    out.append(' ' * indent + '}')
    return True


def _resolved_format_text(fmt_expr: str, vars_map: Dict[str, Var]) -> Optional[str]:
    fmt_strip = fmt_expr.strip()
    if _is_fortran_string_literal(fmt_strip):
        return fmt_strip
    m_id = re.match(r'^\s*([a-z_]\w*)\s*$', fmt_strip, re.IGNORECASE)
    if not m_id:
        return None
    vv = vars_map.get(m_id.group(1).lower())
    if vv is None or (vv.ctype or '').lower() != 'char *':
        return None
    init = (vv.init or '').strip()
    if _is_fortran_string_literal(init):
        return init
    return None


def _normalize_actual_args(
    callee: str,
    raw_args: List[str],
    proc_arg_names: Dict[str, List[str]],
) -> List[str]:
    arg_names = proc_arg_names.get(callee.lower(), [])
    if not arg_names:
        return list(raw_args)
    ordered: List[Optional[str]] = [None] * len(arg_names)
    next_pos = 0
    extras: List[str] = []
    for a in raw_args:
        m_kw = re.match(r'^\s*([a-z_]\w*)\s*=\s*(.+)$', a, re.IGNORECASE)
        if m_kw:
            key = m_kw.group(1).lower()
            if key in arg_names:
                ordered[arg_names.index(key)] = m_kw.group(2).strip()
                continue
        while next_pos < len(ordered) and ordered[next_pos] is not None:
            next_pos += 1
        if next_pos < len(ordered):
            ordered[next_pos] = a.strip()
            next_pos += 1
        else:
            extras.append(a.strip())
    return [x for x in ordered if x is not None] + extras

def _format_item_ctype(expr: str, vars_map: Dict[str, Var], real_type: str) -> str:
    s = _rewrite_type_bound_calls(expr.strip(), vars_map, real_type)
    if _is_fortran_string_literal(s):
        return 'string'
    if re.fullmatch(r"(?i)\.(?:true|false)\.", s):
        return 'logical'
    if re.search(r"(?i)\.(?:and|or|not|eqv|neqv)\.", s):
        return 'logical'
    if _parse_complex_literal(s) is not None:
        return 'complex'
    if re.fullmatch(r'[+\-]?\d+(?:_(?:[a-z_]\w*|\d+))?', s, re.IGNORECASE):
        return 'int'
    if re.fullmatch(r"[+\-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eEdD][+\-]?\d+)?(?:_(?:[a-z_]\w*|\d+))?", s, re.IGNORECASE):
        return real_type.lower()
    if re.match(r'^(?:allocated|present)\s*\(', s, re.IGNORECASE):
        return 'logical'
    if re.match(r'^(?:rank|size|len|len_trim|index|scan|verify|iachar|minloc|maxloc|findloc|selected_real_kind|selected_int_kind|digits|maxexponent|minexponent|precision|radix|range|bit_size|exponent|storage_size)\s*\(', s, re.IGNORECASE):
        return 'int'
    if re.match(r'^(?:shape|lbound|ubound)\s*\(', s, re.IGNORECASE):
        return 'int'
    if re.match(r'^(?:trim|adjustl|adjustr|repeat|achar|char)\s*\(', s, re.IGNORECASE):
        return 'string'
    if re.fullmatch(r'__n_[a-z_]\w*(?:_\d+)?', s, re.IGNORECASE):
        return 'int'
    m_sub_arr = re.match(r'^([a-z_]\w*)\s*\((.+)\)\s*\((.+):(.*)\)$', s, re.IGNORECASE)
    if m_sub_arr:
        vv = vars_map.get(m_sub_arr.group(1).lower())
        if vv is not None and (vv.ctype or '').lower() == 'char *':
            return 'string'
    m_sub = re.match(r'^([a-z_]\w*)\s*\((.+):(.*)\)$', s, re.IGNORECASE)
    if m_sub:
        vv = vars_map.get(m_sub.group(1).lower())
        if vv is not None and (vv.ctype or '').lower() == 'char *' and not vv.is_array:
            return 'string'
    m_part = re.match(r'^([a-z_]\w*)\s*%\s*(re|im)\s*$', s, re.IGNORECASE)
    if m_part:
        vv = vars_map.get(m_part.group(1).lower())
        if vv is not None and _is_complex_ctype(vv.ctype):
            return real_type.lower()
    if "%" in s:
        parts = [x.strip() for x in s.split("%") if x.strip()]
        if len(parts) >= 2:
            fld_spec = _derived_field_spec(parts[0], parts[1:], vars_map)
            if fld_spec is not None and _derived_field_rank(fld_spec) == 0:
                fld_base = (_derived_field_base_ctype(fld_spec) or real_type).lower()
                if fld_base == "char *":
                    return "string"
                if fld_base == "logical":
                    return "logical"
                if _is_complex_ctype(fld_base):
                    return "complex"
                return fld_base
    rewritten_overload = _rewrite_overloaded_operator_expr(s, vars_map, real_type)
    if rewritten_overload != s:
        return _format_item_ctype(rewritten_overload, vars_map, real_type)
    m_call = re.fullmatch(r'([a-z_]\w*)\s*\((.*)\)$', s, re.IGNORECASE)
    if m_call:
        call_name = m_call.group(1).lower()
        call_args = [x.strip() for x in _split_args_top_level(m_call.group(2)) if x.strip()]
        if call_name in {"mod", "modulo"} and len(call_args) >= 2:
            def _looks_int_arg(raw: str) -> bool:
                t = raw.strip().lower()
                if re.fullmatch(r'[+\-]?\d+', t):
                    return True
                if re.fullmatch(r'[a-z_]\w*', t):
                    vv = vars_map.get(t)
                    return vv is not None and (((vv.ctype or "").lower() in {"int", "long long", "long long int"}) or vv.is_logical)
                if re.match(r"^(?:int|nint|floor|ceiling)\s*\(", t, re.IGNORECASE):
                    return True
                return False
            return "int" if _looks_int_arg(call_args[0]) and _looks_int_arg(call_args[1]) else real_type.lower()
        if call_name in {"epsilon", "tiny", "nearest", "spacing", "fraction", "set_exponent", "scale"} and call_args:
            return _format_item_ctype(call_args[0], vars_map, real_type)
        if call_name == "huge" and call_args:
            arg_ct = _format_item_ctype(call_args[0], vars_map, real_type)
            if arg_ct in {"int", "long long", "long long int"}:
                return arg_ct
            return arg_ct
        if call_name in {"cmplx", "conjg"}:
            return "complex"
        if call_name in {"real", "aimag"} and call_args and _format_item_ctype(call_args[0], vars_map, real_type) == "complex":
            return real_type.lower()
        if call_name == "abs" and call_args and _format_item_ctype(call_args[0], vars_map, real_type) == "complex":
            return real_type.lower()
        if call_name == "sqrt" and call_args and _format_item_ctype(call_args[0], vars_map, real_type) == "complex":
            return "complex"
        callee = _resolve_generic_proc_name(
            m_call.group(1),
            call_args,
            vars_map,
            real_type,
        )
        rv = _proc_result_var(callee)
        if rv is not None:
            if (rv.ctype or '').lower() == 'char *':
                return 'string'
            if rv.is_logical:
                return 'logical'
            if _is_complex_ctype(rv.ctype):
                return 'complex'
            return (rv.ctype or real_type).lower()

    def _infer_numeric_ctype(text: str) -> Optional[str]:
        t = text.strip()
        if not t:
            return None
        if t.startswith('(') and t.endswith(')'):
            inner = t[1:-1].strip()
            if inner:
                return _infer_numeric_ctype(inner)
        if re.fullmatch(r'[+\-]?\d+(?:_(?:[a-z_]\w*|\d+))?', t, re.IGNORECASE):
            return 'int'
        if re.fullmatch(r"[+\-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eEdD][+\-]?\d+)?(?:_(?:[a-z_]\w*|\d+))?", t, re.IGNORECASE):
            return real_type.lower()
        if _parse_complex_literal(t) is not None:
            return 'complex'
        m_merge = re.match(r'(?is)^merge\s*\((.*)\)$', t)
        if m_merge:
            args = [x.strip() for x in _split_args_top_level(m_merge.group(1)) if x.strip()]
            if len(args) >= 2:
                ct0 = _infer_numeric_ctype(args[0])
                ct1 = _infer_numeric_ctype(args[1])
                if ct0 == 'string' or ct1 == 'string':
                    return 'string'
                if ct0 == 'complex' or ct1 == 'complex':
                    return 'complex'
                if ct0 == 'int' and ct1 == 'int':
                    return 'int'
                if ct0 is not None and ct1 is not None:
                    return real_type.lower()
        m_var = re.fullmatch(r'([a-z_]\w*)(?:\s*\(.*\))?$', t, re.IGNORECASE)
        if m_var:
            vv = vars_map.get(m_var.group(1).lower())
            if vv is not None:
                if (vv.ctype or '').lower() == 'char *':
                    return 'string'
                if vv.is_logical:
                    return 'logical'
                if _is_complex_ctype(vv.ctype):
                    return 'complex'
                return (vv.ctype or real_type).lower()
        toks = [tok.lower() for tok in re.findall(r'\b[a-z_]\w*\b', t, flags=re.IGNORECASE)]
        if toks:
            saw_var = False
            all_int = True
            any_real = bool(re.search(r'[.]|[eEdD][+\-]?\d', t))
            for tok in toks:
                if tok in {'true', 'false', 'and', 'or', 'not', 'eqv', 'neqv'}:
                    continue
                vv = vars_map.get(tok)
                if vv is None:
                    return None
                saw_var = True
                cty = (vv.ctype or real_type).lower()
                if cty == 'char *':
                    return 'string'
                if vv.is_logical:
                    return 'logical'
                if _is_complex_ctype(vv.ctype):
                    return 'complex'
                if cty != 'int':
                    all_int = False
                    any_real = True
            if saw_var:
                if any(vars_map.get(tok) is not None and vars_map[tok].is_logical for tok in toks if vars_map.get(tok) is not None):
                    return 'logical'
                return 'int' if all_int and not any_real else ('complex' if any(_is_complex_ctype(vars_map.get(tok).ctype if vars_map.get(tok) else None) for tok in toks if vars_map.get(tok) is not None) else real_type.lower())
        return None

    cty_infer = _infer_numeric_ctype(s)
    if cty_infer is not None:
        return cty_infer
    m = re.match(r'^([a-z_]\w*)$', s, re.IGNORECASE)
    if m:
        vv = vars_map.get(m.group(1).lower())
        if vv is not None:
            if (vv.ctype or '').lower() == 'char *':
                return 'string'
            if vv.is_logical:
                return 'logical'
            if _is_complex_ctype(vv.ctype):
                return 'complex'
            return (vv.ctype or real_type).lower()
    return real_type.lower()


def _emit_list_directed_derived_var(
    out: List[str],
    indent: int,
    nm: str,
    vars_map: Dict[str, Var],
    real_type: str,
) -> bool:
    vv = vars_map.get(nm.lower())
    if vv is None:
        return False
    fields = _ACTIVE_DERIVED_TYPES.get((vv.ctype or '').lower())
    if not fields:
        return False
    fmts: List[str] = []
    cargs: List[str] = []
    ctypes_ld: List[str] = []
    for fld_name, fld_ctype in fields:
        cty = (fld_ctype or real_type).lower()
        ctypes_ld.append(cty)
        fmts.append(_list_directed_scalar_fmt(cty))
        cargs.append(f"{nm}.{fld_name}")
    trail = '    ' if _list_directed_has_trailing_real(ctypes_ld) else ''
    out.append(' ' * indent + f'printf("{"".join(fmts)}{trail}\\n", {", ".join(cargs)});')
    return True


def _emit_list_directed_derived_expr(
    out: List[str],
    indent: int,
    expr_raw: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
) -> bool:
    s = expr_raw.strip()
    m_elem = re.match(r'^([a-z_]\w*)\s*\(\s*(.+?)\s*\)$', s, re.IGNORECASE)
    if m_elem:
        base = m_elem.group(1).lower()
        vv = vars_map.get(base)
        if vv is not None and vv.is_array:
            fields = _ACTIVE_DERIVED_TYPES.get((vv.ctype or '').lower())
            if fields:
                cexpr = _convert_expr(s, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                fmts: List[str] = []
                cargs: List[str] = []
                ctypes_ld: List[str] = []
                for fld_name, fld_ctype in fields:
                    cty = (_derived_field_base_ctype(fld_ctype) or real_type).lower()
                    if _derived_field_rank(fld_ctype) != 0:
                        return False
                    ctypes_ld.append(cty)
                    fmts.append(_list_directed_scalar_fmt(cty))
                    cargs.append(f"{cexpr}.{fld_name}")
                trail = '    ' if _list_directed_has_trailing_real(ctypes_ld) else ''
                out.append(' ' * indent + f'printf("{"".join(fmts)}{trail}\\n", {", ".join(cargs)});')
                return True
    m_whole = re.match(r'^([a-z_]\w*)$', s, re.IGNORECASE)
    if m_whole:
        base = m_whole.group(1).lower()
        vv = vars_map.get(base)
        if vv is not None and vv.is_array:
            fields = _ACTIVE_DERIVED_TYPES.get((vv.ctype or '').lower())
            if fields:
                dparts = _resolved_dim_parts(vv, base, assumed_extents)
                npr = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars or set(), assumed_extents)
                out.append(' ' * indent + '{')
                out.append(' ' * (indent + 3) + f'for (int i_pr = 0; i_pr < ({npr}); ++i_pr) {{')
                fmts: List[str] = []
                cargs: List[str] = []
                ctypes_ld: List[str] = []
                for fld_name, fld_ctype in fields:
                    cty = (_derived_field_base_ctype(fld_ctype) or real_type).lower()
                    if _derived_field_rank(fld_ctype) != 0:
                        return False
                    ctypes_ld.append(cty)
                    fmts.append(_list_directed_scalar_fmt(cty))
                    cargs.append(f"{base}[i_pr].{fld_name}")
                trail = '    ' if _list_directed_has_trailing_real(ctypes_ld) else ''
                out.append(' ' * (indent + 6) + f'printf("{"".join(fmts)}{trail}\\n", {", ".join(cargs)});')
                out.append(' ' * (indent + 3) + '}')
                out.append(' ' * indent + '}')
                return True
    return False



def _derived_field_spec(base_name: str, field_path: List[str], vars_map: Dict[str, Var]) -> Optional[str]:
    vv = vars_map.get(base_name.lower())
    if vv is None:
        return None
    dt_name = (vv.ctype or '').lower()
    spec: Optional[str] = None
    for fld in field_path:
        fields = _ACTIVE_DERIVED_TYPES.get(dt_name)
        if not fields:
            return None
        spec = None
        for fld_name, fld_ctype in fields:
            if fld_name.lower() == fld.lower():
                spec = fld_ctype
                break
        if spec is None:
            return None
        base = spec
        if ' allocatable[' in base:
            base = base.split(' allocatable[', 1)[0].strip()
        elif '[' in base and base.endswith(']'):
            base = base.rsplit('[', 1)[0].strip()
        dt_name = base.lower()
    return spec


def _derived_field_base_ctype(spec: str) -> str:
    if ' allocatable[' in spec:
        return spec.split(' allocatable[', 1)[0].strip()
    if '[' in spec and spec.endswith(']'):
        return spec.rsplit('[', 1)[0].strip()
    return spec.strip()


def _derived_field_rank(spec: str) -> int:
    m = re.search(r' allocatable\[([^\[\]]+)\]$', spec)
    if m:
        return len([x for x in _split_args_top_level(m.group(1)) if x.strip()])
    m = re.search(r'\[([^\[\]]+)\]$', spec)
    if m:
        return len([x for x in _split_args_top_level(m.group(1)) if x.strip()])
    return 0


def _is_allocatable_derived_field(spec: str) -> bool:
    return ' allocatable[' in spec


def _expr_derived_type(expr: str, vars_map: Dict[str, Var]) -> Optional[str]:
    s = expr.strip()
    m_name = re.fullmatch(r"([a-z_]\w*)", s, re.IGNORECASE)
    if m_name:
        vv = vars_map.get(m_name.group(1).lower())
        if vv is not None:
            cty = (vv.ctype or "").lower()
            if cty in _ACTIVE_TYPE_BOUND_BINDINGS:
                return cty
        return None
    if "%" not in s:
        return None
    parts = [x.strip().lower() for x in s.split("%") if x.strip()]
    if len(parts) < 2:
        return None
    spec = _derived_field_spec(parts[0], parts[1:], vars_map)
    if spec is None:
        return None
    base = _derived_field_base_ctype(spec).lower()
    return base if base in _ACTIVE_TYPE_BOUND_BINDINGS else None


def _resolve_type_bound_proc_name(obj_expr: str, method_name: str, vars_map: Dict[str, Var]) -> Optional[str]:
    dt_name = _expr_derived_type(obj_expr, vars_map)
    if not dt_name:
        return None
    return _ACTIVE_TYPE_BOUND_BINDINGS.get(dt_name, {}).get(method_name.lower())


def _rewrite_type_bound_calls(expr: str, vars_map: Dict[str, Var], real_type: str) -> str:
    out: List[str] = []
    i = 0
    in_single = False
    in_double = False
    while i < len(expr):
        ch = expr[i]
        if ch == "'" and not in_double:
            if in_single and i + 1 < len(expr) and expr[i + 1] == "'":
                out.append("''")
                i += 2
                continue
            in_single = not in_single
            out.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            i += 1
            continue
        if in_single or in_double:
            out.append(ch)
            i += 1
            continue
        if ch.isalpha() or ch == "_":
            j = i + 1
            while j < len(expr) and (expr[j].isalnum() or expr[j] == "_"):
                j += 1
            probe = j
            last_chain_end = j
            rewritten = False
            while True:
                while probe < len(expr) and expr[probe].isspace():
                    probe += 1
                if probe >= len(expr) or expr[probe] != "%":
                    break
                ident_start = probe + 1
                while ident_start < len(expr) and expr[ident_start].isspace():
                    ident_start += 1
                if ident_start >= len(expr) or not (expr[ident_start].isalpha() or expr[ident_start] == "_"):
                    break
                ident_end = ident_start + 1
                while ident_end < len(expr) and (expr[ident_end].isalnum() or expr[ident_end] == "_"):
                    ident_end += 1
                probe_after_ident = ident_end
                while probe_after_ident < len(expr) and expr[probe_after_ident].isspace():
                    probe_after_ident += 1
                if probe_after_ident < len(expr) and expr[probe_after_ident] == "(":
                    close_pos = _scan_balanced_parens(expr, probe_after_ident)
                    if close_pos is not None:
                        obj_expr = expr[i:probe].strip()
                        method_name = expr[ident_start:ident_end]
                        proc_name = _resolve_type_bound_proc_name(obj_expr, method_name, vars_map)
                        inner = expr[probe_after_ident + 1 : close_pos]
                        inner_rw = _rewrite_type_bound_calls(inner, vars_map, real_type)
                        if proc_name:
                            obj_rw = _rewrite_type_bound_calls(obj_expr, vars_map, real_type)
                            call_args = f"{obj_rw}, {inner_rw}" if inner_rw.strip() else obj_rw
                            out.append(f"{proc_name}({call_args})")
                            i = close_pos + 1
                            rewritten = True
                            break
                        obj_rw = _rewrite_type_bound_calls(obj_expr, vars_map, real_type)
                        out.append(f"{obj_rw}%{method_name}({inner_rw})")
                        i = close_pos + 1
                        rewritten = True
                        break
                last_chain_end = ident_end
                probe = ident_end
            if rewritten:
                continue
            out.append(expr[i:last_chain_end])
            i = last_chain_end
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _emit_allocatable_component_array_ctor(
    out: List[str],
    indent: int,
    comp_parent_expr: str,
    fld_name: str,
    fld_spec: str,
    ctor_items: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: set[str],
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    if (not _is_allocatable_derived_field(fld_spec)) or _derived_field_rank(fld_spec) != 1:
        return False
    base = _derived_field_base_ctype(fld_spec)
    comp_expr = f"{comp_parent_expr}.{fld_name}"
    n_ctor = len([x for x in ctor_items if x.strip()])
    out.append(' ' * indent + f'if ({comp_expr}) free({comp_expr});')
    if base == 'char *':
        out.append(' ' * indent + f'{comp_expr} = (char**) malloc(sizeof(char*) * {n_ctor});')
    else:
        out.append(' ' * indent + f'{comp_expr} = ({base}*) malloc(sizeof({base}) * {n_ctor});')
    out.append(' ' * indent + f'if (!{comp_expr} && {n_ctor} > 0) return 1;')
    out.append(' ' * indent + f'{comp_parent_expr}.__n_{fld_name} = {n_ctor};')
    for k, it in enumerate([x.strip() for x in ctor_items if x.strip()]):
        if base == 'char *':
            cv = _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            out.append(' ' * indent + f'{comp_expr}[{k}] = strdup({cv});')
        else:
            cv = _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            out.append(' ' * indent + f'{comp_expr}[{k}] = {cv};')
    return True


def _emit_list_directed_component_array(
    out: List[str],
    indent: int,
    raw_expr: str,
    vars_map: Dict[str, Var],
    real_type: str,
) -> bool:
    parts = [x.strip().lower() for x in raw_expr.split('%') if x.strip()]
    if len(parts) < 2:
        return False
    fld_spec = _derived_field_spec(parts[0], parts[1:], vars_map)
    if fld_spec is None:
        return False
    rank = _derived_field_rank(fld_spec)
    if rank <= 0:
        return False
    cexpr = raw_expr.replace('%', '.').replace(' ', '')
    parent_expr = cexpr.rsplit('.', 1)[0]
    fld_name = parts[-1]
    base = _derived_field_base_ctype(fld_spec).lower()
    if _is_allocatable_derived_field(fld_spec):
        npr = f'{parent_expr}.__n_{fld_name}' if rank == 1 else ' * '.join([f"{parent_expr}.__n_{fld_name}_{k+1}" for k in range(rank)])
    else:
        m = re.search(r'\[([^\[\]]+)\]$', fld_spec)
        if not m:
            return False
        dims = [x.strip() for x in _split_args_top_level(m.group(1)) if x.strip()]
        npr = ' * '.join(dims) if dims else '1'
    out.append(' ' * indent + '{')
    out.append(' ' * (indent + 3) + 'int __first = 1;')
    out.append(' ' * (indent + 3) + f'for (int i_pr = 0; i_pr < ({npr}); ++i_pr) {{')
    if base == 'int':
        out.append(' ' * (indent + 6) + f'printf("%s%12d", __first ? "" : " ", {cexpr}[i_pr]);')
    elif base == 'char *':
        out.append(' ' * (indent + 6) + f'printf("%s%s", __first ? "" : " ", {cexpr}[i_pr]);')
    else:
        out.append(' ' * (indent + 6) + f'if (__first) printf("%13.6f", {cexpr}[i_pr]);')
        out.append(' ' * (indent + 6) + f'else printf("    %13.6f", {cexpr}[i_pr]);')
    out.append(' ' * (indent + 6) + '__first = 0;')
    out.append(' ' * (indent + 3) + '}')
    out.append(' ' * (indent + 3) + ('printf("\\n");' if base in {'int', 'char *'} else 'printf("    \\n");'))
    out.append(' ' * indent + '}')
    return True

def _emit_basic_formatted_items_output(
    out: List[str],
    indent: int,
    fmt_text: str,
    items: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: set[str],
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    toks = _parse_basic_format_tokens(fmt_text)
    if not toks:
        return False
    repeat_group = None
    fixed_toks = []
    for tok in toks:
        if tok.get('kind') == 'repeat_group' and repeat_group is None:
            repeat_group = list(tok.get('tokens') or [])
        else:
            fixed_toks.append(tok)
    scalar_group = _extract_scalar_repeat_group_tokens(fmt_text)
    if scalar_group is not None and len(items) >= 2:
        tail_node = _parse_implied_do_item(items[-1])
        if tail_node is not None and all(_parse_implied_do_item(it) is None for it in items[:-1]):
            def emit_scalar_group(expr: str) -> None:
                cexpr = _convert_expr(expr, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                ctype = _format_item_ctype(expr, vars_map, real_type)
                for tok in scalar_group:
                    kind = tok.get('kind')
                    if kind == 'space':
                        nsp = int(tok.get('count', 1))
                        lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * indent + f'printf("%s", "{lit}");')
                    elif kind == 'newline':
                        nlb = int(tok.get('count', 1))
                        for _ in range(nlb):
                            out.append(' ' * indent + 'printf("\\n");')
                    elif kind == 'literal':
                        lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * indent + f'printf("%s", "{lit}");')
                    elif kind == 'data':
                        pf = _printf_fmt_for_basic_format_token(tok, ctype).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * indent + f'printf("{pf}", {cexpr});')
            for pit in items[:-1]:
                emit_scalar_group(pit)
            return _emit_implied_do_formatted_output(
                out,
                indent,
                fmt_text,
                items[-1],
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
    if repeat_group is not None and len(items) >= 2:
        m_row = re.match(r'^([a-z_]\w*)\s*\(\s*([^,\)]*)\s*,\s*:\s*\)$', items[-1].strip(), re.IGNORECASE)
        if m_row:
            arr = m_row.group(1).lower()
            av = vars_map.get(arr)
            if av is not None and av.is_array and len(_resolved_dim_parts(av, arr, assumed_extents)) == 2:
                dparts = _resolved_dim_parts(av, arr, assumed_extents)
                d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                row = _convert_expr((m_row.group(2) or "").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                prefix_vals = [(_convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names), _format_item_ctype(it, vars_map, real_type)) for it in items[:-1]]
                data_fixed = sum(1 for tok in fixed_toks if tok.get('kind') == 'data')
                if data_fixed == len(prefix_vals):
                    def emit_tok_prefix(tok, val_expr=None, val_ctype=None):
                        kind = tok.get('kind')
                        if kind == 'space':
                            nsp = int(tok.get('count', 1))
                            lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
                            out.append(' ' * indent + f'printf("%s", "{lit}");')
                        elif kind == 'newline':
                            nlb = int(tok.get('count', 1))
                            for _ in range(nlb):
                                out.append(' ' * indent + 'printf("\\n");')
                        elif kind == 'literal':
                            lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
                            out.append(' ' * indent + f'printf("%s", "{lit}");')
                        elif kind == 'data' and val_expr is not None:
                            pf = _printf_fmt_for_basic_format_token(tok, val_ctype or real_type).replace('\\', '\\\\').replace('"', '\\"')
                            out.append(' ' * indent + f'printf("{pf}", {val_expr});')
                    vi = 0
                    for tok in fixed_toks:
                        if tok.get('kind') == 'data':
                            emit_tok_prefix(tok, prefix_vals[vi][0], prefix_vals[vi][1])
                            vi += 1
                        else:
                            emit_tok_prefix(tok)
                    ctype = (av.ctype or real_type).lower()
                    out.append(' ' * indent + f'for (int __j_fmt = 0; __j_fmt < {d2}; ++__j_fmt) {{')
                    for tok in repeat_group:
                        kind = tok.get('kind')
                        if kind == 'space':
                            nsp = int(tok.get('count', 1))
                            lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
                            out.append(' ' * (indent + 3) + f'printf("%s", "{lit}");')
                        elif kind == 'newline':
                            nlb = int(tok.get('count', 1))
                            for _ in range(nlb):
                                out.append(' ' * (indent + 3) + 'printf("\\n");')
                        elif kind == 'literal':
                            lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
                            out.append(' ' * (indent + 3) + f'printf("%s", "{lit}");')
                        elif kind == 'data':
                            pf = _printf_fmt_for_basic_format_token(tok, ctype).replace('\\', '\\\\').replace('"', '\\"')
                            out.append(' ' * (indent + 3) + f'printf("{pf}", {arr}[(({row}) - 1) + ({d1}) * __j_fmt]);')
                    out.append(' ' * indent + '}')
                    out.append(' ' * indent + 'printf("\\n");')
                    return True
    if repeat_group is not None and len(items) == 1:
        m_row_only = re.match(r'^([a-z_]\w*)\s*\(\s*([^,\)]*)\s*,\s*:\s*\)$', items[0].strip(), re.IGNORECASE)
        m_col_only = re.match(r'^([a-z_]\w*)\s*\(\s*:\s*,\s*([^,\)]*)\s*\)$', items[0].strip(), re.IGNORECASE)
        m_sec_only = m_row_only or m_col_only
        if m_sec_only:
            arr = m_sec_only.group(1).lower()
            av = vars_map.get(arr)
            if av is not None and av.is_array and len(_resolved_dim_parts(av, arr, assumed_extents)) == 2:
                dparts = _resolved_dim_parts(av, arr, assumed_extents)
                d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                ctype = (av.ctype or real_type).lower()
                if m_row_only:
                    row = _convert_expr((m_row_only.group(2) or "").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    out.append(' ' * indent + f'for (int __j_fmt = 0; __j_fmt < {d2}; ++__j_fmt) {{')
                    val_expr = f'{arr}[(({row}) - 1) + ({d1}) * __j_fmt]'
                else:
                    col = _convert_expr((m_col_only.group(2) or "").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    out.append(' ' * indent + f'for (int __i_fmt = 0; __i_fmt < {d1}; ++__i_fmt) {{')
                    val_expr = f'{arr}[__i_fmt + ({d1}) * ((({col})) - 1)]'
                for tok in repeat_group:
                    kind = tok.get('kind')
                    if kind == 'space':
                        nsp = int(tok.get('count', 1))
                        lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * (indent + 3) + f'printf("%s", "{lit}");')
                    elif kind == 'newline':
                        nlb = int(tok.get('count', 1))
                        for _ in range(nlb):
                            out.append(' ' * (indent + 3) + 'printf("\\n");')
                    elif kind == 'literal':
                        lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * (indent + 3) + f'printf("%s", "{lit}");')
                    elif kind == 'data':
                        pf = _printf_fmt_for_basic_format_token(tok, ctype).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * (indent + 3) + f'printf("{pf}", {val_expr});')
                out.append(' ' * indent + '}')
                out.append(' ' * indent + 'printf("\\n");')
                return True
    if repeat_group is None and len(items) == 1 and any(tok.get('kind') == 'data' for tok in fixed_toks):
        m_row_only = re.match(r'^([a-z_]\w*)\s*\(\s*([^,\)]*)\s*,\s*:\s*\)$', items[0].strip(), re.IGNORECASE)
        m_col_only = re.match(r'^([a-z_]\w*)\s*\(\s*:\s*,\s*([^,\)]*)\s*\)$', items[0].strip(), re.IGNORECASE)
        m_sec_only = m_row_only or m_col_only
        if m_sec_only:
            arr = m_sec_only.group(1).lower()
            av = vars_map.get(arr)
            if av is not None and av.is_array and len(_resolved_dim_parts(av, arr, assumed_extents)) == 2:
                dparts = _resolved_dim_parts(av, arr, assumed_extents)
                d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                ctype = (av.ctype or real_type).lower()
                if m_row_only:
                    row = _convert_expr((m_row_only.group(2) or "").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    value_expr = lambda idx_var: f'{arr}[(({row}) - 1) + ({d1}) * {idx_var}]'
                    limit_expr = d2
                else:
                    col = _convert_expr((m_col_only.group(2) or "").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    value_expr = lambda idx_var: f'{arr}[{idx_var} + ({d1}) * ((({col})) - 1)]'
                    limit_expr = d1
                out.append(' ' * indent + '{')
                out.append(' ' * (indent + 3) + 'int __idx_sec = 0;')
                for tok in fixed_toks:
                    kind = tok.get('kind')
                    if kind == 'space':
                        nsp = int(tok.get('count', 1))
                        lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * (indent + 3) + f'printf("%s", "{lit}");')
                    elif kind == 'newline':
                        nlb = int(tok.get('count', 1))
                        for _ in range(nlb):
                            out.append(' ' * (indent + 3) + 'printf("\\n");')
                    elif kind == 'literal':
                        lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * (indent + 3) + f'printf("%s", "{lit}");')
                    elif kind == 'data':
                        pf = _printf_fmt_for_basic_format_token(tok, ctype).replace('\\', '\\\\').replace('"', '\\"')
                        out.append(' ' * (indent + 3) + f'if (__idx_sec < {limit_expr}) printf("{pf}", {value_expr("__idx_sec")});')
                        out.append(' ' * (indent + 3) + '__idx_sec += 1;')
                out.append(' ' * indent + '}')
                out.append(' ' * indent + 'printf("\\n");')
                return True
    vals: List[tuple[str,str]] = []
    if len(items) == 1:
        m_arr = re.match(r'^([a-z_]\w*)$', items[0], re.IGNORECASE)
        if m_arr:
            an = m_arr.group(1).lower()
            av = vars_map.get(an)
            if av is not None and av.is_array and len(_resolved_dim_parts(av, an, assumed_extents)) == 1:
                return _emit_formatted_1d_array_output(out, indent, an, av, fmt_text, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        m_ctor = re.match(r'^\[\s*(.*)\s*\]$', items[0])
        if m_ctor:
            items = [x.strip() for x in _split_args_top_level(m_ctor.group(1)) if x.strip()]
    for it in items:
        vals.append((_convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names), _format_item_ctype(it, vars_map, real_type)))
    if not vals and not any(tok.get('kind') in {'space','literal'} for tok in toks):
        return False
    def emit_tok(tok, val_expr=None, val_ctype=None):
        kind = tok.get('kind')
        if kind == 'space':
            nsp = int(tok.get('count', 1))
            lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
            out.append(' ' * indent + f'printf("%s", "{lit}");')
        elif kind == 'newline':
            nlb = int(tok.get('count', 1))
            for _ in range(nlb):
                out.append(' ' * indent + 'printf("\\n");')
        elif kind == 'literal':
            lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
            out.append(' ' * indent + f'printf("%s", "{lit}");')
        elif kind == 'data' and val_expr is not None:
            pf = _printf_fmt_for_basic_format_token(tok, val_ctype or real_type).replace('\\', '\\\\').replace('"', '\\"')
            out.append(' ' * indent + f'printf("{pf}", {val_expr});')
    data_fixed = sum(1 for tok in fixed_toks if tok.get('kind') == 'data')
    if repeat_group is not None:
        vi = 0
        for tok in fixed_toks:
            if tok.get('kind') == 'data':
                if vi >= len(vals):
                    return False
                emit_tok(tok, vals[vi][0], vals[vi][1])
                vi += 1
            else:
                emit_tok(tok)
        while vi < len(vals):
            for tok in repeat_group:
                if tok.get('kind') == 'data':
                    if vi >= len(vals):
                        break
                    emit_tok(tok, vals[vi][0], vals[vi][1])
                    vi += 1
                else:
                    emit_tok(tok)
        out.append(' ' * indent + 'printf("\\n");')
        return True
    if data_fixed <= 0:
        for tok in fixed_toks:
            emit_tok(tok)
        out.append(' ' * indent + 'printf("\\n");')
        return True
    if data_fixed == 1 and len(vals) > 1:
        vi = 0
        while vi < len(vals):
            for tok in fixed_toks:
                if tok.get('kind') == 'data':
                    emit_tok(tok, vals[vi][0], vals[vi][1])
                    vi += 1
                else:
                    emit_tok(tok)
            out.append(' ' * indent + 'printf("\\n");')
        return True
    vi = 0
    while vi < len(vals):
        for tok in fixed_toks:
            if tok.get('kind') == 'data':
                if vi >= len(vals):
                    break
                emit_tok(tok, vals[vi][0], vals[vi][1])
                vi += 1
            else:
                emit_tok(tok)
        out.append(' ' * indent + 'printf("\\n");')
    return True



def _parse_implied_do_item(text: str):
    t = text.strip()
    if not (t.startswith('(') and t.endswith(')')):
        return None
    inner = t[1:-1].strip()
    parts = [p.strip() for p in _split_args_top_level(inner) if p.strip()]
    if len(parts) < 3:
        return None
    m_step = re.match(r'^([a-z_]\w*)\s*=\s*(.+)$', parts[-3], re.IGNORECASE) if len(parts) >= 4 else None
    if m_step and ('=' not in parts[-2]) and ('=' not in parts[-1]):
        var = m_step.group(1).lower()
        lo = m_step.group(2).strip()
        hi = parts[-2].strip()
        step = parts[-1].strip()
        body_parts = parts[:-3]
    else:
        m = re.match(r'^([a-z_]\w*)\s*=\s*(.+)$', parts[-2], re.IGNORECASE)
        if not m or ('=' in parts[-1]):
            return None
        var = m.group(1).lower()
        lo = m.group(2).strip()
        hi = parts[-1].strip()
        step = None
        body_parts = parts[:-2]
    if not body_parts:
        return None
    body = []
    for bp in body_parts:
        sub = _parse_implied_do_item(bp)
        body.append(sub if sub is not None else bp)
    return {"kind": "implied_do", "var": var, "lo": lo, "hi": hi, "step": step, "body": body}


def _extract_scalar_repeat_group_tokens(fmt_text: str):
    toks = _parse_basic_format_tokens(fmt_text)
    if not toks:
        return None
    if len(toks) == 1 and toks[0].get('kind') == 'repeat_group':
        group = list(toks[0].get('tokens') or [])
    else:
        group = list(toks)
    if sum(1 for tok in group if tok.get('kind') == 'data') != 1:
        return None
    return group


def _emit_implied_do_formatted_output(
    out: List[str],
    indent: int,
    fmt_text: str,
    item_text: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: set[str],
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    node = _parse_implied_do_item(item_text)
    group = _extract_scalar_repeat_group_tokens(fmt_text)
    if node is None or group is None:
        return False

    def emit_scalar(expr: str, ind: int) -> None:
        cexpr = _convert_expr(expr, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        ctype = _format_item_ctype(expr, vars_map, real_type)
        for tok in group:
            kind = tok.get('kind')
            if kind == 'space':
                nsp = int(tok.get('count', 1))
                lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
                out.append(' ' * ind + f'printf("%s", "{lit}");')
            elif kind == 'newline':
                nlb = int(tok.get('count', 1))
                for _ in range(nlb):
                    out.append(' ' * ind + 'printf("\\n");')
            elif kind == 'literal':
                lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
                out.append(' ' * ind + f'printf("%s", "{lit}");')
            elif kind == 'data':
                pf = _printf_fmt_for_basic_format_token(tok, ctype).replace('\\', '\\\\').replace('"', '\\"')
                out.append(' ' * ind + f'printf("{pf}", {cexpr});')

    def emit_node(n, ind: int) -> None:
        if isinstance(n, str):
            emit_scalar(n, ind)
            return
        var = str(n['var'])
        clo = _convert_expr(str(n['lo']), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        chi = _convert_expr(str(n['hi']), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        step = n.get('step')
        if step is None:
            out.append(' ' * ind + f'for ({var} = {clo}; {var} <= {chi}; ++{var}) {{')
            inner_ind = ind + 3
            for child in n['body']:
                emit_node(child, inner_ind)
            out.append(' ' * ind + '}')
        else:
            cstep = _convert_expr(str(step), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            out.append(' ' * ind + '{')
            out.append(' ' * (ind + 3) + f'int __step_{var} = {cstep};')
            out.append(' ' * (ind + 3) + f'for ({var} = {clo}; (__step_{var} >= 0) ? ({var} <= {chi}) : ({var} >= {chi}); {var} += __step_{var}) {{')
            for child in n['body']:
                emit_node(child, ind + 6)
            out.append(' ' * (ind + 3) + '}')
            out.append(' ' * ind + '}')

    out.append(' ' * indent + '{')
    emit_node(node, indent + 3)
    out.append(' ' * (indent + 3) + 'printf("\\n");')
    out.append(' ' * indent + '}')
    return True


def _emit_list_directed_ctor_output(
    out: List[str],
    indent: int,
    expr_text: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: set[str],
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    ctor_items = _array_constructor_items(expr_text)
    if ctor_items is None:
        if _parse_implied_do_item(expr_text) is None:
            return False
        ctor_items = [expr_text.strip()]

    tmp: List[str] = []

    def emit_scalar(item_text: str, ind: int) -> bool:
        nested_items = _array_constructor_items(item_text)
        if nested_items is not None:
            for sub_item in nested_items:
                if not emit_item(sub_item, ind):
                    return False
            return True
        m_reduce = re.match(r"^\s*(all|any|count)\s*\((.*)\)\s*$", item_text, re.IGNORECASE)
        if m_reduce:
            op = m_reduce.group(1).lower()
            rargs = [x.strip() for x in _split_args_top_level(m_reduce.group(2)) if x.strip()]
            if rargs:
                arg_expr = rargs[0]
                bare_arrays = [
                    name
                    for name in sorted({t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(arg_expr), flags=re.IGNORECASE)})
                    if name in vars_map
                    and vars_map[name].is_array
                    and not re.search(rf"\b{re.escape(name)}\s*\(", arg_expr, flags=re.IGNORECASE)
                ]
                if len(bare_arrays) == 1:
                    an = bare_arrays[0]
                    av = vars_map.get(an)
                    if av is not None and len(_resolved_dim_parts(av, an, assumed_extents)) == 1:
                        if av.is_allocatable or av.is_pointer:
                            npr = _dim_product_from_parts(
                                _resolved_dim_parts(av, an, assumed_extents),
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                            )
                        else:
                            npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                        ridx = f"__red_i_{len(tmp)}"
                        expr_i = re.sub(rf"\b{re.escape(an)}\b", f"{an}[{ridx}]", arg_expr, flags=re.IGNORECASE)
                        cexpr_i = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        if op == "count":
                            tmp_name = f"__count_{len(tmp)}"
                            tmp.append(' ' * ind + f"int {tmp_name} = 0;")
                            tmp.append(' ' * ind + f"for (int {ridx} = 0; {ridx} < {npr}; ++{ridx}) if ({cexpr_i}) ++{tmp_name};")
                            _emit_list_directed_scalar_printf(
                                tmp,
                                ind,
                                tmp_name,
                                "int",
                                vars_map,
                                real_type,
                                prefix_expr='__first ? "" : " "',
                                newline=False,
                            )
                        else:
                            tmp_name = f"__{op}_{len(tmp)}"
                            tmp.append(' ' * ind + f"int {tmp_name} = 0;")
                            if op == "all":
                                tmp[-1] = ' ' * ind + f"int {tmp_name} = 1;"
                                tmp.append(' ' * ind + f"for (int {ridx} = 0; {ridx} < {npr}; ++{ridx}) if (!({cexpr_i})) {tmp_name} = 0;")
                            else:
                                tmp.append(' ' * ind + f"for (int {ridx} = 0; {ridx} < {npr}; ++{ridx}) if ({cexpr_i}) {tmp_name} = 1;")
                            _emit_list_directed_scalar_printf(
                                tmp,
                                ind,
                                tmp_name,
                                "logical",
                                vars_map,
                                real_type,
                                prefix_expr='__first ? "" : " "',
                                newline=False,
                            )
                        tmp.append(' ' * ind + "__first = 0;")
                        return True
        if re.fullmatch(r"[a-z_]\w*", item_text.strip(), re.IGNORECASE):
            vv = vars_map.get(item_text.strip().lower())
            if vv is not None and vv.is_array:
                return False
        cexpr = _convert_expr(item_text, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        ctype = _format_item_ctype(item_text, vars_map, real_type)
        _emit_list_directed_scalar_printf(
            tmp,
            ind,
            cexpr,
            ctype,
            vars_map,
            real_type,
            prefix_expr='__first ? "" : " "',
            newline=False,
        )
        tmp.append(' ' * ind + "__first = 0;")
        return True

    def emit_node(node, ind: int) -> bool:
        if isinstance(node, str):
            return emit_scalar(node, ind)
        var = str(node["var"])
        clo = _convert_expr(str(node["lo"]), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        chi = _convert_expr(str(node["hi"]), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        step = node.get("step")
        if step is None:
            tmp.append(' ' * ind + f'for ({var} = {clo}; {var} <= {chi}; ++{var}) {{')
            for child in node["body"]:
                if not emit_node(child, ind + 3):
                    return False
            tmp.append(' ' * ind + '}')
            return True
        cstep = _convert_expr(str(step), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        tmp.append(' ' * ind + '{')
        tmp.append(' ' * (ind + 3) + f'int __step_{var} = {cstep};')
        tmp.append(' ' * (ind + 3) + f'for ({var} = {clo}; (__step_{var} >= 0) ? ({var} <= {chi}) : ({var} >= {chi}); {var} += __step_{var}) {{')
        for child in node["body"]:
            if not emit_node(child, ind + 6):
                return False
        tmp.append(' ' * (ind + 3) + '}')
        tmp.append(' ' * ind + '}')
        return True

    def emit_item(item_text: str, ind: int) -> bool:
        node = _parse_implied_do_item(item_text)
        if node is not None:
            return emit_node(node, ind)
        return emit_scalar(item_text, ind)

    for ctor_item in ctor_items:
        if not emit_item(ctor_item, indent + 3):
            return False

    out.append(' ' * indent + '{')
    out.append(' ' * (indent + 3) + 'int __first = 1;')
    out.extend(tmp)
    out.append(' ' * (indent + 3) + 'printf("\\n");')
    out.append(' ' * indent + '}')
    return True


def _replace_pow(expr: str) -> str:
    # Conservative repeated replacement for simple operands.
    var = r"[a-z_]\w*(?:\[[^\[\]]+\])*"
    num = r"[0-9]+(?:\.[0-9]*)?(?:[eEdD][+\-]?\d+)?"
    par = r"\([^()]+\)"
    pat_int = re.compile(
        rf"({var}|{par}|{num})\s*\*\*\s*([0-9]+)",
        re.IGNORECASE,
    )
    pat = re.compile(
        rf"({var}|{par}|{num})\s*\*\*\s*({var}|{par}|{num})",
        re.IGNORECASE,
    )

    def _int_pow_repl(m: re.Match[str]) -> str:
        base = m.group(1)
        try:
            expo = int(m.group(2))
        except Exception:
            return m.group(0)
        if expo == 0:
            return "1"
        if expo == 1:
            return f"({base})"
        if 2 <= expo <= 8:
            return "(" + " * ".join([f"({base})"] * expo) + ")"
        return f"pow({base}, {expo})"

    prev = None
    out = expr
    while out != prev:
        prev = out
        out = pat_int.sub(_int_pow_repl, out)
        out = pat.sub(r"pow(\1, \2)", out)
        i = 0
        rebuilt: List[str] = []
        changed_bal = False
        while i < len(out):
            if out[i] != "*" or i + 1 >= len(out) or out[i + 1] != "*":
                rebuilt.append(out[i])
                i += 1
                continue
            j = i + 2
            while j < len(out) and out[j].isspace():
                j += 1
            k = j
            while k < len(out) and out[k].isdigit():
                k += 1
            if k == j:
                rebuilt.append(out[i])
                i += 1
                continue
            expo = int(out[j:k])
            b = i - 1
            while b >= 0 and out[b].isspace():
                b -= 1
            if b < 0 or out[b] != ")":
                rebuilt.append(out[i])
                i += 1
                continue
            depth = 1
            a = b - 1
            while a >= 0:
                if out[a] == ")":
                    depth += 1
                elif out[a] == "(":
                    depth -= 1
                    if depth == 0:
                        break
                a -= 1
            if a < 0:
                rebuilt.append(out[i])
                i += 1
                continue
            base = out[a : b + 1]
            prefix = out[:a]
            if expo == 0:
                repl = "1"
            elif expo == 1:
                repl = base
            elif 2 <= expo <= 8:
                repl = "(" + " * ".join([base] * expo) + ")"
            else:
                repl = f"pow{base, expo}"
                repl = f"pow({base}, {expo})"
            out = prefix + repl + out[k:]
            changed_bal = True
            break
        if changed_bal:
            continue
    return out

def _split_args_top_level(text: str) -> List[str]:
    out: List[str] = []
    cur: List[str] = []
    depth = 0
    bdepth = 0
    in_single = False
    in_double = False
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "'" and not in_double:
            in_single = not in_single
            cur.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            cur.append(ch)
            i += 1
            continue
        if not in_single and not in_double:
            if ch == "(":
                depth += 1
            elif ch == ")" and depth > 0:
                depth -= 1
            elif ch == "[":
                bdepth += 1
            elif ch == "]" and bdepth > 0:
                bdepth -= 1
            elif ch == "," and depth == 0 and bdepth == 0:
                out.append("".join(cur).strip())
                cur = []
                i += 1
                continue
        cur.append(ch)
        i += 1
    tail = "".join(cur).strip()
    if tail:
        out.append(tail)
    return out


def _split_decl_entity(ent: str) -> tuple[str, Optional[str], Optional[str]]:
    text = ent.strip()
    if "=>" in text:
        lhs, rhs = text.split("=>", 1)
        return lhs.strip(), None, rhs.strip()
    if "=" in text:
        lhs, rhs = text.split("=", 1)
        return lhs.strip(), rhs.strip(), None
    return text, None, None


def _split_concat_top_level(text: str) -> List[str]:
    out: List[str] = []
    cur: List[str] = []
    depth = 0
    bdepth = 0
    in_single = False
    in_double = False
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "'" and not in_double:
            if in_single and i + 1 < len(text) and text[i + 1] == "'":
                cur.append(ch)
                cur.append(text[i + 1])
                i += 2
                continue
            in_single = not in_single
            cur.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            if in_double and i + 1 < len(text) and text[i + 1] == '"':
                cur.append(ch)
                cur.append(text[i + 1])
                i += 2
                continue
            in_double = not in_double
            cur.append(ch)
            i += 1
            continue
        if not in_single and not in_double:
            if ch == "(":
                depth += 1
            elif ch == ")" and depth > 0:
                depth -= 1
            elif ch == "[":
                bdepth += 1
            elif ch == "]" and bdepth > 0:
                bdepth -= 1
            elif ch == "/" and i + 1 < len(text) and text[i + 1] == "/" and depth == 0 and bdepth == 0:
                part = "".join(cur).strip()
                if part:
                    out.append(part)
                cur = []
                i += 2
                continue
        cur.append(ch)
        i += 1
    tail = "".join(cur).strip()
    if tail:
        out.append(tail)
    return out


def _emit_string_concat_expr(
    out: List[str],
    indent: int,
    expr_raw: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
    newline_each: bool = False,
    list_directed_strings: bool = False,
) -> bool:
    parts = _split_concat_top_level(expr_raw)
    if len(parts) <= 1:
        return False
    byref_scalars = byref_scalars or set()
    assumed_extents = assumed_extents or {}
    proc_arg_extent_names = proc_arg_extent_names or {}

    kind_parts: List[tuple[str, object]] = []
    ctor_lengths: List[int] = []
    array_lengths: List[str] = []

    for part in parts:
        p = part.strip()
        ctor_items = _array_constructor_items(p)
        if ctor_items is not None:
            if any(_format_item_ctype(it, vars_map, real_type) != 'string' for it in ctor_items):
                return False
            kind_parts.append(('ctor', ctor_items))
            ctor_lengths.append(len(ctor_items))
            continue
        m_arr = re.fullmatch(r'([a-z_]\w*)', p, re.IGNORECASE)
        if m_arr:
            an = m_arr.group(1).lower()
            av = vars_map.get(an)
            if av is not None and av.is_array and (av.ctype or '').lower() == 'char *':
                dparts = _resolved_dim_parts(av, an, assumed_extents)
                if len(dparts) != 1:
                    return False
                kind_parts.append(('array', an))
                array_lengths.append(_dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents))
                continue
        if _format_item_ctype(p, vars_map, real_type) != 'string':
            return False
        kind_parts.append(('scalar', p))

    npr_expr: Optional[str] = None
    if ctor_lengths:
        if any(n != ctor_lengths[0] for n in ctor_lengths):
            return False
        npr_expr = str(ctor_lengths[0])
    if array_lengths:
        arr_len = array_lengths[0]
        if any(n != arr_len for n in array_lengths):
            return False
        if npr_expr is None:
            npr_expr = arr_len
        elif any(re.fullmatch(r'[0-9]+', n) and n != npr_expr for n in array_lengths):
            return False

    ctor_decls: List[str] = []
    append_exprs_scalar: List[str] = []
    append_exprs_loop: List[str] = []
    ctor_idx = 0
    for kind, payload in kind_parts:
        if kind == 'ctor':
            items = payload
            cname = f'__ctor_{ctor_idx}'
            ctor_idx += 1
            cinit = ', '.join(_convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for it in items)
            ctor_decls.append(f'char * {cname}[] = {{{cinit}}};')
            append_exprs_loop.append(f'{cname}[i_pr]')
        elif kind == 'array':
            append_exprs_loop.append(f'{payload}[i_pr]')
        else:
            cexpr = _convert_expr(str(payload), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            append_exprs_scalar.append(cexpr)
            append_exprs_loop.append(cexpr)

    if npr_expr is None:
        out.append(' ' * indent + '{')
        out.append(' ' * (indent + 3) + 'char __buf[4096];')
        out.append(' ' * (indent + 3) + "__buf[0] = '\\0';")
        for expr in append_exprs_scalar:
            out.append(' ' * (indent + 3) + f'strncat(__buf, {expr}, sizeof(__buf) - strlen(__buf) - 1);')
        if list_directed_strings or newline_each:
            out.append(' ' * (indent + 3) + 'printf("%s\\n", __buf);')
        else:
            out.append(' ' * (indent + 3) + 'printf("%s", __buf);')
        out.append(' ' * indent + '}')
        return True

    out.append(' ' * indent + '{')
    for decl in ctor_decls:
        out.append(' ' * (indent + 3) + decl)
    if list_directed_strings:
        out.append(' ' * (indent + 3) + 'int __first = 1;')
    out.append(' ' * (indent + 3) + f'for (int i_pr = 0; i_pr < {npr_expr}; ++i_pr) {{')
    out.append(' ' * (indent + 6) + 'char __buf[4096];')
    out.append(' ' * (indent + 6) + "__buf[0] = '\\0';")
    for expr in append_exprs_loop:
        out.append(' ' * (indent + 6) + f'strncat(__buf, {expr}, sizeof(__buf) - strlen(__buf) - 1);')
    if list_directed_strings:
        out.append(' ' * (indent + 6) + 'printf("%s%s", __first ? "" : " ", __buf);')
        out.append(' ' * (indent + 6) + '__first = 0;')
    elif newline_each:
        out.append(' ' * (indent + 6) + 'printf("%s\\n", __buf);')
    else:
        out.append(' ' * (indent + 6) + 'printf("%s", __buf);')
    out.append(' ' * (indent + 3) + '}')
    if list_directed_strings:
        out.append(' ' * (indent + 3) + 'printf("\n");')
    out.append(' ' * indent + '}')
    return True


def _split_colon_top_level(text: str) -> List[str]:
    out: List[str] = []
    cur: List[str] = []
    depth = 0
    bdepth = 0
    in_single = False
    in_double = False
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "'" and not in_double:
            if in_single and i + 1 < len(text) and text[i + 1] == "'":
                cur.append(ch)
                cur.append(ch)
                i += 2
                continue
            in_single = not in_single
            cur.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            cur.append(ch)
            i += 1
            continue
        if not in_single and not in_double:
            if ch == "(":
                depth += 1
            elif ch == ")" and depth > 0:
                depth -= 1
            elif ch == "[":
                bdepth += 1
            elif ch == "]" and bdepth > 0:
                bdepth -= 1
            elif ch == ":" and depth == 0 and bdepth == 0:
                out.append("".join(cur).strip())
                cur = []
                i += 1
                continue
        cur.append(ch)
        i += 1
    out.append("".join(cur).strip())
    return out


def _parse_simple_forall_specs(text: str) -> Optional[tuple[List[tuple[str, str, str]], str]]:
    specs: List[tuple[str, str, str]] = []
    masks: List[str] = []
    for raw_spec in _split_args_top_level(text):
        spec = raw_spec.strip()
        if not spec:
            continue
        m = re.match(r"^([a-z_]\w*)\s*=\s*(.+)$", spec, re.IGNORECASE)
        if not m:
            masks.append(spec)
            continue
        name = m.group(1).lower()
        parts = [p.strip() for p in _split_colon_top_level(m.group(2).strip())]
        if len(parts) not in {2, 3} or not parts[1]:
            return None
        lo = parts[0] or "1"
        hi = parts[1]
        step = parts[2] if len(parts) == 3 and parts[2] else ""
        specs.append((name, lo, hi if not step else f"{hi}, {step}"))
    if not specs:
        return None
    mask_expr = " .and. ".join(masks)
    return specs, mask_expr


def _rewrite_simple_forall(text: str) -> tuple[str, List[int]]:
    def _split_forall_header(line: str) -> Optional[tuple[str, str, str]]:
        m = re.match(r"^(\s*)forall\s*\(", line, re.IGNORECASE)
        if not m:
            return None
        indent = m.group(1)
        i = m.end() - 1
        depth = 0
        in_single = False
        in_double = False
        start = i + 1
        j = start
        while j < len(line):
            ch = line[j]
            if ch == "'" and not in_double:
                in_single = not in_single
            elif ch == '"' and not in_single:
                in_double = not in_double
            elif not in_single and not in_double:
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    if depth == 0:
                        return indent, line[start:j], line[j + 1 :].strip()
                    depth -= 1
            j += 1
        return None

    lines = text.splitlines()
    out: List[str] = []
    line_map: List[int] = []
    i = 0
    while i < len(lines):
        raw = lines[i]
        orig_line_no = i + 1
        code = _strip_comment(raw).strip()
        forall_parts = _split_forall_header(raw)
        if forall_parts and forall_parts[2]:
            indent, spec_text, body = forall_parts
            parsed = _parse_simple_forall_specs(spec_text)
            if parsed and "=" in body:
                specs, mask_expr = parsed
                for name, lo, hi_step in specs:
                    out.append(f"{indent}do {name}={lo},{hi_step}")
                    line_map.append(orig_line_no)
                if mask_expr:
                    out.append(f"{indent}   if ({mask_expr}) then")
                    line_map.append(orig_line_no)
                    out.append(f"{indent}      {body}")
                    line_map.append(orig_line_no)
                    out.append(f"{indent}   end if")
                    line_map.append(orig_line_no)
                else:
                    out.append(f"{indent}   {body}")
                    line_map.append(orig_line_no)
                for _ in reversed(specs):
                    out.append(f"{indent}end do")
                    line_map.append(orig_line_no)
                i += 1
                continue
        if forall_parts and not forall_parts[2]:
            indent, spec_text, _tail = forall_parts
            parsed = _parse_simple_forall_specs(spec_text)
            if parsed:
                specs, mask_expr = parsed
                body_lines: List[str] = []
                j = i + 1
                while j < len(lines):
                    end_code = _strip_comment(lines[j]).strip().lower()
                    if re.match(r"^end\s+forall\s*$", end_code, re.IGNORECASE):
                        break
                    body_lines.append(lines[j])
                    j += 1
                if j < len(lines) and body_lines:
                    for name, lo, hi_step in specs:
                        out.append(f"{indent}do {name}={lo},{hi_step}")
                        line_map.append(orig_line_no)
                    if mask_expr:
                        out.append(f"{indent}   if ({mask_expr}) then")
                        line_map.append(orig_line_no)
                        out.extend(body_lines)
                        line_map.extend(range(i + 2, j + 1))
                        out.append(f"{indent}   end if")
                        line_map.append(orig_line_no)
                    else:
                        out.extend(body_lines)
                        line_map.extend(range(i + 2, j + 1))
                    for _ in reversed(specs):
                        out.append(f"{indent}end do")
                        line_map.append(j + 1)
                    i = j + 1
                    continue
        out.append(raw)
        line_map.append(orig_line_no)
        i += 1
    return "\n".join(out) + ("\n" if text.endswith("\n") else ""), line_map


def _remap_rewritten_line_numbers(messages: List[str], line_map: List[int]) -> List[str]:
    if not line_map:
        return messages

    def map_line(n: int) -> int:
        if 1 <= n <= len(line_map):
            return line_map[n - 1]
        return n

    remapped: List[str] = []
    for msg in messages:
        msg2 = re.sub(
            r"\bline\s+([0-9]+):",
            lambda m: f"line {map_line(int(m.group(1)))}:",
            msg,
        )
        msg2 = re.sub(
            r"(:)([0-9]+)\b",
            lambda m: f"{m.group(1)}{map_line(int(m.group(2)))}",
            msg2,
            count=1,
        )
        remapped.append(msg2)
    return remapped


def _rewrite_inline_if_write(text: str) -> tuple[str, List[int]]:
    lines = text.splitlines()
    out: List[str] = []
    line_map: List[int] = []
    for i, raw in enumerate(lines, start=1):
        m = re.match(r"^(\s*)if\s*\((.*)\)\s*write\s*(\(.+\)\s*.*)$", raw, re.IGNORECASE)
        if m:
            indent = m.group(1)
            cond = m.group(2).strip()
            write_tail = m.group(3).strip()
            out.append(f"{indent}if ({cond}) then")
            line_map.append(i)
            out.append(f"{indent}   write {write_tail}")
            line_map.append(i)
            out.append(f"{indent}end if")
            line_map.append(i)
            continue
        out.append(raw)
        line_map.append(i)
    return "\n".join(out) + ("\n" if text.endswith("\n") else ""), line_map


def _compose_line_maps(prev_map: List[int], next_map: List[int]) -> List[int]:
    if not prev_map:
        return next_map
    out: List[int] = []
    for n in next_map:
        if 1 <= n <= len(prev_map):
            out.append(prev_map[n - 1])
        else:
            out.append(n)
    return out


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
    # Typed zero-size constructors such as [real ::], [integer ::], [type(t) ::]
    if "::" in inner:
        lhs, rhs = inner.split("::", 1)
        if rhs.strip() == "":
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


def _convert_array_initializer(init: str, vars_map: Dict[str, Var], real_type: str) -> str:
    items = _array_constructor_items(init)
    if items is None:
        return _convert_expr(init, vars_map, real_type)
    if len(items) == 0:
        return "{0}"
    citems = [_convert_expr(it, vars_map, real_type) for it in items]
    return "{" + ", ".join(citems) + "}"


def _is_assumed_shape(dim: Optional[str]) -> bool:
    return any(_dim_part_is_assumed_shape(p) for p in _dim_parts(dim))


def _dim_part_is_assumed_shape(part: str) -> bool:
    p = part.strip()
    if p == ":":
        return True
    if ":" not in p:
        return False
    sp = _split_colon_top_level(p)
    hi = (sp[1] if len(sp) >= 2 else "").strip()
    return hi == ""


def _dim_lb_expr(
    part: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
) -> str:
    p = part.strip()
    if p == ":":
        return "1"
    if ":" not in p:
        return "1"
    sp = _split_colon_top_level(p)
    lo = (sp[0] if len(sp) >= 1 else "").strip() or "1"
    return _convert_expr(lo, vars_map, real_type, byref_scalars, assumed_extents)


def _dim_extent_expr(
    part: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
) -> str:
    p = part.strip()
    if p == ":":
        return "1"
    if ":" not in p:
        return _convert_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
    sp = _split_colon_top_level(p)
    lo = (sp[0] if len(sp) >= 1 else "").strip() or "1"
    hi = (sp[1] if len(sp) >= 2 else "").strip() or lo
    clo = _convert_expr(lo, vars_map, real_type, byref_scalars, assumed_extents)
    chi = _convert_expr(hi, vars_map, real_type, byref_scalars, assumed_extents)
    return f"(({chi}) - ({clo}) + 1)"


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


def _dim_product_expr(
    dim: Optional[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
) -> str:
    parts = _dim_parts(dim)
    if not parts:
        return "1"
    conv = [f"({_dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents)})" for p in parts]
    if len(conv) == 1:
        return conv[0][1:-1]
    return "(" + " * ".join(conv) + ")"


def _dim_product_from_parts(
    parts: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
) -> str:
    if not parts:
        return "1"
    conv = [f"({_dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents)})" for p in parts]
    if len(conv) == 1:
        return conv[0][1:-1]
    return "(" + " * ".join(conv) + ")"


def _section_count_expr(lo: str, hi: str, st: str) -> str:
    return f"(((({st}) > 0) ? ((({hi}) - ({lo})) / ({st}) + 1) : ((({lo}) - ({hi})) / (-({st})) + 1)))"


def _section_shape_exprs(
    expr: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
) -> Optional[List[str]]:
    m_sec = _match_whole_name_call(expr.strip())
    if not m_sec:
        return None
    arr = m_sec[0].lower()
    v = vars_map.get(arr)
    if v is None or not v.is_array:
        return None
    idx_parts = _split_args_top_level(m_sec[1])
    dparts = _resolved_dim_parts(v, arr, assumed_extents)
    if len(idx_parts) != len(dparts):
        return None
    out: List[str] = []
    for idx_txt, base_part in zip(idx_parts, dparts):
        idx_txt = idx_txt.strip()
        if ":" not in idx_txt:
            continue
        sp = _split_colon_top_level(idx_txt)
        base_lo = _dim_lb_expr(base_part, vars_map, real_type, byref_scalars, assumed_extents)
        base_ext = _dim_extent_expr(base_part, vars_map, real_type, byref_scalars, assumed_extents)
        base_hi = f"(({base_lo}) + ({base_ext}) - 1)"
        lo_raw = (sp[0] if len(sp) >= 1 else "").strip()
        hi_raw = (sp[1] if len(sp) >= 2 else "").strip()
        st_raw = (sp[2] if len(sp) >= 3 else "").strip()
        lo = _convert_expr(lo_raw or base_lo, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        hi = _convert_expr(hi_raw or base_hi, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        st = _convert_expr(st_raw or "1", vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        out.append(_section_count_expr(lo, hi, st))
    return out


def _shape_like_intrinsic_values(
    nm: str,
    args: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
) -> Optional[List[str]]:
    if not args:
        return None
    arg0 = args[0].strip()
    sec_shape = _section_shape_exprs(
        arg0,
        vars_map,
        real_type,
        byref_scalars,
        assumed_extents,
        proc_arg_extent_names,
    )
    vals: Optional[List[str]] = None
    if sec_shape is not None:
        rank = max(1, len(sec_shape))
        if nm == "rank":
            vals = [str(rank)]
        elif nm == "size":
            vals = sec_shape
        elif nm == "shape":
            vals = sec_shape
        elif nm == "lbound":
            vals = ["1"] * rank
        elif nm == "ubound":
            vals = sec_shape
    else:
        a0 = arg0.lower()
        av0 = vars_map.get(a0)
        if av0 is None or not av0.is_array:
            return None
        dparts0 = _resolved_dim_parts(av0, a0, assumed_extents)
        if nm == "rank":
            vals = [str(max(1, len(dparts0)))]
        elif nm == "size":
            vals = [_dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts0]
        elif nm == "shape":
            vals = [_dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts0]
        elif nm == "lbound":
            vals = [_dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts0]
        elif nm == "ubound":
            vals = []
            for p in dparts0:
                lo0 = _dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                ex0 = _dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                vals.append(f"(({lo0}) + ({ex0}) - 1)")
    if vals is None:
        return None
    if len(args) >= 2:
        dim_raw = args[1]
        m_dim_kw = re.match(r"^\s*dim\s*=\s*(.+?)\s*$", dim_raw, re.IGNORECASE)
        if m_dim_kw:
            dim_raw = m_dim_kw.group(1).strip()
        dim_expr = _convert_expr(dim_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        dim_int = _eval_int_expr(dim_expr)
        if dim_int is not None and 1 <= dim_int <= len(vals):
            return [vals[dim_int - 1]]
        return [f"(" + " : ".join([f"(({dim_expr}) == {k+1}) ? ({vals[k]})" for k in range(len(vals))]) + " : 0)"]
    if nm == "size" and len(vals) > 1:
        return ["(" + " * ".join(f"({v})" for v in vals) + ")"]
    return vals


def _minmax_section_scalar_expr(
    kind: str,
    arg: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
) -> Optional[str]:
    m_sec = _match_whole_name_call(arg.strip())
    if not m_sec:
        return None
    arr = m_sec[0].lower()
    v = vars_map.get(arr)
    if v is None or not v.is_array:
        return None
    idx_parts = _split_args_top_level(m_sec[1])
    dparts = _resolved_dim_parts(v, arr, assumed_extents)
    if len(idx_parts) != len(dparts):
        return None
    if not any(":" in idx for idx in idx_parts):
        return None
    cty = (v.ctype or real_type).lower()
    if cty == "double":
        init = "DBL_MAX" if kind == "minval" else "(-DBL_MAX)"
    elif cty == "int":
        init = "INT_MAX" if kind == "minval" else "INT_MIN"
    else:
        init = "FLT_MAX" if kind == "minval" else "(-FLT_MAX)"
    acc = "__red_sec"
    out_lines: List[str] = []
    out_lines.append(f"({{ {cty} {acc} = {init};")
    loop_vars: List[str] = []
    for k, (idx_txt, base_part) in enumerate(zip(idx_parts, dparts), start=1):
        idx_txt = idx_txt.strip()
        if ":" in idx_txt:
            sp = _split_colon_top_level(idx_txt)
            base_lo = _dim_lb_expr(base_part, vars_map, real_type, byref_scalars, assumed_extents)
            base_ext = _dim_extent_expr(base_part, vars_map, real_type, byref_scalars, assumed_extents)
            base_hi = f"(({base_lo}) + ({base_ext}) - 1)"
            lo = _convert_expr((sp[0] if len(sp) >= 1 else "").strip() or base_lo, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            hi = _convert_expr((sp[1] if len(sp) >= 2 else "").strip() or base_hi, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            st = _convert_expr((sp[2] if len(sp) >= 3 else "").strip() or "1", vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            vnm = f"__is{k}"
            loop_vars.append(vnm)
            out_lines.append(f" for (int {vnm} = {lo}; ({st}) > 0 ? {vnm} <= {hi} : {vnm} >= {hi}; {vnm} += {st}) {{")
        else:
            loop_vars.append(_convert_expr(idx_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names))
    lin = _fortran_sub_to_linear(loop_vars, dparts, vars_map, real_type, byref_scalars, assumed_extents)
    cmp = "<" if kind == "minval" else ">"
    out_lines.append(f" if ({arr}[{lin}] {cmp} {acc}) {acc} = {arr}[{lin}];")
    for _ in range(sum(1 for idx in idx_parts if ":" in idx)):
        out_lines.append(" }")
    out_lines.append(f" {acc}; }})")
    return "".join(out_lines)


def _emit_list_directed_loc_intrinsic(
    out: List[str],
    indent: int,
    items: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
) -> bool:
    if not items:
        return False
    m_loc = re.match(r"^(minloc|maxloc|findloc)\s*\((.*)\)\s*$", items[-1].strip(), re.IGNORECASE)
    if not m_loc:
        return False
    prefix_items = items[:-1]
    for pit in prefix_items:
        m_simple = re.match(r"^([a-z_]\w*)$", pit.strip(), re.IGNORECASE)
        if m_simple:
            vv = vars_map.get(m_simple.group(1).lower())
            if vv is not None and vv.is_array:
                return False
    nm = m_loc.group(1).lower()
    args = [x.strip() for x in _split_args_top_level(m_loc.group(2)) if x.strip()]
    if nm in {"minloc", "maxloc"}:
        if len(args) < 1:
            return False
        arr_arg = args[0]
        val_arg = None
        extras = args[1:]
    else:
        if len(args) < 2:
            return False
        arr_arg = args[0]
        val_arg = args[1]
        extras = args[2:]
    if not re.fullmatch(r"[a-z_]\w*", arr_arg, re.IGNORECASE):
        return False
    arr = arr_arg.lower()
    av = vars_map.get(arr)
    if av is None or not av.is_array:
        return False
    dparts = _resolved_dim_parts(av, arr, assumed_extents)
    rank = len(dparts)
    if rank not in {1, 2}:
        return False
    dim_no: Optional[int] = None
    back_expr = "0"
    for extra in extras:
        m_dim_kw = re.match(r"(?i)^dim\s*=\s*([0-9]+)$", extra)
        if m_dim_kw:
            dim_no = int(m_dim_kw.group(1))
            break
        if re.fullmatch(r"[0-9]+", extra):
            dim_no = int(extra)
            break
    for extra in extras:
        m_back_kw = re.match(r"(?i)^back\s*=\s*(.+)$", extra)
        if m_back_kw:
            back_expr = _convert_expr(
                m_back_kw.group(1).strip(),
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            break
    cty = (av.ctype or real_type).lower()
    if cty not in {"int", "float", "double"}:
        return False
    d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
    d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if rank >= 2 else None
    n_total = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
    val_c = _convert_expr(val_arg, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if val_arg is not None else None
    init_expr = f"{arr}[0]"
    cmp_expr = "<" if nm == "minloc" else ">"

    out.append(" " * indent + "{")
    out.append(" " * (indent + 3) + "int __first = 1;")
    for pit in prefix_items:
        cty_pre = _format_item_ctype(pit, vars_map, real_type)
        cexpr_pre = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        _emit_list_directed_scalar_printf(
            out,
            indent + 3,
            cexpr_pre,
            cty_pre,
            vars_map,
            real_type,
            prefix_expr='__first ? "" : " "',
            newline=False,
        )
        out.append(" " * (indent + 3) + "__first = 0;")

    if dim_no is None:
        out.append(" " * (indent + 3) + "int __loc = 0;")
        if nm == "findloc":
            out.append(" " * (indent + 3) + "int __found = 0;")
            out.append(" " * (indent + 3) + f"if ({back_expr}) {{")
            out.append(" " * (indent + 6) + f"for (int i_pr = ({n_total}) - 1; i_pr >= 0; --i_pr) {{")
            out.append(" " * (indent + 9) + f"if ({arr}[i_pr] == {val_c}) {{ __loc = i_pr; __found = 1; break; }}")
            out.append(" " * (indent + 6) + "}")
            out.append(" " * (indent + 3) + "} else {")
            out.append(" " * (indent + 6) + f"for (int i_pr = 0; i_pr < ({n_total}); ++i_pr) {{")
            out.append(" " * (indent + 9) + f"if ({arr}[i_pr] == {val_c}) {{ __loc = i_pr; __found = 1; break; }}")
            out.append(" " * (indent + 6) + "}")
            out.append(" " * (indent + 3) + "}")
        else:
            out.append(" " * (indent + 3) + f"{cty} __best = {init_expr};")
            out.append(" " * (indent + 3) + f"for (int i_pr = 1; i_pr < ({n_total}); ++i_pr) {{")
            out.append(" " * (indent + 6) + f"if ({arr}[i_pr] {cmp_expr} __best || (({back_expr}) && ({arr}[i_pr] == __best))) {{ __best = {arr}[i_pr]; __loc = i_pr; }}")
            out.append(" " * (indent + 3) + "}")
        if rank == 1:
            comp = "(__found ? (__loc + 1) : 0)" if nm == "findloc" else "(__loc + 1)"
            _emit_list_directed_scalar_printf(out, indent + 3, comp, "int", vars_map, real_type, prefix_expr='__first ? "" : " "', newline=False)
        else:
            comp1 = f"((__loc % ({d1})) + 1)"
            comp2 = f"((__loc / ({d1})) + 1)"
            if nm == "findloc":
                comp1 = f"(__found ? {comp1} : 0)"
                comp2 = f"(__found ? {comp2} : 0)"
            _emit_list_directed_scalar_printf(out, indent + 3, comp1, "int", vars_map, real_type, prefix_expr='__first ? "" : " "', newline=False)
            out.append(" " * (indent + 3) + "__first = 0;")
            _emit_list_directed_scalar_printf(out, indent + 3, comp2, "int", vars_map, real_type, prefix_expr='__first ? "" : " "', newline=False)
    else:
        if rank != 2 or dim_no not in {1, 2}:
            return False
        out_len = d2 if dim_no == 1 else d1
        outer_name = "j_pr" if dim_no == 1 else "i_pr"
        out.append(" " * (indent + 3) + f"for (int {outer_name} = 0; {outer_name} < ({out_len}); ++{outer_name}) {{")
        out.append(" " * (indent + 6) + "int __locv = 0;")
        if nm == "findloc":
            out.append(" " * (indent + 6) + "int __found = 0;")
            if dim_no == 1:
                out.append(" " * (indent + 6) + f"if ({back_expr}) {{")
                out.append(" " * (indent + 9) + f"for (int i_pr = ({d1}) - 1; i_pr >= 0; --i_pr) {{")
                out.append(" " * (indent + 12) + f"if ({arr}[i_pr + ({d1}) * {outer_name}] == {val_c}) {{ __locv = i_pr + 1; __found = 1; break; }}")
                out.append(" " * (indent + 9) + "}")
                out.append(" " * (indent + 6) + "} else {")
                out.append(" " * (indent + 9) + f"for (int i_pr = 0; i_pr < ({d1}); ++i_pr) {{")
                out.append(" " * (indent + 12) + f"if ({arr}[i_pr + ({d1}) * {outer_name}] == {val_c}) {{ __locv = i_pr + 1; __found = 1; break; }}")
                out.append(" " * (indent + 9) + "}")
                out.append(" " * (indent + 6) + "}")
            else:
                out.append(" " * (indent + 6) + f"if ({back_expr}) {{")
                out.append(" " * (indent + 9) + f"for (int j_pr = ({d2}) - 1; j_pr >= 0; --j_pr) {{")
                out.append(" " * (indent + 12) + f"if ({arr}[{outer_name} + ({d1}) * j_pr] == {val_c}) {{ __locv = j_pr + 1; __found = 1; break; }}")
                out.append(" " * (indent + 9) + "}")
                out.append(" " * (indent + 6) + "} else {")
                out.append(" " * (indent + 9) + f"for (int j_pr = 0; j_pr < ({d2}); ++j_pr) {{")
                out.append(" " * (indent + 12) + f"if ({arr}[{outer_name} + ({d1}) * j_pr] == {val_c}) {{ __locv = j_pr + 1; __found = 1; break; }}")
                out.append(" " * (indent + 9) + "}")
                out.append(" " * (indent + 6) + "}")
        else:
            if dim_no == 1:
                out.append(" " * (indent + 6) + f"{cty} __best = {arr}[({d1}) * {outer_name}];")
                out.append(" " * (indent + 6) + f"for (int i_pr = 1; i_pr < ({d1}); ++i_pr) {{")
                out.append(" " * (indent + 9) + f"if ({arr}[i_pr + ({d1}) * {outer_name}] {cmp_expr} __best || (({back_expr}) && ({arr}[i_pr + ({d1}) * {outer_name}] == __best))) {{ __best = {arr}[i_pr + ({d1}) * {outer_name}]; __locv = i_pr; }}")
            else:
                out.append(" " * (indent + 6) + f"{cty} __best = {arr}[{outer_name}];")
                out.append(" " * (indent + 6) + f"for (int j_pr = 1; j_pr < ({d2}); ++j_pr) {{")
                out.append(" " * (indent + 9) + f"if ({arr}[{outer_name} + ({d1}) * j_pr] {cmp_expr} __best || (({back_expr}) && ({arr}[{outer_name} + ({d1}) * j_pr] == __best))) {{ __best = {arr}[{outer_name} + ({d1}) * j_pr]; __locv = j_pr; }}")
            out.append(" " * (indent + 6) + "}")
            out.append(" " * (indent + 6) + "__locv += 1;")
        _emit_list_directed_scalar_printf(out, indent + 6, "__locv", "int", vars_map, real_type, prefix_expr='__first ? "" : " "', newline=False)
        out.append(" " * (indent + 6) + "__first = 0;")
        out.append(" " * (indent + 3) + "}")

    out.append(" " * (indent + 3) + 'printf("\\n");')
    out.append(" " * indent + "}")
    return True


def _fortran_sub_to_linear(
    idx_parts: List[str],
    dim_parts: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
) -> str:
    """Map Fortran subscripts (1-based, column-major) to 0-based linear C index."""
    if len(idx_parts) != len(dim_parts) or not idx_parts:
        return "0"
    lb0 = _dim_lb_expr(dim_parts[0], vars_map, real_type, byref_scalars, assumed_extents)
    idx0 = f"({_convert_expr(idx_parts[0], vars_map, real_type, byref_scalars, assumed_extents)} - ({lb0}))"
    stride = _dim_extent_expr(dim_parts[0], vars_map, real_type, byref_scalars, assumed_extents)
    expr = idx0
    for k in range(1, len(idx_parts)):
        lbk = _dim_lb_expr(dim_parts[k], vars_map, real_type, byref_scalars, assumed_extents)
        ik = f"({_convert_expr(idx_parts[k], vars_map, real_type, byref_scalars, assumed_extents)} - ({lbk}))"
        expr = f"({expr} + ({stride}) * {ik})"
        if k < len(dim_parts) - 1:
            dk = _dim_extent_expr(dim_parts[k], vars_map, real_type, byref_scalars, assumed_extents)
            stride = f"(({stride}) * ({dk}))"
    return expr


def _resolved_dim_parts(
    v: Var,
    var_name: str,
    assumed_extents: Optional[Dict[str, List[str]]],
) -> List[str]:
    dparts = _dim_parts(v.dim)
    if not dparts:
        return []
    if assumed_extents and var_name.lower() in assumed_extents:
        exts = assumed_extents[var_name.lower()]
        out: List[str] = []
        ei = 0
        for d in dparts:
            if _dim_part_is_assumed_shape(d):
                ext = exts[ei] if ei < len(exts) else "1"
                if d.strip() == ":":
                    out.append(ext)
                else:
                    lo = (_split_colon_top_level(d)[0] if _split_colon_top_level(d) else "").strip() or "1"
                    out.append(f"{lo}:(({lo}) + ({ext}) - 1)")
                ei += 1
            else:
                out.append(d)
        return out
    if (v.is_allocatable or v.is_pointer) and any(_dim_part_is_assumed_shape(d) for d in dparts):
        exts = _alloc_extent_names(var_name, len(dparts))
        out: List[str] = []
        ei = 0
        for d in dparts:
            if _dim_part_is_assumed_shape(d):
                ext = exts[ei] if ei < len(exts) else "1"
                if d.strip() == ":":
                    out.append(ext)
                else:
                    lo = (_split_colon_top_level(d)[0] if _split_colon_top_level(d) else "").strip() or "1"
                    out.append(f"{lo}:(({lo}) + ({ext}) - 1)")
                ei += 1
            else:
                out.append(d)
        return out
    return dparts


def _alloc_len_name(name: str) -> str:
    return f"__n_{name.lower()}"


def _alloc_extent_names(name: str, rank: int) -> List[str]:
    if rank <= 1:
        return [_alloc_len_name(name)]
    base = name.lower()
    return [f"__n_{base}_{k+1}" for k in range(rank)]


def _result_extent_names(name: str, rank: int) -> List[str]:
    if rank <= 1:
        return [f"__ret_{name.lower()}_n"]
    base = name.lower()
    return [f"__ret_{base}_n_{k+1}" for k in range(rank)]


def _is_dynamic_array_result(v: Var) -> bool:
    return bool(v.is_array and (v.is_allocatable or v.is_pointer or _is_assumed_shape(v.dim)))


def _result_length_expr(
    func_name: str,
    rv: Var,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
) -> str:
    rank = max(1, len(_dim_parts(rv.dim)))
    if _is_dynamic_array_result(rv):
        exts = _result_extent_names(func_name, rank)
        return " * ".join(f"({en})" for en in exts)
    return _dim_product_expr(rv.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)


def _unit_is_elemental(unit: Dict[str, object]) -> bool:
    header_ln = int(unit.get("header_line_no", 0) or 0)
    source_lines: List[str] = list(unit.get("source_lines", []))
    if header_ln and 1 <= header_ln <= len(source_lines):
        code = _strip_comment(source_lines[header_ln - 1]).strip().lower()
        return "elemental" in code.split()
    return False


def _scan_balanced_parens(text: str, open_pos: int) -> Optional[int]:
    if open_pos < 0 or open_pos >= len(text) or text[open_pos] != "(":
        return None
    depth = 0
    in_single = False
    in_double = False
    i = open_pos
    while i < len(text):
        ch = text[i]
        if ch == "'" and not in_double:
            if in_single and i + 1 < len(text) and text[i + 1] == "'":
                i += 2
                continue
            in_single = not in_single
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            i += 1
            continue
        if not in_single and not in_double:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    return i
        i += 1
    return None


def _match_whole_name_call(text: str) -> Optional[tuple[str, str]]:
    m = re.match(r"^\s*([a-z_]\w*)\s*\(", text, re.IGNORECASE)
    if not m:
        return None
    open_pos = text.find("(", m.start(1) + len(m.group(1)))
    if open_pos < 0:
        return None
    close_pos = _scan_balanced_parens(text, open_pos)
    if close_pos is None or text[close_pos + 1 :].strip():
        return None
    return m.group(1), text[open_pos + 1 : close_pos]


def _rewrite_named_calls(expr: str, rewriter) -> str:
    out: List[str] = []
    i = 0
    in_single = False
    in_double = False
    while i < len(expr):
        ch = expr[i]
        if ch == "'" and not in_double:
            if in_single and i + 1 < len(expr) and expr[i + 1] == "'":
                out.append("''")
                i += 2
                continue
            in_single = not in_single
            out.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            i += 1
            continue
        if in_single or in_double:
            out.append(ch)
            i += 1
            continue
        if ch.isalpha() or ch == "_":
            j = i + 1
            while j < len(expr) and (expr[j].isalnum() or expr[j] == "_"):
                j += 1
            name = expr[i:j]
            k = j
            while k < len(expr) and expr[k].isspace():
                k += 1
            if k < len(expr) and expr[k] == "(":
                close_pos = _scan_balanced_parens(expr, k)
                if close_pos is not None:
                    inner = expr[k + 1 : close_pos]
                    repl = rewriter(name, inner)
                    if repl is not None:
                        out.append(repl)
                        i = close_pos + 1
                        continue
                    inner_rewritten = _rewrite_named_calls(inner, rewriter)
                    out.append(f"{name}({inner_rewritten})")
                    i = close_pos + 1
                    continue
            out.append(expr[i:j])
            i = j
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _extract_rank_reducing_sum(expr: str) -> Optional[tuple[str, str, int, str]]:
    placeholder = "__XF2C_SUM_DIM__"
    found: List[tuple[str, int]] = []

    def _rw(name: str, inner: str) -> Optional[str]:
        if name.lower() != "sum":
            return None
        args = [x.strip() for x in _split_args_top_level(inner) if x.strip()]
        if len(args) < 2:
            return None
        dim_no: Optional[int] = None
        for extra in args[1:]:
            m_dim_kw = re.match(r"(?i)^dim\s*=\s*([0-9]+)$", extra)
            if m_dim_kw:
                dim_no = int(m_dim_kw.group(1))
                break
            if re.fullmatch(r"[0-9]+", extra):
                dim_no = int(extra)
                break
        if dim_no is None:
            return None
        found.append((args[0], dim_no))
        return placeholder

    rewritten = _rewrite_named_calls(expr, _rw)
    if len(found) != 1 or placeholder not in rewritten:
        return None
    pre, post = rewritten.split(placeholder, 1)
    return pre, found[0][0], found[0][1], post


def _extract_scalar_sum(expr: str) -> Optional[tuple[str, str, str]]:
    placeholder = "__XF2C_SUM__"
    found: List[str] = []

    def _rw(name: str, inner: str) -> Optional[str]:
        if name.lower() != "sum":
            return None
        args = [x.strip() for x in _split_args_top_level(inner) if x.strip()]
        if len(args) != 1:
            return None
        found.append(args[0])
        return placeholder

    rewritten = _rewrite_named_calls(expr, _rw)
    if len(found) != 1 or placeholder not in rewritten:
        return None
    pre, post = rewritten.split(placeholder, 1)
    return pre, found[0], post


def _rewrite_rank1_reduction_term(
    expr: str,
    idx_name: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]],
    assumed_extents: Optional[Dict[str, List[str]]],
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]],
) -> Optional[tuple[str, str, str]]:
    expr_rw = expr
    base_extent: Optional[str] = None
    base_ctype: Optional[str] = None

    sec_pat = re.compile(r"\b([a-z_]\w*)\s*\(\s*:\s*,\s*([^,()]+)\s*\)", re.IGNORECASE)

    def _sec_repl(m: re.Match[str]) -> str:
        nonlocal base_extent, base_ctype
        nm = m.group(1).lower()
        vv = vars_map.get(nm)
        if vv is None or (not vv.is_array):
            return m.group(0)
        dps = _resolved_dim_parts(vv, nm, assumed_extents)
        if len(dps) != 2:
            return m.group(0)
        extent = dps[0]
        extent_key = _simplify_int_expr_text(extent).replace(" ", "").lower()
        if base_extent is not None:
            base_key = _simplify_int_expr_text(base_extent).replace(" ", "").lower()
            if extent_key != base_key:
                return m.group(0)
        else:
            base_extent = extent
            base_ctype = vv.ctype or real_type
        col = _convert_expr(
            m.group(2).strip(),
            vars_map,
            real_type,
            byref_scalars,
            assumed_extents,
            proc_arg_extent_names,
        )
        return f"{nm}[({idx_name}) + ({extent}) * ((({col})) - 1)]"

    expr_rw = sec_pat.sub(_sec_repl, expr_rw)

    rank1_names = [
        name
        for name, vv in vars_map.items()
        if vv.is_array
        and len(_resolved_dim_parts(vv, name, assumed_extents)) == 1
        and re.search(rf"\b{re.escape(name)}\b(?!\s*\()", expr_rw, re.IGNORECASE)
    ]
    if not rank1_names and base_extent is None:
        return None
    if rank1_names:
        base_name = rank1_names[0]
        base_var = vars_map[base_name]
        if base_extent is None:
            base_extent = _resolved_dim_parts(base_var, base_name, assumed_extents)[0]
            base_ctype = base_var.ctype or real_type
        base_extent_key = _simplify_int_expr_text(base_extent).replace(" ", "").lower()
        for name in rank1_names:
            vv = vars_map[name]
            extent = _resolved_dim_parts(vv, name, assumed_extents)[0]
            extent_key = _simplify_int_expr_text(extent).replace(" ", "").lower()
            if extent_key != base_extent_key:
                return None
    for name in sorted(rank1_names, key=len, reverse=True):
        expr_rw = re.sub(
            rf"\b{re.escape(name)}\b(?!\s*\()",
            f"{name}[{idx_name}]",
            expr_rw,
            flags=re.IGNORECASE,
        )
    elem_c = _convert_expr(
        expr_rw,
        vars_map,
        real_type,
        byref_scalars,
        assumed_extents,
        proc_arg_extent_names,
    )
    return elem_c, base_extent or "1", base_ctype or real_type


def _rewrite_rank2_reduction_term(
    expr: str,
    red_dim: int,
    outer_idx: str,
    inner_idx: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]],
    assumed_extents: Optional[Dict[str, List[str]]],
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]],
) -> Optional[str]:
    rank2_names = [
        name for name, vv in vars_map.items()
        if vv.is_array and len(_resolved_dim_parts(vv, name, assumed_extents)) == 2
    ]
    if not rank2_names:
        return None
    base_name = None
    for name in sorted(rank2_names, key=len, reverse=True):
        if re.search(rf"\b{re.escape(name)}\b", expr, re.IGNORECASE):
            base_name = name
            break
    if base_name is None:
        return None
    base_parts = _resolved_dim_parts(vars_map[base_name], base_name, assumed_extents)
    d1 = _convert_expr(base_parts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
    row_idx = inner_idx if red_dim == 1 else outer_idx
    col_idx = outer_idx if red_dim == 1 else inner_idx

    def _spread_rw(name: str, inner: str) -> Optional[str]:
        if name.lower() != "spread":
            return None
        args = [x.strip() for x in _split_args_top_level(inner) if x.strip()]
        if not args:
            return None
        src_nm = args[0].lower()
        src_v = vars_map.get(src_nm)
        if src_v is None or (not src_v.is_array) or len(_resolved_dim_parts(src_v, src_nm, assumed_extents)) != 1:
            return None
        dim_no = None
        for extra in args[1:]:
            m_dim_kw = re.match(r"(?i)^dim\s*=\s*([0-9]+)$", extra)
            if m_dim_kw:
                dim_no = int(m_dim_kw.group(1))
                break
            if re.fullmatch(r"[0-9]+", extra):
                dim_no = int(extra)
                break
        if dim_no == 1:
            return f"{src_nm}[{col_idx}]"
        if dim_no == 2:
            return f"{src_nm}[{row_idx}]"
        return None

    expr_rw = _rewrite_named_calls(expr, _spread_rw)
    for an in sorted(rank2_names, key=len, reverse=True):
        expr_rw = re.sub(
            rf"\b{re.escape(an)}\b(?!\s*\()",
            f"{an}[({row_idx}) + ({d1}) * ({col_idx})]",
            expr_rw,
            flags=re.IGNORECASE,
        )
    return expr_rw


def _rewrite_assumed_shape_calls(
    expr: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]],
    assumed_extents: Optional[Dict[str, List[str]]],
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]],
) -> str:
    if not proc_arg_extent_names:
        return expr
    out: List[str] = []
    i = 0
    n = len(expr)
    while i < n:
        ch = expr[i]
        if not (ch.isalpha() or ch == "_"):
            out.append(ch)
            i += 1
            continue
        j = i + 1
        while j < n and (expr[j].isalnum() or expr[j] == "_"):
            j += 1
        name = expr[i:j]
        k = j
        while k < n and expr[k].isspace():
            k += 1
        if k >= n or expr[k] != "(":
            out.append(name)
            i = j
            continue
        depth = 0
        p = k
        while p < n:
            c = expr[p]
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    break
            p += 1
        if p >= n:
            out.append(name)
            i = j
            continue
        inner = expr[k + 1 : p]
        callee = name.lower()
        ex_lists = proc_arg_extent_names.get(callee, [])
        if not any(ex_lists):
            out.append(expr[i : p + 1])
            i = p + 1
            continue
        raw_args = _split_args_top_level(inner) if inner.strip() else []
        new_args: List[str] = []
        for ai, a in enumerate(raw_args):
            exts = ex_lists[ai] if ai < len(ex_lists) else []
            extent_args, carg = _expand_assumed_shape_actual_arg(
                a,
                exts,
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            new_args.extend(extent_args)
            new_args.append(carg)
        out.append(f"{name}({', '.join(new_args)})")
        i = p + 1
    return "".join(out)


def _expand_assumed_shape_actual_arg(
    a: str,
    exts: List[str],
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]],
    assumed_extents: Optional[Dict[str, List[str]]],
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]],
) -> tuple[List[str], str]:
    a_strip = a.strip()
    extent_args: List[str] = []
    if exts:
        ctor_items = _array_constructor_items(a_strip)
        if ctor_items is not None and len(exts) == 1:
            extent_args.append(str(len(ctor_items)))
            return extent_args, _convert_expr(a_strip, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        m_id = re.match(r"^\s*([a-z_]\w*)\s*$", a_strip, re.IGNORECASE)
        if m_id:
            nm = m_id.group(1).lower()
            vv = vars_map.get(nm)
            if vv is not None and vv.is_array:
                dps = _resolved_dim_parts(vv, nm, assumed_extents)
                if len(dps) >= len(exts):
                    for d in dps[: len(exts)]:
                        extent_args.append(_dim_extent_expr(d, vars_map, real_type, byref_scalars, assumed_extents))
                else:
                    extent_args.extend(["1"] * len(exts))
                return extent_args, a_strip
        m_col = re.match(r"^\s*([a-z_]\w*)\s*\(\s*:\s*,\s*([^,()]+)\s*\)\s*$", a_strip, re.IGNORECASE)
        if m_col and len(exts) == 1:
            nm = m_col.group(1).lower()
            vv = vars_map.get(nm)
            if vv is not None and vv.is_array:
                dps = _resolved_dim_parts(vv, nm, assumed_extents)
                if len(dps) == 2:
                    d1 = _convert_expr(dps[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    col = _convert_expr(m_col.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    extent_args.append(d1)
                    return extent_args, f"&{nm}[({d1}) * ((({col})) - 1)]"
        m_plane = re.match(
            r"^\s*([a-z_]\w*)\s*\(\s*:\s*,\s*:\s*,\s*([^,()]+)\s*\)\s*$",
            a_strip,
            re.IGNORECASE,
        )
        if m_plane and len(exts) == 2:
            nm = m_plane.group(1).lower()
            vv = vars_map.get(nm)
            if vv is not None and vv.is_array:
                dps = _resolved_dim_parts(vv, nm, assumed_extents)
                if len(dps) == 3:
                    d1 = _convert_expr(dps[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    d2 = _convert_expr(dps[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    plane = _convert_expr(m_plane.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    extent_args.extend([d1, d2])
                    return extent_args, f"&{nm}[({d1}) * ({d2}) * ((({plane})) - 1)]"
        m_sec1 = re.match(
            r"^\s*([a-z_]\w*)\s*\(\s*([^:,\)]*)\s*:\s*([^:,\)]*)(?:\s*:\s*([^)]+))?\s*\)\s*$",
            a_strip,
            re.IGNORECASE,
        )
        if m_sec1 and len(exts) == 1:
            nm = m_sec1.group(1).lower()
            vv = vars_map.get(nm)
            if vv is not None and vv.is_array:
                dps = _resolved_dim_parts(vv, nm, assumed_extents)
                if len(dps) == 1:
                    lo_raw = (m_sec1.group(2) or "").strip() or "1"
                    hi_raw = (m_sec1.group(3) or "").strip() or dps[0]
                    st_raw = (m_sec1.group(4) or "").strip() or "1"
                    st_key = _simplify_int_expr_text(st_raw).replace(" ", "")
                    if st_key == "1":
                        lo = _convert_expr(lo_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        hi = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        extent_args.append(f"(({hi}) - ({lo}) + 1)")
                        return extent_args, f"&{nm}[({lo}) - 1]"
        extent_args.extend(["1"] * len(exts))
    return extent_args, _convert_expr(a_strip, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)


def _replace_single_quoted_literals_outside_double(text: str) -> str:
    out = []
    i = 0
    in_double = False
    while i < len(text):
        ch = text[i]
        if ch == '"':
            out.append(ch)
            if in_double and i + 1 < len(text) and text[i + 1] == '"':
                out.append(text[i + 1])
                i += 2
                continue
            in_double = not in_double
            i += 1
            continue
        if ch == "'" and not in_double:
            j = i + 1
            buf = []
            while j < len(text):
                if text[j] == "'":
                    if j + 1 < len(text) and text[j + 1] == "'":
                        buf.append("'")
                        j += 2
                        continue
                    break
                buf.append(text[j])
                j += 1
            if j < len(text) and text[j] == "'":
                out.append('"' + ''.join(buf).replace('\\', '\\\\').replace('"', '\\"') + '"')
                i = j + 1
                continue
        out.append(ch)
        i += 1
    return ''.join(out)


def _find_top_level_binary_operator(expr: str, ops: List[str]) -> Optional[tuple[int, str]]:
    depth = 0
    in_single = False
    in_double = False
    last: Optional[tuple[int, str]] = None
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch == "'" and not in_double:
            if in_single and i + 1 < len(expr) and expr[i + 1] == "'":
                i += 2
                continue
            in_single = not in_single
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            i += 1
            continue
        if in_single or in_double:
            i += 1
            continue
        if ch in "([":
            depth += 1
            i += 1
            continue
        if ch in ")]":
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            matched = None
            for op in sorted(ops, key=len, reverse=True):
                if expr.startswith(op, i):
                    matched = op
                    break
            if matched is not None:
                if matched in {"+", "-"}:
                    j = i - 1
                    while j >= 0 and expr[j].isspace():
                        j -= 1
                    prev = expr[j] if j >= 0 else ""
                    if j < 0 or prev in "(,+-*/<>=:":
                        i += len(matched)
                        continue
                    if prev in "eEdD":
                        k = j - 1
                        while k >= 0 and expr[k].isspace():
                            k -= 1
                        if k >= 0 and (expr[k].isdigit() or expr[k] == "."):
                            i += len(matched)
                            continue
                last = (i, matched)
                i += len(matched)
                continue
        i += 1
    return last


def _rewrite_overloaded_operator_expr(
    expr: str,
    vars_map: Dict[str, Var],
    real_type: str,
) -> str:
    s = expr.strip()
    inner = _drop_redundant_outer_parens(s)
    if inner != s:
        rewritten_inner = _rewrite_overloaded_operator_expr(inner, vars_map, real_type)
        if rewritten_inner != inner:
            return f"({rewritten_inner})"
        s = inner
    for op in ["||", ".or.", "&&", ".and."]:
        hit = _find_top_level_binary_operator(s, [op])
        if hit is None:
            continue
        pos, matched = hit
        lhs = s[:pos].strip()
        rhs = s[pos + len(matched):].strip()
        if not lhs or not rhs:
            continue
        lhs_r = _rewrite_overloaded_operator_expr(lhs, vars_map, real_type)
        rhs_r = _rewrite_overloaded_operator_expr(rhs, vars_map, real_type)
        return f"{lhs_r} {matched} {rhs_r}"
    for op in ["!", ".not."]:
        if s.lower().startswith(op.lower()):
            rhs = s[len(op):].strip()
            if rhs:
                rhs_r = _rewrite_overloaded_operator_expr(rhs, vars_map, real_type)
                return f"{op}{rhs_r}" if op == "!" else f"{op} {rhs_r}"
    for ops in (["==", "/=", "<=", ">=", "<", ">"], ["+", "-"]):
        hit = _find_top_level_binary_operator(s, ops)
        if hit is None:
            continue
        pos, op = hit
        lhs = s[:pos].strip()
        rhs = s[pos + len(op):].strip()
        if not lhs or not rhs:
            continue
        lhs_r = _rewrite_overloaded_operator_expr(lhs, vars_map, real_type)
        rhs_r = _rewrite_overloaded_operator_expr(rhs, vars_map, real_type)
        resolved = _resolve_operator_proc_name(op, lhs_r, rhs_r, vars_map, real_type)
        if resolved:
            return f"{resolved}({lhs_r}, {rhs_r})"
        return f"{lhs_r} {op} {rhs_r}"
    return s


def _convert_expr(
    expr: str,
    vars_map: Dict[str, Var],
    real_type: str,
    byref_scalars: Optional[set[str]] = None,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
    proc_arg_extent_names: Optional[Dict[str, List[List[str]]]] = None,
) -> str:
    out = expr.strip()
    # Convert Fortran single-quoted strings to C double-quoted strings,
    # but leave apostrophes inside double-quoted literals untouched.
    out = _replace_single_quoted_literals_outside_double(out)
    out = _rewrite_type_bound_calls(out, vars_map, real_type)
    if _is_fortran_string_literal(out) and ("//" not in out):
        return out
    complex_lit = _parse_complex_literal(out)
    if complex_lit is not None:
        re_part = _convert_expr(complex_lit[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        im_part = _convert_expr(complex_lit[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        cty = _complex_ctype(real_type)
        return f"(({cty}) (({re_part}) + ({im_part}) * I))"
    out = re.sub(r"(?i)\bnew_line\s*\(\s*[^)]*\)", lambda _m: '"\\n"', out)
    concat_parts = _split_concat_top_level(out)
    if len(concat_parts) > 1:
        cparts: List[str] = []
        for part in concat_parts:
            if _format_item_ctype(part.strip(), vars_map, real_type) != "string":
                cparts = []
                break
            cparts.append(_convert_expr(part.strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names))
        if cparts:
            acc = cparts[0]
            for cp in cparts[1:]:
                acc = f"concat_s2({acc}, {cp})"
            return acc

    def _rewrite_generic_call(name: str, inner: str) -> Optional[str]:
        args = [x.strip() for x in _split_args_top_level(inner) if x.strip()]
        resolved = _resolve_generic_proc_name(name, args, vars_map, real_type)
        if resolved != name.lower():
            return f"{resolved}({inner})"
        return None

    out = _rewrite_named_calls(out, _rewrite_generic_call)
    out = _rewrite_overloaded_operator_expr(out, vars_map, real_type)
    ctor_items = _array_constructor_items(out)
    if ctor_items is not None:
        cty = _array_constructor_ctype(ctor_items, vars_map, real_type)
        cbase = "char *" if cty == "string" else cty
        cinit = ", ".join(
            _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            for it in ctor_items
        )
        return f"(({cbase}[]){{{cinit}}})"
    out = re.sub(
        r"(?i)\b([a-z_]\w*)\s*%\s*re\b",
        lambda m: _complex_real_expr(m.group(1), real_type) if _is_complex_ctype(vars_map.get(m.group(1).lower()).ctype if vars_map.get(m.group(1).lower()) else None) else m.group(0),
        out,
    )
    out = re.sub(
        r"(?i)\b([a-z_]\w*)\s*%\s*im\b",
        lambda m: _complex_imag_expr(m.group(1), real_type) if _is_complex_ctype(vars_map.get(m.group(1).lower()).ctype if vars_map.get(m.group(1).lower()) else None) else m.group(0),
        out,
    )
    # Remove kind suffixes only from numeric literals, not identifiers.
    out = re.sub(
        r"(?i)\b(([0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[ed][+\-]?[0-9]+)?)_(?:dp|sp)\b",
        r"\1",
        out,
    )
    out = re.sub(
        r"(?i)\b(([0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[ed][+\-]?[0-9]+)?)_(?:int8|int16|int32|int64|real32|real64|real128)\b",
        r"\1",
        out,
    )
    out = re.sub(
        r"(?i)\b(([0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[ed][+\-]?[0-9]+)?)_(?:[a-z_]\w*|\d+)\b",
        r"\1",
        out,
    )
    out = re.sub(r"(?i)\bkind\s*\(\s*[^)]*[d][+\-]?\d+\s*\)", "8", out)
    out = re.sub(r"(?i)\bkind\s*\(\s*1(?:\.0*)?(?:[e][+\-]?0)?\s*\)", "4", out)
    out = re.sub(r"([0-9])d([+\-]?[0-9]+)", r"\1e\2", out, flags=re.IGNORECASE)
    out = re.sub(
        r"(?i)\breal\s*\(\s*([^,]+)\s*,\s*kind\s*=\s*(?:dp|sp)\s*\)",
        rf"(({real_type}) (\1))",
        out,
    )
    out = re.sub(r"(?i)\bint8\b", "1", out)
    out = re.sub(r"(?i)\bint16\b", "2", out)
    out = re.sub(r"(?i)\bint32\b", "4", out)
    out = re.sub(r"(?i)\bint64\b", "8", out)
    out = re.sub(r"(?i)\breal32\b", "4", out)
    out = re.sub(r"(?i)\breal64\b", "8", out)
    out = re.sub(r"(?i)\breal128\b", "16", out)
    out = re.sub(r"(?i)\.and\.", "&&", out)
    out = re.sub(r"(?i)\.or\.", "||", out)
    out = re.sub(r"(?i)\.not\.", "!", out)
    out = re.sub(r"(?i)\.eqv\.", "==", out)
    out = re.sub(r"(?i)\.neqv\.", "!=", out)
    out = re.sub(r"(?i)\.eq\.", "==", out)
    out = re.sub(r"(?i)\.ne\.", "!=", out)
    out = re.sub(r"(?i)\.lt\.", "<", out)
    out = re.sub(r"(?i)\.le\.", "<=", out)
    out = re.sub(r"(?i)\.gt\.", ">", out)
    out = re.sub(r"(?i)\.ge\.", ">=", out)
    out = re.sub(r"(?<![<>=!])/=", "!=", out)
    out = re.sub(r"(?i)\.true\.", "1", out)
    out = re.sub(r"(?i)\.false\.", "0", out)
    out = re.sub(r"(?i)\bpresent\s*\(\s*([a-z_]\w*)\s*\)", r"(\1 != NULL)", out)

    def _rewrite_derived_ctor(name: str, inner: str) -> Optional[str]:
        nm = name.lower()
        fields = _ACTIVE_DERIVED_TYPES.get(nm)
        if not fields:
            return None
        args = [x.strip() for x in _split_args_top_level(inner) if x.strip()]
        cargs = [_convert_expr(a, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for a in args]
        return f"({nm}){{{', '.join(cargs)}}}"

    out = _rewrite_named_calls(out, _rewrite_derived_ctor)
    m_sub_arr = re.match(r'^([a-z_]\w*)\s*\((.+)\)\s*\((.+):(.*)\)$', out, re.IGNORECASE)
    if m_sub_arr:
        nm = m_sub_arr.group(1).lower()
        vv = vars_map.get(nm)
        if vv is not None and (vv.ctype or '').lower() == 'char *' and vv.is_array:
            idx = _convert_expr(m_sub_arr.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            lo = _convert_expr(m_sub_arr.group(3).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            hi_raw = m_sub_arr.group(4).strip()
            if hi_raw:
                hi = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            elif vv.char_len:
                hi = _simplify_int_expr_text(vv.char_len)
            else:
                hi = f"((int) strlen({nm}[(({idx}) - 1)]))"
            return f"substr_s({nm}[(({idx}) - 1)], {lo}, {hi})"
    m_sub = re.match(r'^([a-z_]\w*)\s*\((.+):(.*)\)$', out, re.IGNORECASE)
    if m_sub:
        nm = m_sub.group(1).lower()
        vv = vars_map.get(nm)
        if vv is not None and (vv.ctype or '').lower() == 'char *' and not vv.is_array:
            lo = _convert_expr(m_sub.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            hi_raw = m_sub.group(3).strip()
            if hi_raw:
                hi = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            elif vv.char_len:
                hi = _simplify_int_expr_text(vv.char_len)
            else:
                hi = f"((int) strlen({nm}))"
            return f"substr_s({nm}, {lo}, {hi})"
    for nm, vv in sorted(vars_map.items(), key=lambda kv: len(kv[0]), reverse=True):
        if (vv.ctype or "").lower() != "char *" or vv.is_array:
            continue
        pat_sub_any = re.compile(rf"(?<!['\"])\b{re.escape(nm)}\s*\(\s*([^()]*?)\s*:\s*([^()]*)\s*\)", re.IGNORECASE)
        def _sub_any(m: re.Match[str]) -> str:
            lo_raw = m.group(1).strip() or "1"
            hi_raw = m.group(2).strip()
            lo = _convert_expr(lo_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            if hi_raw:
                hi = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            elif vv.char_len:
                hi = _simplify_int_expr_text(vv.char_len)
            else:
                hi = f"((int) strlen({nm}))"
            return f"substr_s({nm}, {lo}, {hi})"
        out = pat_sub_any.sub(_sub_any, out)
    out = out.replace("%", ".")
    out = _rewrite_assumed_shape_calls(
        out, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names
    )
    out = re.sub(r'(?i)\b([a-z_]\w*)\s*==\s*("[^"]*")', r"strcmp(\1, \2) == 0", out)
    out = re.sub(r'(?i)\b([a-z_]\w*)\s*!=\s*("[^"]*")', r"strcmp(\1, \2) != 0", out)
    out = re.sub(r'(?i)(substr_s\([^)]*\)|trim_s\([^)]*\)|adjustl_s\([^)]*\)|adjustr_s\([^)]*\))\s*==\s*("[^"]*")', r"strcmp(\1, \2) == 0", out)
    out = re.sub(r'(?i)(substr_s\([^)]*\)|trim_s\([^)]*\)|adjustl_s\([^)]*\)|adjustr_s\([^)]*\))\s*!=\s*("[^"]*")', r"strcmp(\1, \2) != 0", out)

    def _whole_array_helper_name(prefix: str, v: Var, rank: int) -> str:
        cty = (v.ctype or real_type).lower()
        if cty == "double":
            suf = "double"
        elif cty == "int":
            suf = "int"
        else:
            suf = "float"
        return f"{prefix}_{rank}d_{suf}"

    def _rewrite_intrinsic_call(name: str, inner: str) -> Optional[str]:
        nm = name.lower()
        args = [x.strip() for x in _split_args_top_level(inner) if x.strip()]
        def _ctype_for_arg(raw: str) -> str:
            t = raw.strip()
            m_id = re.fullmatch(r"([a-z_]\w*)", t, re.IGNORECASE)
            if m_id:
                vv = vars_map.get(m_id.group(1).lower())
                if vv is not None:
                    return (vv.ctype or real_type).lower()
            if re.search(r"(?i)_(?:dp|real64)\b", t):
                return "double"
            if re.search(r"(?i)_(?:sp|real32)\b", t):
                return "float"
            ct = _format_item_ctype(raw, vars_map, real_type).lower()
            if ct == real_type.lower():
                vv = vars_map.get(raw.strip().lower())
                if vv is not None:
                    ct = (vv.ctype or real_type).lower()
            return ct
        def _float_consts(raw: str) -> tuple[str, str, str, str, str, str]:
            is_float = _ctype_for_arg(raw) == "float"
            return (
                "FLT_EPSILON" if is_float else "DBL_EPSILON",
                "FLT_MIN" if is_float else "DBL_MIN",
                "FLT_MANT_DIG" if is_float else "DBL_MANT_DIG",
                "FLT_MAX_EXP" if is_float else "DBL_MAX_EXP",
                "FLT_MIN_EXP" if is_float else "DBL_MIN_EXP",
                "FLT_DIG" if is_float else "DBL_DIG",
            )
        def _nextafter_name(raw: str) -> str:
            return "nextafterf" if _ctype_for_arg(raw) == "float" else "nextafter"
        def _fabs_name(raw: str) -> str:
            return "fabsf" if _ctype_for_arg(raw) == "float" else "fabs"
        def _ilogb_name(raw: str) -> str:
            return "ilogbf" if _ctype_for_arg(raw) == "float" else "ilogb"
        def _scalbn_name(raw: str) -> str:
            return "scalbnf" if _ctype_for_arg(raw) == "float" else "scalbn"
        def _math1_name(base: str, raw: str) -> str:
            return f"{base}f" if _ctype_for_arg(raw) == "float" else base
        def _pi_expr(raw: str) -> str:
            return "acosf(-1.0f)" if _ctype_for_arg(raw) == "float" else "acos(-1.0)"
        def _deg_to_rad(raw_expr: str, raw_type_ref: str) -> str:
            carg = _convert_expr(raw_expr, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"(({carg}) * ({_pi_expr(raw_type_ref)}) / 180.0)"
        def _rad_to_deg(rad_expr: str, raw_type_ref: str) -> str:
            return f"(({rad_expr}) * 180.0 / ({_pi_expr(raw_type_ref)}))"
        if nm == "selected_real_kind":
            p_val: Optional[int] = None
            r_val: Optional[int] = None
            for idx, arg in enumerate(args):
                m_kw = re.match(r"(?i)^([pr])\s*=\s*(.+)$", arg)
                if m_kw:
                    val = _eval_int_expr(_convert_expr(m_kw.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names))
                    if m_kw.group(1).lower() == "p":
                        p_val = val
                    else:
                        r_val = val
                    continue
                val = _eval_int_expr(_convert_expr(arg, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names))
                if idx == 0:
                    p_val = val
                elif idx == 1:
                    r_val = val
            p_val = 0 if p_val is None else p_val
            r_val = 0 if r_val is None else r_val
            if p_val <= 6 and r_val <= 37:
                return "4"
            if p_val <= 15 and r_val <= 307:
                return "8"
            return "-1"
        if nm == "selected_int_kind" and len(args) >= 1:
            rval = _eval_int_expr(_convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names))
            if rval is None:
                return "-1"
            if rval <= 9:
                return "4"
            if rval <= 18:
                return "8"
            return "-1"
        if nm == "digits" and len(args) >= 1:
            return _float_consts(args[0])[2]
        if nm == "epsilon" and len(args) >= 1:
            return _float_consts(args[0])[0]
        if nm == "tiny" and len(args) >= 1:
            return _float_consts(args[0])[1]
        if nm == "maxexponent" and len(args) >= 1:
            return _float_consts(args[0])[3]
        if nm == "minexponent" and len(args) >= 1:
            return _float_consts(args[0])[4]
        if nm == "precision" and len(args) >= 1:
            return _float_consts(args[0])[5]
        if nm == "radix" and len(args) >= 1:
            return "FLT_RADIX"
        if nm == "range" and len(args) >= 1:
            ct0 = _ctype_for_arg(args[0])
            if ct0 == "int":
                return "9"
            if ct0 in {"long long", "long long int"}:
                return "18"
            return "37" if ct0 == "float" else "307"
        if nm == "bit_size" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((int) (sizeof({carg}) * CHAR_BIT))"
        if nm == "storage_size" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((int) (sizeof({carg}) * CHAR_BIT))"
        if nm == "nearest" and len(args) >= 2:
            x = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            sdir = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            inf = "HUGE_VALF" if _ctype_for_arg(args[0]) == "float" else "HUGE_VAL"
            return f"({_nextafter_name(args[0])}(({x}), (({sdir}) >= 0 ? ({inf}) : -({inf}))))"
        if nm == "spacing" and len(args) >= 1:
            x = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            _, tiny_c, _, _, _, _ = _float_consts(args[0])
            inf = "HUGE_VALF" if _ctype_for_arg(args[0]) == "float" else "HUGE_VAL"
            return f"((({x}) == 0) ? ({tiny_c}) : {_fabs_name(args[0])}({_nextafter_name(args[0])}(({x}), (({x}) >= 0 ? ({inf}) : -({inf}))) - ({x})))"
        if nm == "exponent" and len(args) >= 1:
            x = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((({x}) == 0) ? 0 : ({_ilogb_name(args[0])}({x}) + 1))"
        if nm == "fraction" and len(args) >= 1:
            x = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((({x}) == 0) ? ({x}) : ({_scalbn_name(args[0])}(({x}), -({_ilogb_name(args[0])}({x}) + 1))))"
        if nm == "set_exponent" and len(args) >= 2:
            x = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            i = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            frac = f"((({x}) == 0) ? ({x}) : ({_scalbn_name(args[0])}(({x}), -({_ilogb_name(args[0])}({x}) + 1))))"
            return f"((({x}) == 0) ? ({x}) : ({_scalbn_name(args[0])}(({frac}), ({i}))))"
        if nm == "scale" and len(args) >= 2:
            x = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            i = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"({_scalbn_name(args[0])}(({x}), ({i})))"
        if nm == "real" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            if _format_item_ctype(args[0], vars_map, real_type) == "complex":
                return _complex_real_expr(carg, real_type)
            return f"(({real_type}) ({carg}))"
        if nm == "dble" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            if _format_item_ctype(args[0], vars_map, real_type) == "complex":
                return _complex_real_expr(carg, "double")
            return f"((double) ({carg}))"
        if nm == "cmplx" and len(args) >= 1:
            re_arg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            im_arg = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if len(args) >= 2 else "0"
            cty = _complex_ctype(real_type)
            return f"(({cty}) (({re_arg}) + ({im_arg}) * I))"
        if nm == "conjg" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return _complex_conj_expr(carg, real_type)
        if nm == "aimag" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return _complex_imag_expr(carg, real_type)
        if nm == "abs" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            if _format_item_ctype(args[0], vars_map, real_type) == "complex":
                return _complex_abs_expr(carg, real_type)
            return f"({'fabs' if real_type == 'double' else 'fabsf'}({carg}))"
        if nm == "sqrt" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            if _format_item_ctype(args[0], vars_map, real_type) == "complex":
                return _complex_sqrt_expr(carg, real_type)
            return f"({'sqrt' if real_type == 'double' else 'sqrtf'}({carg}))"
        if nm == "int" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((int) ({carg}))"
        if nm == "nint" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((int) lround({carg}))"
        if nm == "anint" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"({'roundf' if real_type == 'float' else 'round'}({carg}))"
        if nm == "aint" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"({'truncf' if real_type == 'float' else 'trunc'}({carg}))"
        if nm == "floor" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((int) ({'floorf' if real_type == 'float' else 'floor'}({carg})))"
        if nm == "ceiling" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"((int) ({'ceilf' if real_type == 'float' else 'ceil'}({carg})))"
        if nm == "log10" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"({'log10f' if real_type == 'float' else 'log10'}({carg}))"
        if nm in {"sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "exp", "log"} and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"{_math1_name(nm, args[0])}({carg})"
        if nm == "gamma" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"{_math1_name('tgamma', args[0])}({carg})"
        if nm == "log_gamma" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"{_math1_name('lgamma', args[0])}({carg})"
        if nm == "cosd" and len(args) >= 1:
            return f"{_math1_name('cos', args[0])}({_deg_to_rad(args[0], args[0])})"
        if nm == "sind" and len(args) >= 1:
            return f"{_math1_name('sin', args[0])}({_deg_to_rad(args[0], args[0])})"
        if nm == "tand" and len(args) >= 1:
            return f"{_math1_name('tan', args[0])}({_deg_to_rad(args[0], args[0])})"
        if nm == "acosd" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return _rad_to_deg(f"{_math1_name('acos', args[0])}({carg})", args[0])
        if nm == "asind" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return _rad_to_deg(f"{_math1_name('asin', args[0])}({carg})", args[0])
        if nm in {"bessel_j0", "bessel_j1", "bessel_y0", "bessel_y1"} and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            base_map = {
                "bessel_j0": "j0",
                "bessel_j1": "j1",
                "bessel_y0": "y0",
                "bessel_y1": "y1",
            }
            base_nm = base_map[nm]
            if _ctype_for_arg(args[0]) == "float":
                return f"((float) {base_nm}((double) ({carg})))"
            return f"{base_nm}({carg})"
        if nm in {"mod", "modulo"} and len(args) >= 2:
            a_raw = args[0]
            b_raw = args[1]
            a = _convert_expr(a_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            b = _convert_expr(b_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            def _looks_int(raw: str) -> bool:
                s = raw.strip().lower()
                if re.fullmatch(r"[+\-]?\d+", s):
                    return True
                if re.fullmatch(r"[a-z_]\w*", s):
                    vv = vars_map.get(s)
                    return vv is not None and (vv.ctype or "").lower() == "int"
                if re.match(r"^(?:int|nint|floor|ceiling)\s*\(", s, re.IGNORECASE):
                    return True
                return False
            if _looks_int(a_raw) and _looks_int(b_raw):
                if nm == "mod":
                    return f"((({a}) % ({b})))"
                rem = f"((({a}) % ({b})))"
                return f"((({rem}) != 0 && ((({rem}) < 0) != (({b}) < 0))) ? (({rem}) + ({b})) : ({rem}))"
            if nm == "mod":
                return f"({'fmodf' if real_type == 'float' else 'fmod'}({a}, {b}))"
            return f"(({a}) - ({b}) * ({'floorf' if real_type == 'float' else 'floor'}(({a}) / ({b}))))"
        if nm == "sign" and len(args) >= 2:
            a = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            b = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            aabs = f"((({a}) < 0) ? -({a}) : ({a}))"
            return f"((({b}) >= 0) ? ({aabs}) : -({aabs}))"
        if nm == "allocated" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"({carg} != NULL)"
        if nm == "huge" and len(args) >= 1:
            ct0 = _ctype_for_arg(args[0])
            if ct0 == "int":
                return "INT_MAX"
            if ct0 in {"long long", "long long int"}:
                return "LLONG_MAX"
            return "FLT_MAX" if ct0 == "float" else "DBL_MAX"
        if nm == "size" and len(args) >= 1:
            arg0 = args[0].strip()
            sec_shape = _section_shape_exprs(
                arg0,
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            if sec_shape is not None:
                if len(args) >= 2:
                    dim_raw = args[1]
                    m_dim_kw = re.match(r"^\s*dim\s*=\s*(.+?)\s*$", dim_raw, re.IGNORECASE)
                    if m_dim_kw:
                        dim_raw = m_dim_kw.group(1).strip()
                    dim_expr = _convert_expr(dim_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    dim_int = _eval_int_expr(dim_expr)
                    if dim_int is not None and 1 <= dim_int <= len(sec_shape):
                        return sec_shape[dim_int - 1]
                    return "(" + " : ".join([f"(({dim_expr}) == {k+1}) ? ({sec_shape[k]})" for k in range(len(sec_shape))]) + " : 0)"
                if len(sec_shape) == 1:
                    return sec_shape[0]
                return "(" + " * ".join(f"({s})" for s in sec_shape) + ")"
        if nm == "merge" and len(args) >= 3:
            tsource = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            fsource = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            mask = _convert_expr(args[2], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"(({mask}) ? ({tsource}) : ({fsource}))"
        if nm == "rank" and len(args) >= 1:
            arr = args[0].strip().lower()
            v = vars_map.get(arr)
            if v is not None and v.is_array:
                dparts = _resolved_dim_parts(v, arr, assumed_extents)
                return str(max(1, len(dparts)))
            return None
        if nm in {"lbound", "ubound", "shape"} and len(args) >= 1:
            arr = args[0].lower()
            v = vars_map.get(arr)
            if v is None or not v.is_array:
                return None
            dparts = _resolved_dim_parts(v, arr, assumed_extents)
            if nm == "shape":
                vals = [_dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts]
            elif nm == "lbound":
                vals = [_dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts]
            else:
                vals = []
                for p in dparts:
                    lo = _dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                    ext = _dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                    vals.append(f"(({lo}) + ({ext}) - 1)")
            if len(args) >= 2:
                dim_raw = args[1]
                m_dim_kw = re.match(r"^\s*dim\s*=\s*(.+?)\s*$", dim_raw, re.IGNORECASE)
                if m_dim_kw:
                    dim_raw = m_dim_kw.group(1).strip()
                dim_expr = _convert_expr(dim_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                dim_int = _eval_int_expr(dim_expr)
                if dim_int is not None and 1 <= dim_int <= len(vals):
                    return vals[dim_int - 1]
                return "(" + " : ".join([f"(({dim_expr}) == {k+1}) ? ({vals[k]})" for k in range(len(vals))]) + " : 0)"
            if len(vals) == 1:
                return vals[0]
            if vals:
                return "((int[]){" + ", ".join(vals) + "})"
            return None
        if nm in {"minloc", "maxloc", "findloc"} and len(args) >= 1:
            return None
        if nm == "len" and len(args) >= 1:
            arg0 = args[0].strip().lower()
            vv = vars_map.get(arg0)
            if vv is not None and (vv.ctype or '').lower() == 'char *':
                if vv.char_len and ":" not in vv.char_len:
                    return _simplify_int_expr_text(vv.char_len)
                carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                return f"((int) strlen({carg}))"
            if _is_fortran_string_literal(args[0].strip()):
                return str(len(_unquote_fortran_string_literal(args[0].strip())))
        if nm == "len_trim" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"len_trim_s({carg})"
        if nm == "trim" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"trim_s({carg})"
        if nm == "adjustl" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"adjustl_s({carg})"
        if nm == "adjustr" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"adjustr_s({carg})"
        if nm == "repeat" and len(args) >= 2:
            s = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            ncopy = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"repeat_s({s}, {ncopy})"
        if nm == "index" and len(args) >= 2:
            s = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            sub = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"index_s({s}, {sub})"
        if nm == "scan" and len(args) >= 2:
            s = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            setc = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"scan_s({s}, {setc})"
        if nm == "verify" and len(args) >= 2:
            s = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            setc = _convert_expr(args[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"verify_s({s}, {setc})"
        if nm in {"achar", "char"} and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"achar_s({carg})"
        if nm == "iachar" and len(args) >= 1:
            carg = _convert_expr(args[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"iachar_s({carg})"
        if nm in {"count", "any", "all"} and len(args) >= 1 and re.fullmatch(r"[a-z_]\w*", args[0], re.IGNORECASE):
            arr = args[0].lower()
            v = vars_map.get(arr)
            if v is None or not v.is_array:
                return None
            dparts = _resolved_dim_parts(v, arr, assumed_extents)
            rank = max(1, len(dparts))
            if rank > 2:
                return None
            if rank >= 2 and len(dparts) >= 2:
                d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                return f"{nm}_{rank}d_int({d1}, {d2}, {arr})"
            n1 = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
            return f"{nm}_{rank}d_int({n1}, {arr})"
        if nm in {"sum", "product"} and len(args) >= 1:
            arg0s = args[0].strip()
            m_empty_typed = re.match(r"^\[\s*(real|integer|double\s+precision|logical|complex|character(?:\s*\([^\]]*\))?|type\s*\(\s*[a-z_]\w*\s*\))\s*::\s*\]$", arg0s, re.IGNORECASE)
            if m_empty_typed:
                t0 = m_empty_typed.group(1).strip().lower()
                if nm == "sum":
                    if t0.startswith("double"):
                        return "0.0"
                    if t0.startswith("real"):
                        return "0.0f"
                    if t0.startswith("integer"):
                        return "0"
                else:
                    if t0.startswith("double"):
                        return "1.0"
                    if t0.startswith("real"):
                        return "1.0f"
                    if t0.startswith("integer"):
                        return "1"
        if nm == "dot_product" and len(args) >= 2 and re.fullmatch(r"[a-z_]\w*", args[0], re.IGNORECASE) and re.fullmatch(r"[a-z_]\w*", args[1], re.IGNORECASE):
            x = args[0].lower()
            y = args[1].lower()
            vx = vars_map.get(x)
            vy = vars_map.get(y)
            if vx is None or vy is None or (not vx.is_array) or (not vy.is_array):
                return None
            dparts_x = _resolved_dim_parts(vx, x, assumed_extents)
            dparts_y = _resolved_dim_parts(vy, y, assumed_extents)
            if tuple(dparts_x) != tuple(dparts_y):
                return None
            rank = max(1, len(dparts_x))
            if rank > 2:
                return None
            helper = _whole_array_helper_name("dot_product", vx, rank)
            if rank >= 2 and len(dparts_x) >= 2:
                d1 = _convert_expr(dparts_x[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                d2 = _convert_expr(dparts_x[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                return f"{helper}({d1}, {d2}, {x}, {y})"
            n1 = _dim_product_from_parts(dparts_x, vars_map, real_type, byref_scalars, assumed_extents)
            return f"{helper}({n1}, {x}, {y})"
        return None

    out = _rewrite_named_calls(out, _rewrite_intrinsic_call)

    # SUM lowering for simple whole-array forms with DIM on rank-1 arrays.
    def _sum_dim_repl(m: re.Match[str]) -> str:
        arr = m.group(1).lower()
        dim_txt = (m.group(2) or "").strip()
        try:
            dim_no = int(dim_txt)
        except Exception:
            return m.group(0)
        v = vars_map.get(arr)
        if v is None or not v.is_array:
            return m.group(0)
        dparts = _resolved_dim_parts(v, arr, assumed_extents)
        rank = max(1, len(dparts))
        cty = (v.ctype or real_type).lower()
        if cty == "double":
            suf = "double"
        elif cty == "int":
            suf = "int"
        else:
            suf = "float"
        if rank == 1 and dim_no == 1:
            n1 = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
            return f"sum_1d_{suf}({n1}, {arr})"
        return m.group(0)

    out = re.sub(r"(?i)\bsum\s*\(\s*([a-z_]\w*)\s*,\s*dim\s*=\s*([0-9]+)\s*\)", _sum_dim_repl, out)
    out = re.sub(r"(?i)\bsum\s*\(\s*([a-z_]\w*)\s*,\s*([0-9]+)\s*\)", _sum_dim_repl, out)

    # PRODUCT lowering for simple whole-array forms with DIM on rank-1 arrays.
    def _product_dim_repl(m: re.Match[str]) -> str:
        arr = m.group(1).lower()
        dim_txt = (m.group(2) or "").strip()
        try:
            dim_no = int(dim_txt)
        except Exception:
            return m.group(0)
        v = vars_map.get(arr)
        if v is None or not v.is_array:
            return m.group(0)
        dparts = _resolved_dim_parts(v, arr, assumed_extents)
        rank = max(1, len(dparts))
        cty = (v.ctype or real_type).lower()
        if cty == "double":
            suf = "double"
        elif cty == "int":
            suf = "int"
        else:
            suf = "float"
        if rank == 1 and dim_no == 1:
            n1 = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
            return f"product_1d_{suf}({n1}, {arr})"
        return m.group(0)

    out = re.sub(r"(?i)\bproduct\s*\(\s*([a-z_]\w*)\s*,\s*dim\s*=\s*([0-9]+)\s*\)", _product_dim_repl, out)
    out = re.sub(r"(?i)\bproduct\s*\(\s*([a-z_]\w*)\s*,\s*([0-9]+)\s*\)", _product_dim_repl, out)


    # SUM lowering for simple whole-array forms: sum(x), sum(x2d)
    def _sum_repl(m: re.Match[str]) -> str:
        arr = m.group(1).lower()
        v = vars_map.get(arr)
        if v is None or not v.is_array:
            return m.group(0)
        dparts = _resolved_dim_parts(v, arr, assumed_extents)
        rank = max(1, len(dparts))
        cty = (v.ctype or real_type).lower()
        if cty == "double":
            suf = "double"
        elif cty == "int":
            suf = "int"
        else:
            suf = "float"
        if rank >= 2 and len(dparts) >= 2:
            d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"sum_2d_{suf}({d1}, {d2}, {arr})"
        n1 = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
        return f"sum_1d_{suf}({n1}, {arr})"

    out = re.sub(r"(?i)\bsum\s*\(\s*([a-z_]\w*)\s*\)", _sum_repl, out)

    # PRODUCT lowering for simple whole-array forms: product(x), product(x2d)
    def _prod_repl(m: re.Match[str]) -> str:
        arr = m.group(1).lower()
        v = vars_map.get(arr)
        if v is None or not v.is_array:
            return m.group(0)
        dparts = _resolved_dim_parts(v, arr, assumed_extents)
        rank = max(1, len(dparts))
        cty = (v.ctype or real_type).lower()
        if cty == "double":
            suf = "double"
        elif cty == "int":
            suf = "int"
        else:
            suf = "float"
        if rank >= 2 and len(dparts) >= 2:
            d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f"product_2d_{suf}({d1}, {d2}, {arr})"
        n1 = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
        return f"product_1d_{suf}({n1}, {arr})"

    out = re.sub(r"(?i)\bproduct\s*\(\s*([a-z_]\w*)\s*\)", _prod_repl, out)
    # MINVAL/MAXVAL lowering for simple whole-array forms.
    def _minmax_repl(m: re.Match[str], kind: str) -> str:
        arr = m.group(1).lower()
        v = vars_map.get(arr)
        if v is None or not v.is_array:
            return m.group(0)
        dparts = _resolved_dim_parts(v, arr, assumed_extents)
        n1 = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
        cty = (v.ctype or real_type).lower()
        if cty == "double":
            suf = "double"
        elif cty == "int":
            suf = "int"
        else:
            suf = "float"
        return f"{kind}_1d_{suf}({n1}, {arr})"

    out = re.sub(r"(?i)\bminval\s*\(\s*([a-z_]\w*)\s*\)", lambda m: _minmax_repl(m, "minval"), out)
    out = re.sub(r"(?i)\bmaxval\s*\(\s*([a-z_]\w*)\s*\)", lambda m: _minmax_repl(m, "maxval"), out)
    out = _replace_pow(out)
    # SIZE lowering for assumed-shape (and known-shape) arrays.
    def _size_repl(m: re.Match[str]) -> str:
        arr = m.group(1).lower()
        dim_txt = (m.group(2) or "").strip()
        dim_no = None
        if dim_txt:
            try:
                dim_no = int(dim_txt)
            except Exception:
                dim_no = None
        # Prefer explicit assumed-shape extents for dummy arrays.
        if assumed_extents and arr in assumed_extents and assumed_extents[arr]:
            exts = assumed_extents[arr]
            if dim_no is not None and 1 <= dim_no <= len(exts):
                return exts[dim_no - 1]
            if len(exts) == 1:
                return exts[0]
            return "(" + " * ".join(exts) + ")"
        v = vars_map.get(arr)
        if v is not None and v.is_array:
            if v.is_allocatable:
                dps_alloc = _resolved_dim_parts(v, arr, assumed_extents)
                if dim_no is not None and 1 <= dim_no <= len(dps_alloc):
                    return dps_alloc[dim_no - 1]
                if dim_no is None:
                    return _dim_product_from_parts(dps_alloc, vars_map, real_type, byref_scalars, assumed_extents)
            dps = _dim_parts(v.dim)
            if dim_no is not None and 1 <= dim_no <= len(dps):
                return _convert_expr(dps[dim_no - 1], vars_map, real_type, byref_scalars, assumed_extents)
            return _dim_product_expr(v.dim, vars_map, real_type, byref_scalars)
        return m.group(0)

    out = re.sub(
        r"(?i)\bsize\s*\(\s*([a-z_]\w*)\s*(?:,\s*([0-9]+)\s*)?\)",
        _size_repl,
        out,
    )
    out = re.sub(r"(?i)\babs\s*\(", "fabsf(" if real_type == "float" else "fabs(", out)
    if real_type == "float":
        out = re.sub(r"(?i)\bmin\s*\(", "fminf(", out)
        out = re.sub(r"(?i)\bmax\s*\(", "fmaxf(", out)
    else:
        out = re.sub(r"(?i)\bmin\s*\(", "fmin(", out)
        out = re.sub(r"(?i)\bmax\s*\(", "fmax(", out)

    # Array indexing: x(i) -> x[(i)-1] for known rank-1 arrays.
    for name, v in vars_map.items():
        if not v.is_array:
            continue
        pat = re.compile(rf"\b{re.escape(name)}\s*\(\s*([^)]+?)\s*\)", re.IGNORECASE)
        def _arr_idx(m: re.Match[str]) -> str:
            idx_raw = m.group(1).strip()
            idx_parts = _split_args_top_level(idx_raw)
            dparts = _resolved_dim_parts(v, name, assumed_extents)
            if len(idx_parts) <= 1:
                i_expr = _convert_expr(
                    idx_parts[0] if idx_parts else idx_raw,
                    vars_map,
                    real_type,
                    byref_scalars,
                    assumed_extents,
                )
                i_expr = _simplify_int_expr_text(i_expr.strip())
                iv = _eval_int_expr(i_expr)
                lb1 = _dim_lb_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents) if dparts else "1"
                if iv is not None:
                    lbv = _eval_int_expr(lb1)
                    if lbv is not None:
                        return f"{name}[{iv - lbv}]"
                return f"{name}[({i_expr}) - ({lb1})]"
            # Multi-dimensional: flatten in Fortran column-major order.
            if len(dparts) == len(idx_parts):
                lin = _fortran_sub_to_linear(idx_parts, dparts, vars_map, real_type, byref_scalars, assumed_extents)
                return f"{name}[{lin}]"
            # Fallback: keep first index behavior if rank information mismatches.
            i_expr = _convert_expr(idx_parts[0], vars_map, real_type, byref_scalars, assumed_extents)
            lb1 = _dim_lb_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents) if dparts else "1"
            return f"{name}[({i_expr}) - ({lb1})]"
        out = pat.sub(_arr_idx, out)
    for nm, vv in sorted(vars_map.items(), key=lambda kv: len(kv[0]), reverse=True):
        if (vv.ctype or "").lower() in _ACTIVE_DERIVED_TYPES and vv.is_pointer and not vv.is_array:
            out = re.sub(rf"\b{re.escape(nm)}\s*\.", f"{nm}->", out)
    for nm, vv in sorted(vars_map.items(), key=lambda kv: len(kv[0]), reverse=True):
        if vv.is_pointer and not vv.is_array and (vv.ctype or "").lower() not in _ACTIVE_DERIVED_TYPES:
            out = re.sub(rf"\b{re.escape(nm)}\b", f"(*{nm})", out)
    if byref_scalars:
        for nm in sorted(byref_scalars, key=len, reverse=True):
            vv = vars_map.get(nm.lower())
            if vv is not None and (vv.ctype or "").lower() in _ACTIVE_DERIVED_TYPES:
                out = re.sub(rf"\b{re.escape(nm)}\s*\.", f"{nm}->", out)
                continue
            if vv is not None and (vv.ctype or "").lower() == "char *" and not vv.is_array:
                continue
            out = re.sub(rf"(?<![\w*&])\b{re.escape(nm)}\b", f"*{nm}", out)
    for nm, vv in sorted(vars_map.items(), key=lambda kv: len(kv[0]), reverse=True):
        if vv.optional and (vv.ctype or "").lower() == "char *" and not vv.is_array:
            out = re.sub(rf"(?<![\w*&])\b{re.escape(nm)}\b", f"*{nm}", out)
    # Keep present(...) lowering stable even when optional scalars are byref-dereferenced.
    out = re.sub(r"\*\s*([a-z_]\w*)\s*!=\s*NULL", r"\1 != NULL", out, flags=re.IGNORECASE)
    out = re.sub(r"NULL\s*!=\s*\*\s*([a-z_]\w*)", r"NULL != \1", out, flags=re.IGNORECASE)
    out = re.sub(r"\*\s*([a-z_]\w*)\s*==\s*NULL", r"\1 == NULL", out, flags=re.IGNORECASE)
    out = re.sub(r"NULL\s*==\s*\*\s*([a-z_]\w*)", r"NULL == \1", out, flags=re.IGNORECASE)
    return out


def _parse_decls(
    unit: Dict[str, object],
    real_type: str,
    kind_ctype_map: Optional[Dict[str, str]] = None,
    local_derived_types: Optional[Dict[str, List[tuple[str, str]]]] = None,
) -> Dict[str, Var]:
    vars_map: Dict[str, Var] = {}
    body_line_nos: List[int] = list(unit.get("body_line_nos", []))
    source_lines: List[str] = list(unit.get("source_lines", []))
    type_ranges = _local_derived_type_index_ranges(unit) if local_derived_types else []
    for idx, raw in enumerate(unit["body_lines"]):
        if local_derived_types and _index_in_ranges(idx, type_ranges):
            continue
        code = _strip_comment(raw).strip()
        inline_comment = None
        if idx < len(body_line_nos):
            ln = body_line_nos[idx]
            if 1 <= ln <= len(source_lines):
                inline_comment = _extract_fortran_comment(source_lines[ln - 1])
        if not code:
            continue
        is_optional = bool(re.search(r"(?i),\s*optional\b", code))
        code_no_opt = re.sub(r"(?i),\s*optional\b", "", code)
        m_type_decl = re.match(
            r"^(?:type|class)\s*\(\s*([a-z_]\w*)\s*\)\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_type_no_colon = re.match(
            r"^(?:type|class)\s*\(\s*([a-z_]\w*)\s*\)\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        if m_type_decl or (m_type_no_colon and "::" not in code_no_opt):
            if m_type_decl:
                dt_name = m_type_decl.group(1).lower()
                attrs = (m_type_decl.group(2) or "").lower()
                ents = m_type_decl.group(3)
            else:
                dt_name = m_type_no_colon.group(1).lower()
                attrs = ""
                ents = m_type_no_colon.group(2)
            m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
            intent = m_intent.group(1).lower() if m_intent else None
            is_save = "save" in attrs
            is_param = "parameter" in attrs
            is_alloc = "allocatable" in attrs
            is_ptr = "pointer" in attrs
            is_target = "target" in attrs
            m_dim_attr = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
            dim_attr = m_dim_attr.group(1).strip() if m_dim_attr else None
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nma = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nma.lower()] = Var(dt_name, is_array=True, dim=dim, is_allocatable=is_alloc, is_pointer=is_ptr, is_target=is_target, init=init, is_save=is_save, is_param=is_param, intent=intent, optional=is_optional, comment=inline_comment)
                elif dim_attr is not None:
                    vars_map[lhs.lower()] = Var(dt_name, is_array=True, dim=dim_attr, is_allocatable=is_alloc, is_pointer=is_ptr, is_target=is_target, init=init, is_save=is_save, is_param=is_param, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var(dt_name, init=init, is_save=is_save, is_param=is_param, is_pointer=is_ptr, is_target=is_target, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        code_int_norm = re.sub(
            r"(?i)^integer\s*\(\s*kind\s*=\s*[^)]+\s*\)",
            "integer",
            code_no_opt,
        )
        m_int_kind_attr = re.match(
            r"^integer\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\)\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_int_kind_no_colon = re.match(
            r"^integer\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\)\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_int = re.match(
            r"^integer(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?(\s*,\s*parameter)?\s*::\s*(.+)$",
            code_int_norm,
            re.IGNORECASE,
        )
        m_int_attr = re.match(
            r"^integer\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_int_norm,
            re.IGNORECASE,
        )
        m_int_no_colon = re.match(
            r"^integer(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?(\s*,\s*parameter)?\s+(.+)$",
            code_int_norm,
            re.IGNORECASE,
        )
        if m_int_kind_attr:
            kind_tok = (m_int_kind_attr.group(1) or "").strip().lower()
            attrs = (m_int_kind_attr.group(2) or "").lower()
            ents = m_int_kind_attr.group(3)
            m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
            intent = m_intent.group(1).lower() if m_intent else None
            is_param = "parameter" in attrs
            is_save = "save" in attrs
            is_alloc = "allocatable" in attrs
            m_dim_attr = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
            dim_attr = m_dim_attr.group(1).strip() if m_dim_attr else None
            int_ct = kind_ctype_map.get(kind_tok, "long long" if (kind_tok.isdigit() and int(kind_tok) >= 8) else "int") if kind_ctype_map else ("long long" if (kind_tok.isdigit() and int(kind_tok) >= 8) else "int")
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent:
                    nm, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    nm, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", nm, re.IGNORECASE)
                if ma:
                    nma = ma.group(1)
                    dim = ma.group(2)
                    vars_map[nma.lower()] = Var(int_ct, is_array=True, dim=dim, is_allocatable=is_alloc, is_param=is_param, is_save=is_save, init=init, intent=intent, optional=is_optional, comment=inline_comment)
                elif dim_attr:
                    vars_map[nm.lower()] = Var(int_ct, is_array=True, dim=dim_attr, is_allocatable=is_alloc, is_param=is_param, is_save=is_save, init=init, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[nm.lower()] = Var(int_ct, is_param=is_param, is_save=is_save, init=init, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_int_kind_no_colon and "::" not in code_no_opt:
            kind_tok = (m_int_kind_no_colon.group(1) or "").strip().lower()
            ents = m_int_kind_no_colon.group(2)
            int_ct = kind_ctype_map.get(kind_tok, "long long" if (kind_tok.isdigit() and int(kind_tok) >= 8) else "int") if kind_ctype_map else ("long long" if (kind_tok.isdigit() and int(kind_tok) >= 8) else "int")
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent:
                    nm, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    nm, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", nm, re.IGNORECASE)
                if ma:
                    nma = ma.group(1)
                    dim = ma.group(2)
                    vars_map[nma.lower()] = Var(int_ct, is_array=True, dim=dim, init=init, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[nm.lower()] = Var(int_ct, init=init, optional=is_optional, comment=inline_comment)
            continue
        if m_int:
            intent = m_int.group(1).lower() if m_int.group(1) else None
            is_param = bool(m_int.group(2))
            for ent in [x.strip() for x in _split_args_top_level(m_int.group(3)) if x.strip()]:
                if "=" in ent:
                    nm, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    nm, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", nm, re.IGNORECASE)
                if ma:
                    nma = ma.group(1)
                    dim = ma.group(2)
                    vars_map[nma.lower()] = Var(
                        "int",
                        is_array=True,
                        dim=dim,
                        is_param=is_param,
                        init=init,
                        intent=intent,
                        optional=is_optional,
                        comment=inline_comment,
                    )
                else:
                    vars_map[nm.lower()] = Var("int", is_param=is_param, init=init, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_int_attr:
            attrs = (m_int_attr.group(1) or "").lower()
            ents = m_int_attr.group(2)
            m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
            intent = m_intent.group(1).lower() if m_intent else None
            is_param = "parameter" in attrs
            is_save = "save" in attrs
            is_alloc = "allocatable" in attrs
            m_dim_attr = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
            dim_attr = m_dim_attr.group(1).strip() if m_dim_attr else None
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent:
                    nm, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    nm, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", nm, re.IGNORECASE)
                if ma:
                    nma = ma.group(1)
                    dim = ma.group(2)
                    vars_map[nma.lower()] = Var(
                        "int",
                        is_array=True,
                        dim=dim,
                        is_allocatable=is_alloc,
                        is_param=is_param,
                        is_save=is_save,
                        init=init,
                        intent=intent,
                        optional=is_optional,
                        comment=inline_comment,
                    )
                elif dim_attr:
                    vars_map[nm.lower()] = Var(
                        "int",
                        is_array=True,
                        dim=dim_attr,
                        is_allocatable=is_alloc,
                        is_param=is_param,
                        is_save=is_save,
                        init=init,
                        intent=intent,
                        optional=is_optional,
                        comment=inline_comment,
                    )
                else:
                    vars_map[nm.lower()] = Var(
                        "int",
                        is_param=is_param,
                        is_save=is_save,
                        init=init,
                        intent=intent,
                        optional=is_optional,
                        comment=inline_comment,
                    )
            continue
        if m_int_no_colon and "::" not in code_no_opt:
            intent = m_int_no_colon.group(1).lower() if m_int_no_colon.group(1) else None
            is_param = bool(m_int_no_colon.group(2))
            for ent in [x.strip() for x in _split_args_top_level(m_int_no_colon.group(3)) if x.strip()]:
                if "=" in ent:
                    nm, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    nm, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", nm, re.IGNORECASE)
                if ma:
                    nma = ma.group(1)
                    dim = ma.group(2)
                    vars_map[nma.lower()] = Var(
                        "int",
                        is_array=True,
                        dim=dim,
                        is_param=is_param,
                        init=init,
                        intent=intent,
                        optional=is_optional,
                        comment=inline_comment,
                    )
                else:
                    vars_map[nm.lower()] = Var("int", is_param=is_param, init=init, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        m_real = re.match(
            r"^real\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\)(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_real_attr = re.match(
            r"^real\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\)\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        if not m_real:
            m_real = re.match(
                r"^real(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s*,\s*kind\s*=\s*([a-z_]\w*|[0-9]+)\s*::\s*(.+)$",
                code_no_opt,
                re.IGNORECASE,
            )
        m_real_kind_no_colon = re.match(
            r"^real\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\)\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_real_bare = re.match(
            r"^real(?!\s*\()(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_real_bare_attr = re.match(
            r"^real(?!\s*\()\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_real_bare_no_colon = re.match(
            r"^real(?!\s*\()(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_dprec = re.match(
            r"^double\s+precision(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_dprec_no_colon = re.match(
            r"^double\s+precision(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_complex = re.match(
            r"^complex(?:\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\))?(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_complex_attr = re.match(
            r"^complex(?:\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\))?\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_complex_no_colon = re.match(
            r"^complex(?:\s*\(\s*(?:kind\s*=\s*)?([a-z_]\w*|[0-9]+)\s*\))?(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_char = re.match(
            r"^character\s*\(\s*len\s*=\s*.+\)\s*(?:,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_logical = re.match(
            r"^logical(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_logical_attr = re.match(
            r"^logical\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_logical_no_colon = re.match(
            r"^logical(?:\s*,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_char_no_colon = re.match(
            r"^character\s*\(\s*len\s*=\s*.+\)\s*(?:,\s*intent\s*\(\s*(in|out|inout)\s*\))?\s+(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        m_char_attr = re.match(
            r"^character\s*\(\s*len\s*=\s*(.+)\)\s*(?:,\s*([^:]+))?\s*::\s*(.+)$",
            code_no_opt,
            re.IGNORECASE,
        )
        if m_char_attr:
            char_len = (m_char_attr.group(1) or '').strip()
            attrs = (m_char_attr.group(2) or '').lower()
            ents = m_char_attr.group(3)
            m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
            intent = m_intent.group(1).lower() if m_intent else None
            is_param = "parameter" in attrs
            is_alloc = "allocatable" in attrs
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = _infer_array_dim_from_init(ma.group(2).strip(), init)
                    vars_map[nm.lower()] = Var("char *", is_array=True, dim=dim, init=init, intent=intent, is_param=is_param, is_allocatable=is_alloc, optional=is_optional, comment=inline_comment, char_len=char_len)
                else:
                    vars_map[lhs.lower()] = Var("char *", init=init, intent=intent, is_param=is_param, is_allocatable=is_alloc, optional=is_optional, comment=inline_comment, char_len=char_len)
            continue
        if m_real or m_real_attr:
            # Normalize group layout across the two accepted real-decl forms.
            m_use = m_real if m_real is not None else m_real_attr
            assert m_use is not None
            if m_use.re.pattern.startswith("^real\\s*\\("):
                kind_tok = (m_use.group(1) or "").strip().lower()
                attrs = (m_use.group(2) or "").lower()
                m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
                intent = m_intent.group(1).lower() if m_intent else None
                ents = m_use.group(3)
                is_external = "external" in attrs
                is_alloc = "allocatable" in attrs
                m_dim_attr = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
                dim_attr = m_dim_attr.group(1).strip() if m_dim_attr else None
            else:
                kind_tok = (m_use.group(2) or "").strip().lower()
                intent = m_use.group(1).lower() if m_use.group(1) else None
                ents = m_use.group(3)
                is_external = False
                is_alloc = False
                dim_attr = None
            kind_ct = real_type
            if kind_tok:
                if kind_ctype_map and kind_tok in kind_ctype_map:
                    kind_ct = kind_ctype_map[kind_tok]
                elif kind_tok.isdigit():
                    # Heuristic for numeric kind IDs.
                    kind_ct = "double" if int(kind_tok) >= 8 else "float"
            is_param = "parameter" in attrs if "attrs" in locals() else False
            is_save = "save" in attrs if "attrs" in locals() else False
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = _infer_array_dim_from_init(ma.group(2).strip(), init)
                    vars_map[nm.lower()] = Var(
                        kind_ct,
                        is_array=True,
                        dim=dim,
                        init=init,
                        intent=intent,
                        is_external=is_external,
                        is_allocatable=is_alloc,
                        is_param=is_param,
                        is_save=is_save,
                        optional=is_optional,
                        comment=inline_comment,
                    )
                elif dim_attr:
                    vars_map[lhs.lower()] = Var(
                        kind_ct,
                        is_array=True,
                        dim=_infer_array_dim_from_init(dim_attr, init),
                        init=init,
                        intent=intent,
                        is_external=is_external,
                        is_allocatable=is_alloc,
                        is_param=is_param,
                        is_save=is_save,
                        optional=is_optional,
                        comment=inline_comment,
                    )
                else:
                    vars_map[lhs.lower()] = Var(
                        kind_ct,
                        init=init,
                        intent=intent,
                        is_external=is_external,
                        is_allocatable=is_alloc,
                        is_param=is_param,
                        is_save=is_save,
                        optional=is_optional,
                        comment=inline_comment,
                    )
            continue
        if m_real_kind_no_colon and "::" not in code_no_opt:
            kind_tok = (m_real_kind_no_colon.group(1) or "").strip().lower()
            ents = m_real_kind_no_colon.group(2)
            kind_ct = real_type
            if kind_tok:
                if kind_ctype_map and kind_tok in kind_ctype_map:
                    kind_ct = kind_ctype_map[kind_tok]
                elif kind_tok.isdigit():
                    kind_ct = "double" if int(kind_tok) >= 8 else "float"
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var(kind_ct, is_array=True, dim=dim, init=init, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var(kind_ct, init=init, optional=is_optional, comment=inline_comment)
            continue
        m_external = re.match(r"^external\s+(.+)$", code_no_opt, re.IGNORECASE)
        if m_external:
            for ent in [x.strip() for x in _split_args_top_level(m_external.group(1)) if x.strip()]:
                nm = ent.lower()
                v0 = vars_map.get(nm)
                if v0 is None:
                    vars_map[nm] = Var(real_type, is_external=True, optional=is_optional, comment=inline_comment)
                else:
                    v0.is_external = True
            continue
        if m_logical or m_logical_attr:
            m_use = m_logical if m_logical is not None else m_logical_attr
            assert m_use is not None
            if m_use.re.pattern.startswith("^logical(?:\\s*,\\s*intent"):
                intent = m_use.group(1).lower() if m_use.group(1) else None
                ents = m_use.group(2)
                is_external = False
                is_alloc = False
                dim_attr = None
            else:
                attrs = (m_use.group(1) or "").lower()
                ents = m_use.group(2)
                m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
                intent = m_intent.group(1).lower() if m_intent else None
                is_external = "external" in attrs
                is_alloc = "allocatable" in attrs
                m_dim_attr = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
                dim_attr = m_dim_attr.group(1).strip() if m_dim_attr else None
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var("int", is_array=True, dim=dim, is_logical=True, init=init, intent=intent, is_external=is_external, is_allocatable=is_alloc, optional=is_optional, comment=inline_comment)
                elif dim_attr:
                    vars_map[lhs.lower()] = Var("int", is_array=True, dim=dim_attr, is_logical=True, init=init, intent=intent, is_external=is_external, is_allocatable=is_alloc, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var("int", is_logical=True, init=init, intent=intent, is_external=is_external, is_allocatable=is_alloc, optional=is_optional, comment=inline_comment)
            continue
        if m_logical_no_colon and "::" not in code_no_opt:
            intent = m_logical_no_colon.group(1).lower() if m_logical_no_colon.group(1) else None
            ents = m_logical_no_colon.group(2)
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var("int", is_array=True, dim=dim, is_logical=True, init=init, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var("int", is_logical=True, init=init, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_real_bare:
            intent = m_real_bare.group(1).lower() if m_real_bare.group(1) else None
            ents = m_real_bare.group(2)
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var(real_type, is_array=True, dim=dim, init=init, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var(real_type, init=init, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_real_bare_attr:
            attrs = (m_real_bare_attr.group(1) or "").lower()
            ents = m_real_bare_attr.group(2)
            m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
            intent = m_intent.group(1).lower() if m_intent else None
            is_external = "external" in attrs
            is_alloc = "allocatable" in attrs
            is_ptr = "pointer" in attrs
            is_target = "target" in attrs
            is_param = "parameter" in attrs
            is_save = "save" in attrs
            m_dim_attr = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
            dim_attr = m_dim_attr.group(1).strip() if m_dim_attr else None
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                lhs, init, ptr_init = _split_decl_entity(ent)
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = _infer_array_dim_from_init(ma.group(2).strip(), init)
                    vars_map[nm.lower()] = Var(
                        real_type,
                        is_array=True,
                        dim=dim,
                        init=init,
                        ptr_init=ptr_init,
                        is_allocatable=is_alloc,
                        is_pointer=is_ptr,
                        is_target=is_target,
                        intent=intent,
                        is_external=is_external,
                        is_param=is_param,
                        is_save=is_save,
                        optional=is_optional,
                        comment=inline_comment,
                    )
                else:
                    nm = lhs
                    if dim_attr:
                        vars_map[nm.lower()] = Var(
                            real_type,
                            is_array=True,
                            dim=_infer_array_dim_from_init(dim_attr, init),
                            init=init,
                            ptr_init=ptr_init,
                            is_allocatable=is_alloc,
                            is_pointer=is_ptr,
                            is_target=is_target,
                            intent=intent,
                            is_external=is_external,
                            is_param=is_param,
                            is_save=is_save,
                            optional=is_optional,
                            comment=inline_comment,
                        )
                    else:
                        vars_map[nm.lower()] = Var(
                            real_type,
                            init=init,
                            ptr_init=ptr_init,
                            is_allocatable=is_alloc,
                            is_pointer=is_ptr,
                            is_target=is_target,
                            intent=intent,
                            is_external=is_external,
                            is_param=is_param,
                            is_save=is_save,
                            optional=is_optional,
                            comment=inline_comment,
                        )
            continue
        if m_real_bare_no_colon and "::" not in code_no_opt:
            intent = m_real_bare_no_colon.group(1).lower() if m_real_bare_no_colon.group(1) else None
            ents = m_real_bare_no_colon.group(2)
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var(real_type, is_array=True, dim=dim, init=init, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var(real_type, init=init, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_dprec:
            intent = m_dprec.group(1).lower() if m_dprec.group(1) else None
            ents = m_dprec.group(2)
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", ent, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var("double", is_array=True, dim=dim, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[ent.lower()] = Var("double", intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_dprec_no_colon and "::" not in code_no_opt:
            intent = m_dprec_no_colon.group(1).lower() if m_dprec_no_colon.group(1) else None
            ents = m_dprec_no_colon.group(2)
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", ent, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var("double", is_array=True, dim=dim, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[ent.lower()] = Var("double", intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_complex or m_complex_attr:
            m_use = m_complex if m_complex is not None else m_complex_attr
            assert m_use is not None
            kind_tok = (m_use.group(1) or "").strip().lower()
            if m_use.re.pattern.startswith("^complex(?:\\s*\\("):
                attrs = (m_use.group(2) or "").lower()
                m_intent = re.search(r"intent\s*\(\s*(in|out|inout)\s*\)", attrs, re.IGNORECASE)
                intent = m_intent.group(1).lower() if m_intent else None
                ents = m_use.group(3)
                is_external = "external" in attrs
                is_alloc = "allocatable" in attrs
                m_dim_attr = re.search(r"dimension\s*\(\s*([^)]+)\s*\)", attrs, re.IGNORECASE)
                dim_attr = m_dim_attr.group(1).strip() if m_dim_attr else None
            else:
                intent = m_use.group(2).lower() if m_use.group(2) else None
                ents = m_use.group(3)
                is_external = False
                is_alloc = False
                dim_attr = None
                attrs = ""
            kind_ct = _complex_ctype(real_type)
            if kind_tok:
                if kind_ctype_map and kind_tok in kind_ctype_map:
                    base_ct = kind_ctype_map[kind_tok]
                    kind_ct = _complex_ctype("double" if base_ct == "double" else "float")
                elif kind_tok.isdigit():
                    kind_ct = _complex_ctype("double" if int(kind_tok) >= 8 else "float")
            is_param = "parameter" in attrs if "attrs" in locals() else False
            is_save = "save" in attrs if "attrs" in locals() else False
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = _infer_array_dim_from_init(ma.group(2).strip(), init)
                    vars_map[nm.lower()] = Var(kind_ct, is_array=True, dim=dim, init=init, intent=intent, is_external=is_external, is_allocatable=is_alloc, is_param=is_param, is_save=is_save, optional=is_optional, comment=inline_comment)
                elif dim_attr:
                    vars_map[lhs.lower()] = Var(kind_ct, is_array=True, dim=_infer_array_dim_from_init(dim_attr, init), init=init, intent=intent, is_external=is_external, is_allocatable=is_alloc, is_param=is_param, is_save=is_save, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var(kind_ct, init=init, intent=intent, is_external=is_external, is_allocatable=is_alloc, is_param=is_param, is_save=is_save, optional=is_optional, comment=inline_comment)
            continue
        if m_complex_no_colon and "::" not in code_no_opt:
            kind_tok = (m_complex_no_colon.group(1) or "").strip().lower()
            intent = m_complex_no_colon.group(2).lower() if m_complex_no_colon.group(2) else None
            ents = m_complex_no_colon.group(3)
            kind_ct = _complex_ctype(real_type)
            if kind_tok:
                if kind_ctype_map and kind_tok in kind_ctype_map:
                    base_ct = kind_ctype_map[kind_tok]
                    kind_ct = _complex_ctype("double" if base_ct == "double" else "float")
                elif kind_tok.isdigit():
                    kind_ct = _complex_ctype("double" if int(kind_tok) >= 8 else "float")
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = ma.group(2).strip()
                    vars_map[nm.lower()] = Var(kind_ct, is_array=True, dim=dim, init=init, intent=intent, optional=is_optional, comment=inline_comment)
                else:
                    vars_map[lhs.lower()] = Var(kind_ct, init=init, intent=intent, optional=is_optional, comment=inline_comment)
            continue
        if m_char:
            m_char_len = re.match(r"^character\s*\(\s*len\s*=\s*(.+)\)\s*(?:,|::|\s|$)", code_no_opt, re.IGNORECASE)
            char_len = m_char_len.group(1).strip() if m_char_len else None
            intent = m_char.group(1).lower() if m_char.group(1) else None
            ents = m_char.group(2)
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = _infer_array_dim_from_init(ma.group(2).strip(), init)
                    vars_map[nm.lower()] = Var("char *", is_array=True, dim=dim, init=init, intent=intent, optional=is_optional, comment=inline_comment, char_len=char_len)
                else:
                    vars_map[lhs.lower()] = Var("char *", init=init, intent=intent, optional=is_optional, comment=inline_comment, char_len=char_len)
            continue
        if m_char_no_colon and "::" not in code_no_opt:
            m_char_len = re.match(r"^character\s*\(\s*len\s*=\s*(.+)\)\s*(?:,|::|\s|$)", code_no_opt, re.IGNORECASE)
            char_len = m_char_len.group(1).strip() if m_char_len else None
            intent = m_char_no_colon.group(1).lower() if m_char_no_colon.group(1) else None
            ents = m_char_no_colon.group(2)
            for ent in [x.strip() for x in _split_args_top_level(ents) if x.strip()]:
                if "=" in ent and "=>" not in ent:
                    lhs, init = [x.strip() for x in ent.split("=", 1)]
                else:
                    lhs, init = ent, None
                ma = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)$", lhs, re.IGNORECASE)
                if ma:
                    nm = ma.group(1)
                    dim = _infer_array_dim_from_init(ma.group(2).strip(), init)
                    vars_map[nm.lower()] = Var("char *", is_array=True, dim=dim, init=init, intent=intent, optional=is_optional, comment=inline_comment, char_len=char_len)
                else:
                    vars_map[lhs.lower()] = Var("char *", init=init, intent=intent, optional=is_optional, comment=inline_comment, char_len=char_len)
            continue
    return vars_map


def _emit_decl(
    nm: str,
    v: Var,
    vars_map: Dict[str, Var],
    real_type: str,
    for_main: bool,
    as_arg: bool = False,
    assumed_extents: Optional[Dict[str, List[str]]] = None,
) -> str:
    if as_arg:
        if v.is_external:
            return f"{v.ctype} (*{nm})(...)"
        if v.is_pointer and not v.is_array:
            return f"{v.ctype} *{nm}"
        if v.is_array:
            if v.is_allocatable or v.is_pointer:
                if (v.ctype or "").lower() == "char *":
                    return f"char ***{nm}"
                return f"{v.ctype} **{nm}"
            if (v.ctype or "").lower() == "char *":
                if v.intent == "in":
                    return f"char *const *{nm}"
                return f"char **{nm}"
            if v.intent == "in":
                return f"const {v.ctype} *{nm}"
            return f"{v.ctype} *{nm}"
        if v.optional:
            if v.intent == "in":
                return f"const {v.ctype} *{nm}"
            return f"{v.ctype} *{nm}"
        if v.intent in {"out", "inout"}:
            return f"{v.ctype} *{nm}"
        return f"const {v.ctype} {nm}"
    # In Fortran procedures, local variables with declaration-time initialization
    # have implicit SAVE semantics.
    implicit_save_init = (v.init is not None) and (not for_main)
    prefix = "static " if (v.is_save or implicit_save_init) else ""
    if v.is_pointer and not v.is_array:
        return f"{prefix}{v.ctype} *{nm} = NULL;"
    if v.is_array:
        const_prefix = "const " if v.is_param else ""
        if v.is_allocatable or v.is_pointer:
            if (v.ctype or "").lower() == "char *":
                return f"{prefix}char **{nm} = NULL;"
            return f"{prefix}{v.ctype} *{nm} = NULL;"
        if (v.ctype or '').lower() == 'char *' and v.char_len and not v.is_allocatable:
            clen = _simplify_int_expr_text(v.char_len)
            dim = _dim_product_expr(v.dim or "1", vars_map, real_type, assumed_extents=assumed_extents)
            dim_eval = _eval_int_expr(dim)
            if v.init is not None:
                m_ctor = re.match(r"^\[\s*(.*)\s*\]$", (v.init or '').strip())
                if m_ctor:
                    items = [x.strip() for x in _split_args_top_level(m_ctor.group(1)) if x.strip()]
                    if dim_eval == 0 or len(items) == 0:
                        return f"{prefix}char {nm}[1][({clen}) + 1] = {{ {{0}} }};"
                    citems = [_convert_expr(it, vars_map, real_type) for it in items]
                    return f"{prefix}char {nm}[{dim}][({clen}) + 1] = {{{', '.join(citems)}}};"
            if dim_eval == 0:
                return f"{prefix}char {nm}[1][({clen}) + 1] = {{ {{0}} }};"
            return f"{prefix}char {nm}[{dim}][({clen}) + 1];"
        if v.init is not None:
            cinit = _convert_array_initializer(v.init, vars_map, real_type)
            if (v.dim or "").strip() in {"", "*"}:
                return f"{prefix}{const_prefix}{v.ctype} {nm}[] = {cinit};"
            dim = _dim_product_expr(v.dim or "1", vars_map, real_type, assumed_extents=assumed_extents)
            dim_eval = _eval_int_expr(dim)
            if dim_eval == 0:
                return f"{prefix}{const_prefix}{v.ctype} {nm}[1] = {{0}};"
            return f"{prefix}{const_prefix}{v.ctype} {nm}[{dim}] = {cinit};"
        if for_main:
            if _main_fixed_array_uses_heap(v):
                return f"{prefix}{v.ctype} *{nm} = NULL;"
            dim = _dim_product_expr(v.dim or "1", vars_map, real_type, assumed_extents=assumed_extents)
            dim_eval = _eval_int_expr(dim)
            if dim_eval == 0:
                return f"{prefix}{v.ctype} {nm}[1] = {{0}};"
            return f"{prefix}{v.ctype} {nm}[{dim}];"
        dim = _dim_product_expr(v.dim or "1", vars_map, real_type, assumed_extents=assumed_extents)
        dim_eval = _eval_int_expr(dim)
        if dim_eval == 0:
            return f"{prefix}{const_prefix}{v.ctype} {nm}[1] = {{0}};"
        return f"{prefix}{const_prefix}{v.ctype} {nm}[{dim}];"
    if (v.ctype or '').lower() == 'char *' and (v.is_allocatable or v.is_pointer) and not v.is_array:
        return f"{prefix}char *{nm} = NULL;"
    if (v.ctype or '').lower() == 'char *' and v.char_len and not v.is_param and not as_arg:
        clen = _simplify_int_expr_text(v.char_len)
        cinit = _convert_expr(v.init or '""', vars_map, real_type)
        return f"{prefix}char {nm}[({clen}) + 1] = {cinit};"
    if v.is_param and (v.ctype or '').lower() == 'char *':
        cinit = _convert_expr(v.init or '""', vars_map, real_type)
        return f"{prefix}const char *{nm} = {cinit};"
    if v.is_param:
        raw_init = (v.init or "0").replace("_dp", "").replace("_DP", "")
        init = _convert_expr(v.init or "0", vars_map, real_type)
        if (v.ctype or "").lower() == "int":
            val = _eval_int_expr_with_params(raw_init, vars_map)
            if val is not None:
                return f"{prefix}enum {{ {nm} = {val} }};"
        return f"{prefix}const {v.ctype} {nm} = {init};"
    if v.is_external:
        return f"{prefix}{v.ctype} (*{nm})(...);"
        if v.init is not None:
            cinit = _convert_array_initializer(v.init, vars_map, real_type)
            if (v.dim or "").strip() in {"", "*"}:
                return f"{prefix}{const_prefix}{v.ctype} {nm}[] = {cinit};"
            dim = _dim_product_expr(v.dim or "1", vars_map, real_type)
            return f"{prefix}{const_prefix}{v.ctype} {nm}[{dim}] = {cinit};"
        if for_main:
            if v.is_allocatable:
                return f"{prefix}{v.ctype} *{nm} = NULL;"
            if (v.dim or "").strip() in {"", "*"}:
                return f"{prefix}{v.ctype} *{nm};"
            dim = _dim_product_expr(v.dim or "1", vars_map, real_type)
            dim_eval = _eval_int_expr(dim)
            if dim_eval == 0:
                return f"{prefix}{v.ctype} {nm}[1] = {{0}};"
            return f"{prefix}{v.ctype} {nm}[{dim}];"
        dim = _dim_product_expr(v.dim or "1", vars_map, real_type)
        dim_eval = _eval_int_expr(dim)
        if dim_eval == 0:
            return f"{prefix}{const_prefix}{v.ctype} {nm}[1] = {{0}};"
        return f"{prefix}{const_prefix}{v.ctype} {nm}[{dim}];"
        return f"{prefix}{v.ctype} {nm}[{dim}];"
    if v.init is not None:
        init = _convert_expr(v.init, vars_map, real_type)
        return f"{prefix}{v.ctype} {nm} = {init};"
    if (v.ctype or '').lower() in _ACTIVE_DERIVED_TYPES:
        return f"{prefix}{v.ctype} {nm} = {{0}};"
    return f"{prefix}{v.ctype} {nm};"


def _main_fixed_array_uses_heap(v: Var) -> bool:
    if (not v.is_array) or v.is_allocatable or v.is_pointer or v.init is not None:
        return False
    if (v.dim or "").strip() in {"", "*"}:
        return True
    if (v.ctype or "").lower() == "char *" and v.char_len:
        return False
    return True


def _arg_c_name(nm: str, v: Var) -> str:
    if v.is_array and (v.is_allocatable or v.is_pointer):
        return f"{nm}__arg"
    return nm


def _dummy_array_extent_names(proc_name: str, arg_name: str, rank: int) -> List[str]:
    base = f"__argext_{proc_name.lower()}_{arg_name.lower()}"
    if rank <= 1:
        return [base]
    return [f"{base}_{k}" for k in range(1, rank + 1)]


def _fold_zero_init_to_decl(lines: List[str], real_type: str) -> List[str]:
    """Fold `x = 0.0*;` immediately after declaration into `type x = 0.0*;`.

    Conservative:
    - declaration line exactly `<indent><float|double> name;`
    - next non-comment/non-blank statement is `name = 0.0...;`
    """
    out = list(lines)
    decl_re = re.compile(r"^(\s*)(float|double)\s+([a-z_]\w*)\s*;\s*$", re.IGNORECASE)
    zero_re = re.compile(r"^\s*([a-z_]\w*)\s*=\s*0(?:\.0+)?(?:[eE][+\-]?\d+)?(?:f)?\s*;\s*$", re.IGNORECASE)
    i = 0
    while i < len(out):
        m = decl_re.match(out[i])
        if not m:
            i += 1
            continue
        indent, cty, nm = m.group(1), m.group(2), m.group(3)
        j = i + 1
        while j < len(out):
            s = out[j].strip()
            if not s or s.startswith("/*") or s.startswith("//"):
                j += 1
                continue
            break
        if j >= len(out):
            i += 1
            continue
        z = zero_re.match(out[j])
        if not z or z.group(1).lower() != nm.lower():
            i += 1
            continue
        zero_lit = "0.0f" if cty.lower() == "float" else "0.0"
        out[i] = f"{indent}{cty} {nm} = {zero_lit};"
        out[j] = ""
        i = j + 1
    return [ln for ln in out if ln != ""]


def _compound_assign_style(lines: List[str]) -> List[str]:
    """Rewrite `x = x +/- expr;` into `x += expr;` / `x -= expr;`."""
    out: List[str] = []
    pat = re.compile(
        r"^(\s*)([a-z_]\w*(?:\[[^\]]+\])?)\s*=\s*\2\s*([+\-])\s*(.+?)\s*;\s*$",
        re.IGNORECASE,
    )
    for ln in lines:
        m = pat.match(ln)
        if not m:
            out.append(ln)
            continue
        indent, lhs, op, rhs = m.group(1), m.group(2), m.group(3), m.group(4)
        out.append(f"{indent}{lhs} {op}= {rhs};")
    return out


def _coalesce_adjacent_c_declarations(lines: List[str]) -> List[str]:
    """Coalesce adjacent simple declarations with same type and indent.

    Example:
      double a;
      double b;
    -> double a, b;
    """
    out: List[str] = []
    i = 0
    decl_re = re.compile(
        r"^(\s*)((?:const\s+)?(?:int|float|double))\s+([a-z_]\w*)\s*;\s*$",
        re.IGNORECASE,
    )
    ptr_decl_re = re.compile(
        r"^(\s*)((?:const\s+)?(?:int|float|double))\s*\*\s*([a-z_]\w*)\s*;\s*$",
        re.IGNORECASE,
    )
    init_decl_re = re.compile(
        r"^(\s*)((?:const\s+)?(?:int|float|double))\s+([a-z_]\w*)\s*=\s*(.+?)\s*;\s*$",
        re.IGNORECASE,
    )
    ptr_init_decl_re = re.compile(
        r"^(\s*)((?:const\s+)?(?:int|float|double))\s*\*\s*([a-z_]\w*)\s*=\s*(.+?)\s*;\s*$",
        re.IGNORECASE,
    )
    while i < len(lines):
        m = decl_re.match(lines[i])
        if not m:
            m_ptr = ptr_decl_re.match(lines[i])
            if m_ptr:
                indent = m_ptr.group(1)
                cty = m_ptr.group(2).strip()
                names = [m_ptr.group(3)]
                j = i + 1
                while j < len(lines):
                    mj = ptr_decl_re.match(lines[j])
                    if not mj:
                        break
                    if mj.group(1) != indent or mj.group(2).strip().lower() != cty.lower():
                        break
                    names.append(mj.group(3))
                    j += 1
                if len(names) == 1:
                    out.append(lines[i])
                else:
                    out.append(f"{indent}{cty} *{', *'.join(names)};")
                i = j
                continue

            m_init = init_decl_re.match(lines[i])
            if not m_init:
                m_ptr_init = ptr_init_decl_re.match(lines[i])
                if m_ptr_init:
                    indent = m_ptr_init.group(1)
                    cty = m_ptr_init.group(2).strip()
                    parts = [f"*{m_ptr_init.group(3)} = {m_ptr_init.group(4)}"]
                    j = i + 1
                    while j < len(lines):
                        mj = ptr_init_decl_re.match(lines[j])
                        if not mj:
                            break
                        if mj.group(1) != indent or mj.group(2).strip().lower() != cty.lower():
                            break
                        parts.append(f"*{mj.group(3)} = {mj.group(4)}")
                        j += 1
                    if len(parts) == 1:
                        out.append(lines[i])
                    else:
                        out.append(f"{indent}{cty} {', '.join(parts)};")
                    i = j
                    continue
                out.append(lines[i])
                i += 1
                continue
            indent = m_init.group(1)
            cty = m_init.group(2).strip()
            parts = [f"{m_init.group(3)} = {m_init.group(4)}"]
            j = i + 1
            while j < len(lines):
                mj = init_decl_re.match(lines[j])
                if not mj:
                    break
                if mj.group(1) != indent or mj.group(2).strip().lower() != cty.lower():
                    break
                parts.append(f"{mj.group(3)} = {mj.group(4)}")
                j += 1
            if len(parts) == 1:
                out.append(lines[i])
            else:
                out.append(f"{indent}{cty} {', '.join(parts)};")
            i = j
            continue
        indent = m.group(1)
        cty = m.group(2).strip()
        names = [m.group(3)]
        j = i + 1
        while j < len(lines):
            mj = decl_re.match(lines[j])
            if not mj:
                break
            if mj.group(1) != indent or mj.group(2).strip().lower() != cty.lower():
                break
            names.append(mj.group(3))
            j += 1
        if len(names) == 1:
            out.append(lines[i])
        else:
            out.append(f"{indent}{cty} {', '.join(names)};")
        i = j
    return out


def _collapse_one_line_blocks(lines: List[str]) -> List[str]:
    """Collapse simple braced `for`/`if` blocks with one statement to one-line form."""
    out = list(lines)
    i = 0
    while i < len(out):
        hdr = out[i]
        m = re.match(r"^(\s*)(for\s*\(.+\)|if\s*\(.+\))\s*\{\s*$", hdr)
        if not m:
            i += 1
            continue
        indent = m.group(1)
        header = m.group(2)
        j = i + 1
        while j < len(out) and not out[j].strip():
            j += 1
        if j >= len(out):
            i += 1
            continue
        body = out[j]
        body_strip = body.strip()
        if body_strip.startswith("/*") or body_strip.startswith("//"):
            i += 1
            continue
        if body_strip.endswith("{") or body_strip == "}":
            i += 1
            continue
        if not body_strip.endswith(";"):
            i += 1
            continue
        k = j + 1
        while k < len(out) and not out[k].strip():
            k += 1
        if k >= len(out) or out[k].strip() != "}":
            i += 1
            continue
        # Preserve body text as-is (trim leading/trailing spaces only).
        out[i] = f"{indent}{header} {body_strip}"
        out[j] = ""
        out[k] = ""
        i = k + 1
    return [ln for ln in out if ln != ""]


def _rewrite_zero_based_loop_style(lines: List[str]) -> List[str]:
    """Rewrite safe C loop/index patterns to cleaner 0-based style.

    Patterns (safe, conservative):
    - for (i = 1; i <= n; ++i) {
      ...
      x[i - 1]
      ...
      }
    becomes
    - for (i = 0; i < n; ++i) {
      ...
      x[i]
      ...
      }

    - for (i = 2; i <= n; ++i) {
      ...
      x[i - 1]
      ...
      }
    becomes
    - for (i = 1; i < n; ++i) {
      ...
      x[i]
      ...
      }

    Only applied when the loop body uses loop variable `i` exclusively as `i - 1`.
    """
    out = list(lines)
    i = 0
    while i < len(out):
        m1 = re.match(
            r"^(\s*)for\s*\(\s*((?:int\s+)?)\s*([a-z_]\w*)\s*=\s*1\s*;\s*\3\s*<=\s*([a-z_]\w*|\d+)\s*;\s*\+\+\3\s*\)\s*\{\s*$",
            out[i],
            re.IGNORECASE,
        )
        m2 = re.match(
            r"^(\s*)for\s*\(\s*((?:int\s+)?)\s*([a-z_]\w*)\s*=\s*2\s*;\s*\3\s*<=\s*([a-z_]\w*|\d+)\s*;\s*\+\+\3\s*\)\s*\{\s*$",
            out[i],
            re.IGNORECASE,
        )
        if not m1 and not m2:
            i += 1
            continue
        m = m1 if m1 else m2
        assert m is not None
        indent = m.group(1)
        int_kw = m.group(2) or ""
        ivar = m.group(3)
        hi = m.group(4)
        start_val = 1 if m1 else 2
        end = i + 1
        while end < len(out):
            if re.match(rf"^{re.escape(indent)}}}\s*$", out[end]):
                break
            end += 1
        if end >= len(out):
            i += 1
            continue

        body = out[i + 1 : end]
        body_txt = "\n".join(body)
        if not re.search(rf"\[\s*{re.escape(ivar)}\s*-\s*1\s*\]", body_txt):
            i = end + 1
            continue
        # If loop var appears in body in any way other than `i - 1`, skip rewrite.
        raw_uses = re.findall(rf"\b{re.escape(ivar)}\b", body_txt)
        minus_ones = re.findall(rf"\b{re.escape(ivar)}\s*-\s*1\b", body_txt)
        if len(raw_uses) != len(minus_ones):
            i = end + 1
            continue

        if start_val == 1:
            out[i] = f"{indent}for ({int_kw}{ivar} = 0; {ivar} < {hi}; ++{ivar}) {{"
        else:
            out[i] = f"{indent}for ({int_kw}{ivar} = 1; {ivar} < {hi}; ++{ivar}) {{"
        for k in range(i + 1, end):
            out[k] = re.sub(
                rf"\[\s*{re.escape(ivar)}\s*-\s*1\s*\]",
                f"[{ivar}]",
                out[k],
            )
        i = end + 1
    return out


def _use_block_scoped_loop_indices(lines: List[str]) -> List[str]:
    """Prefer `for (int i = ...)` when loop index is loop-local.

    Conservative rules per index variable:
    - declaration line exists exactly as `int <name>;`
    - all uses of `<name>` are inside loops headed by `for (<name> = ... )`
    """
    out = list(lines)
    decl_re = re.compile(r"^(\s*)int\s+([a-z_]\w*)\s*;\s*$", re.IGNORECASE)

    decls: Dict[str, int] = {}
    for idx, ln in enumerate(out):
        m = decl_re.match(ln)
        if m:
            decls[m.group(2)] = idx

    if not decls:
        return out

    for var, decl_idx in list(decls.items()):
        header_re = re.compile(rf"^\s*for\s*\(\s*{re.escape(var)}\s*=", re.IGNORECASE)
        token_re = re.compile(rf"\b{re.escape(var)}\b", re.IGNORECASE)
        loop_ranges: List[tuple[int, int]] = []
        i = 0
        while i < len(out):
            code = out[i].split("//", 1)[0]
            if not header_re.match(code):
                i += 1
                continue
            # Find loop end by brace depth.
            depth = code.count("{") - code.count("}")
            j = i + 1
            while j < len(out):
                c = out[j].split("//", 1)[0]
                depth += c.count("{") - c.count("}")
                if depth <= 0:
                    break
                j += 1
            if j >= len(out):
                break
            loop_ranges.append((i, j))
            i = j + 1
        if not loop_ranges:
            continue

        uses: List[int] = []
        outside_use = False
        for i, ln in enumerate(out):
            if i == decl_idx:
                continue
            # Strip line comments.
            code = ln.split("//", 1)[0]
            if not code.strip():
                continue
            if token_re.search(code) is None:
                continue
            uses.append(i)
            in_any = any(a <= i <= b for a, b in loop_ranges)
            if not in_any:
                outside_use = True
                break
        if outside_use or not uses:
            continue
        # Rewrite loop headers.
        for a, _b in loop_ranges:
            out[a] = re.sub(
                rf"^(\s*)for\s*\(\s*{re.escape(var)}\s*=",
                rf"\1for (int {var} =",
                out[a],
            )
        # Drop standalone declaration.
        out[decl_idx] = ""

    return [ln for ln in out if ln != ""]


def _inline_simple_int_aliases(lines: List[str]) -> List[str]:
    """Inline simple aliases like `int n; n = n_x;` within one emitted unit."""
    out = list(lines)
    decl_re = re.compile(r"^\s*int\s+([a-z_]\w*)\s*;\s*$", re.IGNORECASE)
    asn_re = re.compile(r"^\s*([a-z_]\w*)\s*=\s*([a-z_]\w*)\s*;\s*$", re.IGNORECASE)

    decl_idx: Dict[str, int] = {}
    for i, ln in enumerate(out):
        m = decl_re.match(ln)
        if m:
            decl_idx[m.group(1)] = i

    remove_idx: Set[int] = set()
    for i, ln in enumerate(out):
        m = asn_re.match(ln)
        if not m:
            continue
        lhs = m.group(1)
        rhs = m.group(2)
        if lhs == rhs:
            continue
        di = decl_idx.get(lhs)
        if di is None or di > i:
            continue
        # Reject if LHS is assigned elsewhere.
        reassigned = False
        for j, lj in enumerate(out):
            if j == i:
                continue
            m2 = re.match(rf"^\s*{re.escape(lhs)}\s*=", lj)
            if m2:
                reassigned = True
                break
        if reassigned:
            continue
        # Replace remaining uses.
        pat = re.compile(rf"\b{re.escape(lhs)}\b")
        for j in range(i + 1, len(out)):
            out[j] = pat.sub(rhs, out[j])
        remove_idx.add(di)
        remove_idx.add(i)

    if not remove_idx:
        return out
    return [ln for idx, ln in enumerate(out) if idx not in remove_idx]


def _prefer_simple_n_extent_name(lines: List[str], assumed_extents: Dict[str, List[str]]) -> List[str]:
    """Rename one generated rank-1 extent name to `n` when unambiguous."""
    exts = [e for vals in assumed_extents.values() for e in vals]
    if len(exts) != 1:
        return lines
    old = exts[0]
    if old == "n":
        return lines
    # Only rename when no standalone `n` symbol exists already.
    n_tok = re.compile(r"\bn\b")
    old_tok = re.compile(rf"\b{re.escape(old)}\b")
    if any(n_tok.search(ln) for ln in lines):
        return lines
    return [old_tok.sub("n", ln) for ln in lines]


def _drop_redundant_outer_parens(expr: str) -> str:
    s = expr.strip()
    if len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        ok = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    ok = False
                    break
        if ok:
            return s[1:-1].strip()
    return s


def _inject_runtime_helpers(lines: List[str]) -> List[str]:
    text = "\n".join(lines)
    need_sum_1d_float = "sum_1d_float(" in text
    need_sum_2d_float = "sum_2d_float(" in text
    need_sum_1d_double = "sum_1d_double(" in text
    need_sum_2d_double = "sum_2d_double(" in text
    need_sum_1d_int = "sum_1d_int(" in text
    need_sum_2d_int = "sum_2d_int(" in text
    need_product_1d_float = "product_1d_float(" in text
    need_product_2d_float = "product_2d_float(" in text
    need_product_1d_double = "product_1d_double(" in text
    need_product_2d_double = "product_2d_double(" in text
    need_fill_rand_1d_float = "fill_rand_1d_float(" in text
    need_fill_rand_2d_float = "fill_rand_2d_float(" in text
    need_fill_rand_3d_float = "fill_rand_3d_float(" in text
    need_fill_rand_1d_double = "fill_rand_1d_double(" in text
    need_fill_rand_2d_double = "fill_rand_2d_double(" in text
    need_fill_rand_3d_double = "fill_rand_3d_double(" in text
    need_minval_1d_float = "minval_1d_float(" in text
    need_minval_1d_double = "minval_1d_double(" in text
    need_minval_1d_int = "minval_1d_int(" in text
    need_maxval_1d_float = "maxval_1d_float(" in text
    need_maxval_1d_double = "maxval_1d_double(" in text
    need_maxval_1d_int = "maxval_1d_int(" in text
    need_shared_runtime = (
        ("len_trim_s(" in text)
        or ("trim_s(" in text)
        or ("adjustl_s(" in text)
        or ("adjustr_s(" in text)
        or ("concat_s2(" in text)
        or ("repeat_s(" in text)
        or ("substr_s(" in text)
        or ("index_s(" in text)
        or ("scan_s(" in text)
        or ("verify_s(" in text)
        or ("achar_s(" in text)
        or ("iachar_s(" in text)
        or ("assign_str(" in text)
        or ("assign_str_alloc(" in text)
        or ("assign_substr(" in text)
        or ("free_str_array(" in text)
        or ("open_unit(" in text)
        or ("close_unit(" in text)
        or ("write_a(" in text)
        or ("read_a(" in text)
        or ("fill_rand_1d_float(" in text)
        or ("fill_rand_1d_double(" in text)
        or ("rng_seed(" in text)
        or ("runif(" in text)
        or ("fill_runif_1d(" in text)
        or ("fill_runif_2d(" in text)
        or ("sum_1d_float(" in text)
        or ("sum_1d_double(" in text)
        or ("sum_1d_int(" in text)
        or ("product_1d_float(" in text)
        or ("product_1d_double(" in text)
        or ("minval_1d_float(" in text)
        or ("minval_1d_double(" in text)
        or ("minval_1d_int(" in text)
        or ("maxval_1d_float(" in text)
        or ("maxval_1d_double(" in text)
        or ("maxval_1d_int(" in text)
        or ("count_1d_int(" in text)
        or ("any_1d_int(" in text)
        or ("all_1d_int(" in text)
        or ("dot_product_1d_float(" in text)
        or ("dot_product_1d_double(" in text)
        or ("dot_product_1d_int(" in text)
    )
    need_len_trim = "xf_len_trim(" in text
    need_trim = "xf_trim(" in text
    need_adjustl = "xf_adjustl(" in text
    need_adjustr = "xf_adjustr(" in text
    need_repeat = "xf_repeat(" in text
    need_substr = "xf_substr(" in text
    need_index = "xf_index(" in text
    need_scan = "xf_scan(" in text
    need_verify = "xf_verify(" in text
    need_achar = "xf_achar(" in text
    need_iachar = "xf_iachar(" in text
    need_assign_str = "xf_assign_str(" in text
    need_assign_substr = "xf_assign_substr(" in text
    need_tmp_str_buf = need_trim or need_adjustl or need_adjustr or need_repeat or need_substr or need_achar
    need_file_units = ("xf_open_unit(" in text) or ("xf_close_unit(" in text) or ("xf_write_a(" in text) or ("xf_read_a(" in text)
    need_count_1d_int = "count_1d_int(" in text
    need_count_2d_int = "count_2d_int(" in text
    need_any_1d_int = "any_1d_int(" in text
    need_any_2d_int = "any_2d_int(" in text
    need_all_1d_int = "all_1d_int(" in text
    need_all_2d_int = "all_2d_int(" in text
    need_dot_product_1d_float = "dot_product_1d_float(" in text
    need_dot_product_2d_float = "dot_product_2d_float(" in text
    need_dot_product_1d_double = "dot_product_1d_double(" in text
    need_dot_product_2d_double = "dot_product_2d_double(" in text
    need_dot_product_1d_int = "dot_product_1d_int(" in text
    need_dot_product_2d_int = "dot_product_2d_int(" in text
    need_runtime_1d_helpers = (
        need_sum_1d_float
        or need_sum_1d_double
        or need_sum_1d_int
        or need_product_1d_float
        or need_product_1d_double
        or need_minval_1d_float
        or need_minval_1d_double
        or need_minval_1d_int
        or need_maxval_1d_float
        or need_maxval_1d_double
        or need_maxval_1d_int
        or need_count_1d_int
        or need_any_1d_int
        or need_all_1d_int
        or need_dot_product_1d_float
        or need_dot_product_1d_double
        or need_dot_product_1d_int
    )
    if not (
        need_sum_1d_float
        or need_sum_2d_float
        or need_sum_1d_double
        or need_sum_2d_double
        or need_sum_1d_int
        or need_sum_2d_int
        or need_product_1d_float
        or need_product_2d_float
        or need_product_1d_double
        or need_product_2d_double
        or need_fill_rand_1d_float
        or need_fill_rand_2d_float
        or need_fill_rand_3d_float
        or need_fill_rand_1d_double
        or need_fill_rand_2d_double
        or need_fill_rand_3d_double
        or ("rng_seed(" in text)
        or ("runif(" in text)
        or ("fill_runif_1d(" in text)
        or ("fill_runif_2d(" in text)
        or need_minval_1d_float
        or need_minval_1d_double
        or need_minval_1d_int
        or need_maxval_1d_float
        or need_maxval_1d_double
        or need_maxval_1d_int
        or need_len_trim
        or need_trim
        or need_adjustl
        or need_adjustr
        or need_repeat
        or need_substr
        or need_index
        or need_scan
        or need_verify
        or need_achar
        or need_iachar
        or need_assign_str
        or need_assign_substr
        or need_file_units
        or need_count_1d_int
        or need_count_2d_int
        or need_any_1d_int
        or need_any_2d_int
        or need_all_1d_int
        or need_all_2d_int
        or need_dot_product_1d_float
        or need_dot_product_2d_float
        or need_dot_product_1d_double
        or need_dot_product_2d_double
        or need_dot_product_1d_int
        or need_dot_product_2d_int
        or need_shared_runtime
        or need_runtime_1d_helpers
    ):
        return lines

    helpers: List[str] = []
    if need_sum_1d_float and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static float sum_1d_float(const int n, const float *x) {",
                "   float s = 0.0f;",
                "   for (int i = 0; i < n; ++i) s += x[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_sum_2d_float:
        helpers.extend(
            [
                "static float sum_2d_float(const int n1, const int n2, const float *x) {",
                "   float s = 0.0f;",
                "   for (int i = 0; i < n1 * n2; ++i) s += x[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_sum_1d_double and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static double sum_1d_double(const int n, const double *x) {",
                "   double s = 0.0;",
                "   for (int i = 0; i < n; ++i) s += x[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_sum_2d_double:
        helpers.extend(
            [
                "static double sum_2d_double(const int n1, const int n2, const double *x) {",
                "   double s = 0.0;",
                "   for (int i = 0; i < n1 * n2; ++i) s += x[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_sum_1d_int and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static int sum_1d_int(const int n, const int *x) {",
                "   int s = 0;",
                "   for (int i = 0; i < n; ++i) s += x[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_sum_2d_int:
        helpers.extend(
            [
                "static int sum_2d_int(const int n1, const int n2, const int *x) {",
                "   int s = 0;",
                "   for (int i = 0; i < n1 * n2; ++i) s += x[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_product_1d_float and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static float product_1d_float(const int n, const float *x) {",
                "   float p = 1.0f;",
                "   for (int i = 0; i < n; ++i) p *= x[i];",
                "   return p;",
                "}",
                "",
            ]
        )
    if need_product_2d_float:
        helpers.extend(
            [
                "static float product_2d_float(const int n1, const int n2, const float *x) {",
                "   float p = 1.0f;",
                "   for (int i = 0; i < n1 * n2; ++i) p *= x[i];",
                "   return p;",
                "}",
                "",
            ]
        )
    if need_product_1d_double and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static double product_1d_double(const int n, const double *x) {",
                "   double p = 1.0;",
                "   for (int i = 0; i < n; ++i) p *= x[i];",
                "   return p;",
                "}",
                "",
            ]
        )
    if need_product_2d_double:
        helpers.extend(
            [
                "static double product_2d_double(const int n1, const int n2, const double *x) {",
                "   double p = 1.0;",
                "   for (int i = 0; i < n1 * n2; ++i) p *= x[i];",
                "   return p;",
                "}",
                "",
            ]
        )
    if need_fill_rand_1d_float and not need_shared_runtime:
        helpers.extend(
            [
                "static void fill_rand_1d_float(const int n, float *x) {",
                "   for (int i = 0; i < n; ++i) x[i] = (float)rand() / (float)RAND_MAX;",
                "}",
                "",
            ]
        )
    if need_fill_rand_2d_float:
        helpers.extend(
            [
                "static void fill_rand_2d_float(const int n1, const int n2, float *x) {",
                "   for (int i = 0; i < n1 * n2; ++i) x[i] = (float)rand() / (float)RAND_MAX;",
                "}",
                "",
            ]
        )
    if need_fill_rand_3d_float:
        helpers.extend(
            [
                "static void fill_rand_3d_float(const int n1, const int n2, const int n3, float *x) {",
                "   for (int i = 0; i < n1 * n2 * n3; ++i) x[i] = (float)rand() / (float)RAND_MAX;",
                "}",
                "",
            ]
        )
    if need_fill_rand_1d_double and not need_shared_runtime:
        helpers.extend(
            [
                "static void fill_rand_1d_double(const int n, double *x) {",
                "   for (int i = 0; i < n; ++i) x[i] = (double)rand() / (double)RAND_MAX;",
                "}",
                "",
            ]
        )
    if need_fill_rand_2d_double:
        helpers.extend(
            [
                "static void fill_rand_2d_double(const int n1, const int n2, double *x) {",
                "   for (int i = 0; i < n1 * n2; ++i) x[i] = (double)rand() / (double)RAND_MAX;",
                "}",
                "",
            ]
        )
    if need_fill_rand_3d_double:
        helpers.extend(
            [
                "static void fill_rand_3d_double(const int n1, const int n2, const int n3, double *x) {",
                "   for (int i = 0; i < n1 * n2 * n3; ++i) x[i] = (double)rand() / (double)RAND_MAX;",
                "}",
                "",
            ]
        )
    if need_minval_1d_float and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static float minval_1d_float(const int n, const float *x) {",
                "   if (n <= 0) return 0.0f;",
                "   float m = x[0];",
                "   for (int i = 1; i < n; ++i) if (x[i] < m) m = x[i];",
                "   return m;",
                "}",
                "",
            ]
        )
    if need_minval_1d_double and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static double minval_1d_double(const int n, const double *x) {",
                "   if (n <= 0) return 0.0;",
                "   double m = x[0];",
                "   for (int i = 1; i < n; ++i) if (x[i] < m) m = x[i];",
                "   return m;",
                "}",
                "",
            ]
        )
    if need_minval_1d_int and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static int minval_1d_int(const int n, const int *x) {",
                "   if (n <= 0) return 0;",
                "   int m = x[0];",
                "   for (int i = 1; i < n; ++i) if (x[i] < m) m = x[i];",
                "   return m;",
                "}",
                "",
            ]
        )
    if need_maxval_1d_float and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static float maxval_1d_float(const int n, const float *x) {",
                "   if (n <= 0) return 0.0f;",
                "   float m = x[0];",
                "   for (int i = 1; i < n; ++i) if (x[i] > m) m = x[i];",
                "   return m;",
                "}",
                "",
            ]
        )
    if need_maxval_1d_double and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static double maxval_1d_double(const int n, const double *x) {",
                "   if (n <= 0) return 0.0;",
                "   double m = x[0];",
                "   for (int i = 1; i < n; ++i) if (x[i] > m) m = x[i];",
                "   return m;",
                "}",
                "",
            ]
        )
    if need_maxval_1d_int and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static int maxval_1d_int(const int n, const int *x) {",
                "   if (n <= 0) return 0;",
                "   int m = x[0];",
                "   for (int i = 1; i < n; ++i) if (x[i] > m) m = x[i];",
                "   return m;",
                "}",
                "",
            ]
        )
    if need_len_trim:
        helpers.extend(
            [
                "static int xf_len_trim(const char *s) {",
                "   int n = (int) strlen(s);",
                "   while (n > 0 && s[n - 1] == ' ') --n;",
                "   return n;",
                "}",
                "",
            ]
        )
    if need_tmp_str_buf:
        helpers.extend(
            [
                "static char *xf_tmp_str_buf(size_t need) {",
                "   static char *buf[8] = {0};",
                "   static size_t cap[8] = {0};",
                "   static int slot = 0;",
                "   int use = slot;",
                "   char *out;",
                "   slot = (slot + 1) % 8;",
                "   if (need + 1u > cap[use]) {",
                "      char *tmp = (char *) realloc(buf[use], need + 1u);",
                '      if (!tmp) { fprintf(stderr, "xf_tmp_str_buf: out of memory\\n"); exit(1); }',
                "      buf[use] = tmp;",
                "      cap[use] = need + 1u;",
                "   }",
                "   out = buf[use];",
                "   out[0] = '\\0';",
                "   return out;",
                "}",
                "",
            ]
        )
    if need_trim:
        helpers.extend(
            [
                "static const char *xf_trim(const char *s) {",
                "   if (!s) return xf_tmp_str_buf(0);",
                "   int n = xf_len_trim(s);",
                "   char *out = xf_tmp_str_buf((size_t) n);",
                "   memcpy(out, s, (size_t) n);",
                "   out[n] = '\\0';",
                "   return out;",
                "}",
                "",
            ]
        )
    if need_adjustl:
        helpers.extend(
            [
                "static const char *xf_adjustl(const char *s) {",
                "   if (!s) return xf_tmp_str_buf(0);",
                "   int n = (int) strlen(s);",
                "   char *out = xf_tmp_str_buf((size_t) n);",
                "   int i = 0;",
                "   while (i < n && s[i] == ' ') ++i;",
                "   int m = n - i;",
                "   if (m > 0) memcpy(out, s + i, (size_t) m);",
                "   for (int k = m; k < n; ++k) out[k] = ' ';",
                "   out[n] = '\\0';",
                "   return out;",
                "}",
                "",
            ]
        )
    if need_adjustr:
        helpers.extend(
            [
                "static const char *xf_adjustr(const char *s) {",
                "   if (!s) return xf_tmp_str_buf(0);",
                "   int n = (int) strlen(s);",
                "   int m = xf_len_trim(s);",
                "   char *out = xf_tmp_str_buf((size_t) n);",
                "   if (m > n) m = n;",
                "   for (int k = 0; k < n - m; ++k) out[k] = ' ';",
                "   if (m > 0) memcpy(out + (n - m), s, (size_t) m);",
                "   out[n] = '\\0';",
                "   return out;",
                "}",
                "",
            ]
        )
    if need_repeat:
        helpers.extend(
            [
                "static const char *xf_repeat(const char *s, int ncopy) {",
                "   if (!s || ncopy <= 0) return xf_tmp_str_buf(0);",
                "   size_t used = 0;",
                "   size_t m = strlen(s);",
                "   size_t copies = (size_t) ncopy;",
                "   size_t need = (m > 0u && copies > ((((size_t)-1) - 1u) / m)) ? (((size_t)-1) - 1u) : (m * copies);",
                "   char *out = xf_tmp_str_buf(need);",
                "   for (int i = 0; i < ncopy; ++i) {",
                "      if (m > 0u) memcpy(out + used, s, m);",
                "      used += m;",
                "   }",
                "   out[used] = '\\0';",
                "   return out;",
                "}",
                "",
            ]
        )
    if need_substr:
        helpers.extend(
            [
                "static const char *xf_substr(const char *s, int lo, int hi) {",
                "   if (!s) return xf_tmp_str_buf(0);",
                "   int n = (int) strlen(s);",
                "   if (lo < 1) lo = 1;",
                "   if (hi > n) hi = n;",
                "   if (hi < lo) return xf_tmp_str_buf(0);",
                "   int m = hi - lo + 1;",
                "   char *out = xf_tmp_str_buf((size_t) m);",
                "   memcpy(out, s + (lo - 1), (size_t) m);",
                "   out[m] = '\\0';",
                "   return out;",
                "}",
                "",
            ]
        )
    if need_file_units:
        helpers.extend(
            [
                "static FILE *xf_unit_files[1000] = {0};",
                "static FILE *xf_unit_get(int unit) {",
                "   if (unit >= 0 && unit < 1000) return xf_unit_files[unit];",
                "   return NULL;",
                "}",
                "static int xf_open_unit(int unit, const char *file, const char *action, const char *status) {",
                '   const char *mode = "r";',
                '   if (action && strcmp(action, "write") == 0) mode = "w";',
                '   else if (action && strcmp(action, "read") == 0) mode = "r";',
                '   else if (status && strcmp(status, "replace") == 0) mode = "w";',
                "   FILE *fp = fopen(file, mode);",
                "   if (!fp) return 1;",
                "   if (unit >= 0 && unit < 1000) xf_unit_files[unit] = fp;",
                "   return 0;",
                "}",
                "static int xf_close_unit(int unit) {",
                "   FILE *fp = xf_unit_get(unit);",
                "   if (!fp) return 1;",
                "   fclose(fp);",
                "   if (unit >= 0 && unit < 1000) xf_unit_files[unit] = NULL;",
                "   return 0;",
                "}",
                "static void xf_write_a(int unit, const char *s) {",
                "   FILE *fp = xf_unit_get(unit);",
                "   if (!fp) return;",
                '   fprintf(fp, "%s\\n", s ? s : "");',
                "}",
                "static int xf_read_a(int unit, char *buf, int len) {",
                "   FILE *fp = xf_unit_get(unit);",
                "   if (!fp || !buf || len < 0) return 1;",
                "   for (int i = 0; i < len; ++i) buf[i] = ' ';",
                "   buf[len] = '\\0';",
                "   if (!fgets(buf, len + 1, fp)) return 1;",
                "   int n = (int) strlen(buf);",
                '   while (n > 0 && (buf[n - 1] == \'\\n\' || buf[n - 1] == \'\\r\')) buf[--n] = \'\\0\';',
                "   for (int i = n; i < len; ++i) buf[i] = ' ';",
                "   buf[len] = '\\0';",
                "   return 0;",
                "}",
                "",
            ]
        )
    if need_index:
        helpers.extend(
            [
                "static int xf_index(const char *s, const char *sub) {",
                "   const char *p = strstr(s, sub);",
                "   return p ? (int) (p - s) + 1 : 0;",
                "}",
                "",
            ]
        )
    if need_assign_str:
        helpers.extend(
            [
                "static void xf_assign_str(char *dst, int len, const char *src) {",
                "   if (!dst || len < 0) return;",
                "   const char *src_use = src;",
                "   char *tmp = NULL;",
                "   int n = 0;",
                "   if (src_use) {",
                "      n = (int) strlen(src_use);",
                "      if (n > len) n = len;",
                "      if (src_use >= dst && src_use <= dst + len) {",
                "         tmp = (char *) malloc((size_t) n + 1u);",
                "         if (tmp) {",
                "            if (n > 0) memcpy(tmp, src_use, (size_t) n);",
                "            tmp[n] = '\\0';",
                "            src_use = tmp;",
                "         }",
                "      }",
                "   }",
                "   for (int i = 0; i < len; ++i) dst[i] = ' ';",
                "   if (src_use) {",
                "      if (n > 0) memcpy(dst, src_use, (size_t) n);",
                "   }",
                "   dst[len] = '\\0';",
                "   if (tmp) free(tmp);",
                "}",
                "",
            ]
        )
    if need_assign_substr:
        helpers.extend(
            [
                "static void xf_assign_substr(char *dst, int len, int lo, int hi, const char *src) {",
                "   if (!dst || len < 0) return;",
                "   if (lo < 1) lo = 1;",
                "   if (hi > len) hi = len;",
                "   if (hi < lo) return;",
                "   int span = hi - lo + 1;",
                "   int n = src ? (int) strlen(src) : 0;",
                "   if (n > span) n = span;",
                "   if (n > 0) memmove(dst + (lo - 1), src, (size_t) n);",
                "   for (int i = lo - 1 + n; i <= hi - 1; ++i) dst[i] = ' ';",
                "   dst[len] = '\\0';",
                "}",
                "",
            ]
        )
    if need_scan:
        helpers.extend(
            [
                "static int xf_scan(const char *s, const char *set) {",
                "   if (!s || !set) return 0;",
                "   for (int i = 0; s[i] != '\\0'; ++i) if (strchr(set, s[i])) return i + 1;",
                "   return 0;",
                "}",
                "",
            ]
        )
    if need_verify:
        helpers.extend(
            [
                "static int xf_verify(const char *s, const char *set) {",
                "   if (!s || !set) return 0;",
                "   for (int i = 0; s[i] != '\\0'; ++i) if (!strchr(set, s[i])) return i + 1;",
                "   return 0;",
                "}",
                "",
            ]
        )
    if need_achar:
        helpers.extend(
            [
                "static const char *xf_achar(int code) {",
                "   char *out = xf_tmp_str_buf(1u);",
                "   out[0] = (char) (unsigned char) code;",
                "   out[1] = '\\0';",
                "   return out;",
                "}",
                "",
            ]
        )
    if need_iachar:
        helpers.extend(
            [
                "static int xf_iachar(const char *s) {",
                "   return (s && s[0] != '\\0') ? (int) ((unsigned char) s[0]) : 0;",
                "}",
                "",
            ]
        )
    if need_count_1d_int and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static int count_1d_int(const int n, const int *x) {",
                "   int c = 0;",
                "   for (int i = 0; i < n; ++i) if (x[i]) ++c;",
                "   return c;",
                "}",
                "",
            ]
        )
    if need_count_2d_int:
        helpers.extend(
            [
                "static int count_2d_int(const int n1, const int n2, const int *x) {",
                "   int c = 0;",
                "   for (int i = 0; i < n1 * n2; ++i) if (x[i]) ++c;",
                "   return c;",
                "}",
                "",
            ]
        )
    if need_any_1d_int and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static int any_1d_int(const int n, const int *x) {",
                "   for (int i = 0; i < n; ++i) if (x[i]) return 1;",
                "   return 0;",
                "}",
                "",
            ]
        )
    if need_any_2d_int:
        helpers.extend(
            [
                "static int any_2d_int(const int n1, const int n2, const int *x) {",
                "   for (int i = 0; i < n1 * n2; ++i) if (x[i]) return 1;",
                "   return 0;",
                "}",
                "",
            ]
        )
    if need_all_1d_int and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static int all_1d_int(const int n, const int *x) {",
                "   for (int i = 0; i < n; ++i) if (!x[i]) return 0;",
                "   return 1;",
                "}",
                "",
            ]
        )
    if need_all_2d_int:
        helpers.extend(
            [
                "static int all_2d_int(const int n1, const int n2, const int *x) {",
                "   for (int i = 0; i < n1 * n2; ++i) if (!x[i]) return 0;",
                "   return 1;",
                "}",
                "",
            ]
        )
    if need_dot_product_1d_float and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static float dot_product_1d_float(const int n, const float *x, const float *y) {",
                "   float s = 0.0f;",
                "   for (int i = 0; i < n; ++i) s += x[i] * y[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_dot_product_2d_float:
        helpers.extend(
            [
                "static float dot_product_2d_float(const int n1, const int n2, const float *x, const float *y) {",
                "   float s = 0.0f;",
                "   for (int i = 0; i < n1 * n2; ++i) s += x[i] * y[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_dot_product_1d_double and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static double dot_product_1d_double(const int n, const double *x, const double *y) {",
                "   double s = 0.0;",
                "   for (int i = 0; i < n; ++i) s += x[i] * y[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_dot_product_2d_double:
        helpers.extend(
            [
                "static double dot_product_2d_double(const int n1, const int n2, const double *x, const double *y) {",
                "   double s = 0.0;",
                "   for (int i = 0; i < n1 * n2; ++i) s += x[i] * y[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_dot_product_1d_int and not need_runtime_1d_helpers:
        helpers.extend(
            [
                "static int dot_product_1d_int(const int n, const int *x, const int *y) {",
                "   int s = 0;",
                "   for (int i = 0; i < n; ++i) s += x[i] * y[i];",
                "   return s;",
                "}",
                "",
            ]
        )
    if need_dot_product_2d_int:
        helpers.extend(
            [
                "static int dot_product_2d_int(const int n1, const int n2, const int *x, const int *y) {",
                "   int s = 0;",
                "   for (int i = 0; i < n1 * n2; ++i) s += x[i] * y[i];",
                "   return s;",
                "}",
                "",
            ]
        )

    insert_at = 0
    while insert_at < len(lines) and lines[insert_at].startswith("#include"):
        insert_at += 1
    if need_shared_runtime:
        helpers = ['#include "fortran_runtime.h"', ""] + helpers
    if insert_at < len(lines) and lines[insert_at].strip() == "":
        insert_at += 1
    return lines[:insert_at] + helpers + lines[insert_at:]


def _transpile_unit(
    unit: Dict[str, object],
    real_type: str,
    kind_ctype_map: Dict[str, str],
    proc_arg_modes: Dict[str, List[str]],
    proc_arg_optional: Dict[str, List[bool]],
    proc_arg_ctypes: Dict[str, List[str]],
    proc_arg_is_array: Dict[str, List[bool]],
    proc_arg_array_byref: Dict[str, List[bool]],
    proc_arg_assumed_ranks: Dict[str, List[int]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
    proc_arg_names: Dict[str, List[str]],
    array_result_funcs: set[str],
    vars_map_override: Optional[Dict[str, Var]] = None,
    *,
    one_line: bool = False,
    annotate: bool = False,
) -> List[str]:
    out: List[str] = []
    local_derived_types = _parse_local_derived_types(unit, real_type, kind_ctype_map)
    derived_type_ranges = _local_derived_type_index_ranges(unit) if local_derived_types else []
    global _ACTIVE_DERIVED_TYPES
    active_derived_types = dict(_ACTIVE_DERIVED_TYPES)
    active_derived_types.update(local_derived_types)
    _ACTIVE_DERIVED_TYPES = active_derived_types
    vars_map = dict(vars_map_override) if vars_map_override is not None else _parse_decls(unit, real_type, kind_ctype_map, local_derived_types)
    assumed_extents: Dict[str, List[str]] = {}
    indent = 0
    body_line_nos: List[int] = list(unit.get("body_line_nos", []))
    source_lines: List[str] = list(unit.get("source_lines", []))

    byref_scalars: set[str] = set()
    stdout_unit_names: set[str] = {"output_unit"}

    for _raw_use in unit.get("body_lines", []):
        _use_code = _strip_comment(_raw_use).strip()
        m_use_iso = re.match(r"^use\s+iso_fortran_env\b(?:\s*,\s*only\s*:\s*(.*))?$", _use_code, re.IGNORECASE)
        if not m_use_iso:
            continue
        only_list = (m_use_iso.group(1) or "").strip()
        if not only_list:
            stdout_unit_names.add("output_unit")
            continue
        for _item in _split_args_top_level(only_list):
            _it = _item.strip()
            if not _it:
                continue
            m_rename = re.match(r"^([a-z_]\w*)\s*=>\s*([a-z_]\w*)$", _it, re.IGNORECASE)
            if m_rename:
                local_name = m_rename.group(1).lower()
                use_name = m_rename.group(2).lower()
                if use_name == "output_unit":
                    stdout_unit_names.add(local_name)
                continue
            if _it.lower() == "output_unit":
                stdout_unit_names.add("output_unit")

    unit_name_l = str(unit.get("name", "")).lower()
    implicit_result_name = "__result"
    use_implicit_result = bool(unit["kind"] == "function" and not (unit.get("result") or "").strip())
    ret_name_c = ""
    fail_stmt = "return 1;"

    if unit["kind"] == "function":
        ret_name = (unit.get("result") or "").lower()
        ret_name_c = ret_name if ret_name else implicit_result_name
        ret_lookup = ret_name if ret_name else unit_name_l
        ret_var = _fallback_function_result_var(unit, real_type, kind_ctype_map) or vars_map.get(ret_lookup) or Var(real_type)
        ret_is_array = bool(ret_var.is_array)
        fail_stmt = "return NULL;" if ret_is_array else "return 0;"
        args = []
        proc_name = str(unit.get("name", "")).lower()
        extent_lists = proc_arg_extent_names.get(proc_name, [])
        byref_array_aliases: List[tuple[str, str]] = []
        for idx, a in enumerate(unit.get("args", [])):
            av = vars_map.get(a.lower(), Var("int"))
            exts = extent_lists[idx] if idx < len(extent_lists) else []
            if exts:
                args.extend([f"const int {nm}" for nm in exts])
            carg = _arg_c_name(a, av)
            args.append(_emit_decl(carg, av, vars_map, real_type, False, as_arg=True, assumed_extents=assumed_extents))
            if carg != a:
                byref_array_aliases.append((a, carg))
            if av.is_array and _is_assumed_shape(av.dim) and (not av.is_allocatable) and (not av.is_pointer):
                exts = extent_lists[idx] if idx < len(extent_lists) else _extent_param_names(a.lower(), 1)
                assumed_extents[a.lower()] = exts
            if (
                (not av.is_array)
                and (not av.is_external)
                and (av.intent in {"out", "inout"} or av.optional)
                and ((av.ctype or "").lower() != "char *")
            ):
                byref_scalars.add(a.lower())
        ret_decl = f"{ret_var.ctype} *" if ret_is_array else f"{ret_var.ctype} "
        out.append(f"{ret_decl}{unit['name']}({', '.join(args)}) {{")
        indent = 3
        doc = _first_unit_doc_comment(unit)
        if doc:
            out.append(" " * indent + f"/* {doc} */")
        for a in unit.get("args", []):
            av = vars_map.get(a.lower())
            if av is not None and av.comment:
                out.append(" " * indent + f"/* {a}: {av.comment} */")
        for nm, carg in byref_array_aliases:
            out.append(" " * indent + f"#define {nm} (*{carg})")
        if local_derived_types:
            emit_local_derived_type_typedefs(out, indent, local_derived_types)
        for arr_name, exts in assumed_extents.items():
            for k, en in enumerate(exts, start=1):
                out.append(" " * indent + f"/* {en}: extent of {arr_name} (dimension {k}) */")
        # Declare function result explicitly.
        if ret_name_c:
            if ret_is_array:
                rank_ret = max(1, len(_dim_parts(ret_var.dim)))
                if _is_dynamic_array_result(ret_var):
                    out.append(" " * indent + f"{ret_var.ctype} *{ret_name_c} = NULL;")
                    for en in _alloc_extent_names(ret_name_c, rank_ret):
                        out.append(" " * indent + f"int {en} = 0;")
                else:
                    dim = _dim_product_expr(
                        ret_var.dim or "1",
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                    )
                    out.append(
                        " " * indent
                        + f"{ret_var.ctype} *{ret_name_c} = ({ret_var.ctype}*) malloc(sizeof({ret_var.ctype}) * {_drop_redundant_outer_parens(dim)});"
                    )
                    out.append(" " * indent + f"if (!{ret_name_c}) return NULL;")
                    if (ret_var.ctype or real_type).lower() == "char *":
                        out.append(" " * indent + f"for (int i_fill = 0; i_fill < {_drop_redundant_outer_parens(dim)}; ++i_fill) {ret_name_c}[i_fill] = NULL;")
            else:
                out.append(" " * indent + f"{ret_var.ctype} {ret_name_c};")
        arg_names_lower = {a.lower() for a in unit.get("args", [])}
        for nm, v in vars_map.items():
            if nm in arg_names_lower:
                if (v.is_allocatable or v.is_pointer) and v.is_array:
                    for en in _alloc_extent_names(nm, max(1, len(_dim_parts(v.dim)))):
                        out.append(" " * indent + f"int {en} = 0;")
                continue
            if nm == ret_name or (not ret_name and nm == unit_name_l):
                continue
            if v.comment:
                out.append(" " * indent + f"/* {nm}: {v.comment} */")
            out.append(" " * indent + _emit_decl(nm, v, vars_map, real_type, False, assumed_extents=assumed_extents))
            if (v.is_allocatable or v.is_pointer) and v.is_array:
                for en in _alloc_extent_names(nm, max(1, len(_dim_parts(v.dim)))):
                    out.append(" " * indent + f"int {en} = 0;")
    elif unit["kind"] == "subroutine":
        fail_stmt = "return;"
        args = []
        proc_name = str(unit.get("name", "")).lower()
        extent_lists = proc_arg_extent_names.get(proc_name, [])
        byref_array_aliases: List[tuple[str, str]] = []
        for idx, a in enumerate(unit.get("args", [])):
            av = vars_map.get(a.lower(), Var("int"))
            exts = extent_lists[idx] if idx < len(extent_lists) else []
            if exts:
                args.extend([f"const int {nm}" for nm in exts])
            carg = _arg_c_name(a, av)
            args.append(_emit_decl(carg, av, vars_map, real_type, False, as_arg=True, assumed_extents=assumed_extents))
            if carg != a:
                byref_array_aliases.append((a, carg))
            if av.is_array and _is_assumed_shape(av.dim) and (not av.is_allocatable) and (not av.is_pointer):
                exts = extent_lists[idx] if idx < len(extent_lists) else _extent_param_names(a.lower(), 1)
                assumed_extents[a.lower()] = exts
            if (
                (not av.is_array)
                and (not av.is_external)
                and (av.intent in {"out", "inout"} or av.optional)
                and ((av.ctype or "").lower() != "char *")
            ):
                byref_scalars.add(a.lower())
        out.append(f"void {unit['name']}({', '.join(args)}) {{")
        indent = 3
        doc = _first_unit_doc_comment(unit)
        if doc:
            out.append(" " * indent + f"/* {doc} */")
        for a in unit.get("args", []):
            av = vars_map.get(a.lower())
            if av is not None and av.comment:
                out.append(" " * indent + f"/* {a}: {av.comment} */")
        for nm, carg in byref_array_aliases:
            out.append(" " * indent + f"#define {nm} (*{carg})")
        if local_derived_types:
            emit_local_derived_type_typedefs(out, indent, local_derived_types)
        for arr_name, exts in assumed_extents.items():
            for k, en in enumerate(exts, start=1):
                out.append(" " * indent + f"/* {en}: extent of {arr_name} (dimension {k}) */")
        arg_names_lower = {a.lower() for a in unit.get("args", [])}
        for nm, v in vars_map.items():
            if nm in arg_names_lower:
                if (v.is_allocatable or v.is_pointer) and v.is_array:
                    for en in _alloc_extent_names(nm, max(1, len(_dim_parts(v.dim)))):
                        out.append(" " * indent + f"int {en} = 0;")
                continue
            if v.comment:
                out.append(" " * indent + f"/* {nm}: {v.comment} */")
            out.append(" " * indent + _emit_decl(nm, v, vars_map, real_type, False, assumed_extents=assumed_extents))
            if (v.is_allocatable or v.is_pointer) and v.is_array:
                for en in _alloc_extent_names(nm, max(1, len(_dim_parts(v.dim)))):
                    out.append(" " * indent + f"int {en} = 0;")
    else:
        saw_get_command_argument = any(
            re.match(r"^\s*call\s+get_command_argument\s*\(", _strip_comment(ln).strip(), re.IGNORECASE)
            for ln in unit["body_lines"]
        )
        if saw_get_command_argument:
            out.append("int main(int argc, char **argv) {")
        else:
            out.append("int main(void) {")
        indent = 3
        doc = _first_unit_doc_comment(unit)
        if doc:
            out.append(" " * indent + f"/* {doc} */")
        saw_random = any(re.match(r"^\s*call\s+random_number\s*\(", _strip_comment(ln).strip(), re.IGNORECASE) for ln in unit["body_lines"])
        if saw_random:
            out.append(" " * indent + "srand(1);")
        if local_derived_types:
            emit_local_derived_type_typedefs(out, indent, local_derived_types)
        for nm, v in vars_map.items():
            if v.comment:
                out.append(" " * indent + f"/* {nm}: {v.comment} */")
            out.append(" " * indent + _emit_decl(nm, v, vars_map, real_type, True, assumed_extents=assumed_extents))
            if (v.is_allocatable or v.is_pointer) and v.is_array:
                for en in _alloc_extent_names(nm, max(1, len(_dim_parts(v.dim)))):
                    out.append(" " * indent + f"int {en} = 0;")
        for nm, v in vars_map.items():
            if v.is_array:
                if v.is_allocatable or _is_assumed_shape(v.dim):
                    continue
                if _main_fixed_array_uses_heap(v):
                    dim = _dim_product_expr(v.dim or "1", vars_map, real_type)
                    out.append(" " * indent + f"{nm} = ({v.ctype}*) malloc(sizeof({v.ctype}) * ({_drop_redundant_outer_parens(dim)}));")
                    out.append(" " * indent + f"if (!{nm}) {fail_stmt}")
                    if v.init is not None:
                        m_ctor_init = re.match(r"^\[\s*(.*)\s*\]$", v.init.strip())
                        if m_ctor_init:
                            items = [x.strip() for x in _split_args_top_level(m_ctor_init.group(1)) if x.strip()]
                            for k, it in enumerate(items):
                                cv = _convert_expr(it, vars_map, real_type)
                                out.append(" " * indent + f"{nm}[{k}] = {cv};")
    loop_stack: List[Dict[str, str]] = []
    loop_counter = 0
    select_stack: List[Dict[str, bool]] = []
    if_stack: List[Dict[str, bool]] = []
    last_comment_lineno: Optional[int] = None
    dynamic_write_formats: Dict[str, tuple[str, str]] = {}

    def _emit_error_stop_inline(arg_text: str, base_indent: int) -> None:
        code_arg = arg_text.strip()
        c_stop = "1"
        if code_arg:
            if (code_arg.startswith('"') and code_arg.endswith('"')) or (code_arg.startswith("'") and code_arg.endswith("'")):
                c_msg = _convert_expr(
                    code_arg,
                    vars_map,
                    real_type,
                    byref_scalars,
                    assumed_extents,
                    proc_arg_extent_names,
                )
                out.append(" " * base_indent + f'fprintf(stderr, "%s\\n", {c_msg});')
            else:
                c_stop = _convert_expr(
                    code_arg,
                    vars_map,
                    real_type,
                    byref_scalars,
                    assumed_extents,
                    proc_arg_extent_names,
                )
        if unit["kind"] == "program":
            out.append(" " * base_indent + f"return {c_stop};")
        else:
            out.append(" " * base_indent + f"exit({c_stop});")

    def _emit_allocate_stmt(
        target_raw: str,
        shp_items: List[str],
        alloc_kw: str,
        alloc_val_raw: str,
    ) -> bool:
        source_raw = alloc_val_raw if alloc_kw == 'source' else ''
        mold_raw = alloc_val_raw if alloc_kw == 'mold' else ''
        if '%' in target_raw:
            parts = [x.strip().lower() for x in target_raw.split('%') if x.strip()]
            if len(parts) >= 2:
                fld_spec = _derived_field_spec(parts[0], parts[1:], vars_map)
                if fld_spec is not None and _is_allocatable_derived_field(fld_spec):
                    rank = _derived_field_rank(fld_spec)
                    if len(shp_items) == rank:
                        shp_c = [_convert_expr(s, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for s in shp_items]
                        n_total = _dim_product_from_parts(shp_c, vars_map, real_type, byref_scalars, assumed_extents)
                        comp_expr = target_raw.replace('%', '.').replace(' ', '')
                        parent_expr = comp_expr.rsplit('.', 1)[0]
                        fld_name = parts[-1]
                        base = _derived_field_base_ctype(fld_spec)
                        out.append(' ' * indent + f'if ({comp_expr}) free({comp_expr});')
                        if base == 'char *':
                            out.append(' ' * indent + f'{comp_expr} = (char**) malloc(sizeof(char*) * ({n_total}));')
                        else:
                            out.append(' ' * indent + f'{comp_expr} = ({base}*) malloc(sizeof({base}) * ({n_total}));')
                        out.append(' ' * indent + f'if (!{comp_expr} && ({n_total}) > 0) {fail_stmt}')
                        for k in range(rank):
                            en = f"{parent_expr}.__n_{fld_name}" if rank == 1 else f"{parent_expr}.__n_{fld_name}_{k+1}"
                            out.append(' ' * indent + f'{en} = {shp_c[k]};')
                        if source_raw:
                            src = _convert_expr(source_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            out.append(' ' * indent + f'for (int i_fill = 0; i_fill < ({n_total}); ++i_fill) {comp_expr}[i_fill] = {src};')
                        return True
        else:
            an = target_raw.lower()
            av = vars_map.get(an)
            if av is not None and av.is_array and (av.is_allocatable or av.is_pointer):
                rank = max(1, len(_dim_parts(av.dim)))
                if mold_raw:
                    mv = vars_map.get(mold_raw.strip().lower())
                    if mv is not None and mv.is_array:
                        shp_c = _resolved_dim_parts(mv, mold_raw.strip().lower(), assumed_extents)
                        if len(shp_c) == rank:
                            n_total = _dim_product_from_parts(shp_c, vars_map, real_type, byref_scalars, assumed_extents)
                            if (av.ctype or "").lower() == "char *":
                                n0 = _alloc_len_name(an)
                                out.append(" " * indent + f"if ({an}) free_str_array({an}, {n0});")
                                out.append(" " * indent + f"{an} = (char**) malloc(sizeof(char*) * ({n_total}));")
                                out.append(" " * indent + f"if (!{an} && ({n_total}) > 0) {fail_stmt}")
                                out.append(" " * indent + f"for (int i_fill = 0; i_fill < ({n_total}); ++i_fill) {an}[i_fill] = NULL;")
                            else:
                                out.append(" " * indent + f"if ({an}) free({an});")
                                out.append(" " * indent + f"{an} = ({av.ctype}*) malloc(sizeof({av.ctype}) * ({n_total}));")
                                out.append(" " * indent + f"if (!{an} && ({n_total}) > 0) {fail_stmt}")
                            for k, en in enumerate(_alloc_extent_names(an, rank)):
                                out.append(" " * indent + f"{en} = {shp_c[k]};")
                            if (av.ctype or "").lower() == "char *":
                                out.append(" " * indent + f'for (int i_fill = 0; i_fill < ({n_total}); ++i_fill) assign_str_alloc(&{an}[i_fill], "");')
                            return True
                if len(shp_items) == rank:
                    shp_c = [_convert_expr(s, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for s in shp_items]
                    n_total = _dim_product_from_parts(shp_c, vars_map, real_type, byref_scalars, assumed_extents)
                    if (av.ctype or "").lower() == "char *":
                        n0 = _alloc_len_name(an)
                        out.append(" " * indent + f"if ({an}) free_str_array({an}, {n0});")
                        out.append(" " * indent + f"{an} = (char**) malloc(sizeof(char*) * ({n_total}));")
                        out.append(" " * indent + f"if (!{an} && ({n_total}) > 0) {fail_stmt}")
                        out.append(" " * indent + f"for (int i_fill = 0; i_fill < ({n_total}); ++i_fill) {an}[i_fill] = NULL;")
                    else:
                        out.append(" " * indent + f"if ({an}) free({an});")
                        out.append(" " * indent + f"{an} = ({av.ctype}*) malloc(sizeof({av.ctype}) * ({n_total}));")
                        out.append(" " * indent + f"if (!{an} && ({n_total}) > 0) {fail_stmt}")
                    for k, en in enumerate(_alloc_extent_names(an, rank)):
                        out.append(" " * indent + f"{en} = {shp_c[k]};")
                    if source_raw:
                        src = _convert_expr(source_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        if (av.ctype or "").lower() == "char *":
                            out.append(' ' * indent + f'for (int i_fill = 0; i_fill < ({n_total}); ++i_fill) assign_str_alloc(&{an}[i_fill], {src});')
                        else:
                            out.append(' ' * indent + f'for (int i_fill = 0; i_fill < ({n_total}); ++i_fill) {an}[i_fill] = {src};')
                    elif (av.ctype or "").lower() == "char *":
                        out.append(' ' * indent + f'for (int i_fill = 0; i_fill < ({n_total}); ++i_fill) assign_str_alloc(&{an}[i_fill], "");')
                    return True
        return False

    def _convert_optional_call_expr(callee: str, raw_args: List[str]) -> str:
        cl = callee.lower()
        raw_args = _normalize_actual_args(callee, raw_args, proc_arg_names)
        modes = proc_arg_modes.get(cl, [])
        opts = proc_arg_optional.get(cl, [])
        ctypes = proc_arg_ctypes.get(cl, [])
        is_arr = proc_arg_is_array.get(cl, [])
        array_byref = proc_arg_array_byref.get(cl, [])
        cargs: List[str] = []
        n_expected = max(len(modes), len(opts), len(ctypes), len(is_arr))
        for k in range(n_expected):
            mode = modes[k] if k < len(modes) else "value"
            opt = opts[k] if k < len(opts) else False
            cty = ctypes[k] if k < len(ctypes) else real_type
            arrk = is_arr[k] if k < len(is_arr) else False
            if k >= len(raw_args):
                cargs.append("NULL" if opt else "0")
                continue
            a = raw_args[k]
            cexpr = _convert_expr(a, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            if mode == "value":
                cargs.append(cexpr)
                continue
            m_id = re.match(r"^\s*([a-z_]\w*)\s*$", a, re.IGNORECASE)
            if m_id:
                nm = m_id.group(1).lower()
                vv = vars_map.get(nm)
                if vv is not None:
                    if vv.is_array:
                        byref_arr = array_byref[k] if k < len(array_byref) else False
                        if byref_arr:
                            cargs.append(f"&{nm}")
                        else:
                            cargs.append(nm)
                    else:
                        cargs.append(f"&{nm}")
                    continue
            if opt and (not arrk):
                cargs.append(f"&(({cty}){{{cexpr}}})")
            else:
                cargs.append(f"&({cexpr})")
        return f"{callee}({', '.join(cargs)})"

    def _close_select_case_if_open() -> None:
        nonlocal indent
        if not select_stack:
            return
        top = select_stack[-1]
        if not top.get("case_open", False):
            return
        if top.get("mode") == "switch" and not top.get("current_default", False):
            out.append(" " * indent + "break;")
        indent = max(indent - 3, 0)
        out.append(" " * indent + "}")
        top["case_open"] = False
        top["current_default"] = False

    def _select_case_needs_if_chain(start_idx: int) -> bool:
        depth = 0
        for j in range(start_idx + 1, len(unit["body_lines"])):
            stmt = _strip_comment(unit["body_lines"][j]).strip()
            if not stmt:
                continue
            low_stmt = stmt.lower()
            if re.match(r"^select\s+case\s*\(", low_stmt):
                depth += 1
                continue
            if re.match(r"^end\s+select\s*$", low_stmt):
                if depth == 0:
                    return False
                depth -= 1
                continue
            if depth != 0:
                continue
            m_case_scan = re.match(r"^case\s*\((.+)\)\s*$", stmt, re.IGNORECASE)
            if not m_case_scan:
                continue
            sel_items = [x.strip() for x in _split_args_top_level(m_case_scan.group(1)) if x.strip()]
            if any(":" in s for s in sel_items):
                return True
        return False

    def _select_case_cond(selector: str, selector_ctype: str, item_raw: str) -> str:
        item_raw = item_raw.strip()
        if selector_ctype == "string":
            cv = _convert_expr(item_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            return f'(strcmp(trim_s({selector}), trim_s({cv})) == 0)'
        if ":" in item_raw:
            lo_raw, hi_raw = (item_raw.split(":", 1) + [""])[:2]
            parts = []
            lo_raw = lo_raw.strip()
            hi_raw = hi_raw.strip()
            if lo_raw:
                lo_c = _convert_expr(lo_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                parts.append(f"({selector} >= {lo_c})")
            if hi_raw:
                hi_c = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                parts.append(f"({selector} <= {hi_c})")
            if not parts:
                return "1"
            return "(" + " && ".join(parts) + ")"
        cv = _convert_expr(item_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        return f"({selector} == {cv})"

    def _new_loop_info(loop_name: str, *, var: str = "", step: str = "") -> Dict[str, str]:
        nonlocal loop_counter
        loop_counter += 1
        base = f"xf2c_loop_{loop_counter}"
        return {
            "name": loop_name.lower(),
            "var": var,
            "step": step,
            "continue_label": f"{base}_continue",
            "break_label": f"{base}_break",
        }

    def _find_loop_info(loop_name: str) -> Optional[Dict[str, str]]:
        target = loop_name.strip().lower()
        if not loop_stack:
            return None
        if not target:
            return loop_stack[-1]
        for info in reversed(loop_stack):
            if info.get("name", "") == target:
                return info
        return None

    def _emit_fortran_annot(code_line: str) -> None:
        if not annotate:
            return
        safe = code_line.replace("*/", "* /")
        out.append(" " * indent + f"/* f90: {safe} */")

    for idx, raw in enumerate(unit["body_lines"]):
        code = _strip_comment(raw).strip()
        if not code:
            continue
        code = _rewrite_type_bound_calls(code, vars_map, real_type)
        low = code.lower()

        if low in {"implicit none", "contains"} or low.startswith("use "):
            continue
        if derived_type_ranges and _index_in_ranges(idx, derived_type_ranges):
            continue
        if re.match(r"^type\s*\(\s*[a-z_]\w*\s*\)", low):
            continue
        if re.match(r"^(integer(?:\s*\([^)]*\))?|real|double\s+precision|complex(?:\s*\([^)]*\))?|character|logical)\b", low):
            continue
        if not (
            low.startswith("end ")
            or low in {"else", "end", "contains"}
            or low.startswith("case ")
            or low.startswith("case(")
            or low.startswith("case default")
        ):
            _emit_fortran_annot(code)
        if idx < len(body_line_nos):
            ln = body_line_nos[idx]
            if 1 <= ln <= len(source_lines) and ln != last_comment_lineno:
                cmt = _extract_fortran_comment(source_lines[ln - 1])
                if cmt:
                    out.append(" " * indent + f"/* {cmt} */")
                    last_comment_lineno = ln

        m_do = re.match(r"^(?:([a-z_]\w*)\s*:\s*)?do\s+([a-z_]\w*)\s*=\s*(.+)$", code, re.IGNORECASE)
        if m_do:
            rest_parts = [x.strip() for x in _split_args_top_level(m_do.group(3)) if x.strip()]
            if len(rest_parts) not in {2, 3}:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            loop_name = (m_do.group(1) or "").strip().lower()
            v = m_do.group(2).strip()
            lo = _convert_expr(rest_parts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            hi = _convert_expr(rest_parts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            st = _convert_expr((rest_parts[2] if len(rest_parts) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            info = _new_loop_info(loop_name, var=v, step=st)
            out.append(" " * indent + f"{v} = {lo};")
            out.append(" " * indent + f"while ((({st}) >= 0) ? ({v} <= ({hi})) : ({v} >= ({hi}))) {{")
            indent += 3
            loop_stack.append(info)
            continue
        parsed_open = _split_leading_paren_group(code, "open")
        if parsed_open:
            ctl = parsed_open[0].strip()
            ctl_items = [x.strip() for x in _split_args_top_level(ctl) if x.strip()]
            unit_txt = None
            newunit_txt = None
            file_txt = None
            action_txt = '"read"'
            status_txt = '"old"'
            iostat_txt = None
            for idx_ctl, ctl_item in enumerate(ctl_items):
                m_kw = re.match(r"(?i)^([a-z_]\w*)\s*=\s*(.+)$", ctl_item)
                if m_kw:
                    key = m_kw.group(1).lower()
                    val = m_kw.group(2).strip()
                    if key == 'unit':
                        unit_txt = val
                    elif key == 'newunit':
                        newunit_txt = val
                    elif key == 'file':
                        file_txt = val
                    elif key == 'action':
                        action_txt = val
                    elif key == 'status':
                        status_txt = val
                    elif key == 'iostat':
                        iostat_txt = val
                elif idx_ctl == 0:
                    unit_txt = ctl_item
            if (unit_txt is not None or newunit_txt is not None) and file_txt is not None:
                if newunit_txt is not None:
                    unit_c = _convert_expr(newunit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    out.append(" " * indent + f"{unit_c} = alloc_unit();")
                else:
                    unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                file_c = _convert_expr(file_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                action_c = _convert_expr(action_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                status_c = _convert_expr(status_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                if iostat_txt:
                    out.append(" " * indent + f"{iostat_txt} = open_unit({unit_c}, {file_c}, {action_c}, {status_c});")
                else:
                    out.append(" " * indent + f"if (open_unit({unit_c}, {file_c}, {action_c}, {status_c}) != 0) {fail_stmt}")
                continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue
        parsed_close = _split_leading_paren_group(code, "close")
        if parsed_close:
            ctl = parsed_close[0].strip()
            ctl_items = [x.strip() for x in _split_args_top_level(ctl) if x.strip()]
            unit_txt = ctl_items[0] if ctl_items else None
            for ctl_item in ctl_items:
                m_kw = re.match(r"(?i)^unit\s*=\s*(.+)$", ctl_item)
                if m_kw:
                    unit_txt = m_kw.group(1).strip()
                    break
            if unit_txt is not None:
                unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                out.append(" " * indent + f"close_unit({unit_c});")
                continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue
        parsed_read = _split_leading_paren_group(code, "read")
        if parsed_read:
            ctl = parsed_read[0].strip()
            tail = (parsed_read[1] or '').strip()
            ctl_items = [x.strip() for x in _split_args_top_level(ctl) if x.strip()]
            unit_txt = None
            fmt_txt = None
            iostat_txt = None
            pos_txt = None
            if ctl_items:
                first_ctl = ctl_items[0]
                m_first_kw = re.match(r"(?i)^([a-z_]\w*)\s*=\s*(.+)$", first_ctl)
                if m_first_kw is None:
                    unit_txt = first_ctl
                    if len(ctl_items) >= 2 and re.match(r"(?i)^[a-z_]\w*\s*=", ctl_items[1]) is None:
                        fmt_txt = ctl_items[1]
                for ctl_item in ctl_items:
                    m_kw = re.match(r"(?i)^([a-z_]\w*)\s*=\s*(.+)$", ctl_item)
                    if not m_kw:
                        continue
                    key = m_kw.group(1).lower()
                    val = m_kw.group(2).strip()
                    if key == 'unit':
                        unit_txt = val
                    elif key == 'fmt':
                        fmt_txt = val
                    elif key == 'iostat':
                        iostat_txt = val
                    elif key == 'pos':
                        pos_txt = val
            if tail.startswith(','):
                tail = tail[1:].strip()
            items = [x.strip() for x in _split_args_top_level(tail) if x.strip()] if tail else []
            if unit_txt is not None and fmt_txt is None and len(items) == 1:
                tgt_raw = items[0].strip()
                tgt_nm_m = re.match(r"^\s*([a-z_]\w*)\s*$", tgt_raw, re.IGNORECASE)
                unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                pos_c = _convert_expr(pos_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if pos_txt else "0L"
                ptr_c = None
                elem_size_c = None
                count_c = None
                if tgt_nm_m:
                    tgt_nm = tgt_nm_m.group(1).lower()
                    tv = vars_map.get(tgt_nm)
                    if tv is not None:
                        cty = (tv.ctype or real_type).lower()
                        if tv.is_array:
                            ptr_c = tgt_nm
                            if cty == "int" or tv.is_logical:
                                elem_size_c = "sizeof(int)"
                            elif cty in {"long long", "long long int"}:
                                elem_size_c = "sizeof(long long)"
                            elif cty == "char *":
                                elem_size_c = "1"
                            else:
                                elem_size_c = "sizeof(double)" if cty == "double" else "sizeof(float)"
                            if cty == "char *":
                                count_c = _simplify_int_expr_text(tv.char_len) if tv.char_len else "1"
                            elif tv.is_allocatable or tv.is_pointer:
                                count_c = _dim_product_from_parts(
                                    _resolved_dim_parts(tv, tgt_nm, assumed_extents),
                                    vars_map,
                                    real_type,
                                    byref_scalars,
                                    assumed_extents,
                                )
                            else:
                                count_c = _dim_product_expr(tv.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                        else:
                            if cty == "char *":
                                ptr_c = tgt_nm
                                elem_size_c = "1"
                                count_c = _simplify_int_expr_text(tv.char_len) if tv.char_len else "1"
                            else:
                                ptr_c = f"&({tgt_nm})"
                                if cty == "int" or tv.is_logical:
                                    elem_size_c = "sizeof(int)"
                                elif cty in {"long long", "long long int"}:
                                    elem_size_c = "sizeof(long long)"
                                else:
                                    elem_size_c = "sizeof(double)" if cty == "double" else "sizeof(float)"
                                count_c = "1"
                if ptr_c is not None and elem_size_c is not None and count_c is not None:
                    if iostat_txt:
                        out.append(" " * indent + f"{iostat_txt} = read_bytes_unit({unit_c}, (long) ({pos_c}), {ptr_c}, {elem_size_c}, {count_c});")
                    else:
                        out.append(" " * indent + f"if (read_bytes_unit({unit_c}, (long) ({pos_c}), {ptr_c}, {elem_size_c}, {count_c}) != 0) {fail_stmt}")
                    continue
            if unit_txt is not None and fmt_txt is not None and _is_fortran_string_literal(fmt_txt) and len(items) == 1:
                fmt_clean = _unquote_fortran_string_literal(fmt_txt).strip().lower()
                tgt = items[0].lower()
                tv = vars_map.get(tgt)
                if fmt_clean == '(a)' and tv is not None and (tv.ctype or '').lower() == 'char *' and tv.char_len:
                    unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    len_c = _simplify_int_expr_text(tv.char_len)
                    if iostat_txt:
                        out.append(" " * indent + f"{iostat_txt} = read_a({unit_c}, {tgt}, {len_c});")
                    else:
                        out.append(" " * indent + f"if (read_a({unit_c}, {tgt}, {len_c}) != 0) {fail_stmt}")
                    continue
            if unit_txt is not None and fmt_txt is not None and _is_fortran_string_literal(fmt_txt) and len(items) == 2:
                fmt_clean = _unquote_fortran_string_literal(fmt_txt).strip().lower()
                iv = vars_map.get(items[0].lower())
                rv = vars_map.get(items[1].lower())
                if (
                    fmt_clean == '(i3,1x,f6.1)'
                    and iv is not None
                    and rv is not None
                    and (iv.ctype or "").lower() == "int"
                    and (not iv.is_array)
                    and (not rv.is_array)
                ):
                    unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    rty = (rv.ctype or real_type).lower()
                    helper = "read_int_double_record" if rty == "double" else "read_int_float_record"
                    if iostat_txt:
                        out.append(" " * indent + f"{iostat_txt} = {helper}({unit_c}, &{items[0].lower()}, &{items[1].lower()});")
                    else:
                        out.append(" " * indent + f"if ({helper}({unit_c}, &{items[0].lower()}, &{items[1].lower()}) != 0) {fail_stmt}")
                    continue
            if unit_txt is not None and fmt_txt is not None and fmt_txt.strip() == '*' and len(items) == 2:
                src_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                first_raw = items[0].strip()
                second_raw = items[1].strip()
                fv = vars_map.get(first_raw.lower())
                sv = vars_map.get(second_raw.lower())
                if (
                    fv is not None
                    and (fv.ctype or "").lower() == "int"
                    and (not fv.is_array)
                    and sv is not None
                    and sv.is_array
                    and (sv.ctype or "").lower() == "char *"
                    and (sv.is_allocatable or sv.is_pointer)
                ):
                    if iostat_txt:
                        out.append(" " * indent + f"{iostat_txt} = read_words_after_int_s({src_c}, {first_raw}, {second_raw});")
                    else:
                        out.append(" " * indent + f"if (read_words_after_int_s({src_c}, {first_raw}, {second_raw}) != 0) {fail_stmt}")
                    continue
            if unit_txt is not None and fmt_txt is not None and fmt_txt.strip() == '*' and len(items) == 1:
                src_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                tgt_raw = items[0].strip()
                tgt_c = _convert_expr(tgt_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                tgt_cty = _format_item_ctype(tgt_raw, vars_map, real_type)
                helper = None
                if tgt_cty == "int":
                    helper = "read_first_int_s"
                elif tgt_cty == "float":
                    helper = "read_first_float_s"
                else:
                    helper = "read_first_double_s"
                if iostat_txt:
                    out.append(" " * indent + f"{iostat_txt} = {helper}({src_c}, &({tgt_c}));")
                else:
                    out.append(" " * indent + f"if ({helper}({src_c}, &({tgt_c})) != 0) {fail_stmt}")
                continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue
        m_alloc_multi = re.match(r"^allocate\s*\(\s*(.+)\s*\)\s*$", code, re.IGNORECASE)
        if m_alloc_multi:
            alloc_inner = m_alloc_multi.group(1).strip()
            alloc_items = [x.strip() for x in _split_args_top_level(alloc_inner) if x.strip()]
            has_kw_alloc = any(re.match(r"^(?:source|mold)\s*=", it, re.IGNORECASE) for it in alloc_items)
            if len(alloc_items) > 1 and not has_kw_alloc:
                parsed_multi: List[tuple[str, List[str], str, str]] = []
                ok_multi = True
                for alloc_item in alloc_items:
                    m_one = re.match(
                        r"^([a-z_]\w*(?:\s*%\s*[a-z_]\w*)*)(?:\s*\(\s*(.+?)\s*\))?\s*(?:,\s*(source|mold)\s*=\s*(.+?)\s*)?$",
                        alloc_item,
                        re.IGNORECASE,
                    )
                    if not m_one:
                        ok_multi = False
                        break
                    parsed_multi.append(
                        (
                            m_one.group(1).strip(),
                            [x.strip() for x in _split_args_top_level(m_one.group(2) or '') if x.strip()],
                            (m_one.group(3) or '').strip().lower(),
                            (m_one.group(4) or '').strip(),
                        )
                    )
                if ok_multi:
                    handled_all = True
                    for target_raw, shp_items, alloc_kw, alloc_val_raw in parsed_multi:
                        if not _emit_allocate_stmt(target_raw, shp_items, alloc_kw, alloc_val_raw):
                            handled_all = False
                            break
                    if handled_all:
                        continue
                    out.append(" " * indent + f"/* unsupported: {code} */")
                    continue
        m_alloc = re.match(r"^allocate\s*\(\s*([a-z_]\w*(?:\s*%\s*[a-z_]\w*)*)(?:\s*\(\s*(.+?)\s*\))?\s*(?:,\s*(source|mold)\s*=\s*(.+?)\s*)?\)\s*$", code, re.IGNORECASE)
        if m_alloc:
            target_raw = m_alloc.group(1).strip()
            shp_items = [x.strip() for x in _split_args_top_level(m_alloc.group(2) or '') if x.strip()]
            alloc_kw = (m_alloc.group(3) or '').strip().lower()
            alloc_val_raw = (m_alloc.group(4) or '').strip()
            if _emit_allocate_stmt(target_raw, shp_items, alloc_kw, alloc_val_raw):
                continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue
        m_dealloc = re.match(r"^deallocate\s*\(\s*([a-z_]\w*)\s*\)\s*$", code, re.IGNORECASE)
        if m_dealloc:
            an = m_dealloc.group(1).lower()
            av = vars_map.get(an)
            if av is not None and av.is_array and (av.is_allocatable or av.is_pointer):
                out.append(" " * indent + f"if ({an}) free({an});")
                out.append(" " * indent + f"{an} = NULL;")
                for en in _alloc_extent_names(an, max(1, len(_dim_parts(av.dim)))):
                    out.append(" " * indent + f"{en} = 0;")
                continue
            if av is not None and (av.ctype or "").lower() == "char *" and (av.is_allocatable or av.is_pointer) and (not av.is_array):
                out.append(" " * indent + f"if ({an}) free({an});")
                out.append(" " * indent + f"{an} = NULL;")
                continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue
        m_do_forever = re.match(r"^(?:([a-z_]\w*)\s*:\s*)?do\s*$", code, re.IGNORECASE)
        if m_do_forever:
            loop_name = (m_do_forever.group(1) or "").strip().lower()
            info = _new_loop_info(loop_name)
            out.append(" " * indent + "while (1) {")
            indent += 3
            loop_stack.append(info)
            continue
        m_end_do = re.match(r"^end\s+do(?:\s+([a-z_]\w*))?\s*$", code, re.IGNORECASE)
        if m_end_do:
            if not loop_stack:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            info = loop_stack.pop()
            out.append(" " * indent + f"{info['continue_label']}: ;")
            if info.get("var"):
                out.append(" " * indent + f"{info['var']} += {info['step']};")
            indent = max(indent - 3, 0)
            out.append(" " * indent + "}")
            out.append(" " * indent + f"{info['break_label']}: ;")
            continue
        m_exit = re.match(r"^exit(?:\s+([a-z_]\w*))?\s*$", code, re.IGNORECASE)
        if m_exit:
            info = _find_loop_info(m_exit.group(1) or "")
            if info is None:
                out.append(" " * indent + f"/* unsupported: {code} */")
            else:
                out.append(" " * indent + f"goto {info['break_label']};")
            continue
        m_cycle = re.match(r"^cycle(?:\s+([a-z_]\w*))?\s*$", code, re.IGNORECASE)
        if m_cycle:
            info = _find_loop_info(m_cycle.group(1) or "")
            if info is None:
                out.append(" " * indent + f"/* unsupported: {code} */")
            else:
                out.append(" " * indent + f"goto {info['continue_label']};")
            continue
        if low == "return":
            if unit["kind"] == "function":
                if unit.get("result"):
                    out.append(" " * indent + f"return {unit['result']};")
                else:
                    out.append(" " * indent + f"return {implicit_result_name};")
            elif unit["kind"] == "subroutine":
                out.append(" " * indent + "return;")
            else:
                out.append(" " * indent + "return 0;")
            continue
        m_stop = re.match(r"^stop(?:\s*\(\s*([^)]*)\s*\)|\s+(.+))?\s*$", code, re.IGNORECASE)
        if m_stop:
            code_arg = (m_stop.group(1) if m_stop.group(1) is not None else m_stop.group(2)) or ""
            code_arg = code_arg.strip()
            if not code_arg:
                c_stop = "0"
            else:
                # Integer stop codes map directly; strings map to failure.
                if (code_arg.startswith('"') and code_arg.endswith('"')) or (code_arg.startswith("'") and code_arg.endswith("'")):
                    c_stop = "1"
                else:
                    c_stop = _convert_expr(
                        code_arg,
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    )
            if unit["kind"] == "program":
                out.append(" " * indent + f"return {c_stop};")
            else:
                out.append(" " * indent + f"exit({c_stop});")
            continue
        m_error_stop = re.match(r"^error\s+stop(?:\s*\(\s*([^)]*)\s*\)|\s+(.+))?\s*$", code, re.IGNORECASE)
        if m_error_stop:
            code_arg = (m_error_stop.group(1) if m_error_stop.group(1) is not None else m_error_stop.group(2)) or ""
            _emit_error_stop_inline(code_arg, indent)
            continue
        m_rewind = re.match(r"^rewind\s*\(\s*(.+)\s*\)\s*$", code, re.IGNORECASE)
        if m_rewind:
            unit_expr = _convert_expr(
                m_rewind.group(1).strip(),
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            fail_stmt = "return 1;" if unit["kind"] == "program" else "return;"
            out.append(" " * indent + f"if (rewind_unit({unit_expr}) != 0) {fail_stmt}")
            continue
        m_backspace = re.match(r"^backspace\s*\(\s*(.+)\s*\)\s*$", code, re.IGNORECASE)
        if m_backspace:
            unit_expr = _convert_expr(
                m_backspace.group(1).strip(),
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            fail_stmt = "return 1;" if unit["kind"] == "program" else "return;"
            out.append(" " * indent + f"if (backspace_unit({unit_expr}) != 0) {fail_stmt}")
            continue

        m_select = re.match(r"^select\s+case\s*\((.+)\)\s*$", code, re.IGNORECASE)
        if m_select:
            sel_raw = m_select.group(1).strip()
            sel = _convert_expr(
                sel_raw,
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            sel_ctype = _format_item_ctype(sel_raw, vars_map, real_type)
            use_if_chain = sel_ctype == "string" or _select_case_needs_if_chain(idx)
            if use_if_chain:
                out.append(" " * indent + "{")
                indent += 3
                select_stack.append({
                    "case_open": False,
                    "current_default": False,
                    "mode": "if",
                    "selector": sel,
                    "selector_ctype": sel_ctype,
                    "first_case": True,
                })
            else:
                out.append(" " * indent + f"switch ({sel}) {{")
                indent += 3
                select_stack.append({
                    "case_open": False,
                    "current_default": False,
                    "mode": "switch",
                })
            continue

        if re.match(r"^end\s+select\s*$", code, re.IGNORECASE):
            if not select_stack:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            _close_select_case_if_open()
            indent = max(indent - 3, 0)
            out.append(" " * indent + "}")
            select_stack.pop()
            continue

        m_case = re.match(r"^case\s*\((.+)\)\s*$", code, re.IGNORECASE)
        if m_case:
            if not select_stack:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            _close_select_case_if_open()
            top = select_stack[-1]
            sel_list = [x.strip() for x in _split_args_top_level(m_case.group(1)) if x.strip()]
            if top.get("mode") == "if":
                selector = top.get("selector", "")
                selector_ctype = top.get("selector_ctype", real_type.lower())
                conds = [_select_case_cond(selector, selector_ctype, s) for s in sel_list]
                prefix = "if" if top.get("first_case", True) else "else if"
                out.append(" " * indent + f"{prefix} ({' || '.join(conds)}) {{")
                top["first_case"] = False
            else:
                for s in sel_list:
                    cv = _convert_expr(s, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    out.append(" " * indent + f"case {cv}:")
                out.append(" " * indent + "{")
            indent += 3
            top["case_open"] = True
            top["current_default"] = False
            continue

        if re.match(r"^case\s+default\s*$", code, re.IGNORECASE):
            if not select_stack:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            _close_select_case_if_open()
            top = select_stack[-1]
            if top.get("mode") == "if":
                prefix = "if" if top.get("first_case", True) else "else"
                if prefix == "if":
                    out.append(" " * indent + "if (1) {")
                else:
                    out.append(" " * indent + "else {")
                top["first_case"] = False
            else:
                out.append(" " * indent + "default:")
                out.append(" " * indent + "{")
            indent += 3
            top["case_open"] = True
            top["current_default"] = True
            continue

        m_call_rn = re.match(r"^call\s+random_number\s*\(\s*(.*)\s*\)\s*$", code, re.IGNORECASE)
        if m_call_rn:
            target_raw = m_call_rn.group(1).strip()
            m_id = re.match(r"^([a-z_]\w*)$", target_raw, re.IGNORECASE)
            if m_id:
                arr = m_id.group(1).lower()
                av = vars_map.get(arr)
                if av and av.is_array:
                    dparts = _resolved_dim_parts(av, arr, assumed_extents)
                    rank = max(1, len(dparts))
                    cty = (av.ctype or real_type).lower()
                    suf = "double" if cty == "double" else "float"
                    if rank >= 3 and len(dparts) >= 3:
                        d1 = _dim_extent_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents)
                        d2 = _dim_extent_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents)
                        d3 = _dim_extent_expr(dparts[2], vars_map, real_type, byref_scalars, assumed_extents)
                        out.append(" " * indent + f"fill_rand_3d_{suf}({d1}, {d2}, {d3}, {arr});")
                    elif rank >= 2 and len(dparts) >= 2:
                        d1 = _dim_extent_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents)
                        d2 = _dim_extent_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents)
                        out.append(" " * indent + f"fill_rand_2d_{suf}({d1}, {d2}, {arr});")
                    else:
                        n1 = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                        out.append(" " * indent + f"fill_rand_1d_{suf}({n1}, {arr});")
                elif av is not None:
                    cty = (av.ctype or real_type).lower()
                    if cty == "double":
                        out.append(" " * indent + f"{arr} = (double)rand() / (double)RAND_MAX;")
                    else:
                        out.append(" " * indent + f"{arr} = (float)rand() / (float)RAND_MAX;")
                else:
                    out.append(" " * indent + "/* unsupported random_number target */")
                continue
            # Scalar/element target, e.g. random_number(x(i))
            target_c = _convert_expr(target_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            cty = real_type
            toks = re.findall(r"\b([a-z_]\w*)\b", target_raw, flags=re.IGNORECASE)
            for t in toks:
                vv = vars_map.get(t.lower())
                if vv is not None:
                    cty = vv.ctype or real_type
                    break
            if cty == "double":
                out.append(" " * indent + f"{target_c} = (double)rand() / (double)RAND_MAX;")
            else:
                out.append(" " * indent + f"{target_c} = (float)rand() / (float)RAND_MAX;")
            continue
        m_call_rs = re.match(r"^call\s+random_seed(?:\s*\((.*)\))?\s*$", code, re.IGNORECASE)
        if m_call_rs:
            args_txt = (m_call_rs.group(1) or "").strip()
            if not args_txt:
                # srand(1) is already emitted in main when random is used.
                continue
            size_m = re.search(r"(?i)\bsize\s*=\s*([a-z_]\w*)\b", args_txt)
            if size_m:
                nm = size_m.group(1).lower()
                if nm in vars_map:
                    out.append(" " * indent + f"{nm} = 1;")
                    continue
            # Ignore put/get keyword forms for now.
            continue

        m_if_block = re.match(r"^if\s*\((.+)\)\s*then\s*$", code, re.IGNORECASE)
        if m_if_block:
            cond = _convert_expr(
                m_if_block.group(1).strip(),
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            out.append(" " * indent + f"if ({cond}) {{")
            indent += 3
            if_stack.append({"branch_open": True})
            continue

        m_else_if_block = re.match(r"^else\s+if\s*\((.+)\)\s*then\s*$", code, re.IGNORECASE)
        if m_else_if_block:
            if not if_stack:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            if if_stack[-1].get("branch_open", False):
                indent = max(indent - 3, 0)
                out.append(" " * indent + "}")
            cond = _convert_expr(
                m_else_if_block.group(1).strip(),
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            )
            out.append(" " * indent + f"else if ({cond}) {{")
            indent += 3
            if_stack[-1]["branch_open"] = True
            continue

        if low == "else":
            if not if_stack:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            if if_stack[-1].get("branch_open", False):
                indent = max(indent - 3, 0)
                out.append(" " * indent + "}")
            out.append(" " * indent + "else {")
            indent += 3
            if_stack[-1]["branch_open"] = True
            continue

        if re.match(r"^end\s+if\s*$", code, re.IGNORECASE):
            if not if_stack:
                out.append(" " * indent + f"/* unsupported: {code} */")
                continue
            if if_stack[-1].get("branch_open", False):
                indent = max(indent - 3, 0)
                out.append(" " * indent + "}")
            if_stack.pop()
            continue

        m_if_ret = re.match(r"^if\s*\((.+)\)\s*return\s*$", code, re.IGNORECASE)
        if m_if_ret:
            cond = _convert_expr(m_if_ret.group(1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            out.append(" " * indent + f"if ({cond}) return;")
            continue
        m_if_exit = re.match(r"^if\s*\((.+)\)\s*exit(?:\s+([a-z_]\w*))?\s*$", code, re.IGNORECASE)
        if m_if_exit:
            cond = _convert_expr(m_if_exit.group(1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            info = _find_loop_info(m_if_exit.group(2) or "")
            if info is None:
                out.append(" " * indent + f"/* unsupported: {code} */")
            else:
                out.append(" " * indent + f"if ({cond}) goto {info['break_label']};")
            continue
        m_if_cycle = re.match(r"^if\s*\((.+)\)\s*cycle(?:\s+([a-z_]\w*))?\s*$", code, re.IGNORECASE)
        if m_if_cycle:
            cond = _convert_expr(m_if_cycle.group(1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            info = _find_loop_info(m_if_cycle.group(2) or "")
            if info is None:
                out.append(" " * indent + f"/* unsupported: {code} */")
            else:
                out.append(" " * indent + f"if ({cond}) goto {info['continue_label']};")
            continue
        m_if_inline = None
        if code.lower().startswith("if"):
            open_pos = code.find("(")
            close_pos = _scan_balanced_parens(code, open_pos) if open_pos != -1 else None
            if open_pos != -1 and close_pos is not None:
                tail_txt = code[close_pos + 1 :].strip()
                if tail_txt and tail_txt.lower() != "then":
                    m_if_inline = (code[open_pos + 1 : close_pos], tail_txt)
        if m_if_inline:
            cond = _convert_expr(m_if_inline[0].strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            tail = m_if_inline[1].strip()
            m_tail_error_stop = re.match(r"^error\s+stop(?:\s*\(\s*([^)]*)\s*\)|\s+(.+))?\s*$", tail, re.IGNORECASE)
            m_tail_asn = re.match(r"^(.+?)\s*=\s*(.+)$", tail, re.IGNORECASE)
            m_tail_call = re.match(r"^call\s+([a-z_]\w*)\s*\((.*)\)\s*$", tail, re.IGNORECASE)
            if m_tail_error_stop:
                code_arg = (m_tail_error_stop.group(1) if m_tail_error_stop.group(1) is not None else m_tail_error_stop.group(2)) or ""
                out.append(" " * indent + f"if ({cond}) {{")
                _emit_error_stop_inline(code_arg, indent + 3)
                out.append(" " * indent + "}")
                continue
            if m_tail_asn:
                lhs_raw = m_tail_asn.group(1).strip()
                rhs_raw = m_tail_asn.group(2).strip()
                if use_implicit_result and lhs_raw.lower() == unit_name_l:
                    lhs_raw = implicit_result_name
                m_rhs_any_call = re.match(r"^\s*([a-z_]\w*)\s*\((.*)\)\s*$", rhs_raw, re.IGNORECASE)
                if m_rhs_any_call and any(proc_arg_optional.get(m_rhs_any_call.group(1).lower(), [])):
                    args_rhs = _split_args_top_level(m_rhs_any_call.group(2).strip()) if m_rhs_any_call.group(2).strip() else []
                    rhs = _convert_optional_call_expr(m_rhs_any_call.group(1), args_rhs)
                else:
                    rhs = _convert_expr(rhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                m_lhs_char_elem = re.match(r"^([a-z_]\w*)\s*\(\s*([^,:()]+)\s*\)$", lhs_raw, re.IGNORECASE)
                if m_lhs_char_elem:
                    lhs_nm = m_lhs_char_elem.group(1).lower()
                    lv = vars_map.get(lhs_nm)
                    if lv is not None and lv.is_array and (lv.ctype or "").lower() == "char *" and len(_dim_parts(lv.dim)) == 1:
                        idx = _convert_expr(m_lhs_char_elem.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        if lv.is_allocatable or _is_assumed_shape(lv.dim):
                            out.append(" " * indent + f"if ({cond}) assign_str_alloc(&{lhs_nm}[({idx}) - 1], {rhs});")
                            continue
                        if lv.char_len:
                            out.append(" " * indent + f"if ({cond}) assign_str({lhs_nm}[({idx}) - 1], {_simplify_int_expr_text(lv.char_len)}, {rhs});")
                            continue
                m_lhs_char = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
                if m_lhs_char:
                    lhs_nm = m_lhs_char.group(1).lower()
                    lv = vars_map.get(lhs_nm)
                    if lv is not None and (lv.ctype or '').lower() == 'char *' and (not lv.is_array):
                        if lv.is_allocatable or lv.is_pointer or not lv.char_len:
                            out.append(" " * indent + f"if ({cond}) assign_str_alloc(&{lhs_nm}, {rhs});")
                        else:
                            out.append(" " * indent + f"if ({cond}) assign_str({lhs_nm}, {_simplify_int_expr_text(lv.char_len)}, {rhs});")
                        continue
                lhs = _convert_expr(lhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                out.append(" " * indent + f"if ({cond}) {lhs} = {rhs};")
                continue
            if m_tail_call:
                callee = m_tail_call.group(1)
                fargs = _split_args_top_level(m_tail_call.group(2).strip()) if m_tail_call.group(2).strip() else []
                fargs = _normalize_actual_args(callee, fargs, proc_arg_names)
                modes = proc_arg_modes.get(callee.lower(), [])
                opts = proc_arg_optional.get(callee.lower(), [])
                ctypes = proc_arg_ctypes.get(callee.lower(), [])
                is_arrs = proc_arg_is_array.get(callee.lower(), [])
                extent_lists = proc_arg_extent_names.get(callee.lower(), [])
                cargs: List[str] = []
                pre_call: List[str] = []
                post_call: List[str] = []
                n_expected = max(len(modes), len(opts))
                for k in range(n_expected):
                    if k >= len(fargs):
                        cargs.append("NULL" if (k < len(opts) and opts[k]) else "0")
                        continue
                    a = fargs[k]
                    exts = extent_lists[k] if k < len(extent_lists) else []
                    extent_args, cexpr = _expand_assumed_shape_actual_arg(
                        a,
                        exts,
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    )
                    cargs.extend(extent_args)
                    mode = modes[k] if k < len(modes) else "value"
                    opt = opts[k] if k < len(opts) else False
                    cty = ctypes[k] if k < len(ctypes) else real_type
                    arrk = is_arrs[k] if k < len(is_arrs) else False
                    if mode == "value":
                        if _format_item_ctype(a, vars_map, real_type) == "string" and (not re.fullmatch(r"\s*[a-z_]\w*\s*", a, re.IGNORECASE)) and (not _is_fortran_string_literal(a.strip())):
                            tmp_nm = f"__arg_str_{k}"
                            pre_call.append(" " * (indent + 3) + f"char *{tmp_nm} = copy_str_s({cexpr});")
                            cargs.append(tmp_nm)
                            post_call.append(" " * (indent + 3) + f"if ({tmp_nm}) free({tmp_nm});")
                        else:
                            cargs.append(cexpr)
                    else:
                        m_id = re.match(r"^\s*([a-z_]\w*)\s*$", a, re.IGNORECASE)
                        if m_id:
                            nm = m_id.group(1).lower()
                            vv = vars_map.get(nm)
                            if vv is not None:
                                cargs.append(nm if vv.is_array else f"&{nm}")
                            elif arrk and cexpr.lstrip().startswith("&"):
                                cargs.append(cexpr)
                            else:
                                cargs.append(f"&(({cty}){{{cexpr}}})" if opt and (not arrk) else f"&({cexpr})")
                        else:
                            if arrk and cexpr.lstrip().startswith("&"):
                                cargs.append(cexpr)
                            else:
                                cargs.append(f"&(({cty}){{{cexpr}}})" if opt and (not arrk) else f"&({cexpr})")
                if pre_call or post_call:
                    out.append(" " * indent + f"if ({cond}) {{")
                    out.extend(pre_call)
                    out.append(" " * (indent + 3) + f"{callee}({', '.join(cargs)});")
                    out.extend(post_call)
                    out.append(" " * indent + "}")
                else:
                    out.append(" " * indent + f"if ({cond}) {callee}({', '.join(cargs)});")
                continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue
        m_call = re.match(r"^call\s+([a-z_]\w*)\s*\((.*)\)\s*$", code, re.IGNORECASE)
        if m_call:
            callee = m_call.group(1)
            fargs = _split_args_top_level(m_call.group(2).strip()) if m_call.group(2).strip() else []
            fargs = _normalize_actual_args(callee, fargs, proc_arg_names)
            if _ACTIVE_PROC_IS_ELEMENTAL.get(callee.lower(), False):
                modes_el = proc_arg_modes.get(callee.lower(), [])
                is_arrs_el = proc_arg_is_array.get(callee.lower(), [])
                ctypes_el = proc_arg_ctypes.get(callee.lower(), [])
                if fargs and all(not arr for arr in is_arrs_el[:len(fargs)]):
                    elem_setup: List[str] = []
                    elem_args: List[str] = []
                    loop_len: Optional[str] = None
                    loop_shape: Optional[tuple[str, ...]] = None
                    elemental_ok = True
                    for k, a in enumerate(fargs):
                        mode = modes_el[k] if k < len(modes_el) else "value"
                        cty = ctypes_el[k] if k < len(ctypes_el) else real_type
                        ctor_items = _array_constructor_items(a)
                        if ctor_items is not None:
                            if mode != "value":
                                elemental_ok = False
                                break
                            ctor_cty = _array_constructor_ctype(ctor_items, vars_map, real_type)
                            base_cty = "int" if ctor_cty == "logical" else ("char *" if ctor_cty == "string" else ctor_cty)
                            tmp_nm = f"__elem_arr_{k}"
                            init = ", ".join(
                                _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                for it in ctor_items
                            )
                            elem_setup.append(" " * indent + f"{base_cty} {tmp_nm}[] = {{{init}}};")
                            cur_len = str(len(ctor_items))
                            cur_shape = (cur_len.replace(" ", "").lower(),)
                            if loop_len is None:
                                loop_len = cur_len
                                loop_shape = cur_shape
                            elif loop_shape != cur_shape:
                                elemental_ok = False
                                break
                            elem_args.append(f"{tmp_nm}[i_el]")
                            continue
                        m_id = re.match(r"^\s*([a-z_]\w*)\s*$", a, re.IGNORECASE)
                        if m_id:
                            nm = m_id.group(1).lower()
                            vv = vars_map.get(nm)
                            if vv is not None and vv.is_array:
                                dparts = _resolved_dim_parts(vv, nm, assumed_extents)
                                shape_parts = tuple(
                                    _convert_expr(dp, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names).replace(" ", "").lower()
                                    for dp in dparts
                                )
                                cur_len = _dim_product_from_parts(dparts, vars_map, real_type, byref_scalars, assumed_extents)
                                if loop_len is None:
                                    loop_len = cur_len
                                    loop_shape = shape_parts
                                elif loop_shape != shape_parts:
                                    elemental_ok = False
                                    break
                                elem_args.append(f"{nm}[i_el]" if mode == "value" else f"&{nm}[i_el]")
                                continue
                            if vv is not None:
                                elem_args.append(nm if mode == "value" else f"&{nm}")
                                continue
                        cexpr = _convert_expr(a, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        if mode == "value":
                            elem_args.append(cexpr)
                        else:
                            elem_args.append(f"&(({cty}){{{cexpr}}})")
                    if elemental_ok and loop_len is not None:
                        out.append(" " * indent + "{")
                        out.extend(elem_setup)
                        out.append(" " * indent + f"for (int i_el = 0; i_el < ({loop_len}); ++i_el) {{")
                        out.append(" " * (indent + 3) + f"{callee}({', '.join(elem_args)});")
                        out.append(" " * indent + "}")
                        out.append(" " * indent + "}")
                        continue
            if callee.lower() == "rng_seed" and len(fargs) >= 1:
                seed_c = _convert_expr(fargs[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                out.append(" " * indent + f"rng_seed({seed_c});")
                continue
            if callee.lower() == "fill_runif_1d" and len(fargs) >= 1:
                arr_raw = fargs[0].strip()
                m_arr = re.match(r"^([a-z_]\w*)$", arr_raw, re.IGNORECASE)
                if m_arr:
                    arr_nm = m_arr.group(1).lower()
                    av = vars_map.get(arr_nm)
                    if av is not None and av.is_array:
                        dparts = _resolved_dim_parts(av, arr_nm, assumed_extents)
                        if len(dparts) == 1:
                            n1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            out.append(" " * indent + f"fill_runif_1d({n1}, {arr_nm});")
                            continue
            if callee.lower() == "get_command_argument" and len(fargs) >= 2:
                idx_c = _convert_expr(fargs[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                tgt_raw = fargs[1].strip().lower()
                tv = vars_map.get(tgt_raw)
                if tv is not None and (tv.ctype or "").lower() == "char *" and (not tv.is_array) and tv.char_len:
                    tlen = _simplify_int_expr_text(tv.char_len)
                    guard = f'((({idx_c}) >= 0) && (({idx_c}) < argc))'
                    if re.fullmatch(r"\s*[0-9]+\s*", idx_c) and int(idx_c.strip()) >= 0:
                        guard = f'(({idx_c}) < argc)'
                    out.append(" " * indent + f'assign_str({tgt_raw}, {tlen}, {guard} ? argv[{idx_c}] : "");')
                    continue
            modes = proc_arg_modes.get(callee.lower(), [])
            opts = proc_arg_optional.get(callee.lower(), [])
            ctypes = proc_arg_ctypes.get(callee.lower(), [])
            is_arrs = proc_arg_is_array.get(callee.lower(), [])
            array_byref = proc_arg_array_byref.get(callee.lower(), [])
            extent_lists = proc_arg_extent_names.get(callee.lower(), [])
            formal_names = proc_arg_names.get(callee.lower(), [])
            cargs: List[str] = []
            pre_call: List[str] = []
            post_call: List[str] = []
            n_expected = max(len(modes), len(opts))
            for k in range(n_expected):
                if k >= len(fargs):
                    if k < len(opts) and opts[k]:
                        cargs.append("NULL")
                        continue
                    cargs.append("0")
                    continue
                a = fargs[k]
                exts = extent_lists[k] if k < len(extent_lists) else []
                extent_args, cexpr = _expand_assumed_shape_actual_arg(
                    a,
                    exts,
                    vars_map,
                    real_type,
                    byref_scalars,
                    assumed_extents,
                    proc_arg_extent_names,
                )
                cargs.extend(extent_args)
                mode = modes[k] if k < len(modes) else "value"
                opt = opts[k] if k < len(opts) else False
                cty = ctypes[k] if k < len(ctypes) else real_type
                arrk = is_arrs[k] if k < len(is_arrs) else False
                if mode == "value":
                    if _format_item_ctype(a, vars_map, real_type) == "string" and (not re.fullmatch(r"\s*[a-z_]\w*\s*", a, re.IGNORECASE)) and (not _is_fortran_string_literal(a.strip())):
                        tmp_nm = f"__arg_str_{k}"
                        pre_call.append(" " * indent + f"char *{tmp_nm} = copy_str_s({cexpr});")
                        cargs.append(tmp_nm)
                        post_call.append(" " * indent + f"if ({tmp_nm}) free({tmp_nm});")
                    else:
                        cargs.append(cexpr)
                else:
                    m_id = re.match(r"^\s*([a-z_]\w*)\s*$", a, re.IGNORECASE)
                    if m_id:
                        nm = m_id.group(1).lower()
                        vv = vars_map.get(nm)
                        if vv is not None:
                            if vv.is_array:
                                byref_arr = array_byref[k] if k < len(array_byref) else False
                                if byref_arr:
                                    cargs.append(f"&{nm}")
                                    formal_nm = formal_names[k] if k < len(formal_names) else nm
                                    rank = max(1, len(_dim_parts(vv.dim)))
                                    for loc_en, glob_en in zip(_alloc_extent_names(nm, rank), _dummy_array_extent_names(callee.lower(), formal_nm, rank)):
                                        post_call.append(" " * indent + f"{loc_en} = {glob_en};")
                                else:
                                    cargs.append(nm)
                            elif nm in byref_scalars:
                                cargs.append(nm)
                            else:
                                cargs.append(f"&{nm}")
                        elif arrk and cexpr.lstrip().startswith("&"):
                            cargs.append(cexpr)
                        else:
                            cargs.append(f"&(({cty}){{{cexpr}}})" if opt and (not arrk) else f"&({cexpr})")
                    else:
                        if arrk and cexpr.lstrip().startswith("&"):
                            cargs.append(cexpr)
                        else:
                            cargs.append(f"&(({cty}){{{cexpr}}})" if opt and (not arrk) else f"&({cexpr})")
            out.extend(pre_call)
            out.append(" " * indent + f"{callee}({', '.join(cargs)});")
            out.extend(post_call)
            continue

        items: List[str] = []
        m_print_any = re.match(r'^print\s+(.+)$', code, re.IGNORECASE)
        if m_print_any:
            print_tail = m_print_any.group(1).strip()
            parts_print = [x.strip() for x in _split_args_top_level(print_tail) if x.strip()]
            if len(parts_print) >= 2 and parts_print[0] != '*':
                fmt_raw = parts_print[0].strip()
                items = parts_print[1:]
                fmt_text = _resolved_format_text(fmt_raw, vars_map)
                if fmt_text is not None:
                    fmt_clean = _unquote_fortran_string_literal(fmt_text).strip().lower()
                    if len(items) == 1:
                        m_fmt_char = re.match(r'^\(\*\(a(\d+)\)\)\s*$', fmt_clean, re.IGNORECASE)
                        m_arr_char = re.match(r'^\s*([a-z_]\w*)\s*$', items[0], re.IGNORECASE)
                        if m_fmt_char and m_arr_char:
                            an = m_arr_char.group(1).lower()
                            av = vars_map.get(an)
                            if av is not None and av.is_array and (av.ctype or "").lower() == "char *" and len(_resolved_dim_parts(av, an, assumed_extents)) == 1:
                                width = int(m_fmt_char.group(1))
                                npr = _dim_product_from_parts(
                                    _resolved_dim_parts(av, an, assumed_extents),
                                    vars_map,
                                    real_type,
                                    byref_scalars,
                                    assumed_extents,
                                )
                                out.append(" " * indent + f"for (int __i_fmt = 0; __i_fmt < {npr}; ++__i_fmt) {{")
                                out.append(" " * (indent + 3) + f'printf("%{width}s", {an}[__i_fmt]);')
                                out.append(" " * indent + "}")
                                out.append(" " * indent + 'printf("\\n");')
                                continue
                    if fmt_clean == '(a)' and len(items) == 1 and _emit_string_concat_expr(out, indent, items[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names, newline_each=True):
                        continue
                    if len(items) == 1 and _emit_implied_do_formatted_output(out, indent, fmt_text, items[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                        continue
                    if _emit_basic_formatted_items_output(out, indent, fmt_text, items, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                        continue

        if re.match(r"^print\s*\*\s*$", code, re.IGNORECASE):
            out.append(" " * indent + 'printf("\\n");')
            continue
        m_print = re.match(r"^print\s*\*\s*,?\s*(.*)$", code, re.IGNORECASE)
        if m_print:
            raw_items = [x.strip() for x in _split_args_top_level(m_print.group(1)) if x.strip()]
            items: List[str] = []
            for rit in raw_items:
                items.append(rit)
            if not items:
                out.append(" " * indent + 'printf("\\n");')
                continue
            changed_ctor_items = True
            while changed_ctor_items:
                changed_ctor_items = False
                flat_items: List[str] = []
                for it0 in items:
                    ctor_items0 = _array_constructor_items(it0)
                    if ctor_items0 is not None:
                        flat_items.extend([x.strip() for x in ctor_items0 if x.strip()])
                        changed_ctor_items = True
                    else:
                        flat_items.append(it0)
                items = flat_items
            if not items:
                out.append(" " * indent + 'printf("\\n");')
                continue
            if _emit_list_directed_loc_intrinsic(
                out,
                indent,
                items,
                vars_map,
                real_type,
                byref_scalars,
                assumed_extents,
                proc_arg_extent_names,
            ):
                continue
            if len(items) == 1:
                m_minmax_print = re.match(r"^(minval|maxval)\s*\((.*)\)\s*$", items[0], re.IGNORECASE)
                if m_minmax_print:
                    kind_mm = m_minmax_print.group(1).lower()
                    arg_mm = m_minmax_print.group(2).strip()
                    sec_expr_mm = _minmax_section_scalar_expr(
                        kind_mm,
                        arg_mm,
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    )
                    if sec_expr_mm is not None:
                        out.append(" " * indent + f'printf("%g\\n", {sec_expr_mm});')
                        continue
                    mm_expr = _convert_expr(items[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    if mm_expr != items[0]:
                        out.append(" " * indent + f'printf("%g\\n", {mm_expr});')
                        continue
            early_intr_items: List[tuple[str, str]] = []
            early_intr_supported = True
            early_saw_intr = False
            for pit in items:
                m_intr_early = re.match(r"^(size|rank|shape|lbound|ubound)\s*\((.*)\)\s*$", pit, re.IGNORECASE)
                if m_intr_early:
                    early_saw_intr = True
                    vals_early = _shape_like_intrinsic_values(
                        m_intr_early.group(1).lower(),
                        [x.strip() for x in _split_args_top_level(m_intr_early.group(2)) if x.strip()],
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    )
                    if vals_early is None:
                        early_intr_supported = False
                        break
                    for vv_early in vals_early:
                        early_intr_items.append(("int", vv_early))
                    continue
                for tok in re.findall(r"\b[a-z_]\w*\b", _strip_comment(pit), flags=re.IGNORECASE):
                    vv_tok = vars_map.get(tok.lower())
                    if vv_tok is not None and vv_tok.is_array:
                        early_intr_supported = False
                        break
                if not early_intr_supported:
                    break
                early_intr_items.append(
                    (
                        _format_item_ctype(pit, vars_map, real_type),
                        _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names),
                    )
                )
            if early_saw_intr and early_intr_supported:
                out.append(" " * indent + "{")
                out.append(" " * (indent + 3) + "int __first = 1;")
                for cty_early, cexpr_early in early_intr_items:
                    if cty_early == "string":
                        out.append(" " * (indent + 3) + f'printf("%s%s", __first ? "" : " ", {cexpr_early});')
                    elif cty_early == "int":
                        out.append(" " * (indent + 3) + f'printf("%s%d", __first ? "" : " ", {cexpr_early});')
                    else:
                        out.append(" " * (indent + 3) + f'printf("%s%g", __first ? "" : " ", {cexpr_early});')
                    out.append(" " * (indent + 3) + "__first = 0;")
                out.append(" " * (indent + 3) + 'printf("\\n");')
                out.append(" " * indent + "}")
                continue
            if len(items) >= 2:
                last_sec = items[-1].strip()
                m_last_row = re.match(r"^([a-z_]\w*)\s*\(\s*([^,\)]*)\s*,\s*:\s*\)$", last_sec, re.IGNORECASE)
                m_last_col = re.match(r"^([a-z_]\w*)\s*\(\s*:\s*,\s*([^,\)]*)\s*\)$", last_sec, re.IGNORECASE)
                m_last_sec = m_last_row or m_last_col
                if m_last_sec:
                    an_last = m_last_sec.group(1).lower()
                    av_last = vars_map.get(an_last)
                    if av_last is not None and av_last.is_array:
                        dparts_last = _resolved_dim_parts(av_last, an_last, assumed_extents)
                        if len(dparts_last) == 2:
                            prefix_has_array = any(
                                (
                                    re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE)
                                    and vars_map.get(re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE).group(1).lower()) is not None
                                    and vars_map.get(re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE).group(1).lower()).is_array
                                )
                                for pit in items[:-1]
                            )
                            if not prefix_has_array:
                                d1_last = _convert_expr(dparts_last[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                d2_last = _convert_expr(dparts_last[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                cty_last = (av_last.ctype or real_type).lower()
                                efmt_last = "%d" if cty_last == "int" else "%g"
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                for pit in items[:-1]:
                                    cty_pre = _format_item_ctype(pit, vars_map, real_type)
                                    cexpr_pre = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    if cty_pre == "string":
                                        out.append(" " * (indent + 3) + f'printf("%s%s", __first ? "" : " ", {cexpr_pre});')
                                    elif cty_pre == "int":
                                        out.append(" " * (indent + 3) + f'printf("%s%d", __first ? "" : " ", {cexpr_pre});')
                                    else:
                                        out.append(" " * (indent + 3) + f'printf("%s%g", __first ? "" : " ", {cexpr_pre});')
                                    out.append(" " * (indent + 3) + "__first = 0;")
                                if m_last_row:
                                    row_last = _convert_expr(m_last_row.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * (indent + 3) + f"for (int j_pr = 0; j_pr < {d2_last}; ++j_pr) {{")
                                    out.append(" " * (indent + 6) + f'printf("%s{efmt_last}", __first ? "" : " ", {an_last}[(({row_last}) - 1) + ({d1_last}) * j_pr]);')
                                else:
                                    col_last = _convert_expr(m_last_col.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {d1_last}; ++i_pr) {{")
                                    out.append(" " * (indent + 6) + f'printf("%s{efmt_last}", __first ? "" : " ", {an_last}[i_pr + ({d1_last}) * ((({col_last})) - 1)]);')
                                out.append(" " * (indent + 6) + "__first = 0;")
                                out.append(" " * (indent + 3) + "}")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
            if len(items) == 1 and ("//" not in items[0]) and _is_fortran_string_literal(items[0].strip()):
                lit = _unquote_fortran_string_literal(items[0].strip()).replace("\\", "\\\\").replace('"', '\\"')
                out.append(" " * indent + f'printf("%s\\n", "{lit}");')
                continue
                if len(items) >= 2:
                    last_simple = items[-1].strip()
                    m_last_arr = re.match(r"^([a-z_]\w*)$", last_simple, re.IGNORECASE)
                if m_last_arr:
                    an_last = m_last_arr.group(1).lower()
                    av_last = vars_map.get(an_last)
                    prefix_has_array = any(
                        (
                            re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE)
                            and vars_map.get(re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE).group(1).lower()) is not None
                            and vars_map.get(re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE).group(1).lower()).is_array
                        )
                        for pit in items[:-1]
                    )
                    if av_last is not None and av_last.is_array and (not prefix_has_array) and len(_resolved_dim_parts(av_last, an_last, assumed_extents)) == 1:
                        if av_last.is_allocatable or av_last.is_pointer:
                            npr_last = _dim_product_from_parts(
                                _resolved_dim_parts(av_last, an_last, assumed_extents),
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                            )
                        else:
                            npr_last = _dim_product_expr(av_last.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                        cty_last = (av_last.ctype or real_type).lower()
                        efmt_last = "%d" if cty_last == "int" else "%g"
                        out.append(" " * indent + "{")
                        out.append(" " * (indent + 3) + "int __first = 1;")
                        for pit in items[:-1]:
                            cty_pre = _format_item_ctype(pit, vars_map, real_type)
                            cexpr_pre = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            if cty_pre == "string":
                                out.append(" " * (indent + 3) + f'printf("%s%s", __first ? "" : " ", {cexpr_pre});')
                            elif cty_pre == "int":
                                out.append(" " * (indent + 3) + f'printf("%s%d", __first ? "" : " ", {cexpr_pre});')
                            else:
                                out.append(" " * (indent + 3) + f'printf("%s%g", __first ? "" : " ", {cexpr_pre});')
                            out.append(" " * (indent + 3) + "__first = 0;")
                        out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {npr_last}; ++i_pr) {{")
                        out.append(" " * (indent + 6) + f'printf("%s{efmt_last}", __first ? "" : " ", {an_last}[i_pr]);')
                        out.append(" " * (indent + 6) + "__first = 0;")
                        out.append(" " * (indent + 3) + "}")
                        out.append(" " * (indent + 3) + 'printf("\\n");')
                        out.append(" " * indent + "}")
                        continue
                if len(items) >= 2:
                    mixed_parts: List[tuple[str, str]] = []
                    mixed_supported = True
                    for pit in items:
                        if _is_fortran_string_literal(pit.strip()):
                            lit = _unquote_fortran_string_literal(pit.strip()).replace("\\", "\\\\").replace('"', '\\"')
                            mixed_parts.append(("string", f'"{lit}"'))
                            continue
                        m_trim = re.match(r"^\s*trim\s*\(\s*([a-z_]\w*)\s*\)\s*$", pit, re.IGNORECASE)
                        if m_trim:
                            nm_trim = m_trim.group(1).lower()
                            mixed_parts.append(("trim_string", nm_trim))
                            continue
                        m_intr_mix = re.match(r"^(size|rank|shape|lbound|ubound)\s*\((.*)\)\s*$", pit, re.IGNORECASE)
                        if m_intr_mix:
                            inm = m_intr_mix.group(1).lower()
                            iargs = [x.strip() for x in _split_args_top_level(m_intr_mix.group(2)) if x.strip()]
                            if not iargs:
                                mixed_supported = False
                                break
                            vals0 = _shape_like_intrinsic_values(
                                inm,
                                iargs,
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                                proc_arg_extent_names,
                            )
                            if vals0 is None:
                                mixed_supported = False
                                break
                            mixed_parts.extend(("int", vv) for vv in vals0)
                            continue
                        m_simple = re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE)
                        if m_simple:
                            vv = vars_map.get(m_simple.group(1).lower())
                            if vv is not None and vv.is_array:
                                mixed_supported = False
                                break
                        toks_p = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(pit), flags=re.IGNORECASE)}
                        has_bad_array_ref = False
                        for t in toks_p:
                            vv = vars_map.get(t)
                            if vv is None or (not vv.is_array):
                                continue
                            if re.search(rf"\b{re.escape(t)}\s*\(", pit, flags=re.IGNORECASE):
                                continue
                            if re.match(r"^\s*(sum|minval|maxval|product|any|all|count)\s*\(", pit, re.IGNORECASE) and not re.search(r"\bdim\s*=", pit, re.IGNORECASE):
                                continue
                            has_bad_array_ref = True
                            break
                        if has_bad_array_ref:
                            mixed_supported = False
                            break
                        cty_p = _format_item_ctype(pit, vars_map, real_type)
                        cexpr_p = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        mixed_parts.append((cty_p, cexpr_p))
                    if mixed_supported and mixed_parts:
                        out.append(" " * indent + "{")
                        out.append(" " * (indent + 3) + "int __first = 1;")
                        all_string_like = all(cty_p in {"string", "trim_string"} for cty_p, _ in mixed_parts)
                        sep_expr = '""' if all_string_like else '" "'
                        for cty_p, cexpr_p in mixed_parts:
                            _emit_list_directed_scalar_printf(
                                out,
                                indent + 3,
                                cexpr_p,
                                cty_p,
                                vars_map,
                                real_type,
                                prefix_expr=f'__first ? "" : {sep_expr}',
                            )
                            out.append(" " * (indent + 3) + "__first = 0;")
                        out.append(" " * (indent + 3) + 'printf("\\n");')
                        out.append(" " * indent + "}")
                        continue
                expr_last = items[-1]
                if len(re.findall(r"(?i)\bsum\s*\(", expr_last)) == 1:
                    m_sum_dim_tail = re.match(
                        r"^(.*?)(sum\s*\(\s*([a-z_]\w*)\s*,\s*(?:dim\s*=\s*)?([0-9]+)\s*\))(.*)$",
                        expr_last,
                        re.IGNORECASE,
                    )
                    if m_sum_dim_tail:
                        pre = m_sum_dim_tail.group(1) or ""
                        an = m_sum_dim_tail.group(3).lower()
                        try:
                            dim_no = int(m_sum_dim_tail.group(4))
                        except Exception:
                            dim_no = None
                        post = m_sum_dim_tail.group(5) or ""
                        av = vars_map.get(an)
                        prefix_items = items[:-1]
                        if av is not None and av.is_array and dim_no is not None:
                            dparts = _resolved_dim_parts(av, an, assumed_extents)
                            rank = len(dparts)
                            if rank in {2, 3} and 1 <= dim_no <= rank and all(not (vars_map.get(it.lower()) and vars_map[it.lower()].is_array) for it in [x.strip() for x in prefix_items if re.fullmatch(r"[a-z_]\w*", x.strip(), re.IGNORECASE)]):
                                d = [
                                    _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    for k in range(rank)
                                ]
                                tmp_var = "__red"
                                vars_map_red = dict(vars_map)
                                vars_map_red[tmp_var] = Var(av.ctype or real_type)
                                expr_red = f"{pre}{tmp_var}{post}"
                                cexpr_red = _convert_expr(expr_red, vars_map_red, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                expr_cty = _format_item_ctype(expr_red, vars_map_red, real_type)
                                efmt_red = "%d" if expr_cty == "int" else "%g"
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                out.append(" " * (indent + 3) + f"{av.ctype} {tmp_var};")
                                for pit in prefix_items:
                                    cty_pre = _format_item_ctype(pit, vars_map, real_type)
                                    cexpr_pre = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    if cty_pre == "string":
                                        out.append(" " * (indent + 3) + f'printf("%s%s", __first ? "" : " ", {cexpr_pre});')
                                    elif cty_pre == "int":
                                        out.append(" " * (indent + 3) + f'printf("%s%d", __first ? "" : " ", {cexpr_pre});')
                                    else:
                                        out.append(" " * (indent + 3) + f'printf("%s%g", __first ? "" : " ", {cexpr_pre});')
                                    out.append(" " * (indent + 3) + "__first = 0;")
                                if rank == 2 and dim_no == 1:
                                    out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                    out.append(" " * (indent + 6) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                    out.append(" " * (indent + 6) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 6) + "__first = 0;")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 2 and dim_no == 2:
                                    out.append(" " * (indent + 3) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                    out.append(" " * (indent + 6) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                    out.append(" " * (indent + 6) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 6) + "__first = 0;")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 3 and dim_no == 1:
                                    out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                    out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                    out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 9) + f"for (int i = 1; i <= {d[0]}; ++i) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 3 and dim_no == 2:
                                    out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                    out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                    out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 9) + f"for (int j = 1; j <= {d[1]}; ++j) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 3 and dim_no == 3:
                                    out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                    out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                    out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 9) + f"for (int k = 1; k <= {d[2]}; ++k) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                expanded_intr_items: List[tuple[str, str]] = []
                expandable_intrs = True
                saw_intr_like = False
                for pit in items:
                    m_intr_any = re.match(r"^(size|rank|shape|lbound|ubound)\s*\((.*)\)\s*$", pit, re.IGNORECASE)
                    if m_intr_any:
                        saw_intr_like = True
                        vals_any = _shape_like_intrinsic_values(
                            m_intr_any.group(1).lower(),
                            [x.strip() for x in _split_args_top_level(m_intr_any.group(2)) if x.strip()],
                            vars_map,
                            real_type,
                            byref_scalars,
                            assumed_extents,
                            proc_arg_extent_names,
                        )
                        if vals_any is None:
                            expandable_intrs = False
                            break
                        for vv_any in vals_any:
                            expanded_intr_items.append(("int", vv_any))
                        continue
                    for tok in re.findall(r"\b[a-z_]\w*\b", _strip_comment(pit), flags=re.IGNORECASE):
                        vv_tok = vars_map.get(tok.lower())
                        if vv_tok is not None and vv_tok.is_array:
                            expandable_intrs = False
                            break
                    if not expandable_intrs:
                        break
                    expanded_intr_items.append(
                        (
                            _format_item_ctype(pit, vars_map, real_type),
                            _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names),
                        )
                    )
                if saw_intr_like and expandable_intrs:
                    out.append(" " * indent + "{")
                    out.append(" " * (indent + 3) + "int __first = 1;")
                    for cty_any, cexpr_any in expanded_intr_items:
                        if cty_any == "string":
                            out.append(" " * (indent + 3) + f'printf("%s%s", __first ? "" : " ", {cexpr_any});')
                        elif cty_any == "int":
                            out.append(" " * (indent + 3) + f'printf("%s%d", __first ? "" : " ", {cexpr_any});')
                        else:
                            out.append(" " * (indent + 3) + f'printf("%s%g", __first ? "" : " ", {cexpr_any});')
                        out.append(" " * (indent + 3) + "__first = 0;")
                    out.append(" " * (indent + 3) + 'printf("\\n");')
                    out.append(" " * indent + "}")
                    continue
                scalar_only = True
                for pit in items:
                    for tok in re.findall(r"\b[a-z_]\w*\b", _strip_comment(pit), flags=re.IGNORECASE):
                        vv = vars_map.get(tok.lower())
                        if vv is not None and vv.is_array:
                            scalar_only = False
                            break
                    if not scalar_only:
                        break
                    if re.search(r"//|\b(sum|product|spread|pack|merge|shape|lbound|ubound|rank|size)\s*\(", pit, flags=re.IGNORECASE):
                        scalar_only = False
                        break
                if scalar_only:
                    fmts: List[str] = []
                    cargs: List[str] = []
                    ctypes_ld: List[str] = []
                    for it in items:
                        if (it.startswith('"') and it.endswith('"')) or (it.startswith("'") and it.endswith("'")):
                            content = it[1:-1].replace('\\', '\\\\').replace('"', '\\"')
                            cargs.append(f'"{content}"')
                            ctypes_ld.append('string')
                            fmts.append(_list_directed_scalar_fmt('string'))
                            continue
                        cit = _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        cargs.append(cit)
                        cty = _format_item_ctype(it, vars_map, real_type)
                        ctypes_ld.append(cty)
                        fmts.append(_list_directed_scalar_fmt(cty))
                    trail = '    ' if _list_directed_has_trailing_real(ctypes_ld) else ''
                    prefix = ' ' if ctypes_ld and all((ct or '').lower() == 'string' for ct in ctypes_ld) else ''
                    out.append(" " * indent + f'printf("{prefix}{"".join(fmts)}{trail}\\n", {", ".join(cargs)});')
                    continue
            if len(items) == 1:
                if _emit_string_concat_expr(out, indent, items[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names, list_directed_strings=True):
                    continue
                if '%' in items[0] and _emit_list_directed_component_array(out, indent, items[0], vars_map, real_type):
                    continue
                if _emit_list_directed_derived_expr(out, indent, items[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                    continue
                m_intr0 = re.match(r"^(size|rank|shape|lbound|ubound)\s*\((.*)\)\s*$", items[0], re.IGNORECASE)
                if m_intr0:
                    inm = m_intr0.group(1).lower()
                    iargs = [x.strip() for x in _split_args_top_level(m_intr0.group(2)) if x.strip()]
                    if iargs:
                        vals0 = _shape_like_intrinsic_values(
                            inm,
                            iargs,
                            vars_map,
                            real_type,
                            byref_scalars,
                            assumed_extents,
                            proc_arg_extent_names,
                        )
                        if vals0 is not None:
                            if len(vals0) == 1:
                                out.append(" " * indent + f'printf("%d\\n", {vals0[0]});')
                                continue
                            out.append(" " * indent + "{")
                            out.append(" " * (indent + 3) + "int __first = 1;")
                            for vv in vals0:
                                out.append(" " * (indent + 3) + f'printf("%s%d", __first ? "" : " ", {vv});')
                                out.append(" " * (indent + 3) + "__first = 0;")
                            out.append(" " * (indent + 3) + 'printf("\\n");')
                            out.append(" " * indent + "}")
                            continue
                m_vsub1 = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)\s*$", items[0], re.IGNORECASE)
                if m_vsub1:
                    an = m_vsub1.group(1).lower()
                    av = vars_map.get(an)
                    inner = m_vsub1.group(2).strip()
                    if av is not None and av.is_array and len(_resolved_dim_parts(av, an, assumed_extents)) == 1:
                        m_ctor_idx = re.match(r"^\[\s*(.*)\s*\]$", inner)
                        cty = (av.ctype or real_type).lower()
                        efmt = "%d" if cty == "int" else "%g"
                        if m_ctor_idx:
                            idx_items = [x.strip() for x in _split_args_top_level(m_ctor_idx.group(1)) if x.strip()]
                            out.append(" " * indent + "{")
                            out.append(" " * (indent + 3) + "int __first = 1;")
                            for iv in idx_items:
                                civ = _convert_expr(iv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                out.append(" " * (indent + 3) + f'printf("%s{efmt}", __first ? "" : " ", {an}[({civ}) - 1]);')
                                out.append(" " * (indent + 3) + "__first = 0;")
                            out.append(" " * (indent + 3) + 'printf("\\n");')
                            out.append(" " * indent + "}")
                            continue
                        m_idx_arr = re.match(r"^([a-z_]\w*)$", inner, re.IGNORECASE)
                        if m_idx_arr:
                            idxn = m_idx_arr.group(1).lower()
                            ivv = vars_map.get(idxn)
                            if ivv is not None and ivv.is_array:
                                if ivv.is_allocatable:
                                    nidx = _dim_product_from_parts(
                                        _resolved_dim_parts(ivv, idxn, assumed_extents),
                                        vars_map,
                                        real_type,
                                        byref_scalars,
                                        assumed_extents,
                                    )
                                else:
                                    nidx = _dim_product_expr(ivv.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                out.append(" " * indent + f"for (int i_pr = 0; i_pr < {nidx}; ++i_pr) {{")
                                out.append(" " * (indent + 3) + f"int __iv = {idxn}[i_pr];")
                                out.append(" " * (indent + 3) + f'printf("{efmt}%s", {an}[__iv - 1], (i_pr + 1 < {nidx}) ? " " : "\\n");')
                                out.append(" " * indent + "}")
                                continue
                m_sec = _match_whole_name_call(items[0])
                if m_sec:
                    an = m_sec[0].lower()
                    av = vars_map.get(an)
                    if av is not None and av.is_array:
                        idx_parts = _split_args_top_level(m_sec[1])
                        dparts = _resolved_dim_parts(av, an, assumed_extents)
                        rank = len(dparts)
                        if rank in {2, 3} and len(idx_parts) == rank:
                            cty = (av.ctype or real_type).lower()
                            efmt = "%d" if cty == "int" else "%g"
                            dimc = [
                                _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                for k in range(rank)
                            ]

                            def _parse_dim_spec(txt: str, dflt_hi: str) -> dict:
                                t = txt.strip()
                                m_ctor = re.match(r"^\[\s*(.*)\s*\]$", t)
                                if m_ctor:
                                    vals = [x.strip() for x in _split_args_top_level(m_ctor.group(1)) if x.strip()]
                                    cvals = [
                                        _convert_expr(vv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        for vv in vals
                                    ]
                                    return {"kind": "vec", "vals": cvals}
                                if ":" in t:
                                    sp = _split_colon_top_level(t)
                                    lo = _convert_expr((sp[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    hi = _convert_expr((sp[1] or dflt_hi).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    st = _convert_expr((sp[2] if len(sp) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    return {"kind": "sec", "lo": lo, "hi": hi, "st": st}
                                val = _convert_expr(t, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                return {"kind": "scalar", "val": val}

                            specs = [_parse_dim_spec(idx_parts[k], dimc[k]) for k in range(rank)]
                            if any(sp["kind"] != "scalar" for sp in specs):
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                idx_map: Dict[int, str] = {}

                                def _lin_expr() -> str:
                                    i1 = idx_map.get(1, "1")
                                    lin = f"(({i1}) - 1)"
                                    if rank >= 2:
                                        i2 = idx_map.get(2, "1")
                                        lin = f"{lin} + ({dimc[0]}) * (({i2}) - 1)"
                                    if rank >= 3:
                                        i3 = idx_map.get(3, "1")
                                        lin = f"{lin} + ({dimc[0]}) * ({dimc[1]}) * (({i3}) - 1)"
                                    return lin

                                def _emit_dim(dim_k: int, ind: int) -> None:
                                    if dim_k < 1:
                                        lin = _lin_expr()
                                        out.append(" " * ind + f'printf("%s{efmt}", __first ? "" : " ", {an}[{lin}]);')
                                        out.append(" " * ind + "__first = 0;")
                                        return
                                    sp = specs[dim_k - 1]
                                    if sp["kind"] == "scalar":
                                        idx_map[dim_k] = sp["val"]
                                        _emit_dim(dim_k - 1, ind)
                                        return
                                    if sp["kind"] == "vec":
                                        for vv in sp["vals"]:
                                            idx_map[dim_k] = vv
                                            _emit_dim(dim_k - 1, ind)
                                        return
                                    vnm = f"__i{dim_k}"
                                    idx_map[dim_k] = vnm
                                    out.append(" " * ind + f"for (int {vnm} = {sp['lo']}; ({sp['st']}) > 0 ? {vnm} <= {sp['hi']} : {vnm} >= {sp['hi']}; {vnm} += {sp['st']}) {{")
                                    _emit_dim(dim_k - 1, ind + 3)
                                    out.append(" " * ind + "}")

                                _emit_dim(rank, indent + 3)
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                        if len(idx_parts) == 2 and len(dparts) >= 2:
                            d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            cty = (av.ctype or real_type).lower()
                            efmt = "%d" if cty == "int" else "%g"
                            m_v0_ctor = re.match(r"^\[\s*(.*)\s*\]$", idx_parts[0].strip())
                            m_v1_ctor = re.match(r"^\[\s*(.*)\s*\]$", idx_parts[1].strip())
                            if m_v0_ctor or m_v1_ctor:
                                def _dim_span(idx_txt: str, dflt_hi: str) -> tuple[str, str, str]:
                                    idx_txt = idx_txt.strip()
                                    if ":" in idx_txt:
                                        sp = _split_colon_top_level(idx_txt)
                                        lo = _convert_expr((sp[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        hi = _convert_expr((sp[1] or dflt_hi).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        st = _convert_expr((sp[2] if len(sp) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        return lo, hi, st
                                    s = _convert_expr(idx_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    return s, s, "1"
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                if m_v0_ctor and m_v1_ctor:
                                    v0 = [x.strip() for x in _split_args_top_level(m_v0_ctor.group(1)) if x.strip()]
                                    v1 = [x.strip() for x in _split_args_top_level(m_v1_ctor.group(1)) if x.strip()]
                                    for jv in v1:
                                        cj = _convert_expr(jv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        for iv in v0:
                                            ci = _convert_expr(iv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                            out.append(" " * (indent + 3) + f'printf("%s{efmt}", __first ? "" : " ", {an}[(({ci}) - 1) + ({d1}) * (({cj}) - 1)]);')
                                            out.append(" " * (indent + 3) + "__first = 0;")
                                elif m_v0_ctor:
                                    v0 = [x.strip() for x in _split_args_top_level(m_v0_ctor.group(1)) if x.strip()]
                                    j_lo, j_hi, j_st = _dim_span(idx_parts[1], d2)
                                    out.append(" " * (indent + 3) + f"for (int j_pr = {j_lo}; ({j_st}) > 0 ? j_pr <= {j_hi} : j_pr >= {j_hi}; j_pr += {j_st}) {{")
                                    for iv in v0:
                                        ci = _convert_expr(iv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", {an}[(({ci}) - 1) + ({d1}) * (j_pr - 1)]);')
                                        out.append(" " * (indent + 6) + "__first = 0;")
                                    out.append(" " * (indent + 3) + "}")
                                else:
                                    i_lo, i_hi, i_st = _dim_span(idx_parts[0], d1)
                                    v1 = [x.strip() for x in _split_args_top_level(m_v1_ctor.group(1)) if x.strip()]
                                    for jv in v1:
                                        cj = _convert_expr(jv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        out.append(" " * (indent + 3) + f"for (int i_pr = {i_lo}; ({i_st}) > 0 ? i_pr <= {i_hi} : i_pr >= {i_hi}; i_pr += {i_st}) {{")
                                        out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", {an}[(i_pr - 1) + ({d1}) * (({cj}) - 1)]);')
                                        out.append(" " * (indent + 6) + "__first = 0;")
                                        out.append(" " * (indent + 3) + "}")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                            sec0 = ":" in idx_parts[0]
                            sec1 = ":" in idx_parts[1]
                            if sec0 or sec1:
                                if sec0:
                                    sp0 = _split_colon_top_level(idx_parts[0].strip())
                                    if len(sp0) not in {2, 3}:
                                        sp0 = [idx_parts[0].strip(), idx_parts[0].strip(), "1"]
                                else:
                                    sp0 = [idx_parts[0].strip(), idx_parts[0].strip(), "1"]
                                if sec1:
                                    sp1 = _split_colon_top_level(idx_parts[1].strip())
                                    if len(sp1) not in {2, 3}:
                                        sp1 = [idx_parts[1].strip(), idx_parts[1].strip(), "1"]
                                else:
                                    sp1 = [idx_parts[1].strip(), idx_parts[1].strip(), "1"]
                                i1_lo = _convert_expr((sp0[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                i1_hi = _convert_expr((sp0[1] or d1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                i1_st = _convert_expr((sp0[2] if len(sp0) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                i2_lo = _convert_expr((sp1[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                i2_hi = _convert_expr((sp1[1] or d2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                i2_st = _convert_expr((sp1[2] if len(sp1) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                out.append(" " * (indent + 3) + f"for (int j_pr = {i2_lo}; ({i2_st}) > 0 ? j_pr <= {i2_hi} : j_pr >= {i2_hi}; j_pr += {i2_st}) {{")
                                out.append(" " * (indent + 6) + f"for (int i_pr = {i1_lo}; ({i1_st}) > 0 ? i_pr <= {i1_hi} : i_pr >= {i1_hi}; i_pr += {i1_st}) {{")
                                out.append(" " * (indent + 9) + f"int __lin = (i_pr - 1) + ({d1}) * (j_pr - 1);")
                                out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", {an}[__lin]);')
                                out.append(" " * (indent + 9) + "__first = 0;")
                                out.append(" " * (indent + 6) + "}")
                                out.append(" " * (indent + 3) + "}")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                m_arr = re.match(r"^([a-z_]\w*)$", items[0], re.IGNORECASE)
                if m_arr:
                    an = m_arr.group(1).lower()
                    av = vars_map.get(an)
                    if av is not None and _emit_list_directed_derived_var(out, indent, an, vars_map, real_type):
                        continue
                    if av is not None and av.is_array:
                        if av.is_allocatable or av.is_pointer:
                            npr = _dim_product_from_parts(
                                _resolved_dim_parts(av, an, assumed_extents),
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                            )
                        else:
                            npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                        cty = (av.ctype or real_type).lower()
                        if cty == "char *":
                            out.append(" " * indent + "{")
                            out.append(" " * (indent + 3) + "int __first = 1;")
                            out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {npr}; ++i_pr) {{")
                            out.append(" " * (indent + 6) + f'printf("%s%.*s", __first ? "" : " ", len_trim_s({an}[i_pr]), {an}[i_pr]);')
                            out.append(" " * (indent + 6) + "__first = 0;")
                            out.append(" " * (indent + 3) + "}")
                            out.append(" " * (indent + 3) + 'printf("\\n");')
                            out.append(" " * indent + "}")
                        else:
                            _emit_list_directed_1d_value_stream(out, indent, f"{an}[i_pr]", cty, f"for (int i_pr = 0; i_pr < {npr}; ++i_pr)", vars_map)
                        continue
                        continue
                # Array expression print, e.g. print*, 10*x
                expr0 = items[0]
                m_merge_call = re.match(r"^merge\s*\((.*)\)\s*$", expr0, re.IGNORECASE)
                if m_merge_call:
                    margs = [x.strip() for x in _split_args_top_level(m_merge_call.group(1)) if x.strip()]
                    if len(margs) >= 3:
                        toks_m = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(expr0), flags=re.IGNORECASE)}
                        arrs_m = [t for t in sorted(toks_m) if t in vars_map and vars_map[t].is_array]
                        if arrs_m and not any(re.search(rf"\b{re.escape(a)}\s*\(", expr0, flags=re.IGNORECASE) for a in arrs_m):
                            base = vars_map.get(arrs_m[0])
                            compatible = base is not None and all((vars_map.get(a) is not None and vars_map.get(a).dim == base.dim) for a in arrs_m)
                            if compatible and base is not None:
                                if base.is_allocatable and len(_dim_parts(base.dim)) == 1:
                                    npr = _alloc_len_name(arrs_m[0])
                                else:
                                    npr = _dim_product_expr(base.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                expr_i = expr0
                                for a in sorted(arrs_m, key=len, reverse=True):
                                    expr_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_pr]", expr_i, flags=re.IGNORECASE)
                                cit = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                expr_cty = _var_render_ctype(base, real_type) if len(arrs_m) == 1 and expr0.strip().lower() == arrs_m[0] else _format_item_ctype(expr0, vars_map, real_type)
                                _emit_list_directed_1d_value_stream(out, indent, cit, expr_cty, f"for (int i_pr = 0; i_pr < {npr}; ++i_pr)", vars_map)
                                continue
                m_pack_call = re.match(r"^pack\s*\((.*)\)\s*$", expr0, re.IGNORECASE)
                if m_pack_call:
                    pargs = [x.strip() for x in _split_args_top_level(m_pack_call.group(1)) if x.strip()]
                    if len(pargs) >= 2:
                        m_arr = re.match(r"^([a-z_]\w*)$", pargs[0], re.IGNORECASE)
                        m_mask = re.match(r"^([a-z_]\w*)$", pargs[1], re.IGNORECASE)
                        if m_arr and m_mask:
                            an = m_arr.group(1).lower()
                            mn = m_mask.group(1).lower()
                            av = vars_map.get(an)
                            mv = vars_map.get(mn)
                            if av is not None and mv is not None and av.is_array and mv.is_array:
                                npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                cty = (av.ctype or real_type).lower()
                                efmt = "%d" if cty == "int" else "%g"
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {npr}; ++i_pr) {{")
                                out.append(" " * (indent + 6) + f"if ({mn}[i_pr]) {{")
                                out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", {an}[i_pr]);')
                                out.append(" " * (indent + 9) + "__first = 0;")
                                out.append(" " * (indent + 6) + "}")
                                out.append(" " * (indent + 3) + "}")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                if len(re.findall(r"(?i)\bsum\s*\(", expr0)) == 1:
                    m_sum_dim_expr = re.match(
                        r"^(.*?)(sum\s*\(\s*([a-z_]\w*)\s*,\s*(?:dim\s*=\s*)?([0-9]+)\s*\))(.*)$",
                        expr0,
                        re.IGNORECASE,
                    )
                    if m_sum_dim_expr:
                        pre = m_sum_dim_expr.group(1) or ""
                        an = m_sum_dim_expr.group(3).lower()
                        try:
                            dim_no = int(m_sum_dim_expr.group(4))
                        except Exception:
                            dim_no = None
                        post = m_sum_dim_expr.group(5) or ""
                        av = vars_map.get(an)
                        if av is not None and av.is_array and dim_no is not None and (pre.strip() or post.strip()):
                            dparts = _resolved_dim_parts(av, an, assumed_extents)
                            rank = len(dparts)
                            if rank in {2, 3} and 1 <= dim_no <= rank:
                                d = [
                                    _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    for k in range(rank)
                                ]
                                tmp_var = "__red"
                                vars_map_red = dict(vars_map)
                                vars_map_red[tmp_var] = Var(av.ctype or real_type)
                                expr_red = f"{pre}{tmp_var}{post}"
                                cexpr_red = _convert_expr(expr_red, vars_map_red, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                expr_cty = _format_item_ctype(expr_red, vars_map_red, real_type)
                                efmt = "%d" if expr_cty == "int" else "%g"
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                out.append(" " * (indent + 3) + f"{av.ctype} {tmp_var};")
                                if rank == 2 and dim_no == 1:
                                    out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                    out.append(" " * (indent + 6) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                    out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 6) + "__first = 0;")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 2 and dim_no == 2:
                                    out.append(" " * (indent + 3) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                    out.append(" " * (indent + 6) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                    out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 6) + "__first = 0;")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 3 and dim_no == 1:
                                    out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                    out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                    out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 9) + f"for (int i = 1; i <= {d[0]}; ++i) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 3 and dim_no == 2:
                                    out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                    out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                    out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 9) + f"for (int j = 1; j <= {d[1]}; ++j) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                elif rank == 3 and dim_no == 3:
                                    out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                    out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                    out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 9) + f"for (int k = 1; k <= {d[2]}; ++k) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", {cexpr_red});')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                m_sum_call = re.match(r"^sum\s*\((.*)\)\s*$", expr0, re.IGNORECASE)
                if m_sum_call:
                    sargs = [x.strip() for x in _split_args_top_level(m_sum_call.group(1)) if x.strip()]
                    if sargs:
                        arg0 = sargs[0]
                        dim_no = None
                        mask_arg: Optional[str] = None
                        if len(sargs) >= 2:
                            s1 = sargs[1]
                            m_dim_kw = re.match(r"(?i)^dim\s*=\s*([0-9]+)$", s1)
                            m_mask_kw = re.match(r"(?i)^mask\s*=\s*(.+)$", s1)
                            if m_dim_kw:
                                dim_no = int(m_dim_kw.group(1))
                            elif m_mask_kw:
                                mask_arg = m_mask_kw.group(1).strip()
                            elif re.fullmatch(r"[0-9]+", s1):
                                dim_no = int(s1)
                            else:
                                mask_arg = s1
                        # Generic scalar SUM over an array expression, with optional MASK.
                        if dim_no is None:
                            arr_tokens_0 = [t for t in sorted({t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(arg0), flags=re.IGNORECASE)}) if t in vars_map and vars_map[t].is_array]
                            arr_tokens_m = []
                            if mask_arg:
                                arr_tokens_m = [t for t in sorted({t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(mask_arg), flags=re.IGNORECASE)}) if t in vars_map and vars_map[t].is_array]
                            all_arrs = arr_tokens_0 + [a for a in arr_tokens_m if a not in arr_tokens_0]
                            if all_arrs:
                                base = vars_map.get(all_arrs[0])
                                assert base is not None
                                compatible = all((vars_map.get(a) is not None and vars_map.get(a).dim == base.dim) for a in all_arrs)
                                if compatible:
                                    npr = _dim_product_expr(base.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                    expr_i = arg0
                                    for a in sorted(all_arrs, key=len, reverse=True):
                                        expr_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_pr]", expr_i, flags=re.IGNORECASE)
                                    mask_i = "1"
                                    if mask_arg:
                                        mask_i = mask_arg
                                        for a in sorted(all_arrs, key=len, reverse=True):
                                            mask_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_pr]", mask_i, flags=re.IGNORECASE)
                                    cexpr_i = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    cmask_i = _convert_expr(mask_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    cty = (base.ctype or real_type).lower()
                                    efmt = "%d" if cty == "int" else "%g"
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + f"{base.ctype} __sum = 0;")
                                    out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {npr}; ++i_pr) {{")
                                    out.append(" " * (indent + 6) + f"if ({cmask_i}) __sum += {cexpr_i};")
                                    out.append(" " * (indent + 3) + "}")
                                    out.append(" " * (indent + 3) + f'printf("{efmt}\\n", __sum);')
                                    out.append(" " * indent + "}")
                                    continue
                        m_arr0 = re.match(r"^([a-z_]\w*)$", sargs[0], re.IGNORECASE)
                        if m_arr0:
                            an = m_arr0.group(1).lower()
                            av = vars_map.get(an)
                            if av is not None and av.is_array:
                                dparts = _resolved_dim_parts(av, an, assumed_extents)
                                rank = len(dparts)
                                cty = (av.ctype or real_type).lower()
                                efmt = "%d" if cty == "int" else "%g"
                                if mask_arg is not None and dim_no is None:
                                    npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                    mexpr = mask_arg
                                    for arrn, vv in vars_map.items():
                                        if vv.is_array and vv.dim == av.dim and re.search(rf"\b{re.escape(arrn)}\b", mexpr, re.IGNORECASE):
                                            mexpr = re.sub(rf"\b{re.escape(arrn)}\b", f"{arrn}[i_pr]", mexpr, flags=re.IGNORECASE)
                                    cmask = _convert_expr(mexpr, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + f"{av.ctype} __sum = 0;")
                                    out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {npr}; ++i_pr) {{")
                                    out.append(" " * (indent + 6) + f"if ({cmask}) __sum += {an}[i_pr];")
                                    out.append(" " * (indent + 3) + "}")
                                    out.append(" " * (indent + 3) + f'printf("{efmt}\\n", __sum);')
                                    out.append(" " * indent + "}")
                                    continue
                                if dim_no is None:
                                    csum = _convert_expr(expr0, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + f'printf("{efmt}\\n", {csum});')
                                    continue
                                if rank == 1 and dim_no == 1:
                                    csum = _convert_expr(f"sum({an})", vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + f'printf("{efmt}\\n", {csum});')
                                    continue
                                if rank in {2, 3} and 1 <= dim_no <= rank:
                                    d = [
                                        _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        for k in range(rank)
                                    ]
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + "int __first = 1;")
                                    out.append(" " * (indent + 3) + f"{av.ctype} __sum;")
                                    if rank == 2 and dim_no == 1:
                                        out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                        out.append(" " * (indent + 6) + "__sum = 0;")
                                        out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                        out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                        out.append(" " * (indent + 6) + "__first = 0;")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 2 and dim_no == 2:
                                        out.append(" " * (indent + 3) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                        out.append(" " * (indent + 6) + "__sum = 0;")
                                        out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                        out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                        out.append(" " * (indent + 6) + "__first = 0;")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 3 and dim_no == 1:
                                        out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                        out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                        out.append(" " * (indent + 9) + "__sum = 0;")
                                        out.append(" " * (indent + 9) + f"for (int i = 1; i <= {d[0]}; ++i) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                        out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                        out.append(" " * (indent + 9) + "__first = 0;")
                                        out.append(" " * (indent + 6) + "}")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 3 and dim_no == 2:
                                        out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                        out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                        out.append(" " * (indent + 9) + "__sum = 0;")
                                        out.append(" " * (indent + 9) + f"for (int j = 1; j <= {d[1]}; ++j) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                        out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                        out.append(" " * (indent + 9) + "__first = 0;")
                                        out.append(" " * (indent + 6) + "}")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 3 and dim_no == 3:
                                        out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                        out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                        out.append(" " * (indent + 9) + "__sum = 0;")
                                        out.append(" " * (indent + 9) + f"for (int k = 1; k <= {d[2]}; ++k) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                        out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                        out.append(" " * (indent + 9) + "__first = 0;")
                                        out.append(" " * (indent + 6) + "}")
                                        out.append(" " * (indent + 3) + "}")
                                    out.append(" " * (indent + 3) + 'printf("\\n");')
                                    out.append(" " * indent + "}")
                                    continue
                m_product_call = re.match(r"^product\s*\((.*)\)\s*$", expr0, re.IGNORECASE)
                if m_product_call:
                    sargs = [x.strip() for x in _split_args_top_level(m_product_call.group(1)) if x.strip()]
                    if sargs:
                        arg0 = sargs[0]
                        dim_no = None
                        if len(sargs) >= 2:
                            s1 = sargs[1]
                            m_dim_kw = re.match(r"(?i)^dim\s*=\s*([0-9]+)$", s1)
                            if m_dim_kw:
                                dim_no = int(m_dim_kw.group(1))
                            elif re.fullmatch(r"[0-9]+", s1):
                                dim_no = int(s1)
                        m_arr0 = re.match(r"^([a-z_]\w*)$", arg0, re.IGNORECASE)
                        if m_arr0:
                            an = m_arr0.group(1).lower()
                            av = vars_map.get(an)
                            if av is not None and av.is_array:
                                dparts = _resolved_dim_parts(av, an, assumed_extents)
                                rank = len(dparts)
                                cty = (av.ctype or real_type).lower()
                                efmt = "%d" if cty == "int" else "%g"
                                if dim_no is None:
                                    cprod = _convert_expr(expr0, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + f'printf("{efmt}\\n", {cprod});')
                                    continue
                                if rank == 1 and dim_no == 1:
                                    cprod = _convert_expr(f"product({an})", vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + f'printf("{efmt}\\n", {cprod});')
                                    continue
                                if rank in {2, 3} and 1 <= dim_no <= rank:
                                    d = [
                                        _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        for k in range(rank)
                                    ]
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + "int __first = 1;")
                                    out.append(" " * (indent + 3) + f"{av.ctype} __prod;")
                                    if rank == 2 and dim_no == 1:
                                        out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                        out.append(" " * (indent + 6) + "__prod = 1;")
                                        out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) __prod *= {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                        out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", __prod);')
                                        out.append(" " * (indent + 6) + "__first = 0;")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 2 and dim_no == 2:
                                        out.append(" " * (indent + 3) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                        out.append(" " * (indent + 6) + "__prod = 1;")
                                        out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) __prod *= {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                        out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", __prod);')
                                        out.append(" " * (indent + 6) + "__first = 0;")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 3 and dim_no == 1:
                                        out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                        out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                        out.append(" " * (indent + 9) + "__prod = 1;")
                                        out.append(" " * (indent + 9) + f"for (int i = 1; i <= {d[0]}; ++i) __prod *= {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                        out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __prod);')
                                        out.append(" " * (indent + 9) + "__first = 0;")
                                        out.append(" " * (indent + 6) + "}")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 3 and dim_no == 2:
                                        out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                        out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                        out.append(" " * (indent + 9) + "__prod = 1;")
                                        out.append(" " * (indent + 9) + f"for (int j = 1; j <= {d[1]}; ++j) __prod *= {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                        out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __prod);')
                                        out.append(" " * (indent + 9) + "__first = 0;")
                                        out.append(" " * (indent + 6) + "}")
                                        out.append(" " * (indent + 3) + "}")
                                    elif rank == 3 and dim_no == 3:
                                        out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                        out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                        out.append(" " * (indent + 9) + "__prod = 1;")
                                        out.append(" " * (indent + 9) + f"for (int k = 1; k <= {d[2]}; ++k) __prod *= {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                        out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __prod);')
                                        out.append(" " * (indent + 9) + "__first = 0;")
                                        out.append(" " * (indent + 6) + "}")
                                        out.append(" " * (indent + 3) + "}")
                                    out.append(" " * (indent + 3) + 'printf("\\n");')
                                    out.append(" " * indent + "}")
                                    continue
                m_expr_vsub = re.match(r"^(.*?)([a-z_]\w*)\s*\(\s*(.+?)\s*\)(.*)$", expr0, re.IGNORECASE)
                if m_expr_vsub and len(re.findall(r"\b[a-z_]\w*\s*\(", expr0, flags=re.IGNORECASE)) == 1:
                    pre = m_expr_vsub.group(1)
                    an = m_expr_vsub.group(2).lower()
                    inner = m_expr_vsub.group(3).strip()
                    post = m_expr_vsub.group(4) or ""
                    av = vars_map.get(an)
                    if av is not None and av.is_array:
                        idx_parts = _split_args_top_level(inner)
                        dparts = _resolved_dim_parts(av, an, assumed_extents)
                        rank = len(dparts)
                        if rank in {2, 3} and len(idx_parts) == rank:
                            dimc = [
                                _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                for k in range(rank)
                            ]

                            def _parse_dim_spec(txt: str, dflt_hi: str) -> dict:
                                t = txt.strip()
                                m_ctor = re.match(r"^\[\s*(.*)\s*\]$", t)
                                if m_ctor:
                                    vals = [x.strip() for x in _split_args_top_level(m_ctor.group(1)) if x.strip()]
                                    cvals = [
                                        _convert_expr(vv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        for vv in vals
                                    ]
                                    return {"kind": "vec", "vals": cvals}
                                if ":" in t:
                                    sp = _split_colon_top_level(t)
                                    lo = _convert_expr((sp[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    hi = _convert_expr((sp[1] or dflt_hi).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    st = _convert_expr((sp[2] if len(sp) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    return {"kind": "sec", "lo": lo, "hi": hi, "st": st}
                                val = _convert_expr(t, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                return {"kind": "scalar", "val": val}

                            specs = [_parse_dim_spec(idx_parts[k], dimc[k]) for k in range(rank)]
                            if any(sp["kind"] != "scalar" for sp in specs):
                                expr_elem = f"{pre}__elem{post}"
                                cexpr = _convert_expr(expr_elem, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                out.append(" " * (indent + 3) + f"{av.ctype} __elem;")

                                idx_map: Dict[int, str] = {}

                                def _lin_expr() -> str:
                                    i1 = idx_map.get(1, "1")
                                    lin = f"(({i1}) - 1)"
                                    if rank >= 2:
                                        i2 = idx_map.get(2, "1")
                                        lin = f"{lin} + ({dimc[0]}) * (({i2}) - 1)"
                                    if rank >= 3:
                                        i3 = idx_map.get(3, "1")
                                        lin = f"{lin} + ({dimc[0]}) * ({dimc[1]}) * (({i3}) - 1)"
                                    return lin

                                def _emit_dim(dim_k: int, ind: int) -> None:
                                    if dim_k < 1:
                                        lin = _lin_expr()
                                        out.append(" " * ind + f"__elem = {an}[{lin}];")
                                        out.append(" " * ind + f'printf("%s%g", __first ? "" : " ", {cexpr});')
                                        out.append(" " * ind + "__first = 0;")
                                        return
                                    sp = specs[dim_k - 1]
                                    if sp["kind"] == "scalar":
                                        idx_map[dim_k] = sp["val"]
                                        _emit_dim(dim_k - 1, ind)
                                        return
                                    if sp["kind"] == "vec":
                                        for vv in sp["vals"]:
                                            idx_map[dim_k] = vv
                                            _emit_dim(dim_k - 1, ind)
                                        return
                                    vnm = f"__i{dim_k}"
                                    idx_map[dim_k] = vnm
                                    out.append(" " * ind + f"for (int {vnm} = {sp['lo']}; ({sp['st']}) > 0 ? {vnm} <= {sp['hi']} : {vnm} >= {sp['hi']}; {vnm} += {sp['st']}) {{")
                                    _emit_dim(dim_k - 1, ind + 3)
                                    out.append(" " * ind + "}")

                                _emit_dim(rank, indent + 3)
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                m_elem_intr = re.match(r"^\s*(nint|anint|aint|floor|ceiling|int|real|dble)\s*\((.*)\)\s*$", expr0, re.IGNORECASE)
                if m_elem_intr:
                    intr = m_elem_intr.group(1).lower()
                    arg_expr = m_elem_intr.group(2).strip()
                    arrs_intr = [t for t in sorted({t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(arg_expr), flags=re.IGNORECASE)}) if t in vars_map and vars_map[t].is_array]
                    if arrs_intr and not any(re.search(rf"\b{re.escape(a)}\s*\(", arg_expr, flags=re.IGNORECASE) for a in arrs_intr):
                        base = vars_map.get(arrs_intr[0])
                        compatible = base is not None and all((vars_map.get(a) is not None and vars_map.get(a).dim == base.dim) for a in arrs_intr)
                        if compatible and base is not None:
                            if base.is_allocatable and len(_dim_parts(base.dim)) == 1:
                                npr = _alloc_len_name(arrs_intr[0])
                            else:
                                npr = _dim_product_expr(base.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                            expr_i = expr0
                            for a in sorted(arrs_intr, key=len, reverse=True):
                                expr_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_pr]", expr_i, flags=re.IGNORECASE)
                            cit = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            efmt = "%d" if intr in {"nint", "floor", "ceiling", "int"} else "%g"
                            out.append(" " * indent + f"for (int i_pr = 0; i_pr < {npr}; ++i_pr) {{")
                            out.append(" " * (indent + 3) + f'printf("{efmt}%s", {cit}, (i_pr + 1 < {npr}) ? " " : "\\n");')
                            out.append(" " * indent + "}")
                            continue
                            continue
                if _emit_list_directed_ctor_broadcast_expr(out, indent, expr0, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                    continue
                if _emit_list_directed_ctor_output(out, indent, expr0, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                    continue
                expr_sec = expr0
                npr_sec: Optional[str] = None
                sec_changed = False
                for an_sec, av_sec in sorted(vars_map.items(), key=lambda kv: len(kv[0]), reverse=True):
                    if not av_sec.is_array:
                        continue
                    dparts_sec = _resolved_dim_parts(av_sec, an_sec, assumed_extents)
                    pat_sec = re.compile(rf"\b{re.escape(an_sec)}\s*\(\s*([^()]*)\s*\)", re.IGNORECASE)

                    def _repl_print_sec(mm: re.Match[str]) -> str:
                        nonlocal npr_sec, sec_changed
                        inner = mm.group(1)
                        idx_parts = _split_args_top_level(inner)
                        if len(dparts_sec) == 1 and len(idx_parts) == 1 and ":" in idx_parts[0]:
                            sp = _split_colon_top_level(idx_parts[0].strip())
                            lo = _convert_expr((sp[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            hi = _convert_expr((sp[1] or dparts_sec[0]).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            st = _convert_expr((sp[2] if len(sp) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            ncur = _section_count_expr(lo, hi, st)
                            if npr_sec is None:
                                npr_sec = ncur
                            elif npr_sec.replace(" ", "") != ncur.replace(" ", ""):
                                return mm.group(0)
                            sec_changed = True
                            return f"{an_sec}[(({lo}) + i_pr * ({st})) - 1]"
                        if len(dparts_sec) == 2 and len(idx_parts) == 2:
                            d1 = _convert_expr(dparts_sec[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            d2 = _convert_expr(dparts_sec[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            sec0 = ":" in idx_parts[0]
                            sec1 = ":" in idx_parts[1]
                            if sec0 and not sec1:
                                sp0 = _split_colon_top_level(idx_parts[0].strip())
                                lo0 = _convert_expr((sp0[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                hi0 = _convert_expr((sp0[1] or d1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                st0 = _convert_expr((sp0[2] if len(sp0) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                col = _convert_expr(idx_parts[1].strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                ncur = _section_count_expr(lo0, hi0, st0)
                                if npr_sec is None:
                                    npr_sec = ncur
                                elif npr_sec.replace(" ", "") != ncur.replace(" ", ""):
                                    return mm.group(0)
                                sec_changed = True
                                return f"{an_sec}[(({lo0}) + i_pr * ({st0})) - 1 + ({d1}) * (({col}) - 1)]"
                            if sec1 and not sec0:
                                row = _convert_expr(idx_parts[0].strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                sp1 = _split_colon_top_level(idx_parts[1].strip())
                                lo1 = _convert_expr((sp1[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                hi1 = _convert_expr((sp1[1] or d2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                st1 = _convert_expr((sp1[2] if len(sp1) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                ncur = _section_count_expr(lo1, hi1, st1)
                                if npr_sec is None:
                                    npr_sec = ncur
                                elif npr_sec.replace(" ", "") != ncur.replace(" ", ""):
                                    return mm.group(0)
                                sec_changed = True
                                return f"{an_sec}[(({row}) - 1) + ({d1}) * ((({lo1}) + i_pr * ({st1})) - 1)]"
                        return mm.group(0)

                    expr_sec = pat_sec.sub(_repl_print_sec, expr_sec)
                if sec_changed and npr_sec is not None:
                    cit = _convert_expr(expr_sec, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    expr_cty = _format_item_ctype(expr0, vars_map, real_type)
                    _emit_list_directed_1d_value_stream(out, indent, cit, expr_cty, f"for (int i_pr = 0; i_pr < {npr_sec}; ++i_pr)", vars_map)
                    continue
                toks0 = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(expr0), flags=re.IGNORECASE)}
                arrs0 = [t for t in sorted(toks0) if t in vars_map and vars_map[t].is_array]
                if arrs0 and not any(re.search(rf"\b{re.escape(a)}\s*\(", expr0, flags=re.IGNORECASE) for a in arrs0):
                    base = vars_map.get(arrs0[0])
                    compatible = base is not None and all((vars_map.get(a) is not None and vars_map.get(a).dim == base.dim) for a in arrs0)
                    if compatible and base is not None:
                        if (base.is_allocatable or base.is_pointer) and len(_dim_parts(base.dim)) == 1:
                            npr = _alloc_len_name(arrs0[0])
                        else:
                            npr = _dim_product_expr(base.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                        expr_i = expr0
                        for a in sorted(arrs0, key=len, reverse=True):
                            expr_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_pr]", expr_i, flags=re.IGNORECASE)
                        cit = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        expr_cty = _var_render_ctype(base, real_type) if len(arrs0) == 1 and expr0.strip().lower() == arrs0[0] else _format_item_ctype(expr0, vars_map, real_type)
                        _emit_list_directed_1d_value_stream(out, indent, cit, expr_cty, f"for (int i_pr = 0; i_pr < {npr}; ++i_pr)", vars_map)
                        continue
                        continue
            # Mixed list with one or more whole-array variables: print on one line.
            arr_items: List[tuple[int, str, Var, Optional[str]]] = []
            for ii, it in enumerate(items):
                m_ai = re.match(r"^([a-z_]\w*)$", it, re.IGNORECASE)
                if m_ai:
                    an = m_ai.group(1).lower()
                    av = vars_map.get(an)
                    if av is not None and av.is_array:
                        arr_items.append((ii, an, av, None))
                        continue
                m_runif_arr = re.match(r"^runif_1d\s*\(\s*(.+)\s*\)$", it, re.IGNORECASE)
                if m_runif_arr:
                    arr_items.append((ii, it.strip(), Var(real_type, is_array=True, dim=":"), "runif_1d"))
                    continue
                call_info = _array_result_call_info(it, vars_map, real_type)
                if call_info is not None:
                    callee, rv, _ = call_info
                    arr_items.append((ii, it.strip(), rv, callee))
            if arr_items:
                if len(arr_items) == 1 and len(items) == 1:
                    _, an0, av0, callee0 = arr_items[0]
                    if callee0 is None:
                        if av0.is_allocatable or av0.is_pointer:
                            npr0 = _dim_product_from_parts(
                                _resolved_dim_parts(av0, an0, assumed_extents),
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                            )
                        else:
                            npr0 = _dim_product_expr(av0.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                        if (av0.ctype or real_type).lower() == "char *":
                            clen0 = _convert_expr(av0.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if av0.char_len else None
                            out.append(" " * indent + "{")
                            out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {npr0}; ++i_pr) {{")
                            if clen0:
                                out.append(" " * (indent + 6) + f'printf("%-*s", {clen0}, {an0}[i_pr]);')
                            else:
                                out.append(" " * (indent + 6) + f'printf("%s", {an0}[i_pr]);')
                            out.append(" " * (indent + 3) + "}")
                            out.append(" " * (indent + 3) + 'printf("\\n");')
                            out.append(" " * indent + "}")
                        else:
                            _emit_list_directed_1d_value_stream(out, indent, f"{an0}[i_pr]", _var_render_ctype(av0, real_type), f"for (int i_pr = 0; i_pr < {npr0}; ++i_pr)", vars_map)
                    else:
                        tmp0 = "__arr_call_0"
                        out.append(" " * indent + "{")
                        if callee0 == "runif_1d":
                            m_call0 = re.match(r"^runif_1d\s*\((.*)\)\s*$", an0, re.IGNORECASE)
                            n1_0 = _convert_expr((m_call0.group(1) if m_call0 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            out_len0 = n1_0
                            out.append(" " * (indent + 3) + f"{av0.ctype} *{tmp0} = ({av0.ctype}*) malloc(sizeof({av0.ctype}) * ({out_len0}));")
                            out.append(" " * (indent + 3) + f"if (!{tmp0} && ({out_len0}) > 0) {fail_stmt}")
                            out.append(" " * (indent + 3) + f"fill_runif_1d({out_len0}, {tmp0});")
                        else:
                            m_call0 = re.match(r"^([a-z_]\w*)\s*\((.*)\)\s*$", an0, re.IGNORECASE)
                            raw_args0 = _split_args_top_level(m_call0.group(2).strip()) if m_call0 and m_call0.group(2).strip() else []
                            raw_args0 = _normalize_actual_args(callee0, raw_args0, proc_arg_names)
                            cargs0: List[str] = []
                            out_len0: Optional[str] = None
                            extent_lists0 = proc_arg_extent_names.get(callee0, [])
                            for k0, a0 in enumerate(raw_args0):
                                exts0 = extent_lists0[k0] if k0 < len(extent_lists0) else []
                                extent_args0, carg0 = _expand_assumed_shape_actual_arg(
                                    a0,
                                    exts0,
                                    vars_map,
                                    real_type,
                                    byref_scalars,
                                    assumed_extents,
                                    proc_arg_extent_names,
                                )
                                if out_len0 is None and extent_args0:
                                    out_len0 = extent_args0[0]
                                cargs0.extend(extent_args0)
                                cargs0.append(carg0)
                            if _is_dynamic_array_result(av0) or out_len0 is None:
                                out_len0 = _result_length_expr(callee0, av0, vars_map, real_type, byref_scalars, assumed_extents)
                            out.append(" " * (indent + 3) + f"{av0.ctype} *{tmp0} = {callee0}({', '.join(cargs0)});")
                        if _var_render_ctype(av0, real_type) == "string":
                            out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {out_len0}; ++i_pr) printf(\"%s\", {tmp0}[i_pr]);")
                            out.append(" " * (indent + 3) + 'printf("\\n");')
                            out.append(" " * (indent + 3) + f"if ({tmp0}) free_str_array({tmp0}, {out_len0});")
                        else:
                            _emit_list_directed_1d_value_stream(out, indent + 3, f"{tmp0}[i_pr]", _var_render_ctype(av0, real_type), f"for (int i_pr = 0; i_pr < {out_len0}; ++i_pr)", vars_map)
                            out.append(" " * (indent + 3) + f"free({tmp0});")
                        out.append(" " * indent + "}")
                    continue
                out.append(" " * indent + "{")
                out.append(" " * (indent + 3) + "int __first_pr = 1;")
                arr_pos = {ii for ii, _, _, _ in arr_items}
                for ii, it in enumerate(items):
                    if ii in arr_pos:
                        an, av, callee_arr = [(a, v, c) for j, a, v, c in arr_items if j == ii][0]
                        if callee_arr is None:
                            if av.is_allocatable or av.is_pointer:
                                npr = _dim_product_from_parts(
                                    _resolved_dim_parts(av, an, assumed_extents),
                                    vars_map,
                                    real_type,
                                    byref_scalars,
                                    assumed_extents,
                                )
                            else:
                                npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                            cty = (av.ctype or real_type).lower()
                            efmt = "%d" if cty == "int" else "%g"
                            out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {npr}; ++i_pr) {{")
                            if cty == "char *":
                                clen = _convert_expr(av.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if av.char_len else None
                                if clen:
                                    out.append(" " * (indent + 6) + f'printf("%s%-*s", (i_pr == 0) ? (__first_pr ? "" : " ") : "", {clen}, {an}[i_pr]);')
                                else:
                                    out.append(" " * (indent + 6) + f'printf("%s%s", (i_pr == 0) ? (__first_pr ? "" : " ") : "", {an}[i_pr]);')
                            else:
                                out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first_pr ? "" : " ", {an}[i_pr]);')
                            out.append(" " * (indent + 6) + "__first_pr = 0;")
                            out.append(" " * (indent + 3) + "}")
                        else:
                            tmp = f"__arr_call_{ii}"
                            if callee_arr == "runif_1d":
                                m_call = re.match(r"^runif_1d\s*\((.*)\)\s*$", an, re.IGNORECASE)
                                out_len = _convert_expr((m_call.group(1) if m_call else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                out.append(" " * (indent + 3) + f"{av.ctype} *{tmp} = ({av.ctype}*) malloc(sizeof({av.ctype}) * ({out_len}));")
                                out.append(" " * (indent + 3) + f"if (!{tmp} && ({out_len}) > 0) {fail_stmt}")
                                out.append(" " * (indent + 3) + f"fill_runif_1d({out_len}, {tmp});")
                            else:
                                m_call = re.match(r"^([a-z_]\w*)\s*\((.*)\)\s*$", an, re.IGNORECASE)
                                raw_args = _split_args_top_level(m_call.group(2).strip()) if m_call and m_call.group(2).strip() else []
                                raw_args = _normalize_actual_args(callee_arr, raw_args, proc_arg_names)
                                cargs: List[str] = []
                                out_len: Optional[str] = None
                                extent_lists = proc_arg_extent_names.get(callee_arr, [])
                                for k, a_raw in enumerate(raw_args):
                                    exts = extent_lists[k] if k < len(extent_lists) else []
                                    extent_args, carg = _expand_assumed_shape_actual_arg(
                                        a_raw,
                                        exts,
                                        vars_map,
                                        real_type,
                                        byref_scalars,
                                        assumed_extents,
                                        proc_arg_extent_names,
                                    )
                                    if out_len is None and extent_args:
                                        out_len = extent_args[0]
                                    cargs.extend(extent_args)
                                    cargs.append(carg)
                                if _is_dynamic_array_result(av) or out_len is None:
                                    out_len = _result_length_expr(callee_arr, av, vars_map, real_type, byref_scalars, assumed_extents)
                                out.append(" " * (indent + 3) + f"{av.ctype} *{tmp} = {callee_arr}({', '.join(cargs)});")
                            out.append(" " * (indent + 3) + f"for (int i_pr = 0; i_pr < {out_len}; ++i_pr) {{")
                            if (av.ctype or real_type).lower() == "char *":
                                out.append(" " * (indent + 6) + f'printf("%s%s", (i_pr == 0) ? (__first_pr ? "" : " ") : "", {tmp}[i_pr]);')
                            else:
                                efmt = "%d" if (av.ctype or real_type).lower() == "int" else "%g"
                                out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first_pr ? "" : " ", {tmp}[i_pr]);')
                            out.append(" " * (indent + 6) + "__first_pr = 0;")
                            out.append(" " * (indent + 3) + "}")
                            if (av.ctype or real_type).lower() == "char *":
                                out.append(" " * (indent + 3) + f"if ({tmp}) free_str_array({tmp}, {out_len});")
                            else:
                                out.append(" " * (indent + 3) + f"free({tmp});")
                        continue
                    if (it.startswith('"') and it.endswith('"')) or (it.startswith("'") and it.endswith("'")):
                        content = it[1:-1].replace("\\", "\\\\").replace('"', '\\"')
                        out.append(" " * (indent + 3) + f'printf("%s%s", __first_pr ? "" : " ", "{content}");')
                        out.append(" " * (indent + 3) + "__first_pr = 0;")
                        continue
                    m_trim = re.match(r"^\s*trim\s*\(\s*([a-z_]\w*)\s*\)\s*$", it, re.IGNORECASE)
                    if m_trim:
                        nm_trim = m_trim.group(1).lower()
                        out.append(" " * (indent + 3) + f'printf("%s%.*s", __first_pr ? "" : " ", len_trim_s({nm_trim}), {nm_trim});')
                        out.append(" " * (indent + 3) + "__first_pr = 0;")
                        continue
                    cit = _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    fmt = _list_directed_scalar_fmt(_format_item_ctype(it, vars_map, real_type))
                    out.append(" " * (indent + 3) + f'printf("%s{fmt}", __first_pr ? "" : " ", {cit});')
                    out.append(" " * (indent + 3) + "__first_pr = 0;")
                out.append(" " * (indent + 3) + 'printf("\\n");')
                out.append(" " * indent + "}")
                continue

            expr_last = items[-1]
            if len(re.findall(r"(?i)\bsum\s*\(", expr_last)) == 1:
                m_sum_dim_tail = re.match(
                    r"^(.*?)(sum\s*\(\s*([a-z_]\w*)\s*,\s*(?:dim\s*=\s*)?([0-9]+)\s*\))(.*)$",
                    expr_last,
                    re.IGNORECASE,
                )
                if m_sum_dim_tail:
                    pre = m_sum_dim_tail.group(1) or ""
                    an = m_sum_dim_tail.group(3).lower()
                    try:
                        dim_no = int(m_sum_dim_tail.group(4))
                    except Exception:
                        dim_no = None
                    post = m_sum_dim_tail.group(5) or ""
                    av = vars_map.get(an)
                    prefix_items = items[:-1]
                    if av is not None and av.is_array and dim_no is not None:
                        dparts = _resolved_dim_parts(av, an, assumed_extents)
                        rank = len(dparts)
                        if rank in {2, 3} and 1 <= dim_no <= rank and all(not (vars_map.get(it.lower()) and vars_map[it.lower()].is_array) for it in [x.strip() for x in prefix_items if re.fullmatch(r"[a-z_]\w*", x.strip(), re.IGNORECASE)]):
                            d = [
                                _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                for k in range(rank)
                            ]
                            tmp_var = "__red"
                            vars_map_red = dict(vars_map)
                            vars_map_red[tmp_var] = Var(av.ctype or real_type)
                            expr_red = f"{pre}{tmp_var}{post}"
                            cexpr_red = _convert_expr(expr_red, vars_map_red, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            expr_cty = _format_item_ctype(expr_red, vars_map_red, real_type)
                            efmt_red = "%d" if expr_cty == "int" else "%g"
                            out.append(" " * indent + "{")
                            out.append(" " * (indent + 3) + "int __first = 1;")
                            out.append(" " * (indent + 3) + f"{av.ctype} {tmp_var};")
                            for pit in prefix_items:
                                cty_pre = _format_item_ctype(pit, vars_map, real_type)
                                cexpr_pre = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                if cty_pre == "string":
                                    out.append(" " * (indent + 3) + f'printf("%s%s", __first ? "" : " ", {cexpr_pre});')
                                elif cty_pre == "int":
                                    out.append(" " * (indent + 3) + f'printf("%s%d", __first ? "" : " ", {cexpr_pre});')
                                else:
                                    out.append(" " * (indent + 3) + f'printf("%s%g", __first ? "" : " ", {cexpr_pre});')
                                out.append(" " * (indent + 3) + "__first = 0;")
                            if rank == 2 and dim_no == 1:
                                out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                out.append(" " * (indent + 6) + f"{tmp_var} = 0;")
                                out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                out.append(" " * (indent + 6) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                out.append(" " * (indent + 6) + "__first = 0;")
                                out.append(" " * (indent + 3) + "}")
                            elif rank == 2 and dim_no == 2:
                                out.append(" " * (indent + 3) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                out.append(" " * (indent + 6) + f"{tmp_var} = 0;")
                                out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                out.append(" " * (indent + 6) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                out.append(" " * (indent + 6) + "__first = 0;")
                                out.append(" " * (indent + 3) + "}")
                            elif rank == 3 and dim_no == 1:
                                out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                out.append(" " * (indent + 9) + f"for (int i = 1; i <= {d[0]}; ++i) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                out.append(" " * (indent + 9) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                out.append(" " * (indent + 9) + "__first = 0;")
                                out.append(" " * (indent + 6) + "}")
                                out.append(" " * (indent + 3) + "}")
                            elif rank == 3 and dim_no == 2:
                                out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                out.append(" " * (indent + 9) + f"for (int j = 1; j <= {d[1]}; ++j) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                out.append(" " * (indent + 9) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                out.append(" " * (indent + 9) + "__first = 0;")
                                out.append(" " * (indent + 6) + "}")
                                out.append(" " * (indent + 3) + "}")
                            elif rank == 3 and dim_no == 3:
                                out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                out.append(" " * (indent + 9) + f"{tmp_var} = 0;")
                                out.append(" " * (indent + 9) + f"for (int k = 1; k <= {d[2]}; ++k) {tmp_var} += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                out.append(" " * (indent + 9) + f'printf("%s{efmt_red}", __first ? "" : " ", {cexpr_red});')
                                out.append(" " * (indent + 9) + "__first = 0;")
                                out.append(" " * (indent + 6) + "}")
                                out.append(" " * (indent + 3) + "}")
                            out.append(" " * (indent + 3) + 'printf("\\n");')
                            out.append(" " * indent + "}")
                            continue

            mixed_parts: List[tuple[str, str]] = []
            mixed_supported = True
            for pit in items:
                if _is_fortran_string_literal(pit.strip()):
                    lit = _unquote_fortran_string_literal(pit.strip()).replace("\\", "\\\\").replace('"', '\\"')
                    mixed_parts.append(("string", f'"{lit}"'))
                    continue
                m_trim = re.match(r"^\s*trim\s*\(\s*([a-z_]\w*)\s*\)\s*$", pit, re.IGNORECASE)
                if m_trim:
                    nm_trim = m_trim.group(1).lower()
                    mixed_parts.append(("trim_string", nm_trim))
                    continue
                m_intr_mix = re.match(r"^(size|rank|shape|lbound|ubound)\s*\((.*)\)\s*$", pit, re.IGNORECASE)
                if m_intr_mix:
                    inm = m_intr_mix.group(1).lower()
                    iargs = [x.strip() for x in _split_args_top_level(m_intr_mix.group(2)) if x.strip()]
                    if not iargs:
                        mixed_supported = False
                        break
                    a0 = iargs[0].lower()
                    av0 = vars_map.get(a0)
                    if av0 is None or (not av0.is_array):
                        mixed_supported = False
                        break
                    dparts0 = _resolved_dim_parts(av0, a0, assumed_extents)
                    if inm in {"size", "rank"} or len(iargs) >= 2 or len(dparts0) == 1:
                        cexpr0 = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        mixed_parts.append(("int", cexpr0))
                        continue
                    vals0: List[str] = []
                    if inm == "shape":
                        vals0 = [_dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts0]
                    elif inm == "lbound":
                        vals0 = [_dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts0]
                    else:
                        for p in dparts0:
                            lo0 = _dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                            ex0 = _dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                            vals0.append(f"(({lo0}) + ({ex0}) - 1)")
                    mixed_parts.extend(("int", vv) for vv in vals0)
                    continue
                m_simple = re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE)
                if m_simple:
                    vv = vars_map.get(m_simple.group(1).lower())
                    if vv is not None and vv.is_array:
                        mixed_supported = False
                        break
                toks_p = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(pit), flags=re.IGNORECASE)}
                has_bad_array_ref = False
                for t in toks_p:
                    vv = vars_map.get(t)
                    if vv is None or (not vv.is_array):
                        continue
                    if re.search(rf"\b{re.escape(t)}\s*\(", pit, flags=re.IGNORECASE):
                        continue
                    if re.match(r"^\s*(sum|minval|maxval|product|any|all|count)\s*\(", pit, re.IGNORECASE) and not re.search(r"\bdim\s*=", pit, re.IGNORECASE):
                        continue
                    has_bad_array_ref = True
                    break
                if has_bad_array_ref:
                    mixed_supported = False
                    break
                cty_p = _format_item_ctype(pit, vars_map, real_type)
                cexpr_p = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                mixed_parts.append((cty_p, cexpr_p))
            if mixed_supported and mixed_parts:
                out.append(" " * indent + "{")
                out.append(" " * (indent + 3) + "int __first = 1;")
                all_string_like = all(cty_p in {"string", "trim_string"} for cty_p, _ in mixed_parts)
                sep_expr = '""' if all_string_like else '" "'
                for cty_p, cexpr_p in mixed_parts:
                    _emit_list_directed_scalar_printf(
                        out,
                        indent + 3,
                        cexpr_p,
                        cty_p,
                        vars_map,
                        real_type,
                        prefix_expr=f'__first ? "" : {sep_expr}',
                    )
                    out.append(" " * (indent + 3) + "__first = 0;")
                out.append(" " * (indent + 3) + 'printf("\\n");')
                out.append(" " * indent + "}")
                continue

            if len(items) == 1:
                if _emit_list_directed_ctor_output(out, indent, items[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                    continue
                cit = _convert_expr(items[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                cty = _format_item_ctype(items[0], vars_map, real_type)
                _emit_list_directed_scalar_printf(
                    out,
                    indent,
                    cit,
                    cty,
                    vars_map,
                    real_type,
                    newline=True,
                )
                continue

        parsed_write = _split_leading_paren_group(code, "write")
        if parsed_write:
            ctl = parsed_write[0].strip()
            tail = (parsed_write[1] or "").strip()
            ctl_items = [x.strip() for x in _split_args_top_level(ctl) if x.strip()]
            unit_txt = None
            fmt_txt = None
            if ctl_items:
                first_ctl = ctl_items[0]
                m_first_kw = re.match(r"(?i)^([a-z_]\w*)\s*=\s*(.+)$", first_ctl)
                if m_first_kw is None:
                    unit_txt = first_ctl
                    if len(ctl_items) >= 2:
                        second_ctl = ctl_items[1]
                        m_second_kw = re.match(r"(?i)^fmt\s*=\s*(.+)$", second_ctl)
                        if m_second_kw:
                            fmt_txt = m_second_kw.group(1).strip()
                        elif re.match(r"(?i)^[a-z_]\w*\s*=", second_ctl) is None:
                            fmt_txt = second_ctl
                for ctl_item in ctl_items:
                    m_kw = re.match(r"(?i)^([a-z_]\w*)\s*=\s*(.+)$", ctl_item)
                    if not m_kw:
                        continue
                    key = m_kw.group(1).lower()
                    val = m_kw.group(2).strip()
                    if key == "unit":
                        unit_txt = val
                    elif key == "fmt":
                        fmt_txt = val
            unit_norm = unit_txt.strip().lower() if unit_txt is not None else ""
            write_to_stdout = unit_norm == "*" or unit_norm in stdout_unit_names or ctl.startswith("*")
            if (not write_to_stdout) and fmt_txt is not None and _is_fortran_string_literal(fmt_txt):
                fmt_clean = _unquote_fortran_string_literal(fmt_txt).strip().lower()
                tail_file = tail[1:].strip() if tail.startswith(",") else tail
                items_file = [x.strip() for x in _split_args_top_level(tail_file) if x.strip()]
                m_unit_var = re.match(r"^\s*([a-z_]\w*)\s*$", unit_txt or "", re.IGNORECASE)
                if m_unit_var and len(items_file) == 1:
                    unit_var = m_unit_var.group(1).lower()
                    if fmt_clean == '("(a",i0,",2x,a14,2x,a14)")':
                        dynamic_write_formats[unit_var] = ("a_a14_a14", items_file[0])
                        continue
                    if fmt_clean == '("(a",i0,",2x,f14.8,2x,f14.8)")':
                        dynamic_write_formats[unit_var] = ("a_f14_8_f14_8", items_file[0])
                        continue
                if fmt_clean == '(i3,1x,f6.1)' and unit_txt is not None and len(items_file) == 2:
                    unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    i_c = _convert_expr(items_file[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    r_c = _convert_expr(items_file[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    out.append(" " * indent + f"if (write_int_float_record({unit_c}, 3, 6, 1, {i_c}, {r_c}) != 0) {fail_stmt}")
                    continue
                if fmt_clean == '(i0,*(1x,a))' and unit_txt is not None and len(items_file) >= 1:
                    unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    first_c = _convert_expr(items_file[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    word_items = items_file[1:]
                    out.append(" " * indent + "{")
                    if word_items:
                        carr = ", ".join(_convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for it in word_items)
                        out.append(" " * (indent + 3) + f"const char *__write_words[] = {{{carr}}};")
                        out.append(" " * (indent + 3) + f"write_i0_then_words({unit_c}, {first_c}, {len(word_items)}, __write_words);")
                    else:
                        out.append(" " * (indent + 3) + f"write_i0_then_words({unit_c}, {first_c}, 0, NULL);")
                    out.append(" " * indent + "}")
                    continue
                if fmt_clean == '(a)' and len(items_file) == 1 and unit_txt is not None:
                    unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    arg_c = _convert_expr(items_file[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    out.append(" " * indent + f"write_a({unit_c}, {arg_c});")
                    continue
            if (not write_to_stdout) and fmt_txt is None:
                tail_file = tail[1:].strip() if tail.startswith(",") else tail
                items_file = [x.strip() for x in _split_args_top_level(tail_file) if x.strip()]
                pos_txt = None
                for ctl_item in ctl_items:
                    m_kw = re.match(r"(?i)^([a-z_]\w*)\s*=\s*(.+)$", ctl_item)
                    if m_kw and m_kw.group(1).lower() == "pos":
                        pos_txt = m_kw.group(2).strip()
                        break
                if unit_txt is not None and len(items_file) == 1:
                    arg_raw = items_file[0].strip()
                    arg_nm_m = re.match(r"^\s*([a-z_]\w*)\s*$", arg_raw, re.IGNORECASE)
                    unit_c = _convert_expr(unit_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    pos_c = _convert_expr(pos_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if pos_txt else "0L"
                    ptr_c = None
                    elem_size_c = None
                    count_c = None
                    if arg_nm_m:
                        arg_nm = arg_nm_m.group(1).lower()
                        av = vars_map.get(arg_nm)
                        if av is not None:
                            cty = (av.ctype or real_type).lower()
                            if av.is_array:
                                ptr_c = arg_nm
                                if cty == "int" or av.is_logical:
                                    elem_size_c = "sizeof(int)"
                                elif cty in {"long long", "long long int"}:
                                    elem_size_c = "sizeof(long long)"
                                elif cty == "char *":
                                    elem_size_c = "1"
                                else:
                                    elem_size_c = "sizeof(double)" if cty == "double" else "sizeof(float)"
                                if cty == "char *":
                                    count_c = _simplify_int_expr_text(av.char_len) if av.char_len else "1"
                                elif av.is_allocatable or av.is_pointer:
                                    count_c = _dim_product_from_parts(
                                        _resolved_dim_parts(av, arg_nm, assumed_extents),
                                        vars_map,
                                        real_type,
                                        byref_scalars,
                                        assumed_extents,
                                    )
                                else:
                                    count_c = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                            else:
                                if cty == "char *":
                                    ptr_c = arg_nm
                                    elem_size_c = "1"
                                    count_c = _simplify_int_expr_text(av.char_len) if av.char_len else "1"
                                else:
                                    ptr_c = f"&({arg_nm})"
                                    if cty == "int" or av.is_logical:
                                        elem_size_c = "sizeof(int)"
                                    elif cty in {"long long", "long long int"}:
                                        elem_size_c = "sizeof(long long)"
                                    else:
                                        elem_size_c = "sizeof(double)" if cty == "double" else "sizeof(float)"
                                    count_c = "1"
                    if ptr_c is not None and elem_size_c is not None and count_c is not None:
                        out.append(" " * indent + f"if (write_bytes_unit({unit_c}, (long) ({pos_c}), {ptr_c}, {elem_size_c}, {count_c}) != 0) {fail_stmt}")
                        continue
            # Support formatted/list-directed WRITE to stdout, including
            # USE iso_fortran_env, ONLY: output_unit ; write(unit=output_unit,...)
            if write_to_stdout:
                m_fmt_var = re.match(r"^\s*([a-z_]\w*)\s*$", fmt_txt or "", re.IGNORECASE)
                if m_fmt_var:
                    fmt_var = m_fmt_var.group(1).lower()
                    dyn_spec = dynamic_write_formats.get(fmt_var)
                    tail_fmt_var = tail[1:].strip() if tail.startswith(",") else tail
                    items_fmt_var = [x.strip() for x in _split_args_top_level(tail_fmt_var) if x.strip()]
                    if dyn_spec and len(items_fmt_var) == 3:
                        width_c = _convert_expr(dyn_spec[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        c0 = _convert_expr(items_fmt_var[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        c1 = _convert_expr(items_fmt_var[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        c2 = _convert_expr(items_fmt_var[2], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        if dyn_spec[0] == "a_a14_a14":
                            out.append(" " * indent + f'printf("%*s  %14s  %14s\\n", {width_c}, {c0}, {c1}, {c2});')
                            continue
                        if dyn_spec[0] == "a_f14_8_f14_8":
                            out.append(" " * indent + f'printf("%*s  %14.8f  %14.8f\\n", {width_c}, {c0}, {c1}, {c2});')
                            continue
                if fmt_txt is not None and _is_fortran_string_literal(fmt_txt):
                    tail_fmt = tail[1:].strip() if tail.startswith(",") else tail
                    items_fmt = [x.strip() for x in _split_args_top_level(tail_fmt) if x.strip()]
                    fmt_clean = _unquote_fortran_string_literal(fmt_txt).strip().lower()
                    if fmt_clean == '(a)' and len(items_fmt) == 1 and _emit_string_concat_expr(out, indent, items_fmt[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names, newline_each=True):
                        continue
                    if len(items_fmt) == 1 and _emit_implied_do_formatted_output(out, indent, fmt_txt, items_fmt[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                        continue
                    if _emit_basic_formatted_items_output(out, indent, fmt_txt, items_fmt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names):
                        continue
                if tail.startswith(","):
                    tail = tail[1:].strip()
                if not tail:
                    out.append(" " * indent + 'printf("\\n");')
                    continue
                items = [x.strip() for x in _split_args_top_level(tail) if x.strip()]
                if len(items) == 1:
                    expr0 = items[0]
                    m_pack_call = re.match(r"^pack\s*\((.*)\)\s*$", expr0, re.IGNORECASE)
                    if m_pack_call:
                        pargs = [x.strip() for x in _split_args_top_level(m_pack_call.group(1)) if x.strip()]
                        if len(pargs) >= 2:
                            m_arr = re.match(r"^([a-z_]\w*)$", pargs[0], re.IGNORECASE)
                            m_mask = re.match(r"^([a-z_]\w*)$", pargs[1], re.IGNORECASE)
                            if m_arr and m_mask:
                                an = m_arr.group(1).lower()
                                mn = m_mask.group(1).lower()
                                av = vars_map.get(an)
                                mv = vars_map.get(mn)
                                if av is not None and mv is not None and av.is_array and mv.is_array:
                                    npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                    cty = (av.ctype or real_type).lower()
                                    efmt = "%d" if cty == "int" else "%g"
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + "int __first = 1;")
                                    out.append(" " * (indent + 3) + f"for (int i_wr = 0; i_wr < {npr}; ++i_wr) {{")
                                    out.append(" " * (indent + 6) + f"if ({mn}[i_wr]) {{")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", {an}[i_wr]);')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                    out.append(" " * (indent + 3) + 'printf("\\n");')
                                    out.append(" " * indent + "}")
                                    continue
                    m_sum_call = re.match(r"^sum\s*\((.*)\)\s*$", expr0, re.IGNORECASE)
                    if m_sum_call:
                        sargs = [x.strip() for x in _split_args_top_level(m_sum_call.group(1)) if x.strip()]
                        if sargs:
                            arg0 = sargs[0]
                            dim_no = None
                            mask_arg: Optional[str] = None
                            if len(sargs) >= 2:
                                s1 = sargs[1]
                                m_dim_kw = re.match(r"(?i)^dim\s*=\s*([0-9]+)$", s1)
                                m_mask_kw = re.match(r"(?i)^mask\s*=\s*(.+)$", s1)
                                if m_dim_kw:
                                    dim_no = int(m_dim_kw.group(1))
                                elif m_mask_kw:
                                    mask_arg = m_mask_kw.group(1).strip()
                                elif re.fullmatch(r"[0-9]+", s1):
                                    dim_no = int(s1)
                                else:
                                    mask_arg = s1
                            if dim_no is None:
                                arr_tokens_0 = [t for t in sorted({t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(arg0), flags=re.IGNORECASE)}) if t in vars_map and vars_map[t].is_array]
                                arr_tokens_m = []
                                if mask_arg:
                                    arr_tokens_m = [t for t in sorted({t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(mask_arg), flags=re.IGNORECASE)}) if t in vars_map and vars_map[t].is_array]
                                all_arrs = arr_tokens_0 + [a for a in arr_tokens_m if a not in arr_tokens_0]
                                if all_arrs:
                                    base = vars_map.get(all_arrs[0])
                                    assert base is not None
                                    compatible = all((vars_map.get(a) is not None and vars_map.get(a).dim == base.dim) for a in all_arrs)
                                    if compatible:
                                        npr = _dim_product_expr(base.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                        expr_i = arg0
                                        for a in sorted(all_arrs, key=len, reverse=True):
                                            expr_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_wr]", expr_i, flags=re.IGNORECASE)
                                        mask_i = "1"
                                        if mask_arg:
                                            mask_i = mask_arg
                                            for a in sorted(all_arrs, key=len, reverse=True):
                                                mask_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_wr]", mask_i, flags=re.IGNORECASE)
                                        cexpr_i = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        cmask_i = _convert_expr(mask_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        cty = (base.ctype or real_type).lower()
                                        efmt = "%d" if cty == "int" else "%g"
                                        out.append(" " * indent + "{")
                                        out.append(" " * (indent + 3) + f"{base.ctype} __sum = 0;")
                                        out.append(" " * (indent + 3) + f"for (int i_wr = 0; i_wr < {npr}; ++i_wr) {{")
                                        out.append(" " * (indent + 6) + f"if ({cmask_i}) __sum += {cexpr_i};")
                                        out.append(" " * (indent + 3) + "}")
                                        out.append(" " * (indent + 3) + f'printf("{efmt}\\n", __sum);')
                                        out.append(" " * indent + "}")
                                        continue
                            m_arr0 = re.match(r"^([a-z_]\w*)$", sargs[0], re.IGNORECASE)
                            if m_arr0:
                                an = m_arr0.group(1).lower()
                                av = vars_map.get(an)
                                if av is not None and av.is_array:
                                    dparts = _resolved_dim_parts(av, an, assumed_extents)
                                    rank = len(dparts)
                                    cty = (av.ctype or real_type).lower()
                                    efmt = "%d" if cty == "int" else "%g"
                                    if mask_arg is not None and dim_no is None:
                                        npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                        mexpr = mask_arg
                                        for arrn, vv in vars_map.items():
                                            if vv.is_array and vv.dim == av.dim and re.search(rf"\b{re.escape(arrn)}\b", mexpr, re.IGNORECASE):
                                                mexpr = re.sub(rf"\b{re.escape(arrn)}\b", f"{arrn}[i_wr]", mexpr, flags=re.IGNORECASE)
                                        cmask = _convert_expr(mexpr, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        out.append(" " * indent + "{")
                                        out.append(" " * (indent + 3) + f"{av.ctype} __sum = 0;")
                                        out.append(" " * (indent + 3) + f"for (int i_wr = 0; i_wr < {npr}; ++i_wr) {{")
                                        out.append(" " * (indent + 6) + f"if ({cmask}) __sum += {an}[i_wr];")
                                        out.append(" " * (indent + 3) + "}")
                                        out.append(" " * (indent + 3) + f'printf("{efmt}\\n", __sum);')
                                        out.append(" " * indent + "}")
                                        continue
                                    if dim_no is None:
                                        csum = _convert_expr(expr0, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        out.append(" " * indent + f'printf("{efmt}\\n", {csum});')
                                        continue
                                    if rank == 1 and dim_no == 1:
                                        csum = _convert_expr(f"sum({an})", vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        out.append(" " * indent + f'printf("{efmt}\\n", {csum});')
                                        continue
                                    if rank in {2, 3} and 1 <= dim_no <= rank:
                                        d = [
                                            _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                            for k in range(rank)
                                        ]
                                        out.append(" " * indent + "{")
                                        out.append(" " * (indent + 3) + "int __first = 1;")
                                        out.append(" " * (indent + 3) + f"{av.ctype} __sum;")
                                        if rank == 2 and dim_no == 1:
                                            out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                            out.append(" " * (indent + 6) + "__sum = 0;")
                                            out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                            out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                            out.append(" " * (indent + 6) + "__first = 0;")
                                            out.append(" " * (indent + 3) + "}")
                                        elif rank == 2 and dim_no == 2:
                                            out.append(" " * (indent + 3) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                            out.append(" " * (indent + 6) + "__sum = 0;")
                                            out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1)];")
                                            out.append(" " * (indent + 6) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                            out.append(" " * (indent + 6) + "__first = 0;")
                                            out.append(" " * (indent + 3) + "}")
                                        elif rank == 3 and dim_no == 1:
                                            out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                            out.append(" " * (indent + 6) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                            out.append(" " * (indent + 9) + "__sum = 0;")
                                            out.append(" " * (indent + 9) + f"for (int i = 1; i <= {d[0]}; ++i) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                            out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                            out.append(" " * (indent + 9) + "__first = 0;")
                                            out.append(" " * (indent + 6) + "}")
                                            out.append(" " * (indent + 3) + "}")
                                        elif rank == 3 and dim_no == 2:
                                            out.append(" " * (indent + 3) + f"for (int k = 1; k <= {d[2]}; ++k) {{")
                                            out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                            out.append(" " * (indent + 9) + "__sum = 0;")
                                            out.append(" " * (indent + 9) + f"for (int j = 1; j <= {d[1]}; ++j) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                            out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                            out.append(" " * (indent + 9) + "__first = 0;")
                                            out.append(" " * (indent + 6) + "}")
                                            out.append(" " * (indent + 3) + "}")
                                        elif rank == 3 and dim_no == 3:
                                            out.append(" " * (indent + 3) + f"for (int j = 1; j <= {d[1]}; ++j) {{")
                                            out.append(" " * (indent + 6) + f"for (int i = 1; i <= {d[0]}; ++i) {{")
                                            out.append(" " * (indent + 9) + "__sum = 0;")
                                            out.append(" " * (indent + 9) + f"for (int k = 1; k <= {d[2]}; ++k) __sum += {an}[(i - 1) + ({d[0]}) * (j - 1) + ({d[0]}) * ({d[1]}) * (k - 1)];")
                                            out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", __sum);')
                                            out.append(" " * (indent + 9) + "__first = 0;")
                                            out.append(" " * (indent + 6) + "}")
                                            out.append(" " * (indent + 3) + "}")
                                        out.append(" " * (indent + 3) + 'printf("\\n");')
                                        out.append(" " * indent + "}")
                                        continue
                    m_vsub1 = re.match(r"^([a-z_]\w*)\s*\(\s*(.+)\s*\)\s*$", items[0], re.IGNORECASE)
                    if m_vsub1:
                        an = m_vsub1.group(1).lower()
                        av = vars_map.get(an)
                        inner = m_vsub1.group(2).strip()
                        if av is not None and av.is_array and len(_resolved_dim_parts(av, an, assumed_extents)) == 1:
                            m_ctor_idx = re.match(r"^\[\s*(.*)\s*\]$", inner)
                            cty = (av.ctype or real_type).lower()
                            efmt = "%d" if cty == "int" else "%g"
                            if m_ctor_idx:
                                idx_items = [x.strip() for x in _split_args_top_level(m_ctor_idx.group(1)) if x.strip()]
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                for iv in idx_items:
                                    civ = _convert_expr(iv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * (indent + 3) + f'printf("%s{efmt}", __first ? "" : " ", {an}[({civ}) - 1]);')
                                    out.append(" " * (indent + 3) + "__first = 0;")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                                continue
                            m_idx_arr = re.match(r"^([a-z_]\w*)$", inner, re.IGNORECASE)
                            if m_idx_arr:
                                idxn = m_idx_arr.group(1).lower()
                                ivv = vars_map.get(idxn)
                                if ivv is not None and ivv.is_array:
                                    if ivv.is_allocatable:
                                        nidx = _dim_product_from_parts(
                                            _resolved_dim_parts(ivv, idxn, assumed_extents),
                                            vars_map,
                                            real_type,
                                            byref_scalars,
                                            assumed_extents,
                                        )
                                    else:
                                        nidx = _dim_product_expr(ivv.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                                    out.append(" " * indent + f"for (int i_wr = 0; i_wr < {nidx}; ++i_wr) {{")
                                    out.append(" " * (indent + 3) + f"int __iv = {idxn}[i_wr];")
                                    out.append(" " * (indent + 3) + f'printf("{efmt}%s", {an}[__iv - 1], (i_wr + 1 < {nidx}) ? " " : "\\n");')
                                    out.append(" " * indent + "}")
                                    continue
                    m_sec = _match_whole_name_call(items[0])
                    if m_sec:
                        an = m_sec[0].lower()
                        av = vars_map.get(an)
                        if av is not None and av.is_array:
                            idx_parts = _split_args_top_level(m_sec[1])
                            dparts = _resolved_dim_parts(av, an, assumed_extents)
                            rank = len(dparts)
                            if rank in {2, 3} and len(idx_parts) == rank:
                                cty = (av.ctype or real_type).lower()
                                efmt = "%d" if cty == "int" else "%g"
                                dimc = [
                                    _convert_expr(dparts[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    for k in range(rank)
                                ]

                                def _parse_dim_spec_w(txt: str, dflt_hi: str) -> dict:
                                    t = txt.strip()
                                    m_ctor = re.match(r"^\[\s*(.*)\s*\]$", t)
                                    if m_ctor:
                                        vals = [x.strip() for x in _split_args_top_level(m_ctor.group(1)) if x.strip()]
                                        cvals = [
                                            _convert_expr(vv, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                            for vv in vals
                                        ]
                                        return {"kind": "vec", "vals": cvals}
                                    if ":" in t:
                                        sp = _split_colon_top_level(t)
                                        lo = _convert_expr((sp[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        hi = _convert_expr((sp[1] or dflt_hi).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        st = _convert_expr((sp[2] if len(sp) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                        return {"kind": "sec", "lo": lo, "hi": hi, "st": st}
                                    val = _convert_expr(t, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    return {"kind": "scalar", "val": val}

                                specs = [_parse_dim_spec_w(idx_parts[k], dimc[k]) for k in range(rank)]
                                if any(sp["kind"] != "scalar" for sp in specs):
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + "int __first = 1;")
                                    idx_map: Dict[int, str] = {}

                                    def _lin_expr_w() -> str:
                                        i1 = idx_map.get(1, "1")
                                        lin = f"(({i1}) - 1)"
                                        if rank >= 2:
                                            i2 = idx_map.get(2, "1")
                                            lin = f"{lin} + ({dimc[0]}) * (({i2}) - 1)"
                                        if rank >= 3:
                                            i3 = idx_map.get(3, "1")
                                            lin = f"{lin} + ({dimc[0]}) * ({dimc[1]}) * (({i3}) - 1)"
                                        return lin

                                    def _emit_dim_w(dim_k: int, ind: int) -> None:
                                        if dim_k < 1:
                                            lin = _lin_expr_w()
                                            out.append(" " * ind + f'printf("%s{efmt}", __first ? "" : " ", {an}[{lin}]);')
                                            out.append(" " * ind + "__first = 0;")
                                            return
                                        sp = specs[dim_k - 1]
                                        if sp["kind"] == "scalar":
                                            idx_map[dim_k] = sp["val"]
                                            _emit_dim_w(dim_k - 1, ind)
                                            return
                                        if sp["kind"] == "vec":
                                            for vv in sp["vals"]:
                                                idx_map[dim_k] = vv
                                                _emit_dim_w(dim_k - 1, ind)
                                            return
                                        vnm = f"__i{dim_k}"
                                        idx_map[dim_k] = vnm
                                        out.append(" " * ind + f"for (int {vnm} = {sp['lo']}; ({sp['st']}) > 0 ? {vnm} <= {sp['hi']} : {vnm} >= {sp['hi']}; {vnm} += {sp['st']}) {{")
                                        _emit_dim_w(dim_k - 1, ind + 3)
                                        out.append(" " * ind + "}")

                                    _emit_dim_w(rank, indent + 3)
                                    out.append(" " * (indent + 3) + 'printf("\\n");')
                                    out.append(" " * indent + "}")
                                    continue
                            if len(idx_parts) == 2 and len(dparts) >= 2:
                                d1 = _convert_expr(dparts[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                d2 = _convert_expr(dparts[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                cty = (av.ctype or real_type).lower()
                                efmt = "%d" if cty == "int" else "%g"
                                sec0 = ":" in idx_parts[0]
                                sec1 = ":" in idx_parts[1]
                                if sec0 or sec1:
                                    if sec0:
                                        sp0 = _split_colon_top_level(idx_parts[0].strip())
                                        if len(sp0) not in {2, 3}:
                                            sp0 = [idx_parts[0].strip(), idx_parts[0].strip(), "1"]
                                    else:
                                        sp0 = [idx_parts[0].strip(), idx_parts[0].strip(), "1"]
                                    if sec1:
                                        sp1 = _split_colon_top_level(idx_parts[1].strip())
                                        if len(sp1) not in {2, 3}:
                                            sp1 = [idx_parts[1].strip(), idx_parts[1].strip(), "1"]
                                    else:
                                        sp1 = [idx_parts[1].strip(), idx_parts[1].strip(), "1"]
                                    i1_lo = _convert_expr((sp0[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    i1_hi = _convert_expr((sp0[1] or d1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    i1_st = _convert_expr((sp0[2] if len(sp0) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    i2_lo = _convert_expr((sp1[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    i2_hi = _convert_expr((sp1[1] or d2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    i2_st = _convert_expr((sp1[2] if len(sp1) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + "int __first = 1;")
                                    out.append(" " * (indent + 3) + f"for (int j_wr = {i2_lo}; ({i2_st}) > 0 ? j_wr <= {i2_hi} : j_wr >= {i2_hi}; j_wr += {i2_st}) {{")
                                    out.append(" " * (indent + 6) + f"for (int i_wr = {i1_lo}; ({i1_st}) > 0 ? i_wr <= {i1_hi} : i_wr >= {i1_hi}; i_wr += {i1_st}) {{")
                                    out.append(" " * (indent + 9) + f"int __lin = (i_wr - 1) + ({d1}) * (j_wr - 1);")
                                    out.append(" " * (indent + 9) + f'printf("%s{efmt}", __first ? "" : " ", {an}[__lin]);')
                                    out.append(" " * (indent + 9) + "__first = 0;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                    out.append(" " * (indent + 3) + 'printf("\\n");')
                                    out.append(" " * indent + "}")
                                    continue
                    m_arr = re.match(r"^([a-z_]\w*)$", items[0], re.IGNORECASE)
                    if m_arr:
                        an = m_arr.group(1).lower()
                        av = vars_map.get(an)
                        if av is not None and av.is_array:
                            if av.is_allocatable or av.is_pointer:
                                npr = _dim_product_from_parts(
                                    _resolved_dim_parts(av, an, assumed_extents),
                                    vars_map,
                                    real_type,
                                    byref_scalars,
                                    assumed_extents,
                                )
                            else:
                                npr = _dim_product_expr(av.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                            cty = (av.ctype or real_type).lower()
                            if cty == "char *":
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __first = 1;")
                                out.append(" " * (indent + 3) + f"for (int i_wr = 0; i_wr < {npr}; ++i_wr) {{")
                                out.append(" " * (indent + 6) + f'printf("%s%.*s", __first ? "" : " ", len_trim_s({an}[i_wr]), {an}[i_wr]);')
                                out.append(" " * (indent + 6) + "__first = 0;")
                                out.append(" " * (indent + 3) + "}")
                                out.append(" " * (indent + 3) + 'printf("\\n");')
                                out.append(" " * indent + "}")
                            else:
                                efmt = "%d" if cty == "int" else "%g"
                                out.append(" " * indent + f"for (int i_wr = 0; i_wr < {npr}; ++i_wr) {{")
                                out.append(" " * (indent + 3) + f'printf("{efmt}%s", {an}[i_wr], (i_wr + 1 < {npr}) ? " " : "\\n");')
                                out.append(" " * indent + "}")
                            continue
                    expr0 = items[0]
                    toks0 = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(expr0), flags=re.IGNORECASE)}
                    arrs0 = [t for t in sorted(toks0) if t in vars_map and vars_map[t].is_array]
                    if arrs0 and not any(re.search(rf"\b{re.escape(a)}\s*\(", expr0, flags=re.IGNORECASE) for a in arrs0):
                        base = vars_map.get(arrs0[0])
                        compatible = base is not None and all((vars_map.get(a) is not None and vars_map.get(a).dim == base.dim) for a in arrs0)
                        if compatible and base is not None:
                            if (base.is_allocatable or base.is_pointer) and len(_dim_parts(base.dim)) == 1:
                                npr = _alloc_len_name(arrs0[0])
                            else:
                                npr = _dim_product_expr(base.dim or "1", vars_map, real_type, byref_scalars, assumed_extents)
                            expr_i = expr0
                            for a in sorted(arrs0, key=len, reverse=True):
                                expr_i = re.sub(rf"\b{re.escape(a)}\b", f"{a}[i_wr]", expr_i, flags=re.IGNORECASE)
                            cit = _convert_expr(expr_i, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            out.append(" " * indent + f"for (int i_wr = 0; i_wr < {npr}; ++i_wr) {{")
                            out.append(" " * (indent + 3) + f'printf("%g%s", {cit}, (i_wr + 1 < {npr}) ? " " : "\\n");')
                            out.append(" " * indent + "}")
                            continue
                fmts: List[str] = []
                cargs: List[str] = []
                ctypes_ld: List[str] = []
                for it in items:
                    if (it.startswith('"') and it.endswith('"')) or (it.startswith("'") and it.endswith("'")):
                        content = it[1:-1].replace('\\', '\\\\').replace('"', '\\"')
                        cargs.append(f'"{content}"')
                        ctypes_ld.append('string')
                        fmts.append(_list_directed_scalar_fmt('string'))
                        continue
                    cit = _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    cargs.append(cit)
                    cty = _format_item_ctype(it, vars_map, real_type)
                    ctypes_ld.append(cty)
                    fmts.append(_list_directed_scalar_fmt(cty))
                trail = '    ' if _list_directed_has_trailing_real(ctypes_ld) else ''
                prefix = ' ' if ctypes_ld and all((ct or '').lower() == 'string' for ct in ctypes_ld) else ''
                out.append(" " * indent + f'printf("{prefix}{"".join(fmts)}{trail}\\n", {", ".join(cargs)});')
                continue
            mixed_parts: List[tuple[str, str]] = []
            mixed_supported = True
            for pit in items:
                if _is_fortran_string_literal(pit.strip()):
                    lit = _unquote_fortran_string_literal(pit.strip()).replace("\\", "\\\\").replace('"', '\\"')
                    mixed_parts.append(("string", f'"{lit}"'))
                    continue
                m_trim = re.match(r"^\s*trim\s*\(\s*([a-z_]\w*)\s*\)\s*$", pit, re.IGNORECASE)
                if m_trim:
                    nm_trim = m_trim.group(1).lower()
                    mixed_parts.append(("trim_string", nm_trim))
                    continue
                m_intr_mix = re.match(r"^(size|rank|shape|lbound|ubound)\s*\((.*)\)\s*$", pit, re.IGNORECASE)
                if m_intr_mix:
                    inm = m_intr_mix.group(1).lower()
                    iargs = [x.strip() for x in _split_args_top_level(m_intr_mix.group(2)) if x.strip()]
                    if not iargs:
                        mixed_supported = False
                        break
                    a0 = iargs[0].lower()
                    av0 = vars_map.get(a0)
                    if av0 is None or (not av0.is_array):
                        mixed_supported = False
                        break
                    dparts0 = _resolved_dim_parts(av0, a0, assumed_extents)
                    if inm in {"size", "rank"} or len(iargs) >= 2 or len(dparts0) == 1:
                        cexpr0 = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        mixed_parts.append(("int", cexpr0))
                        continue
                    vals0: List[str] = []
                    if inm == "shape":
                        vals0 = [_dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts0]
                    elif inm == "lbound":
                        vals0 = [_dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents) for p in dparts0]
                    else:
                        for p in dparts0:
                            lo0 = _dim_lb_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                            ex0 = _dim_extent_expr(p, vars_map, real_type, byref_scalars, assumed_extents)
                            vals0.append(f"(({lo0}) + ({ex0}) - 1)")
                    mixed_parts.extend(("int", vv) for vv in vals0)
                    continue
                m_simple = re.match(r"^([a-z_]\w*)$", pit, re.IGNORECASE)
                if m_simple:
                    vv = vars_map.get(m_simple.group(1).lower())
                    if vv is not None and vv.is_array:
                        mixed_supported = False
                        break
                toks_p = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(pit), flags=re.IGNORECASE)}
                if any((vars_map.get(t) is not None and vars_map[t].is_array) for t in toks_p):
                    mixed_supported = False
                    break
                cty_p = _format_item_ctype(pit, vars_map, real_type)
                cexpr_p = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                mixed_parts.append((cty_p, cexpr_p))
            if mixed_supported and mixed_parts:
                out.append(" " * indent + "{")
                out.append(" " * (indent + 3) + "int __first = 1;")
                for cty_p, cexpr_p in mixed_parts:
                    _emit_list_directed_scalar_printf(
                        out,
                        indent + 3,
                        cexpr_p,
                        cty_p,
                        vars_map,
                        real_type,
                        prefix_expr='__first ? "" : " "',
                    )
                    out.append(" " * (indent + 3) + "__first = 0;")
                out.append(" " * (indent + 3) + 'printf("\\n");')
                out.append(" " * indent + "}")
                continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue

        m_ptr_asn = re.match(r"^([a-z_]\w*)\s*=>\s*(.+)$", code, re.IGNORECASE)
        if m_ptr_asn:
            lhs_nm = m_ptr_asn.group(1).lower()
            rhs_ptr = m_ptr_asn.group(2).strip()
            lv_ptr = vars_map.get(lhs_nm)
            if lv_ptr is not None and lv_ptr.is_pointer:
                if re.match(r"(?i)^null\s*\(\s*\)\s*$", rhs_ptr):
                    out.append(" " * indent + f"{lhs_nm} = NULL;")
                    if lv_ptr.is_array:
                        for en in _alloc_extent_names(lhs_nm, max(1, len(_dim_parts(lv_ptr.dim)))):
                            out.append(" " * indent + f"{en} = 0;")
                    continue
                if lv_ptr.is_array:
                    m_sec_ptr = re.match(
                        r"^([a-z_]\w*)\s*\(\s*([^:,\)]*)\s*:\s*([^:,\)]*)(?:\s*:\s*([^)]+))?\s*\)$",
                        rhs_ptr,
                        re.IGNORECASE,
                    )
                    if m_sec_ptr:
                        base_nm = m_sec_ptr.group(1).lower()
                        base_v = vars_map.get(base_nm)
                        if base_v is not None and base_v.is_array and len(_resolved_dim_parts(base_v, base_nm, assumed_extents)) == 1:
                            lo = _convert_expr((m_sec_ptr.group(2) or "").strip() or "1", vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            hi_raw = (m_sec_ptr.group(3) or "").strip()
                            st = _convert_expr((m_sec_ptr.group(4) or "").strip() or "1", vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            base_parts = _resolved_dim_parts(base_v, base_nm, assumed_extents)
                            hi = _convert_expr(hi_raw or (base_parts[0] if base_parts else "1"), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            out.append(" " * indent + f"{lhs_nm} = &{base_nm}[({lo}) - 1];")
                            out.append(" " * indent + f"{_alloc_len_name(lhs_nm)} = {_section_count_expr(lo, hi, st)};")
                            continue
                    m_arr_ptr = re.match(r"^([a-z_]\w*)$", rhs_ptr, re.IGNORECASE)
                    if m_arr_ptr:
                        base_nm = m_arr_ptr.group(1).lower()
                        base_v = vars_map.get(base_nm)
                        if base_v is not None and base_v.is_array and len(_resolved_dim_parts(base_v, base_nm, assumed_extents)) == 1:
                            out.append(" " * indent + f"{lhs_nm} = {base_nm};")
                            out.append(" " * indent + f"{_alloc_len_name(lhs_nm)} = {_dim_product_from_parts(_resolved_dim_parts(base_v, base_nm, assumed_extents), vars_map, real_type, byref_scalars, assumed_extents)};")
                            continue
                else:
                    m_id_ptr = re.match(r"^([a-z_]\w*)$", rhs_ptr, re.IGNORECASE)
                    if m_id_ptr:
                        out.append(" " * indent + f"{lhs_nm} = &{m_id_ptr.group(1).lower()};")
                        continue
            out.append(" " * indent + f"/* unsupported: {code} */")
            continue

        m_asn = re.match(r"^(.+?)\s*=\s*(.+)$", code, re.IGNORECASE)
        if m_asn:
            lhs_raw = m_asn.group(1).strip()
            rhs_raw = m_asn.group(2).strip()
            if use_implicit_result and lhs_raw.lower() == unit_name_l:
                lhs_raw = implicit_result_name
            m_lhs_col_runif = re.match(r"^([a-z_]\w*)\s*\(\s*:\s*,\s*([^)]+)\s*\)\s*$", lhs_raw, re.IGNORECASE)
            m_lhs_runif = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
            m_rhs_runif_1d = re.match(r"^runif_1d\s*\(\s*(.+)\s*\)\s*$", rhs_raw, re.IGNORECASE)
            if m_lhs_col_runif and m_rhs_runif_1d:
                lhs_nm_runif = m_lhs_col_runif.group(1).lower()
                lv_runif = vars_map.get(lhs_nm_runif)
                if lv_runif is not None and lv_runif.is_array:
                    dparts_runif = _resolved_dim_parts(lv_runif, lhs_nm_runif, assumed_extents)
                    if len(dparts_runif) == 2:
                        col_c = _convert_expr(m_lhs_col_runif.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        d1_c = _convert_expr(dparts_runif[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        n1_c = _convert_expr(m_rhs_runif_1d.group(1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        out.append(" " * indent + f"fill_runif_1d({n1_c}, &{lhs_nm_runif}[({d1_c}) * ((({col_c})) - 1)]);")
                        continue
            if m_lhs_runif and m_rhs_runif_1d:
                lhs_nm_runif = m_lhs_runif.group(1).lower()
                lv_runif = vars_map.get(lhs_nm_runif)
                if lv_runif is not None and lv_runif.is_array:
                    n1_c = _convert_expr(m_rhs_runif_1d.group(1).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    if lv_runif.is_allocatable:
                        cty = lv_runif.ctype or real_type
                        out.append(" " * indent + f"if ({lhs_nm_runif}) free({lhs_nm_runif});")
                        out.append(" " * indent + f"{lhs_nm_runif} = ({cty}*) malloc(sizeof({cty}) * ({n1_c}));")
                        out.append(" " * indent + f"if (!{lhs_nm_runif} && ({n1_c}) > 0) {fail_stmt}")
                        if len(_dim_parts(lv_runif.dim)) == 1:
                            out.append(" " * indent + f"{_alloc_len_name(lhs_nm_runif)} = {n1_c};")
                    out.append(" " * indent + f"fill_runif_1d({n1_c}, {lhs_nm_runif});")
                    continue
            m_lhs_whole_ctor = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
            m_rhs_ctor = re.match(r"^\[\s*(.*)\s*\]\s*$", rhs_raw)
            if m_lhs_whole_ctor and m_rhs_ctor:
                lhs_nm_ctor = m_lhs_whole_ctor.group(1).lower()
                lv_ctor = vars_map.get(lhs_nm_ctor)
                if lv_ctor is not None and lv_ctor.is_array:
                    ctor_inner = m_rhs_ctor.group(1).strip()
                    ctor_items = _split_args_top_level(ctor_inner) if ctor_inner else []
                    n_ctor = len([x for x in ctor_items if x.strip()])
                    if lv_ctor.is_allocatable:
                        out.append(" " * indent + f"if ({lhs_nm_ctor}) free({lhs_nm_ctor});")
                        out.append(" " * indent + f"{lhs_nm_ctor} = ({lv_ctor.ctype}*) malloc(sizeof({lv_ctor.ctype}) * {n_ctor});")
                        out.append(" " * indent + f"if (!{lhs_nm_ctor} && {n_ctor} > 0) {fail_stmt}")
                        if len(_dim_parts(lv_ctor.dim)) == 1:
                            out.append(" " * indent + f"{_alloc_len_name(lhs_nm_ctor)} = {n_ctor};")
                    for k, it in enumerate([x.strip() for x in ctor_items if x.strip()]):
                        cv = _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        out.append(" " * indent + f"{lhs_nm_ctor}[{k}] = {cv};")
                    continue
            m_lhs_comp_ctor = re.match(r"^([a-z_]\w*(?:\s*%\s*[a-z_]\w*)*)$", lhs_raw, re.IGNORECASE)
            if m_lhs_comp_ctor and m_rhs_ctor and '%' in lhs_raw:
                parts = [x.strip().lower() for x in lhs_raw.split('%') if x.strip()]
                if len(parts) >= 2:
                    fld_spec = _derived_field_spec(parts[0], parts[1:], vars_map)
                    if fld_spec is not None and _emit_allocatable_component_array_ctor(
                        out,
                        indent,
                        _convert_expr(lhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names).rsplit('.', 1)[0],
                        parts[-1],
                        fld_spec,
                        [x.strip() for x in _split_args_top_level(m_rhs_ctor.group(1)) if x.strip()],
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    ):
                        continue
            # x = reshape([..], [..]) for allocatable arrays.
            m_lhs_whole = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
            m_rhs_reshape = re.match(r"^reshape\s*\((.*)\)\s*$", rhs_raw, re.IGNORECASE)
            if m_lhs_whole and m_rhs_reshape:
                lhs_nm_r = m_lhs_whole.group(1).lower()
                lv_r = vars_map.get(lhs_nm_r)
                if lv_r is not None and lv_r.is_array:
                    rargs = _split_args_top_level(m_rhs_reshape.group(1))
                    if len(rargs) >= 2:
                        src_raw = rargs[0].strip()
                        shp_raw = rargs[1].strip()
                        pad_raw = ""
                        order_raw = ""
                        extra_pos: List[str] = []
                        for extra in rargs[2:]:
                            extra_s = extra.strip()
                            m_pad_kw = re.match(r"(?i)^pad\s*=\s*(.+)$", extra_s)
                            if m_pad_kw:
                                pad_raw = m_pad_kw.group(1).strip()
                                continue
                            m_order_kw = re.match(r"(?i)^order\s*=\s*(.+)$", extra_s)
                            if m_order_kw:
                                order_raw = m_order_kw.group(1).strip()
                                continue
                            extra_pos.append(extra_s)
                        if extra_pos and not pad_raw:
                            pad_raw = extra_pos.pop(0)
                        if extra_pos and not order_raw:
                            order_raw = extra_pos.pop(0)
                        m_src_ctor = re.match(r"^\[\s*(.*)\s*\]$", src_raw)
                        m_shp_ctor = re.match(r"^\[\s*(.*)\s*\]$", shp_raw)
                        if m_src_ctor and m_shp_ctor:
                            src_items = [x.strip() for x in _split_args_top_level(m_src_ctor.group(1)) if x.strip()]
                            shp_items = [x.strip() for x in _split_args_top_level(m_shp_ctor.group(1)) if x.strip()]
                            pad_items: List[str] = []
                            order_items: List[str] = []
                            if pad_raw:
                                m_pad_ctor = re.match(r"^\[\s*(.*)\s*\]$", pad_raw)
                                if m_pad_ctor:
                                    pad_items = [x.strip() for x in _split_args_top_level(m_pad_ctor.group(1)) if x.strip()]
                                else:
                                    pad_items = [pad_raw]
                            if order_raw:
                                m_order_ctor = re.match(r"^\[\s*(.*)\s*\]$", order_raw)
                                if m_order_ctor:
                                    order_items = [x.strip() for x in _split_args_top_level(m_order_ctor.group(1)) if x.strip()]
                                else:
                                    order_items = [order_raw]
                            rank_lhs = max(1, len(_dim_parts(lv_r.dim)))
                            if len(shp_items) == rank_lhs:
                                shp_c = [_convert_expr(s, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for s in shp_items]
                                n_total = _dim_product_from_parts(shp_c, vars_map, real_type, byref_scalars, assumed_extents)
                                if lv_r.is_allocatable:
                                    exts = _alloc_extent_names(lhs_nm_r, rank_lhs)
                                    out.append(" " * indent + f"if ({lhs_nm_r}) free({lhs_nm_r});")
                                    out.append(" " * indent + f"{lhs_nm_r} = ({lv_r.ctype}*) malloc(sizeof({lv_r.ctype}) * ({n_total}));")
                                    out.append(" " * indent + f"if (!{lhs_nm_r} && ({n_total}) > 0) {fail_stmt}")
                                    for k, en in enumerate(exts):
                                        val = shp_c[k] if k < len(shp_c) else "1"
                                        out.append(" " * indent + f"{en} = {val};")
                                src_n = len(src_items)
                                if src_n > 0:
                                    order_perm: Optional[List[int]] = None
                                    if order_items and len(order_items) == rank_lhs:
                                        perm_vals: List[int] = []
                                        ok_perm = True
                                        for oit in order_items:
                                            oi_c = _convert_expr(oit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                            oi_v = _eval_int_expr(oi_c)
                                            if oi_v is None:
                                                ok_perm = False
                                                break
                                            perm_vals.append(int(oi_v))
                                        if ok_perm and sorted(perm_vals) == list(range(1, rank_lhs + 1)):
                                            order_perm = perm_vals
                                    if order_perm is not None:
                                        src_init = ", ".join(
                                            _convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                            for it in src_items
                                        )
                                        out.append(" " * indent + "{")
                                        out.append(" " * (indent + 3) + f"{lv_r.ctype} __reshape_src[] = {{{src_init}}};")
                                        pad_n = len(pad_items)
                                        if pad_n > 0:
                                            pad_init = ", ".join(
                                                _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                                for pit in pad_items
                                            )
                                            out.append(" " * (indent + 3) + f"{lv_r.ctype} __reshape_pad[] = {{{pad_init}}};")
                                        out.append(" " * (indent + 3) + "int __reshape_pos = 0;")
                                        idx_vars = [f"__r{k+1}" for k in range(rank_lhs)]

                                        def _emit_order_loop(depth: int, loop_indent: int) -> None:
                                            if depth >= len(order_perm):
                                                lin = _fortran_sub_to_linear(idx_vars, shp_c, vars_map, real_type, byref_scalars, assumed_extents)
                                                if pad_n > 0:
                                                    val_expr = f"((__reshape_pos < {src_n}) ? __reshape_src[__reshape_pos] : __reshape_pad[(__reshape_pos - {src_n}) % {pad_n}])"
                                                else:
                                                    val_expr = f"__reshape_src[__reshape_pos % {src_n}]"
                                                out.append(" " * loop_indent + f"{lhs_nm_r}[{lin}] = {val_expr};")
                                                out.append(" " * loop_indent + "__reshape_pos += 1;")
                                                return
                                            dim_idx = order_perm[len(order_perm) - 1 - depth]
                                            vnm = idx_vars[dim_idx - 1]
                                            hi = shp_c[dim_idx - 1]
                                            out.append(" " * loop_indent + f"for (int {vnm} = 1; {vnm} <= {hi}; ++{vnm}) {{")
                                            _emit_order_loop(depth + 1, loop_indent + 3)
                                            out.append(" " * loop_indent + "}")

                                        _emit_order_loop(0, indent + 3)
                                        out.append(" " * indent + "}")
                                    else:
                                        for k in range(src_n):
                                            cv = _convert_expr(src_items[k], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                            out.append(" " * indent + f"if ({k} < ({n_total})) {lhs_nm_r}[{k}] = {cv};")
                                        pad_n = len(pad_items)
                                        if pad_n > 0:
                                            for pk, pit in enumerate(pad_items):
                                                cp = _convert_expr(pit, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                                out.append(" " * indent + f"{lv_r.ctype} __pad_{pk} = {cp};")
                                            if pad_n == 1:
                                                out.append(" " * indent + f"for (int i_fill = {src_n}; i_fill < ({n_total}); ++i_fill) {lhs_nm_r}[i_fill] = __pad_0;")
                                            else:
                                                out.append(" " * indent + f"for (int i_fill = {src_n}; i_fill < ({n_total}); ++i_fill) {{")
                                                out.append(" " * (indent + 3) + f"switch ((i_fill - {src_n}) % {pad_n}) {{")
                                                for pk in range(pad_n):
                                                    out.append(" " * (indent + 3) + f"case {pk}: {lhs_nm_r}[i_fill] = __pad_{pk}; break;")
                                                out.append(" " * (indent + 3) + "default: break;")
                                                out.append(" " * (indent + 3) + "}")
                                                out.append(" " * indent + "}")
                                        elif src_n < 64:
                                            out.append(" " * indent + f"for (int i_fill = {src_n}; i_fill < ({n_total}); ++i_fill) {{")
                                            out.append(" " * (indent + 3) + f"{lhs_nm_r}[i_fill] = {lhs_nm_r}[i_fill % {src_n}];")
                                            out.append(" " * indent + "}")
                                        else:
                                            out.append(" " * indent + f"for (int i_fill = {src_n}; i_fill < ({n_total}); ++i_fill) {lhs_nm_r}[i_fill] = {lhs_nm_r}[i_fill % {src_n}];")
                                continue
            # Whole allocatable 1D assignment from section expression:
            # x = f(a(l:u:s), ...)
            m_lhs_whole_sec_expr = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
            if m_lhs_whole_sec_expr:
                lhs_nm = m_lhs_whole_sec_expr.group(1).lower()
                lv0 = vars_map.get(lhs_nm)
                if lv0 is not None and lv0.is_array and lv0.is_allocatable and len(_dim_parts(lv0.dim)) == 1:
                    def _rewrite_section_expr(expr: str) -> tuple[str, List[tuple[str, str, str, str]]]:
                        out_chars: List[str] = []
                        sections: List[tuple[str, str, str, str]] = []
                        i = 0
                        n = len(expr)
                        while i < n:
                            ch = expr[i]
                            if ch.isalpha() or ch == "_":
                                j = i + 1
                                while j < n and (expr[j].isalnum() or expr[j] == "_"):
                                    j += 1
                                name = expr[i:j]
                                k = j
                                while k < n and expr[k].isspace():
                                    k += 1
                                if k < n and expr[k] == "(":
                                    depth = 0
                                    in_s = False
                                    in_d = False
                                    p = k
                                    endp = -1
                                    while p < n:
                                        c = expr[p]
                                        if c == "'" and not in_d:
                                            if in_s and p + 1 < n and expr[p + 1] == "'":
                                                p += 2
                                                continue
                                            in_s = not in_s
                                            p += 1
                                            continue
                                        if c == '"' and not in_s:
                                            in_d = not in_d
                                            p += 1
                                            continue
                                        if not in_s and not in_d:
                                            if c == "(":
                                                depth += 1
                                            elif c == ")":
                                                depth -= 1
                                                if depth == 0:
                                                    endp = p
                                                    break
                                        p += 1
                                    if endp != -1:
                                        inside = expr[k + 1 : endp]
                                        parts = _split_colon_top_level(inside)
                                        if len(parts) in {2, 3}:
                                            arr = name.lower()
                                            vv = vars_map.get(arr)
                                            if vv is not None and vv.is_array and len(_dim_parts(vv.dim)) == 1:
                                                d0 = _dim_parts(vv.dim)[0] if _dim_parts(vv.dim) else "1"
                                                lo_raw = (parts[0] or "").strip() or "1"
                                                hi_raw = (parts[1] or "").strip()
                                                st_raw = (parts[2] if len(parts) == 3 else "").strip() or "1"
                                                lo = _convert_expr(lo_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                                if hi_raw:
                                                    hi = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                                else:
                                                    if vv.is_allocatable:
                                                        hi = _alloc_len_name(arr)
                                                    else:
                                                        hi = _convert_expr(d0, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                                st = _convert_expr(st_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                                idx = f"(({lo}) + (p_fill * ({st})))"
                                                out_chars.append(f"{arr}[{idx} - 1]")
                                                sections.append((arr, lo, hi, st))
                                                i = endp + 1
                                                continue
                                out_chars.append(ch)
                                i += 1
                                continue
                            out_chars.append(ch)
                            i += 1
                        return "".join(out_chars), sections

                    rhs_expr_raw, sec_infos = _rewrite_section_expr(rhs_raw)
                    if sec_infos:
                        rhs_tokens = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", _strip_comment(rhs_raw), flags=re.IGNORECASE)}
                        unresolved_whole = False
                        for an in sorted(rhs_tokens):
                            vv = vars_map.get(an)
                            if vv is None or (not vv.is_array):
                                continue
                            if re.search(rf"\b{re.escape(an)}\s*\(", rhs_raw, flags=re.IGNORECASE):
                                continue
                            unresolved_whole = True
                            break
                        if not unresolved_whole:
                            arr0, lo0, hi0, st0 = sec_infos[0]
                            vv0 = vars_map.get(arr0)
                            if vv0 is not None and vv0.is_array and len(_dim_parts(vv0.dim)) == 1:
                                rhs = _convert_expr(rhs_expr_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                nname = _alloc_len_name(lhs_nm)
                                self_ref = lhs_nm in rhs_tokens
                                out.append(" " * indent + "{")
                                out.append(" " * (indent + 3) + "int __n_tmp = 0;")
                                out.append(" " * (indent + 3) + f"if ({st0} > 0) {{")
                                out.append(" " * (indent + 6) + f"for (int i_fill = {lo0}; i_fill <= {hi0}; i_fill += {st0}) ++__n_tmp;")
                                out.append(" " * (indent + 3) + "} else {")
                                out.append(" " * (indent + 6) + f"for (int i_fill = {lo0}; i_fill >= {hi0}; i_fill += {st0}) ++__n_tmp;")
                                out.append(" " * (indent + 3) + "}")
                                if self_ref:
                                    if (lv0.ctype or "").lower() == "char *":
                                        out.append(" " * (indent + 3) + "char **__rhs_tmp = (char**) malloc(sizeof(char*) * __n_tmp);")
                                        out.append(" " * (indent + 3) + f"if (!__rhs_tmp && __n_tmp > 0) {fail_stmt}")
                                        out.append(" " * (indent + 3) + "for (int p_fill = 0; p_fill < __n_tmp; ++p_fill) __rhs_tmp[p_fill] = NULL;")
                                        out.append(" " * (indent + 3) + "for (int p_fill = 0; p_fill < __n_tmp; ++p_fill) {")
                                        out.append(" " * (indent + 6) + f"assign_str_alloc(&__rhs_tmp[p_fill], {rhs});")
                                        out.append(" " * (indent + 3) + "}")
                                        out.append(" " * (indent + 3) + f"if ({lhs_nm}) free_str_array({lhs_nm}, {nname});")
                                        out.append(" " * (indent + 3) + f"{lhs_nm} = __rhs_tmp;")
                                    else:
                                        out.append(" " * (indent + 3) + f"{lv0.ctype} *__rhs_tmp = ({lv0.ctype}*) malloc(sizeof({lv0.ctype}) * __n_tmp);")
                                        out.append(" " * (indent + 3) + f"if (!__rhs_tmp && __n_tmp > 0) {fail_stmt}")
                                        out.append(" " * (indent + 3) + "for (int p_fill = 0; p_fill < __n_tmp; ++p_fill) {")
                                        out.append(" " * (indent + 6) + f"__rhs_tmp[p_fill] = {rhs};")
                                        out.append(" " * (indent + 3) + "}")
                                        out.append(" " * (indent + 3) + f"if ({lhs_nm}) free({lhs_nm});")
                                        out.append(" " * (indent + 3) + f"{lhs_nm} = __rhs_tmp;")
                                    out.append(" " * (indent + 3) + f"{nname} = __n_tmp;")
                                else:
                                    if (lv0.ctype or "").lower() == "char *":
                                        out.append(" " * (indent + 3) + f"if ({lhs_nm}) free_str_array({lhs_nm}, {nname});")
                                        out.append(" " * (indent + 3) + f"{lhs_nm} = (char**) malloc(sizeof(char*) * __n_tmp);")
                                        out.append(" " * (indent + 3) + f"if (!{lhs_nm} && __n_tmp > 0) {fail_stmt}")
                                        out.append(" " * (indent + 3) + f"for (int p_fill = 0; p_fill < __n_tmp; ++p_fill) {lhs_nm}[p_fill] = NULL;")
                                    else:
                                        out.append(" " * (indent + 3) + f"if ({lhs_nm}) free({lhs_nm});")
                                        out.append(" " * (indent + 3) + f"{lhs_nm} = ({lv0.ctype}*) malloc(sizeof({lv0.ctype}) * __n_tmp);")
                                        out.append(" " * (indent + 3) + f"if (!{lhs_nm} && __n_tmp > 0) {fail_stmt}")
                                    out.append(" " * (indent + 3) + f"{nname} = __n_tmp;")
                                    out.append(" " * (indent + 3) + "for (int p_fill = 0; p_fill < __n_tmp; ++p_fill) {")
                                    if (lv0.ctype or "").lower() == "char *":
                                        out.append(" " * (indent + 6) + f"assign_str_alloc(&{lhs_nm}[p_fill], {rhs});")
                                    else:
                                        out.append(" " * (indent + 6) + f"{lhs_nm}[p_fill] = {rhs};")
                                    out.append(" " * (indent + 3) + "}")
                                out.append(" " * indent + "}")
                                continue
            m_lhs_row = re.match(r"^([a-z_]\w*)\s*\(\s*([^,\)]*)\s*,\s*:\s*\)$", lhs_raw, re.IGNORECASE)
            if m_lhs_row:
                lhs_nm_sec = m_lhs_row.group(1).lower()
                lv_sec = vars_map.get(lhs_nm_sec)
                if lv_sec is not None and lv_sec.is_array and len(_dim_parts(lv_sec.dim)) == 2:
                    dparts2 = _dim_parts(lv_sec.dim)
                    row = _convert_expr((m_lhs_row.group(2) or "").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    ncol = _convert_expr(dparts2[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    rhs_expr_raw = rhs_raw
                    rhs_scan = _strip_comment(rhs_raw)
                    rhs_tokens = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", rhs_scan, flags=re.IGNORECASE)}
                    unresolved_whole_array = False
                    for an in sorted(rhs_tokens):
                        vv = vars_map.get(an)
                        if vv is None or (not vv.is_array):
                            continue
                        if re.search(rf"\b{re.escape(an)}\s*\(", rhs_raw, flags=re.IGNORECASE):
                            continue
                        if len(_dim_parts(vv.dim)) == 1:
                            rhs_expr_raw = re.sub(rf"\b{re.escape(an)}\b", f"{an}[p_fill]", rhs_expr_raw, flags=re.IGNORECASE)
                        else:
                            unresolved_whole_array = True
                            break
                    if not unresolved_whole_array:
                        rhs = _convert_expr(rhs_expr_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        out.append(" " * indent + f"for (int p_fill = 0; p_fill < {ncol}; ++p_fill) {{")
                        out.append(" " * (indent + 3) + f"{lhs_nm_sec}[(({row}) - 1) + ({dparts2[0]}) * p_fill] = {rhs};")
                        out.append(" " * indent + "}")
                        continue
            m_lhs_col = re.match(r"^([a-z_]\w*)\s*\(\s*:\s*,\s*([^,\)]*)\s*\)$", lhs_raw, re.IGNORECASE)
            if m_lhs_col:
                lhs_nm_sec = m_lhs_col.group(1).lower()
                lv_sec = vars_map.get(lhs_nm_sec)
                if lv_sec is not None and lv_sec.is_array and len(_dim_parts(lv_sec.dim)) == 2:
                    dparts2 = _dim_parts(lv_sec.dim)
                    col = _convert_expr((m_lhs_col.group(2) or "").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    nrow = _convert_expr(dparts2[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    rhs_expr_raw = rhs_raw
                    rhs_scan = _strip_comment(rhs_raw)
                    rhs_tokens = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", rhs_scan, flags=re.IGNORECASE)}
                    unresolved_whole_array = False
                    for an in sorted(rhs_tokens):
                        vv = vars_map.get(an)
                        if vv is None or (not vv.is_array):
                            continue
                        if re.search(rf"\b{re.escape(an)}\s*\(", rhs_raw, flags=re.IGNORECASE):
                            continue
                        if len(_dim_parts(vv.dim)) == 1:
                            rhs_expr_raw = re.sub(rf"\b{re.escape(an)}\b", f"{an}[p_fill]", rhs_expr_raw, flags=re.IGNORECASE)
                        else:
                            unresolved_whole_array = True
                            break
                    if not unresolved_whole_array:
                        rhs = _convert_expr(rhs_expr_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        out.append(" " * indent + f"for (int p_fill = 0; p_fill < {nrow}; ++p_fill) {{")
                        out.append(" " * (indent + 3) + f"{lhs_nm_sec}[p_fill + ({dparts2[0]}) * ((({col}) - 1))] = {rhs};")
                        out.append(" " * indent + "}")
                        continue
            m_lhs_sec = re.match(
                r"^([a-z_]\w*)\s*\(\s*([^:,\)]*)\s*:\s*([^:,\)]*)(?:\s*:\s*([^)]+))?\s*\)$",
                lhs_raw,
                re.IGNORECASE,
            )
            if m_lhs_sec:
                lhs_nm_sec = m_lhs_sec.group(1).lower()
                lv_sec = vars_map.get(lhs_nm_sec)
                if lv_sec is not None and lv_sec.is_array and len(_dim_parts(lv_sec.dim)) == 1:
                    d0 = _dim_parts(lv_sec.dim)[0] if _dim_parts(lv_sec.dim) else "1"
                    lo_raw = (m_lhs_sec.group(2) or "").strip() or "1"
                    hi_raw = (m_lhs_sec.group(3) or "").strip() or d0
                    st_raw = (m_lhs_sec.group(4) or "").strip() or "1"
                    lo = _convert_expr(lo_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    hi = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    st = _convert_expr(st_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    rhs_scan = _strip_comment(rhs_raw)
                    rhs_tokens = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", rhs_scan, flags=re.IGNORECASE)}

                    rhs_expr_raw = rhs_raw
                    # Map RHS 1D sections to element access driven by section position p_fill.
                    sec_pat = re.compile(
                        r"\b([a-z_]\w*)\s*\(\s*([^():,\)]*)\s*:\s*([^():,\)]*)(?:\s*:\s*([^():,\)]+))?\s*\)",
                        re.IGNORECASE,
                    )

                    def _rhs_sec_repl(mm: re.Match[str]) -> str:
                        arr = mm.group(1).lower()
                        vv = vars_map.get(arr)
                        if vv is None or (not vv.is_array) or len(_dim_parts(vv.dim)) != 1:
                            return mm.group(0)
                        rdim0 = _dim_parts(vv.dim)[0] if _dim_parts(vv.dim) else "1"
                        rlo_raw = (mm.group(2) or "").strip() or "1"
                        _rhi_raw = (mm.group(3) or "").strip() or rdim0
                        rst_raw = (mm.group(4) or "").strip() or "1"
                        rlo = _convert_expr(rlo_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        rst = _convert_expr(rst_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        idx = f"(({rlo}) + (p_fill * ({rst})))"
                        return f"{arr}[{idx} - 1]"

                    rhs_expr_raw = sec_pat.sub(_rhs_sec_repl, rhs_expr_raw)
                    # Reject unresolved whole-array operands for section assignment.
                    unresolved_whole_array = False
                    for an in sorted(rhs_tokens):
                        vv = vars_map.get(an)
                        if vv is None or (not vv.is_array):
                            continue
                        if re.search(rf"\b{re.escape(an)}\s*\(", rhs_raw, flags=re.IGNORECASE):
                            continue
                        unresolved_whole_array = True
                        break
                    if not unresolved_whole_array:
                        rhs = _convert_expr(rhs_expr_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                        out.append(" " * indent + f"if ({st} > 0) {{")
                        out.append(" " * (indent + 3) + f"for (int i_fill = {lo}, p_fill = 0; i_fill <= {hi}; i_fill += {st}, ++p_fill) {{")
                        if (lv_sec.ctype or "").lower() == "char *":
                            if lv_sec.is_allocatable or _is_assumed_shape(lv_sec.dim):
                                out.append(" " * (indent + 6) + f"assign_str_alloc(&{lhs_nm_sec}[i_fill - 1], {rhs});")
                            elif lv_sec.char_len:
                                out.append(" " * (indent + 6) + f"assign_str({lhs_nm_sec}[i_fill - 1], {_simplify_int_expr_text(lv_sec.char_len)}, {rhs});")
                            else:
                                out.append(" " * (indent + 6) + f"assign_str_alloc(&{lhs_nm_sec}[i_fill - 1], {rhs});")
                        else:
                            out.append(" " * (indent + 6) + f"{lhs_nm_sec}[i_fill - 1] = {rhs};")
                        out.append(" " * (indent + 3) + "}")
                        out.append(" " * indent + "} else {")
                        out.append(" " * (indent + 3) + f"for (int i_fill = {lo}, p_fill = 0; i_fill >= {hi}; i_fill += {st}, ++p_fill) {{")
                        if (lv_sec.ctype or "").lower() == "char *":
                            if lv_sec.is_allocatable or _is_assumed_shape(lv_sec.dim):
                                out.append(" " * (indent + 6) + f"assign_str_alloc(&{lhs_nm_sec}[i_fill - 1], {rhs});")
                            elif lv_sec.char_len:
                                out.append(" " * (indent + 6) + f"assign_str({lhs_nm_sec}[i_fill - 1], {_simplify_int_expr_text(lv_sec.char_len)}, {rhs});")
                            else:
                                out.append(" " * (indent + 6) + f"assign_str_alloc(&{lhs_nm_sec}[i_fill - 1], {rhs});")
                        else:
                            out.append(" " * (indent + 6) + f"{lhs_nm_sec}[i_fill - 1] = {rhs};")
                        out.append(" " * (indent + 3) + "}")
                        out.append(" " * indent + "}")
                        continue
            m_lhs_whole_arr = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
            if m_lhs_whole_arr:
                lhs_nm_arr = m_lhs_whole_arr.group(1).lower()
                lv_arr = vars_map.get(lhs_nm_arr)
                if lv_arr is not None and lv_arr.is_array:
                    # Whole-array assignment lowering.
                    rhs_scan = _strip_comment(rhs_raw)
                    rhs_tokens = {t.lower() for t in re.findall(r"\b[a-z_]\w*\b", rhs_scan, flags=re.IGNORECASE)}
                    rhs_array_names = [tok for tok in sorted(rhs_tokens) if tok in vars_map and vars_map[tok].is_array]
                    lhs_parts_resolved = _resolved_dim_parts(lv_arr, lhs_nm_arr, assumed_extents) if (lv_arr.is_allocatable or lv_arr.is_pointer or _is_assumed_shape(lv_arr.dim)) else _dim_parts(lv_arr.dim)
                    m_spread = re.match(r"^spread\s*\(\s*(.*)\s*\)\s*$", rhs_raw, re.IGNORECASE)
                    if m_spread:
                        sargs = [x.strip() for x in _split_args_top_level(m_spread.group(1)) if x.strip()]
                        if sargs:
                            src_nm = sargs[0].lower()
                            src_v = vars_map.get(src_nm)
                            dim_no = None
                            ncopies_txt = None
                            for extra in sargs[1:]:
                                m_dim_kw = re.match(r"(?i)^dim\s*=\s*([0-9]+)$", extra)
                                m_n_kw = re.match(r"(?i)^ncopies\s*=\s*(.+)$", extra)
                                if m_dim_kw:
                                    dim_no = int(m_dim_kw.group(1))
                                elif m_n_kw:
                                    ncopies_txt = m_n_kw.group(1).strip()
                                elif dim_no is None and re.fullmatch(r"[0-9]+", extra):
                                    dim_no = int(extra)
                                elif ncopies_txt is None:
                                    ncopies_txt = extra
                            if src_v is not None and src_v.is_array and len(_resolved_dim_parts(src_v, src_nm, assumed_extents)) == 1 and len(lhs_parts_resolved) == 2 and dim_no in {1, 2} and ncopies_txt:
                                src_len = _convert_expr(_resolved_dim_parts(src_v, src_nm, assumed_extents)[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                ncopies_c = _convert_expr(ncopies_txt, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                lhs_d1 = _convert_expr(lhs_parts_resolved[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                lhs_d2 = _convert_expr(lhs_parts_resolved[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                if lv_arr.is_allocatable:
                                    out_d1 = ncopies_c if dim_no == 1 else src_len
                                    out_d2 = src_len if dim_no == 1 else ncopies_c
                                    nfill = f"(({out_d1}) * ({out_d2}))"
                                    out.append(" " * indent + f"if ({lhs_nm_arr}) free({lhs_nm_arr});")
                                    out.append(" " * indent + f"{lhs_nm_arr} = ({lv_arr.ctype}*) malloc(sizeof({lv_arr.ctype}) * {nfill});")
                                    out.append(" " * indent + f"if (!{lhs_nm_arr} && ({nfill}) > 0) {fail_stmt}")
                                    ext_names = _alloc_extent_names(lhs_nm_arr, 2)
                                    out.append(" " * indent + f"{ext_names[0]} = {out_d1};")
                                    out.append(" " * indent + f"{ext_names[1]} = {out_d2};")
                                    lhs_d1 = out_d1
                                    lhs_d2 = out_d2
                                out.append(" " * indent + f"for (int j_fill = 0; j_fill < {lhs_d2}; ++j_fill) {{")
                                out.append(" " * (indent + 3) + f"for (int i_fill = 0; i_fill < {lhs_d1}; ++i_fill) {{")
                                if dim_no == 1:
                                    out.append(" " * (indent + 6) + f"{lhs_nm_arr}[i_fill + ({lhs_d1}) * j_fill] = {src_nm}[j_fill];")
                                else:
                                    out.append(" " * (indent + 6) + f"{lhs_nm_arr}[i_fill + ({lhs_d1}) * j_fill] = {src_nm}[i_fill];")
                                out.append(" " * (indent + 3) + "}")
                                out.append(" " * indent + "}")
                                continue
                    m_pack = re.match(r"^pack\s*\(\s*(.*)\s*\)\s*$", rhs_raw, re.IGNORECASE)
                    if m_pack and len(lhs_parts_resolved) == 1:
                        pargs = [x.strip() for x in _split_args_top_level(m_pack.group(1)) if x.strip()]
                        if len(pargs) >= 2:
                            src_raw = pargs[0]
                            mask_raw = pargs[1]
                            if not any(re.search(rf"\b{re.escape(tok)}\s*\(", src_raw, flags=re.IGNORECASE) for tok in rhs_array_names) and not any(re.search(rf"\b{re.escape(tok)}\s*\(", mask_raw, flags=re.IGNORECASE) for tok in rhs_array_names):
                                rank1_arrays = []
                                base_extent = None
                                shape_ok = True
                                for an in rhs_array_names:
                                    vv = vars_map.get(an)
                                    if vv is None or (not vv.is_array):
                                        continue
                                    dps = _resolved_dim_parts(vv, an, assumed_extents)
                                    if len(dps) != 1:
                                        shape_ok = False
                                        break
                                    rank1_arrays.append(an)
                                    cur_extent = _convert_expr(dps[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    cur_key = cur_extent.replace(" ", "").lower()
                                    if base_extent is None:
                                        base_extent = cur_extent
                                    elif base_extent.replace(" ", "").lower() != cur_key:
                                        shape_ok = False
                                        break
                                if shape_ok and base_extent is not None and rank1_arrays:
                                    src_elem = src_raw
                                    mask_elem = mask_raw
                                    for an in sorted(rank1_arrays, key=len, reverse=True):
                                        src_elem = re.sub(rf"\b{re.escape(an)}\b", f"{an}[i_fill]", src_elem, flags=re.IGNORECASE)
                                        mask_elem = re.sub(rf"\b{re.escape(an)}\b", f"{an}[i_fill]", mask_elem, flags=re.IGNORECASE)
                                    src_c = _convert_expr(src_elem, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    mask_c = _convert_expr(mask_elem, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + "int pack_n = 0;")
                                    out.append(" " * (indent + 3) + f"for (int i_fill = 0; i_fill < ({base_extent}); ++i_fill) if ({mask_c}) ++pack_n;")
                                    if lv_arr.is_allocatable:
                                        out.append(" " * (indent + 3) + f"if ({lhs_nm_arr}) free({lhs_nm_arr});")
                                        out.append(" " * (indent + 3) + f"{lhs_nm_arr} = ({lv_arr.ctype}*) malloc(sizeof({lv_arr.ctype}) * pack_n);")
                                        out.append(" " * (indent + 3) + f"if (!{lhs_nm_arr} && pack_n > 0) {fail_stmt}")
                                        for en in _alloc_extent_names(lhs_nm_arr, 1):
                                            out.append(" " * (indent + 3) + f"{en} = pack_n;")
                                    out.append(" " * (indent + 3) + "for (int i_fill = 0, j_fill = 0; i_fill < (" + base_extent + "); ++i_fill) {")
                                    out.append(" " * (indent + 6) + f"if ({mask_c}) {{")
                                    out.append(" " * (indent + 9) + f"{lhs_nm_arr}[j_fill] = {src_c};")
                                    out.append(" " * (indent + 9) + "++j_fill;")
                                    out.append(" " * (indent + 6) + "}")
                                    out.append(" " * (indent + 3) + "}")
                                    out.append(" " * indent + "}")
                                    continue
                    rhs_uses_array = len(rhs_array_names) > 0
                    if not rhs_uses_array:
                        # Scalar-to-whole-array assignment.
                        rhs = _convert_expr(
                            rhs_raw,
                            vars_map,
                            real_type,
                            byref_scalars,
                            assumed_extents,
                            proc_arg_extent_names,
                        )
                        if lv_arr.is_allocatable or lv_arr.is_pointer or _is_assumed_shape(lv_arr.dim):
                            nfill = _dim_product_from_parts(
                                _resolved_dim_parts(lv_arr, lhs_nm_arr, assumed_extents),
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                            )
                        else:
                            nfill = _dim_product_expr(
                                lv_arr.dim or "1",
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                            )
                        out.append(" " * indent + f"for (int i_fill = 0; i_fill < {nfill}; ++i_fill) {{")
                        if (lv_arr.ctype or "").lower() == "char *":
                            if lhs_nm_arr == ret_name_c:
                                out.append(" " * (indent + 3) + f"assign_str_alloc(&{lhs_nm_arr}[i_fill], {rhs});")
                            elif lv_arr.is_allocatable or lv_arr.is_pointer or _is_assumed_shape(lv_arr.dim):
                                out.append(" " * (indent + 3) + f"assign_str_alloc(&{lhs_nm_arr}[i_fill], {rhs});")
                            elif lv_arr.char_len:
                                out.append(" " * (indent + 3) + f"assign_str({lhs_nm_arr}[i_fill], {_convert_expr(lv_arr.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)}, {rhs});")
                            else:
                                out.append(" " * (indent + 3) + f"assign_str_alloc(&{lhs_nm_arr}[i_fill], {rhs});")
                        else:
                            out.append(" " * (indent + 3) + f"{lhs_nm_arr}[i_fill] = {rhs};")
                        out.append(" " * indent + "}")
                        continue
                    if len(lhs_parts_resolved) == 2:
                        rhs_sec_expr = rhs_raw
                        sec_changed = False
                        for an_sec, av_sec in sorted(vars_map.items(), key=lambda kv: len(kv[0]), reverse=True):
                            if not av_sec.is_array:
                                continue
                            dparts_sec = _resolved_dim_parts(av_sec, an_sec, assumed_extents)
                            pat_sec = re.compile(rf"\b{re.escape(an_sec)}\s*\(\s*([^()]*)\s*\)", re.IGNORECASE)

                            def _repl_rhs_rank2(mm: re.Match[str]) -> str:
                                nonlocal sec_changed
                                inner = mm.group(1)
                                idx_parts = _split_args_top_level(inner)
                                if len(dparts_sec) != 2 or len(idx_parts) != 2:
                                    return mm.group(0)
                                if (":" not in idx_parts[0]) or (":" not in idx_parts[1]):
                                    return mm.group(0)
                                d1 = _convert_expr(dparts_sec[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                d2 = _convert_expr(dparts_sec[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                sp0 = _split_colon_top_level(idx_parts[0].strip())
                                sp1 = _split_colon_top_level(idx_parts[1].strip())
                                lo0 = _convert_expr((sp0[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                lo1 = _convert_expr((sp1[0] or "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                st0 = _convert_expr((sp0[2] if len(sp0) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                st1 = _convert_expr((sp1[2] if len(sp1) == 3 else "1").strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                sec_changed = True
                                return f"{an_sec}[((({lo0}) + i1_fill * ({st0})) - 1) + ({d1}) * (((( {lo1}) + i2_fill * ({st1})) - 1))]"

                            rhs_sec_expr = pat_sec.sub(_repl_rhs_rank2, rhs_sec_expr)
                        if sec_changed:
                            rhs = _convert_expr(rhs_sec_expr, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            d1_lhs = _convert_expr(lhs_parts_resolved[0], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            d2_lhs = _convert_expr(lhs_parts_resolved[1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                            out.append(" " * indent + f"for (int i2_fill = 0; i2_fill < {d2_lhs}; ++i2_fill) {{")
                            out.append(" " * (indent + 3) + f"for (int i1_fill = 0; i1_fill < {d1_lhs}; ++i1_fill) {{")
                            out.append(" " * (indent + 6) + f"{lhs_nm_arr}[i1_fill + ({d1_lhs}) * i2_fill] = {rhs};")
                            out.append(" " * (indent + 3) + "}")
                            out.append(" " * indent + "}")
                            continue
                    # Elementwise array-expression assignment (e.g. y = 2*x, y = x + z).
                    # Conservative: skip if array operands are explicitly subscripted in RHS.
                    explicit_subscript = any(
                        re.search(rf"\b{re.escape(an)}\s*\(", rhs_raw, flags=re.IGNORECASE)
                        for an in rhs_array_names
                    )
                    rhs_ref_parts = None
                    if rhs_array_names:
                        rv0 = vars_map.get(rhs_array_names[0])
                        if rv0 is not None:
                            rhs_ref_parts = _resolved_dim_parts(rv0, rhs_array_names[0], assumed_extents)
                        if lv_arr.is_allocatable:
                            same_shape = bool(rhs_ref_parts) and all(
                                (
                                    vars_map.get(an) is not None
                                and tuple(p.replace(" ", "").lower() for p in _resolved_dim_parts(vars_map.get(an), an, assumed_extents))
                                == tuple(p.replace(" ", "").lower() for p in rhs_ref_parts)
                            )
                            for an in rhs_array_names
                        )
                        elif not lv_arr.is_pointer:
                            lhs_shape = tuple(
                                _convert_expr(p, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names).replace(" ", "").lower()
                                for p in lhs_parts_resolved
                            )
                            same_shape = all(
                                (
                                    vars_map.get(an) is not None
                                    and tuple(
                                        _convert_expr(p, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names).replace(" ", "").lower()
                                        for p in _resolved_dim_parts(vars_map.get(an), an, assumed_extents)
                                    ) == lhs_shape
                                )
                                for an in rhs_array_names
                            )
                        else:
                            lhs_shape = tuple(p.replace(" ", "").lower() for p in lhs_parts_resolved)
                            same_shape = all(
                                (
                                    vars_map.get(an) is not None
                                    and tuple(p.replace(" ", "").lower() for p in _resolved_dim_parts(vars_map.get(an), an, assumed_extents)) == lhs_shape
                                )
                                for an in rhs_array_names
                            )
                    sum_red = _extract_rank_reducing_sum(rhs_raw) if len(lhs_parts_resolved) == 1 else None
                    if sum_red is not None:
                        pre, arg_expr, red_dim, post = sum_red
                        if red_dim in {1, 2}:
                            elem_expr = _rewrite_rank2_reduction_term(
                                arg_expr,
                                red_dim,
                                "j_fill",
                                "i_fill",
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                                proc_arg_extent_names,
                            )
                            if elem_expr is not None:
                                rank2_names = [
                                    name for name, vv in vars_map.items()
                                    if vv.is_array and len(_resolved_dim_parts(vv, name, assumed_extents)) == 2
                                    and re.search(rf"\b{re.escape(name)}\b", arg_expr, re.IGNORECASE)
                                ]
                                if rank2_names:
                                    red_arr = rank2_names[0]
                                    rv_red = vars_map[red_arr]
                                    red_parts = _resolved_dim_parts(rv_red, red_arr, assumed_extents)
                                    out_len = red_parts[1] if red_dim == 1 else red_parts[0]
                                    tmp_var = "__red"
                                    vars_map_red = dict(vars_map)
                                    vars_map_red[tmp_var] = Var(rv_red.ctype or real_type)
                                    expr_red = f"{pre}{tmp_var}{post}"
                                    rhs_red = _convert_expr(
                                        expr_red,
                                        vars_map_red,
                                        real_type,
                                        byref_scalars,
                                        assumed_extents,
                                        proc_arg_extent_names,
                                    )
                                    elem_c = _convert_expr(
                                        elem_expr,
                                        vars_map,
                                        real_type,
                                        byref_scalars,
                                        assumed_extents,
                                        proc_arg_extent_names,
                                    )
                                    elem_c = _replace_pow(elem_c)
                                    if lv_arr.is_allocatable:
                                        out.append(" " * indent + f"if ({lhs_nm_arr}) free({lhs_nm_arr});")
                                        out.append(" " * indent + f"{lhs_nm_arr} = ({lv_arr.ctype}*) malloc(sizeof({lv_arr.ctype}) * ({out_len}));")
                                        out.append(" " * indent + f"if (!{lhs_nm_arr} && ({out_len}) > 0) {fail_stmt}")
                                        out.append(" " * indent + f"{_alloc_len_name(lhs_nm_arr)} = {out_len};")
                                    inner_extent = _convert_expr(red_parts[0 if red_dim == 1 else 1], vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                                    out.append(" " * indent + "{")
                                    out.append(" " * (indent + 3) + f"{rv_red.ctype} {tmp_var};")
                                    out.append(" " * (indent + 3) + f"for (int j_fill = 0; j_fill < ({out_len}); ++j_fill) {{")
                                    out.append(" " * (indent + 6) + f"{tmp_var} = 0;")
                                    out.append(" " * (indent + 6) + f"for (int i_fill = 0; i_fill < ({inner_extent}); ++i_fill) {tmp_var} += {elem_c};")
                                    out.append(" " * (indent + 6) + f"{lhs_nm_arr}[j_fill] = {rhs_red};")
                                    out.append(" " * (indent + 3) + "}")
                                    out.append(" " * indent + "}")
                                    continue
                    if (not explicit_subscript) and same_shape:
                        rhs_elem = rhs_raw
                        # Replace array variables with element access, longest first.
                        for an in sorted(rhs_array_names, key=len, reverse=True):
                            rhs_elem = re.sub(
                                rf"\b{re.escape(an)}\b",
                                f"{an}[i_fill]",
                                rhs_elem,
                                flags=re.IGNORECASE,
                            )
                        rhs = _convert_expr(
                            rhs_elem,
                            vars_map,
                            real_type,
                            byref_scalars,
                            assumed_extents,
                            proc_arg_extent_names,
                        )
                        if lv_arr.is_allocatable or lv_arr.is_pointer:
                            shp_c = [_convert_expr(p, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) for p in (rhs_ref_parts or [])]
                            nfill = _dim_product_from_parts(shp_c, vars_map, real_type, byref_scalars, assumed_extents)
                            if lv_arr.is_allocatable:
                                out.append(" " * indent + f"if ({lhs_nm_arr}) free({lhs_nm_arr});")
                                out.append(" " * indent + f"{lhs_nm_arr} = ({lv_arr.ctype}*) malloc(sizeof({lv_arr.ctype}) * ({nfill}));")
                                out.append(" " * indent + f"if (!{lhs_nm_arr} && ({nfill}) > 0) {fail_stmt}")
                            for k, en in enumerate(_alloc_extent_names(lhs_nm_arr, max(1, len(shp_c)))):
                                out.append(" " * indent + f"{en} = {shp_c[k]};")
                        else:
                            nfill = _dim_product_expr(
                                lv_arr.dim or "1",
                                vars_map,
                                real_type,
                                byref_scalars,
                                assumed_extents,
                            )
                        out.append(" " * indent + f"for (int i_fill = 0; i_fill < {nfill}; ++i_fill) {{")
                        if (lv_arr.ctype or "").lower() == "char *":
                            if lhs_nm_arr == ret_name_c:
                                out.append(" " * (indent + 3) + f"assign_str_alloc(&{lhs_nm_arr}[i_fill], {rhs});")
                            elif lv_arr.is_allocatable or lv_arr.is_pointer or _is_assumed_shape(lv_arr.dim):
                                out.append(" " * (indent + 3) + f"assign_str_alloc(&{lhs_nm_arr}[i_fill], {rhs});")
                            elif lv_arr.char_len:
                                out.append(" " * (indent + 3) + f"assign_str({lhs_nm_arr}[i_fill], {_convert_expr(lv_arr.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)}, {rhs});")
                            else:
                                out.append(" " * (indent + 3) + f"assign_str_alloc(&{lhs_nm_arr}[i_fill], {rhs});")
                        else:
                            out.append(" " * (indent + 3) + f"{lhs_nm_arr}[i_fill] = {rhs};")
                        out.append(" " * indent + "}")
                        continue
            m_lhs_name = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
            m_rhs_call = re.match(r"^([a-z_]\w*)\s*\((.*)\)\s*$", rhs_raw, re.IGNORECASE)
            if m_lhs_name and m_rhs_call:
                lhs_nm = m_lhs_name.group(1).lower()
                raw_args = _split_args_top_level(m_rhs_call.group(2).strip()) if m_rhs_call.group(2).strip() else []
                callee = _resolve_generic_proc_name(m_rhs_call.group(1), raw_args, vars_map, real_type)
                lv = vars_map.get(lhs_nm)
                if lv is not None and lv.is_array and callee in array_result_funcs:
                    raw_args = _normalize_actual_args(callee, raw_args, proc_arg_names)
                    cargs: List[str] = []
                    extent_lists = proc_arg_extent_names.get(callee, [])
                    rv = _proc_result_var(callee) or lv
                    for k, a in enumerate(raw_args):
                        exts = extent_lists[k] if k < len(extent_lists) else []
                        extent_args, carg = _expand_assumed_shape_actual_arg(
                            a,
                            exts,
                            vars_map,
                            real_type,
                            byref_scalars,
                            assumed_extents,
                            proc_arg_extent_names,
                        )
                        cargs.extend(extent_args)
                        cargs.append(carg)
                    tmp = f"__tmp_{callee}"
                    dim = _result_length_expr(callee, rv, vars_map, real_type, byref_scalars, assumed_extents) if _is_dynamic_array_result(rv) else _dim_product_expr(lv.dim or "1", vars_map, real_type, byref_scalars)
                    out.append(
                        " " * indent + f"{lv.ctype} *{tmp} = {callee}({', '.join(cargs)});"
                    )
                    if lv.is_allocatable:
                        out.append(" " * indent + f"if ({lhs_nm}) free({lhs_nm});")
                        out.append(" " * indent + f"{lhs_nm} = ({lv.ctype}*) malloc(sizeof({lv.ctype}) * ({dim}));")
                        out.append(" " * indent + f"if (!{lhs_nm} && ({dim}) > 0) {fail_stmt}")
                        lhs_exts = _alloc_extent_names(lhs_nm, max(1, len(_dim_parts(lv.dim))))
                        if _is_dynamic_array_result(rv):
                            rhs_exts = _result_extent_names(callee, max(1, len(_dim_parts(rv.dim))))
                            for en, src_en in zip(lhs_exts, rhs_exts):
                                out.append(" " * indent + f"{en} = {src_en};")
                        else:
                            for en in lhs_exts:
                                out.append(" " * indent + f"{en} = {dim};")
                    out.append(" " * indent + f"for (int i_copy = 0; i_copy < {dim}; ++i_copy) {{")
                    out.append(" " * (indent + 3) + f"{lhs_nm}[i_copy] = {tmp}[i_copy];")
                    out.append(" " * indent + "}")
                    out.append(" " * indent + f"free({tmp});")
                    continue
            m_lhs_char_elem = re.match(r"^([a-z_]\w*)\s*\(\s*([^,:()]+)\s*\)$", lhs_raw, re.IGNORECASE)
            if m_lhs_char_elem:
                lhs_nm = m_lhs_char_elem.group(1).lower()
                lv = vars_map.get(lhs_nm)
                if lv is not None and lv.is_array and (lv.ctype or "").lower() == "char *" and len(_dim_parts(lv.dim)) == 1:
                    idx = _convert_expr(m_lhs_char_elem.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    m_rhs_any_call = re.match(r"^\s*([a-z_]\w*)\s*\((.*)\)\s*$", rhs_raw, re.IGNORECASE)
                    if m_rhs_any_call and any(proc_arg_optional.get(m_rhs_any_call.group(1).lower(), [])):
                        args_rhs = _split_args_top_level(m_rhs_any_call.group(2).strip()) if m_rhs_any_call.group(2).strip() else []
                        rhs = _convert_optional_call_expr(m_rhs_any_call.group(1), args_rhs)
                    else:
                        rhs = _convert_expr(rhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    if lv.is_allocatable or _is_assumed_shape(lv.dim):
                        out.append(" " * indent + f"assign_str_alloc(&{lhs_nm}[({idx}) - 1], {rhs});")
                        continue
                    if lv.char_len:
                        out.append(" " * indent + f"assign_str({lhs_nm}[({idx}) - 1], {_convert_expr(lv.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)}, {rhs});")
                        continue
            m_lhs_char = re.match(r"^([a-z_]\w*)$", lhs_raw, re.IGNORECASE)
            if m_lhs_char:
                lhs_nm = m_lhs_char.group(1).lower()
                lv = vars_map.get(lhs_nm)
                if lv is not None and (lv.ctype or '').lower() == 'char *' and (not lv.is_array):
                    m_rhs_any_call = re.match(r"^\s*([a-z_]\w*)\s*\((.*)\)\s*$", rhs_raw, re.IGNORECASE)
                    if m_rhs_any_call and any(proc_arg_optional.get(m_rhs_any_call.group(1).lower(), [])):
                        args_rhs = _split_args_top_level(m_rhs_any_call.group(2).strip()) if m_rhs_any_call.group(2).strip() else []
                        rhs = _convert_optional_call_expr(m_rhs_any_call.group(1), args_rhs)
                    else:
                        rhs = _convert_expr(rhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    if lhs_nm == ret_name_c:
                        out.append(" " * indent + f"{lhs_nm} = {rhs};")
                    elif lv.is_allocatable or lv.is_pointer or not lv.char_len:
                        out.append(" " * indent + f"assign_str_alloc(&{lhs_nm}, {rhs});")
                    else:
                        out.append(" " * indent + f"assign_str({lhs_nm}, {_convert_expr(lv.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)}, {rhs});")
                    continue
            m_lhs_sub = re.match(r"^([a-z_]\w*)\s*\((.+):(.*)\)$", lhs_raw, re.IGNORECASE)
            if m_lhs_sub:
                lhs_nm = m_lhs_sub.group(1).lower()
                lv = vars_map.get(lhs_nm)
                if lv is not None and (lv.ctype or '').lower() == 'char *' and (not lv.is_array) and lv.char_len:
                    lo = _convert_expr(m_lhs_sub.group(2).strip(), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    hi_raw = m_lhs_sub.group(3).strip()
                    hi = _convert_expr(hi_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names) if hi_raw else _convert_expr(lv.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    m_rhs_any_call = re.match(r"^\s*([a-z_]\w*)\s*\((.*)\)\s*$", rhs_raw, re.IGNORECASE)
                    if m_rhs_any_call and any(proc_arg_optional.get(m_rhs_any_call.group(1).lower(), [])):
                        args_rhs = _split_args_top_level(m_rhs_any_call.group(2).strip()) if m_rhs_any_call.group(2).strip() else []
                        rhs = _convert_optional_call_expr(m_rhs_any_call.group(1), args_rhs)
                    else:
                        rhs = _convert_expr(rhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
                    out.append(" " * indent + f"assign_substr({lhs_nm}, {_convert_expr(lv.char_len, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)}, {lo}, {hi}, {rhs});")
                    continue
            scalar_sum = _extract_scalar_sum(rhs_raw)
            if scalar_sum is not None:
                pre, arg_expr, post = scalar_sum
                red_term = _rewrite_rank1_reduction_term(
                    arg_expr,
                    "i_fill",
                    vars_map,
                    real_type,
                    byref_scalars,
                    assumed_extents,
                    proc_arg_extent_names,
                )
                if red_term is not None:
                    elem_c, red_extent_raw, red_ctype = red_term
                    red_extent = _convert_expr(
                        red_extent_raw,
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    )
                    tmp_var = "__red"
                    vars_map_red = dict(vars_map)
                    vars_map_red[tmp_var] = Var(red_ctype)
                    expr_red = f"{pre}{tmp_var}{post}"
                    rhs_red = _convert_expr(
                        expr_red,
                        vars_map_red,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    )
                    lhs = _convert_expr(
                        lhs_raw,
                        vars_map,
                        real_type,
                        byref_scalars,
                        assumed_extents,
                        proc_arg_extent_names,
                    )
                    out.append(" " * indent + "{")
                    out.append(" " * (indent + 3) + f"{red_ctype} {tmp_var};")
                    out.append(" " * (indent + 3) + f"{tmp_var} = 0;")
                    out.append(" " * (indent + 3) + f"for (int i_fill = 0; i_fill < ({red_extent}); ++i_fill) {tmp_var} += {elem_c};")
                    out.append(" " * (indent + 3) + f"{lhs} = {rhs_red};")
                    out.append(" " * indent + "}")
                    continue
            lhs = _convert_expr(lhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            m_rhs_any_call = re.match(r"^\s*([a-z_]\w*)\s*\((.*)\)\s*$", rhs_raw, re.IGNORECASE)
            if m_rhs_any_call and any(proc_arg_optional.get(m_rhs_any_call.group(1).lower(), [])):
                args_rhs = _split_args_top_level(m_rhs_any_call.group(2).strip()) if m_rhs_any_call.group(2).strip() else []
                rhs = _convert_optional_call_expr(m_rhs_any_call.group(1), args_rhs)
            else:
                rhs = _convert_expr(rhs_raw, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
            out.append(" " * indent + f"{lhs} = {rhs};")
            continue

        out.append(" " * indent + f"/* unsupported: {code} */")

    if unit["kind"] == "function":
        for a in unit.get("args", []):
            av = vars_map.get(a.lower(), Var("int"))
            if av.is_array and (av.is_allocatable or av.is_pointer):
                for loc_en, glob_en in zip(_alloc_extent_names(a.lower(), max(1, len(_dim_parts(av.dim)))), _dummy_array_extent_names(unit_name_l, a.lower(), max(1, len(_dim_parts(av.dim))))):
                    out.append(" " * indent + f"{glob_en} = {loc_en};")
        for nm, _carg in reversed(byref_array_aliases):
            out.append(" " * indent + f"#undef {nm}")
        if ret_is_array and _is_dynamic_array_result(ret_var):
            ret_rank = max(1, len(_dim_parts(ret_var.dim)))
            for loc_en, glob_en in zip(_alloc_extent_names(ret_name_c, ret_rank), _result_extent_names(unit_name_l, ret_rank)):
                out.append(" " * indent + f"{glob_en} = {loc_en};")
        if unit.get("result"):
            out.append(" " * indent + f"return {unit['result']};")
        else:
            out.append(" " * indent + f"return {implicit_result_name};")
        out.append("}")
    elif unit["kind"] == "subroutine":
        for a in unit.get("args", []):
            av = vars_map.get(a.lower(), Var("int"))
            if av.is_array and (av.is_allocatable or av.is_pointer):
                for loc_en, glob_en in zip(_alloc_extent_names(a.lower(), max(1, len(_dim_parts(av.dim)))), _dummy_array_extent_names(unit_name_l, a.lower(), max(1, len(_dim_parts(av.dim))))):
                    out.append(" " * indent + f"{glob_en} = {loc_en};")
        for nm, _carg in reversed(byref_array_aliases):
            out.append(" " * indent + f"#undef {nm}")
        out.append("}")
    else:
        for nm, v in vars_map.items():
            if v.is_array and (v.is_allocatable or (unit["kind"] == "program" and _main_fixed_array_uses_heap(v))):
                if (v.ctype or "").lower() == "char *" and v.is_allocatable:
                    out.append(" " * indent + f"free_str_array({nm}, {_alloc_len_name(nm)});")
                else:
                    out.append(" " * indent + f"free({nm});")
        has_terminal_return = False
        for j in range(len(out) - 1, -1, -1):
            s = out[j].strip()
            if not s or s.startswith("/*"):
                continue
            has_terminal_return = s.startswith("return ")
            break
        if not has_terminal_return:
            out.append(" " * indent + "return 0;")
        out.append("}")
    out = _rewrite_zero_based_loop_style(out)
    out = _use_block_scoped_loop_indices(out)
    out = _inline_simple_int_aliases(out)
    out = _prefer_simple_n_extent_name(out, assumed_extents)
    out = _fold_zero_init_to_decl(out, real_type)
    out = _coalesce_adjacent_c_declarations(out)
    out = _compound_assign_style(out)
    if one_line:
        out = _collapse_one_line_blocks(out)
    out.append("")
    return out



def _extract_module_parameter_maps(
    text: str, real_type: str, kind_ctype_map: Dict[str, str]
) -> tuple[Dict[str, Dict[str, Var]], Dict[str, str]]:
    """Collect module-scope PARAMETER declarations and contained-procedure parents."""
    lines = text.splitlines()
    module_decl_lines: Dict[str, List[str]] = {}
    proc_parent_module: Dict[str, str] = {}
    current_module: Optional[str] = None
    before_contains = False
    for raw in lines:
        code = _strip_comment(raw).strip()
        if not code:
            continue
        m_mod = re.match(r"^module\s+([a-z_]\w*)\b", code, re.IGNORECASE)
        if m_mod and not re.match(r"^module\s+procedure\b", code, re.IGNORECASE):
            current_module = m_mod.group(1).lower()
            before_contains = True
            module_decl_lines.setdefault(current_module, [])
            continue
        if current_module is None:
            continue
        if re.match(r"^end\s+module\b", code, re.IGNORECASE):
            current_module = None
            before_contains = False
            continue
        if re.match(r"^contains\b", code, re.IGNORECASE):
            before_contains = False
            continue
        if before_contains:
            module_decl_lines[current_module].append(code)
            continue
        m_proc = re.match(
            r"^(?:[a-z_][\w()=,\s]*\s+)?(?:recursive\s+|pure\s+|elemental\s+)*"
            r"(function|subroutine)\s+([a-z_]\w*)\b",
            code,
            re.IGNORECASE,
        )
        if m_proc:
            proc_parent_module[m_proc.group(2).lower()] = current_module
    module_param_maps: Dict[str, Dict[str, Var]] = {}
    for mod_name, decl_lines in module_decl_lines.items():
        pseudo = {"body_lines": decl_lines, "body_line_nos": [], "source_lines": []}
        parsed = _parse_decls(pseudo, real_type, kind_ctype_map)
        module_param_maps[mod_name] = {nm: v for nm, v in parsed.items() if v.is_param}
    return module_param_maps, proc_parent_module


def _imported_module_parameters_for_unit(
    unit: Dict[str, object],
    module_param_maps: Dict[str, Dict[str, Var]],
    proc_parent_module: Dict[str, str],
) -> Dict[str, Var]:
    """Return module PARAMETERs visible in a unit via containment or USE."""
    imported: Dict[str, Var] = {}
    unit_name = str(unit.get("name", "")).lower()
    parent_mod = proc_parent_module.get(unit_name)
    if parent_mod and parent_mod in module_param_maps:
        imported.update(dict(module_param_maps[parent_mod]))
    for raw in unit.get("body_lines", []):
        code = _strip_comment(str(raw)).strip()
        m_use = re.match(r"^use\s+([a-z_]\w*)\b(?:\s*,\s*only\s*:\s*(.*))?$", code, re.IGNORECASE)
        if not m_use:
            continue
        mod_name = m_use.group(1).lower()
        params = module_param_maps.get(mod_name)
        if not params:
            continue
        only_list = (m_use.group(2) or "").strip()
        if not only_list:
            imported.update(dict(params))
            continue
        for item in _split_args_top_level(only_list):
            it = item.strip()
            if not it:
                continue
            m_rename = re.match(r"^([a-z_]\w*)\s*=>\s*([a-z_]\w*)$", it, re.IGNORECASE)
            if m_rename:
                local_name = m_rename.group(1).lower()
                use_name = m_rename.group(2).lower()
                if use_name in params:
                    imported[local_name] = params[use_name]
                continue
            nm = it.lower()
            if nm in params:
                imported[nm] = params[nm]
    return imported

def transpile_fortran_to_c(
    text: str, *, one_line: bool = False, validate: bool = True, annotate: bool = False
) -> str:
    text, rewrite_line_map = _rewrite_simple_forall(text)
    text, rewrite_line_map_2 = _rewrite_inline_if_write(text)
    rewrite_line_map = _compose_line_maps(rewrite_line_map, rewrite_line_map_2)
    if validate:
        basic_errors = fscan.validate_fortran_basic_statements(text)
        if basic_errors:
            basic_errors = _remap_rewritten_line_numbers(basic_errors, rewrite_line_map)
            msg = "\n".join(basic_errors[:20])
            if len(basic_errors) > 20:
                msg += f"\n... and {len(basic_errors)-20} more"
            raise ValueError(msg)

    real_type = _fortran_to_c_real_type(text)
    kind_ctype_map = _extract_kind_alias_c_types(text)
    units = fscan.split_fortran_units_simple(text)
    _defined_modules, _used_modules, generic_interfaces = fscan.parse_modules_and_generics(text.splitlines())
    known_proc_names = {str(u.get("name", "")).lower() for u in units}
    known_proc_names.update(generic_interfaces.keys())
    if validate:
        errors = fscan.find_implicit_none_undeclared_identifiers(
            text, known_procedure_names=known_proc_names
        )
        if errors:
            errors = _remap_rewritten_line_numbers(errors, rewrite_line_map)
            msg = "\n".join(errors[:20])
            if len(errors) > 20:
                msg += f"\n... and {len(errors)-20} more"
            raise ValueError(f"Implicit-none validation failed:\n{msg}")

    out: List[str] = [
        "#include <stdio.h>",
        "#include <stdlib.h>",
        "#include <math.h>",
        "#include <complex.h>",
        "#include <float.h>",
        "#include <limits.h>",
        "#include <string.h>",
        "",
    ]
    decl_maps: List[Dict[str, Var]] = [_parse_decls(u, real_type, kind_ctype_map) for u in units]
    module_param_maps, proc_parent_module = _extract_module_parameter_maps(text, real_type, kind_ctype_map)
    for u, vmap in zip(units, decl_maps):
        imported_params = _imported_module_parameters_for_unit(u, module_param_maps, proc_parent_module)
        for nm, vv in imported_params.items():
            if nm not in vmap:
                vmap[nm] = vv
    # Infer simple dummy-argument traits from usage:
    # - mutated scalar dummy -> inout
    # - scalar dummy used as callee (f(...)) -> external procedure argument
    for u, vmap in zip(units, decl_maps):
        if u.get("kind") not in {"function", "subroutine"}:
            continue
        args_l = [str(a).lower() for a in u.get("args", [])]
        body = [str(s) for s in u.get("body_lines", [])]
        for a in args_l:
            vv = vmap.get(a)
            if vv is None:
                continue
            if vv.intent is None:
                asn_pat = re.compile(rf"^\s*{re.escape(a)}(?:\s*\([^)]*\))?\s*=", re.IGNORECASE)
                mut_pat = re.compile(rf"^\s*{re.escape(a)}\s*[\+\-\*/]=", re.IGNORECASE)
                for s in body:
                    code = _strip_comment(s).strip()
                    if asn_pat.match(code) or mut_pat.match(code):
                        vv.intent = "inout"
                        break
            if (not vv.is_array) and (not vv.is_external):
                callee_pat = re.compile(rf"\b{re.escape(a)}\s*\(", re.IGNORECASE)
                for s in body:
                    code = _strip_comment(s).strip()
                    if not callee_pat.search(code):
                        continue
                    # Skip plain assignment to a(...)=... indexing forms.
                    if re.match(rf"^\s*{re.escape(a)}\s*\(", code, re.IGNORECASE) and "=" in code:
                        continue
                    if (vv.ctype or "").lower() == "char *" and (not vv.is_array):
                        continue
                    vv.is_external = True
                    break
    known_proc_names = {str(u.get("name", "")).lower() for u in units if u.get("kind") in {"function", "subroutine"}}
    # Declarations like `real :: f` can denote external function type.
    # If such a name is used as `f(...)`, do not emit it as a local variable.
    for u, vmap in zip(units, decl_maps):
        called_names: set[str] = set()
        for stmt in u.get("body_lines", []):
            code = _strip_comment(str(stmt)).strip()
            for m in re.finditer(r"\b([a-z_]\w*)\s*\(", code, flags=re.IGNORECASE):
                called_names.add(m.group(1).lower())
        arg_names = {str(a).lower() for a in u.get("args", [])}
        unit_name = str(u.get("name", "")).lower()
        for nm in list(vmap.keys()):
            vv = vmap.get(nm)
            if vv is None:
                continue
            if nm in arg_names:
                continue
            # Preserve function result naming patterns in function units.
            if u.get("kind") == "function" and (nm == unit_name or nm == str(u.get("result", "")).lower()):
                continue
            if nm in known_proc_names and nm in called_names and (not vv.is_array) and (not vv.is_param):
                del vmap[nm]
    proc_arg_modes: Dict[str, List[str]] = {}
    proc_arg_optional: Dict[str, List[bool]] = {}
    proc_arg_ctypes: Dict[str, List[str]] = {}
    proc_arg_is_array: Dict[str, List[bool]] = {}
    proc_arg_array_byref: Dict[str, List[bool]] = {}
    proc_arg_assumed_ranks: Dict[str, List[int]] = {}
    proc_arg_extent_names: Dict[str, List[List[str]]] = {}
    proc_arg_names: Dict[str, List[str]] = {}
    array_result_funcs: set[str] = set()
    proc_results: Dict[str, Var] = {}
    global_derived_types: Dict[str, List[tuple[str, str]]] = _parse_local_derived_types(
        {"body_lines": text.splitlines()},
        real_type,
        kind_ctype_map,
    )
    for u, vmap in zip(units, decl_maps):
        if u.get("kind") not in {"function", "subroutine"}:
            continue
        modes: List[str] = []
        optionals: List[bool] = []
        ctypes: List[str] = []
        is_arrays: List[bool] = []
        array_byref: List[bool] = []
        assumed_ranks: List[int] = []
        extent_names_per_arg: List[List[str]] = []
        arg_names_lower = [str(a).lower() for a in u.get("args", [])]
        assumed_rank1_count = 0
        for a in arg_names_lower:
            av0 = vmap.get(a, Var("int"))
            if (
                av0.is_array
                and _is_assumed_shape(av0.dim)
                and (not av0.is_allocatable)
                and (not av0.is_pointer)
                and max(1, len(_dim_parts(av0.dim))) == 1
            ):
                assumed_rank1_count += 1
        for a in u.get("args", []):
            av = vmap.get(str(a).lower(), Var("int"))
            optionals.append(bool(av.optional))
            ctypes.append(av.ctype)
            is_arrays.append(bool(av.is_array))
            array_byref.append(bool(av.is_array and (av.is_allocatable or av.is_pointer)))
            if av.is_array:
                modes.append("ptr")
                if _is_assumed_shape(av.dim) and (not av.is_allocatable) and (not av.is_pointer):
                    rank = max(1, len(_dim_parts(av.dim)))
                    assumed_ranks.append(rank)
                    use_simple_n = (
                        rank == 1
                        and assumed_rank1_count == 1
                        and "n" not in arg_names_lower
                        and "n" not in vmap
                    )
                    extent_names_per_arg.append(
                        _extent_param_names(str(a).lower(), rank, use_simple_n=use_simple_n)
                    )
                else:
                    assumed_ranks.append(0)
                    extent_names_per_arg.append([])
            elif av.is_external:
                modes.append("value")
                assumed_ranks.append(0)
                extent_names_per_arg.append([])
            elif av.intent == "in":
                modes.append("ptr" if av.optional else "value")
                assumed_ranks.append(0)
                extent_names_per_arg.append([])
            elif av.intent in {"out", "inout"}:
                modes.append("ptr")
                assumed_ranks.append(0)
                extent_names_per_arg.append([])
            else:
                modes.append("ptr" if av.optional else "value")
                assumed_ranks.append(0)
                extent_names_per_arg.append([])
        proc_arg_modes[str(u.get("name", "")).lower()] = modes
        proc_arg_optional[str(u.get("name", "")).lower()] = optionals
        proc_arg_ctypes[str(u.get("name", "")).lower()] = ctypes
        proc_arg_is_array[str(u.get("name", "")).lower()] = is_arrays
        proc_arg_array_byref[str(u.get("name", "")).lower()] = array_byref
        proc_arg_assumed_ranks[str(u.get("name", "")).lower()] = assumed_ranks
        proc_arg_extent_names[str(u.get("name", "")).lower()] = extent_names_per_arg
        proc_arg_names[str(u.get("name", "")).lower()] = [str(a).lower() for a in u.get("args", [])]
        if u.get("kind") == "function":
            ret_name = str(u.get("result") or "").lower()
            ret_lookup = ret_name if ret_name else str(u.get("name", "")).lower()
            rv = _fallback_function_result_var(u, real_type, kind_ctype_map)
            if rv is None:
                rv = vmap.get(ret_lookup)
            if rv is not None:
                proc_results[str(u.get("name", "")).lower()] = rv
            if rv is not None and rv.is_array:
                array_result_funcs.add(str(u.get("name", "")).lower())

    type_bound_bindings = _extract_type_bound_bindings(text)

    global _ACTIVE_DERIVED_TYPES, _ACTIVE_PROC_RESULTS, _ACTIVE_GENERIC_BINDINGS, _ACTIVE_OPERATOR_BINDINGS, _ACTIVE_TYPE_BOUND_BINDINGS, _ACTIVE_PROC_ARG_CTYPES, _ACTIVE_PROC_ARG_IS_ARRAY, _ACTIVE_PROC_ARG_ASSUMED_RANKS, _ACTIVE_PROC_IS_ELEMENTAL
    _ACTIVE_DERIVED_TYPES = dict(global_derived_types)
    _ACTIVE_PROC_RESULTS = dict(proc_results)
    _ACTIVE_GENERIC_BINDINGS = {k.lower(): [x.lower() for x in v] for k, v in generic_interfaces.items()}
    _ACTIVE_OPERATOR_BINDINGS = {
        k[len("operator("):-1].strip().lower(): [x.lower() for x in v]
        for k, v in generic_interfaces.items()
        if k.lower().startswith("operator(") and k.endswith(")")
    }
    _ACTIVE_TYPE_BOUND_BINDINGS = {
        dt.lower(): {name.lower(): proc.lower() for name, proc in methods.items()}
        for dt, methods in type_bound_bindings.items()
    }
    _ACTIVE_PROC_ARG_CTYPES = {k.lower(): list(v) for k, v in proc_arg_ctypes.items()}
    _ACTIVE_PROC_ARG_IS_ARRAY = {k.lower(): list(v) for k, v in proc_arg_is_array.items()}
    _ACTIVE_PROC_ARG_ASSUMED_RANKS = {k.lower(): list(v) for k, v in proc_arg_assumed_ranks.items()}
    _ACTIVE_PROC_IS_ELEMENTAL = {
        str(u.get("name", "")).lower(): _unit_is_elemental(u)
        for u in units
        if u.get("kind") in {"function", "subroutine"}
    }

    result_extent_declared = False
    for fn_name, rv in proc_results.items():
        if not _is_dynamic_array_result(rv):
            continue
        for en in _result_extent_names(fn_name, max(1, len(_dim_parts(rv.dim)))):
            out.append(f"static int {en} = 0;")
        result_extent_declared = True
    dummy_array_extent_declared = False
    for u, vmap in zip(units, decl_maps):
        if u.get("kind") not in {"function", "subroutine"}:
            continue
        proc_name = str(u.get("name", "")).lower()
        for a in u.get("args", []):
            av = vmap.get(str(a).lower(), Var("int"))
            if av.is_array and (av.is_allocatable or av.is_pointer):
                for en in _dummy_array_extent_names(proc_name, str(a), max(1, len(_dim_parts(av.dim)))):
                    out.append(f"static int {en} = 0;")
                dummy_array_extent_declared = True
    if result_extent_declared or dummy_array_extent_declared:
        out.append("")

    if global_derived_types:
        emit_local_derived_type_typedefs(out, 0, global_derived_types)
        out.append("")

    # Emit forward declarations so calls compile even when definitions appear later.
    for u, vmap in zip(units, decl_maps):
        if u.get("kind") == "function":
            ret_name = (u.get("result") or "").lower()
            ret_lookup = ret_name if ret_name else str(u.get("name", "")).lower()
            ret_var = _fallback_function_result_var(u, real_type, kind_ctype_map) or vmap.get(ret_lookup) or Var(real_type)
            args: List[str] = []
            proc_name = str(u.get("name", "")).lower()
            extent_lists = proc_arg_extent_names.get(proc_name, [])
            flat_exts = [e for lst in extent_lists for e in lst]
            proto_simple_n = (len(flat_exts) == 1 and flat_exts[0] != "n")
            for idx, a in enumerate(u.get("args", [])):
                av = vmap.get(str(a).lower(), Var("int"))
                exts = extent_lists[idx] if idx < len(extent_lists) else []
                if exts:
                    use_exts = (["n"] if (proto_simple_n and len(exts) == 1) else exts)
                    args.extend([f"const int {nm}" for nm in use_exts])
                args.append(_emit_decl(_arg_c_name(str(a), av), av, vmap, real_type, False, as_arg=True))
            cmt = _as_c_inline_comment(_first_unit_doc_comment(u))
            ret_decl = f"{ret_var.ctype} *" if ret_var.is_array else f"{ret_var.ctype} "
            out.append(f"{ret_decl}{u['name']}({', '.join(args)});{cmt}")
        elif u.get("kind") == "subroutine":
            args = []
            proc_name = str(u.get("name", "")).lower()
            extent_lists = proc_arg_extent_names.get(proc_name, [])
            flat_exts = [e for lst in extent_lists for e in lst]
            proto_simple_n = (len(flat_exts) == 1 and flat_exts[0] != "n")
            for idx, a in enumerate(u.get("args", [])):
                av = vmap.get(str(a).lower(), Var("int"))
                exts = extent_lists[idx] if idx < len(extent_lists) else []
                if exts:
                    use_exts = (["n"] if (proto_simple_n and len(exts) == 1) else exts)
                    args.extend([f"const int {nm}" for nm in use_exts])
                args.append(_emit_decl(_arg_c_name(str(a), av), av, vmap, real_type, False, as_arg=True))
            cmt = _as_c_inline_comment(_first_unit_doc_comment(u))
            out.append(f"void {u['name']}({', '.join(args)});{cmt}")
    if any(u.get("kind") in {"function", "subroutine"} for u in units):
        out.append("")

    for u, vmap in zip(units, decl_maps):
        out.extend(
            _transpile_unit(
                u,
            real_type,
            kind_ctype_map,
            proc_arg_modes,
            proc_arg_optional,
            proc_arg_ctypes,
            proc_arg_is_array,
            proc_arg_array_byref,
            proc_arg_assumed_ranks,
            proc_arg_extent_names,
            proc_arg_names,
            array_result_funcs,
            vmap,
            one_line=one_line,
            annotate=annotate,
            )
        )
    out = _inject_runtime_helpers(out)
    if not units:
        out.extend(["int main(void) {", "   return 0;", "}"])
    return "\n".join(out).rstrip() + "\n"



__all__ = ["Var", "transpile_fortran_to_c"]
