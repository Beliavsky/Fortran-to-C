#!/usr/bin/env python3
"""xf2c_io.py: formatted I/O helpers for xf2c."""

from __future__ import annotations

import re
from typing import Dict, List

from xf2c_textutil import _split_args_top_level


def _is_fortran_string_literal(text: str) -> bool:
    t = text.strip()
    return len(t) >= 2 and ((t[0] == "'" and t[-1] == "'") or (t[0] == '"' and t[-1] == '"'))


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
        return "%s"
    if desc == 'l':
        return "%d"
    return "%g" if (ctype or '').lower() != 'int' else "%d"


def _emit_formatted_1d_array_output(
    out: List[str],
    indent: int,
    arr_name: str,
    arr_var,
    fmt_text: str,
    vars_map,
    real_type: str,
    byref_scalars,
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    import xf2c_core as core

    toks = _parse_basic_format_tokens(fmt_text)
    if not toks:
        return False
    if not any(tok.get('kind') == 'data' for tok in toks):
        return False
    if arr_var.is_allocatable:
        npr = core._dim_product_from_parts(
            core._resolved_dim_parts(arr_var, arr_name, assumed_extents),
            vars_map,
            real_type,
            byref_scalars,
            assumed_extents,
        )
    else:
        npr = core._dim_product_expr(arr_var.dim or '1', vars_map, real_type, byref_scalars, assumed_extents)
    ctype = (arr_var.ctype or real_type).lower()
    out.append(' ' * indent + '{')
    out.append(' ' * (indent + 3) + 'int __idx_fmt = 0;')
    out.append(' ' * (indent + 3) + f'while (__idx_fmt < {npr}) {{')
    for tok in toks:
        kind = tok.get('kind')
        if kind == 'space':
            nsp = int(tok.get('count', 1))
            lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
            out.append(' ' * (indent + 6) + f'printf("%s", "{lit}");')
        elif kind == 'literal':
            lit = str(tok.get('text', '')).replace('\\', '\\\\').replace('"', '\\"')
            out.append(' ' * (indent + 6) + f'printf("%s", "{lit}");')
        elif kind == 'data':
            pf = _printf_fmt_for_basic_format_token(tok, ctype).replace('\\', '\\\\').replace('"', '\\"')
            out.append(' ' * (indent + 6) + f'if (__idx_fmt < {npr}) printf("{pf}", {arr_name}[__idx_fmt++]);')
    out.append(' ' * (indent + 6) + 'printf("\\n");')
    out.append(' ' * (indent + 3) + '}')
    out.append(' ' * indent + '}')
    return True


def _format_item_ctype(expr: str, vars_map, real_type: str) -> str:
    import xf2c_core as core

    s = expr.strip()
    if _is_fortran_string_literal(s):
        return 'string'
    if re.fullmatch(r'[+\-]?\d+', s):
        return 'int'
    if re.fullmatch(r"[+\-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eEdD][+\-]?\d+)?(?:_[a-z_]\w*)?", s):
        return real_type.lower()
    m_comp = re.match(r'^([a-z_]\w*)(?:\s*%\s*([a-z_]\w*))+$', s, re.IGNORECASE)
    if m_comp:
        base = m_comp.group(1).lower()
        vv = vars_map.get(base)
        if vv is not None:
            ctype = (vv.ctype or real_type).lower()
            parts = [p.lower() for p in re.findall(r'%\s*([a-z_]\w*)', s, flags=re.IGNORECASE)]
            for part in parts:
                fields = core._ACTIVE_DERIVED_TYPES.get(ctype)
                if not fields:
                    break
                hit = None
                for fname, fctype in fields:
                    if fname == part:
                        hit = fctype.lower()
                        break
                if hit is None:
                    break
                ctype = hit
            return ctype
    m = re.match(r'^([a-z_]\w*)$', s, re.IGNORECASE)
    if m:
        vv = vars_map.get(m.group(1).lower())
        if vv is not None:
            return (vv.ctype or real_type).lower() if not getattr(vv, 'is_char', False) else 'string'
    return real_type.lower()


def _emit_basic_formatted_items_output(
    out: List[str],
    indent: int,
    fmt_text: str,
    items: List[str],
    vars_map,
    real_type: str,
    byref_scalars,
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    import xf2c_core as core

    toks = _parse_basic_format_tokens(fmt_text)
    if not toks:
        return False
    vals: List[tuple[str, str]] = []
    if len(items) == 1:
        m_arr = re.match(r'^([a-z_]\w*)$', items[0], re.IGNORECASE)
        if m_arr:
            an = m_arr.group(1).lower()
            av = vars_map.get(an)
            if av is not None and av.is_array and len(core._resolved_dim_parts(av, an, assumed_extents)) == 1:
                return _emit_formatted_1d_array_output(out, indent, an, av, fmt_text, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        m_ctor = re.match(r'^\[\s*(.*)\s*\]$', items[0])
        if m_ctor:
            items = [x.strip() for x in _split_args_top_level(m_ctor.group(1)) if x.strip()]
    for it in items:
        vals.append((core._convert_expr(it, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names), _format_item_ctype(it, vars_map, real_type)))
    if not vals and not any(tok.get('kind') in {'space', 'literal'} for tok in toks):
        return False
    repeat_group = None
    fixed_toks = []
    for tok in toks:
        if tok.get('kind') == 'repeat_group' and repeat_group is None:
            repeat_group = list(tok.get('tokens') or [])
        else:
            fixed_toks.append(tok)

    def emit_tok(tok, val_expr=None, val_ctype=None):
        kind = tok.get('kind')
        if kind == 'space':
            nsp = int(tok.get('count', 1))
            lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
            out.append(' ' * indent + f'printf("%s", "{lit}");')
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
    vars_map,
    real_type: str,
    byref_scalars,
    assumed_extents: Dict[str, List[str]],
    proc_arg_extent_names: Dict[str, List[List[str]]],
) -> bool:
    import xf2c_core as core

    node = _parse_implied_do_item(item_text)
    group = _extract_scalar_repeat_group_tokens(fmt_text)
    if node is None or group is None:
        return False

    def emit_scalar(expr: str, ind: int) -> None:
        cexpr = core._convert_expr(expr, vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        ctype = _format_item_ctype(expr, vars_map, real_type)
        for tok in group:
            kind = tok.get('kind')
            if kind == 'space':
                nsp = int(tok.get('count', 1))
                lit = (' ' * nsp).replace('\\', '\\\\').replace('"', '\\"')
                out.append(' ' * ind + f'printf("%s", "{lit}");')
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
        clo = core._convert_expr(str(n['lo']), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        chi = core._convert_expr(str(n['hi']), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
        step = n.get('step')
        if step is None:
            out.append(' ' * ind + f'for ({var} = {clo}; {var} <= {chi}; ++{var}) {{')
            inner_ind = ind + 3
            for child in n['body']:
                emit_node(child, inner_ind)
            out.append(' ' * ind + '}')
        else:
            cstep = core._convert_expr(str(step), vars_map, real_type, byref_scalars, assumed_extents, proc_arg_extent_names)
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
