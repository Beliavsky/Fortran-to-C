#!/usr/bin/env python3
"""xf2c_textutil.py: shared text and parsing utilities for xf2c."""

from __future__ import annotations

import re
from typing import Dict, List, Optional

import fortran_scan as fscan

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

def _replace_pow(expr: str) -> str:
    # Conservative repeated replacement for simple operands.
    var = r"[a-z_]\w*(?:\[[^\[\]]+\])*"
    num = r"[0-9]+(?:\.[0-9]*)?(?:[eEdD][+\-]?[0-9]+)?"
    par = r"\([^()]+\)"
    pat = re.compile(
        rf"({var}|{par}|{num})\s*\*\*\s*({var}|{par}|{num})",
        re.IGNORECASE,
    )
    prev = None
    out = expr
    while out != prev:
        prev = out
        out = pat.sub(r"pow(\1, \2)", out)
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

def _split_concat_top_level(text: str) -> List[str]:
    out: List[str] = []
    cur: List[str] = []
    depth = 0
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
            elif ch == "/" and i + 1 < len(text) and text[i + 1] == "/" and depth == 0:
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
