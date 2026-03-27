#!/usr/bin/env python3
"""Conservative post-processing rewrites for generated C code."""

from __future__ import annotations

import argparse
import ast
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional


@dataclass(frozen=True)
class Expr:
    kind: str
    value: object = None
    left: Optional["Expr"] = None
    right: Optional["Expr"] = None
    operand: Optional["Expr"] = None
    base: Optional["Expr"] = None
    index: Optional["Expr"] = None
    func: Optional["Expr"] = None
    args: tuple["Expr", ...] = ()
    attr: Optional[str] = None


HELPER_BASE_NAMES = {
    "__first": ("first", True),
    "__first_pr": ("first_pr", True),
    "__sum": ("sum", False),
    "__prod": ("prod", False),
    "__buf": ("buf", False),
    "__idx_fmt": ("idx_fmt", True),
    "__iv": ("iv", True),
    "__lin": ("lin", True),
    "__elem": ("elem", False),
    "__n_tmp": ("n_tmp", True),
    "__rhs_tmp": ("rhs_tmp", False),
}

_PROTECTED_ATOMIC_PAREN_NAMES = {
    "char",
    "short",
    "int",
    "long",
    "signed",
    "unsigned",
    "float",
    "double",
    "size_t",
    "ptrdiff_t",
    "const",
    "volatile",
    "restrict",
    "void",
    "bool",
}


def _split_cpp_comment(line: str) -> tuple[str, str]:
    in_single = False
    in_double = False
    esc = False
    i = 0
    while i < len(line) - 1:
        ch = line[i]
        if esc:
            esc = False
            i += 1
            continue
        if ch == "\\" and (in_single or in_double):
            esc = True
            i += 1
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            i += 1
            continue
        if not in_single and not in_double and line[i : i + 2] == "//":
            return line[:i], line[i:]
        i += 1
    return line, ""


def _helper_base_name(name: str) -> tuple[str, bool]:
    if name in HELPER_BASE_NAMES:
        return HELPER_BASE_NAMES[name]
    if name.startswith("__n_"):
        return name[2:], True
    if name.startswith("__step_"):
        return "step_" + name[len("__step_") :], True
    if name.startswith("__tmp_"):
        return "tmp_" + name[len("__tmp_") :], False
    if name.startswith("__ctor_"):
        return "ctor_" + name[len("__ctor_") :], False
    if name.startswith("__pad_"):
        return "pad_" + name[len("__pad_") :], False
    m = re.fullmatch(r"__i([0-9]+)", name)
    if m:
        return f"i{m.group(1)}", True
    if name.startswith("__"):
        return name[2:], False
    return name, False


def _collect_identifiers(code: str) -> list[str]:
    out: list[str] = []
    in_single = False
    in_double = False
    esc = False
    i = 0
    while i < len(code):
        ch = code[i]
        if esc:
            esc = False
            i += 1
            continue
        if ch == "\\" and (in_single or in_double):
            esc = True
            i += 1
            continue
        if ch == "'" and not in_double:
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
        if ch.isalpha() or ch == "_":
            j = i + 1
            while j < len(code) and (code[j].isalnum() or code[j] == "_"):
                j += 1
            out.append(code[i:j])
            i = j
            continue
        i += 1
    return out


def _helper_rename_map(text: str) -> dict[str, str]:
    identifiers = _collect_identifiers(text)
    helpers = sorted({name for name in identifiers if name.startswith("__")})
    used = {name for name in identifiers if name not in helpers}
    assigned: dict[str, str] = {}
    for helper in helpers:
        base, is_int = _helper_base_name(helper)
        candidate = base
        if candidate in used or candidate in assigned.values():
            prefix = "i" if is_int else "x"
            candidate = f"{prefix}{base}"
        idx = 2
        while candidate in used or candidate in assigned.values():
            candidate = f"{base}_{idx}" if not is_int else f"i{base}_{idx}"
            idx += 1
        assigned[helper] = candidate
        used.add(candidate)
    return assigned


def _rewrite_atomic_scalar_parens(code: str) -> str:
    out: list[str] = []
    i = 0
    in_single = False
    in_double = False
    esc = False
    while i < len(code):
        ch = code[i]
        if esc:
            out.append(ch)
            esc = False
            i += 1
            continue
        if ch == "\\" and (in_single or in_double):
            out.append(ch)
            esc = True
            i += 1
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
            out.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            i += 1
            continue
        if in_single or in_double or ch != "(":
            out.append(ch)
            i += 1
            continue

        end = _find_matching_paren(code, i)
        if end is None:
            out.append(ch)
            i += 1
            continue

        inner = code[i + 1 : end].strip()
        if not re.fullmatch(r"[A-Za-z_]\w*|[+\-]?\d+", inner) or inner in _PROTECTED_ATOMIC_PAREN_NAMES:
            out.append(ch)
            i += 1
            continue

        prev_idx = i - 1
        while prev_idx >= 0 and code[prev_idx].isspace():
            prev_idx -= 1
        prev_ch = code[prev_idx] if prev_idx >= 0 else ""
        next_idx = end + 1
        while next_idx < len(code) and code[next_idx].isspace():
            next_idx += 1
        next_ch = code[next_idx] if next_idx < len(code) else ""

        if prev_ch and (prev_ch.isalnum() or prev_ch in "_]"):
            out.append(ch)
            i += 1
            continue
        if next_ch and (next_ch.isalnum() or next_ch in "_["):
            out.append(ch)
            i += 1
            continue
        if prev_ch not in "=,+-*/%!?<>:&|([{};)":
            out.append(ch)
            i += 1
            continue
        if next_ch and next_ch not in "=,+-*/%!?<>:&|)]};":
            out.append(ch)
            i += 1
            continue

        out.append(inner)
        i = end + 1
    return "".join(out)


def _rewrite_helper_names(code: str, rename_map: dict[str, str]) -> str:
    out: list[str] = []
    in_single = False
    in_double = False
    esc = False
    i = 0
    while i < len(code):
        ch = code[i]
        if esc:
            out.append(ch)
            esc = False
            i += 1
            continue
        if ch == "\\" and (in_single or in_double):
            out.append(ch)
            esc = True
            i += 1
            continue
        if ch == "'" and not in_double:
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
            while j < len(code) and (code[j].isalnum() or code[j] == "_"):
                j += 1
            name = code[i:j]
            out.append(rename_map.get(name, name))
            i = j
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _brace_delta(line: str) -> int:
    code, _comment = _split_cpp_comment(line)
    depth = 0
    in_single = False
    in_double = False
    esc = False
    for ch in code:
        if esc:
            esc = False
            continue
        if ch == "\\" and (in_single or in_double):
            esc = True
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            continue
        if in_single or in_double:
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
    return depth


def _rewrite_zero_based_loop_lines(lines: list[str]) -> list[str]:
    out: list[str] = []
    i = 0
    header_re = re.compile(
        r"^(?P<indent>\s*)for\s*\(\s*int\s+(?P<var>[A-Za-z_]\w*)\s*=\s*1\s*;\s*(?P=var)\s*<=\s*(?P<hi>[^;]+?)\s*;\s*\+\+(?P=var)\s*\)\s*\{\s*$"
    )
    single_re = re.compile(
        r"^(?P<indent>\s*)for\s*\(\s*int\s+(?P<var>[A-Za-z_]\w*)\s*=\s*1\s*;\s*(?P=var)\s*<=\s*(?P<hi>[^;]+?)\s*;\s*\+\+(?P=var)\s*\)\s*(?P<body>.+?)\s*$"
    )
    while i < len(lines):
        line = lines[i]
        code, comment = _split_cpp_comment(line.rstrip("\r\n"))
        eol = "\n" if line.endswith("\n") else ""
        m_single = single_re.match(code)
        if m_single and "{" not in code and "}" not in code:
            var = m_single.group("var")
            hi = m_single.group("hi").strip()
            body = m_single.group("body")
            allowed_pat = re.compile(rf"\(\s*{re.escape(var)}\s*-\s*1\s*\)|\b{re.escape(var)}\s*-\s*1\b")
            masked = allowed_pat.sub("", body)
            if not re.search(rf"\b{re.escape(var)}\b", masked):
                repl_pat = re.compile(rf"\(\s*{re.escape(var)}\s*-\s*1\s*\)|\b{re.escape(var)}\s*-\s*1\b")
                body_new = repl_pat.sub(var, body)
                out.append(f"{m_single.group('indent')}for (int {var} = 0; {var} < {hi}; ++{var}) {body_new}{comment}{eol}")
                i += 1
                continue
        m = header_re.match(code)
        if not m or _brace_delta(line) <= 0:
            out.append(line)
            i += 1
            continue
        depth = _brace_delta(line)
        j = i + 1
        body: list[str] = []
        while j < len(lines):
            next_depth = _brace_delta(lines[j])
            if depth + next_depth == 0:
                break
            body.append(lines[j])
            depth += next_depth
            j += 1
        if j >= len(lines):
            out.append(line)
            i += 1
            continue
        closing = lines[j]
        body = _rewrite_zero_based_loop_lines(body)
        var = m.group("var")
        hi = m.group("hi").strip()
        allowed_pat = re.compile(rf"\(\s*{re.escape(var)}\s*-\s*1\s*\)|\b{re.escape(var)}\s*-\s*1\b")
        masked = allowed_pat.sub("", "".join(body))
        if re.search(rf"\b{re.escape(var)}\b", masked):
            out.append(line)
            out.extend(body)
            out.append(closing)
            i = j + 1
            continue
        repl_pat = re.compile(rf"\(\s*{re.escape(var)}\s*-\s*1\s*\)|\b{re.escape(var)}\s*-\s*1\b")
        body = [repl_pat.sub(var, ln) for ln in body]
        new_header = f"{m.group('indent')}for (int {var} = 0; {var} < {hi}; ++{var}) {{{comment}{eol}"
        out.append(new_header)
        out.extend(body)
        out.append(closing)
        i = j + 1
    return out


def _rewrite_zero_based_while_lines(lines: list[str]) -> list[str]:
    out: list[str] = []
    i = 0
    init_re = re.compile(r"^(?P<indent>\s*)(?P<var>[A-Za-z_]\w*)\s*=\s*1\s*;\s*$")
    while_re = re.compile(r"^(?P<indent>\s*)while\s*\(\s*(?P<var>[A-Za-z_]\w*)\s*<=\s*(?P<hi>.+?)\s*\)\s*\{\s*$")
    step_re_template = r"^\s*{var}\s*\+=\s*1\s*;\s*$"
    while i < len(lines):
        line = lines[i]
        m_init = init_re.match(_split_cpp_comment(line.rstrip("\r\n"))[0])
        if not m_init or i + 1 >= len(lines):
            out.append(line)
            i += 1
            continue

        while_line = lines[i + 1]
        while_code, while_comment = _split_cpp_comment(while_line.rstrip("\r\n"))
        m_while = while_re.match(while_code)
        if not m_while or m_while.group("var") != m_init.group("var") or _brace_delta(while_line) <= 0:
            out.append(line)
            i += 1
            continue

        depth = _brace_delta(while_line)
        j = i + 2
        body: list[str] = []
        while j < len(lines):
            next_depth = _brace_delta(lines[j])
            if depth + next_depth == 0:
                break
            body.append(lines[j])
            depth += next_depth
            j += 1
        if j >= len(lines):
            out.append(line)
            i += 1
            continue

        closing = lines[j]
        body = _rewrite_zero_based_while_lines(body)
        var = m_init.group("var")
        hi = m_while.group("hi").strip()
        step_re = re.compile(step_re_template.format(var=re.escape(var)))
        step_idx = None
        for idx in range(len(body) - 1, -1, -1):
            code = _split_cpp_comment(body[idx].rstrip("\r\n"))[0]
            if step_re.match(code):
                step_idx = idx
                break
            if code.strip():
                break
        if step_idx is None:
            out.append(line)
            out.append(while_line)
            out.extend(body)
            out.append(closing)
            i = j + 1
            continue

        allowed_pat = re.compile(rf"\(\s*{re.escape(var)}\s*-\s*1\s*\)|\b{re.escape(var)}\s*-\s*1\b")
        masked_parts: list[str] = []
        for idx, body_line in enumerate(body):
            if idx == step_idx:
                continue
            masked_parts.append(allowed_pat.sub("", body_line))
        masked = "".join(masked_parts)
        if re.search(rf"\b{re.escape(var)}\b", masked):
            out.append(line)
            out.append(while_line)
            out.extend(body)
            out.append(closing)
            i = j + 1
            continue

        repl_pat = re.compile(rf"\(\s*{re.escape(var)}\s*-\s*1\s*\)|\b{re.escape(var)}\s*-\s*1\b")
        body = [repl_pat.sub(var, ln) if idx != step_idx else ln for idx, ln in enumerate(body)]
        init_eol = "\n" if line.endswith("\n") else ""
        while_eol = "\n" if while_line.endswith("\n") else ""
        out.append(f"{m_init.group('indent')}{var} = 0;{init_eol}")
        out.append(f"{m_while.group('indent')}while ({var} < {hi}) {{{while_comment}{while_eol}")
        out.extend(body)
        out.append(closing)
        i = j + 1
    return out


def _find_matching_paren(code: str, start: int) -> Optional[int]:
    if start >= len(code) or code[start] != "(":
        return None
    depth = 1
    in_single = False
    in_double = False
    esc = False
    i = start + 1
    while i < len(code):
        ch = code[i]
        if esc:
            esc = False
            i += 1
            continue
        if ch == "\\" and (in_single or in_double):
            esc = True
            i += 1
            continue
        if ch == "'" and not in_double:
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
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def _strip_wrapping_parens(text: str) -> str:
    out = text.strip()
    while out.startswith("(") and out.endswith(")"):
        end = _find_matching_paren(out, 0)
        if end != len(out) - 1:
            break
        out = out[1:-1].strip()
    return out


def _eval_literal_condition(text: str) -> Optional[bool]:
    cond = _strip_wrapping_parens(text)
    cond = re.sub(r"\(\s*([+\-]?\d+)\s*\)", r"\1", cond)
    if re.fullmatch(r"[+\-]?\d+", cond):
        return int(cond) != 0
    m = re.fullmatch(r"([+\-]?\d+)\s*(>=|<=|==|!=|>|<)\s*([+\-]?\d+)", cond)
    if not m:
        return None
    lhs = int(m.group(1))
    op = m.group(2)
    rhs = int(m.group(3))
    if op == ">=":
        return lhs >= rhs
    if op == "<=":
        return lhs <= rhs
    if op == "==":
        return lhs == rhs
    if op == "!=":
        return lhs != rhs
    if op == ">":
        return lhs > rhs
    return lhs < rhs


def _split_top_level_ternary(text: str) -> Optional[tuple[str, str, str]]:
    depth_paren = 0
    depth_brack = 0
    depth_brace = 0
    in_single = False
    in_double = False
    esc = False
    q_pos: Optional[int] = None
    ternary_depth = 0
    for i, ch in enumerate(text):
        if esc:
            esc = False
            continue
        if ch == "\\" and (in_single or in_double):
            esc = True
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            continue
        if in_single or in_double:
            continue
        if ch == "(":
            depth_paren += 1
            continue
        if ch == ")":
            depth_paren = max(0, depth_paren - 1)
            continue
        if ch == "[":
            depth_brack += 1
            continue
        if ch == "]":
            depth_brack = max(0, depth_brack - 1)
            continue
        if ch == "{":
            depth_brace += 1
            continue
        if ch == "}":
            depth_brace = max(0, depth_brace - 1)
            continue
        if depth_paren or depth_brack or depth_brace:
            continue
        if ch == "?":
            if q_pos is None:
                q_pos = i
            else:
                ternary_depth += 1
            continue
        if ch == ":" and q_pos is not None:
            if ternary_depth == 0:
                return text[:q_pos], text[q_pos + 1 : i], text[i + 1 :]
            ternary_depth -= 1
    return None


def _atomic_expr(branch: str) -> bool:
    text = branch.strip()
    if re.fullmatch(r"[+\-]?\d+(?:\.\d+)?(?:[eE][+\-]?\d+)?", text):
        return True
    if re.fullmatch(r"[A-Za-z_]\w*(?:\[[^\[\]]+\]|\.[A-Za-z_]\w*|\([^\(\)]*\))*", text):
        return True
    return False


def _rewrite_wrapped_literal_ternaries(code: str) -> str:
    out: list[str] = []
    in_single = False
    in_double = False
    esc = False
    i = 0
    while i < len(code):
        ch = code[i]
        if esc:
            out.append(ch)
            esc = False
            i += 1
            continue
        if ch == "\\" and (in_single or in_double):
            out.append(ch)
            esc = True
            i += 1
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
            out.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            i += 1
            continue
        if not in_single and not in_double and ch == "(":
            j = i + 1
            while j < len(code) and code[j].isspace():
                j += 1
            if j < len(code) and code[j] == "(":
                cond_end = _find_matching_paren(code, j)
                if cond_end is not None:
                    k = cond_end + 1
                    while k < len(code) and code[k].isspace():
                        k += 1
                    if k < len(code) and code[k] == "?":
                        yes_start = k + 1
                        while yes_start < len(code) and code[yes_start].isspace():
                            yes_start += 1
                        if yes_start < len(code) and code[yes_start] == "(":
                            yes_end = _find_matching_paren(code, yes_start)
                            if yes_end is not None:
                                k2 = yes_end + 1
                                while k2 < len(code) and code[k2].isspace():
                                    k2 += 1
                                if k2 < len(code) and code[k2] == ":":
                                    no_start = k2 + 1
                                    while no_start < len(code) and code[no_start].isspace():
                                        no_start += 1
                                    if no_start < len(code) and code[no_start] == "(":
                                        no_end = _find_matching_paren(code, no_start)
                                        if no_end is not None:
                                            k3 = no_end + 1
                                            while k3 < len(code) and code[k3].isspace():
                                                k3 += 1
                                            if k3 < len(code) and code[k3] == ")":
                                                cond = code[j + 1 : cond_end]
                                                choice = _eval_literal_condition(cond)
                                                if choice is not None:
                                                    branch = code[yes_start + 1 : yes_end] if choice else code[no_start + 1 : no_end]
                                                    branch = branch.strip()
                                                    out.append(branch if _atomic_expr(branch) else f"({branch})")
                                                    i = k3 + 1
                                                    continue
        out.append(ch)
        i += 1
    return "".join(out)


def _simplify_condition_code(code: str) -> str:
    out = code
    if re.search(r"\(\s*(?:const\s+)?(?:unsigned\s+|signed\s+)?(?:short\s+|long\s+)?(?:int|float|double|char|size_t)\s*\)", out):
        return code
    while True:
        parts = _split_top_level_ternary(out.strip())
        if parts is None:
            break
        cond, yes, no = parts
        choice = _eval_literal_condition(cond)
        if choice is None:
            break
        out = yes.strip() if choice else no.strip()
    out = _strip_wrapping_parens(out)
    while out.count(")") > out.count("(") and out.endswith(")"):
        out = out[:-1].rstrip()
    out = re.sub(r"(?<![A-Za-z0-9_])\(\s*([A-Za-z_]\w*|[+\-]?\d+)\s*\)", r"\1", out)
    return out


def _rewrite_constant_condition_lines(lines: list[str]) -> list[str]:
    out: list[str] = []
    line_if_re = re.compile(r"^(?P<indent>\s*)if\s*\(\s*(?P<cond>[01])\s*\)\s*(?P<body>.+?)\s*$")
    line_while_re = re.compile(r"^(?P<indent>\s*)while\s*\(\s*(?P<cond>.+)\s*\)\s*(?P<tail>\{\s*)$")
    line_for_re = re.compile(
        r"^(?P<indent>\s*)for\s*\(\s*(?P<init>[^;]*?)\s*;\s*(?P<cond>[^;]*?)\s*;\s*(?P<step>[^)]*?)\s*\)\s*(?P<tail>\{\s*)$"
    )
    for line in lines:
        eol = "\n" if line.endswith("\n") else ""
        body0 = line[:-1] if eol else line
        code, comment = _split_cpp_comment(body0)
        m_if = line_if_re.match(code)
        if m_if:
            if m_if.group("body").lstrip().startswith("{"):
                out.append(line)
                continue
            if m_if.group("cond") == "1":
                out.append(f"{m_if.group('indent')}{m_if.group('body')}{comment}{eol}")
            else:
                # Dead single-line branch.
                out.append(f"{m_if.group('indent')};{comment}{eol}")
            continue
        m_while = line_while_re.match(code)
        if m_while:
            cond_new = _simplify_condition_code(m_while.group("cond").strip())
            out.append(f"{m_while.group('indent')}while ({cond_new}) {m_while.group('tail')}{comment}{eol}")
            continue
        m_for = line_for_re.match(code)
        if m_for:
            cond_new = _simplify_condition_code(m_for.group("cond").strip())
            out.append(
                f"{m_for.group('indent')}for ({m_for.group('init').strip()}; {cond_new}; {m_for.group('step').strip()}) "
                f"{m_for.group('tail')}{comment}{eol}"
            )
            continue
        out.append(line)
    return out


def _remove_shared_runtime_csv_helper_lines(lines: list[str]) -> list[str]:
    proto_res = [
        re.compile(r"^\s*int\s+count_fields\s*\(\s*const\s+char\s*\*\s*line\s*\)\s*;\s*(?:/\*.*\*/)?\s*$"),
        re.compile(r"^\s*void\s+split_csv_line\s*\(\s*const\s+char\s*\*\s*line\s*,\s*const\s+int\s+n\s*,\s*char\s+\*\*fields\s*\)\s*;\s*(?:/\*.*\*/)?\s*$"),
    ]
    def_res = [
        re.compile(r"^\s*int\s+count_fields\s*\(\s*const\s+char\s*\*\s*line\s*\)\s*\{\s*$"),
        re.compile(r"^\s*void\s+split_csv_line\s*\(\s*const\s+char\s*\*\s*line\s*,\s*const\s+int\s+n\s*,\s*char\s+\*\*fields\s*\)\s*\{\s*$"),
    ]
    out: list[str] = []
    i = 0
    while i < len(lines):
        body = lines[i].rstrip("\r\n")
        code, _comment = _split_cpp_comment(body)
        if any(rx.match(code) for rx in proto_res):
            i += 1
            continue
        if any(rx.match(code) for rx in def_res):
            depth = _brace_delta(lines[i])
            i += 1
            while i < len(lines) and depth > 0:
                depth += _brace_delta(lines[i])
                i += 1
            while i < len(lines) and not lines[i].strip():
                i += 1
            continue
        out.append(lines[i])
        i += 1
    return out


def _remove_unused_const_int_decl_lines(lines: list[str]) -> list[str]:
    text = "".join(lines)
    ids = _collect_identifiers(text)
    counts: dict[str, int] = {}
    for name in ids:
        counts[name] = counts.get(name, 0) + 1
    decl_re = re.compile(
        r"^\s*(?:static\s+)?const\s+int\s+([A-Za-z_]\w*)\s*=\s*[^;]+;\s*$"
    )
    decl_counts: dict[str, int] = {}
    for line in lines:
        body = line.rstrip("\r\n")
        code, _comment = _split_cpp_comment(body)
        m = decl_re.match(code)
        if m:
            name = m.group(1)
            decl_counts[name] = decl_counts.get(name, 0) + 1
    out: list[str] = []
    for line in lines:
        body = line.rstrip("\r\n")
        code, comment = _split_cpp_comment(body)
        m = decl_re.match(code)
        if m:
            name = m.group(1)
            if counts.get(name, 0) == decl_counts.get(name, 0):
                continue
        out.append(line)
    return out


def _split_decl_items(text: str) -> list[str]:
    items: list[str] = []
    cur: list[str] = []
    in_single = False
    in_double = False
    esc = False
    bracket = 0
    for ch in text:
        if esc:
            cur.append(ch)
            esc = False
            continue
        if ch == "\\" and (in_single or in_double):
            cur.append(ch)
            esc = True
            continue
        if ch == "'" and not in_double:
            cur.append(ch)
            in_single = not in_single
            continue
        if ch == '"' and not in_single:
            cur.append(ch)
            in_double = not in_double
            continue
        if in_single or in_double:
            cur.append(ch)
            continue
        if ch == "[":
            bracket += 1
            cur.append(ch)
            continue
        if ch == "]":
            bracket = max(0, bracket - 1)
            cur.append(ch)
            continue
        if ch == "," and bracket == 0:
            item = "".join(cur).strip()
            if item:
                items.append(item)
            cur = []
            continue
        cur.append(ch)
    item = "".join(cur).strip()
    if item:
        items.append(item)
    return items


def _safe_decl_initializer(init: str) -> bool:
    raw = init.strip()
    if not raw:
        return True
    if raw == "NULL":
        return True
    if re.fullmatch(r"[+\-]?\d+(?:\.\d+)?(?:[eE][+\-]?\d+)?(?:f)?", raw):
        return True
    if re.fullmatch(r'"(?:[^"\\]|\\.)*"', raw):
        return True
    return False


def _parse_mergeable_decl_line(line: str) -> Optional[tuple[str, str, str, list[str], str]]:
    eol = "\n" if line.endswith("\n") else ""
    body = line[:-1] if eol else line
    code, comment = _split_cpp_comment(body)
    if comment or not code.strip():
        return None
    if any(tok in code for tok in ("(", ")", "{", "}")):
        return None
    m = re.match(
        r"^(?P<indent>\s*)(?P<prefix>(?:(?:static|const|unsigned|signed|short|long|volatile|restrict)\s+)*(?:int|float|double|char|size_t|ptrdiff_t|FILE|[A-Za-z_]\w*))\s+(?P<decls>.+?)\s*;\s*$",
        code,
    )
    if not m:
        return None
    prefix = m.group("prefix").strip()
    if prefix in {"return", "goto", "break", "continue"}:
        return None
    decl_items = _split_decl_items(m.group("decls"))
    if not decl_items:
        return None
    item_re = re.compile(
        r"^(?P<stars>\*+)?\s*(?P<name>[A-Za-z_]\w*)(?P<suffix>\s*\[[^\]]*\])?\s*(?:=\s*(?P<init>.+))?$"
    )
    star_kind: Optional[int] = None
    for item in decl_items:
        m_item = item_re.match(item)
        if not m_item:
            return None
        stars = m_item.group("stars") or ""
        kind = len(stars)
        if star_kind is None:
            star_kind = kind
        elif star_kind != kind:
            return None
        if not _safe_decl_initializer(m_item.group("init") or ""):
            return None
    key = f"{prefix}|{star_kind}"
    return m.group("indent"), prefix, key, decl_items, eol


def _merge_simple_decl_block(block: list[str]) -> list[str]:
    parsed = [_parse_mergeable_decl_line(line) for line in block]
    if any(p is None for p in parsed):
        return block
    groups: dict[str, list[str]] = {}
    group_order: list[str] = []
    indent = parsed[0][0]  # type: ignore[index]
    for p in parsed:
        p_indent, prefix, key, decl_items, _eol = p  # type: ignore[misc]
        if p_indent != indent:
            return block
        if key not in groups:
            groups[key] = [prefix]
            group_order.append(key)
        groups[key].extend(decl_items)
    out: list[str] = []
    max_len = 110
    for key in group_order:
        prefix = groups[key][0]
        items = groups[key][1:]
        cur = f"{indent}{prefix} {items[0]}"
        for item in items[1:]:
            candidate = f"{cur}, {item}"
            if len(candidate) + 1 > max_len:
                out.append(f"{cur};\n")
                cur = f"{indent}{prefix} {item}"
            else:
                cur = candidate
        out.append(f"{cur};\n")
    return out


def _merge_simple_decl_blocks(lines: list[str]) -> list[str]:
    out: list[str] = []
    block: list[str] = []
    for line in lines:
        if _parse_mergeable_decl_line(line) is not None:
            block.append(line)
            continue
        if block:
            out.extend(_merge_simple_decl_block(block))
            block = []
        out.append(line)
    if block:
        out.extend(_merge_simple_decl_block(block))
    return out


def _remove_unused_loop_label_lines(lines: list[str]) -> list[str]:
    label_re = re.compile(r"^\s*(xf2c_loop_\d+_(?:continue|break))\s*:\s*;\s*$")
    goto_re = re.compile(r"\bgoto\s+(xf2c_loop_\d+_(?:continue|break))\s*;")
    referenced: set[str] = set()
    for line in lines:
        code, _comment = _split_cpp_comment(line.rstrip("\r\n"))
        for m in goto_re.finditer(code):
            referenced.add(m.group(1))
    out: list[str] = []
    for line in lines:
        code, _comment = _split_cpp_comment(line.rstrip("\r\n"))
        m = label_re.match(code)
        if m and m.group(1) not in referenced:
            continue
        out.append(line)
    return out


def _rewrite_local_buffer_length_enums(lines: list[str]) -> list[str]:
    func_header_re = re.compile(r"^\s*[A-Za-z_][\w\s\*]*\([^;]*\)\s*\{\s*$")
    char_decl_re = re.compile(r"^\s*char\s+(.+?)\s*;\s*$")
    item_re = re.compile(r"^(?P<name>[A-Za-z_]\w*)\[(?P<size>\d+)\](?P<rest>\s*(?:=\s*.+)?)$")
    out: list[str] = []
    i = 0

    def process_function_block(block: list[str]) -> list[str]:
        candidates: dict[str, tuple[int, str]] = {}
        first_decl_idx: Optional[int] = None
        for idx, line in enumerate(block):
            body = line.rstrip("\r\n")
            code, comment = _split_cpp_comment(body)
            if comment:
                continue
            m_decl = char_decl_re.match(code)
            if not m_decl:
                continue
            decl_items = _split_decl_items(m_decl.group(1))
            for item in decl_items:
                m_item = item_re.match(item.strip())
                if not m_item:
                    continue
                size = int(m_item.group("size"))
                if size <= 1:
                    continue
                logical = size - 1
                enum_name = f"{m_item.group('name')}_len"
                candidates[m_item.group("name")] = (logical, enum_name)
                if first_decl_idx is None:
                    first_decl_idx = idx
        if not candidates or first_decl_idx is None:
            return block

        use_counts: dict[str, int] = {name: 1 for name in candidates}
        for line in block:
            body = line.rstrip("\r\n")
            code, _comment = _split_cpp_comment(body)
            for name, (logical, _enum_name) in candidates.items():
                if re.search(rf"\bassign_str\s*\(\s*{re.escape(name)}\s*,\s*{logical}\b", code):
                    use_counts[name] += 1
                if re.search(rf"\bassign_substr\s*\(\s*{re.escape(name)}\s*,\s*{logical}\b", code):
                    use_counts[name] += 1
                if re.search(rf"\bread_a\s*\(\s*[^,]+,\s*{re.escape(name)}\s*,\s*{logical}\b", code):
                    use_counts[name] += 1
        chosen = {name: meta for name, meta in candidates.items() if use_counts[name] > 1}
        if not chosen:
            return block

        new_block = list(block)
        enum_items = ", ".join(f"{enum_name} = {logical}" for logical, enum_name in chosen.values())
        indent_match = re.match(r"^(\s*)", block[first_decl_idx])
        indent = indent_match.group(1) if indent_match else ""
        new_block.insert(first_decl_idx, f"{indent}enum {{ {enum_items} }};\n")

        for idx, line in enumerate(new_block):
            body = line.rstrip("\r\n")
            code, comment = _split_cpp_comment(body)
            m_decl = char_decl_re.match(code)
            if m_decl:
                decl_items = _split_decl_items(m_decl.group(1))
                changed = False
                new_items: list[str] = []
                for item in decl_items:
                    m_item = item_re.match(item.strip())
                    if m_item and m_item.group("name") in chosen:
                        _logical, enum_name = chosen[m_item.group("name")]
                        new_items.append(f"{m_item.group('name')}[{enum_name} + 1]{m_item.group('rest')}")
                        changed = True
                    else:
                        new_items.append(item.strip())
                if changed:
                    eol = "\n" if line.endswith("\n") else ""
                    new_block[idx] = f"{indent}char {', '.join(new_items)};{comment}{eol}"
                    continue
            for name, (logical, enum_name) in chosen.items():
                code = re.sub(
                    rf"\bassign_str\s*\(\s*{re.escape(name)}\s*,\s*{logical}\b",
                    f"assign_str({name}, {enum_name}",
                    code,
                )
                code = re.sub(
                    rf"\bassign_substr\s*\(\s*{re.escape(name)}\s*,\s*{logical}\b",
                    f"assign_substr({name}, {enum_name}",
                    code,
                )
                code = re.sub(
                    rf"\bread_a\s*\(\s*([^,]+,\s*){re.escape(name)}\s*,\s*{logical}\b",
                    rf"read_a(\1{name}, {enum_name}",
                    code,
                )
            eol = "\n" if line.endswith("\n") else ""
            new_block[idx] = f"{code}{comment}{eol}"
        return new_block

    while i < len(lines):
        line = lines[i]
        code, _comment = _split_cpp_comment(line.rstrip("\r\n"))
        if not func_header_re.match(code):
            out.append(line)
            i += 1
            continue
        depth = _brace_delta(line)
        block = [line]
        i += 1
        while i < len(lines) and depth > 0:
            block.append(lines[i])
            depth += _brace_delta(lines[i])
            i += 1
        out.extend(process_function_block(block))
    return out


def _is_supported_ast(node: ast.AST) -> bool:
    if isinstance(node, ast.Expression):
        return _is_supported_ast(node.body)
    if isinstance(node, ast.Name):
        return True
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (int, float))
    if isinstance(node, ast.UnaryOp):
        return isinstance(node.op, (ast.UAdd, ast.USub)) and _is_supported_ast(node.operand)
    if isinstance(node, ast.BinOp):
        return isinstance(node.op, (ast.Add, ast.Sub, ast.Mult)) and _is_supported_ast(node.left) and _is_supported_ast(node.right)
    if isinstance(node, ast.Subscript):
        sl = node.slice
        if isinstance(sl, ast.Slice):
            return False
        return _is_supported_ast(node.value) and _is_supported_ast(sl)
    if isinstance(node, ast.Attribute):
        return _is_supported_ast(node.value)
    if isinstance(node, ast.Call):
        return _is_supported_ast(node.func) and all(_is_supported_ast(arg) for arg in node.args) and not node.keywords
    return False


def _from_ast(node: ast.AST) -> Expr:
    if isinstance(node, ast.Expression):
        return _from_ast(node.body)
    if isinstance(node, ast.Name):
        return Expr("name", value=node.id)
    if isinstance(node, ast.Constant):
        return Expr("const", value=node.value)
    if isinstance(node, ast.UnaryOp):
        op = "+" if isinstance(node.op, ast.UAdd) else "-"
        return Expr("unary", value=op, operand=_from_ast(node.operand))
    if isinstance(node, ast.BinOp):
        op_map = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}
        op = op_map[type(node.op)]
        return Expr("bin", value=op, left=_from_ast(node.left), right=_from_ast(node.right))
    if isinstance(node, ast.Subscript):
        return Expr("subscript", base=_from_ast(node.value), index=_from_ast(node.slice))
    if isinstance(node, ast.Attribute):
        return Expr("attr", base=_from_ast(node.value), attr=node.attr)
    if isinstance(node, ast.Call):
        return Expr("call", func=_from_ast(node.func), args=tuple(_from_ast(arg) for arg in node.args))
    raise TypeError(f"unsupported AST node: {type(node).__name__}")


def _is_int_const(expr: Expr) -> bool:
    return expr.kind == "const" and isinstance(expr.value, int) and not isinstance(expr.value, bool)


def _const_int(expr: Expr) -> int:
    return int(expr.value)


def _contains_call(expr: Expr) -> bool:
    if expr.kind == "call":
        return True
    if expr.kind == "bin":
        return _contains_call(expr.left) or _contains_call(expr.right)
    if expr.kind == "unary":
        return _contains_call(expr.operand)
    if expr.kind == "subscript":
        return _contains_call(expr.base) or _contains_call(expr.index)
    if expr.kind == "attr":
        return _contains_call(expr.base)
    return False


def _simplify(expr: Expr) -> Expr:
    if expr.kind == "bin":
        left = _simplify(expr.left)
        right = _simplify(expr.right)
        op = str(expr.value)
        if _is_int_const(left) and _is_int_const(right):
            a = _const_int(left)
            b = _const_int(right)
            if op == "+":
                return Expr("const", value=a + b)
            if op == "-":
                return Expr("const", value=a - b)
            if op == "*":
                return Expr("const", value=a * b)
        if op == "+":
            if _is_int_const(left) and _const_int(left) == 0:
                return right
            if _is_int_const(right) and _const_int(right) == 0:
                return left
        if op == "-":
            if _is_int_const(right) and _const_int(right) == 0:
                return left
            if _is_int_const(left) and _const_int(left) == 0:
                return _simplify(Expr("unary", value="-", operand=right))
        if op == "*":
            if _is_int_const(left) and _const_int(left) == 1:
                return right
            if _is_int_const(right) and _const_int(right) == 1:
                return left
            if _is_int_const(left) and _const_int(left) == 0 and not _contains_call(right):
                return Expr("const", value=0)
            if _is_int_const(right) and _const_int(right) == 0 and not _contains_call(left):
                return Expr("const", value=0)
        return Expr("bin", value=op, left=left, right=right)
    if expr.kind == "unary":
        operand = _simplify(expr.operand)
        op = str(expr.value)
        if _is_int_const(operand):
            return Expr("const", value=(+_const_int(operand) if op == "+" else -_const_int(operand)))
        if operand.kind == "unary":
            inner_op = str(operand.value)
            if op == "+":
                return operand
            if op == "-" and inner_op == "-":
                return operand.operand
        return Expr("unary", value=op, operand=operand)
    if expr.kind == "subscript":
        return Expr("subscript", base=_simplify(expr.base), index=_simplify(expr.index))
    if expr.kind == "attr":
        return Expr("attr", base=_simplify(expr.base), attr=expr.attr)
    if expr.kind == "call":
        return Expr("call", func=_simplify(expr.func), args=tuple(_simplify(arg) for arg in expr.args))
    return expr


def _precedence(expr: Expr) -> int:
    if expr.kind in {"const", "name", "subscript", "attr", "call"}:
        return 100
    if expr.kind == "unary":
        return 90
    if expr.kind == "bin":
        if expr.value == "*":
            return 80
        return 70
    return 0


def _emit(expr: Expr, parent_prec: int = 0, side: str = "") -> str:
    if expr.kind == "const":
        if isinstance(expr.value, float):
            return repr(expr.value)
        return str(expr.value)
    if expr.kind == "name":
        return str(expr.value)
    if expr.kind == "subscript":
        return f"{_emit(expr.base, 100)}[{_emit(expr.index, 0)}]"
    if expr.kind == "attr":
        return f"{_emit(expr.base, 100)}.{expr.attr}"
    if expr.kind == "call":
        return f"{_emit(expr.func, 100)}({', '.join(_emit(arg, 0) for arg in expr.args)})"
    if expr.kind == "unary":
        cur = _precedence(expr)
        body = _emit(expr.operand, cur, "right")
        text = f"{expr.value}{body}"
        if cur < parent_prec:
            return f"({text})"
        return text
    if expr.kind == "bin":
        cur = _precedence(expr)
        right_prec = cur + 1 if expr.value == "-" else cur
        left_txt = _emit(expr.left, cur, "left")
        right_txt = _emit(expr.right, right_prec, "right")
        text = f"{left_txt} {expr.value} {right_txt}"
        if cur < parent_prec:
            return f"({text})"
        return text
    raise TypeError(f"cannot emit expr kind {expr.kind}")


def simplify_expr_text(expr_text: str) -> str:
    raw = expr_text.strip()
    if not raw:
        return expr_text
    if any(tok in raw for tok in ("++", "--", "->", "&&", "||", "?")):
        return expr_text
    if re.search(r"\(\s*(?:const\s+)?(?:unsigned\s+|signed\s+)?(?:short\s+|long\s+)?(?:int|float|double|char|size_t)\s*\)\s*\(", raw):
        return expr_text
    try:
        parsed = ast.parse(raw, mode="eval")
    except SyntaxError:
        return expr_text
    if not _is_supported_ast(parsed):
        return expr_text
    simp = _simplify(_from_ast(parsed))
    return _emit(simp)


def _rewrite_bracket_exprs(code: str) -> str:
    out: list[str] = []
    in_single = False
    in_double = False
    esc = False
    i = 0
    while i < len(code):
        ch = code[i]
        if esc:
            out.append(ch)
            esc = False
            i += 1
            continue
        if ch == "\\" and (in_single or in_double):
            out.append(ch)
            esc = True
            i += 1
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
            out.append(ch)
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            i += 1
            continue
        if not in_single and not in_double and ch == "[":
            depth = 1
            j = i + 1
            inner_single = False
            inner_double = False
            inner_esc = False
            while j < len(code):
                cj = code[j]
                if inner_esc:
                    inner_esc = False
                    j += 1
                    continue
                if cj == "\\" and (inner_single or inner_double):
                    inner_esc = True
                    j += 1
                    continue
                if cj == "'" and not inner_double:
                    inner_single = not inner_single
                    j += 1
                    continue
                if cj == '"' and not inner_single:
                    inner_double = not inner_double
                    j += 1
                    continue
                if not inner_single and not inner_double:
                    if cj == "[":
                        depth += 1
                    elif cj == "]":
                        depth -= 1
                        if depth == 0:
                            inner = code[i + 1 : j]
                            out.append("[")
                            out.append(simplify_expr_text(inner))
                            out.append("]")
                            i = j + 1
                            break
                j += 1
            else:
                out.append(ch)
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _find_top_level_assignment(code: str) -> Optional[int]:
    depth_paren = 0
    depth_brack = 0
    depth_brace = 0
    in_single = False
    in_double = False
    esc = False
    for i, ch in enumerate(code):
        if esc:
            esc = False
            continue
        if ch == "\\" and (in_single or in_double):
            esc = True
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            continue
        if in_single or in_double:
            continue
        if ch == "(":
            depth_paren += 1
            continue
        if ch == ")":
            depth_paren = max(0, depth_paren - 1)
            continue
        if ch == "[":
            depth_brack += 1
            continue
        if ch == "]":
            depth_brack = max(0, depth_brack - 1)
            continue
        if ch == "{":
            depth_brace += 1
            continue
        if ch == "}":
            depth_brace = max(0, depth_brace - 1)
            continue
        if depth_paren or depth_brack or depth_brace:
            continue
        if ch != "=":
            continue
        prev = code[i - 1] if i > 0 else ""
        nxt = code[i + 1] if i + 1 < len(code) else ""
        if prev in "=!<>+-*/%&|^":
            continue
        if nxt == "=":
            continue
        return i
    return None


def _rewrite_assignment_rhs(code: str) -> str:
    semi = code.rfind(";")
    if semi < 0:
        return code
    assign_pos = _find_top_level_assignment(code[:semi])
    if assign_pos is None:
        return code
    lhs = code[: assign_pos + 1]
    rhs = code[assign_pos + 1 : semi]
    raw_rhs = rhs.strip()
    rhs_new = simplify_expr_text(raw_rhs)
    if rhs_new == raw_rhs:
        return code
    return f"{lhs.rstrip()} {rhs_new}{code[semi:]}"


def postprocess_c_line(line: str, rename_map: Optional[dict[str, str]] = None) -> str:
    eol = "\n" if line.endswith("\n") else ""
    body = line[:-1] if eol else line
    code, comment = _split_cpp_comment(body)
    code = _rewrite_helper_names(code, rename_map or {})
    code = _rewrite_wrapped_literal_ternaries(code)
    code = _rewrite_atomic_scalar_parens(code)
    code = _rewrite_bracket_exprs(code)
    code = _rewrite_assignment_rhs(code)
    return f"{code}{comment}{eol}"


def postprocess_c_text(text: str) -> str:
    out = text
    for _ in range(4):
        lines = out.splitlines(keepends=True)
        rename_map = _helper_rename_map(out)
        renamed_lines: list[str] = []
        for line in lines:
            eol = "\n" if line.endswith("\n") else ""
            body = line[:-1] if eol else line
            code, comment = _split_cpp_comment(body)
            renamed_lines.append(f"{_rewrite_helper_names(code, rename_map)}{comment}{eol}")
        shared_runtime_lines = _remove_shared_runtime_csv_helper_lines(renamed_lines)
        loop_lines = _rewrite_zero_based_loop_lines(shared_runtime_lines)
        while_lines = _rewrite_zero_based_while_lines(loop_lines)
        cond_lines = _rewrite_constant_condition_lines(while_lines)
        final_lines = _remove_unused_loop_label_lines(
            _rewrite_local_buffer_length_enums(
                _merge_simple_decl_blocks(_remove_unused_const_int_decl_lines(cond_lines))
            )
        )
        new_out = "".join(postprocess_c_line(line, {}) for line in final_lines)
        if new_out == out:
            break
        out = new_out
    return out


def _write_or_check(path: Path, new_text: str, *, in_place: bool, check: bool) -> int:
    old_text = path.read_text(encoding="utf-8", errors="replace")
    changed = (new_text != old_text)
    if check:
        if changed:
            print(f"would change: {path}")
            return 1
        return 0
    if in_place:
        if changed:
            path.write_text(new_text, encoding="utf-8")
            print(f"rewrote {path}")
        return 0
    sys.stdout.write(new_text)
    return 0


def main(argv: Optional[Iterable[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="Conservative readability cleanup for generated C code.")
    ap.add_argument("c_files", nargs="+", help="Input C source file(s).")
    ap.add_argument("--in-place", action="store_true", help="Rewrite files in place.")
    ap.add_argument("--check", action="store_true", help="Exit nonzero if any file would change.")
    args = ap.parse_args(list(argv) if argv is not None else None)

    if len(args.c_files) > 1 and not (args.in_place or args.check):
        ap.error("multiple input files require --in-place or --check")

    rc = 0
    for raw in args.c_files:
        path = Path(raw)
        text = path.read_text(encoding="utf-8", errors="replace")
        new_text = postprocess_c_text(text)
        rc = max(rc, _write_or_check(path, new_text, in_place=args.in_place, check=args.check))
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
