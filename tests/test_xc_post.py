from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from xc_post import postprocess_c_text, simplify_expr_text


REPO_ROOT = Path(__file__).resolve().parents[1]
XC_POST_PATH = REPO_ROOT / "xc_post.py"


def test_simplify_expr_text_folds_integer_index_arithmetic() -> None:
    assert simplify_expr_text("((1) - 1) + (2) * p_fill") == "2 * p_fill"
    assert simplify_expr_text("((2) - 1) + (2) * p_fill") == "1 + 2 * p_fill"
    assert simplify_expr_text("n - 1 + 1 - 1") == "n - 1"
    assert simplify_expr_text("i - -2") == "i + 2"


def test_postprocess_c_text_simplifies_generated_array_fill() -> None:
    src = "\n".join(
        [
            "for (int p_fill = 0; p_fill < 3; ++p_fill) {",
            "   y[((1) - 1) + (2) * p_fill] = x[p_fill];",
            "}",
            "for (int p_fill = 0; p_fill < 3; ++p_fill) {",
            "   y[((2) - 1) + (2) * p_fill] = 10*x[p_fill];",
            "}",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "y[2 * p_fill] = x[p_fill];" in got
    assert "y[1 + 2 * p_fill] = 10 * x[p_fill];" in got


def test_xc_post_cli_rewrites_in_place() -> None:
    src = "y[((2) - 1) + (2) * p_fill] = 10*x[p_fill];\n"
    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "temp_demo.c"
        path.write_text(src, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(XC_POST_PATH), str(path), "--in-place"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "rewrote" in proc.stdout
        assert path.read_text(encoding="utf-8") == "y[1 + 2 * p_fill] = 10 * x[p_fill];\n"


def test_postprocess_c_text_preserves_predecrement_indexing() -> None:
    src = "while (n > 0) buf[--n] = '\\0';\n"
    assert postprocess_c_text(src) == src


def test_postprocess_c_text_preserves_c_style_casts() -> None:
    src = "x2 = ((float) (n)) * x;\n"
    assert postprocess_c_text(src) == "x2 = ((float) n) * x;\n"


def test_postprocess_c_text_renames_common_helper_identifiers() -> None:
    src = "\n".join(
        [
            "int __first = 1;",
            "float __sum = 0;",
            "char __buf[4096];",
            'printf("%s%s", __first ? "" : " ", __buf);',
            "__first = 0;",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "int first = 1;" in got
    assert "float sum = 0;" in got
    assert "char buf[4096];" in got
    assert 'printf("%s%s", first ? "" : " ", buf);' in got
    assert "__first" not in got


def test_postprocess_c_text_uses_i_prefix_for_integer_helper_collisions() -> None:
    src = "\n".join(
        [
            "int first = 7;",
            "float sum = 1.0f;",
            "int __first = 1;",
            "float __sum = 0;",
            "__first = 0;",
            "__sum += sum;",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "int first = 7, ifirst = 1;" in got
    assert "float sum = 1.0f, xsum = 0;" in got
    assert "ifirst = 0;" in got
    assert "xsum += sum;" in got


def test_postprocess_c_text_renames_generated_extent_and_temp_identifiers() -> None:
    src = "\n".join(
        [
            "int __n_names = 0;",
            "char *__arg_str_0 = trim_s(filename);",
            "double __red = 0.0;",
            "__n_names = n_assets;",
            "__red += values[i];",
            "use_line(__arg_str_0, __n_names, __red);",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "int n_names = 0;" in got
    assert "char *arg_str_0 = trim_s(filename);" in got
    assert "double red = 0.0;" in got
    assert "__n_names" not in got
    assert "__arg_str_0" not in got
    assert "__red" not in got


def test_postprocess_c_text_strips_atomic_scalar_parens_but_keeps_casts() -> None:
    src = "\n".join(
        [
            "for (int i_fill = 0; i_fill < (n_assets); ++i_fill) names[i_fill] = NULL;",
            "if (!names && (n_assets) > 0) return 1;",
            "mu[j_fill] = __red / ((double) (__n_rets_1));",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "for (int i_fill = 0; i_fill < n_assets; ++i_fill) names[i_fill] = NULL;" in got
    assert "if (!names && n_assets > 0) return 1;" in got
    assert "mu[j_fill] = red / ((double) n_rets_1);" in got


def test_postprocess_c_text_rewrites_simple_one_based_loops_to_zero_based() -> None:
    src = "\n".join(
        [
            "for (int j = 1; j <= 3; ++j) {",
            "   sum = 0;",
            "   for (int i = 1; i <= 2; ++i) sum += y[(i - 1) + (2) * (j - 1)];",
            '   printf("%s%g", first ? "" : " ", sum);',
            "   first = 0;",
            "}",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "for (int j = 0; j < 3; ++j) {" in got
    assert "for (int i = 0; i < 2; ++i) sum += y[i + 2 * j];" in got


def test_postprocess_c_text_rewrites_simple_one_based_while_loops_to_zero_based() -> None:
    src = "\n".join(
        [
            "j = 1;",
            "while (j <= n_assets) {",
            "   name_width = fmax(name_width, len_trim_s(names[j - 1]));",
            "   xf2c_loop_4_continue: ;",
            "   j += 1;",
            "}",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "j = 0;" in got
    assert "while (j < n_assets) {" in got
    assert "len_trim_s(names[j]))" in got
    assert "j += 1;" in got


def test_postprocess_c_text_removes_always_true_single_line_if() -> None:
    src = "if (1) sum += x[i_pr];\n"
    assert postprocess_c_text(src) == "sum += x[i_pr];\n"


def test_postprocess_c_text_preserves_block_if_else_when_condition_is_literal() -> None:
    src = "\n".join(
        [
            "if (1) {",
            "   found = 1;",
            "} else {",
            "   found = 0;",
            "}",
            "",
        ]
    )
    assert postprocess_c_text(src) == src


def test_postprocess_c_text_simplifies_literal_controlled_while_condition() -> None:
    src = "while (((1) >= 0) ? (i <= (n)) : (i >= (n))) {\n"
    assert postprocess_c_text(src) == "while (i <= n) {\n"


def test_postprocess_c_text_preserves_function_call_arguments_in_conditions() -> None:
    src = "while (i <= (len_trim_s(line))) {\n"
    assert postprocess_c_text(src) == "while (i <= (len_trim_s(line))) {\n"


def test_postprocess_c_text_folds_integer_arithmetic_inside_conditions() -> None:
    src = "while (i <= ((-2 + ((4 - -2 + 1)) - 1))) {\n"
    assert postprocess_c_text(src) == "while (i <= 4) {\n"


def test_postprocess_c_text_removes_consecutive_minus_signs() -> None:
    src = "x[i - -2] = 10.0 * i;\nwhile (i <= n - 1 + 1 - 1) {\n"
    got = postprocess_c_text(src)
    assert "x[i + 2] = 10.0 * i;\n" in got
    assert "while (i <= n - 1) {\n" in got


def test_postprocess_c_text_simplifies_parenthesized_integer_arithmetic() -> None:
    src = "\n".join(
        [
            "x = (float*) malloc(sizeof(float) * (4 - -2 + 1));",
            "sub((4 - -2 + 1), x);",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "x = (float*) malloc(sizeof(float) * 7);\n" in got
    assert "sub(7, x);\n" in got


def test_postprocess_c_text_simplifies_literal_controlled_for_condition() -> None:
    src = "for (int i2 = 1; (1) > 0 ? i2 <= 3 : i2 >= 3; i2 += 1) {\n"
    assert postprocess_c_text(src) == "for (int i2 = 1; i2 <= 3; i2 += 1) {\n"


def test_postprocess_c_text_simplifies_wrapped_literal_ternary_expression() -> None:
    src = 'printf("%12d", ((1) ? (10) : (w[i_pr])));\n'
    assert postprocess_c_text(src) == 'printf("%12d", 10);\n'


def test_postprocess_c_text_removes_unused_const_int_declaration() -> None:
    src = "\n".join(
        [
            "int n;",
            "const int dp = 8;",
            "n = 3;",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "const int dp = 8;" not in got
    assert "int n = 3;" in got


def test_postprocess_c_text_removes_inline_csv_runtime_helpers() -> None:
    src = "\n".join(
        [
            '#include "fortran_runtime.h"',
            "",
            "int count_fields(const char * line); /* count comma-separated fields */",
            "void split_csv_line(const char * line, const int n, char **fields); /* split a csv line on commas */",
            "",
            "int count_fields(const char * line) {",
            "   int nfields = 1;",
            "   return nfields;",
            "}",
            "",
            "void split_csv_line(const char * line, const int n, char **fields) {",
            "   (void) line;",
            "   (void) n;",
            "   (void) fields;",
            "}",
            "",
            "int main(void) {",
            "   return count_fields(\"a,b\");",
            "}",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert 'int count_fields(const char * line);' not in got
    assert 'void split_csv_line(const char * line, const int n, char **fields);' not in got
    assert 'int count_fields(const char * line) {' not in got
    assert 'void split_csv_line(const char * line, const int n, char **fields) {' not in got
    assert 'return count_fields("a,b");' in got


def test_postprocess_c_text_merges_simple_declaration_blocks() -> None:
    src = "\n".join(
        [
            "char **names = NULL;",
            "int n_names = 0;",
            "char **fields = NULL;",
            "int n_fields = 0;",
            "double *prices = NULL;",
            "int n_prices_1 = 0, n_prices_2 = 0;",
            "double *rets = NULL;",
            "int n_rets_1 = 0, n_rets_2 = 0;",
            "double *mu = NULL;",
            "int n_mu = 0;",
            "double *sig = NULL;",
            "int n_sig = 0;",
            "int iu, ios, n_assets, nobs, i, j, name_width;",
            'char fmt[101] = "";',
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "char **names = NULL, **fields = NULL;" in got
    assert "double *prices = NULL, *rets = NULL, *mu = NULL, *sig = NULL;" in got
    assert "int n_names = 0, n_fields = 0, n_prices_1 = 0, n_prices_2 = 0, n_rets_1 = 0, n_rets_2 = 0, n_mu = 0;" in got
    assert "int n_sig = 0, iu, ios, n_assets, nobs, i, j, name_width;" in got


def test_postprocess_c_text_removes_only_unreferenced_loop_labels() -> None:
    src = "\n".join(
        [
            "while (1) {",
            "   xf2c_loop_1_continue: ;",
            "   if (done) goto xf2c_loop_1_break;",
            "}",
            "xf2c_loop_1_break: ;",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "xf2c_loop_1_continue: ;" not in got
    assert "goto xf2c_loop_1_break;" in got
    assert "xf2c_loop_1_break: ;" in got


def test_postprocess_c_text_introduces_local_enums_for_reused_buffer_lengths() -> None:
    src = "\n".join(
        [
            "int main(int argc, char **argv) {",
            '   char filename[257] = "", line[4097] = "", fmt[101] = "";',
            '   assign_str(filename, 256, (1 < argc) ? argv[1] : "");',
            "   ios = read_a(iu, line, 4096);",
            "   ios = read_a(iu, line, 4096);",
            "}",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "enum { filename_len = 256, line_len = 4096 };" in got
    assert 'char filename[filename_len + 1] = "", line[line_len + 1] = "", fmt[101] = "";' in got
    assert 'assign_str(filename, filename_len, (1 < argc) ? argv[1] : "");' in got
    assert "read_a(iu, line, line_len)" in got


def test_postprocess_c_text_merges_immediate_simple_initializer() -> None:
    src = "\n".join(
        [
            "void f(void) {",
            "   int i;",
            "   i = 0;",
            "}",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert "   int i = 0;\n" in got
    assert "   int i;\n" not in got
    assert "   i = 0;\n" not in got


def test_postprocess_c_text_does_not_merge_initializer_across_comment() -> None:
    src = "\n".join(
        [
            "void f(void) {",
            "   int i;",
            "   /* keep */",
            "   i = 0;",
            "}",
            "",
        ]
    )
    got = postprocess_c_text(src)
    assert got == src
