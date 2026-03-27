# Fortran-to-C

`xf2c.py` is a Python source-to-source transpiler, developed with Codex, that converts a substantial subset of free-form Fortran into readable C.

It is intended for:

- understanding and inspecting translated code
- building small and medium Fortran examples as C programs
- regression-testing Fortran and generated C side by side
- growing coverage incrementally from real Fortran codes

It is not positioned as a full Fortran compiler. It emits C source and then uses a C compiler such as `gcc` or `clang`.

## Current Status

The project currently handles a broad practical subset of Fortran used in the example corpus in this repository, including:

- `program`, `module`, `use`, contained procedures
- `function`, `subroutine`, optional arguments, generic interfaces with module procedures
- simple derived types, selected type-bound procedures, and selected operator overloading
- `allocatable`, `pointer`, `target`, `save`, `parameter`
- scalar and array expressions
- array constructors, array sections, lower bounds other than `1`
- `size`, `shape`, `lbound`, `ubound`
- `sum`, `product`, `minval`, `maxval`, `count`, `any`, `all`, `dot_product`
- `spread`, `reshape` including `order=`, `pack`
- `minloc`, `maxloc`, `findloc`
- `forall`
- scalar complex numbers and common complex intrinsics
- allocatable strings and many common CHARACTER operations
- list-directed output and a growing subset of formatted I/O
- stream I/O, `rewind`, and `backspace`
- `select case`, including character selectors and numeric ranges

Coverage is still incomplete. The project is driven by real examples, so unsupported features are added as they are encountered and generalized.

## Requirements

- Python 3
- A Fortran compiler for `--run-both` or `--compile-both`
  - typically `gfortran`
- A C compiler for generated C
  - `gcc` is the default target
  - `clang` is also supported
  - `cl.exe` support exists as an option, but `gcc` is the primary target and `clang` is secondary

## Main Files

- [xf2c.py](xf2c.py): thin CLI entry point
- [xf2c_driver.py](xf2c_driver.py): CLI, build, run, and orchestration
- [xf2c_core.py](xf2c_core.py): main transpilation logic
- [fortran_scan.py](fortran_scan.py): scanning and validation
- [fortran_runtime.c](fortran_runtime.c): shared C runtime helpers
- [fortran_runtime.h](fortran_runtime.h): shared runtime declarations
- [xc_post.py](xc_post.py): conservative C readability cleanup
- [xnormalize.py](xnormalize.py): output normalization used by `--pretty`

## Basic Usage

Generate C:

```cmd
python xf2c.py xhello.f90
```

Write generated C to stdout as well:

```cmd
python xf2c.py xhello.f90 --tee
```

Compile generated C:

```cmd
python xf2c.py xhello.f90 --compile
```

Compile and run generated C:

```cmd
python xf2c.py xhello.f90 --run
```

Build and run both the original Fortran and the generated C:

```cmd
python xf2c.py xhello.f90 --run-both
```

Normalize displayed output from both runs for easier comparison:

```cmd
python xf2c.py xhello.f90 --run-both --pretty
```

## Output Files

By default, generated C is written as:

```text
temp_<source-stem>.c
```

Examples:

- `xhello.f90` -> `temp_xhello.c`
- `xstream.f90` -> `temp_xstream.c`

Use `--out` to choose the output filename explicitly:

```cmd
python xf2c.py xhello.f90 --out hello_transpiled.c
```

## Useful Options

```text
--tee            print generated C
--compile        compile generated C
--compile-c      compile generated C only, no link
--run            compile and run generated C
--run-both       run original Fortran and generated C
--compile-both   build original Fortran and generated C
--one-line       collapse simple one-statement C blocks
--annotate       add original-Fortran comments before translated code
--raw            disable C postprocessing
--single-file    embed runtime helpers directly into the generated C file
--clang          compile generated C with clang
--msvc           compile generated C with cl.exe
--pretty         normalize displayed run output only
--no-validate    skip pre-validation
```

Examples:

```cmd
python xf2c.py xmean_sd.f90 --run-both --pretty
python xf2c.py xreturns.f90 --compile --tee
python xf2c.py xstream.f90 --single-file --run
python xf2c.py xcomplex.f90 --compile --clang
```

## Raw vs Postprocessed C

By default, generated C is postprocessed for readability.

That cleanup currently does conservative transformations such as:

- removing dead loop labels
- simplifying constant integer expressions
- reducing redundant parentheses
- consolidating declarations
- improving generated temporary names

To see the raw transpiler output:

```cmd
python xf2c.py xsum_dim.f90 --raw --tee
```

## Shared Runtime vs Single File

By default, generated programs include and link the shared runtime:

- [fortran_runtime.h](fortran_runtime.h)
- [fortran_runtime.c](fortran_runtime.c)

This keeps emitted C shorter and more readable.

If you want one standalone generated C file:

```cmd
python xf2c.py xread.f90 --single-file
```

## Running Many Examples

The batch runner reads example names from [fortran_files.txt](fortran_files.txt):

```cmd
xf2c.bat
```

Override the file list on the command line:

```cmd
xf2c.bat xhello.f90 xlogical.f90
```

Limit how many files are processed:

```cmd
xf2c.bat --limit 5
```

## Testing

Run the Python test suite:

```cmd
python -m pytest tests/test_xf2c_cli.py tests/test_xc_post.py tests/test_mt19937_runif.py -q
```

The pytest harness can also select the C compiler:

```cmd
python -m pytest tests/test_xf2c_cli.py tests/test_xc_post.py tests/test_mt19937_runif.py -q --c-compiler=gcc
python -m pytest tests/test_xf2c_cli.py tests/test_xc_post.py tests/test_mt19937_runif.py -q --c-compiler=clang
python -m pytest tests/test_xf2c_cli.py tests/test_xc_post.py tests/test_mt19937_runif.py -q --c-compiler=msvc
```

The most meaningful tests use `--run-both` and compare normalized Fortran and C output, not just whether the generated C compiles.

## What Works Well Today

The project is strongest on:

- numerically oriented procedural code
- arrays and common array intrinsics
- string handling used in practical examples
- small module-based programs
- source inspection and debugging of translated output

The generated C is intended to be readable, especially with the default postprocessing enabled.

## Current Limitations

This is still a subset transpiler. You should expect gaps.

Known limits include:

- some formatted I/O patterns are still unsupported
- some advanced module and interface cases still need work
- polymorphic and richer object-oriented Fortran is only partially handled
- support is much stronger for free-form Fortran than for older fixed-form code
- `gcc` is the primary supported C compiler; `clang` is useful; `msvc` is not a current priority

If a construct is unsupported, the transpiler usually emits a clear validation or `/* unsupported: ... */` marker showing what still needs lowering.

## Recommended Workflow

For a new example:

1. Run:

```cmd
python xf2c.py your_file.f90 --run-both --pretty
```

2. If validation fails, fix or extend the transpiler.

3. If C builds but output differs, inspect:

```cmd
python xf2c.py your_file.f90 --run-both
python xf2c.py your_file.f90 --tee
```

4. Add a focused pytest regression once the feature works.

## Project Direction

The long-term goal is broad practical coverage of Fortran-to-C translation while keeping generated C understandable.

This project is best thought of as:

- a Fortran-to-C transpiler
- a source-to-source compiler in workflow style

but not a replacement for a full native Fortran compiler.
