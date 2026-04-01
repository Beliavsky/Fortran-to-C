from __future__ import annotations

import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
EXAMPLE_MD_PATH = REPO_ROOT / "xf2c_example_md.py"


def test_xf2c_example_md_writes_markdown(tmp_path: Path) -> None:
    src_path = tmp_path / "demo.f90"
    src_path.write_text("program demo\nprint *, 42\nend program demo\n", encoding="utf-8")

    c_path = tmp_path / "temp_demo.c"
    xf2c_stub = tmp_path / "xf2c.py"
    xf2c_stub.write_text(
        "\n".join(
            [
                "from pathlib import Path",
                "import sys",
                "Path('temp_demo.c').write_text('int main(void) { return 0; }\\n', encoding='utf-8')",
                "print('Build (original-fortran): PASS')",
                "print('Run (original-fortran): PASS')",
                "print('42')",
                "print()",
                "print('Wrote temp_demo.c')",
                "print('Build (transformed-c): PASS')",
                "print('Run (transformed-c): PASS')",
                "print('42')",
                "",
            ]
        ),
        encoding="utf-8",
    )

    out_path = tmp_path / "demo.md"
    proc = subprocess.run(
        [
            sys.executable,
            str(EXAMPLE_MD_PATH),
            str(src_path),
            "--xf2c",
            str(xf2c_stub),
            "--out",
            str(out_path),
        ],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert c_path.is_file()
    md = out_path.read_text(encoding="utf-8")
    assert "# demo" in md
    assert "## Fortran" in md
    assert "## Fortran Output" in md
    assert "## Generated C" in md
    assert "## C Output" in md
    assert "program demo" in md
    assert "int main(void) { return 0; }" in md
    assert "42" in md
    assert "`python xf2c.py demo.f90 --run-both`" in md
