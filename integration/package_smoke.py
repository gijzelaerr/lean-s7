"""Build and run a separate offline Lake consumer of the public library."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


def run(root: Path) -> None:
    root = root.resolve()
    fixture = root / "integration" / "package_smoke"
    lake = os.environ.get("LAKE", "lake")
    config = (
        (fixture / "lakefile.toml.in")
        .read_text()
        .replace("@REPOSITORY_PATH@", json.dumps(str(root), ensure_ascii=False))
    )
    # The dependency is a local path: no clone, fetch, publication or PLC IO.
    with tempfile.TemporaryDirectory(prefix="lean-s7-consumer-") as directory:
        consumer = Path(directory)
        (consumer / "lakefile.toml").write_text(config)
        shutil.copyfile(root / "lean-toolchain", consumer / "lean-toolchain")
        shutil.copyfile(fixture / "Main.lean", consumer / "Main.lean")
        result = subprocess.run(
            [lake, "exe", "consumer-smoke"],
            cwd=consumer,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        if result.returncode:
            raise AssertionError(
                f"external consumer failed ({result.returncode}):\n"
                f"{result.stdout}\n{result.stderr}"
            )
        if result.stdout.strip() != "external Lake consumer smoke passed":
            raise AssertionError(
                f"unexpected external consumer output: {result.stdout!r}"
            )
    print(
        "external Lake package smoke passed: public imports, proof, codecs and IO API"
    )


if __name__ == "__main__":
    run(Path(__file__).resolve().parents[1])
