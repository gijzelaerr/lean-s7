"""Build a pinned independent Snap7 endpoint; never link it into the client."""

from __future__ import annotations

import hashlib
import json
import os
import platform
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request
from pathlib import Path

REVISION = "30f37da3114024a71ba93f7fd855c680b97a406f"
ARCHIVE_SHA256 = "2840d50a833d928e5175b8ccc5383fae0fcc3e826c07e60b2b4190a30c613c36"
URL = f"https://codeload.github.com/davenardella/snap7/tar.gz/{REVISION}"
SOURCES = (
    "sys/snap_msgsock.cpp",
    "sys/snap_sysutils.cpp",
    "sys/snap_tcpsrvr.cpp",
    "sys/snap_threads.cpp",
    "core/s7_client.cpp",
    "core/s7_isotcp.cpp",
    "core/s7_partner.cpp",
    "core/s7_peer.cpp",
    "core/s7_server.cpp",
    "core/s7_text.cpp",
    "core/s7_micro_client.cpp",
    "lib/snap7_libmain.cpp",
)


def build(root: Path) -> Path:
    system = platform.system()
    if system not in ("Linux", "Darwin"):
        raise ValueError("native endpoint builder supports Linux and macOS only")
    compiler = shutil.which(os.environ.get("CXX", "c++"))
    if compiler is None:
        raise RuntimeError("native endpoint testing requires a C++ compiler")
    destination = root / ".lake" / "native-snap7"
    destination.mkdir(parents=True, exist_ok=True)
    library = destination / ("libsnap7.dylib" if system == "Darwin" else "libsnap7.so")
    with tempfile.TemporaryDirectory(prefix="lean-s7-native-build-") as directory:
        staging = Path(directory)
        archive = staging / "source.tar.gz"
        with (
            urllib.request.urlopen(URL, timeout=60) as response,
            archive.open("wb") as output,
        ):
            shutil.copyfileobj(response, output)
        if hashlib.sha256(archive.read_bytes()).hexdigest() != ARCHIVE_SHA256:
            raise ValueError("pinned native source archive digest mismatch")
        with tarfile.open(archive) as source_archive:
            source_archive.extractall(staging, filter="data")
        source = staging / f"snap7-{REVISION}"
        command = [compiler, "-std=c++11", "-O2", "-fPIC", "-pthread"]
        command += ["-dynamiclib" if system == "Darwin" else "-shared"]
        command += ["-I", "src/sys", "-I", "src/core", "-I", "src/lib"]
        command += [f"src/{name}" for name in SOURCES]
        temporary_library = staging / library.name
        command += ["-o", str(temporary_library)]
        compilation = subprocess.run(
            command,
            cwd=source,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        (destination / "build.log").write_text(compilation.stdout + compilation.stderr)
        if compilation.returncode:
            raise RuntimeError(f"native build failed; see {destination / 'build.log'}")
        shutil.copyfile(temporary_library, library)
    library.with_suffix(library.suffix + ".json").write_text(
        json.dumps(
            {
                "repository": "davenardella/snap7",
                "revision": REVISION,
                "archive_sha256": ARCHIVE_SHA256,
                "library_sha256": hashlib.sha256(library.read_bytes()).hexdigest(),
                "platform": system,
                "machine": platform.machine(),
                "compiler": compiler,
            },
            sort_keys=True,
        )
    )
    print(f"native Snap7 test endpoint built: {REVISION}; {library}")
    return library


if __name__ == "__main__":
    build(Path(__file__).resolve().parents[1])
