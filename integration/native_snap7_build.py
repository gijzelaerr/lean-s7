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


def _msvc_environment_script() -> Path:
    """Locate vcvars64.bat of a Visual Studio with the C++ x64 tools."""
    installer = Path(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"))
    vswhere = installer / "Microsoft Visual Studio" / "Installer" / "vswhere.exe"
    if not vswhere.exists():
        raise RuntimeError(
            "native endpoint testing on Windows requires Visual Studio C++ tools"
        )
    found = subprocess.run(
        [
            str(vswhere),
            "-latest",
            "-products",
            "*",
            "-requires",
            "Microsoft.VisualStudio.Component.VC.Tools.x86.x64",
            "-property",
            "installationPath",
        ],
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    ).stdout.strip()
    script = Path(found) / "VC" / "Auxiliary" / "Build" / "vcvars64.bat"
    if not found or not script.exists():
        raise RuntimeError(
            "native endpoint testing on Windows requires Visual Studio C++ tools"
        )
    return script


def build(root: Path) -> Path:
    system = platform.system()
    if system not in ("Linux", "Darwin", "Windows"):
        raise ValueError(
            "native endpoint builder supports Linux, macOS and Windows only"
        )
    if system == "Windows":
        compiler = str(_msvc_environment_script())
    else:
        found_compiler = shutil.which(os.environ.get("CXX", "c++"))
        if found_compiler is None:
            raise RuntimeError("native endpoint testing requires a C++ compiler")
        compiler = found_compiler
    destination = root / ".lake" / "native-snap7"
    destination.mkdir(parents=True, exist_ok=True)
    library = destination / {
        "Darwin": "libsnap7.dylib",
        "Windows": "snap7.dll",
    }.get(system, "libsnap7.so")
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
        temporary_library = staging / library.name
        if system == "Windows":
            files = " ".join(f"src/{name}" for name in SOURCES)
            script = staging / "build.bat"
            script.write_text(
                f'@call "{compiler}" >nul || exit /b 1\r\n'
                f"@cl /nologo /LD /EHsc /O2 /I src/sys /I src/core /I src/lib {files} "
                f'/Fe:"{temporary_library}" /link ws2_32.lib winmm.lib /DEF:src/lib/snap7.def\r\n',
                encoding="ascii",
            )
            invocation: list[str] = ["cmd", "/c", str(script)]
        else:
            invocation = [compiler, "-std=c++11", "-O2", "-fPIC", "-pthread"]
            invocation += ["-dynamiclib" if system == "Darwin" else "-shared"]
            invocation += ["-I", "src/sys", "-I", "src/core", "-I", "src/lib"]
            invocation += [f"src/{name}" for name in SOURCES]
            invocation += ["-o", str(temporary_library)]
        compilation = subprocess.run(
            invocation,
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
