"""Independent native Snap7 endpoint and complete backing-memory oracle."""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import os
import socket
import subprocess
from pathlib import Path

from native_snap7_build import ARCHIVE_SHA256, REVISION


def _bind(library: Path) -> ctypes.CDLL:
    api = ctypes.CDLL(str(library.resolve()))
    handle = ctypes.c_size_t
    signatures = {
        "Srv_Create": ([], handle),
        "Srv_Destroy": ([ctypes.POINTER(handle)], None),
        "Srv_SetParam": ([handle, ctypes.c_int, ctypes.c_void_p], ctypes.c_int),
        "Srv_SetCpuStatus": ([handle, ctypes.c_int], ctypes.c_int),
        "Srv_RegisterArea": (
            [handle, ctypes.c_int, ctypes.c_uint16, ctypes.c_void_p, ctypes.c_int],
            ctypes.c_int,
        ),
        "Srv_StartTo": ([handle, ctypes.c_char_p], ctypes.c_int),
        "Srv_Stop": ([handle], ctypes.c_int),
    }
    for name, (arguments, result) in signatures.items():
        function = getattr(api, name)
        function.argtypes, function.restype = arguments, result
    return api


def _check(code: int, label: str) -> None:
    if code:
        raise RuntimeError(f"native Snap7 {label}: 0x{code:08x}")


def _verify(buffers: dict, expected: dict) -> None:
    if buffers.keys() != expected.keys():
        raise AssertionError("native backing buffer identities differ")
    for key, contents in expected.items():
        actual = bytes(buffers[key])
        if actual != contents:
            raise AssertionError(f"native backing memory {key} differs")


def _self_test() -> None:
    expected = _expected()
    if len(expected) != 5 or sum(map(len, expected.values())) != 9728:
        raise AssertionError("native fixture extents changed")
    _verify(expected, expected)
    for key in expected:
        mutated = {name: bytearray(contents) for name, contents in expected.items()}
        mutated[key][-1] ^= 1
        try:
            _verify(mutated, expected)
        except AssertionError:
            continue
        raise AssertionError(
            "native memory oracle accepted a surrounding-byte mutation"
        )
    for changed in ({}, {**expected, (5, 999): b""}):
        try:
            _verify(changed, expected)
        except AssertionError:
            continue
        raise AssertionError(
            "native memory oracle accepted missing/extra buffer identity"
        )


def _expected() -> dict[tuple[int, int], bytearray]:
    expected = {
        (5, db): bytearray((db * 3 + index * 17 + 3) & 255 for index in range(4096))
        for db in (1, 2)
    }
    expected[(5, 1)][1275:2676] = bytes(
        (index * 37 + 11) & 255 for index in range(1401)
    )
    expected[(5, 1)][64:74] = b"\x08\x03\xe9S7" + b"\0" * 5
    expected[(5, 1)][128:148] = b"\0\x08\0\x04" + "A🌍é".encode("utf-16-be") + b"\0" * 8
    expected[(5, 1)][200] |= 8
    for index in range(40):
        start = 512 + index * 7
        expected[(5, 2)][start : start + 3] = bytes(
            (index, index * 11 & 255, 255 - index)
        )
    for area in (0, 1, 2):
        expected[(area, 0)] = bytearray(
            (area * 31 + index * 13) & 255 for index in range(512)
        )
        expected[(area, 0)][33:344] = bytes(
            (index * 37 + 11) & 255 for index in range(311)
        )
    return expected


def run(root: Path, library: Path) -> dict:
    _self_test()
    provenance = json.loads(
        library.with_suffix(library.suffix + ".json").read_text(encoding="utf-8")
    )
    fingerprint = hashlib.sha256(library.read_bytes()).hexdigest()
    if (
        provenance.get("repository") != "davenardella/snap7"
        or provenance.get("revision") != REVISION
        or provenance.get("archive_sha256") != ARCHIVE_SHA256
        or provenance.get("library_sha256") != fingerprint
    ):
        raise ValueError(
            "native build provenance/digest does not match the pinned endpoint"
        )
    api = _bind(library)
    observations = []
    for pdu in (240, 480):
        server = ctypes.c_size_t(api.Srv_Create())
        if not server.value:
            raise RuntimeError("native server allocation failed")
        buffers = {}
        try:
            with socket.socket() as reservation:
                reservation.bind(("127.0.0.1", 0))
                port = ctypes.c_uint16(reservation.getsockname()[1])
            _check(api.Srv_SetParam(server, 1, ctypes.byref(port)), "local port")
            pdu_parameter = ctypes.c_int32(pdu)
            _check(
                api.Srv_SetParam(server, 10, ctypes.byref(pdu_parameter)),
                "forced test PDU",
            )
            _check(api.Srv_SetCpuStatus(server, 8), "fixture RUN state")
            initial = {
                (5, db): bytes((db * 3 + index * 17 + 3) & 255 for index in range(4096))
                for db in (1, 2)
            }
            initial.update(
                {
                    (area, 0): bytes(
                        (area * 31 + index * 13) & 255 for index in range(512)
                    )
                    for area in (0, 1, 2)
                }
            )
            for key, contents in initial.items():
                buffer = (ctypes.c_ubyte * len(contents)).from_buffer_copy(contents)
                buffers[key] = buffer  # Native registration borrows this storage.
                _check(
                    api.Srv_RegisterArea(server, *key, buffer, len(buffer)),
                    f"register {key}",
                )
            _check(api.Srv_StartTo(server, b"127.0.0.1"), "start localhost")
            result = subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-native",
                    "127.0.0.1",
                    str(port.value),
                    str(pdu),
                ],
                cwd=root,
                capture_output=True,
                text=True,
                timeout=45,
                check=False,
            )
            if (
                result.returncode
                or result.stdout.strip()
                != f"native endpoint client checks passed: PDU={pdu}"
            ):
                raise RuntimeError(
                    f"native PDU{pdu} client failed:\n{result.stdout}\n{result.stderr}"
                )
            _check(api.Srv_Stop(server), "stop")
            _verify(buffers, _expected())
            observations.append(
                {
                    "pdu": pdu,
                    "buffers_checked": len(buffers),
                    "bytes_checked": sum(map(len, buffers.values())),
                }
            )
            print(result.stdout.strip())
        finally:
            # Stop/destroy before allowing borrowed buffers to leave scope.
            api.Srv_Stop(server)
            api.Srv_Destroy(ctypes.byref(server))
    return {
        "endpoint": "official native Snap7 server",
        "revision": REVISION,
        "library_sha256": fingerprint,
        "source_archive_sha256": ARCHIVE_SHA256,
        "platform": provenance["platform"],
        "machine": provenance["machine"],
        "profiles": observations,
        "scope": "localhost buffers, classic reads/writes/metadata/CPU-state query; not PLC qualification",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--library", type=Path, default=os.environ.get("LEAN_S7_NATIVE_LIBRARY")
    )
    arguments = parser.parse_args()
    if arguments.library is None:
        parser.error(
            "provide --library or LEAN_S7_NATIVE_LIBRARY from native_snap7_build.py"
        )
    print(
        json.dumps(
            run(Path(__file__).resolve().parents[1], arguments.library), sort_keys=True
        )
    )
