"""Measured same-process reconnect stress on Linux /proc and Darwin libproc.

Plateau bounds catch material accumulation; they are not proof of leak freedom.
"""

from __future__ import annotations

import argparse
import ctypes
import os
import socket
import subprocess
import sys
import threading
from dataclasses import dataclass
from pathlib import Path

from _compat import stdout_ready
from multi_batching import _ack, _receive, _request, _send


@dataclass(frozen=True)
class Sample:
    descriptors: int
    threads: int
    rss_bytes: int


class _TaskInfo(ctypes.Structure):
    _fields_ = [
        (name, ctypes.c_uint64)
        for name in (
            "virtual_size",
            "resident_size",
            "total_user",
            "total_system",
            "threads_user",
            "threads_system",
        )
    ] + [
        (name, ctypes.c_int32)
        for name in (
            "policy",
            "faults",
            "pageins",
            "cow_faults",
            "messages_sent",
            "messages_received",
            "syscalls_mach",
            "syscalls_unix",
            "csw",
            "threadnum",
            "numrunning",
            "priority",
        )
    ]


def sample_process(pid: int) -> Sample:
    if sys.platform.startswith("linux"):
        status = dict(
            line.split(":", 1)
            for line in Path(f"/proc/{pid}/status")
            .read_text(encoding="utf-8")
            .splitlines()
        )
        return Sample(
            len(os.listdir(f"/proc/{pid}/fd")),
            int(status["Threads"]),
            int(status["VmRSS"].split()[0]) * 1024,
        )
    if sys.platform == "darwin":
        library = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
        info = library.proc_pidinfo
        info.argtypes = [
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_uint64,
            ctypes.c_void_p,
            ctypes.c_int,
        ]
        info.restype = ctypes.c_int
        task = _TaskInfo()
        if info(pid, 4, 0, ctypes.byref(task), ctypes.sizeof(task)) != ctypes.sizeof(
            task
        ):
            raise OSError(ctypes.get_errno(), "could not read child task metrics")
        capacity = info(pid, 1, 0, None, 0)
        if capacity <= 0:
            raise OSError(ctypes.get_errno(), "could not size child descriptor metrics")
        buffer = ctypes.create_string_buffer(capacity + 4096)
        used = info(pid, 1, 0, buffer, len(buffer))
        if used <= 0 or used % 8:
            raise OSError(ctypes.get_errno(), "could not read child descriptor metrics")
        return Sample(used // 8, task.threadnum, task.resident_size)
    raise RuntimeError(f"resource stress metrics unsupported on {sys.platform}")


def check_plateau(samples: list[Sample]) -> None:
    if len(samples) != 17:
        raise RuntimeError("resource stress sample count changed")
    baseline = samples[0]
    limits = {"descriptors": 8, "threads": 16, "rss_bytes": 32 * 1024 * 1024}
    for field, margin in limits.items():
        growth = max(getattr(sample, field) for sample in samples[1:]) - getattr(
            baseline, field
        )
        if growth > margin:
            raise RuntimeError(
                f"resource accumulation: {field} grew {growth}, limit {margin}; {samples}"
            )


def _test_plateau_checker() -> None:
    baseline = Sample(10, 4, 8 * 1024 * 1024)
    check_plateau([baseline] * 17)
    check_plateau([baseline] + [Sample(18, 20, 40 * 1024 * 1024)] * 16)
    for field, leaking in (
        ("descriptors", Sample(19, 4, baseline.rss_bytes)),
        ("threads", Sample(10, 21, baseline.rss_bytes)),
        ("rss_bytes", Sample(10, 4, baseline.rss_bytes + 32 * 1024 * 1024 + 1)),
    ):
        try:
            check_plateau([baseline] * 16 + [leaking])
        except RuntimeError as error:
            if not str(error).startswith(f"resource accumulation: {field} grew "):
                raise RuntimeError(
                    "plateau checker reported the wrong metric"
                ) from error
        else:
            raise RuntimeError(f"plateau checker missed synthetic {field} accumulation")
    try:
        check_plateau([baseline] * 16)
    except RuntimeError:
        pass
    else:
        raise RuntimeError("plateau checker accepted missing measurements")


def _closed(connection: socket.socket) -> None:
    try:
        if connection.recv(1):
            raise RuntimeError("stress failure continued handshake")
    except ConnectionResetError:
        pass


def _accept(listener: socket.socket) -> socket.socket:
    connection, _ = listener.accept()
    connection.settimeout(3)
    return connection


def _setup(connection: socket.socket, cr: bytes) -> None:
    _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
    setup = _request(connection)
    _send(
        connection,
        b"\x02\xf0\x80"
        + _ack(int.from_bytes(setup[4:6], "big"), b"\xf0\0\0\x01\0\x01\0\xf0"),
    )


def _read(connection: socket.socket) -> bytes:
    request = _request(connection)
    if request[10:12] != b"\x04\x01" or request[16:18] != b"\0\x01":
        raise RuntimeError("stress peer expected one-byte read")
    return request


def _reply_and_disconnect(connection: socket.socket, request: bytes) -> None:
    _send(
        connection,
        b"\x02\xf0\x80"
        + _ack(int.from_bytes(request[4:6], "big"), b"\x04\x01", b"\xff\x04\0\x08\x2a"),
    )
    frame = _receive(connection)
    if len(frame) < 2 or frame[1] != 0x80:
        raise RuntimeError("stress successful session omitted disconnect")


def _serve(listener: socket.socket, errors: list[Exception], rounds: int) -> None:
    try:
        for index in range(216 * rounds):
            mode = index % 4
            with _accept(listener) as connection:
                cr = _receive(connection)
                if mode == 1:
                    _send(connection, b"\x01\xd0")
                    _closed(connection)
                elif mode == 2:
                    _closed(connection)
                else:
                    _setup(connection, cr)
                    request = _read(connection)
                    if mode == 0:
                        connection.shutdown(socket.SHUT_RDWR)
                    else:
                        _reply_and_disconnect(connection, request)
            if mode == 0:
                with _accept(listener) as replacement:
                    _setup(replacement, _receive(replacement))
                    replay = _read(replacement)
                    if replay != request:
                        raise RuntimeError("stress reconnect changed read request")
                    _reply_and_disconnect(replacement, replay)
    except (OSError, RuntimeError, ValueError, IndexError) as error:
        errors.append(error)


def run_resource_stress(root: Path, rounds: int = 1) -> None:
    if not 1 <= rounds <= 1000:
        raise ValueError("stress rounds must be between 1 and 1000")
    if sys.platform == "win32":
        # Descriptor/thread/RSS sampling is implemented for Linux (/proc) and macOS
        # (libproc) only; do not claim a resource-leak result on Windows.
        print("resource stress skipped: process metrics unsupported on win32")
        return
    _test_plateau_checker()
    samples: list[Sample] = []
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(8)
        listener.settimeout(5)
        worker = threading.Thread(target=_serve, args=(listener, errors, rounds))
        worker.start()
        process = subprocess.Popen(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-resource-stress",
                "127.0.0.1",
                str(listener.getsockname()[1]),
                str(rounds),
            ],
            cwd=root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env={**os.environ, "LEAN_NUM_THREADS": "2"},
        )
        try:
            assert process.stdout is not None and process.stdin is not None
            for index in range(17):
                if not stdout_ready(process.stdout, 8 * rounds):
                    raise RuntimeError(
                        f"resource stress sample stalled; peer errors: {errors}"
                    )
                line = process.stdout.readline().strip()
                if line != f"resource sample {index}":
                    raise RuntimeError(
                        f"resource stress barrier changed: {line}; peer errors: {errors}"
                    )
                samples.append(sample_process(process.pid))
                process.stdin.write("continue\n")
                process.stdin.flush()
            stdout, stderr = process.communicate(timeout=8)
            if process.returncode or "resource stress passed" not in stdout:
                raise RuntimeError(f"resource stress native failure: {stdout}{stderr}")
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()
            worker.join(timeout=6)
        if worker.is_alive():
            raise RuntimeError("resource stress peer did not finish")
        if errors:
            raise errors[0]
    check_plateau(samples)
    peak = Sample(
        *(
            max(getattr(sample, field) for sample in samples)
            for field in ("descriptors", "threads", "rss_bytes")
        )
    )
    print(
        f"resource stress passed: {216 * rounds} attempts/{54 * rounds} retry reconnects; "
        f"baseline={samples[0]}, peak={peak}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rounds", type=int, default=1, help="multiply same-process soak length"
    )
    run_resource_stress(Path(__file__).resolve().parents[1], parser.parse_args().rounds)
