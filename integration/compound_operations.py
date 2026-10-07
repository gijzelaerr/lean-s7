"""Whole-call serialization and receive budgets for bit and string operations."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from _compat import stdout_ready
from concurrency import _handshake
from multi_batching import _ack, _receive, _request, _send
from transfer_deadlines import _delay

_BARRIERS = {
    "bit-db",
    "bit-input",
    "bit-output",
    "bit-db-clear",
    "bit-output-clear",
    "string-success",
    "wstring-success",
}

# Client test budget: 3 s. A first 1 s stage leaves 2 s of the shared budget;
# a 2.5 s second-stage window expires it, but not a fresh 3 s stage budget.
# Keep these independent peer windows explicit, rather than deriving them
# from the implementation's configured deadline.
_INITIAL_DEADLINE_DELAY = 1.0
_SECOND_DEADLINE_WINDOW = 2.5
_DEADLINE_MODES = ("string-deadline", "wstring-deadline", "bit-deadline")


def _refresh_diagnostic(mode: str) -> str:
    return (
        "bit write refreshed its receive budget"
        if mode == "bit-deadline"
        else "compound body refreshed its receive budget"
    )


def _read_reply(connection: socket.socket, request: bytes, data: bytes) -> None:
    reference = int.from_bytes(request[4:6], "big")
    _send(
        connection,
        b"\x02\xf0\x80"
        + _ack(
            reference, b"\x04\x01", struct.pack(">BBH", 255, 4, len(data) * 8) + data
        ),
    )


def _check(
    request: bytes, function: int, start: int, count: int, area: int = 0x84
) -> None:
    expected = bytes([function, 1, 0x12, 0x0A, 0x10, 2])
    expected += struct.pack(">HHB", count, int(area == 0x84), area)
    expected += (start * 8).to_bytes(3, "big")
    if request[10:24] != expected:
        raise RuntimeError("compound operation interleaved or encoded wrong range")


def _disconnect(connection: socket.socket) -> None:
    frame = _receive(connection)
    if len(frame) < 2 or frame[1] != 0x80:
        raise RuntimeError(
            "compound operation sent unexpected IO instead of disconnect"
        )


def _serve(
    listener: socket.socket,
    mode: str,
    pending: threading.Event,
    release: threading.Event,
    errors: list[Exception],
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection)
            first = _request(connection)
            barrier = mode in _BARRIERS
            if barrier:
                pending.set()
                if not release.wait(5):
                    raise RuntimeError("compound process barrier did not release")
            if mode.startswith("bit"):
                area = (
                    0x81
                    if mode.startswith("bit-input")
                    else 0x82
                    if mode.startswith("bit-output")
                    else 0x84
                )
                clearing = mode.endswith("clear")
                value = 255 if clearing else 0
                for index in range(1 if mode in ("bit-drop", "bit-deadline") else 8):
                    request = first if index == 0 else _request(connection)
                    _check(request, 4, 0, 1, area)
                    if mode == "bit-deadline" and not _delay(
                        connection, _INITIAL_DEADLINE_DELAY
                    ):
                        raise RuntimeError(
                            "bit deadline expired before its initial response"
                        )
                    _read_reply(connection, request, bytes([value]))
                    write = _request(connection)
                    _check(write, 5, 0, 1, area)
                    if len(write) != 29 or write[24:28] != b"\0\x04\0\x08":
                        raise RuntimeError("compound bit write payload mismatch")
                    updated = write[28]
                    difference = updated ^ value
                    if (
                        (
                            updated | value != value
                            if clearing
                            else updated & value != value
                        )
                        or not difference
                        or difference & (difference - 1)
                    ):
                        raise RuntimeError(
                            "compound bit update lost or changed another bit"
                        )
                    value = updated
                    if mode == "bit-deadline":
                        if _delay(connection, _SECOND_DEADLINE_WINDOW):
                            raise RuntimeError(_refresh_diagnostic(mode))
                        return
                    if mode == "bit-drop":
                        connection.shutdown(socket.SHUT_RDWR)
                        break
                    _send(
                        connection,
                        b"\x02\xf0\x80"
                        + _ack(int.from_bytes(write[4:6], "big"), b"\x05\x01", b"\xff"),
                    )
                if mode != "bit-drop":
                    final = _request(connection)
                    _check(final, 4, 0, 1, area)
                    if value != (0 if clearing else 255):
                        raise RuntimeError("compound bit updates were incomplete")
                    _read_reply(connection, final, bytes([value]))
                    _disconnect(connection)
            else:
                wide = mode.startswith("wstring")
                header_size = 4 if wide else 2
                _check(first, 4, 0, header_size)
                if mode.endswith("bad-header"):
                    header = b"\0\x01\0\x02" if wide else b"\x01\x02"
                    _read_reply(connection, first, header)
                    _disconnect(connection)
                    return
                if mode == "wstring-bad-utf16":
                    data = b"\0\x01\0\x01\xd8\0"
                else:
                    text = "PLC 🚀".encode("utf-16-be") if wide else b"lean"
                    maximum = 150 if wide else 250
                    header = (
                        struct.pack(">HH", maximum, len(text) // 2)
                        if wide
                        else bytes([maximum, len(text)])
                    )
                    data = (
                        header + text + bytes(maximum * (2 if wide else 1) - len(text))
                    )
                if mode.endswith("deadline") and not _delay(
                    connection, _INITIAL_DEADLINE_DELAY
                ):
                    raise RuntimeError("compound timed out before valid first response")
                _read_reply(connection, first, data[:header_size])
                if mode.endswith(("capacity-shrink", "capacity-grow")):
                    changed = maximum + (-1 if mode.endswith("shrink") else 1)
                    data = (
                        struct.pack(">H", changed) + data[2:]
                        if wide
                        else bytes([changed]) + data[1:]
                    )
                elif mode.endswith("length-update"):
                    text = "updated 🌍".encode("utf-16-be") if wide else b"updated"
                    header = (
                        struct.pack(">HH", maximum, len(text) // 2)
                        if wide
                        else bytes([maximum, len(text)])
                    )
                    data = (
                        header + text + bytes(maximum * (2 if wide else 1) - len(text))
                    )
                for offset in range(0, len(data), 222):
                    request = _request(connection)
                    count = min(222, len(data) - offset)
                    _check(request, 4, offset, count)
                    if mode.endswith("deadline"):
                        if _delay(connection, _SECOND_DEADLINE_WINDOW):
                            raise RuntimeError(_refresh_diagnostic(mode))
                        return
                    _read_reply(connection, request, data[offset : offset + count])
                if barrier:
                    competing = _request(connection)
                    _check(competing, 5, 2000, 1)
                    if competing[24:] != b"\0\x04\0\x08\x63":
                        raise RuntimeError("competing compound test write mismatch")
                    _send(
                        connection,
                        b"\x02\xf0\x80"
                        + _ack(
                            int.from_bytes(competing[4:6], "big"), b"\x05\x01", b"\xff"
                        ),
                    )
                _disconnect(connection)
        if mode == "bit-drop":
            listener.settimeout(0.6)
            try:
                unexpected, _ = listener.accept()
            except TimeoutError:
                return
            unexpected.close()
            raise RuntimeError("compound write reconnected after completed read")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)
        pending.set()


def run_compound_operations(root: Path, deadline_rounds: int = 2) -> None:
    if not 1 <= deadline_rounds <= 10:
        raise ValueError("compound deadline rounds must be between 1 and 10")
    modes = (
        "bit-db",
        "bit-input",
        "bit-output",
        "bit-db-clear",
        "bit-output-clear",
        "string-success",
        "wstring-success",
        "string-bad-header",
        "wstring-bad-header",
        "wstring-bad-utf16",
        "string-capacity-shrink",
        "wstring-capacity-shrink",
        "string-capacity-grow",
        "wstring-capacity-grow",
        "string-length-update",
        "wstring-length-update",
        "string-deadline",
        "wstring-deadline",
        "bit-drop",
        "bit-deadline",
    )
    cases = [(mode, False) for mode in modes]
    cases += [
        (mode, False) for _ in range(deadline_rounds - 1) for mode in _DEADLINE_MODES
    ]
    cases += [(mode, True) for mode in _DEADLINE_MODES]
    for mode, fresh_budget_control in cases:
        errors: list[Exception] = []
        pending, release = threading.Event(), threading.Event()
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(2)
            listener.settimeout(5)
            worker = threading.Thread(
                target=_serve, args=(listener, mode, pending, release, errors)
            )
            worker.start()
            process = subprocess.Popen(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-compound-fresh-budget"
                    if fresh_budget_control
                    else "integration-compound",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    mode,
                ],
                cwd=root,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                if mode in _BARRIERS:
                    if not pending.wait(5) or errors:
                        raise RuntimeError(f"compound did not reach barrier: {errors}")
                    assert process.stdin is not None and process.stdout is not None
                    process.stdin.write("launch\n")
                    process.stdin.flush()
                    if (
                        not stdout_ready(process.stdout, 5)
                        or process.stdout.readline().strip()
                        != "compound calls launched"
                    ):
                        raise RuntimeError("compound competing task barrier failed")
                    release.set()
                stdout, stderr = process.communicate(timeout=12)
                if process.returncode and not fresh_budget_control:
                    raise RuntimeError(f"compound {mode} failed: {stdout}{stderr}")
                if not fresh_budget_control:
                    print(stdout.strip())
            finally:
                release.set()
                if process.poll() is None:
                    process.kill()
                    process.communicate()
                worker.join(timeout=6)
            if worker.is_alive():
                raise RuntimeError("compound peer did not finish")
            if fresh_budget_control:
                # A crash, an earlier timeout, or a malformed request is not
                # evidence that the oracle detects budget refresh. Require
                # its precise second-stage diagnostic and client failure.
                if (
                    process.returncode == 0
                    or len(errors) != 1
                    or str(errors[0]) != _refresh_diagnostic(mode)
                ):
                    raise RuntimeError(
                        f"fresh-budget mutation missed its diagnostic: {mode}; "
                        f"errors={errors}; client={stdout}{stderr}"
                    )
                print(f"compound fresh-budget mutation rejected: {mode}")
            elif errors:
                raise errors[0]
    print(
        f"compound peers passed: {len(modes)} scenarios, "
        f"{deadline_rounds} deadline rounds, 3 fresh-budget negative controls"
    )
