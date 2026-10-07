"""Verified localhost scalability measurements, without timing pass/fail gates.

Includes Python peer/network costs; not a PLC benchmark or complexity proof.
RSS is sampled after operations, not a guaranteed peak or allocation count.
"""

from __future__ import annotations

import argparse
import json
import platform
import socket
import statistics
import struct
import subprocess
import sys
import threading
from pathlib import Path

from boundary_operations import _closed, _handshake
from multi_batching import _ack, _request, _send
from resource_stress import sample_process


def _data(start: int, count: int) -> bytes:
    return bytes(((start + index) * 37 + 11) % 256 for index in range(count))


def _serve(
    listener: socket.socket,
    pdu: int,
    mode: str,
    size: int,
    rounds: int,
    errors: list[Exception],
    counts: list[int],
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection, pdu)
            packets = 0
            for _ in range(rounds + 1):
                completed = 0
                while completed < size:
                    request = _request(connection)
                    if len(request) > pdu or request[:4] != b"\x32\x01\0\0":
                        raise RuntimeError("benchmark request framing/budget mismatch")
                    reference, parameter_size, data_size = struct.unpack_from(
                        ">HHH", request, 4
                    )
                    function, item_count = request[10:12]
                    write = mode == "multi-write"
                    count = (
                        min(size - completed, pdu - 18)
                        if mode == "read"
                        else min(
                            20,
                            size - completed,
                            (pdu - 12) // 18
                            if write
                            else min((pdu - 12) // 12, (pdu - 14) // 6),
                        )
                    )
                    expected_items = 1 if mode == "read" else count
                    if (
                        function != (5 if write else 4)
                        or item_count != expected_items
                        or parameter_size != 2 + 12 * expected_items
                        or len(request) != 10 + parameter_size + data_size
                    ):
                        raise RuntimeError("benchmark item count/section mismatch")
                    expected_parameters = bytes([function, item_count])
                    expected_data, reply = bytearray(), bytearray()
                    for offset in range(expected_items):
                        start = (
                            completed if mode == "read" else (completed + offset) * 2
                        )
                        length = count if mode == "read" else 1
                        expected_parameters += (
                            b"\x12\x0a\x10\x02"
                            + struct.pack(">HHB", length, 1, 0x84)
                            + (start * 8).to_bytes(3, "big")
                        )
                        data = _data(start, length)
                        if write:
                            expected_data.extend(
                                b"\0\x04" + struct.pack(">H", length * 8) + data
                            )
                            reply.append(255)
                            if offset + 1 < expected_items:
                                expected_data.append(0)
                        else:
                            reply.extend(
                                b"\xff\x04" + struct.pack(">H", length * 8) + data
                            )
                            if offset + 1 < expected_items and length % 2:
                                reply.append(0)
                    if (
                        request[10 : 10 + parameter_size] != expected_parameters
                        or request[10 + parameter_size :] != expected_data
                    ):
                        raise RuntimeError("benchmark reordered/corrupted request")
                    response = _ack(
                        reference, bytes([function, item_count]), bytes(reply)
                    )
                    if len(response) > pdu:
                        raise RuntimeError("benchmark response exceeded PDU")
                    _send(connection, b"\x02\xf0\x80" + response)
                    completed += count
                    packets += 1
            _closed(connection)
            counts.append(packets)
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)


def measure(root: Path, pdu: int, mode: str, size: int, rounds: int) -> dict:
    errors: list[Exception] = []
    counts: list[int] = []
    samples, resident = [], []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        listener.settimeout(5)
        worker = threading.Thread(
            target=_serve, args=(listener, pdu, mode, size, rounds, errors, counts)
        )
        worker.start()
        process = subprocess.Popen(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "benchmark-scalability",
                "127.0.0.1",
                str(listener.getsockname()[1]),
                mode,
                str(size),
                str(rounds),
            ],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        watchdog = threading.Timer(60, process.kill)
        watchdog.start()
        try:
            assert process.stdout is not None
            for line in process.stdout:
                fields = line.split()
                if fields[:2] != ["benchmark", "sample"] or len(fields) != 3:
                    raise RuntimeError(f"unexpected benchmark output: {line}")
                samples.append(int(fields[2]))
                try:
                    resident.append(sample_process(process.pid).rss_bytes)
                except (OSError, FileNotFoundError):
                    pass  # The child may exit before the final post-operation sample.
            _, stderr = process.communicate(timeout=5)
            if process.returncode or len(samples) != rounds:
                raise RuntimeError(f"benchmark failed: {stderr}")
        finally:
            watchdog.cancel()
            if process.poll() is None:
                process.kill()
                process.communicate()
            worker.join(timeout=6)
        if worker.is_alive():
            raise RuntimeError("benchmark peer did not terminate")
        if errors:
            raise errors[0]
    return {
        "pdu_bytes": pdu,
        "operation": mode,
        "size": size,
        "size_unit": "bytes" if mode == "read" else "caller_items",
        "samples_ns": samples,
        "median_ns": int(statistics.median(samples)),
        "post_operation_rss_bytes": resident,
        "exchanges_including_warmup": counts[0],
    }


def run(rounds: int = 3, smoke: bool = False) -> dict:
    if sys.platform == "win32":
        print(
            "scalability benchmark skipped: process memory sampling unsupported on win32"
        )
        return {"schema_version": 1, "skipped": "win32", "cases": []}
    root = Path(__file__).resolve().parents[1]
    cases = []
    for pdu in (240, 480):
        for mode in ("read", "multi-read", "multi-write"):
            sizes = (
                (1024,)
                if smoke and mode == "read"
                else (32,)
                if smoke
                else (16384, 65536, 262144)
                if mode == "read"
                else (128, 512, 2048)
            )
            for size in sizes:
                result = measure(root, pdu, mode, size, rounds)
                cases.append(result)
    return {
        "schema_version": 1,
        "platform": platform.platform(),
        "rounds": rounds,
        "timing_scope": "public operation, excluding handshake/warmup/verification; includes localhost peer/network costs",
        "cases": cases,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rounds", type=int, choices=range(1, 17), default=3)
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()
    print(json.dumps(run(args.rounds, args.smoke), indent=2))
