"""Seeded, parameter-aware wire conversations around negotiated size boundaries."""

from __future__ import annotations

import random
import socket
import struct
import subprocess
import threading
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from mixed_operations import minimize
from multi_batching import _ack, _receive, _request, _send


@dataclass(frozen=True)
class Operation:
    identifier: int
    kind: str
    size: int

    def token(self) -> str:
        return f"{self.identifier}:{self.kind}:{self.size}"


def generate(seed: int, pdu: int, terminal: str) -> tuple[Operation, ...]:
    """Mandatory boundary coverage, seed-shuffled ordering, and stable IDs."""
    read, write = pdu - 18, pdu - 28
    specifications = [
        (kind, size)
        for kind, maximum in (("r", read), ("w", write))
        for size in (0, 1, maximum - 1, maximum, maximum + 1, 2 * maximum + 1)
    ]
    capacities = sorted(
        {0, 1, 2, min(254, read - 3), min(254, read - 2), min(254, read - 1), 254}
    )
    specifications += [(kind, size) for kind in ("s", "S") for size in capacities]
    wide_capacities = sorted(
        {0, 1, 2, (read - 4) // 2, (read - 4) // 2 + 1, read // 2 + 1}
    )
    specifications += [(kind, size) for kind in ("t", "T") for size in wide_capacities]
    # R drops the first chunk, then checks replay and remaining chunk coverage.
    specifications += [("R", read + 1), ("j", read), ("r", read + 1)]
    operations = [
        Operation(index + 1, *spec) for index, spec in enumerate(specifications)
    ]
    random.Random(seed).shuffle(operations)
    terminal_size = (
        1 if terminal == "u" else min(254, write) if terminal == "q" else write
    )
    operations.append(Operation(len(operations) + 1, terminal, terminal_size))
    return tuple(operations)


def encode(operations: tuple[Operation, ...]) -> str:
    return "|".join(operation.token() for operation in operations)


def decode(plan: str) -> tuple[Operation, ...]:
    if not plan:
        return ()
    result = []
    for token in plan.split("|"):
        identifier, kind, size = token.split(":")
        result.append(Operation(int(identifier), kind, int(size)))
    return tuple(result)


def reduce_plan(
    operations: tuple[Operation, ...],
    fails: Callable[[tuple[Operation, ...]], bool],
    budget: int = 12,
) -> tuple[Operation, ...]:
    """Reuse the bounded reducer on opaque IDs, never tokenize numeric fields.

    Unlike deleting characters from the wire plan, deleting one mapped character
    removes exactly one complete operation and preserves every retained parameter.
    """
    mapping = {
        chr(0x100 + index): operation for index, operation in enumerate(operations)
    }
    reduced = minimize(
        "".join(mapping),
        lambda candidate: fails(tuple(mapping[key] for key in candidate)),
        budget=budget,
    )
    return tuple(mapping[key] for key in reduced)


def _check_generator() -> None:
    for pdu in (240, 480):
        for seed, terminal in zip(
            (7, 2026, 65535, 0x5A17), ("q", "u", "z", "d"), strict=True
        ):
            operations = generate(seed, pdu, terminal)
            if (
                operations != generate(seed, pdu, terminal)
                or decode(encode(operations)) != operations
            ):
                raise RuntimeError(
                    "boundary generator is not deterministically replayable"
                )
            for kind, maximum in (("r", pdu - 18), ("w", pdu - 28)):
                covered = {op.size for op in operations if op.kind == kind}
                if (
                    not {0, 1, maximum - 1, maximum, maximum + 1, 2 * maximum + 1}
                    <= covered
                ):
                    raise RuntimeError(
                        "boundary generator lost mandatory chunk coverage"
                    )
            read = pdu - 18
            for kind in ("s", "S"):
                covered = {op.size for op in operations if op.kind == kind}
                expected = {
                    0,
                    1,
                    2,
                    min(254, read - 3),
                    min(254, read - 2),
                    min(254, read - 1),
                    254,
                }
                if covered != expected:
                    raise RuntimeError(
                        "boundary generator lost mandatory STRING capacity coverage"
                    )
            for kind in ("t", "T"):
                covered = {op.size for op in operations if op.kind == kind}
                expected = {
                    0,
                    1,
                    2,
                    (read - 4) // 2,
                    (read - 4) // 2 + 1,
                    read // 2 + 1,
                }
                if covered != expected:
                    raise RuntimeError(
                        "boundary generator lost mandatory UTF16 capacity coverage"
                    )
            if sum(op.kind == "R" and op.size == read + 1 for op in operations) != 1:
                raise RuntimeError(
                    "boundary generator lost mandatory chunked-read retry"
                )
            if sum(op.kind == "j" and op.size == read for op in operations) != 1:
                raise RuntimeError(
                    "boundary generator lost mandatory recoverable PLC rejection"
                )
            terminal_size = (
                1
                if terminal == "u"
                else min(254, pdu - 28)
                if terminal == "q"
                else pdu - 28
            )
            if (
                operations[-1].kind != terminal
                or operations[-1].size != terminal_size
                or sum(op.kind in "quzd" for op in operations) != 1
            ):
                raise RuntimeError(
                    "boundary generator lost its sole final terminal parser/write check"
                )
            required = tuple(op for op in operations if op.kind in ("R", terminal))
            reduced = reduce_plan(
                operations,
                lambda candidate, required=required: all(
                    op in candidate for op in required
                ),
                budget=200,
            )
            if reduced != required:
                raise RuntimeError(
                    "boundary reducer mutated operation parameters or stable IDs"
                )


def _handshake(connection: socket.socket, pdu: int) -> None:
    connection.settimeout(4)
    cr = _receive(connection)
    _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
    setup = _request(connection)
    if setup[10:] != b"\xf0\0\0\x01\0\x01\x01\xe0":
        raise RuntimeError("boundary client requested unexpected PDU")
    _send(
        connection,
        b"\x02\xf0\x80"
        + _ack(
            int.from_bytes(setup[4:6], "big"), setup[10:16] + struct.pack(">H", pdu)
        ),
    )


def _accept(listener: socket.socket, pdu: int) -> socket.socket:
    connection, _ = listener.accept()
    try:
        _handshake(connection, pdu)
    except Exception:
        connection.close()
        raise
    return connection


def _payload(operation: Operation) -> bytes:
    if operation.kind in "sSq":
        return bytes([operation.size, operation.size]) + b"\xe9" * operation.size
    if operation.kind in "tTu":
        text = ("x" if operation.size % 2 else "") + "🌍" * (operation.size // 2)
        return struct.pack(">HH", operation.size, operation.size) + text.encode(
            "utf-16-be"
        )
    return bytes(
        (operation.identifier * 19 + index * 37) % 256
        for index in range(operation.size)
    )


def _check_request(
    request: bytes,
    operation: Operation,
    write: bool,
    offset: int,
    count: int,
    pdu: int,
    payload: bytes,
) -> int:
    parameters = b"\x05\x01" if write else b"\x04\x01"
    parameters += b"\x12\x0a\x10\x02" + struct.pack(">HH", count, 1) + b"\x84"
    parameters += ((operation.identifier * 4096 + offset) * 8).to_bytes(3, "big")
    data = (
        b"\0\x04" + struct.pack(">H", count * 8) + payload[offset : offset + count]
        if write
        else b""
    )
    expected = (
        struct.pack(">BBHHHH", 0x32, 1, 0, 0, len(parameters), len(data))
        + parameters
        + data
    )
    if len(request) > pdu or request[:4] != expected[:4] or request[6:] != expected[6:]:
        raise RuntimeError(
            f"boundary wire mismatch {operation.token()} offset={offset} count={count} PDU={pdu}"
        )
    return int.from_bytes(request[4:6], "big")


def _closed(connection: socket.socket) -> None:
    # Only a clean EOF/reset before any byte, or one complete expected COTP DR,
    # is cleanup. Partial frames are forbidden traffic, never proof of closure.
    try:
        first = connection.recv(1)
    except ConnectionResetError:
        return
    if not first:
        return
    expected = b"\x03\0\0\x0b\x06\x80\0\x01\0\x01\0"
    received = bytearray(first)
    while len(received) < len(expected):
        try:
            chunk = connection.recv(len(expected) - len(received))
        except ConnectionResetError as error:
            raise RuntimeError(
                "boundary terminal failure reset after partial traffic"
            ) from error
        if not chunk:
            raise RuntimeError("boundary terminal failure closed after partial traffic")
        received.extend(chunk)
    if received != expected:
        raise RuntimeError("boundary terminal failure allowed later IO")
    try:
        remaining = connection.recv(1)
    except ConnectionResetError:
        remaining = b""
    if remaining:
        raise RuntimeError("boundary terminal failure sent IO after disconnect")


def _check_closed() -> None:
    expected = b"\x03\0\0\x0b\x06\x80\0\x01\0\x01\0"
    cases = [(b"", True), (expected, True)]
    cases += [(expected[:length], False) for length in range(1, len(expected))]
    cases += [
        (expected + b"\x03", False),
        (expected[:-1] + b"\x01", False),
        (b"\x03\0\0\x0b\x06\x80\0\x02\0\x01\0", False),
    ]
    for data, accepted in cases:
        sender, receiver = socket.socketpair()
        with sender, receiver:
            receiver.settimeout(1)
            sender.sendall(data)
            sender.shutdown(socket.SHUT_WR)
            try:
                _closed(receiver)
                observed = True
            except RuntimeError:
                observed = False
            if observed != accepted:
                raise RuntimeError(
                    f"boundary closure checker misclassified {data.hex()}"
                )


def _serve(
    listener: socket.socket,
    pdu: int,
    operations: tuple[Operation, ...],
    errors: list[str],
) -> None:
    connection = None
    try:
        connection = _accept(listener, pdu)
        for operation in operations:
            payload = _payload(operation)
            write = operation.kind in "wSTd"
            segments = [len(payload)]
            if operation.kind in "stqu":
                segments = [4 if operation.kind in "tu" else 2, len(payload)]
            for phase, total in enumerate(segments):
                offset = 0
                while offset < total:
                    count = min(pdu - (28 if write else 18), total - offset)
                    request = _request(connection)
                    reference = _check_request(
                        request, operation, write, offset, count, pdu, payload
                    )
                    if operation.kind == "R" and offset == 0:
                        connection.close()
                        connection = _accept(listener, pdu)
                        replay = _request(connection)
                        if replay != request:
                            raise RuntimeError(
                                f"boundary read retry changed request {operation.token()}"
                            )
                    if operation.kind == "d":
                        connection.shutdown(socket.SHUT_RDWR)
                        connection.close()
                        connection = None
                        listener.settimeout(0.15)
                        try:
                            unexpected, _ = listener.accept()
                        except TimeoutError:
                            return
                        unexpected.close()
                        raise RuntimeError("boundary lost write ACK was replayed")
                    if operation.kind == "j":
                        packet = bytearray(_ack(reference, b"\x04\x01"))
                        packet[10:12] = b"\x81\x04"
                    elif write:
                        packet = _ack(reference, b"\x05\x01", b"\xff")
                    else:
                        content = payload[offset : offset + count]
                        if operation.kind == "q" and phase == 0:
                            content = bytes([operation.size, operation.size + 1])
                        if operation.kind == "u" and phase == 1:
                            content = struct.pack(">HHH", 1, 1, 0xD800)
                        if operation.kind == "z":
                            content += b"\0"
                        packet = _ack(
                            reference,
                            b"\x04\x01",
                            b"\xff\x04" + struct.pack(">H", len(content) * 8) + content,
                        )
                    _send(connection, b"\x02\xf0\x80" + packet)
                    if operation.kind in "qz" or operation.kind == "u" and phase == 1:
                        _closed(connection)
                        return
                    offset += count
        disconnect = _receive(connection)
        if len(disconnect) != 7 or disconnect[1] != 0x80:
            raise RuntimeError("boundary plan omitted final disconnect")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(str(error))
    finally:
        if connection is not None:
            connection.close()


def _case(root: Path, pdu: int, operations: tuple[Operation, ...]) -> str | None:
    errors: list[str] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(2)
        listener.settimeout(4)
        thread = threading.Thread(
            target=_serve, args=(listener, pdu, operations, errors)
        )
        thread.start()
        try:
            outcome = subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-boundary-operations",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    str(pdu),
                    encode(operations),
                ],
                capture_output=True,
                text=True,
                timeout=15,
                check=False,
            )
        except subprocess.TimeoutExpired:
            outcome = None
        thread.join(5)
        if outcome is None:
            return "native: timeout"
        if outcome.returncode:
            return "native: " + (outcome.stderr.strip() or outcome.stdout.strip())
        if thread.is_alive():
            return "peer: unfinished conversation"
        if errors:
            return "peer: " + errors[0]
        return None


def run_boundary_operations(root: Path) -> None:
    _check_generator()
    _check_closed()
    for pdu in (240, 480):
        for seed, terminal in zip(
            (7, 2026, 65535, 0x5A17), ("q", "u", "z", "d"), strict=True
        ):
            operations = generate(seed, pdu, terminal)
            failure = _case(root, pdu, operations)
            if failure is not None:
                reduced = reduce_plan(
                    operations,
                    lambda candidate, pdu=pdu, failure=failure: (
                        _case(root, pdu, candidate) == failure
                    ),
                )
                raise RuntimeError(
                    f"boundary seed={seed} PDU={pdu} plan={encode(operations)!r} reduced={encode(reduced)!r}: {failure}; replay boundary_operations._case(root, {pdu}, boundary_operations.decode({encode(reduced)!r}))"
                )
            print(
                f"boundary operation seed={seed} PDU={pdu}: {len(operations)} parameterized operations passed"
            )


if __name__ == "__main__":
    run_boundary_operations(Path(__file__).resolve().parents[1])
