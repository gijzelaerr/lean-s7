"""Seeded, stateful DB histories checked against independent mutable memory."""

from __future__ import annotations

import random
import socket
import struct
import subprocess
import threading
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from boundary_operations import _closed, _handshake
from mixed_operations import minimize
from multi_batching import _ack, _request, _send

MEMORY_SIZE = 2048
SEEDS = (7, 2026, 65535, 0x5A17)


@dataclass(frozen=True)
class Operation:
    identifier: int
    kind: str
    start: int
    size: int
    argument: int = 0

    def token(self) -> str:
        return f"{self.identifier}:{self.kind}:{self.start}:{self.size}:{self.argument}"


def encode(operations: tuple[Operation, ...]) -> str:
    return "|".join(operation.token() for operation in operations)


def decode(plan: str) -> tuple[Operation, ...]:
    result = []
    for token in plan.split("|") if plan else ():
        identifier, kind, start, size, argument = token.split(":")
        result.append(
            Operation(int(identifier), kind, int(start), int(size), int(argument))
        )
    return tuple(result)


def generate(seed: int, pdu: int) -> tuple[Operation, ...]:
    """Keep dependent histories ordered; vary their addresses, values and extras."""
    rng = random.Random(seed)
    specifications: list[tuple[str, int, int, int]] = []
    maximum = pdu - 28
    base = rng.randrange(16, 64)
    # Duplicate writes, last-write-wins, and tiny overwrites across chunk cuts.
    for count in (0, 1, maximum - 1, maximum, maximum + 1, 2 * maximum + 1):
        salt = rng.randrange(1, 100000)
        specifications.extend(
            [("w", base, count, salt), ("w", base, count, salt), ("r", base, count, 0)]
        )
        if count >= maximum:
            cross = base + maximum - 1
            specifications.extend(
                [("w", cross, 3, salt + 1), ("r", base, count + 2, 0)]
            )
    read_maximum = pdu - 18
    specifications.extend(
        ("r", base, count, 0)
        for count in (
            0,
            1,
            read_maximum - 1,
            read_maximum,
            read_maximum + 1,
            2 * read_maximum + 1,
        )
    )
    # Both directions of containment, and disjoint guards beside overlapping data.
    for index in range(12):
        start = rng.randrange(base, base + maximum)
        count = rng.choice((1, 3, 17, maximum + 1))
        specifications.extend(
            [
                ("w", start, count, rng.randrange(1, 100000)),
                ("r", max(0, start - 3), count + 6, 0),
            ]
        )
        if index % 3 == 0:
            specifications.append(("r", 0, MEMORY_SIZE, 0))
    # All bits are set, repeated, then cleared; the surrounding range is observed.
    bit_start = base + maximum
    for bit in range(8):
        for enabled in (1, 1, 0):
            specifications.extend(
                [("b", bit_start, bit, enabled), ("r", bit_start - 2, 5, 0)]
            )
    # Seeded mixed scalar writes/bit changes force interaction, not isolated bits.
    for _ in range(12):
        if rng.randrange(2):
            specifications.append(("b", bit_start, rng.randrange(8), rng.randrange(2)))
        else:
            specifications.append(("w", bit_start - 1, 3, rng.randrange(1, 100000)))
        specifications.append(("r", bit_start - 3, 7, 0))
    return tuple(
        Operation(index + 1, *spec) for index, spec in enumerate(specifications)
    )


def reduce_plan(
    operations: tuple[Operation, ...],
    fails: Callable[[tuple[Operation, ...]], bool],
    budget: int = 12,
) -> tuple[Operation, ...]:
    """Remove whole operations, retaining stable addresses, sizes, values and IDs."""
    mapping = {
        chr(0x100 + index): operation for index, operation in enumerate(operations)
    }
    reduced = minimize(
        "".join(mapping),
        lambda candidate: fails(tuple(mapping[key] for key in candidate)),
        budget=budget,
    )
    return tuple(mapping[key] for key in reduced)


def initial_memory() -> bytearray:
    return bytearray((index * 29 + 113) % 256 for index in range(MEMORY_SIZE))


def payload(salt: int, count: int) -> bytes:
    return bytes((salt * 17 + index * 43) % 256 for index in range(count))


def update_bit(value: int, bit: int, enabled: int) -> int:
    mask = 1 << bit
    return value | mask if enabled else value & (255 ^ mask)


def _check_request(
    request: bytes, write: bool, start: int, count: int, pdu: int, data: bytes = b""
) -> int:
    parameters = bytes([5 if write else 4, 1])
    parameters += b"\x12\x0a\x10\x02" + struct.pack(">HH", count, 1) + b"\x84"
    parameters += (start * 8).to_bytes(3, "big")
    content = b"\0\x04" + struct.pack(">H", count * 8) + data if write else b""
    expected = struct.pack(">BBHHHH", 0x32, 1, 0, 0, len(parameters), len(content))
    expected += parameters + content
    if len(request) > pdu or request[:4] != expected[:4] or request[6:] != expected[6:]:
        raise RuntimeError(f"wire mismatch write={write} start={start} count={count}")
    return int.from_bytes(request[4:6], "big")


def _read(
    connection: socket.socket, memory: bytearray, start: int, count: int, pdu: int
) -> None:
    offset = 0
    while offset < count:
        size = min(pdu - 18, count - offset)
        request = _request(connection)
        reference = _check_request(request, False, start + offset, size, pdu)
        data = memory[start + offset : start + offset + size]
        packet = _ack(
            reference, b"\x04\x01", b"\xff\x04" + struct.pack(">H", size * 8) + data
        )
        _send(connection, b"\x02\xf0\x80" + packet)
        offset += size


def _write(
    connection: socket.socket, memory: bytearray, start: int, data: bytes, pdu: int
) -> None:
    offset = 0
    while offset < len(data):
        size = min(pdu - 28, len(data) - offset)
        request = _request(connection)
        reference = _check_request(
            request, True, start + offset, size, pdu, data[offset : offset + size]
        )
        # Apply observed bytes only after checking the expected logical write.
        memory[start + offset : start + offset + size] = request[-size:]
        _send(connection, b"\x02\xf0\x80" + _ack(reference, b"\x05\x01", b"\xff"))
        offset += size


def _serve(
    listener: socket.socket,
    pdu: int,
    operations: tuple[Operation, ...],
    errors: list[str],
) -> None:
    current = "handshake"
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection, pdu)
            memory = initial_memory()
            for operation in operations:
                current = operation.token()
                if operation.kind == "r":
                    _read(connection, memory, operation.start, operation.size, pdu)
                elif operation.kind == "w":
                    _write(
                        connection,
                        memory,
                        operation.start,
                        payload(operation.argument, operation.size),
                        pdu,
                    )
                elif operation.kind == "b":
                    previous = memory[operation.start]
                    _read(connection, memory, operation.start, 1, pdu)
                    updated = update_bit(previous, operation.size, operation.argument)
                    _write(connection, memory, operation.start, bytes([updated]), pdu)
                    _read(connection, memory, operation.start, 1, pdu)
                else:
                    raise RuntimeError("unknown operation kind")
            current = "final full-memory observation"
            _read(connection, memory, 0, MEMORY_SIZE, pdu)
            _closed(connection)
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(f"{current}: {error}")


def _case(root: Path, pdu: int, operations: tuple[Operation, ...]) -> str | None:
    errors: list[str] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        listener.settimeout(4)
        thread = threading.Thread(
            target=_serve, args=(listener, pdu, operations, errors)
        )
        thread.start()
        try:
            outcome = subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-overlap-operations",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    str(pdu),
                    str(MEMORY_SIZE),
                    encode(operations),
                ],
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
        except subprocess.TimeoutExpired:
            outcome = None
        thread.join(5)
        if errors:
            return "peer: " + errors[0]
        if outcome is None:
            return "native: timeout"
        if outcome.returncode:
            return "native: " + (outcome.stderr.strip() or outcome.stdout.strip())
        if thread.is_alive():
            return "peer: unfinished conversation"
        return None


def _check_model() -> None:
    for value in range(256):
        for bit in range(8):
            for enabled in (0, 1):
                updated = update_bit(value, bit, enabled)
                if (updated // 2**bit) % 2 != enabled:
                    raise RuntimeError("memory oracle bit readback failed")
                for other in range(8):
                    if (
                        other != bit
                        and (updated // 2**other) % 2 != (value // 2**other) % 2
                    ):
                        raise RuntimeError("memory oracle changed an unrelated bit")
                if update_bit(updated, bit, enabled) != updated:
                    raise RuntimeError("memory oracle bit update not idempotent")
    memory = initial_memory()
    original = memory[:]
    data = payload(19, 11)
    memory[12:23] = data
    memory[12:23] = data
    if (
        memory[:12] != original[:12]
        or memory[23:] != original[23:]
        or memory[12:23] != data
    ):
        raise RuntimeError("memory oracle write locality/duplicate failed")
    memory[15:18] = payload(20, 3)
    if (
        memory[12:15] != data[:3]
        or memory[18:23] != data[6:]
        or memory[15:18] != payload(20, 3)
    ):
        raise RuntimeError("memory oracle overlapping overwrite failed")


def _check_wire_oracle() -> None:
    for write in (False, True):
        start, count, reference = 37, 3, 1234
        parameters = bytes([5 if write else 4, 1])
        parameters += b"\x12\x0a\x10\x02" + struct.pack(">HH", count, 1) + b"\x84"
        parameters += (start * 8).to_bytes(3, "big")
        data = b"\0\x04\0\x18\x93\xbe\xe9" if write else b""
        request = struct.pack(
            ">BBHHHH", 0x32, 1, 0, reference, len(parameters), len(data)
        )
        request += parameters + data
        expected_data = b"\x93\xbe\xe9" if write else b""
        if (
            _check_request(request, write, start, count, 240, expected_data)
            != reference
        ):
            raise RuntimeError("overlap wire oracle lost response correlation")
        mutations = [request[:-1], request + b"\0"]
        for position in range(len(request)):
            if position in (4, 5):
                continue  # Dynamic request reference is echoed, not a fixed fixture.
            altered = bytearray(request)
            altered[position] ^= 1
            mutations.append(bytes(altered))
        for altered in mutations:
            try:
                _check_request(altered, write, start, count, 240, expected_data)
            except RuntimeError:
                pass
            else:
                raise RuntimeError("overlap wire oracle accepted a mutated request")
        try:
            _check_request(
                request, write, start, count, len(request) - 1, expected_data
            )
        except RuntimeError:
            pass
        else:
            raise RuntimeError("overlap wire oracle ignored negotiated PDU")


def _check_generator() -> None:
    for pdu in (240, 480):
        for seed in SEEDS:
            operations = generate(seed, pdu)
            if (
                operations != generate(seed, pdu)
                or decode(encode(operations)) != operations
            ):
                raise RuntimeError("overlap generator is not reproducible")
            if len({op.identifier for op in operations}) != len(operations):
                raise RuntimeError("overlap generator reused stable IDs")
            maximum = pdu - 28
            if not {0, 1, maximum - 1, maximum, maximum + 1, 2 * maximum + 1} <= {
                op.size for op in operations if op.kind == "w"
            }:
                raise RuntimeError("overlap generator lost write chunk boundaries")
            read_maximum = pdu - 18
            if not {
                0,
                1,
                read_maximum - 1,
                read_maximum,
                read_maximum + 1,
                2 * read_maximum + 1,
            } <= {op.size for op in operations if op.kind == "r"}:
                raise RuntimeError("overlap generator lost read chunk boundaries")
            if not {(bit, enabled) for bit in range(8) for enabled in (0, 1)} <= {
                (op.size, op.argument) for op in operations if op.kind == "b"
            }:
                raise RuntimeError("overlap generator lost mandatory bit coverage")
            for op in operations:
                count = 1 if op.kind == "b" else op.size
                if op.start < 0 or op.start + count > MEMORY_SIZE:
                    raise RuntimeError("overlap generator escaped memory bounds")
            required = operations[1:3]
            reduced = reduce_plan(
                operations,
                lambda candidate, required=required: all(
                    op in candidate for op in required
                ),
                budget=200,
            )
            if reduced != required:
                raise RuntimeError("overlap reduction mutated retained parameters")
    if generate(SEEDS[0], 240) == generate(SEEDS[1], 240):
        raise RuntimeError("overlap seeds did not vary histories")


def run_overlap_operations(root: Path) -> None:
    _check_model()
    _check_wire_oracle()
    _check_generator()
    for pdu in (240, 480):
        for seed in SEEDS:
            operations = generate(seed, pdu)
            failure = _case(root, pdu, operations)
            if failure is not None:
                reduced = reduce_plan(
                    operations,
                    lambda candidate, pdu=pdu, failure=failure: (
                        _case(root, pdu, candidate) == failure
                    ),
                )
                raise RuntimeError(
                    f"overlap seed={seed} PDU={pdu} plan={encode(operations)!r} reduced={encode(reduced)!r}: {failure}; replay overlap_operations._case(root, {pdu}, overlap_operations.decode({encode(reduced)!r}))"
                )
            print(
                f"overlap seed={seed} PDU={pdu}: {len(operations)} stateful operations and final {MEMORY_SIZE}-byte observation passed"
            )


if __name__ == "__main__":
    run_overlap_operations(Path(__file__).resolve().parents[1])
