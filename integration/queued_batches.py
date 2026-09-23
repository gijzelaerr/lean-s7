"""Seeded mixed-size batches behind a public FIFO admission barrier.

The peer independently budgets requests and worst-case successful responses. It
checks every caller item and chunk, including duplicate ranges, odd padding,
rejections, retries, and terminal failures without a PLC or private reflection.
"""

from __future__ import annotations

import random
import select
import socket
import struct
import subprocess
import threading
from dataclasses import dataclass
from pathlib import Path

from multi_batching import _ack, _receive, _request, _send


@dataclass(frozen=True)
class Piece:
    item: int
    start: int
    offset: int
    size: int


def generate(seed: int, pdu: int) -> tuple[int, ...]:
    """A reproducible tiny prefix plus shuffled single-item byte boundaries."""
    rng = random.Random(seed)
    tiny = [rng.choice((1, 2, 3)) for _ in range(21)]
    boundaries = [pdu - 29, pdu - 28, pdu - 27, pdu - 19, pdu - 18, pdu - 17]
    rng.shuffle(boundaries)
    return tuple(tiny + boundaries + [2 * (pdu - 28) + 3, tiny[0]])


def _payload(piece: Piece) -> bytes:
    return bytes(
        (piece.item * 29 + offset * 37 + 11) % 256
        for offset in range(piece.offset, piece.offset + piece.size)
    )


def _batches(
    sizes: tuple[int, ...], pdu: int, write: bool
) -> tuple[tuple[Piece, ...], ...]:
    """Independent conservative planner; padding reserves include the final item.

    The actual wire includes padding only between items. Oversized logical items
    become consecutive singleton exchanges before the following caller item.
    """
    batches: list[tuple[Piece, ...]] = []
    selected: list[Piece] = []
    request, response = 12, 14
    maximum = pdu - (28 if write else 18)
    for item, size in enumerate(sizes):
        start = 0 if item + 1 == len(sizes) else item * 2048
        contribution = 4 + size + size % 2
        alone_fits = (
            12 + 12 + (contribution if write else 0) <= pdu
            and 14 + (1 if write else contribution) <= pdu
        )
        if not alone_fits:
            if selected:
                batches.append(tuple(selected))
                selected = []
            request, response = 12, 14
            for offset in range(0, size, maximum):
                batches.append(
                    (Piece(item, start + offset, offset, min(maximum, size - offset)),)
                )
            continue
        next_request = request + 12 + (contribution if write else 0)
        next_response = response + (1 if write else contribution)
        if len(selected) == 20 or next_request > pdu or next_response > pdu:
            batches.append(tuple(selected))
            selected = []
            request, response = 12, 14
        selected.append(Piece(item, start, 0, size))
        request += 12 + (contribution if write else 0)
        response += 1 if write else contribution
    if selected:
        batches.append(tuple(selected))
    return tuple(batches)


def _wire(batch: tuple[Piece, ...], write: bool) -> bytes:
    parameters = bytearray((5 if write else 4, len(batch)))
    data = bytearray()
    for position, piece in enumerate(batch):
        parameters.extend(
            b"\x12\x0a\x10\x02" + struct.pack(">HHB", piece.size, 1, 0x84)
        )
        parameters.extend((piece.start * 8).to_bytes(3, "big"))
        if write:
            data.extend(struct.pack(">BBH", 0, 4, piece.size * 8) + _payload(piece))
            if position + 1 < len(batch) and piece.size % 2:
                data.append(0)
    return (
        struct.pack(">BBHHHH", 0x32, 1, 0, 0, len(parameters), len(data))
        + parameters
        + data
    )


def _check(request: bytes, batch: tuple[Piece, ...], pdu: int, write: bool) -> int:
    expected = _wire(batch, write)
    if len(request) > pdu or request[:4] != expected[:4] or request[6:] != expected[6:]:
        raise RuntimeError(
            f"wire/order/padding mismatch function={5 if write else 4} "
            f"items={[(piece.item, piece.offset, piece.size) for piece in batch]} "
            f"request={request.hex()} expected={expected.hex()}"
        )
    return int.from_bytes(request[4:6], "big")


def _reply(reference: int, batch: tuple[Piece, ...], write: bool) -> bytes:
    data = bytearray()
    for position, piece in enumerate(batch):
        rejected = piece.item == 2
        if write:
            data.append(5 if rejected else 0xFF)
        elif rejected:
            data.extend(b"\x05\0\0\0")
        else:
            data.extend(struct.pack(">BBH", 0xFF, 4, piece.size * 8) + _payload(piece))
            if position + 1 < len(batch) and piece.size % 2:
                data.append(0)
    return _ack(reference, bytes((5 if write else 4, len(batch))), bytes(data))


def _handshake(connection: socket.socket, pdu: int) -> None:
    connection.settimeout(5)
    cr = _receive(connection)
    if len(cr) < 7 or cr[1] != 0xE0:
        raise RuntimeError("missing classic COTP connection request")
    _send(connection, bytes((0x11, 0xD0, cr[4], cr[5], 0, 1, 0)) + cr[7:])
    setup = _request(connection)
    if (
        setup[:4] != b"\x32\x01\0\0"
        or setup[6:] != b"\0\x08\0\0\xf0\0\0\x01\0\x01\x01\xe0"
    ):
        raise RuntimeError(f"unexpected classic SETUP request: {setup.hex()}")
    _send(
        connection,
        b"\x02\xf0\x80"
        + _ack(
            int.from_bytes(setup[4:6], "big"),
            b"\xf0\0\0\x01\0\x01" + struct.pack(">H", pdu),
        ),
    )


def _no_reconnect(listener: socket.socket) -> None:
    listener.settimeout(0.15)
    try:
        unexpected, _ = listener.accept()
    except TimeoutError:
        return
    unexpected.close()
    raise RuntimeError("queued operation reconnected/replayed after closure")


def _serve(
    listener: socket.socket,
    sizes: tuple[int, ...],
    pdu: int,
    mode: str,
    pending: threading.Event,
    release: threading.Event,
    errors: list[Exception],
) -> None:
    stage = "accept"
    connection: socket.socket | None = None
    try:
        connection, _ = listener.accept()
        stage = "initial handshake"
        _handshake(connection, pdu)
        read_batches = _batches(sizes, pdu, False)
        first = _request(connection)
        _check(first, read_batches[0], pdu, False)
        pending.set()
        stage = "five actual gate admissions"
        if not release.wait(5):
            raise RuntimeError("process did not admit all queued calls")
        if mode == "early-retry":
            connection.close()
            connection, _ = listener.accept()
            stage = "early read retry handshake"
            _handshake(connection, pdu)
            retry = _request(connection)
            if retry != first:
                raise RuntimeError(
                    "early retry changed reference/items or yielded its FIFO place"
                )
        references: set[int] = set()
        for operation, write in enumerate((False, True, False)):
            batches = _batches(sizes, pdu, write)
            for position, batch in enumerate(batches):
                stage = f"operation {operation}, batch {position}, items {[(p.item, p.offset) for p in batch]}"
                request = (
                    first if operation == 0 and position == 0 else _request(connection)
                )
                reference = _check(request, batch, pdu, write)
                if reference in references:
                    raise RuntimeError("completed exchanges reused a reference")
                references.add(reference)
                drop = (
                    (
                        mode == "read-partial-drop"
                        and operation == 0
                        and batch[0].item == len(sizes) - 2
                        and batch[0].offset == pdu - 18
                    )
                    or (mode == "write-drop" and operation == 1 and position == 0)
                    or (
                        mode == "write-partial-drop"
                        and operation == 1
                        and batch[0].item == len(sizes) - 2
                        and batch[0].offset == pdu - 28
                    )
                )
                if drop:
                    connection.close()
                    connection = None
                    stage = "no retry after acknowledged prefix/lost mutating ACK"
                    _no_reconnect(listener)
                    return
                reply = _reply(reference, batch, write)
                if len(reply) > pdu:
                    raise RuntimeError("independent response exceeds negotiated budget")
                _send(connection, b"\x02\xf0\x80" + reply)
        stage = "FIFO disconnect before late write"
        if _receive(connection) != b"\x06\x80\0\x01\0\x01\0":
            raise RuntimeError("queued late write overtook disconnect")
        try:
            remaining = connection.recv(1)
        except ConnectionResetError:
            remaining = b""
        if remaining:
            raise RuntimeError("late write or repeated disconnect sent further traffic")
        connection.close()
        connection = None
        stage = "no session resurrection"
        _no_reconnect(listener)
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(
            RuntimeError(f"queued batches PDU={pdu} mode={mode} at {stage}: {error}")
        )
        pending.set()
    finally:
        if connection is not None:
            connection.close()


def _self_test() -> None:
    """Check mandatory coverage and that wire mutations cannot pass the oracle."""
    for seed in (19, 2026):
        for pdu in (240, 480):
            sizes = generate(seed, pdu)
            assert sizes == generate(seed, pdu) and sizes[0] == sizes[-1]
            assert {
                pdu - 29,
                pdu - 28,
                pdu - 27,
                pdu - 19,
                pdu - 18,
                pdu - 17,
            }.issubset(sizes)
            for write in (False, True):
                batches = _batches(sizes, pdu, write)
                flattened = tuple(piece for batch in batches for piece in batch)
                assert tuple(sorted(piece.item for piece in flattened)) == tuple(
                    piece.item for piece in flattened
                )
                assert flattened[0].start == flattened[-1].start == 0
                assert any(piece.offset > 0 for piece in flattened)
                if pdu == 480:
                    assert len(batches[0]) == 20
                for batch in batches:
                    assert 1 <= len(batch) <= 20
                    wire = _wire(batch, write)
                    assert len(wire) <= pdu and len(_reply(0, batch, write)) <= pdu
                    assert _check(wire, batch, pdu, write) == 0
                    for index in (1, 6, 10, 11, 16, 23, len(wire) - 1):
                        damaged = bytearray(wire)
                        damaged[index] ^= 1
                        try:
                            _check(bytes(damaged), batch, pdu, write)
                        except RuntimeError:
                            pass
                        else:
                            raise RuntimeError(
                                f"queued batch oracle accepted wire mutation at {index}"
                            )
                    if len(batch) > 1:
                        try:
                            _check(
                                _wire(tuple(reversed(batch)), write), batch, pdu, write
                            )
                        except RuntimeError:
                            pass
                        else:
                            raise RuntimeError(
                                "queued batch oracle accepted reordered caller items"
                            )


def run_queued_batches(root: Path) -> None:
    _self_test()
    modes = (
        "success",
        "early-retry",
        "read-partial-drop",
        "write-drop",
        "write-partial-drop",
    )
    for seed in (19, 2026):
        for pdu in (240, 480):
            sizes = generate(seed, pdu)
            for mode in modes:
                errors: list[Exception] = []
                pending, release = threading.Event(), threading.Event()
                with socket.socket() as listener:
                    listener.bind(("127.0.0.1", 0))
                    listener.listen(4)
                    listener.settimeout(5)
                    worker = threading.Thread(
                        target=_serve,
                        args=(listener, sizes, pdu, mode, pending, release, errors),
                    )
                    worker.start()
                    process = subprocess.Popen(
                        [
                            str(root / ".lake/build/bin/lean-s7"),
                            "integration-queued-batches",
                            "127.0.0.1",
                            str(listener.getsockname()[1]),
                            str(pdu),
                            mode,
                            ",".join(map(str, sizes)),
                        ],
                        cwd=root,
                        stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                    )
                    try:
                        if not pending.wait(5) or errors:
                            if process.poll() is not None:
                                stdout, stderr = process.communicate()
                                raise RuntimeError(
                                    f"queued batches exited before first request: {stdout}{stderr}"
                                )
                            raise RuntimeError(
                                f"queued batches seed={seed} failed before first barrier: {errors}"
                            )
                        assert process.stdin is not None and process.stdout is not None
                        process.stdin.write("launch\n")
                        process.stdin.flush()
                        if not select.select([process.stdout], [], [], 5)[0]:
                            raise RuntimeError(
                                "queued batches did not establish five gate admissions"
                            )
                        barrier = process.stdout.readline().strip()
                        if barrier != "queued batches admitted 5":
                            raise RuntimeError(
                                f"unexpected queued batches barrier: {barrier!r}"
                            )
                        release.set()
                        stdout, stderr = process.communicate(timeout=15)
                        if process.returncode:
                            raise RuntimeError(
                                f"queued batches seed={seed} PDU={pdu} mode={mode} failed: {stdout}{stderr}"
                            )
                        print(f"seed={seed} {stdout.strip()}")
                    finally:
                        release.set()
                        if process.poll() is None:
                            process.kill()
                            process.communicate()
                        worker.join(timeout=6)
                    if worker.is_alive():
                        raise RuntimeError("queued batch peer did not terminate")
                    if errors:
                        raise errors[0]
    print(
        "queued batch campaign passed: 20 seeded conversations, 29 caller items per operation"
    )
