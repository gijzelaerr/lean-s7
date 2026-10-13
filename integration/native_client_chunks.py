"""Record the full request sequence of the official native Snap7 client for chunked transfers.

The pinned native client library (see ``native_snap7_build.py``; never linked into lean-s7)
reads and writes more elements than fit one PDU against a stub peer that answers every
read with zero bytes and acknowledges every write. The requests it sends (function, area,
word length, element count and raw wire address) are the golden file
``native_client_chunks.json``. This documents what that implementation does, including
where it disagrees with the protocol's meaning of an address; it is not a specification.

    python integration/native_client_chunks.py --library .lake/native-snap7/snap7.dll --check
"""

from __future__ import annotations

import argparse
import ctypes
import json
import socket
import struct
import threading
from pathlib import Path
from typing import Any

from native_client_requests import _bind, _read_frame, _tpkt

GOLDEN = Path(__file__).with_name("native_client_chunks.json")
WIDTH = {1: 1, 2: 1, 4: 2, 6: 4, 0x1C: 2, 0x1D: 2}
AREAS = {0x1C: "counters", 0x1D: "timers", 0x83: "markers", 0x84: "data-blocks"}


def _answer(pdu: bytes) -> bytes | None:
    function, items, reference = pdu[10], pdu[11], pdu[4:6]
    if function == 4:
        data = b""
        for index in range(items):
            item = pdu[12 + 12 * index : 24 + 12 * index]
            word = item[3]
            size = struct.unpack(">H", item[4:6])[0] * WIDTH.get(word, 1)
            data += bytes([0xFF, 0x09]) + struct.pack(">H", size) + bytes(size)
        parameters = bytes([4, items])
    elif function == 5:
        data = bytes([0xFF]) * items
        parameters = bytes([5, items])
    else:
        return None
    header = (
        bytes([0x32, 3, 0, 0]) + reference + struct.pack(">HH", 2, len(data)) + bytes(2)
    )
    return header + parameters + data


def _serve(listener: socket.socket, captured: list[bytes], pdu_length: int) -> None:
    try:
        connection, _ = listener.accept()
    except OSError:
        return
    with connection:
        connection.settimeout(3)
        try:
            request = _read_frame(connection)
            if request is None:
                return
            confirm = bytes([0x11, 0xD0, request[4], request[5], 0, 1, 0]) + request[7:]
            connection.sendall(_tpkt(confirm))
            setup = _read_frame(connection)
            if setup is None:
                return
            ack = (
                bytes([0x32, 3, 0, 0])
                + setup[11:13]
                + bytes([0, 8, 0, 0, 0, 0, 0xF0, 0, 0, 1, 0, 1])
                + struct.pack(">H", pdu_length)
            )
            connection.sendall(_tpkt(bytes([2, 0xF0, 0x80]) + ack))
            while (frame := _read_frame(connection)) is not None:
                captured.append(frame[3:])
                reply = _answer(frame[3:])
                if reply is None:
                    return
                connection.sendall(_tpkt(bytes([2, 0xF0, 0x80]) + reply))
        except (OSError, TimeoutError, IndexError):
            return


def _describe(pdu: bytes) -> dict[str, Any]:
    item = pdu[12:24]
    return {
        "function": pdu[10],
        "area": AREAS[item[8]],
        "db": struct.unpack(">H", item[6:8])[0],
        "word_length": item[3],
        "count": struct.unpack(">H", item[4:6])[0],
        "wire_address": int.from_bytes(item[9:12], "big"),
    }


def _scenarios(api: ctypes.CDLL, big: Any) -> dict[str, Any]:
    return {
        "read-counters-500-from-16": lambda c: api.Cli_ReadArea(
            c, 0x1C, 0, 16, 500, 0x1C, big
        ),
        "read-timers-300-from-3": lambda c: api.Cli_ReadArea(
            c, 0x1D, 0, 3, 300, 0x1D, big
        ),
        "read-db1-bytes-1000-from-10": lambda c: api.Cli_ReadArea(
            c, 0x84, 1, 10, 1000, 2, big
        ),
        "read-db1-words-500-from-10": lambda c: api.Cli_ReadArea(
            c, 0x84, 1, 10, 500, 4, big
        ),
        "read-markers-bytes-1000-from-0": lambda c: api.Cli_ReadArea(
            c, 0x83, 0, 0, 1000, 2, big
        ),
        "write-db1-bytes-1000-from-10": lambda c: api.Cli_WriteArea(
            c, 0x84, 1, 10, 1000, 2, big
        ),
        "write-counters-300-from-16": lambda c: api.Cli_WriteArea(
            c, 0x1C, 0, 16, 300, 0x1C, big
        ),
    }


def capture(library: Path) -> dict[str, Any]:
    api = _bind(library)
    big = ctypes.create_string_buffer(70000)
    results: dict[str, Any] = {}
    for pdu_length in (480, 240):
        for name, call in _scenarios(api, big).items():
            listener = socket.socket()
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            captured: list[bytes] = []
            thread = threading.Thread(
                target=_serve, args=(listener, captured, pdu_length), daemon=True
            )
            thread.start()
            client = api.Cli_Create()
            api.Cli_SetParam(
                client, 2, ctypes.byref(ctypes.c_uint16(listener.getsockname()[1]))
            )
            for parameter in (3, 4, 5):
                api.Cli_SetParam(client, parameter, ctypes.byref(ctypes.c_int(1500)))
            if api.Cli_ConnectTo(client, b"127.0.0.1", 0, 2):
                raise RuntimeError("native client could not connect to the stub")
            result = call(client)
            api.Cli_Disconnect(client)
            api.Cli_Destroy(ctypes.byref(ctypes.c_size_t(client)))
            listener.close()
            thread.join(timeout=3)
            results[f"pdu{pdu_length}-{name}"] = {
                "result": result & 0xFFFFFFFF,
                "requests": [_describe(pdu) for pdu in captured],
            }
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--library", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    document = {
        "source": "official native Snap7 client (pinned revision), chunked transfers",
        "scenarios": capture(arguments.library),
    }
    text = json.dumps(document, indent=1, sort_keys=True) + chr(10)
    if arguments.write:
        GOLDEN.write_text(text, encoding="utf-8", newline=chr(10))
        print(f"wrote {GOLDEN}")
    elif arguments.check:
        if json.loads(GOLDEN.read_text(encoding="utf-8")) != document:
            raise SystemExit("native chunk sequences differ from the golden file")
        print(f"native chunk sequences match ({len(document['scenarios'])})")
    else:
        print(text)


if __name__ == "__main__":
    main()
