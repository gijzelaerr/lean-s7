"""Capture the request PDUs the official native Snap7 client sends for each operation.

The native client library (pinned and built by ``native_snap7_build.py``; never linked into
lean-s7) is pointed at a recording stub peer on localhost. The stub completes the COTP and
S7 setup handshake, records the first S7 PDU the client sends for the operation and closes.
The recorded bytes are independent evidence for the request encoders: they come from a
different implementation than lean-s7, python-snap7 and the conformance corpus.

    python integration/native_client_requests.py --library .lake/native-snap7/snap7.dll
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

PDU_LENGTH = 480


def _tpkt(payload: bytes) -> bytes:
    return b"\x03\x00" + struct.pack(">H", len(payload) + 4) + payload


def _read_frame(connection: socket.socket) -> bytes | None:
    header = b""
    while len(header) < 4:
        chunk = connection.recv(4 - len(header))
        if not chunk:
            return None
        header += chunk
    length = struct.unpack(">H", header[2:4])[0]
    body = b""
    while len(body) < length - 4:
        chunk = connection.recv(length - 4 - len(body))
        if not chunk:
            return None
        body += chunk
    return body


def _serve(
    listener: socket.socket,
    captured: list[bytes],
    responses: list[bytes] | None = None,
) -> None:
    try:
        connection, _ = listener.accept()
    except OSError:
        return
    with connection:
        connection.settimeout(5)
        try:
            request = _read_frame(connection)
            if request is None:
                return
            confirm = bytes([0x11, 0xD0, request[4], request[5], 0, 1, 0]) + request[7:]
            connection.sendall(_tpkt(confirm))
            setup = _read_frame(connection)
            if setup is None:
                return
            reference = setup[7 + 4 : 7 + 6]
            ack = (
                b"\x32\x03\x00\x00"
                + reference
                + b"\x00\x08\x00\x00\x00\x00"
                + b"\xf0\x00\x00\x01\x00\x01"
                + struct.pack(">H", PDU_LENGTH)
            )
            connection.sendall(_tpkt(b"\x02\xf0\x80" + ack))
            # Record the first request; answer each scripted fragment (with the
            # request's PDU reference) and record the request that follows it.
            for reply in [None, *(responses or [])]:
                if reply is not None:
                    previous = captured[-1]
                    patched = reply[:4] + previous[4:6] + reply[6:]
                    connection.sendall(_tpkt(bytes([0x02, 0xF0, 0x80]) + patched))
                frame = _read_frame(connection)
                if frame is None:
                    break
                captured.append(frame[3:])  # strip the COTP data header
        except (OSError, TimeoutError):
            return


def _bind(library: Path) -> ctypes.CDLL:
    api = ctypes.CDLL(str(library.resolve()))
    handle = ctypes.c_size_t
    pointer = ctypes.c_void_p
    integer = ctypes.c_int
    signatures: dict[str, tuple[list[Any], Any]] = {
        "Cli_Create": ([], handle),
        "Cli_Destroy": ([ctypes.POINTER(handle)], None),
        "Cli_SetParam": ([handle, integer, pointer], integer),
        "Cli_ConnectTo": ([handle, ctypes.c_char_p, integer, integer], integer),
        "Cli_Disconnect": ([handle], integer),
        "Cli_ReadArea": ([handle] + [integer] * 5 + [pointer], integer),
        "Cli_WriteArea": ([handle] + [integer] * 5 + [pointer], integer),
        "Cli_DBRead": ([handle, integer, integer, integer, pointer], integer),
        "Cli_DBWrite": ([handle, integer, integer, integer, pointer], integer),
        "Cli_ReadMultiVars": ([handle, pointer, integer], integer),
        "Cli_WriteMultiVars": ([handle, pointer, integer], integer),
        "Cli_ListBlocks": ([handle, pointer], integer),
        "Cli_ListBlocksOfType": (
            [handle, integer, pointer, ctypes.POINTER(integer)],
            integer,
        ),
        "Cli_GetAgBlockInfo": ([handle, integer, integer, pointer], integer),
        "Cli_Upload": (
            [handle, integer, integer, pointer, ctypes.POINTER(integer)],
            integer,
        ),
        "Cli_FullUpload": (
            [handle, integer, integer, pointer, ctypes.POINTER(integer)],
            integer,
        ),
        "Cli_Download": ([handle, integer, pointer, integer], integer),
        "Cli_Delete": ([handle, integer, integer], integer),
        "Cli_GetPlcDateTime": ([handle, pointer], integer),
        "Cli_SetPlcDateTime": ([handle, pointer], integer),
        "Cli_ReadSZL": (
            [handle, integer, integer, pointer, ctypes.POINTER(integer)],
            integer,
        ),
        "Cli_PlcHotStart": ([handle], integer),
        "Cli_PlcColdStart": ([handle], integer),
        "Cli_PlcStop": ([handle], integer),
        "Cli_CopyRamToRom": ([handle, integer], integer),
        "Cli_Compress": ([handle, integer], integer),
        "Cli_SetSessionPassword": ([handle, ctypes.c_char_p], integer),
        "Cli_ClearSessionPassword": ([handle], integer),
        "Cli_GetPlcStatus": ([handle, ctypes.POINTER(integer)], integer),
    }
    for name, (arguments, result) in signatures.items():
        function = getattr(api, name)
        function.argtypes, function.restype = arguments, result
    return api


class DataItem(ctypes.Structure):
    _fields_ = [
        ("Area", ctypes.c_int),
        ("WordLen", ctypes.c_int),
        ("Result", ctypes.c_int),
        ("DBNumber", ctypes.c_int),
        ("Start", ctypes.c_int),
        ("Amount", ctypes.c_int),
        ("pdata", ctypes.c_void_p),
    ]


class Tm(ctypes.Structure):
    _fields_ = [
        (name, ctypes.c_int)
        for name in (
            [
                "tm_sec",
                "tm_min",
                "tm_hour",
                "tm_mday",
                "tm_mon",
                "tm_year",
                "tm_wday",
                "tm_yday",
                "tm_isdst",
            ]
        )
    ]


AREA = {"PE": 0x81, "PA": 0x82, "MK": 0x83, "DB": 0x84, "CT": 0x1C, "TM": 0x1D}
WORDLEN = {"BIT": 1, "BYTE": 2, "WORD": 4, "DWORD": 6, "COUNTER": 0x1C, "TIMER": 0x1D}
BLOCK = {
    "OB": 0x38,
    "DB": 0x41,
    "SDB": 0x42,
    "FC": 0x43,
    "SFC": 0x44,
    "FB": 0x45,
    "SFB": 0x46,
}


def operations(api: ctypes.CDLL, client: int) -> dict[str, Any]:
    big = ctypes.create_string_buffer(70000)
    size = ctypes.c_int(len(big))
    items = ctypes.c_int(100)

    def multi(function: str, entries: list[tuple[int, int, int, int, int]]) -> int:
        array = (DataItem * len(entries))()
        buffers = [ctypes.create_string_buffer(512) for _ in entries]
        for slot, (area, word, db, start, amount) in zip(array, entries, strict=True):
            slot.Area, slot.WordLen, slot.DBNumber = area, word, db
            slot.Start, slot.Amount = start, amount
        for slot, buffer in zip(array, buffers, strict=True):
            slot.pdata = ctypes.cast(buffer, ctypes.c_void_p).value
        return getattr(api, function)(client, array, len(entries))

    def block_image() -> ctypes.Array[Any]:
        # Compact block header (36 bytes, big endian) for a 128-byte DB image.
        image = bytearray(128)
        image[0:6] = bytes([0x70, 0x70, 1, 0, 5, 0x0A])  # "pp", flags, language, DB
        image[6:8] = (7).to_bytes(2, "big")  # block number
        image[8:12] = (128).to_bytes(4, "big")  # load memory length
        image[34:36] = (16).to_bytes(2, "big")  # MC7 length
        return ctypes.create_string_buffer(bytes(image), 128)

    stamp = Tm()
    stamp.tm_sec, stamp.tm_min, stamp.tm_hour = 56, 34, 12
    stamp.tm_mday, stamp.tm_mon, stamp.tm_year, stamp.tm_wday = 24, 8, 126, 4
    ops: dict[str, Any] = {}
    for name, (area, word, db, start, amount) in {
        "read-db1-byte-16x2": (AREA["DB"], WORDLEN["BYTE"], 1, 16, 2),
        "read-db300-word-0x1fe": (AREA["DB"], WORDLEN["WORD"], 300, 0x1FE, 3),
        "read-db-bit-1.3": (AREA["DB"], WORDLEN["BIT"], 5, 11, 1),
        "read-pe-byte": (AREA["PE"], WORDLEN["BYTE"], 0, 7, 4),
        "read-pa-byte": (AREA["PA"], WORDLEN["BYTE"], 0, 7, 4),
        "read-mk-byte": (AREA["MK"], WORDLEN["BYTE"], 0, 100, 4),
        "read-ct-16": (AREA["CT"], WORDLEN["COUNTER"], 0, 16, 2),
        "read-tm-16": (AREA["TM"], WORDLEN["TIMER"], 0, 16, 2),
    }.items():
        ops[name] = lambda a=area, w=word, d=db, s=start, n=amount: api.Cli_ReadArea(
            client, a, d, s, n, w, big
        )
    ops["write-db1-byte-16x2"] = lambda: api.Cli_WriteArea(
        client,
        AREA["DB"],
        1,
        16,
        2,
        WORDLEN["BYTE"],
        ctypes.create_string_buffer(b"\xaa\xbb", 2),
    )
    ops["write-db-bit-5.3"] = lambda: api.Cli_WriteArea(
        client,
        AREA["DB"],
        5,
        11,
        1,
        WORDLEN["BIT"],
        ctypes.create_string_buffer(b"\x01", 1),
    )
    ops["write-mk-word"] = lambda: api.Cli_WriteArea(
        client,
        AREA["MK"],
        0,
        10,
        1,
        WORDLEN["WORD"],
        ctypes.create_string_buffer(b"\x12\x34", 2),
    )
    ops["dbread-1-0-8"] = lambda: api.Cli_DBRead(client, 1, 0, 8, big)
    ops["multi-read"] = lambda: multi(
        "Cli_ReadMultiVars",
        [
            (AREA["DB"], WORDLEN["BYTE"], 1, 0, 2),
            (AREA["DB"], WORDLEN["BYTE"], 2, 4, 3),
        ],
    )
    ops["multi-write"] = lambda: multi(
        "Cli_WriteMultiVars",
        [
            (AREA["DB"], WORDLEN["BYTE"], 1, 0, 2),
            (AREA["DB"], WORDLEN["BYTE"], 2, 4, 3),
        ],
    )
    ops["list-blocks"] = lambda: api.Cli_ListBlocks(client, big)
    for kind, code in BLOCK.items():
        ops[f"list-blocks-of-type-{kind}"] = lambda c=code: api.Cli_ListBlocksOfType(
            client, c, big, ctypes.byref(items)
        )
        ops[f"block-info-{kind}-7"] = lambda c=code: api.Cli_GetAgBlockInfo(
            client, c, 7, big
        )
        ops[f"start-upload-{kind}-7"] = lambda c=code: api.Cli_Upload(
            client, c, 7, big, ctypes.byref(size)
        )
        ops[f"delete-{kind}-7"] = lambda c=code: api.Cli_Delete(client, c, 7)
    ops["block-info-DB-65535"] = lambda: api.Cli_GetAgBlockInfo(
        client, BLOCK["DB"], 65535, big
    )
    ops["start-full-upload-DB-7"] = lambda: api.Cli_FullUpload(
        client, BLOCK["DB"], 7, big, ctypes.byref(size)
    )
    ops["read-clock"] = lambda: api.Cli_GetPlcDateTime(client, big)
    ops["set-clock"] = lambda: api.Cli_SetPlcDateTime(client, ctypes.byref(stamp))
    ops["read-szl-0x0424-0"] = lambda: api.Cli_ReadSZL(
        client, 0x0424, 0, big, ctypes.byref(size)
    )
    ops["read-szl-0x0011-0"] = lambda: api.Cli_ReadSZL(
        client, 0x0011, 0, big, ctypes.byref(size)
    )
    ops["read-szl-0x001c-3"] = lambda: api.Cli_ReadSZL(
        client, 0x001C, 3, big, ctypes.byref(size)
    )
    ops["plc-stop"] = lambda: api.Cli_PlcStop(client)
    ops["plc-hot-start"] = lambda: api.Cli_PlcHotStart(client)
    ops["plc-cold-start"] = lambda: api.Cli_PlcColdStart(client)
    ops["copy-ram-to-rom"] = lambda: api.Cli_CopyRamToRom(client, 5000)
    ops["compress"] = lambda: api.Cli_Compress(client, 5000)
    ops["set-session-password"] = lambda: api.Cli_SetSessionPassword(client, b"abc")
    ops["set-session-password-8"] = lambda: api.Cli_SetSessionPassword(
        client, b"12345678"
    )
    ops["clear-session-password"] = lambda: api.Cli_ClearSessionPassword(client)
    ops["plc-status"] = lambda: api.Cli_GetPlcStatus(client, ctypes.byref(items))
    ops["download-start"] = lambda: api.Cli_Download(client, 7, block_image(), 128)
    return ops


def _fragment(group: int, subfunction: int, sequence: int, payload: bytes) -> bytes:
    """A USER_DATA reply fragment that announces more data (last-data-unit flag 1)."""
    parameters = bytes(
        [0, 1, 0x12, 8, 0x12, 0x80 | group, subfunction, sequence, 0, 1, 0, 0]
    )
    data = bytes([0xFF, 9]) + struct.pack(">H", len(payload)) + payload
    header = bytes([0x32, 0x07, 0, 0, 0, 0]) + struct.pack(
        ">HH", len(parameters), len(data)
    )
    return header + parameters + data


# Operations whose second request (the follow-up) is captured after one fragment.
FOLLOW_UPS: dict[str, bytes] = {
    "read-szl-0x0424-0": _fragment(
        4, 1, 0x7B, bytes([4, 0x24, 0, 0, 0, 2, 0, 1, 0xAA, 0xBB])
    ),
    "read-szl-0x001c-3": _fragment(
        4, 1, 0x7B, bytes([0, 0x1C, 0, 3, 0, 2, 0, 1, 0xAA, 0xBB])
    ),
    "list-blocks-of-type-DB": _fragment(
        3, 2, 0x7B, bytes([0, 1, 0x22, 0, 0, 2, 0x22, 0])
    ),
    "list-blocks-of-type-OB": _fragment(
        3, 2, 0x7B, bytes([0, 1, 0x22, 0, 0, 2, 0x22, 0])
    ),
}


def capture(library: Path) -> dict[str, dict[str, Any]]:
    api = _bind(library)
    names = list(operations(api, 0))
    results: dict[str, dict[str, Any]] = {}
    for name in names:
        listener = socket.socket()
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        port = listener.getsockname()[1]
        captured: list[bytes] = []
        thread = threading.Thread(
            target=_serve,
            args=(
                listener,
                captured,
                [FOLLOW_UPS[name]] if name in FOLLOW_UPS else None,
            ),
            daemon=True,
        )
        thread.start()
        client = api.Cli_Create()
        api.Cli_SetParam(client, 2, ctypes.byref(ctypes.c_uint16(port)))
        for parameter in (3, 4, 5):  # ping, send, receive timeouts (ms)
            api.Cli_SetParam(client, parameter, ctypes.byref(ctypes.c_int(1500)))
        connect = api.Cli_ConnectTo(client, b"127.0.0.1", 0, 2)
        if connect:
            results[name] = {"error": f"connect 0x{connect:08x}"}
        else:
            result = operations(api, client)[name]()
            thread.join(timeout=5)
            results[name] = {
                "pdu": captured[0].hex() if captured else None,
                **({"follow_up": captured[1].hex()} if len(captured) > 1 else {}),
                "result": f"0x{result & 0xFFFFFFFF:08x}",
            }
        api.Cli_Disconnect(client)
        api.Cli_Destroy(ctypes.byref(ctypes.c_size_t(client)))
        listener.close()
    return results


GOLDEN = Path(__file__).with_name("native_client_requests.json")


def normalized(results: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """Drop what varies between runs: the PDU reference bytes and the call results."""

    def zero_reference(text: str) -> str:
        data = bytearray(bytes.fromhex(text))
        data[4:6] = bytes(2)
        return data.hex()

    requests: dict[str, dict[str, str]] = {}
    for name, entry in sorted(results.items()):
        record = {"pdu": zero_reference(entry["pdu"])}
        if "follow_up" in entry:
            record["follow_up"] = zero_reference(entry["follow_up"])
        requests[name] = record
    return {
        "source": "official native Snap7 client (pinned revision), first request(s) per operation",
        "requests": requests,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--library", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="rewrite the golden vectors")
    mode.add_argument("--check", action="store_true", help="fail if they differ")
    arguments = parser.parse_args()
    document = normalized(capture(arguments.library))
    text = json.dumps(document, indent=1, sort_keys=True) + chr(10)
    if arguments.write:
        GOLDEN.write_text(text, encoding="utf-8", newline=chr(10))
        print(f"wrote {GOLDEN}")
    elif arguments.check:
        if json.loads(GOLDEN.read_text(encoding="utf-8")) != document:
            raise SystemExit("native client requests differ from the golden vectors")
        print(
            f"native client requests match the golden vectors ({len(document['requests'])})"
        )
    else:
        print(text)


if __name__ == "__main__":
    main()
