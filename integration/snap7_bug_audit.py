"""Deterministic classic-S7 bug probes; no network or PLC required.

Run with PYTHONPATH pointing at the python-snap7 checkout under investigation.
The fake peer replaces only transport: real request builders, response parsers,
reference checks, and public client methods remain in use.
"""

from __future__ import annotations

import struct
from collections.abc import Callable
from ctypes import POINTER, c_uint8, cast

from snap7.client import Client
from snap7.type import Area, S7DataItem, WordLen


def ack(request: bytes, parameters: bytes, data: bytes) -> bytes:
    return (
        b"\x32\x03\x00\x00"
        + request[4:6]
        + struct.pack(">HH", len(parameters), len(data))
        + b"\x00\x00"
        + parameters
        + data
    )


class Peer:
    def __init__(self, reply: Callable[[bytes], bytes]) -> None:
        self.reply = reply
        self.requests: list[bytes] = []

    def send_data(self, request: bytes) -> None:
        self.requests.append(request)

    def receive_data(self) -> bytes:
        return self.reply(self.requests[-1])

    def disconnect(self) -> None:
        pass


def client_for(reply: Callable[[bytes], bytes]) -> tuple[Client, Peer]:
    client = Client()
    peer = Peer(reply)
    client.connection = peer
    client.connected = True
    return client, peer


def main() -> None:
    # Outer S7 section length is accurate, but the item promises four bytes.
    client, _ = client_for(lambda r: ack(r, b"\x04\x01", bytes.fromhex("ff040020aa")))
    result = client.db_read(1, 0, 4)
    assert result == bytearray.fromhex("aa")
    print("short read: requested 4 bytes, returned", result.hex())
    client.disconnect()

    # A valid READ response with the WRITE request's reference is not a write ACK.
    client, _ = client_for(lambda r: ack(r, b"\x04\x01", bytes.fromhex("ff040008aa")))
    result = client.db_write(1, 0, bytearray(b"\xbb"))
    assert result == 0
    print("wrong function: db_write returned success for a READ response")
    client.disconnect()

    def words_reply(request: bytes) -> bytes:
        count = int.from_bytes(request[16:18], "big")
        start = int.from_bytes(request[21:24], "big") // 8
        payload = bytes((start + i) % 251 for i in range(count * 2))
        return ack(
            request,
            b"\x04\x01",
            b"\xff\x04" + struct.pack(">H", len(payload) * 8) + payload,
        )

    client, peer = client_for(words_reply)
    client.pdu_length = 480
    result = client.read_area(Area.DB, 1, 0, 500, WordLen.Word)
    spans = [
        (int.from_bytes(r[21:24], "big") // 8, int.from_bytes(r[16:18], "big"))
        for r in peer.requests
    ]
    assert spans == [(0, 462), (462, 38)]
    assert result != bytearray(i % 251 for i in range(1000))
    print("WORD read (start byte, count):", spans)
    print("first response needs", 18 + spans[0][1] * 2, "bytes; budget is 480")
    print("second chunk starts at byte 462; first chunk ends at byte 924")
    client.disconnect()

    client, peer = client_for(lambda r: ack(r, b"\x05\x01", b"\xff"))
    payload = (c_uint8 * 4)(0x11, 0x22, 0x33, 0x44)
    item = S7DataItem()
    item.Area = Area.DB
    item.DBNumber = 1
    item.Start = 0
    item.WordLen = WordLen.Word
    item.Amount = 2
    item.pData = cast(payload, POINTER(c_uint8))
    client.write_multi_vars([item])
    request = peer.requests[0]
    assert request[15] == WordLen.Byte
    assert request[28:] == b"\x11\x22"
    print("write_multi_vars: two WORDs became two BYTEs; payload", request[28:].hex())
    client.disconnect()


if __name__ == "__main__":
    main()
