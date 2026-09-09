"""Check shared S7 semantics against python-snap7 using an in-memory peer."""

from __future__ import annotations

import argparse
import json
import struct
from ctypes import POINTER, c_uint8, cast
from pathlib import Path

from snap7.client import Client
from snap7.error import S7Error
from snap7.type import Area, S7DataItem, WordLen

DEFAULT_CORPUS = Path(__file__).resolve().parents[1] / "conformance/v1/s7.json"


class Peer:
    def __init__(self, reply):
        self.reply = reply
        self.requests = []

    def send_data(self, request):
        self.requests.append(request)

    def receive_data(self):
        return self.reply(self.requests[-1])

    def disconnect(self):
        pass


def ack(request, parameters, data):
    return (
        b"\x32\x03\x00\x00"
        + request[4:6]
        + struct.pack(">HH", len(parameters), len(data))
        + b"\x00\x00"
        + parameters
        + data
    )


def client_for(reply):
    client = Client()
    peer = Peer(reply)
    client.connection = peer
    client.connected = True
    return client, peer


def response_case(test):
    client, _ = client_for(
        lambda r: ack(r, bytes(test["parameters"]), bytes(test["data"]))
    )
    expected = test["expected"]
    try:
        try:
            if test["operation"] == "read":
                result = client.db_read(1, 0, test["requested_bytes"])
            elif test["operation"] == "write":
                status = client.db_write(1, 0, bytearray(test["requested_bytes"]))
                if status != 0:
                    return (
                        None
                        if expected["status"] == "reject"
                        else "valid write reported failure"
                    )
                result = b""
            else:
                raise ValueError("unsupported operation")
        except S7Error:
            return None if expected["status"] == "reject" else "valid response rejected"
        if expected["status"] == "reject":
            return "malformed response accepted"
        if bytes(result) != bytes(expected["payload"]):
            return "returned payload differs"
    finally:
        client.disconnect()


def chunk_case(test):
    width = test["element_bytes"]
    if width != 2:
        raise ValueError("unsupported element width")

    def reply(request):
        count = int.from_bytes(request[16:18], "big")
        start = int.from_bytes(request[21:24], "big") // 8
        payload = bytes((start + i) % 251 for i in range(count * width))
        return ack(
            request,
            b"\x04\x01",
            b"\xff\x04" + struct.pack(">H", len(payload) * 8) + payload,
        )

    client, peer = client_for(reply)
    client.pdu_length = test["pdu_bytes"]
    try:
        result = client.read_area(Area.DB, 1, 0, test["count"], WordLen.Word)
        counts = [int.from_bytes(r[16:18], "big") for r in peer.requests]
        starts = [int.from_bytes(r[21:24], "big") // 8 for r in peer.requests]
        expected = bytes(i % 251 for i in range(test["count"] * width))
        if counts != test["expected_counts"] or starts != test["expected_byte_starts"]:
            return f"unexpected chunks: counts={counts}, byte starts={starts}"
        if any(
            test["response_overhead_bytes"] + n * width > client.pdu_length
            for n in counts
        ):
            return "response exceeds negotiated PDU budget"
        if bytes(result) != expected:
            return "assembled read payload differs"
    finally:
        client.disconnect()


def write_case(test):
    if test["element_bytes"] != 2:
        raise ValueError("unsupported element width")
    client, peer = client_for(lambda r: ack(r, b"\x05\x01", b"\xff"))
    payload = (c_uint8 * len(test["payload"]))(*test["payload"])
    item = S7DataItem()
    item.Area, item.DBNumber, item.Start = Area.DB, 1, 0
    item.WordLen, item.Amount = WordLen.Word, test["count"]
    item.pData = cast(payload, POINTER(c_uint8))
    try:
        result = client.write_multi_vars([item])
        if result != 0 or item.Result != 0:
            return "valid write rejected"
        request = peer.requests[0]
        if request[28:] != bytes(test["expected_payload"]):
            return f"write payload differs: {request[28:].hex()}"
        if int.from_bytes(request[26:28], "big") != len(test["expected_payload"]) * 8:
            return "write data length differs"
    finally:
        client.disconnect()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    corpus = json.loads(parser.parse_args().corpus.read_text())
    if (
        corpus["schema_version"] != 1
        or corpus["protocol"] != "classic S7 read/write semantics"
    ):
        raise ValueError("unsupported corpus")
    failures = []
    total = 0
    for group, run in (
        ("response_cases", response_case),
        ("chunk_cases", chunk_case),
        ("write_cases", write_case),
    ):
        for test in corpus[group]:
            total += 1
            try:
                failure = run(test)
            except Exception as error:  # noqa: BLE001 -- report crashes as failed cases
                failure = f"unexpected {type(error).__name__}: {error}"
            if failure:
                failures.append(f"{test['id']}: {failure}")
    for failure in failures:
        print(f"FAIL {failure}")
    print(f"{total - len(failures)}/{total} S7 conformance cases passed")
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
