"""Check shared S7 semantics against python-snap7 using an in-memory peer."""

from __future__ import annotations

import argparse
import json
import struct
from ctypes import POINTER, c_uint8, cast
from datetime import datetime, timezone
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


def userdata_case(test):
    client = Client()
    expected = test["expected"]
    try:
        try:
            response = client.protocol.parse_response(bytes(test["pdu"]))
        except S7Error:
            return None if expected["status"] == "reject" else "valid response rejected"
        if expected["status"] == "reject":
            return "malformed USER_DATA response accepted"
        parameters = response.get("parameters") or {}
        data = response.get("data") or {}
        if parameters.get("group") != test["expected_group"]:
            return "USER_DATA function group differs"
        if parameters.get("subfunction") != test["expected_subfunction"]:
            return "USER_DATA subfunction differs"
        if parameters.get("sequence_number") != expected["sequence"]:
            return "USER_DATA sequence differs"
        if bool(parameters.get("last_data_unit")) != expected["has_more_data"]:
            return "USER_DATA continuation flag differs"
        if bytes(data.get("data", b"")) != bytes(expected["payload"]):
            return "USER_DATA payload differs"
    finally:
        client.disconnect()


def upload_case(test):
    client = Client()
    expected = test["expected"]
    try:
        try:
            response = client.protocol.parse_response(bytes(test["pdu"]))
            payload = client.protocol.parse_upload_response(response)
        except S7Error:
            return None if expected["status"] == "reject" else "valid response rejected"
        if expected["status"] == "reject":
            return "malformed upload response accepted"
        if bytes(payload) != bytes(expected["payload"]):
            return "upload payload differs"
    finally:
        client.disconnect()


def request_case(test):
    protocol = Client().protocol
    operation = test["operation"]
    if operation == "read_clock":
        packet = protocol.build_get_clock_request()
    elif operation == "list_blocks":
        packet = protocol.build_list_blocks_request()
    elif operation == "list_data_blocks":
        packet = protocol.build_list_blocks_of_type_request(0x41)
    elif operation == "plc_stop":
        packet = protocol.build_plc_control_request("stop")
    elif operation == "plc_hot_start":
        packet = protocol.build_plc_control_request("hot_start")
    elif operation == "plc_cold_start":
        packet = protocol.build_plc_control_request("cold_start")
    elif operation == "start_db_upload":
        packet = protocol.build_start_upload_request(0x41, 1)
    elif operation == "upload_fragment":
        packet = protocol.build_upload_request(7)
    elif operation == "end_upload":
        packet = protocol.build_end_upload_request(7)
    elif operation == "set_clock":
        packet = protocol.build_set_clock_request(
            datetime(2026, 9, 23, 12, 34, 56, 789000, tzinfo=timezone.utc)
        )
    elif operation in {
        "set_password",
        "clear_password",
        "download_fragment_response",
        "final_download_fragment_response",
        "download_ended_response",
    }:
        return "operation is not implemented by python-snap7 protocol"
    elif operation == "get_db_info":
        packet = protocol.build_get_block_info_request(0x41, 1)
    elif operation == "request_db_download":
        packet = protocol.build_download_request(0x41, 1, bytes(64))
    else:
        raise ValueError(f"unsupported request operation: {operation}")
    if bytes(packet) != bytes(test["expected_packet"]):
        return f"request packet differs: {bytes(packet).hex()}"


def block_count_case(test):
    protocol = Client().protocol
    expected = test["expected"]
    try:
        actual = protocol.parse_list_blocks_response(
            {"data": {"data": bytes(test["payload"])}}
        )
    except S7Error:
        return None if expected["status"] == "reject" else "valid block counts rejected"
    if expected["status"] == "reject":
        return "malformed block counts accepted"
    counts = expected["counts"]
    expected_python = {
        "OBCount": counts["organization_blocks"],
        "FBCount": counts["function_blocks"],
        "FCCount": counts["functions"],
        "DBCount": counts["data_blocks"],
        "SDBCount": counts["system_data_blocks"],
        "SFCCount": counts["system_functions"],
        "SFBCount": counts["system_function_blocks"],
    }
    if actual != expected_python:
        return f"decoded block counts differ: {actual}"


def block_list_case(test):
    protocol = Client().protocol
    expected = test["expected"]
    try:
        actual = protocol.parse_list_blocks_of_type_response(
            {"data": {"data": bytes(test["payload"])}}
        )
    except S7Error:
        return None if expected["status"] == "reject" else "valid block list rejected"
    if expected["status"] == "reject":
        return "malformed block list accepted"
    expected_numbers = [entry["number"] for entry in expected["entries"]]
    if actual != expected_numbers:
        return f"decoded block list differs: {actual}"


def block_info_case(test):
    protocol = Client().protocol
    expected = test["expected"]
    try:
        actual = protocol.parse_get_block_info_response(
            {"data": {"data": bytes(test["payload"])}}
        )
    except S7Error:
        return None if expected["status"] == "reject" else "valid block info rejected"
    if expected["status"] == "reject":
        return "malformed block info accepted"
    info = expected["info"]
    comparable = {
        "block_type": actual["block_type"],
        "number": actual["block_number"],
        "language": actual["block_lang"],
        "flags": actual["block_flags"],
        "mc7_size": actual["mc7_size"],
        "load_size": actual["load_size"],
        "local_data_size": actual["local_data"],
        "sbb_size": actual["sbb_length"],
        "checksum": actual["checksum"],
        "version": actual["version"],
        "code_date": list(actual["code_date"]),
        "interface_date": list(actual["intf_date"]),
        "author": bytes(actual["author"]).rstrip(b" \x00").decode("ascii"),
        "family": bytes(actual["family"]).rstrip(b" \x00").decode("ascii"),
        "name": bytes(actual["header"]).rstrip(b" \x00").decode("ascii"),
    }
    if comparable != info:
        return f"decoded block info differs: {comparable}"


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
    if corpus["schema_version"] != 1 or corpus["protocol"] != "classic S7 semantics":
        raise ValueError("unsupported corpus")
    failures = []
    total = 0
    for group, run in (
        ("response_cases", response_case),
        ("userdata_cases", userdata_case),
        ("upload_cases", upload_case),
        ("request_cases", request_case),
        ("block_count_cases", block_count_case),
        ("block_list_cases", block_list_case),
        ("block_info_cases", block_info_case),
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
