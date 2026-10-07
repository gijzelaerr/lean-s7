"""Cross-check the conformance corpus with the Wireshark S7comm dissector.

Optional, not run in CI and never a runtime dependency: it needs ``tshark``
(pinned to the version recorded in the baseline). Corpus PDUs are wrapped in
TPKT/COTP and in synthetic Ethernet/IPv4/TCP port-102 frames of an offline pcap, so
no sockets or controllers are involved. The dissector is an independent decoder of
the same wire bytes; its fields are compared with the corpus's decoded values.

Every probe is classified as

* ``agree``       dissected fields match the corpus (accepted cases), or the
                  dissector also flags the packet as malformed/unexpected
                  (rejected cases);
* ``limitation``  a corpus rejection that the dissector decodes silently. The
                  dissector is a display tool and does not enforce every rule
                  that a strict client must; this is not a lean-s7 defect;
* ``fixture``     the dissector's service-specific payload parser (for example the
                  fixed SZL 0x0424 record layout) reports a malformed packet because
                  the corpus fixture carries a shorter, synthetic payload, while the
                  envelope fields still agree. A property of the fixture, not of
                  either decoder;
* ``disagree``    fields differ for an accepted case. Needs triage: a lean-s7
                  issue, a dissector issue, or a genuine ambiguity.

The reviewed classification of every probe is stored in
``integration/wireshark_baseline.json``; the run fails when any status changes.

    python integration/wireshark_corpus.py [--tshark PATH] [--update-baseline] [--list STATUS]

This is independent-decoder evidence for the listed inputs, not controller
qualification.
"""

from __future__ import annotations

import argparse
import json
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from addressing_conformance import capture

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "conformance" / "v1"
BASELINE = Path(__file__).with_name("wireshark_baseline.json")
PINNED_TSHARK = "4.6"

AGREE, LIMITATION, FIXTURE, DISAGREE = "agree", "limitation", "fixture", "disagree"

FIELDS = [
    "frame.number",
    "s7comm.header.rosctr",
    "s7comm.header.pduref",
    "s7comm.param.func",
    "s7comm.param.userdata.funcgroup",
    "s7comm.param.userdata.subfunc",
    "s7comm.param.userdata.seq_num",
    "s7comm.param.userdata.dataunitref",
    "s7comm.param.userdata.lastdataunit",
    "s7comm.param.item.db",
    "s7comm.param.item.area",
    "s7comm.param.item.address.byte",
    "s7comm.param.item.length",
    "s7comm.param.blockcontrol.functionstatus.more",
    "s7comm.data.returncode",
    "s7comm.data.transportsize",
    "s7comm.data.length",
    "s7comm.resp.data",
    "_ws.malformed",
    "_ws.expert.message",
]

# Independent expectations for the request/response PDUs the client builds, from
# the S7 function and USER_DATA group/subfunction numbering (not from lean-s7).
REQUEST_SHAPE: dict[str, dict[str, str]] = {
    "read_clock": {"rosctr": "7", "group": "7", "sub": "1"},
    "set_clock": {"rosctr": "7", "group": "7", "sub": "2"},
    "list_blocks": {"rosctr": "7", "group": "3", "sub": "1"},
    "list_data_blocks": {"rosctr": "7", "group": "3", "sub": "2"},
    "get_db_info": {"rosctr": "7", "group": "3", "sub": "3"},
    "set_password": {"rosctr": "7", "group": "5", "sub": "1"},
    "clear_password": {"rosctr": "7", "group": "5", "sub": "2"},
    "plc_stop": {"rosctr": "1", "func": "0x29"},
    "plc_hot_start": {"rosctr": "1", "func": "0x28"},
    "plc_cold_start": {"rosctr": "1", "func": "0x28"},
    "start_db_upload": {"rosctr": "1", "func": "0x1d"},
    "upload_fragment": {"rosctr": "1", "func": "0x1e"},
    "end_upload": {"rosctr": "1", "func": "0x1f"},
    "request_db_download": {"rosctr": "1", "func": "0x1a"},
    "download_fragment_response": {"rosctr": "3", "func": "0x1b"},
    "final_download_fragment_response": {"rosctr": "3", "func": "0x1b"},
    "download_ended_response": {"rosctr": "3", "func": "0x1c"},
}


def wrap(pdu: bytes) -> bytes:
    cotp = b"\x02\xf0\x80" + pdu
    return b"\x03\x00" + struct.pack(">H", len(cotp) + 4) + cotp


def ack_data(reference: int, parameters: bytes, data: bytes) -> bytes:
    header = struct.pack(
        ">BBHHHHBB", 0x32, 3, 0, reference, len(parameters), len(data), 0, 0
    )
    return header + parameters + data


class Probe:
    def __init__(self, key: str, pdu: bytes, check: Any, reject: bool) -> None:
        self.key = key
        self.pdu = pdu
        self.check = check  # (Row) -> str: "" when fields agree, else a difference
        self.reject = reject


class Row:
    def __init__(self, values: list[str]) -> None:
        self.values = dict(zip(FIELDS, values, strict=True))

    def get(self, field: str) -> list[str]:
        raw = self.values[
            field if field.startswith(("_ws", "frame")) else "s7comm." + field
        ]
        return [item for item in raw.split(",") if item] if raw else []

    def one(self, field: str) -> str:
        found = self.get(field)
        return found[0] if found else ""

    def flagged(self) -> bool:
        return bool(self.get("_ws.malformed") or self.get("_ws.expert.message"))


def hex_colon(data: list[int] | bytes) -> str:
    return bytes(data).hex()


def compare(pairs: list[tuple[str, Any, Any]]) -> str:
    return "; ".join(
        f"{label}: dissector {got!r}, corpus {want!r}"
        for label, got, want in pairs
        if got != want
    )


def userdata_check(
    case: dict[str, Any], group: int, sub: int, reference: int | None
) -> Any:
    expected = case["expected"]

    def check(row: Row) -> str:
        pairs = [
            ("rosctr", row.one("header.rosctr"), "7"),
            ("group", row.one("param.userdata.funcgroup"), str(group)),
            ("subfunction", row.one("param.userdata.subfunc"), str(sub)),
            ("sequence", row.one("param.userdata.seq_num"), str(expected["sequence"])),
            ("payload length", row.one("data.length"), str(len(expected["payload"]))),
        ]
        if reference is not None:
            pairs.append(("pdu reference", row.one("header.pduref"), str(reference)))
        if "data_unit_reference" in expected:
            pairs.append(
                (
                    "data unit ref",
                    row.one("param.userdata.dataunitref"),
                    str(expected["data_unit_reference"]),
                )
            )
        if "return_code" in expected:
            pairs.append(
                (
                    "return code",
                    int(row.one("data.returncode") or "0", 0),
                    expected["return_code"],
                )
            )
        if "transport_size" in expected:
            pairs.append(
                (
                    "transport size",
                    int(row.one("data.transportsize") or "0", 0),
                    expected["transport_size"],
                )
            )
        # S7comm "last data unit": 0x00 = this is the last unit, 0x01 = more follow.
        last = row.one("param.userdata.lastdataunit")
        if last:
            pairs.append(("more data", int(last, 0) != 0, expected["has_more_data"]))
        return compare(pairs)

    return check


def multi_check(case: dict[str, Any], request: bool) -> Any:
    ranges = case["ranges"]
    reading = case["operation"] == "read"

    def check(row: Row) -> str:
        if request:
            func = "0x04" if reading else "0x05"
            pairs = [
                ("rosctr", row.one("header.rosctr"), "1"),
                ("function", row.one("param.func"), func),
                (
                    "item db",
                    row.get("param.item.db"),
                    [str(r["db_number"]) for r in ranges],
                ),
                ("item area", row.get("param.item.area"), ["0x84"] * len(ranges)),
                (
                    "item byte",
                    row.get("param.item.address.byte"),
                    [str(r["start"]) for r in ranges],
                ),
                (
                    "item length",
                    row.get("param.item.length"),
                    [str(r["count"]) for r in ranges],
                ),
                ("reference", row.one("header.pduref"), str(case["reference"])),
            ]
            return compare(pairs)
        items = case["expected"]["items"]
        codes = [
            ("0xff" if item["status"] == "success" else f"0x{item['code']:02x}")
            for item in items
        ]
        pairs = [
            ("rosctr", row.one("header.rosctr"), "3"),
            ("function", row.one("param.func"), "0x04" if reading else "0x05"),
            ("return codes", row.get("data.returncode"), codes),
        ]
        if reading:
            payloads = [
                hex_colon(item["payload"])
                for item in items
                if item["status"] == "success"
            ]
            pairs.append(("item payloads", row.get("resp.data"), payloads))
        return compare(pairs)

    return check


def build_probes() -> list[Probe]:
    s7 = json.loads((CORPUS / "s7.json").read_text(encoding="utf-8"))
    management = json.loads((CORPUS / "management.json").read_text(encoding="utf-8"))
    probes: list[Probe] = []

    for case in s7["userdata_cases"]:
        accept = case["expected"]["status"] == "accept"
        check = (
            userdata_check(
                case, case["expected_group"], case["expected_subfunction"], None
            )
            if accept
            else (lambda row: "")
        )
        probes.append(
            Probe(
                f"s7.json/userdata_cases/{case['id']}",
                bytes(case["pdu"]),
                check,
                not accept,
            )
        )

    for case in management["decoder_cases"]:
        accept = case["expected"]["status"] == "accept"
        check = (
            userdata_check(case, case["group"], case["subfunction"], case["reference"])
            if accept
            else (lambda row: "")
        )
        probes.append(
            Probe(
                f"management.json/decoder_cases/{case['id']}",
                bytes(case["pdu"]),
                check,
                not accept,
            )
        )

    for case in s7["multi_item_cases"]:
        probes.append(
            Probe(
                f"s7.json/multi_item_cases/{case['id']}/request",
                bytes(case["request_pdu"]),
                multi_check(case, True),
                False,
            )
        )
        accept = case["expected"]["status"] == "accept"
        check = multi_check(case, False) if accept else (lambda row: "")
        probes.append(
            Probe(
                f"s7.json/multi_item_cases/{case['id']}/response",
                bytes(case["response_pdu"]),
                check,
                not accept,
            )
        )

    for case in s7["upload_cases"]:
        expected = case["expected"]
        accept = expected["status"] == "accept"

        def upload_check(row: Row, expected: dict[str, Any] = expected) -> str:
            return compare(
                [
                    ("rosctr", row.one("header.rosctr"), "3"),
                    ("function", row.one("param.func"), "0x1e"),
                    (
                        "more fragments",
                        row.one("param.blockcontrol.functionstatus.more"),
                        "False" if expected["is_last"] else "True",
                    ),
                    (
                        "fragment",
                        row.get("resp.data"),
                        [hex_colon(expected["payload"])] if expected["payload"] else [],
                    ),
                ]
            )

        probes.append(
            Probe(
                f"s7.json/upload_cases/{case['id']}",
                bytes(case["pdu"]),
                upload_check if accept else (lambda row: ""),
                not accept,
            )
        )

    for case in s7["response_cases"]:
        expected = case["expected"]
        accept = expected["status"] == "accept"
        pdu = ack_data(1, bytes(case["parameters"]), bytes(case["data"]))

        def response_check(
            row: Row, case: dict[str, Any] = case, expected: dict[str, Any] = expected
        ) -> str:
            if case["operation"] == "read":
                return compare(
                    [
                        ("function", row.one("param.func"), "0x04"),
                        (
                            "payload",
                            row.get("resp.data"),
                            [hex_colon(expected["payload"])],
                        ),
                    ]
                )
            return compare(
                [
                    ("function", row.one("param.func"), "0x05"),
                    ("return code", row.get("data.returncode"), ["0xff"]),
                ]
            )

        probes.append(
            Probe(
                f"s7.json/response_cases/{case['id']}",
                pdu,
                response_check if accept else (lambda row: ""),
                not accept,
            )
        )

    for case in s7["request_cases"]:
        shape = REQUEST_SHAPE[case["operation"]]

        def request_check(row: Row, shape: dict[str, str] = shape) -> str:
            pairs = [("rosctr", row.one("header.rosctr"), shape["rosctr"])]
            if "func" in shape:
                pairs.append(("function", row.one("param.func"), shape["func"]))
            else:
                pairs.append(
                    ("group", row.one("param.userdata.funcgroup"), shape["group"])
                )
                pairs.append(
                    ("subfunction", row.one("param.userdata.subfunc"), shape["sub"])
                )
            return compare(pairs)

        probes.append(
            Probe(
                f"s7.json/request_cases/{case['id']}",
                bytes(case["expected_packet"]),
                request_check,
                False,
            )
        )
    return probes


def find_tshark(requested: str | None) -> str:
    for candidate in (
        requested,
        shutil.which("tshark"),
        r"C:\Program Files\Wireshark\tshark.exe",
    ):
        if candidate and (Path(candidate).exists() or shutil.which(candidate)):
            return candidate
    raise SystemExit("tshark not found; install Wireshark or pass --tshark PATH")


def dissect(tshark: str, probes: list[Probe]) -> list[Row]:
    with tempfile.TemporaryDirectory(prefix="lean-s7-wireshark-") as directory:
        path = Path(directory) / "corpus.pcap"
        path.write_bytes(capture([wrap(probe.pdu) for probe in probes]))
        command = [
            tshark,
            "-r",
            str(path),
            "-T",
            "fields",
            "-E",
            "separator=/t",
            "-E",
            "occurrence=a",
            "-E",
            "aggregator=,",
        ]
        for field in FIELDS:
            command += ["-e", field]
        output = subprocess.run(
            command, check=True, capture_output=True, text=True
        ).stdout.split("\n")
    by_frame: dict[int, Row] = {}
    for line in output:
        if not line.strip():
            continue
        row = Row((line.split("	") + [""] * len(FIELDS))[: len(FIELDS)])
        by_frame[int(row.one("frame.number"))] = row
    empty = Row([""] * len(FIELDS))
    return [by_frame.get(index, empty) for index in range(1, len(probes) + 1)]


def classify(probe: Probe, row: Row) -> tuple[str, str]:
    if probe.reject:
        return (
            (AGREE, "dissector also flags the packet")
            if row.flagged()
            else (LIMITATION, "dissector decodes it silently")
        )
    difference = probe.check(row)
    if difference:
        return DISAGREE, difference
    if row.flagged():
        reason = ",".join(row.get("_ws.expert.message") or row.get("_ws.malformed"))
        return (
            FIXTURE,
            "envelope fields agree; dissector payload parser reports: " + reason,
        )
    return AGREE, ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tshark")
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument(
        "--list", choices=[AGREE, LIMITATION, FIXTURE, DISAGREE], action="append"
    )
    args = parser.parse_args()
    tshark = find_tshark(args.tshark)
    version = subprocess.run(
        [tshark, "--version"], check=True, capture_output=True, text=True
    ).stdout.splitlines()[0]
    print(version)
    if PINNED_TSHARK not in version:
        print(
            f"warning: baseline reviewed with tshark {PINNED_TSHARK}.x", file=sys.stderr
        )

    probes = build_probes()
    rows = dissect(tshark, probes)
    results = {
        probe.key: classify(probe, row) for probe, row in zip(probes, rows, strict=True)
    }
    counts = {
        status: sum(1 for value in results.values() if value[0] == status)
        for status in (AGREE, LIMITATION, FIXTURE, DISAGREE)
    }
    print(
        f"{len(results)} probes: "
        + ", ".join(f"{status} {count}" for status, count in counts.items())
    )
    for status in args.list or []:
        for key, (found, detail) in sorted(results.items()):
            if found == status:
                print(f"  [{status}] {key}: {detail}")

    recorded = {
        key: {"status": found, "detail": detail}
        for key, (found, detail) in sorted(results.items())
    }
    if args.update_baseline:
        BASELINE.write_text(
            json.dumps({"tshark": PINNED_TSHARK, "probes": recorded}, indent=1) + "\n",
            encoding="utf-8",
        )
        print(f"wrote {BASELINE}")
        return 0
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))["probes"]
    problems = [
        f"{key}: baseline {baseline.get(key, {}).get('status')}, now {recorded.get(key, {}).get('status')}"
        for key in sorted(set(baseline) | set(recorded))
        if baseline.get(key, {}).get("status") != recorded.get(key, {}).get("status")
    ]
    if problems:
        print("classification differs from the reviewed baseline:", file=sys.stderr)
        for line in problems:
            print("  " + line, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
