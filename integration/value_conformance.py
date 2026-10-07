"""Independent stdlib oracle for portable integer, Unicode, and clock cases.

This checks exported value-codec behavior, not PLC firmware or network IO.
64-bit integer values are decimal strings; floats and NaN equality are out of scope.
"""

from __future__ import annotations

import argparse
import datetime
import json
from copy import deepcopy
from pathlib import Path

DEFAULT_CORPUS = Path(__file__).resolve().parents[1] / "conformance/v1/values.json"


def octets(spec: dict) -> bytes:
    if (
        not isinstance(spec, dict)
        or set(spec) != {"chunks"}
        or not isinstance(spec["chunks"], list)
    ):
        raise ValueError("unsupported byte specification")
    result = bytearray()
    for chunk in spec["chunks"]:
        if not isinstance(chunk, dict):
            raise TypeError("invalid byte chunk")
        if set(chunk) == {"bytes"}:
            values = chunk["bytes"]
            if not isinstance(values, list) or any(
                type(value) is not int or not 0 <= value <= 255 for value in values
            ):
                raise ValueError("invalid literal octets")
            result.extend(values)
        elif set(chunk) == {"repeat"}:
            repeat = chunk["repeat"]
            if not isinstance(repeat, dict) or set(repeat) != {"byte", "count"}:
                raise ValueError("invalid repeated octets")
            byte, count = repeat["byte"], repeat["count"]
            if (
                type(byte) is not int
                or type(count) is not int
                or not 0 <= byte <= 255
                or not 0 <= count <= 1_000_000
            ):
                raise ValueError("invalid repeated octet range")
            result.extend(bytes([byte]) * count)
        else:
            raise ValueError("unsupported byte chunk")
        if len(result) > 1_000_000:
            raise ValueError("oversized byte specification")
    return bytes(result)


def reject(category: str) -> dict:
    return {"status": "reject", "category": category}


def decode_integer(test: dict) -> dict:
    sizes = {
        f"{signed}int{bits}": bits // 8
        for signed in ("", "u")
        for bits in (8, 16, 32, 64)
    }
    codec = test["codec"]
    if codec not in sizes:
        raise ValueError("unsupported integer codec")
    raw_value = test["input_value"]
    if not isinstance(raw_value, str) or raw_value != str(int(raw_value)):
        raise ValueError("integer input must be a canonical decimal string")
    data, offset, width = octets(test["data"]), test["offset"], sizes[codec]
    if type(offset) is not int or offset < 0:
        raise ValueError("invalid integer offset")
    if len(data) - offset < width:
        return reject("truncated-value")
    signed = not codec.startswith("u")
    value = int.from_bytes(data[offset : offset + width], "big", signed=signed)
    encoded = int(raw_value).to_bytes(width, "big", signed=signed)
    return {"status": "accept", "encoded": encoded, "value": str(value)}


def decode_string(test: dict) -> dict:
    encoding = test["encoding"]
    if encoding not in ("latin-1", "utf-16-be"):
        raise ValueError("unsupported string encoding")
    width, limit = (1, 254) if encoding == "latin-1" else (2, 16382)
    fields = {}
    if test["operation"] == "roundtrip":
        maximum, value = test["maximum"], test["input_value"]
        if type(maximum) is not int or maximum < 0 or not isinstance(value, str):
            raise ValueError("invalid string encoding input")
        try:
            raw = value.encode(encoding)
        except UnicodeEncodeError:
            return reject("encode-value")
        current = len(raw) // width
        if maximum > limit or current > maximum:
            return reject("encode-value")
        fields["encoded"] = (
            maximum.to_bytes(width, "big")
            + current.to_bytes(width, "big")
            + raw
            + bytes((maximum - current) * width)
        )
    elif test["operation"] != "decode":
        raise ValueError("unsupported string operation")
    data, offset = octets(test["data"]), test["offset"]
    if type(offset) is not int or offset < 0:
        raise ValueError("invalid string offset")
    data = data[offset:]
    if len(data) < width * 2:
        return reject("value-codec")
    maximum = int.from_bytes(data[:width], "big")
    current = int.from_bytes(data[width : width * 2], "big")
    if maximum > limit or current > maximum or len(data) < (maximum + 2) * width:
        return reject("value-codec")
    try:
        value = data[width * 2 : width * (current + 2)].decode(encoding)
    except UnicodeDecodeError:
        return reject("value-codec")
    return {"status": "accept", **fields, "value": value}


def validate_clock(value: dict) -> None:
    if set(value) != {
        "year",
        "month",
        "day",
        "hour",
        "minute",
        "second",
        "millisecond",
        "weekday",
    } or any(type(field) is not int for field in value.values()):
        raise ValueError("invalid clock structure")
    if (
        not 1990 <= value["year"] <= 2089
        or not 0 <= value["millisecond"] <= 999
        or not 1 <= value["weekday"] <= 7
    ):
        raise ValueError("invalid clock range")
    # Firmware weekday convention is not inferred from calendar alignment.
    datetime.datetime(
        value["year"],
        value["month"],
        value["day"],
        value["hour"],
        value["minute"],
        value["second"],
        tzinfo=datetime.timezone.utc,
    )


def _bcd(value: int) -> int:
    return int(f"{value:02d}", 16)


def decode_clock(test: dict) -> dict:
    fields = {}
    if test["operation"] == "roundtrip":
        value = test["input_value"]
        try:
            validate_clock(value)
        except ValueError:
            return reject("encode-clock")
        fields["encoded"] = bytes(
            [
                0,
                0x19,
                _bcd(value["year"] % 100),
                _bcd(value["month"]),
                _bcd(value["day"]),
                _bcd(value["hour"]),
                _bcd(value["minute"]),
                _bcd(value["second"]),
                _bcd(value["millisecond"] // 10),
                (value["millisecond"] % 10) * 16 + value["weekday"],
            ]
        )
    elif test["operation"] != "decode":
        raise ValueError("unsupported clock operation")
    data = octets(test["data"])
    if len(data) != 10:
        return reject("clock-validation")
    digits = [f"{byte:02x}" for byte in data[2:9]]
    if any(not digit.isdecimal() for digit in digits) or data[9] >> 4 > 9:
        return reject("clock-validation")
    year, month, day, hour, minute, second, millisecond_high = map(int, digits)
    value = {
        "year": 2000 + year if year < 90 else 1900 + year,
        "month": month,
        "day": day,
        "hour": hour,
        "minute": minute,
        "second": second,
        "millisecond": millisecond_high * 10 + (data[9] >> 4),
        "weekday": data[9] & 15,
    }
    try:
        validate_clock(value)
    except ValueError:
        return reject("clock-validation")
    return {"status": "accept", **fields, "value": value}


def check(corpus: dict) -> int:
    if (
        type(corpus["schema_version"]) is not int
        or corpus["schema_version"] != 1
        or corpus["protocol"] != "classic S7 typed values and clock"
    ):
        raise ValueError("unsupported value corpus")
    total, ids = 0, set()
    for group, decode in (
        ("integer_cases", decode_integer),
        ("string_codec_cases", decode_string),
        ("clock_codec_cases", decode_clock),
    ):
        if not corpus[group]:
            raise ValueError("empty value case group")
        for test in corpus[group]:
            if test["id"] in ids:
                raise ValueError("duplicate value case identity")
            ids.add(test["id"])
            expected = dict(test["expected"])
            if "encoded" in expected:
                expected["encoded"] = octets(expected["encoded"])
            actual = decode(test)
            if actual != expected:
                raise AssertionError(f"{test['id']}: {actual!r} != {expected!r}")
            total += 1
    return total


def _check_checker(corpus: dict) -> None:
    for group in ("integer_cases", "string_codec_cases", "clock_codec_cases"):
        wrong = deepcopy(corpus)
        test = next(
            case for case in wrong[group] if case["expected"]["status"] == "accept"
        )
        test["expected"] = reject("synthetic-wrong-result")
        try:
            check(wrong)
        except AssertionError:
            pass
        else:
            raise AssertionError(f"value oracle missed wrong result in {group}")
    duplicate = deepcopy(corpus)
    duplicate["integer_cases"].append(duplicate["integer_cases"][0])
    try:
        check(duplicate)
    except ValueError:
        pass
    else:
        raise AssertionError("value oracle accepted duplicate identity")
    for version in (True, 1.0, 0, 2, "1"):
        invalid = {**corpus, "schema_version": version}
        try:
            check(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("value oracle accepted malformed schema version")
    for value in (True, 0, 0.0, "00", "-0", "+0", " 0", "0.0"):
        invalid = deepcopy(corpus)
        invalid["integer_cases"][0]["input_value"] = value
        try:
            check(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("value oracle accepted noncanonical integer input")
    if octets({"chunks": [{"bytes": [7, 7, 7]}]}) != octets(
        {"chunks": [{"repeat": {"byte": 7, "count": 3}}]}
    ):
        raise AssertionError("compact byte representation changed literal bytes")
    invalid_specs = [
        None,
        True,
        {},
        {"chunks": {}},
        {"chunks": [{"hex": "00"}]},
        {"chunks": [None]},
        {"chunks": [{"repeat": True}]},
        *({"chunks": [{"bytes": [value]}]} for value in (True, -1, 256)),
        *(
            {"chunks": [{"repeat": {"byte": value, "count": 1}}]}
            for value in (True, -1, 256)
        ),
        *(
            {"chunks": [{"repeat": {"byte": 0, "count": count}}]}
            for count in (True, -1, 1_000_001)
        ),
        {"chunks": [{"repeat": {"byte": 0}}]},
        {"chunks": [{"repeat": {"byte": 0, "count": 600_000}}] * 2},
    ]
    for spec in invalid_specs:
        try:
            octets(spec)
        except (TypeError, ValueError):
            pass
        else:
            raise AssertionError("value oracle accepted malformed compact byte input")
    for group in ("integer_cases", "string_codec_cases", "clock_codec_cases"):
        for field in ("encoded", "value"):
            wrong = deepcopy(corpus)
            test = next(
                case for case in wrong[group] if case["expected"]["status"] == "accept"
            )
            test["expected"][field] = (
                {"chunks": [{"bytes": [0x42]}]} if field == "encoded" else "wrong-value"
            )
            try:
                check(wrong)
            except AssertionError:
                pass
            else:
                raise AssertionError(f"value oracle missed wrong {field} in {group}")


def run(corpus_path: Path = DEFAULT_CORPUS) -> None:
    corpus = json.loads(corpus_path.read_text(encoding="utf-8"))
    total = check(corpus)
    _check_checker(corpus)
    print(f"{total}/{total} independent value corpus cases passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    run(parser.parse_args().corpus)
