# python-snap7 3.2.1 against the conformance corpus — 2026-10-07

Differential evidence from `python integration/python_snap7_consumer.py` against
python-snap7 3.2.1 (released after the [3.0.0 report](python-snap7-consumer-2026-10-06.md)),
extended from 98 to 467 cases: TPKT, COTP data, S7 requests/responses, upload
fragments, multi-item reads, USER_DATA and management codecs, block counts/lists/info,
the clock codec, word writes, and integer/STRING/WSTRING values.

Each finding below states its evidence. python-snap7 is not the specification: only
items marked **native-confirmed** or **self-inconsistent** are bugs by an independent
or internal standard; the rest are leads or policy differences. The native source is
the SHA-256-pinned official Snap7 revision `30f37da3114024a71ba93f7fd855c680b97a406f`
already used by `integration/native_snap7_build.py` (file and symbol names below refer
to it). Issues for the evidence-backed bugs were filed afterwards (see the end).

| 3.2.1 result | Cases |
| --- | ---: |
| agree | 385 |
| disagree | 68 |
| gap (no API expresses the case) | 12 |
| ambiguity (only unspecified padding differs) | 2 |

Compared with 3.0.0 (same adapters; reviewed baselines for both versions are in
`integration/python_snap7_baseline-<version>.json`): 145 cases that disagreed in 3.0.0
now agree and none regressed. The leads from the earlier report that
are fixed in 3.2.1: read-response length/function validation, upload fragment
validation (marker, length, flag, function) and the two-byte fragment drop, the COTP
header-length and TPDU-number checks, the TPKT minimum, and the WSTRING current length
for supplementary characters (which is now handled by rejecting them, see 7). 19
earlier disagreements remain, and newly mapped areas add 49.

## Bugs with independent or internal evidence

1. **`set_wstring` writes values `get_wstring` rejects (self-inconsistent).** Any
   capacity of 8192 characters or more, up to the documented 16382, round-trips with a
   `TypeError`: `get_wstring` doubles the declared maximum and compares it with 16382
   (characters versus bytes). Repro:
   `b = bytearray(40000); set_wstring(b, 0, "a", 16382); get_wstring(b, 0)` raises. The
   self-consistency probe found this and nothing else among integers, STRING, REAL,
   LREAL, BOOL, DATE, TOD, DTL, DT, CHAR and WCHAR.
2. **Clock weekday uses ISO numbering (native-confirmed).** `build_set_clock_request`
   writes `dt.weekday() + 1`, i.e. Monday = 1. S7 DATE_AND_TIME and native Snap7 use
   Sunday = 1: `s7_micro_client.cpp` stores `Time[7] = DateTime->tm_wday + 1` and reads
   `tm_wday = (Time[7] & 0x0F) - 1`, and C's `tm_wday` is Sunday = 0. Every
   `set_plc_datetime` call is off by one day of the week (all seven cases checked).
3. **Clock read expects 8 bytes, the wire form is 10 (native-confirmed).**
   `parse_get_clock_response` requires exactly eight data bytes. Native Snap7's
   `TResDataGetTime` is `Rsvd`, `HiYear`, `Time[8]` (ten bytes, `s7_types.h`), python-snap7's
   own `build_set_clock_request` emits ten bytes, and the corpus uses ten. A native
   server or a PLC reply is rejected ("must contain exactly eight bytes"); the bundled
   emulator answers with eight, which hides this. The Lean client rejects that
   emulator's clock reply for the same reason (`clock payload must contain 10 bytes,
   got 8`).
4. **Out-of-range years wrap into another century (internal evidence).**
   `build_set_clock_request` encodes `year % 100`, so 1989 and 2090 are accepted and
   decoded by a PLC as 2089 and 1990; the S7 two-digit year only spans 1990–2089.
5. **`build_get_block_info_request` has the wrong field order (native-confirmed).** It
   sends `"0" "A" "A" "00001"`; native `TReqDataBlockInfo` is `BlkPrfx(0x30)`,
   `BlkType`, `AsciiBlk[5]`, then the constant `A` (`s7_types.h`): `"0" "A" "00001" "A"`.
   The corpus carries the native layout (lean-s7 fixed the same mistake earlier, see
   [the block-management report](block-management-2026-09-24.md)). The request is
   therefore malformed for an endpoint that follows the native layout (not exercised here);
   the bundled emulator parses python-snap7's own layout.

## Leniency leads (malformed input accepted)

Each needs independent evidence about what a real controller may legitimately send
before it is called a defect.

6. **Short storage is accepted.** `get_string([3,3,65])` and `get_wstring` return a
   truncated value when the buffer ends before the declared allocation
   (`string-short-allocation`, `wstring-short-allocation`). A malformed or cropped
   buffer yields a plausible but wrong string.
7. **Supplementary characters are rejected.** `set_wstring` now refuses code points
   above U+FFFF (an explicit, documented policy), whereas the corpus encodes them as
   UTF-16 surrogate pairs counted as two units (four cases). This is a policy
   difference: Siemens documents WSTRING as UTF-16, but the behavior of a PLC with
   surrogate pairs was not verified here.
8. **USER_DATA data transport size is not validated (42 management cases).** With a
   success return code, any transport size (0, 4, 7, 0x0a, 0xff) and several data
   lengths are accepted for SZL, block-list, clock and security responses; the corpus
   requires the octet-string size 0x09.
9. **USER_DATA last-data-unit values other than 0 and 1 are accepted** (`2` and `0xff`:
   three cases). Wireshark and the native client treat the field as a flag.
10. **Duplicate block types in a block-count response silently overwrite** earlier counts
    (two cases, including identical counts), so a malformed reply can change a count.
11. **A failed item aborts the whole multi-read.** `extract_multi_read_data` raises when
    any item has an error code, discarding later successful items (the corpus keeps
    them). This is an API design difference as much as a leniency.
12. **Native null acknowledgements are rejected.** Password set/clear and clock-set
    acknowledgements that carry no data (three management cases) are rejected, while the
    corpus accepts them as native Snap7 produces them (see
    [the USER_DATA evidence](userdata-evidence-2026-09-24.md)).

## API gaps (not disagreements)

No standalone TPKT decoder and no COTP end-of-transmission flag (three cases), no signed
64-bit encoder (three), no multi-variable write builder (three), no
`request_db_download` builder with explicit sizes (one), and no way to supply an
explicit weekday (two).

## Emulator observations

Against the 3.2.1 emulator the Lean CLI can read DBs and list/describe blocks and decode
the order-code SZL, but CPU-info SZL has a record header describing zero data bytes
for a 206-byte payload, CPU state returns an item error, and the clock reply is eight
bytes. The emulator is therefore not a faithful independent S7 endpoint for those
services; the native Snap7 endpoint and scripted peers remain the evidence for them.

## Upstream issues

Filed on 2026-10-07: 1 as [#923](https://github.com/gijzelaerr/python-snap7/issues/923),
2 as [#924](https://github.com/gijzelaerr/python-snap7/issues/924), 3 as
[#925](https://github.com/gijzelaerr/python-snap7/issues/925), 4 as
[#926](https://github.com/gijzelaerr/python-snap7/issues/926), 5 as
[#927](https://github.com/gijzelaerr/python-snap7/issues/927). Differential fuzzing added
[#930](https://github.com/gijzelaerr/python-snap7/issues/930) (header error code) and
[#931](https://github.com/gijzelaerr/python-snap7/issues/931) (block-count table length),
see [the fuzzing report](python-snap7-fuzz-2026-10-07.md). Items 6 and 8-12 are hardening
leads and are not filed.
