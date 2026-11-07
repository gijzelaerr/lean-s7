# python-snap7 3.3.1 against the conformance corpus — 2026-11-02

Differential evidence from `python integration/python_snap7_consumer.py` against the
released python-snap7 3.3.1, with a classification of all 62 disagreements and 20
ambiguities. The reviewed result is `integration/python_snap7_baseline-3.3.1.json`.

Neither implementation is treated as the specification, and no case here has real-PLC
validation of the rejected behaviour. The evidence used is the six public captures already
replayed by `integration/real_captures.py`, the SHA-256-pinned native Snap7 revision
`30f37da3114024a71ba93f7fd855c680b97a406f`, python-snap7's own documentation, tests and
history, and direct probes of its codecs and clients.

| Result | 3.2.1 | 3.3.1 |
| --- | ---: | ---: |
| agree | 411 | 413 |
| gap | 85 | 85 |
| ambiguity | 2 | 20 |
| disagree | 82 | 62 |

Between the two versions, 23 disagreements became agreements (ten-byte clock, block-count
table length, block-info layout, last-data-unit values, and the null acknowledgements with
complete metadata). The other movements follow from those fixes. 18 cases moved from agree to
ambiguity: 3.2.1 rejected every ten-byte clock reply, so those rejections agreed vacuously.
3 cases moved from agree to disagree: `null-*-1`, which 3.2.1 also rejected vacuously because
it rejected every null acknowledgement.

## Classification

Each case gets one class, by this test: python-snap7 returns a wrong value or contradicts
itself (**bug**); it tolerates input that real traffic never shows, as native Snap7 also does,
with no wrong value (**leniency**); it made a documented, tested choice (**deliberate**); or
the corpus rejects or pins something no source requires (**lean-s7 stricter**). The appendix
lists every case.

| Class | Cases | Group |
| --- | ---: | --- |
| Bug | 6 | `clock-millisecond-low-bcd-10..15` |
| Leniency | 42 | `ff-*`: USER_DATA transport size not checked |
| Leniency | 8 | `*-incomplete`, `null-*-1`: last-data-unit ignored on single-response services |
| Leniency | 4 | `fragments-*-identity`: data-unit reference not compared across fragments |
| Leniency | 11 | `clock-weekday-*`, `clock-invalid-decoded-12/13`: weekday not validated |
| Deliberate | 5 | `wstring-*` above U+FFFF refused by the encoder |
| Deliberate | 1 | `mixed-read-odd-padding`: a failed item aborts the multi-read |
| lean-s7 stricter | 2 | `string-short-allocation`, `wstring-short-allocation` |
| lean-s7 stricter | 2 | `string-latin1-nul`, `string-maximum-padding`: padding bytes |
| lean-s7 stricter | 1 | `set-clock`: corpus weekday nibble |

### Bug: invalid millisecond digit becomes a plausible time (6 ambiguities)

`clock-millisecond-low-bcd-10..15` are labelled ambiguity with the detail "python-snap7
decodes no weekday or milliseconds". That detail is out of date: since
[#934](https://github.com/gijzelaerr/python-snap7/pull/934) `parse_get_clock_response` does
decode milliseconds. It runs `from_bcd` on every other digit but uses the last one unchecked
(`time_bytes[7] >> 4`), so `56 12 a3` decodes to `12:34:56.130` instead of being rejected.
The consumer's `visible_digits_valid` only covers `wire[2:8]`, so it does not see this.
python-snap7 contradicts its own BCD rule and returns a wrong value. The adapter is unchanged
here, so the baseline still records these six as ambiguity; this report's classification
takes precedence.

### Leniency: transport size (42 disagreements)

`ff-<group>-<sub>-<transport>-<length>` carries return code `0xff` with a transport size
other than `0x09`. All 131 successful USER_DATA replies in the captures use `ff 09`, so the
corpus rule matches observed traffic. Nothing shows that another value is an error, though:
the native client checks only the return code, and
[the USER_DATA evidence](userdata-evidence-2026-09-24.md) calls the Lean rule a
supported-profile decision. `_parse_data_section` enforces the exact length for each transport
size, and each service parser then checks its own payload size, so no wrong value was found.

### Leniency: last-data-unit on single-response services (8 disagreements)

`*-incomplete` (`ff 09`) and `null-*-1` (`0a 00 0000`) set the "more data follows" flag on a
service that never fragments. These are one behaviour, differing only in the acknowledgement
shape. They are new only in appearance: 3.2.1 rejected every null acknowledgement, and
[#940](https://github.com/gijzelaerr/python-snap7/pull/940) accepted the real shape without
also checking the flag. In the captures every clock, set-clock and block-info reply has the
flag clear (group 5 password services do not occur), and only SZL and block-list replies set
it. The native `opGetDateTime` and `opSetDateTime` ignore the flag.

The consumer tests only the envelope check. At the operation level `clock-incomplete` and
`block-info-incomplete` are still rejected, by the payload length checks, not the flag. A
complete 10-byte clock or 78-byte block-info with the flag set is returned whole, so nothing
is lost. The set-clock and password services report success, which is the one effect worth
hardening.

### Leniency: data-unit reference (4 disagreements)

`fragments-{3,4}-{0,81}-identity` change the data-unit reference on the third fragment.
python-snap7 never reads that field, and neither does the native client. All six fragmented
conversations in the captures keep it constant, and Wireshark keys reassembly on it, so the corpus
rule is reasonable, but only two-fragment conversations have been observed.

### Leniency: weekday (11 ambiguities)

`clock-weekday-0`, `clock-weekday-8..15` and `clock-invalid-decoded-12/13` differ only in a
weekday nibble outside 1–7. python-snap7 returns a `datetime` and never uses the nibble; the
returned date and time are right. The native client decodes it unchecked.

### Deliberate: supplementary characters in WSTRING (5 disagreements)

`set_wstring` refuses code points above U+FFFF with an explicit error, a changelog entry and
a Hypothesis test. The corpus encodes them as surrogate pairs counted as two units. No
Siemens document or controller capture was found that settles this, so the question stays
open and neither side is wrong on the evidence. The error text's claim that the PLC type does
not support them is equally unverified. `get_wstring` does decode a pair, so a value read from
a PLC may not be writable back.

### Deliberate: a failed multi-read item (1 disagreement)

`extract_multi_read_data` documents that it raises when any item fails, and fails closed: no
wrong data is returned. Native Snap7 instead records a per-item `Result`, and the corpus keeps
the good items. The only multi-item response in the captures has five successful items, so
real traffic does not settle this. It is an API decision and not a small fix: reporting per-item
failure changes what `read_multi_vars` returns, and the read optimizer merges items, so a bad
address also fails unrelated items and the error's item index refers to the merged block.

### lean-s7 stricter (5 cases)

**Short allocation.** The hazard in [the 3.2.1 report](python-snap7-3.2.1-2026-10-07.md)
(item 6, truncated values) was fixed by
[#945](https://github.com/gijzelaerr/python-snap7/pull/945), and `get_string([3,3,65])` now
raises. What remains is `[3,1,65,0]`: every character the current length declares is present
and the decoded `'A'` is correct, and only padding is absent. The consumer treats padding as
unspecified elsewhere, and `get_string`'s own docstring example uses this shape, which is what
a caller gets from reading fewer bytes than the declared capacity. Requiring the whole
allocation is a sound rule for lean-s7, but it is not protocol evidence.

**Padding.** `set_string` fills unused capacity with spaces and the corpus with zeros; only
those bytes differ. No source fixes them.

**`set-clock`.** The corpus input fixes weekday 3 for 2026-09-23, a Wednesday. python-snap7
derives 4, the Sunday = 1 value that the real captures confirm.

## python-snap7 bugs

Three bugs, one per proposed change. Only the first comes from the 82 cases; the other two came
up while checking them. None is filed.

1. **Clock millisecond digit is not validated** (above). Apply the BCD check to the last digit
   in `parse_get_clock_response`, which both clients share. Six cases would agree.
2. **USER_DATA follow-up replies are not correlated.** The follow-up loops in `read_szl` and
   `list_blocks_of_type`, in both clients, call `parse_response` directly and skip the PDU
   reference check that `_send_receive` applies. A probe of the synchronous
   `list_blocks_of_type` raises for a wrong reference on the first reply but appends a follow-up
   fragment with a wrong reference to the result. The other three loops have the same code but
   were read, not run. **The four `fragments-*-reference` cases agree only because the
   consumer's `assemble()` calls `validate_pdu_reference` itself**, so the corpus overstates
   python-snap7 here.
3. **`set_wchar` grows the caller's buffer.** A code point above U+FFFF encodes to four bytes
   and is assigned into a two-byte slice, so a 4-byte buffer becomes 6 bytes and every later
   field shifts by two. `set_wstring` already refuses these characters. No corpus case covers
   this.

Optional hardening, not bugs: reject last-data-unit 1 on single-response services (8 cases),
require transport size `0x09` (42 cases), compare the data-unit reference (4 cases).

## Consumer follow-ups

Two adapter corrections are left out so that this baseline records the existing adapter's
results: the stale clock detail and digit check, and `assemble()` validating references on
python-snap7's behalf. Correcting them changes recorded statuses and needs its own review.
`.github/workflows/real-captures.yml` also still installs 3.2.1.

## Checks

`integration/python_snap7_fuzz.py` against 3.3.1 reports no accepted-but-different values.
`integration/real_captures.py` under 3.3.1 keeps every lean-s7 check green. The consumer passes
with the reviewed baselines for 3.0.0 and 3.3.1. The native-endpoint checks were not run because
no wire format or endpoint behaviour changed.

## Appendix: every case

| Case | Consumer status | Class | Group |
| --- | --- | --- | --- |
| `management.json/continuation_cases/fragments-3-0-identity` | disagree | Leniency | data-unit reference |
| `management.json/continuation_cases/fragments-3-81-identity` | disagree | Leniency | data-unit reference |
| `management.json/continuation_cases/fragments-4-0-identity` | disagree | Leniency | data-unit reference |
| `management.json/continuation_cases/fragments-4-81-identity` | disagree | Leniency | data-unit reference |
| `management.json/decoder_cases/ff-3-2-0-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-3-2-0-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-3-2-10-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-3-2-255-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-3-2-4-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-3-2-7-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-3-2-7-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-4-1-0-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-4-1-0-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-4-1-10-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-4-1-255-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-4-1-4-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-4-1-7-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-4-1-7-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-1-0-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-1-0-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-1-10-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-1-255-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-1-4-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-1-7-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-1-7-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-2-0-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-2-0-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-2-10-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-2-255-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-2-4-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-2-7-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-5-2-7-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-1-0-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-1-0-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-1-10-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-1-255-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-1-4-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-1-7-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-1-7-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-2-0-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-2-0-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-2-10-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-2-255-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-2-4-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-2-7-0` | disagree | Leniency | transport size |
| `management.json/decoder_cases/ff-7-2-7-2` | disagree | Leniency | transport size |
| `management.json/decoder_cases/null-5-1-0-0-1` | disagree | Leniency | last-data-unit |
| `management.json/decoder_cases/null-5-2-0-0-1` | disagree | Leniency | last-data-unit |
| `management.json/decoder_cases/null-7-2-0-0-1` | disagree | Leniency | last-data-unit |
| `operations.json/single_userdata_cases/block-info-incomplete` | disagree | Leniency | last-data-unit |
| `operations.json/single_userdata_cases/clear-password-incomplete` | disagree | Leniency | last-data-unit |
| `operations.json/single_userdata_cases/clock-incomplete` | disagree | Leniency | last-data-unit |
| `operations.json/single_userdata_cases/set-clock-incomplete` | disagree | Leniency | last-data-unit |
| `operations.json/single_userdata_cases/set-password-incomplete` | disagree | Leniency | last-data-unit |
| `s7.json/multi_item_cases/mixed-read-odd-padding` | disagree | Deliberate | failed multi-read item |
| `s7.json/request_cases/set-clock` | ambiguity | lean-s7 stricter | corpus weekday |
| `values.json/clock_codec_cases/clock-invalid-decoded-12` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-invalid-decoded-13` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-millisecond-low-bcd-10` | ambiguity | Bug | unchecked millisecond digit |
| `values.json/clock_codec_cases/clock-millisecond-low-bcd-11` | ambiguity | Bug | unchecked millisecond digit |
| `values.json/clock_codec_cases/clock-millisecond-low-bcd-12` | ambiguity | Bug | unchecked millisecond digit |
| `values.json/clock_codec_cases/clock-millisecond-low-bcd-13` | ambiguity | Bug | unchecked millisecond digit |
| `values.json/clock_codec_cases/clock-millisecond-low-bcd-14` | ambiguity | Bug | unchecked millisecond digit |
| `values.json/clock_codec_cases/clock-millisecond-low-bcd-15` | ambiguity | Bug | unchecked millisecond digit |
| `values.json/clock_codec_cases/clock-weekday-0` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-10` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-11` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-12` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-13` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-14` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-15` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-8` | ambiguity | Leniency | weekday |
| `values.json/clock_codec_cases/clock-weekday-9` | ambiguity | Leniency | weekday |
| `values.json/string_codec_cases/string-latin1-nul` | ambiguity | lean-s7 stricter | padding |
| `values.json/string_codec_cases/string-maximum-padding` | ambiguity | lean-s7 stricter | padding |
| `values.json/string_codec_cases/string-short-allocation` | disagree | lean-s7 stricter | short allocation |
| `values.json/string_codec_cases/wstring-first-astral` | disagree | Deliberate | WSTRING above U+FFFF |
| `values.json/string_codec_cases/wstring-last-scalar` | disagree | Deliberate | WSTRING above U+FFFF |
| `values.json/string_codec_cases/wstring-maximum-padding` | disagree | Deliberate | WSTRING above U+FFFF |
| `values.json/string_codec_cases/wstring-mixed-padding` | disagree | Deliberate | WSTRING above U+FFFF |
| `values.json/string_codec_cases/wstring-short-allocation` | disagree | lean-s7 stricter | short allocation |
| `values.json/string_codec_cases/wstring-surrogate-pair` | disagree | Deliberate | WSTRING above U+FFFF |
