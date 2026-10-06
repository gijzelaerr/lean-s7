# python-snap7 consumption of the conformance corpus — 2026-10-06

Differential evidence from `python integration/python_snap7_consumer.py` against
python-snap7 3.0.0 (the pinned version). Cases are classified `agree`, `gap` (no
python-snap7 API expresses the case), `ambiguity` (only protocol-unspecified bytes
differ) or `disagree`. The reviewed classification of every case is in
[`integration/python_snap7_baseline.json`](../integration/python_snap7_baseline.json);
the run fails if any case changes status.

**This is a lead list, not a verdict.** python-snap7 behavior is not the protocol
specification and neither is lean-s7. A disagreement needs independent evidence
(protocol documentation, native Snap7 source, captures) before deciding which side
is wrong. A pass is differential evidence for those inputs only, not a proof of
python-snap7's source. Nothing here has been reported upstream yet.

Scope of this first pass: TPKT, COTP data, S7 read/write response and upload-fragment
cases, and integer/STRING/WSTRING value cases (98 cases). Management, conversations,
sessions, operations and the S7 request/multi-item/block-metadata arrays are not yet
mapped.

| Result | Cases |
| --- | ---: |
| agree | 69 |
| disagree | 21 |
| gap | 6 |
| ambiguity | 2 |

The loader lives in this repository for now (it needs only the corpus and the pinned
package, and keeps python-snap7 out of the Lean build). It can move to python-snap7's
test suite once the cases it exposes are triaged there.

## API gaps (not disagreements)

- python-snap7 has no standalone TPKT decoder: `receive_data()` composes TPKT, a
  socket stream and the COTP data header, so `tpkt decode maximum-valid` (payload is
  not a COTP TPDU) cannot be expressed.
- `_build_cotp_dt` always sets the end-of-transmission bit and `_parse_cotp_data` does
  not expose it: the two `segmented-data` COTP cases cannot be expressed.
- No signed 64-bit encoder in `snap7.util.setters` (decoders agree): three `int64` cases.

## Leads for independent confirmation

Each group names the python-snap7 function and the corpus cases involved. "Corpus
requires" is lean-s7's current behavior.

1. **COTP data decoder ignores header fields.** `ISOTCPConnection._parse_cotp_data`
   accepts a wrong header-length byte (`invalid-header-length`) and a nonzero TPDU
   number (`nonzero-tpdu-number`). Evidence to gather: ISO 8073 class 0 DT header
   (length indicator 2, TPDU number 0 for class 0).
2. **Read responses are not checked against the request or their own lengths.**
   `S7Protocol.extract_read_data` returns whatever bytes are present: a truncated
   read, a declared length shorter than the data, trailing bytes, and a write
   acknowledged by a read-shaped response are all accepted (`truncated-read`,
   `short-declared-read`, `trailing-read-data`, `write-answered-by-read`). A truncated
   read returns fewer bytes than requested without an error. This extends
   [the September audit](python-snap7-audit-2026-09-08.md).
3. **Upload fragments are not validated, and short ones are dropped.**
   `S7Protocol.parse_upload_response` ignores the `0x00fb` marker, declared length,
   continuation flag and function code (`upload-invalid-marker`,
   `upload-length-mismatch`, both continuation-flag cases, `upload-wrong-function`)
   and returns an empty result for any fragment of two bytes or fewer
   (`last-upload-fragment`; a three-byte fragment is returned, checked directly). Reading
   `Client.upload` also shows a single UPLOAD request with no continuation loop;
   that observation is from source reading, not from a corpus case.
4. **WSTRING length is counted in code points, not UTF-16 units.** `set_wstring`
   stores `len(value)`; the corpus (and S7 WSTRING semantics: 16-bit WCHARs) count
   units, so any character outside the BMP is encoded with a wrong current length
   (`wstring-surrogate-pair`, `wstring-first-astral`, `wstring-last-scalar`,
   `wstring-mixed-padding`) and `wstring-unit-overflow` is accepted instead of
   rejected. Needs a PLC-side or Siemens-documentation reference for the unit.
5. **WSTRING maximum.** `get_wstring` multiplies the declared maximum by two before
   comparing with 16382 (bytes versus characters), so a legal maximum capacity of
   16382 characters is rejected (`wstring-maximum-padding`); a declared maximum of 8191
   is accepted and 16382 raises `TypeError` (checked directly).
6. **Short storage is accepted.** `get_string` / `get_wstring` return a value when the
   buffer ends before the declared allocation (`string-short-allocation`,
   `wstring-short-allocation`). This is a lean-s7 policy (require the whole declared
   storage) and may be a design choice for a codec that reads from a larger buffer.
7. **TPKT encoder minimum.** `_build_tpkt` accepts a payload below the COTP minimum
   (`below-minimum`). The corpus rejects it as `frame-too-small`; this is lean-s7's
   stricter policy, needing an RFC 1006 reading before either side is called wrong.

## Ambiguity

`set_string` pads unused capacity with spaces; the corpus pads with zero bytes
(`string-latin1-nul`, `string-maximum-padding`). The S7 STRING has no defined content
beyond the current length, so this is a representation difference, not a defect.

## Next steps (need a decision)

- python-snap7 is the maintainer's project: draft and file one focused issue per
  group above (2, 3, 4/5, 1) once each has independent evidence, cross-referencing
  the September audit. Nothing has been filed.
- Extend the adapters to management, conversations, sessions and the remaining S7
  arrays; python-snap7's `parse_read_szl_response`, clock and block-info helpers are
  the likely targets.
