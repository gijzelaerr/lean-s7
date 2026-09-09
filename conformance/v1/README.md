# Conformance corpus v1

Generate `s7.json` with `lake exe lean-s7-conformance s7`. The generator and
deterministic Lean tests validate the expectations before accepting the corpus.
CI compares generated output with the checked-in JSON.

All byte arrays in the S7 corpus are arrays of integers from 0 through 255.
Counts, offsets, and lengths are nonnegative integers. Offsets named
`byte_starts` are byte offsets, and `count` denotes elements unless explicitly
named `requested_bytes`. TPKT/COTP files retain their compact chunk encoding.

## Response cases

`operation` is `read` or `write`. `parameters` and `data` are S7 ACK_DATA
sections, not complete TCP packets. Wrap them in a successful ACK_DATA header
with accurate section lengths and the current request's reference. For reads,
request `requested_bytes` from DB 1 at byte zero. For writes, write that many
zero bytes. An accepted read must return exactly `expected.payload`; an accepted
write must report success (its expected payload is empty). A `reject` expectation
requires a protocol rejection, not a crash or accidental indexing exception.

## Chunk cases

Read `count` two-byte WORD elements from DB 1 at byte zero with the given
negotiated `pdu_bytes`. Each peer response supplies the requested element count,
with byte value `(byte_start + index) % 251`. Check request element counts,
byte offsets, response budgets, and the complete assembled payload.
`response_overhead_bytes` is the single-item S7 response overhead, excluding
TPKT/COTP. `expected_counts` and `expected_byte_starts` specify the greedy
chunk plan used by this model, not the only protocol-valid partition.

## Address cases

`address_cases` contains complete TPKT/COTP/S7 read-request packets. `start_bytes`
is Lean's API offset; `wire_address` is the literal 24-bit address field.
The five vectors contrast DB byte 16 with counter/timer starts 16 and 478.
Each requests two elements; these are isolated address checks, not a complete
multi-packet transaction. The second offset also represents 16 + 231 * 2 in the
native Snap7 chunk-start convention.

Run `python integration/addressing_conformance.py` with `tshark` installed to
dissect synthetic Ethernet/IPv4/TCP envelopes offline. The runner checks the raw
address and Wireshark's number-versus-byte interpretation, records its version,
and exits nonzero for mismatches. It does not use the python-snap7 emulator or
contact controllers. The separate `s7_conformance.py` checks the eight response,
chunk, and write cases; it does not run these five address cases.

Native Snap7 source agrees with the direct counter/timer address encoding.
Wireshark interprets these fields as counter/timer numbers. Neither establishes
that Lean's byte-offset API matches physical controller indexing. See the
[addressing investigation](../../reports/addressing-evidence-2026-09-09.md).

## Write cases

Write `count` WORD elements to DB 1 at byte zero through the multi-write API.
The peer returns a successful write item. Verify the complete request data payload
and its encoded bit length. A byte-based implementation may express the same
transfer as `count * element_bytes` BYTE elements.

Lean has no DB WORD override or Python ctypes interface. The WORD comparisons
validate shared element/byte arithmetic and payload preservation. They do not
claim equivalent APIs or prove the Python implementation. These cases were
motivated by the September 2026 audit; the audit's historical reproductions remain
separate because they intentionally assert the observed faulty behavior.
