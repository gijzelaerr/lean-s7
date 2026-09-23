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

## USER_DATA cases

`userdata_cases` contains complete S7 USER_DATA response PDUs. Decode each PDU
for the specified function group and subfunction. Accepted cases expose the
exact payload, sequence number, and continuation flag. Rejected cases cover a
wrong group or subfunction, USER_DATA and item error codes, truncated declared
payloads, invalid continuation flags, and trailing bytes. A rejection must occur
while parsing or validating
the response rather than through unchecked indexing.

## Upload cases

`upload_cases` contains complete S7 ACK_DATA PDUs for block-upload fragments.
Accepted cases expose the exact fragment payload and end-of-upload flag.
Rejected cases cover an invalid data marker, inconsistent declared length,
invalid continuation flags, and the wrong service function. These are
fragment-codec cases; they do not claim that a controller contains or serves a
particular block.

## Request cases

`request_cases` contains complete management, CPU-control, and block-transfer
request PDUs generated with reference 1. Consumers should build the named
operation from a fresh protocol session and compare the complete packet.

## Block-count cases

`block_count_cases` contains raw list-blocks response payloads. Duplicate type
records reject rather than silently overwriting a count, even when their counts
are identical. Accepted cases
must expose the seven typed counts exactly; rejected cases cover truncation,
trailing bytes, and an unknown block type.

`block_list_cases` contains raw list-blocks-of-type response payloads. Accepted
cases expose ordered block numbers, flags, and language codes; rejected cases
cover partial four-byte records.

`block_info_cases` contains raw 78-byte block-metadata response payloads with
typed size, identity, date, and text fields. Both truncation and trailing bytes
must be rejected.

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
contact controllers. The separate `s7_conformance.py` checks response,
USER_DATA, upload, request, chunk, and write cases; it does not run these five address
cases.

Native Snap7 source agrees with the direct counter/timer address encoding.
Wireshark interprets these fields as counter/timer numbers. Neither establishes
that Lean's byte-offset API matches physical controller indexing. See the
[addressing investigation](../../reports/addressing-evidence-2026-09-09.md).

## Multi-item and USERDATA conversations

`multi_item_cases` pairs complete S7 `request_pdu` and `response_pdu` octet arrays,
reference 1, and ordered DB ranges. These are unframed S7 PDUs (no TPKT/COTP).
An accepted response's `items` preserve caller order: success, PLC item failure
code 5, success. Read payloads are respectively `[170]` and `[187, 204]`;
the odd first payload requires an inter-item padding byte. Missing padding,
trailing response bytes, and missing/trailing write statuses must reject.
An item-level PLC error is not a malformed packet and must not discard later
successful items.

`userdata_conversation_cases` supplies ordered, complete S7 `response_pdus`,
the expected reference/group/subfunction, and explicit assembly byte/fragment
bounds. Decode each response, append its payload in order, and stop only at
the final-fragment flag. Empty continuations consume a fragment slot. Reject
payload overflow, a continuation exhausting the fragment limit, any fragment
after completion, and a conversation that ends before completion. These cases
exercise bounded assembly, not request scheduling, retry policy, or validation
of sequence/reference changes between fragments.

The exporter checks fixed expectations against the actual decoders and assembly
function before producing JSON. Run `python integration/sequence_conformance.py`
to independently decode both sections using a strict standard-library-only
byte-level oracle. It checks request ranges as well as ordered response results
and bounded continuation assembly. This oracle does not validate python-snap7.

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

## Operation regressions

Generate `operations.json` with `lake exe lean-s7-conformance operations`. The
exporter first checks fixed expectations against the actual value codecs,
USER_DATA decoder/completion guard, retry policy, and write-progress state model.
Run `python integration/operation_conformance.py` for an independent strict
standard-library-only oracle. All bytes are integer arrays, not hex strings.

`string_read_cases` pairs `initial_header` from the first DB read with `body`
from the second read of the originally advertised storage capacity. These are
assembled value bytes, not S7 or TCP packets. STRING uses Latin-1 and two
one-byte length fields; WSTRING uses UTF-16BE and two big-endian two-byte length
fields. Capacity must remain unchanged between reads, while current length may
change. Expected negative categories distinguish `initial-header`,
`capacity-changed`, and `value-codec`. The guard model mirrors the client check
and invokes its actual value codecs; it does not establish atomic PLC snapshots,
network scheduling, operation deadlines, or thread serialization.

`single_userdata_cases` supplies complete unframed S7 response PDUs for fixed
single-response services. Validate the reference/group/subfunction and PDU
extent before requiring a zero continuation flag. Categories distinguish
`pdu-validation` from `incomplete-single-response`. A syntactically valid first
fragment must still reject, including an empty password/clock acknowledgement.
Acceptance exposes only the guarded payload; service-specific clock or block
metadata interpretation is outside these vectors. Segmented SZL/block-list
services use the separate conversation corpus and must not use this guard.

`retry_policy_cases` specifies operation replay permission, not whether a
particular error triggers a retry: reads permit replay, potentially mutating
operations require an explicit opt-in. Actual attempt counts, reconnects,
compound-operation replay suppression, and remote side effects remain network
integration concerns.

`write_progress_cases` supplies ordered pure events (`send`, `acknowledge`,
`replay`, `global-reject`). Each location retains the memory range, original
multi-item `item_index` (null for scalar), and `chunk_byte_offset` in bytes within
the caller payload. Duplicate memory ranges are distinct caller items. A replay
retains the earlier unacknowledged attempt as `replayed-unknown`; a later success
or rejection cannot retroactively establish its remote outcome. Expected traces
preserve chronological order and specify counts for acknowledged, globally
rejected, replay-uncertain, and currently uncertain attempts. Item failure code 5
is an acknowledged item result, not a global rejection. Successful prefixes
are not an atomic transaction or rollback guarantee.

The Python oracle is independent conformance evidence, not a formal proof of
Python source or a test of python-snap7. These vectors require no controller and
do not establish physical PLC compatibility.
