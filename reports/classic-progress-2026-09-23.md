# Classic S7 emulator-only assurance — 2026-09-23

## Scope

Continued classic S7 client assurance without access to a physical PLC. Evidence
comes from Lean proofs and deterministic tests, generated conformance vectors,
the pinned python-snap7 3.0.0 emulator, and focused scripted TCP peers. None of
this substitutes for controller-family and firmware validation.

## Implemented

- Added five live-stack negotiation rejection cases for wrong COTP reference,
  transport class, excessive TPDU size, undersized S7 PDU, and an S7 PDU that
  exceeds the negotiated COTP payload budget.
- Extended the S7 corpus from 8 to 48 response, USER_DATA, upload, request,
  chunk, and write cases, alongside the five separate addressing vectors.
- Added malformed USER_DATA cases for wrong group/subfunction, USER_DATA and
  item errors, truncated declared payloads, and trailing payload bytes.
- Added valid and malformed upload-fragment cases, including the final-fragment
  flag, marker validation, declared length, and service-function validation.
- Added nine complete request vectors for clock read, block listing, CPU
  control, and the upload start/fragment/end lifecycle.
- Added fixed clock-setting, password, block-info, and PLC-driven download
  request/response vectors plus strict block-count response cases.
- Added typed block-list and block-metadata response vectors and fixed the Lean
  block-info decoder to reject trailing bytes after its 78-byte structure.
- Added live adversarial SZL and upload peers. They exercise wrong USER_DATA
  groups, truncated payloads, the 256-fragment limit, invalid upload markers,
  inconsistent lengths, wrong functions, and end-upload cleanup after failure.
- Added a PLC-driven download peer that closes between fragments; the client
  reports a structured disconnected error and leaves the connected state.
- Added the equivalent USER_DATA continuation interruption case for fragmented
  block lists.
- Added `DecodeError.remoteFailure` and `ClientErrorKind.plcRejected`, keeping
  PLC-declared failures distinct from malformed packets without message parsing.
- Added deterministic PDU-reference wraparound coverage: a scripted peer checks
  correlated requests at references 65535 and 0.
- Restricted reconnect retries to timeout, disconnect, and transport failures;
  malformed responses, PLC rejections, lifecycle errors, and invalid input are
  never automatically resent. Scripted peers verify that neither a PLC rejection
  nor a stale-response protocol failure opens a second TCP session with retries enabled.
- Replaced the old stale-response reconnect fixture with a two-session transport
  drop/recovery peer that verifies the original request is retried byte-for-byte.
- Split request/value encoding failures into the `invalidInput` category and
  reject raw exchanges whose supplied reference differs from the encoded PDU.
- Added pinned Python lint and formatting checks to CI.
- Reject reconnects that negotiate a smaller S7 PDU than the session whose
  already-planned request is being retried.
- Extended `CoreProtocolAssurance` with explicit TPKT round trips, USER_DATA
  size/reference properties, response-function validation, download-fragment
  size, and transport-closure safety.
- Proved the exact encoded size of PLC-driven download-fragment responses.

## Differential result

python-snap7 3.0.0 passes 10 of the 48 S7 corpus cases. The 38 divergences include
the previously recorded read/write/chunking issues plus acceptance of malformed
USER_DATA metadata and payload lengths, acceptance of malformed upload markers
and lengths, omission of a valid two-byte final upload payload, and fifteen
request/response differences or unsupported operations across block listing,
CPU control, clock setting, block metadata, password handling, and the
upload/download lifecycle.
These are cross-implementation observations, not formal claims about the Python source.

## Validation

- Clean build of `lean-s7`, `lean-s7-tests`, and `lean-s7-conformance`.
- All deterministic Lean tests passed.
- TPKT, COTP, and S7 generated corpora match the checked-in artifacts.
- Full python-snap7 3.0.0 emulator integration suite passed.
- Python lint, formatting, and whitespace checks passed.

## Blocked boundaries

- Socket sends remain unbounded: the current Lean async TCP API exposes receive
  cancellation but no cancellable send or immediate socket-close primitive;
  deterministic send-cancellation coverage depends on such a primitive.
- Physical counter/timer indexing and all real-controller service semantics
  remain unresolved without hardware or captures.

## Download-service validation follow-up

- The Lean client now requires the exact PLC-driven download service parameters:
  function, seven reserved bytes, and the addressed block type and number. It
  rejects an unexpected data section for both fragment and completion jobs.
- Request-download acknowledgements must contain exactly the one-byte service
  function and no data before the client sends any fragment.
- The scripted peer now uses full service requests and checks malformed
  acknowledgements, wrong block numbers, nonzero reserved bytes, truncated
  parameters, and unexpected data. These are emulator-independent rejection
  checks, not evidence of behavior on a physical controller.

## Download phase assurance follow-up

- Added a pure download state machine used by the client for acknowledgement,
  fragment, and completion transitions. Fragment plans contain proof witnesses
  for progress and the negotiated PDU slice bound.
- Proved that each accepted fragment extends exactly the previously sent prefix,
  that no fragment or completion occurs before acknowledgement, that incomplete
  transfers cannot complete, and that encoded responses fit their PDU budget.
  These properties are part of `CoreProtocolAssurance`.
- Scripted peers reject an early download-ended request and an extra fragment
  request after the complete block has been sent. The resulting client error is
  a protocol failure and the transport is closed.
- The successful scripted transfer now runs at both 240- and 480-byte
  negotiated S7 PDU sizes and checks every fragment response against that limit.

## Upload assembly assurance follow-up

- Added a pure upload state machine used by the client. Its bounded accumulator
  checks the cumulative size before appending a fragment. Proofs of byte order,
  cumulative bounds, continuation progress, and exact declared size at completion
  are included in `CoreProtocolAssurance`.
- Enforced the PLC's declared upload length, rejected continuation flags other
  than 0 or 1, and rejected empty continuation fragments. No block data is returned
  until a valid END_UPLOAD acknowledgement. Rejected uploads attempt cleanup
  with the validated upload ID, then close the transport.
- Start-upload replies accept the canonical 16-byte parameters and the explicit
  legacy eight-byte form without a declared length; other sizes, unexpected data,
  and invalid ASCII length digits are rejected. The decimal decoder uses the
  bounded cursor rather than panicking indexing.
- Added two invalid-flag corpus vectors, bringing the S7 corpus to 50 cases.
  Added scripted peers for invalid flags, no progress, early termination,
  declared-length overflow across fragments, continuation at the declared end,
  and malformed END_UPLOAD acknowledgements on success and cleanup paths.
- Validation passed: clean build, all Lean tests, generated corpus comparisons,
  full pinned python-snap7 3.0.0 integration suite, and Python lint/format checks.

## Parallel transfer and batching assurance follow-up

- Added a pure SZL/USER_DATA accumulator with pre-append byte and fragment
  checks, ordered assembly, count progress, completion tracking, and proofs
  that continuing replies leave an available fragment slot. Empty metadata
  fragments remain valid. The client closes failed transfers, including final
  record/entry decoding failures.
- Added a configurable absolute upload/SZL/segmented USER_DATA receive deadline
  (30 seconds by default), shared across continuations, retries, and cleanup.
  Per-exchange limits remain active; disabling the transfer budget does not
  disable those limits. Sends and connection establishment remain outside the
  cancellation guarantee.
- Actual multi-item client loops now use proof-carrying planner certificates
  for ordered partitioning, item count, and both PDU budgets. Added positive
  read-count and exact write-payload properties to the core assurance contract.
  Executable tests check actual encoder accounting and mixed return-code order;
  these tests are not an encoder-correspondence theorem.
- Added deterministic mutation testing over valid corpus seeds. The initial
  2,636 checks found acceptance of USER_DATA continuation flag 2; values other
  than 0 and 1 are now rejected, with two focused corpus regressions (52 S7
  cases). The supported flag values are independently corroborated by the
  [Wireshark S7 dissector's `userdata_lastdataunit_names` definitions](https://github.com/wireshark/wireshark/blob/master/epan/dissectors/packet-s7comm.c).
- Independent peer checks passed: 19 deadline scenarios across all three
  transfer kinds, and four 41-item read/write batching scenarios at 240/480-byte
  PDU sizes with one- and 37-byte payloads and interleaved PLC failures.
- Combined validation passed: clean build, all Lean tests, all three generated
  corpus comparisons, Ruff lint/format, whitespace checks, and the full pinned
  python-snap7 3.0.0 emulator/scripted-peer suite. No real-controller
  compatibility claim is made.

## Extended assurance workstreams

- Implemented logical-range and whole-request write validation before any
  multi-item IO, without imposing the wire packet's 16-bit count limit on
  chunkable logical transfers. Late invalid payloads, areas/DB numbers, and
  final addresses are covered by no-write peers.
- Oversized multi-item transfers now use singleton multi-item decoders for each
  chunk, returning the original PLC item failure code, skipping the failed
  item's remaining chunks, and preserving later item/result order. Successful
  write chunks preceding a PLC rejection remain written; this is not atomic.
- Extended absolute receive budgets to scalar chunked reads/writes, multi-item
  calls, and PLC-driven downloads including final insertion acknowledgement.
  Automatic reconnect retries are restricted to the initial exchange, avoiding
  restarted partially completed transfers.
- Added checked encoder/planner correspondence: actual read requests have
  exactly the planned parameter size; actual write requests fit the conservative
  planned size including inter-item padding. Both planned request-size theorems
  are included in `CoreProtocolAssurance`.
- Added 5,960 expanded mutation/sequence checks, including every bit position,
  mixed multi-item replies, block counts/metadata/lists, clocks, STRING/WSTRING,
  and continuation sequences. These found silent overwriting of duplicate
  block-count types; ambiguous duplicates now reject, with two new corpus cases
  (54 S7 cases).
- Combined validation passed: clean build, all Lean tests, all three corpus
  comparisons, Ruff lint/format, whitespace checks, the full pinned emulator
  suite, and the expanded successful-oversized-transfer peer checks. Sends and
  connection establishment remain outside cancellation guarantees; no
  physical-controller claim is made.
- The final wire-length audit also caught large-PDU planning that could exceed
  the 16-bit bit-length field despite fitting the PDU budget. Byte-transport
  reads/writes now chunk beyond 8,191 payload bytes; octet transport uses its
  byte-length bound. Planner certificates prove representable selected lengths,
  with exact-boundary and fallback tests included.
- Independent new peer checks passed: 18 oversized-item success/failure/prevalidation
  scenarios at PDU sizes 240/480 and 34 extended deadline/prevalidation scenarios,
  including spent-budget reconnect and continuation-no-retry checks.

## Operation safety and conversation assurance

- Five follow-up items are being implemented in parallel: operation-aware
  retries, concurrency/lifecycle peers, structured write progress, stateful
  fault conversations, and broader value-codec proofs/conformance scenarios.
- Retry and write-progress changes share an owner because they affect the
  same client failure paths. Mutation/control/raw operations will not replay
  automatically without explicit opt-in; session-allocating upload start is
  treated conservatively too.
- New exhaustive short conversations compare the production upload, download,
  and USER_DATA state machines to independent arithmetic/phase oracles at each
  accepted prefix. Independent peers inject disconnects and wrong services at
  each upload and segmented SZL receive phase.
- New concurrency peers use process barriers rather than timing guesses. After
  correcting a Python peer framing assumption, the queued-failure test exposed
  a real client defect: service-specific read decoding could fail after the
  cleanup boundary without closing the session. The fix retains the gate
  through typed read, USER_DATA, control-service, and SZL projection validation.
- Codec work adds actual surrounded WORD/INT round-trip theorems and narrowly
  stated floating-point bit interpretation theorems, plus mixed multi-item and
  continuation corpus conversations. Focused tests passed for 31,310 stateful
  conversations, all 65,536 WORD/INT values, 20 upload/SZL wire faults, and 12
  independently decoded corpus conversations. Final combined checks remain pending.
- The combined clean build passed all 82 jobs; the complete Lean test suite,
  generated TPKT/COTP/S7 corpus comparisons, Python lint/format, and whitespace
  checks passed. The full pinned emulator suite is now running with all new
  peers wired in. No commit or push has been made for this follow-up.
- Independent review found a write-progress edge case under explicit replay
  opt-in: a validated rejection of the replay must not erase uncertainty about
  an earlier attempt whose acknowledgement was lost. Earlier-attempt uncertainty
  is being retained separately, with replay-then-rejection regression peers.
- Concurrency failure assertions now distinguish the initiating protocol error
  from disconnected queued calls. Task-creation barriers do not prove every
  competitor has already entered the queue; disconnect and reconnect are
  exercised separately, not as a combined disconnect-during-reconnect scenario.
- Final source refinements preserve earlier write attempts in
  `replayedUncertain`, mark current uncertainty only when sending starts, and
  avoid inventing a write attempt when reconnect fails. Three extra regression
  peers cover scalar/multi replay rejection and rejected reconnect diagnostics;
  successful replay assertions are strengthened (15 retry/progress scenarios total).
- Compact-header/MC7 decoding now stays inside the upload gate as well, with
  a successful raw-transfer/invalid-compact-block regression (21 phase-fault
  scenarios total). These final refinements await the final clean validation.
- Final clean validation passed all 82 build jobs, all Lean tests, all three
  generated corpus comparisons, lint/format, and whitespace checks. Independent
  focused runs against this exact build passed all 15 retry/progress scenarios
  and all four concurrency modes with strict initiating/queued error categories.
  The focused 21-phase fault run also passed, including compact-upload closure.
  The full final emulator suite remains underway.
- Final complete pinned python-snap7 3.0.0 emulator/scripted-peer suite passed
  against the final clean build, including all 15 retry/progress scenarios,
  four concurrency modes, 21 phase faults, and all existing integration checks.
  The complete local validation is green. No follow-up commit or push has
  been made. Progress is wire-range/ordered-result based, not indexed by caller
  item identity; replay uncertainty does not imply rollback or exactly-once IO.
  Sends/connects remain outside cancellation guarantees, and no physical PLC
  compatibility or safety certification is claimed.
