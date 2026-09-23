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
