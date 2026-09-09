# S7 conformance and transfer assurance — 2026-09-09

## Implemented

- Shared S7 corpus with eight response/chunk/write cases and five address vectors.
- Checked single-read byte counts, ordered read assembly, contiguous offsets,
  bounded write slices, and complete write-payload reconstruction.
- COTP reassembly bounded by the negotiated PDU budget, with a checked size theorem.
- One monotonic receive deadline across TCP fragments, TPKT headers and bodies,
  COTP segments, and stale responses within an exchange attempt.
- Eleven scripted transport cases covering valid fragmentation, size limits,
  missing EOT, truncated input, stale responses, and slow streams.

## Published commits

- `5790513`: transfer assembly proofs, shared conformance cases, and audit evidence.
- `b64bded`: bounded COTP reassembly and transport regression tests.
- `17c1b15`: receive deadlines across fragments and stale responses.

## Validation

The implementation passed clean builds, Lean tests, the full python-snap7 3.0.0
emulator suite, all corpus freshness checks, Python lint/format, and whitespace
checks. Five generated address packets passed offline Wireshark 4.6.8 dissection.

Both python-snap7 3.0.0 and source revision
`383852f3eb6465c92aebd7d3457c14e7d6f4f92a` passed the two valid response controls
and diverged on the other six response/chunk/write cases. Historical bug probes
remain separate from conformance tests because they assert the observed faulty
behavior. No upstream implementation changes were made.

## Remaining boundaries

- Physical counter/timer indexing is unresolved. The emulator fixture explicitly
  applies Lean's address convention; passing those tests is not controller evidence.
- Receive deadlines do not bound sending or total duration across retries.
- Transfer proofs do not establish controller memory correctness, atomic writes,
  persistence, transport liveness, or safety certification.

See [the addressing investigation](addressing-evidence-2026-09-09.md) and
[the Python audit](python-snap7-audit-2026-09-08.md) for evidence and qualifications.
