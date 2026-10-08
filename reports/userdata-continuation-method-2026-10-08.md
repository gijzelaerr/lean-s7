# USER_DATA follow-up requests: method 0x12 for every group — 2026-10-08

## Finding

Mapping the management continuation corpus onto python-snap7 (see
[the consumer report](python-snap7-consumer-adapters-2026-10-08.md), on its own branch)
compared follow-up request bytes for the first time and exposed an inconsistency in
lean-s7 itself:

- `Management.encodeReadSzlContinuation` (SZL follow-ups) sent parameter method `0x12`,
  matching the public real S7-300 captures
  ([report](real-s7-300-captures-2026-10-07.md): twelve-byte block
  `00 01 12 08 12 44 01 <seq> 00 00 00 00`).
- `Advanced.encodeUserDataContinuation` (used by `Client` for block-list follow-ups and
  by the corpus) sent method `0x11`, the request-method byte of an initial request.
- The pinned native Snap7 `opListBlocksOfType` sends `Uk = 0x12` with a 12-byte parameter
  block on every follow-up, so the real engineering tool and the independent native
  client agree and lean-s7's generic encoder did not.

The corpus bytes and the independent Python oracle (`integration/management_conformance.py`)
had been written from the same `0x11` assumption, so the existing agreement checks could
not detect it; `integration/userdata_assurance.py` had singled out SZL as the only `0x12`
case for the same reason. Nothing here has been tested against a real controller for
block-list follow-ups, so the effect on hardware is unknown; the evidence is two
independent sources for `0x12` and none for `0x11`.

## Change

- `encodeUserDataContinuation` now builds its parameters with the shared
  `userDataParameters … true` used by the SZL follow-up, so the two cannot diverge; a
  test pins them equal for the SZL group.
- The Lean conformance writer, the Python oracle and the live-peer checker expect `0x12`
  for every follow-up.
- Corpus `1.1.0`: the 48 follow-up `request_pdu` values of the 16 management
  `continuation_cases` change at byte 14 only (`0x11` → `0x12`). See
  `conformance/v1/VERSIONING.md` ("Corrections within a generation") for why this is
  released as a minor version.

## Checks

Unit tests, axiom audit (standard axioms only), corpus manifest and archive checks,
`integration/run.py` (python-snap7 3.0.0 emulator), CLI smoke, the python-snap7 consumer
(3.2.1 baseline unchanged), the Wireshark corpus check (73 / 156 / 3 / 0, unchanged) and
the real-capture replay all pass.
