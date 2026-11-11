# Classic S7 0.3.0 candidate readiness — 2026-11-11

Version 0.3.0 is prepared as a candidate. `docs/RELEASE.md` requires the repository
owner to approve the version, tag and publication. The owner asked on 2026-11-11 for
the 0.3.0 release to be cut, which approves the version and the `v0.3.0` tag. The tag
goes on the merge commit of this change once its CI passes. Versions 0.1.0, 0.1.1 and
0.2.0 and their tags are untouched.

## What changed since 0.2.0

Three behaviour changes in production code, each merged on its own:

- USER_DATA follow-up requests send method `0x12` for every group (#49).
- Counter and timer transfers that need more than one request are rejected before any
  IO (#52).
- `Client.serialized` runs on a pure ticket model with a run-time order check (#46).

Everything else is new proofs (canonical-form theorems for every decoder in the
inventory, #62–#65), tests, evidence harnesses, reports, the corpus provenance and the
package version. See [the release notes](../docs/releases/0.3.0.md).

## Local validation of the candidate (Windows 11, Lean 4.33.1)

Run on the candidate working tree (base `555b10a` plus the version, notes and corpus
provenance edits in this change):

- `lake clean`, then a build of all seven targets (`lean-s7`, `lean-s7-tests`,
  `lean-s7-conformance`, `lean-s7-fuzz`, `lean-s7-axioms`, `lean-s7-cli`,
  `lean-s7-decode`): 186 jobs.
- `lake exe lean-s7-tests` passes. `lake exe lean-s7-axioms`: 1,743 theorems, 50
  documented theorem names resolved, 0 failures.
- All eight corpora reproduce exactly; the corpus manifest check, the package
  verification and the archive reproducibility check pass (corpus 1.1.1, a
  provenance-only patch: only `corpus_version` and `lean_s7_version` change).
- The full pinned emulator, fault and peer integration suite (`integration/run.py`,
  python-snap7 3.0.0) passes on Windows, including the import-boundary guard for six
  public/executable roots and the external Lake package smoke test. The resource-stress
  and scalability steps are skipped on Windows (no process metrics).
- The CLI smoke test passes. The python-snap7 consumer runs against 3.0.0 (580 cases:
  95 agree, 296 gap, 52 ambiguity, 137 disagree) and 3.4.0 (419 agree, 85 gap, 14
  ambiguity, 62 disagree) and matches the recorded baselines.
- Ruff 0.16.8 (the version CI pins) lint and format pass on `integration/`.
- The official native Snap7 endpoint cross-tests pass at PDU 240 and 480 (library
  SHA-256 `4b376292…`); the native client's request golden vectors (60) and chunk
  sequences (14) match.
- The optional real-capture replay: 351 of 351 lean-s7 checks agree on six public
  captures.

## CI evidence

Every change merged since 0.2.0 (#45–#71) passed CI on its own branch before merging.
That is not evidence for the tagged revision. The exact-revision evidence (CI on the
merge commit of `main`, CI on the tag, and the resource soak on the tag, Linux and
macOS) is recorded when the release is published, in the release attachment
`validation-0.3.0.json`.

## Not covered

No physical-controller qualification (the replayed captures cover only the conversations
they contain), no counter/timer addressing beyond one request (gate H1), no hard native
cancellation (the Lean runtime offers no send-cancel or force-close primitive), no
multi-fragment upload evidence, no full IO/scheduler equivalence proof, and the native
Snap7 and python-snap7 dependencies remain test-only. Windows CI stays informational
(#58).
