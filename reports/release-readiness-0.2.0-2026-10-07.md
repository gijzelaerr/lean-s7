# Classic S7 0.2.0 candidate readiness — 2026-10-07

Version 0.2.0 was prepared, tagged and **published on 2026-10-07**. `docs/RELEASE.md`
requires the repository owner to approve the version, tag and publication; the owner
accepted gates L1–L4, then approved version 0.2.0 and the `v0.2.0` tag on commit
`b0fd9c5`. Versions 0.1.0 and 0.1.1 and their tags are untouched.

## What changed since 0.1.1

Production code: ten lines in `LeanS7/Client.lean` (the client now calls the pure
`LeanS7.Correlation` core for reference allocation and the stale-reply decision; the
behavior is unchanged) and one test-only deadline in `Main.lean`. Everything else is
new proofs and tests, tools outside the library import graph, evidence harnesses,
reports, the corpus packaging and the package version. See
[the release notes](../docs/releases/0.2.0.md).

## Local validation of the candidate (Windows 11, Lean 4.33.1)

Run on the candidate working tree (base `f15eb3a` plus the version, notes and gate
edits in this change):

- Clean build of all seven targets (`lean-s7`, `lean-s7-tests`, `lean-s7-conformance`,
  `lean-s7-fuzz`, `lean-s7-axioms`, `lean-s7-cli`, `lean-s7-decode`): 182 jobs.
- `lake exe lean-s7-tests` passes; `lake exe lean-s7-axioms`: 1,388 theorems, 19
  documented theorem names resolved, 0 failures.
- All eight corpora reproduce exactly; the corpus manifest and archive reproducibility
  checks pass (corpus 1.0.1, a provenance-only patch for the new version).
- Ruff lint and format; the CLI smoke test; the pinned python-snap7 3.2.1 and 3.0.0
  differential baselines verify.
- The full pinned emulator, fault and peer integration suite (`integration/run.py`,
  python-snap7 3.0.0) passes on Windows: 415 checks, including the import-boundary guard
  for six public/executable roots and the external Lake package smoke test. The
  resource-stress and scalability steps are skipped on Windows (no process metrics).
- The optional real-capture replay: 351 of 351 lean-s7 checks agree on six public
  captures and the PDU counts equal Wireshark's.

## CI evidence

Every change merged since 0.1.1 (#28–#41) passed the Linux and macOS CI on its own
branch before merging. That is not evidence for the tagged revision.

Exact-revision evidence for tag `v0.2.0` (commit `b0fd9c5`), all green on Linux and macOS:

- [CI on the merge commit of `main`](https://github.com/gijzelaerr/lean-s7/actions/runs/37613626847);
- [CI on the tag](https://github.com/gijzelaerr/lean-s7/actions/runs/37614264408);
- [resource soak on the tag](https://github.com/gijzelaerr/lean-s7/actions/runs/37614296100), 32 rounds.

The release attachment `validation-0.2.0.json` records these runs and the local checks.
The release is at <https://github.com/gijzelaerr/lean-s7/releases/tag/v0.2.0>; corpus
1.0.1 (identical JSON files, new provenance) is
[`corpus-v1-1.0.1`](https://github.com/gijzelaerr/lean-s7/releases/tag/corpus-v1-1.0.1).

## Not covered

No physical-controller qualification (the replayed captures cover only the conversations
they contain), no hard native cancellation (the Lean runtime offers no send-cancel or
force-close primitive), no multi-fragment upload evidence, no full IO/scheduler
equivalence proof, and the native Snap7 and python-snap7 dependencies remain test-only.
