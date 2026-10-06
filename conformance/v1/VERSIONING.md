# Conformance corpus versioning

The corpus has two version numbers.

- **Directory/schema generation (`v1`)**: every file carries `schema_version: 1`.
  This changes only with a breaking change, which starts a new `conformance/v2/`
  directory. `v1` stays published and consumable.
- **Corpus release (`MAJOR.MINOR.PATCH`, currently recorded as `corpus_version` in
  [`MANIFEST.json`](MANIFEST.json))**: the release consumers pin to. `MAJOR` is
  always the directory generation (`1.x.y` for `v1`).

Consumers should pin to a corpus release and verify the per-file SHA-256 values in
`MANIFEST.json`, not to a git revision of this repository. The manifest also records
the generating lean-s7 version and the Lean toolchain; the exact git revision is
recorded in `PROVENANCE.json` inside each release archive.

## What is a compatible change (MINOR or PATCH)

A consumer written against `1.0.0` that ignores unknown fields and unknown cases
must keep passing against every `1.x.y`.

MINOR (bump `1.N.0`):

- adding cases to an existing array, or adding a new case array to a file;
- adding a new corpus file;
- adding optional fields to a case or expectation object (for example the
  `sub_block_type` field added to block-info expectations);
- tightening a case from "unspecified" to an exact expectation that all correct
  implementations already satisfy.

PATCH (bump `1.N.P`): changes that cannot alter any consumer's verdict: README or
VERSIONING edits, new provenance fields, or regenerating files with identical content.

## What is a breaking change (new `v2`)

Any of the following requires a new `conformance/v2/` directory and
`schema_version: 2` in the files it affects:

- removing or renaming a file, case array, field or case `id`;
- changing the type, unit or encoding of a field (for example byte arrays to hex
  strings, byte offsets to element offsets);
- changing an `accept` expectation to `reject`, or the opposite, or changing an
  accepted result value;
- renaming or merging normalized error categories that consumers compare
  against.

Case `id` values are stable within a corpus generation and are never reused for a
different case. A case that was wrong is not silently corrected in place: if it
asserted behavior that is incorrect per the protocol sources, the correction is a
breaking change unless no `1.x` consumer could have depended on it, and the release
notes say which case changed and why.

## Releasing

1. Regenerate each corpus file with `lake exe lean-s7-conformance [subcommand]` (see
   `MANIFEST.json` for the exact command per file) and keep CI's byte comparison
   green.
2. Decide MINOR, PATCH or "new `v2`" using the rules above and update
   `CORPUS_VERSION` in `integration/corpus_package.py`.
3. Run `python integration/corpus_package.py --write`, review the manifest diff and
   commit it.
4. After the commit is on the default branch, build the archive and attach it with
   its checksum to a GitHub release:

   ```console
   python integration/corpus_package.py --package dist
   gh release create corpus-v1-1.0.0 dist/lean-s7-conformance-v1-1.0.0.tar.gz \
     dist/lean-s7-conformance-v1-1.0.0.tar.gz.sha256 --title "Conformance corpus 1.0.0"
   ```

The packaging script uses only the Python standard library and is not part of the
Lean client's import graph (see `integration/import_boundaries.py`). Publishing a
PyPI or npm data package is optional and not provided.
