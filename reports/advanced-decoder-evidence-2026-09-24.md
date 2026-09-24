# Advanced management decoder audit — 2026-09-24

Scope: pure classic S7 management decoders; no physical PLC validation and no
python-snap7 changes.

## Confirmed public-structure validation defect

`decodeSzl` already enforces `data.size = recordLength * recordCount`. However,
`Szl` is publicly constructible, and the five typed SZL parsers and force-table
parser previously did not enforce that invariant. A caller could provide enough
data for the fields while supplying incompatible record metadata and obtain a
successful typed value. The new shared `validateSzlData` check prevents that
bypass. This is a local structure-consistency check, not a newly inferred wire
restriction. Transport-decoded valid SZLs retain their behavior.

## Primary-source cross-checks and retained behavior

- The [native Snap7 block-info wire structure](https://github.com/SCADACS/snap7/blob/master/src/core/s7_types.h#L948-L980)
  distinguishes the outer block type from `SubBlkType`; it also names several
  unknown/reserved fields. We have no evidence establishing strict constants for
  those opaque fields, so this audit does not add such restrictions.
- The [native Snap7 block-info operation](https://github.com/SCADACS/snap7/blob/master/src/core/s7_micro_client.cpp#L778-L866)
  exposes `SubBlkType` in its public result. The current Lean `BlockInfo.blockType`
  retains the outer type at payload offset 1, not the subtype at offset 11.
  Changing that existing meaning or adding another public/corpus field requires
  an explicit API/schema decision; neither is done in this batch. The client also
  does not currently compare the returned block address with the requested one.
  This audit records that limitation without inventing a policy for five-digit
  request numbers versus the 16-bit response number.
- The [native Snap7 order-code operation](https://github.com/SCADACS/snap7/blob/master/src/core/s7_micro_client.cpp#L1859-L1876)
  obtains the version from the final three assembled data bytes. Lean retains
  that behavior for multiple records; the first record supplies the code text.
- The [native Snap7 typed information operations](https://github.com/SCADACS/snap7/blob/master/src/core/s7_micro_client.cpp#L1879-L1919)
  corroborate the CPU/CP field offsets. Lean's SZL data excludes the four-byte
  length/count header included in native `opData`, accounting for the offset
  difference.

## Checked properties and tests

`AdvancedDecoderAssurance.lean` proves supported block-code round trips and
injectivity; actual successful decoder count/list/info extents; exact block-info
date positions and six-byte sizes; force-table discriminator, alignment, and SZL
metadata consistency; and all five typed parsers' SZL metadata consistency. The
successful-decoder theorems quantify over arbitrary inputs, not only local
encoder output. They do not claim a full semantic specification of block counts,
force records, every typed field, or live client IO.

`AdvancedDecoderAssuranceTests.lean` checks all 5,040 seven-type permutations;
every possible marker/type substitution at each count-record position; block
entry order, aligned prefixes and partial extents; all 256 flags/language byte
values and duplicate-number controls; block-info truncation, trailing bytes,
field offsets and opaque outer-type bytes; all 65,536 force bit/value pairs;
force entry order, wrong identifiers, partial extents and public metadata
tampering; and typed SZL positive/minimal-length, truncation, discriminator and
public metadata cases.

No restriction on opaque block-entry flags/languages, duplicate block numbers,
force area/reserved bytes, or nonzero force-value encodings is inferred from
these tests. Force bit indices remain limited to 0–7; nonzero values normalize to
`true`, preserving existing behavior.
