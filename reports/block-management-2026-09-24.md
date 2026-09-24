# Block-info identity and subtype closure — 2026-09-24

Scope: classic S7 client metadata; no python-snap7 changes, controller writes,
physical PLC testing, or universal firmware compatibility claim.

## Explicit supported policy

`BlockInfo.blockType` keeps its existing outer response-byte meaning (payload
offset 1). The additive `subBlockType : UInt8 := 0` exposes the distinct compact
header byte at offset 11. Decoding retains all 256 values of both fields rather
than inventing unknown/reserved-field restrictions. The default preserves source
compatibility for callers constructing the public structure without the field.

`Client.getBlockInfo` supports numbers 0 through 65535 and rejects larger numbers
as invalid input before allocating a request reference or performing IO. This is
an explicit correlated-client profile, not a claim that five-digit requests are
universally invalid on the wire. `encodeGetBlockInfo` continues to encode numbers
through 99999 for independent profiles and the raw escape hatch.

The client now compares the decoded 16-bit number with the full requested `Nat`:
it does not truncate or wrap the request. A mismatch is a malformed typed reply,
decoded while the operation gate is held, and closes the session before queued
work can begin. Both type fields remain losslessly exposed but are not correlated
with the requested type. That remaining limit is deliberate: evidence does not
justify imposing universal outer-field or subtype constants on existing peers.

## Primary-source evidence

The audit also found an actual request layout defect: `encodeGetBlockInfo`
placed `A` before the five ASCII digits, matching the pinned Python emulator's
parser but not the native request structure. The codec now puts the five-digit
number before the final `A`. This follows both the
[native request layout](https://github.com/SCADACS/snap7/blob/master/src/core/s7_types.h#L937-L945)
and the [native client field assignments](https://github.com/SCADACS/snap7/blob/master/src/core/s7_micro_client.cpp#L815-L829).
Native C++ assignment order does not determine field layout: `A` is assigned
first but stored after the declared `AsciiBlk[5]` field. No evidence established
the old order as a valid alternative controller dialect, so no compatibility
toggle was added. The emulator adaptation belongs only to the integration
fixture, not the client or the separate Python repository.

The [native Snap7 constants and wire structure](https://github.com/SCADACS/snap7/blob/master/src/core/s7_types.h#L59-L75)
distinguish request/directory type codes from compact subtypes. Its
[block-info reply layout](https://github.com/SCADACS/snap7/blob/master/src/core/s7_types.h#L948-L980)
uses separate fields and a 16-bit block number. The
[native client operation](https://github.com/SCADACS/snap7/blob/master/src/core/s7_micro_client.cpp#L778-L866)
exposes the compact subtype to its API. The
[native server implementation](https://github.com/SCADACS/snap7/blob/master/src/core/s7_server.cpp#L1839-L1851)
populates the outer field from the requested type. That corroborates its own
server profile, not a normative Siemens rule for every controller or our own PLC
capture. Therefore this batch does not impose strict outer-field equality.

`BlockType.subCode` exposes the seven independently documented native subtype
constants without applying them as decoder rejection rules. The unmodified
pinned emulator uses the request/directory code as the subtype for its DB
metadata, rather than compact subtype 0x0a. The local integration fixture now parses
the canonical request directly and supplies the DB subtype 0x0a; it does not
translate the native wire packet back to the legacy erroneous order. Its four
numeric identities and nine malformed/unsupported controls passed independently.
No firmware-wide type-completeness claim is made for emulator metadata.

## Assurance and portable artifact

Checked actual-function theorems establish the client profile's numeric bound,
successful correlation's full numeric equality, and lossless result identity.
These are pure-boundary claims, not proofs of live Client IO or PLC identity.

Existing dedicated advanced tests additionally exercise all 256 subtype values,
distinguish offsets 1 and 11, preserve opaque values during numeric correlation,
reject wrong and wrapping high numeric identities, cover supported client bounds,
and retain the low-level five-digit request domain.
Twenty-eight independent exact packet goldens cover seven block types and
numbers 0, 1, 65535 and 99999, with the filesystem marker at the final byte.
The expectations assemble literal headers, decimal strings and the terminal
marker independently of `encodeGetBlockInfo`; they reuse `BlockType.code` for
the existing type-code mapping. They test request layout, not an independently
implemented mapping of every block type.

The v1 S7 block-info expectation adds `sub_block_type` without changing the
existing `block_type` meaning. Its positive wire fixture uses distinct outer
0x41 and compact 0x0a fields. The independent Python checker compares the legacy
parser's existing fields and checks the additive subtype directly at wire offset
11; it does not claim the legacy Python parser exposes that field.

Five independent exact-wire peers exercise numeric boundary identities, opaque
outer/subtype acceptance, mismatch classification and terminal gate cleanup, and
three unsupported-number preflights followed by a valid request on the same
connection. The peer verifies that rejected preflights neither transmit packets
nor consume operation references. These are bounded observations of the actual
client, not universal scheduling or firmware guarantees.

Local focused validation passed: the dedicated module and all native tests;
three new theorem axiom audits (only `propext`/`Quot.sound`); all five live
scripted peers again after the request-layout fix; all 28 request goldens; Ruff
lint/format; checked corpus regeneration; and the positive Python block-info case.
The containing batch subsequently passed the root's full clean build and
integration checks; see [the combined validation record](classic-progress-2026-09-23.md#completion-closure--2026-09-24-locally-validated).

The positive portable block-info case passes the pinned Python parser. The full
historical `s7_conformance.py` diagnostic still reports its existing broad
parser/wire differences against python-snap7 3.0.0 (8/54 pass); it is not the
required current emulator integration runner, and these differences are not new
subtype regressions or a reason to modify the separate Python repository.
