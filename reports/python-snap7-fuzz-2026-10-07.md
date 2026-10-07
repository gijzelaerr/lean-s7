# Differential fuzzing against python-snap7 3.2.1 — 2026-10-07

`python integration/python_snap7_fuzz.py` mutates the 23 accepted corpus cases of the
decoders both sides implement (USER_DATA/management responses, block counts/lists/
info, upload fragments and read responses) with a fixed seed: bit flips, byte
replacement (boundary values such as 0x00, 0x01, 0x09, 0x7f, 0x80, 0xfb, 0xff),
truncation, insertion, deletion, duplication and trailing bytes. Each mutant is decoded
by the Lean decoders (`lean-s7-decode`, a stdin/stdout oracle over the same functions
the client calls) and by the python-snap7 3.2.1 calls its client makes. Optional and
local; not run in CI.

Result for seeds 1 and 2 (800 mutants per accepted case, about 18,400 inputs each; one
seed whose unmutated form already disagrees, a null acknowledgement, is excluded):

| | seed 1 | seed 2 |
| --- | ---: | ---: |
| both accept, identical decoded values | 1,114 | 1,094 |
| both reject | 14,615 | 14,622 |
| Lean rejects, python-snap7 accepts | 308 | 323 |
| python-snap7 rejects, Lean accepts | 0 | 0 |
| both accept, different values | 0 | 0 |

So python-snap7 never rejects an input Lean accepts and never decodes a different
value from an input both accept: every difference is python-snap7 being more lenient.
Same-length mutants identify what it does not check:

1. **Header error code with error class 0 (read and upload responses, header offset
   11).** Accepted by the read/upload parsers and rejected by python-snap7's own write
   check. Native Snap7 fails on any nonzero 16-bit error word
   ([s7_micro_client.cpp#L397](https://github.com/davenardella/snap7/blob/30f37da3114024a71ba93f7fd855c680b97a406f/src/core/s7_micro_client.cpp#L397)).
   Filed as python-snap7 [#930](https://github.com/gijzelaerr/python-snap7/issues/930).
2. **Block-count tables that are not exactly seven entries.** Empty and partial tables
   are accepted as zero counts; native requires a data length of 28
   ([#L633](https://github.com/davenardella/snap7/blob/30f37da3114024a71ba93f7fd855c680b97a406f/src/core/s7_micro_client.cpp#L633)).
   Filed as [#931](https://github.com/gijzelaerr/python-snap7/issues/931).
3. **USER_DATA parameter-header bytes and data transport size.** Mutations of the item
   count (offset 11), the address-specification length (13), the type nibble of the
   group byte (15), the last-data-unit flag (19) and the data transport size (23) are
   accepted, as are non-zero reserved header bytes. This matches the transport-size and
   continuation-flag leads in
   [the 3.2.1 report](python-snap7-3.2.1-2026-10-07.md); they are hardening items, not
   filed, because it is not established which of them a real controller may legitimately
   vary.

Decoders with no differences in either seed: block-list entries and block-info
(accept/reject and every decoded field agree on all mutants of those seeds).

## What this does and does not show

It is differential evidence over mutations of 23 seeds. It does not show that either
implementation is correct on inputs outside those neighborhoods, and the Lean
decoders' stricter rules are deliberate rather than ground truth. Clock payloads are
not included because python-snap7 reads an eight-byte clock (see the 3.2.1 report).
