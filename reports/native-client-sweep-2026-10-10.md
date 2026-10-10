# Native-client parameter sweep and chunk sequences — 2026-10-10

Follow-up to [the encoder audit](native-client-request-audit-2026-10-08.md): the same
recording-stub method, widened from 60 sample requests to a grid of 1,123 parameter
combinations, plus the full request sequence of multi-chunk transfers. The pinned native
Snap7 client is one implementation, not the specification, and nothing here qualifies a
controller.

## Sweep (1,123 cases, single requests)

Memory reads at every area with DB numbers 1, 2, 255, 256 and 65535, starts from 0 to
`0x200000` and counts 1 to 462; DB writes; every SZL id/index form; list-by-type, block
info, start upload and delete for seven block types and thirteen numbers; session passwords
of 0 to 9 characters; set-clock dates including the century and leap-day edges; multi-item
reads and writes of 1 to 20 items. The grid and the Lean-side driver were exploratory
scratch code and are not committed; `native_client_requests.py` and the new
`native_client_chunks.py` are the repeatable parts.

| Outcome | Cases |
| --- | ---: |
| Byte-identical request | 920 |
| lean-s7 refuses, native sends | 174 |
| Counter/timer count 462 (native clamps to 231 elements) | 8 |
| Multi-write, payload bytes only | 19 |
| Both refuse (empty and 9-character passwords) | 2 |

No case showed lean-s7 sending a different layout for the same valid request. Explanations
for the others:

- **Refusals, memory addresses (98).** The request extends past the 24-bit wire address
  (`(start + count) * 8 > 0xffffff`). The native client sends these anyway, and for starts of
  `0x200000` and above (48 cases) it silently truncates the address to 24 bits, so it would
  read a different location from the one asked for. lean-s7's refusal is correct.
- **Refusals, counter/timer starts (74).** lean-s7 accepts only starts that are multiples
  of the element size (2), so odd counter and timer numbers cannot be addressed. See below.
- **Refusals, set clock (2).** Years 1989 and 2090 are outside the S7 DATE_AND_TIME range;
  the native client sends them encoded as other years (2090 as 1990), lean-s7 refuses.
- **Counter/timer count 462.** The native client clamps one request to 231 elements; the
  lean-s7 encoder is given the count by the chunk planner and does not clamp.
- **Multi-write payloads.** The native bytes were not the zero-filled buffers the harness
  supplied (they showed 0xA5, the fill of an earlier write in the same process), so payload
  bytes are excluded; the layout is identical.

## Chunk sequences (`integration/native_client_chunks.py`)

For reads and writes larger than one PDU, the native client's request sequence (function,
area, word length, element count and raw wire address) is the golden file
`integration/native_client_chunks.json`, checked in CI with the native build.

- **DB, marker and word transfers** advance by the bytes already transferred, with the
  address field in bits: for example 1,000 DB bytes from byte 10 at PDU 480 are requested
  as 462, 462 and 76 bytes at bit addresses 80, 3,776 and 7,472. Writes carry 452 bytes per
  request at PDU 480 and 212 at PDU 240. This matches lean-s7's chunk plan.
- **Counters and timers advance by the bytes transferred too, not by the elements.** 500
  counters from index 16 at PDU 480 are requested as 231, 231 and 38 elements at addresses
  16, 478 and 940: the second request starts 462 counters in, not 231 (at PDU 240: 16, 238,
  460, 682, 904 with 111-element chunks). lean-s7 does the same (`Chunking.ReadAssembly.nextStart`
  adds the assembled bytes for every area), and the conformance case `counter-next-chunk-478`
  encodes it. python-snap7 3.2.1 advances counter and timer starts by element count.

## Open question (gate H1)

The S7 address field of a counter or timer is its number (the Wireshark dissector shows
"number"), so the second chunk of a long counter read ought to start at the first number plus
the elements already read. Both native Snap7 and lean-s7 skip ahead by twice that, and
python-snap7 does not. Until a controller shows which is right:

- A counter or timer read or write that needs more than one PDU (more than 111 elements at
  PDU 240, 231 at PDU 480) may address elements that were not asked for. On a controller
  with few counters the second request is out of range and the PLC rejects it; on one with
  many it could return the wrong counters without an error.
- Odd counter and timer numbers cannot be addressed through the byte-offset API.

`docs/COMPLETENESS.md` already lists physical counter/timer indexing under H1; this report
adds executed evidence for the native behavior and the chunk-advance consequence.
