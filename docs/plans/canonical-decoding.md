# Plan: canonical decoding proofs

Status: phases 0–6 done on 2026-10-28, phases 7–9 on 2026-10-29. Every decoder
in the classification table now has a canonical-form theorem. The open decisions
below await owner review.

## Phase 9 results

Phase 9 covers `Advanced.decodeForceTable`, the last decoder in the table. It is
lossy in two ways, so the theorem is a per-entry characterisation rather than a
re-encoding:

- each entry's value byte decodes to `value != 0`, so only its zero-ness is
  recovered;
- the last word of each entry is read and discarded.

**`S7.decodeForceTable_canonical`**: an accepted force table holds exactly one
eight-byte entry per decoded entry, in order (`szl.data.size = 8 * entries.size`),
and each decoded entry satisfies `ForceEntryBytes`. That predicate says:

- bytes 0–4 are exactly the area code, byte offset and bit index;
- byte 5 is zero exactly when the value is false;
- bytes 6–7 are not read.

The decoder is a `for … in [0:n]` loop over a mutable cursor and result array.
The proof rewrites it to a `forIn` over `List.range'` and proves a loop
invariant by induction over that list: each iteration consumes eight bytes and
appends their entry. The loop body isn't restated anywhere. The invariant is
proved with the loop hypothesis reverted into the goal, so the decoder is
unchanged.

## Phase 8 results

Phase 8 covers the two string decoders. Neither can be stated as plain
canonicity, because both ignore the unused capacity after the active characters
and the encoder writes zeros there. Both decoders are otherwise injective, which
was checked before stating the theorems:

- STRING maps each byte to a character through `Char.ofNat`. Code points 0–255
  are all valid characters, so `toNat_ofNat_byte` recovers the byte, and Latin-1
  encoding inverts the mapping (`encodeLatin1_bytes`).
- WSTRING accepts a non-surrogate BMP unit or a high/low surrogate pair, and
  rejects everything else. UTF-16 encoding of the decoded characters gives back
  exactly the accepted units (`encodeUtf16_decodeUtf16Units`, by functional
  induction over `decodeUtf16Units`).

The theorems:

- **`Value.decodeString_canonical`**: re-encoding a decoded STRING with the
  capacity from its header reproduces the header and the active characters
  exactly, followed by zeros for the unused capacity.
- **`Value.decodeWString_canonical`**: the same for WSTRING, with UTF-16 units.
  `readUtf16Units_extract` shows the units read are exactly the big-endian words
  at the cursor.

Both decoders read a field inside a larger buffer and don't call `finish`, so
the theorems are about the field's bytes `offset … offset + 2 + current` (STRING)
or `offset … offset + 4 + 2 * current` (WSTRING). They also show that the whole
declared capacity is inside the buffer.

## Phase 7 results

Phase 7 covers the management decoders and the COTP disconnect request. It adds
four theorems and changes no decoder:

- **`COTP.decodeDisconnectRequest_canonical`**: strict. Every accepted disconnect
  request is exactly `encodeDisconnectRequest` of the decoded value.
- **`S7.decodeUserDataResponse_canonical`**: lenient. Re-encoding an accepted
  USER_DATA response reproduces the input with only the reserved word
  (offsets 2–3) cleared. The response has no encoder in the client, so this adds
  the spec function `encodeUserDataResponse`, as phase 3 did with
  `S7.encodeResponse` (open decision 3). Every other byte is determined by the
  decoded value: the decoder's checks fix the parameter head, the parameter
  length 8, the method, the zero error code and the type nibble. The
  type/function-group byte is rebuilt by `userDataTypeGroup`, a check over all 256
  byte values (`decide +kernel`, standard axioms only). The continuation flag is 0
  or 1, so it equals `if hasMoreData then 1 else 0`. Both data dialects (octet
  payload and null acknowledgement) are covered.
- **`S7.decodePlcDateTime_canonical`**: lenient. Re-encoding an accepted clock
  payload reproduces it with bytes 0–1 replaced by the `00 19` that
  `encodePlcDateTime` writes. The decoder ignores those two bytes.
- **`S7.decodePduReference_canonical`**: a characterisation, not a re-encoding.
  `decodePduReference` is a prefix reader for correlation: it never calls `finish`,
  checks only the protocol ID and returns the reference at offsets 4–5. The
  theorem states that an accepted PDU is the protocol ID, bytes 1–3 unread, the
  returned reference and everything after offset 6 unread.

Phases 8 and 9 cover the remaining string and force-table decoders.

## Phase 6 results

Phase 6 was planned as the hardest phase, canonicity modulo TLV permutation and
duplicates. It turned out to be the simplest. Neither decoder interprets the TLVs
semantically:

- `decodeConnectionConfirm` keeps the variable part as raw bytes.
- `decodeParameters` returns every TLV in wire order, duplicates included.

The ISO 8073 last-duplicate rule is applied afterwards, by the lookup
`findLastParameter`. So both decoders are strict:

- **`COTP.decodeConnectionConfirm_canonical`**: every accepted confirmation is exactly
  `encodeConnectionConfirm` of the decoded value. The length indicator is
  `6 + parameters.size`.
- **`COTP.decodeParameters_canonical`**: every accepted variable part is exactly
  `encodeParameters` of the decoded list. The proof is an induction over the
  fuel-bounded TLV walk (`decodeParametersWithFuel_canonical`).

Both encoders are new spec functions. Each has a one-byte length field, and its
doc comment states the size bound within which it is exact. That bound covers
everything the matching decoder accepts.

## Phase 5 results

The request-context decoders read an already-decoded `Response`. So instead of
adding a response encoder for each of them (open question 3), phase 5 states an
exact characterisation of what they accept. Each theorem pins `response.reference`,
the error bytes, and the precise `parameters` and `data` bytes as a function of
the decoded value and the request context. Any genuine choice is an explicit
disjunction or existential. With `S7.decodeResponse_canonical`, that fixes every
byte of an accepted response except the named reserved bytes, the PDU type and
those choices. These decoders call `validateResponse`, which never checks the PDU
type, so ACK and ACK_DATA are both accepted.

| Theorem | What an accepted response must be |
| --- | --- |
| `S7.decodeDbWrite_canonical` | parameters `[writeFunction, 1]`, data `[0xff]`. Fully determined |
| `S7.decodeDbRead_canonical` | parameters `[readFunction, 1]`, data `[0xff, byteTransportSize] ++ bit length ++ payload`. Fully determined |
| `S7.decodeAreaRead_canonical` | as for a DB read, except the transport size may be the area's own or, for counters and timers, the byte transport size. The length counts bytes for the octet transport size and bits otherwise (`readItemLength`) |
| `S7.decodeSetupCommunication_canonical` | parameters equal `result.parameters` except byte 1, which is not read. The data section is not read at all |
| `S7.decodeAreaWriteMany_canonical` | parameters `[writeFunction, count]`, data exactly the results' return codes in order (`WriteItemResult.returnCode`). Fully determined |
| `S7.decodeAreaReadMany_canonical` | parameters `[readFunction, count]`, data exactly `ReadItemsBytes`: per successful item the same form as `decodeAreaRead`. A failed item fixes only its return code: its transport size, length word and payload bytes are read but not interpreted. One padding byte of any value follows a non-final odd payload |

The single-item theorems are in the new `LeanS7/CanonicalResponseAssurance.lean`.
The two multi-item theorems are in `S7.lean`, because their item walkers
(`decodeReadItems`, `validateItemParameters`) are private there. The read-many
proof is one induction over the item walk (`decodeReadItems_bytes`), with a shared
`readItems_step` lemma covering its four leaves: padding or not, success or
failure.

New public names, for owner review:

- `S7.validateResponse_exact`
- `S7.readItemLength`
- `S7.WriteItemResult.returnCode` and its inverse lemma
- `S7.ReadItemBytes` and `S7.ReadItemsBytes`
- the module `LeanS7.CanonicalResponseAssurance`, imported from the `LeanS7` root

## Phase 4 results

- **`Protocol.decodeJob_canonical`** and **`Protocol.decodeResponse_canonical`**:
  re-encoding an accepted complete TPKT/COTP/S7 packet reproduces it with exactly
  three bytes cleared. Those are byte 1, the TPKT reserved byte, and bytes 9–10,
  the S7 reserved word. Every other byte is reproduced: the TPKT length, the COTP
  header, the S7 protocol ID and PDU type, the reference, both lengths, the error
  class and code for responses, and both sections.
- The composed proofs reuse the layer theorems rather than re-reading bytes.
  `TPKT.decode_layout` (new, and now also the basis of `TPKT.decode_canonical`)
  and `COTP.decodeData_canonical` place the S7 PDU at byte 7. Then
  `S7.decode…_canonical` handles the S7 part. Two private helpers in
  `Protocol.lean` carry the shared steps: `decode_layers` places the layers and
  `reframe` re-encodes the outer headers. Each composed theorem is then about 15
  lines.
- Like phase 3, phase 4 adds the composed `Protocol.encodeResponse`, pinned to
  `Protocol.encodeAckData` by `Protocol.encodeAckData_eq_encodeResponse`, and
  `S7.encodedResponse_size`.

## Phase 3 results

- **`S7.decodeJob_canonical`**: `decodeJob pdu = .ok job →
  encodeJob job = .ok (bytes #[protocolId, jobType, 0, 0] ++ pdu.extract 4 pdu.size)`.
- **`S7.decodeResponse_canonical`**: the same for ACK and ACK_DATA responses, with
  the response's own PDU type in byte 1. The decoder had no encoder for every
  response it accepts: `encodeAckData` only writes an error-free ACK_DATA. So
  phase 3 adds `S7.encodeResponse`, which writes the PDU type, error class and
  error code too. `encodeAckData_eq_encodeResponse` proves by `rfl` that
  `encodeAckData` is its error-free ACK_DATA case, so the new encoder is pinned to
  the one the client uses.
- **New reconstruction helpers** in `Binary.lean`:
  `ByteArray.extract_append_extract_of_le`, `ByteArray.extract_one`,
  `ByteArray.extract_two` and `ByteArray.extract_two_uint16BE`.

The pilot recipe carried over unchanged. The job and response proofs are about
50 lines each, and the response proof needed no iteration beyond adding the
error bytes.

## Pilot results

- **`COTP.decodeData_canonical`** (strict): `decodeData data = .ok pdu →
  encodeData pdu = data`.
- **`TPKT.decode_canonical`** (lenient): `decode data = .ok frame →
  encode frame = .ok (bytes #[version, 0] ++ data.extract 2 data.size)`. The
  re-encoding equals the input except at the reserved byte, which becomes 0. The
  version byte is checked, so it is already equal.
- **Reverse lemmas** in `Binary.lean`: `Cursor.readUInt8_value`,
  `Cursor.readUInt16BE_value`, `Cursor.readBytes_value`, `Cursor.finish_ok`,
  `uint16BE_ofBytes` and `ByteArray.eq_extract_append_extract`.

Both pilots depend only on `propext`, `Classical.choice` and `Quot.sound`. Each
proof is about 40 lines. One recipe covered both: peel the `do` block with
`split`, turn each successful read into a byte fact with the reverse lemmas,
then reassemble the input with `ByteArray.extract_append_extract`. The S7 job and
response headers have the same shape, with more fields, so phase 3 should cost
about the same per decoder.

## Goal

Every checked codec theorem today runs in one direction: *encode, then decode,
gives back the value* (`TPKT.decode_encode`, `COTP.decodeData_encodeData`, and 14
more `decode…_encode…` round trips). Nothing runs the other way. Nothing proves
what a byte string must look like for a decoder to accept it.

This plan adds the converse, **canonical decoding**: if a decoder accepts a
packet, re-encoding the decoded value reproduces that packet. It is reproduced
byte for byte, or byte for byte up to an explicitly listed set of fields that the
decoder deliberately ignores.

Two theorem shapes, chosen per decoder:

```lean
-- Strict decoder: the accepted packet is exactly the canonical encoding.
theorem decodeX_canonical (data : ByteArray) (v : X)
    (h : decodeX data = .ok v) : encodeX v = .ok data

-- Lenient decoder: canonical after normalising the ignored fields.
theorem decodeX_canonical (data : ByteArray) (v : X)
    (h : decodeX data = .ok v) : encodeX v = .ok (normalizeX data)
```

Together with the existing round trips, a strict decoder becomes a bijection
between the values its encoder accepts and the packets it decodes. A lenient
decoder becomes a bijection up to `normalizeX`, and `normalizeX` names exactly
the leniency.

## Why this one

- **It closes the "bounded and total decoding of untrusted packets" priority in
  `CLAUDE.md`.** That priority isn't stated as a theorem yet. Totality is
  structural in Lean; acceptance has no characterisation at all today.
- **It pins down what the differential oracle accepts.** `DecodeMain` drives
  `integration/python_snap7_fuzz.py`. A canonicity theorem turns "no
  accepted-but-different values" from a fuzzing observation into a statement
  about every input. Any python-snap7 acceptance outside the canonical set is
  then a real divergence, not noise.
- **It documents the deliberate leniencies.** Each `normalizeX` is a
  machine-checked list of the bytes lean-s7 ignores. Today these are recorded
  only in tests such as `testTPKTIgnoresReservedInput`.

## Decoder classification (phase 0)

Canonicity is false by design for some decoders, so each decoder is classified
before anything is proved about it. Ignored fields were found by reading each
decoder for discarded reads (`let (_, …) ←`, `let _ ←`). The classification
covers the decoders reachable from the inventory in `docs/COMPLETENESS.md`.

| Decoder | Class | Ignored or ambiguous input |
| --- | --- | --- |
| `COTP.decodeData` | strict, **proved** | none: header length, code and TPDU-number bits are checked, and EOT is encoded |
| `COTP.decodeDisconnectRequest` | strict, **proved** (phase 7) | none: every field is read into the result or checked |
| `TPKT.decode` | lenient, **proved** | `TPKT.lean`, offset 1: the reserved byte. `encode` writes 0 and `testTPKTIgnoresReservedInput` asserts it is ignored |
| `S7.decodeJob` | lenient, **proved** | `S7.lean:63`: the reserved word at offsets 2–3 |
| `S7.decodeResponse` | lenient, **proved** | `S7.lean:366`: the reserved word. Re-encoded through the new `S7.encodeResponse` |
| `Protocol.decodeJob` / `decodeResponse` | composed, **proved** | union of the TPKT, COTP data and S7 header leniencies |
| `COTP.decodeConnectionConfirm`, `decodeParameters` | strict, **proved** (phase 6) | none at decode time. The last-duplicate rule belongs to the lookup `findLastParameter`, not the decoders |
| `S7.decodeAreaReadMany` | lenient, **proved** | the fill byte after an odd-length item, and the transport size, length word and payload of failed items |
| `Management.decodeUserDataResponse` | lenient, **proved** (phase 7) | `Management.lean:162`: the reserved word. Re-encoded through the new `encodeUserDataResponse` |
| `Management.decodePduReference` | prefix reader, **characterised** (phase 7) | `Management.lean:255–256`: the PDU kind and the reserved word. It never calls `finish`, so everything after offset 6 is unread too |
| `Management.decodePlcDateTime` | lenient, **proved** (phase 7) | `Management.lean:611–612`: bytes 0–1 |
| `Advanced.decodeForceTable` | lossy, **characterised** (phase 9) | `Advanced.lean:214`: a word per entry; the value byte only up to zero/non-zero |
| `Value.decodeWString` | lenient, **proved** (phase 8) | `Value.lean:261`: the unused capacity bytes after the string |
| `Value.decodeString` | lenient, **proved** (phase 8) | `Value.lean:200`: the unused capacity bytes after the string |
| `S7.decodeAreaRead`, `decodeAreaWriteMany`, `decodeDbRead/Write`, `decodeSetupCommunication` | **proved** (phase 5) | characterised directly; see phase 5 results |
| the SZL, block, upload, download and CPU-control decoders | no encoder | the client only decodes these responses; see open question 3 |

No discarded reads were found in the remaining decoders. That's a grep-level
reading, not a proof: each one is confirmed only when its theorem is proved.

## Phases

**Phase 1: reverse `Binary` lemmas.** The existing lemmas (`readUInt16BE_ok`,
`readBytes_next`, `Cursor.readBytes_append`, …) compute what a read returns from
known bytes. The converse direction needs:

- `readUInt8` / `readUInt16BE` / `readUInt32BE` succeeding at offset `o` implies
  the bytes at `o` are `uint…BE value`;
- `readBytes count` succeeding implies `data.extract o (o + count) = payload`;
- `finish` succeeding implies `offset = data.size`;
- a reconstruction lemma: a cursor walk from 0 that ends in `finish` means
  `data` is the concatenation of the fields read.

**Phase 2: pilots.**

- `COTP.decodeData_canonical`, the strict form.
- `TPKT.decode_canonical`, the lenient form, with
  `normalize data = data.set! 1 0`. Equivalently: agreement everywhere except
  offset 1.

The pilots measure the effort per decoder and settle the proof style before the
plan commits to anything larger.

**Phase 3: S7 job and response headers.** `S7.decodeJob_canonical` and
`S7.decodeResponse_canonical`, both normalising the reserved word.

**Phase 4: the composed stack.** `Protocol.decodeJob_canonical` and
`Protocol.decodeResponse_canonical`, built from phases 2–3. The normaliser is
the composition of the layer normalisers.

**Phase 5: context decoders.** Area reads and writes, DB read and write, and
setup communication, in whichever form open question 3 settles on.

**Phase 6, optional: COTP connection confirm.** Planned as canonicity modulo TLV
permutation and duplicates. Done as plain canonicity, because the decoders turned
out to be strict; see phase 6 results.

## Repository integration

- **Axiom audit.** Every new theorem is cited in the docs, and so is picked up by
  `lake exe lean-s7-axioms`, or added to `explicitTheorems` in
  `AxiomAuditMain.lean`. Standard axioms only.
- **Completeness matrix.** Add a "Canonical form" column to the decoder
  inventory in `docs/COMPLETENESS.md`, with each decoder's leniency stated.
- **Required checks.** Run the full list in `CLAUDE.md`, including the
  differential fuzzer for decoder changes. The toolchain stays pinned.
- **No decoder behaviour change.** The plan proves properties of the decoders as
  they are. It doesn't tighten them, because tightening could reject packets that
  controllers or the emulator send.

## Out of scope

- IO (`partial def`s in `Client.lean` and `Transport.lean`), sockets and timing.
- Semantic meaning of fields. Canonicity is about bytes, not about what a
  controller does with them.
- Python source. Conformance against a proved model is evidence, not a proof of
  python-snap7.

## Open decisions for the owner

1. **Where the propositions live.** Add canonicity fields to
   `CoreProtocolAssurance`, which the README calls the single auditable
   proposition, or start a separate `CanonicalDecodingAssurance`?
2. **Reserved fields.** Keep the TPKT and S7 reserved-field leniency and state it
   through `normalize`? The alternative is a behaviour change, and so a separate
   decision.
3. **Decoders without an encoder.** For response-side decoders that the client
   only decodes, either add test-only canonical encoders, or prove a weaker
   reconstruction property: the packet is a fixed function of the decoded value
   plus the request context. Phase 3 took the first route for `decodeResponse`,
   adding `S7.encodeResponse` and pinning it to `encodeAckData`. That's a small
   pure function in the library, not test-only code. Phase 5 took the second
   route instead and added no encoders: it characterises the accepted sections
   directly. Phase 7 took the first route for `decodeUserDataResponse`, adding
   `encodeUserDataResponse`. The remaining decoders could follow either route.
4. **Remaining decoders.** Done: phases 6–9 cover every decoder in the
   classification table. Decoders added later should get a classification row
   and a theorem in the same PR.

## Alternatives considered

The following are the other unproved items that `docs/COMPLETENESS.md` names.
Either could be the target instead:

- **The promise-chain order.** The `Client.serialized` IO promise chain actually
  realises the order of the proved `Correlation.Gate` ticket model. Today a
  runtime check enforces it.
- **The `Correlation.scan` model and the socket loop.** Prove they correspond
  beyond the shared `step` function.

Both are IO-adjacent and need a model of the runtime first. Canonical decoding
stays within the pure codecs, where the project's proof infrastructure already
is, and it has a direct payoff for the differential fuzzing work.
