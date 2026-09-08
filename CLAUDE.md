# lean-s7 repository guidance

## Project

lean-s7 is an independent, exploratory Lean 4 implementation of Siemens classic
S7 communication over ISO-on-TCP. Its primary goals are to build practical
experience with Lean and formal proofs, and to determine how an executable
specification and machine-checked protocol properties can improve python-snap7
and other S7 implementations. A usable client is an important validation vehicle,
not the sole outcome. It does not preserve the python-snap7 API and does not
require Python at runtime.

The toolchain is pinned in `lean-toolchain`. Do not upgrade it incidentally.

## Architecture

- `LeanS7/Binary.lean`: bounded binary readers and writers.
- `LeanS7/TPKT.lean`: RFC 1006 framing and framing properties.
- `LeanS7/COTP.lean`: ISO 8073 connection and data TPDUs.
- `LeanS7/S7.lean`: classic S7 PDU codecs and validation.
- `LeanS7/Protocol.lean`: composed TPKT/COTP/S7 framing and stack-level proofs.
- `LeanS7/Chunking.lean`: proved transfer chunk plans and coverage bounds.
- `LeanS7/Management.lean`: USER_DATA, SZL, clock, security, and CPU-control codecs.
- `LeanS7/Advanced.lean`: block discovery, transfer, maintenance, and force-table codecs.
- `LeanS7/Value.lean`: typed DB values, bits, STRING, and WSTRING codecs.
- `LeanS7/Transport.lean`: TCP, TPKT, and COTP IO.
- `LeanS7/Client.lean`: client lifecycle and public operations.
- `Tests.lean`: deterministic unit and golden-packet tests.
- `integration/run.py`: end-to-end tests against a pinned python-snap7
  emulator on a dynamic localhost port.

Keep pure protocol codecs separate from IO. Validate lengths, discriminators,
references, negotiated limits, and return codes before exposing payload data.
Do not use panicking ByteArray indexing in packet decoders.

## Required checks

Run the complete local check before every commit:

```console
lake clean
lake build lean-s7 lean-s7-tests
lake exe lean-s7-tests
python -m pip install "python-snap7==3.0.0"
python integration/run.py
```

Also run Python lint and formatting checks on integration harness changes.
GitHub Actions is a final platform check, not a substitute for local testing.

## Compatibility strategy

Use several independent layers of evidence:

1. Lean unit tests and proofs for local invariants.
2. Golden wire vectors derived from protocol documentation and captures.
3. End-to-end behavior against the python-snap7 emulator.
4. Cross-tests against other implementations and Wireshark where useful.
5. Explicit real-PLC validation before claiming production compatibility.

Do not treat python-snap7 behavior alone as the protocol specification.

The long-term shared artifact should be a versioned, language-neutral
conformance corpus generated from the Lean model. It should describe structured
inputs, expected wire bytes, decoded values, and expected failures so that
python-snap7 and independent S7 implementations can consume the same cases.

Prioritize proofs at pure protocol boundaries:

- bounded and total decoding of untrusted packets
- encode/decode round trips and exact encoded lengths
- adherence to negotiated PDU limits
- complete, non-overlapping chunk coverage
- order-preserving multi-item batching within count and size limits
- request/response correlation and legal connection-state transitions

Writing implementation code in Lean is not sufficient evidence for a formal
claim. Describe a property as verified only when the corresponding theorem is
present and checked. Likewise, conformance testing Python against a proved Lean
model provides strong assurance but is not a formal proof of the Python source.

## Contributions

- Keep related client work in one coherent branch or pull request.
- Track substantial missing capabilities with focused GitHub issues.
- Run all checks locally before committing or pushing.
- Never force-push or rebase a published branch unless explicitly requested.
- Never attribute commits or pull requests to Codex, Claude, OpenAI,
  Anthropic, an AI assistant, or any other agentic programming agent or tool.
  Do not mention them in commit messages, commit trailers, pull-request titles,
  or pull-request descriptions, and do not add co-author trailers, generated-by
  text, or AI signatures. Always use
  `Gijs Molenaar <gijsmolenaar@gmail.com>` as the Git author and committer, and
  inspect full commit metadata before every push.
- This library can control industrial equipment. Use conservative defaults,
  reject malformed or ambiguous packets, and do not imply safety certification.
