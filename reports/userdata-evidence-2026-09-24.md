# USER_DATA audit evidence — 2026-09-24

Two codec defects were reproduced against the previous decoder definition
from the current committed source, independently of the emulator:

- An otherwise valid `ff 04 0004` SZL item exposed four bytes as if its
  discriminator selected an octet string. It now rejects the discriminator.
- A correlated, complete native clock-set `0a 00 0000` reply with zero
  parameter error was classified as PLC rejection. It now accepts that exact
  null acknowledgement shape for clock-set and password enter/clear only.

## Primary implementation evidence

[Wireshark's S7 dissector](https://github.com/wireshark/wireshark/blob/master/epan/dissectors/packet-s7comm.c#L6265-L6279)
reads the common four-byte USER_DATA item header and identifies the byte at
the transport-size position as the observed constant `09`. The
[transport discriminator definitions](https://github.com/wireshark/wireshark/blob/master/epan/dissectors/packet-s7comm.c)
assign `09` to octet strings with byte-counted length. Consequently this
client's supported successful payload-bearing USER_DATA profile requires
`ff 09`, including an empty octet payload. This is a supported-profile
decision, not a claim about every classic S7 USER_DATA service.

Wireshark's [CPU/default reassembly selection](https://github.com/wireshark/wireshark/blob/master/epan/dissectors/packet-s7comm.c#L6302-L6329)
uses data-unit reference as the fragment identity, with CPU and block
groups using that default path. The sequence token is not required to
increase. Native Snap7's
[block-list continuation client](https://github.com/SCADACS/snap7/blob/master/src/core/s7_micro_client.cpp#L629-L747)
and [SZL continuation client](https://github.com/SCADACS/snap7/blob/master/src/core/s7_micro_client.cpp#L1544-L1659)
echo the previous PLC sequence byte in the next request. Lean retains that
behavior, including repeated and nonmonotonic byte values.

Native Snap7's [SZL answer metadata](https://github.com/SCADACS/snap7/blob/master/src/core/s7_server.cpp#L1969-L1977)
allocates the data-unit reference in the first segmented response and reuses
it in middle and final responses. Its
[clock-set acknowledgement](https://github.com/SCADACS/snap7/blob/master/src/core/s7_server.cpp#L2689-L2723)
and [security acknowledgement](https://github.com/SCADACS/snap7/blob/master/src/core/s7_server.cpp#L2604-L2636)
emit return code `0a`, transport `00`, length `0000`, zero parameter error,
and complete metadata. Those exact service-scoped shapes are supported;
nonempty, continuing, or nonzero-transport null acknowledgements reject.
The previously supported `ff 09 0000` complete empty acknowledgement remains
accepted for these services. Parameter-level errors still reject before
any acknowledgement interpretation.

## New evidence layers and limits

The new deterministic tests check all 256 transport discriminator values
with both empty and nonempty octet data for six supported services;
all three mutating-service null acknowledgements with every discriminator,
empty/nonempty extents, and complete/continuing flags; and all 65,536
sequence/reference byte pairs. Initial and successful correlated identity
properties have direct checked theorems over the actual helper.

The independent live peer suite covers 31 complete conversations: opaque
echo propagation and assembled SZL/block payloads with zero and nonzero
stable identities, malformed continuation correlation/discriminators, and
both positive acknowledgement dialects plus malformed null ACKs. Terminal
malformations must close the session, reject fresh calls, and never reconnect.
Stale-reference cases explicitly configure a zero stale-response allowance
to test protocol rejection on allowance exhaustion. Normal client correlation
retains its bounded stale-PDU discard policy; stale traffic alone is not
reclassified as an immediately fatal decoder error under default settings.

These implementation sources support the conservative profile above but
are not Siemens normative specifications or physical-controller captures.
Zero unit identities are permitted; the client does not invent a nonzero
requirement, monotonic sequence arithmetic, or global reference uniqueness.
Unsupported USER_DATA groups may have different identity or transport rules.
No real-PLC interoperability or industrial safety claim is made.
