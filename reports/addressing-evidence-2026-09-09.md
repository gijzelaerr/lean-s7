# Counter/timer addressing evidence — 2026-09-09

## Result

Lean's direct counter/timer wire addresses match the native Snap7 client source
reviewed below. Wireshark 4.6.8 successfully dissects five generated packets,
interpreting DB addresses as bit-encoded byte positions and counter/timer fields
as numbers. This rules out treating those fields as ordinary DB bit addresses
in the fixture, but does not establish how Lean's byte-offset API maps to
physical controller counter/timer indices. No codec change was made.

## Independent sources

The public SCADACS/snap7 master revision resolved to
`f6ff90317ca5d54250f4dcd29209689a74e26d82` during this review.
In [the native client](https://github.com/SCADACS/snap7/blob/f6ff90317ca5d54250f4dcd29209689a74e26d82/src/core/s7_micro_client.cpp),
`opReadArea` and `opWriteArea` put Start directly into timer/counter addresses,
while ordinary byte areas multiply Start by eight. Read chunk starts advance
by element count times byte width. This is source comparison, not execution
against a native client or real PLC.

The [Wireshark dissector](https://github.com/wireshark/wireshark/blob/v4.6.8/epan/dissectors/packet-s7comm.c)
distinguishes timer/counter numbers from ordinary byte/bit addresses.
The locally executed TShark reports version 4.6.8, commit `e677bf052328`.
For generated Lean packets it reported:

| Lean API start | Area | Raw address | Dissector interpretation |
| --- | --- | --- | --- |
| 16 | DB | 128 | byte 16 |
| 16 | counter | 16 | number 16 |
| 16 | timer | 16 | number 16 |
| 478 | counter | 478 | number 478 |
| 478 | timer | 478 | number 478 |

The [native Snap7 server](https://github.com/SCADACS/snap7/blob/f6ff90317ca5d54250f4dcd29209689a74e26d82/src/core/s7_server.cpp)
uses a different internal conversion for counter/timer memory access. A
[2018 first-hand bug report](https://sourceforge.net/p/snap7/discussion/bugfix/thread/049b691b/)
describes an offset mismatch caused by that conversion and byte-based backing
memory. This is a historical report, not a verified current controller result.
It is a reason to avoid treating emulator memory behavior as authoritative.

## Repeatable checks and limits

`lake exe lean-s7-conformance s7` validates all address fields against explicit
expected values and exports the packets in `conformance/v1/s7.json`.
`python integration/addressing_conformance.py` wraps those packets in a temporary
synthetic capture and asks the installed TShark to decode them. It checks all
five cases, including the raw address and interpreted number/byte fields.
No sockets are opened, and temporary captures are automatically removed.

The existing Python emulator override remains explicitly a fixture convention.
The evidence does not settle whether physical timer/counter numbers should map
to half of Lean's byte offset, whether odd starts should be accepted, or the
controller-specific valid index range. Resolve these using captured requests
for known adjacent counters/timers or a lab PLC with known distinct values
before changing the API or asserting production compatibility.
