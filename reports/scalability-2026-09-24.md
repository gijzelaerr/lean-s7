# Localhost scalability baseline — 2026-09-24

All 18 cases passed independent wire validation and native result checks.
Measurements use the pinned Lean toolchain on macOS-26.7-arm64-arm-64bit, one warmup and
three measured public operations per case. The client algorithm is unchanged.

Reproduce with `python integration/scalability_bench.py --rounds 3` after building
`lean-s7`. [Raw samples](scalability-2026-09-24.json) retain nanosecond timings,
completion-triggered process RSS observations and exchange counts. Smoke cases
also run in the full integration suite, with no timing thresholds.

| PDU bytes | Operation | Logical size | Median ms | Max observed RSS MiB | Exchanges, including warmup |
| --- | --- | --- | ---: | ---: | ---: |
| 240 | read | 16384 bytes | 20.367 | 6.95 | 296 |
| 240 | read | 65536 bytes | 75.348 | 7.67 | 1184 |
| 240 | read | 262144 bytes | 305.483 | 11.86 | 4724 |
| 240 | multi-read | 128 items | 1.887 | 5.75 | 28 |
| 240 | multi-read | 512 items | 6.945 | 6.70 | 108 |
| 240 | multi-read | 2048 items | 29.195 | 7.94 | 432 |
| 240 | multi-write | 128 items | 2.893 | 6.14 | 44 |
| 240 | multi-write | 512 items | 11.067 | 6.97 | 172 |
| 240 | multi-write | 2048 items | 44.201 | 9.17 | 684 |
| 480 | read | 16384 bytes | 9.659 | 6.86 | 144 |
| 480 | read | 65536 bytes | 39.272 | 7.73 | 568 |
| 480 | read | 262144 bytes | 148.902 | 11.22 | 2272 |
| 480 | multi-read | 128 items | 1.760 | 5.92 | 28 |
| 480 | multi-read | 512 items | 6.874 | 6.56 | 104 |
| 480 | multi-read | 2048 items | 26.480 | 7.83 | 412 |
| 480 | multi-write | 128 items | 1.803 | 6.00 | 28 |
| 480 | multi-write | 512 items | 6.646 | 6.59 | 104 |
| 480 | multi-write | 2048 items | 27.255 | 9.23 | 412 |

Over these tested sizes, elapsed times are broadly proportional to data/item
count; larger PDUs reduce scalar fragmentation and multi-write exchanges.
These results do not justify a speculative client optimization. They also do
not establish asymptotic complexity: timing includes Python peer and localhost
network costs and uses only three samples. External scheduling, allocator state
and machine load affect results.

RSS is sampled by the parent on completion messages, so the child may already
have advanced into the next operation. Samples can be missed when the child
exits; they are neither peaks nor allocation counts. Harness input/verification
allocations are included in the process's resident memory. No leak-freedom or
physical-PLC performance claim follows.

The final full emulator/scripted-peer suite passed separately, including six
small benchmark correctness cases. No core optimization, timing gate or toolchain
upgrade was introduced.
