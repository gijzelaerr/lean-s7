import LeanS7.Client

namespace LeanS7.ScalabilityBenchTests

private def data (start count : Nat) : ByteArray :=
  bytes ((Array.range count).map fun index => UInt8.ofNat ((start + index) * 37 + 11))

/-- Timings cover one actual public operation, excluding connection, warmup and
    correctness checking. No machine-dependent performance threshold is asserted. -/
def runIntegration (host portString mode sizeString roundsString : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some size := sizeString.toNat? | throw <| IO.userError "invalid benchmark size"
  let some rounds := roundsString.toNat? | throw <| IO.userError "invalid benchmark rounds"
  unless port ≤ 65535 && 1 ≤ rounds && rounds ≤ 16 && 1 ≤ size && size ≤ 262144 do
    throw <| IO.userError "benchmark bounds exceeded"
  unless ["read","multi-read","multi-write"].contains mode do throw <| IO.userError "invalid benchmark mode"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port
    connectTimeoutMs := some 2000, operationTimeoutMs := some 5000
    transferReceiveTimeoutMs := some 60000, reconnectRetries := 0 }
  try
    let count := if mode == "read" then 1 else size
    let ranges := (Array.range count).map fun index => ({
      area := .dataBlocks, dbNumber := 1
      start := index * 2, count := if mode == "read" then size else 1 } : S7.MemoryRange)
    let items := ranges.map fun range => ({ range, payload := data range.start range.count } : S7.WriteItem)
    for iteration in [:rounds + 1] do
      let started ← IO.monoNanosNow
      if mode == "read" then
        let result ← client.dbRead 1 0 size
        let elapsed := (← IO.monoNanosNow) - started
        unless result == data 0 size do throw <| IO.userError "fragmented benchmark read corrupted bytes"
        if iteration > 0 then IO.println s!"benchmark sample {elapsed}"
      else if mode == "multi-read" then
        let results ← client.readMulti ranges
        let elapsed := (← IO.monoNanosNow) - started
        unless results.size == count do throw <| IO.userError "benchmark lost read items"
        for index in [:count] do
          unless results[index]? == some (.success (data (index * 2) 1)) do
            throw <| IO.userError "benchmark read reordered bytes"
        if iteration > 0 then IO.println s!"benchmark sample {elapsed}"
      else
        let results ← client.writeMulti items
        let elapsed := (← IO.monoNanosNow) - started
        unless results.size == count && results.all (· == .success) do
          throw <| IO.userError "benchmark lost write results"
        if iteration > 0 then IO.println s!"benchmark sample {elapsed}"
      (← IO.getStdout).flush
    client.disconnect
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.ScalabilityBenchTests
