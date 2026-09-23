import LeanS7.Client

namespace LeanS7.ResourceStressTests

def runIntegration (host portString : String) (rounds : Nat := 1) : IO Unit := do
  unless 1 ≤ rounds && rounds ≤ 1000 do throw <| IO.userError "invalid stress rounds"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  for batch in [:18] do
    for offset in [:12 * rounds] do
      let index := batch * 12 * rounds + offset
      let mode := index % 4
      let outcome ← try
        let client ← Client.connect {
          endpoint := .ipv4 address, port := UInt16.ofNat port
          connectTimeoutMs := some (if mode == 2 then 20 else 1000)
          operationTimeoutMs := some 1000, reconnectRetries := 1 }
        try
          let data ← client.dbRead 1 0 1
          unless data == bytes #[42] do throw <| IO.userError "stress read value changed"
        finally client.disconnect
        pure (none : Option IO.Error)
      catch error => pure (some error)
      match outcome with
      | none =>
          if mode == 1 || mode == 2 then throw <| IO.userError "stress fault accepted"
      | some error =>
          let expected := if mode == 1 then ClientErrorKind.protocol else .timeout
          if (mode != 1 && mode != 2) || classifyClientError error != expected then
            throw <| IO.userError s!"stress initiating error changed at {index}: {error}"
    if batch ≥ 1 then
      IO.println s!"resource sample {batch - 1}"
      (← IO.getStdout).flush
      unless (← (← IO.getStdin).getLine).trimAscii.toString == "continue" do
        throw <| IO.userError "resource stress sample barrier failed"
  IO.println s!"resource stress passed: {216 * rounds} attempts, {54 * rounds} retry reconnects"

end LeanS7.ResourceStressTests
