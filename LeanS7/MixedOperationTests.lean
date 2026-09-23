import LeanS7.Client

namespace LeanS7.MixedOperationTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"mixed operations: {message}"

def runIntegration (host portString plan : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let config : ClientConfig := {
    endpoint := .ipv4 address, port := UInt16.ofNat port,
    connectTimeoutMs := some 500, operationTimeoutMs := some 500,
    reconnectRetries := 1 }
  let mut client ← Client.connect config
  try
    for (op, index) in plan.toList.zipIdx do
      let value := UInt8.ofNat (index * 17 + 3)
      let start := 10 + index
      let range : S7.MemoryRange := {
        area := .dataBlocks, dbNumber := 1, start, count := 1 }
      if op == 'r' || op == 'R' then
        require ((← client.dbRead 1 start 1) == bytes #[value]) "read/retry value"
      else if op == 'w' then
        client.dbWrite 1 start (bytes #[value])
      else if op == 'm' then
        let actual ← client.readMulti #[range, { range with start := start + 1 }]
        require (actual == #[.success (bytes #[value]), .failure 5]) "mixed read result order"
      else if op == 'n' then
        let actual ← client.writeMulti #[{ range, payload := bytes #[value] },
          { range, payload := bytes #[value + 1] }]
        require (actual == #[.success, .failure 5]) "duplicate write result order"
      else if op == 'x' then
        let error ← try
          client.dbWrite 1 start (bytes #[value])
          pure (none : Option IO.Error)
        catch error => pure (some error)
        let some error := error | throw <| IO.userError "write rejection accepted"
        require (classifyClientError error == .plcRejected) "write rejection category"
      else if op == 'c' then
        client.disconnect
        require (!(← client.isConnected)) "disconnect did not close"
        client ← Client.connect config
      else if op == 'z' then
        let error ← try
          discard <| client.dbRead 1 start 1
          pure (none : Option IO.Error)
        catch error => pure (some error)
        let some error := error | throw <| IO.userError "malformed read accepted"
        require (classifyClientError error == .protocol) "malformed category"
      else if op == 'd' then
        match ← client.writeAreaDetailed .dataBlocks 1 start (bytes #[value]) with
        | .ok _ => throw <| IO.userError "lost write ACK accepted"
        | .error failure =>
            require (failure.kind == .disconnected && failure.progress.uncertain.size == 1 &&
              failure.progress.acknowledged.isEmpty && failure.progress.attempts.size == 1)
              "lost write ACK progress/replay"
      else throw <| IO.userError s!"unknown mixed operation {op}"
      if op == 'z' || op == 'd' then
        require (!(← client.isConnected)) "terminal failure left session usable"
        let blocked ← try
          client.dbWrite 1 0 (bytes #[99])
          pure false
        catch error => pure (classifyClientError error == .disconnected)
        require blocked "write escaped terminal closure"
      else require (← client.isConnected) "recoverable operation closed session"
    client.disconnect
    IO.println s!"mixed operation plan passed: {plan}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.MixedOperationTests
