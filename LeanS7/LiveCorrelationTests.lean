import LeanS7.Client

namespace LeanS7.LiveCorrelationTests

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"live correlation: {label}"

/-- Bounded observable outcomes of actual mixed IO; this is not an IO-equivalence
    proof of the pure session model. The independent peer checks exact requests. -/
def runIntegration (host portString plan : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid correlation port"
  let tokens := plan.splitOn "|"
  unless port > 0 && port ≤ 65535 && tokens.length ≤ 12 do
    throw <| IO.userError "correlation fixture bounds exceeded"
  let client ← Client.connect {
    endpoint := .hostname host, port := UInt16.ofNat port
    operationTimeoutMs := some 1000, transferReceiveTimeoutMs := some 5000
    reconnectRetries := 2, maxStaleResponses := 2, initialRequestReference := 0xffff
  }
  try
    for (token, index) in tokens.zipIdx do
      let [kind, status, staleText, valueText] := token.splitOn ":"
        | throw <| IO.userError "invalid correlation token"
      let some stale := staleText.toNat? | throw <| IO.userError "invalid stale count"
      let some value := valueText.toNat? | throw <| IO.userError "invalid correlation byte"
      unless ["r", "w"].contains kind &&
          ["ok", "global", "item", "overflow", "protocol"].contains status &&
          stale ≤ 3 && value ≤ 255 do
        throw <| IO.userError "invalid correlation configuration"
      let terminal := status == "overflow" || status == "protocol"
      let expectedError := if terminal then ClientErrorKind.protocol else .plcRejected
      let offset := index * 16
      if kind == "r" then
        let outcome ← try pure (.ok (← client.dbRead 1 offset 1) : Except IO.Error ByteArray)
          catch error => pure (.error error)
        match outcome with
        | .ok data => require (status == "ok" && data == bytes #[UInt8.ofNat value]) "read payload/status"
        | .error error => require (status != "ok" && classifyClientError error == expectedError) "read error category"
      else
        let location : WriteLocation := {
          range := { area := .dataBlocks, dbNumber := 1, start := offset, count := 1 }
        }
        match ← client.writeAreaDetailed .dataBlocks 1 offset (bytes #[UInt8.ofNat value]) with
        | .ok progress =>
            require (status == "ok" && progress.attempts == #[{ location, outcome := .itemResult .success }]) "successful write trace"
            require (progress.acknowledged.size == 1 && progress.rejected.isEmpty &&
              progress.uncertain.isEmpty && progress.replayedUncertain.isEmpty) "successful write accounting"
        | .error failure =>
            require (status != "ok" && failure.kind == expectedError) "write error category"
            require (failure.progress.attempts == #[{ location, outcome := if terminal then .pending else .globalRejected }]) "failed write trace/reset"
            require (failure.progress.acknowledged.isEmpty && failure.progress.replayedUncertain.isEmpty &&
              failure.progress.rejected.size == (if terminal then 0 else 1) &&
              failure.progress.uncertain.size == (if terminal then 1 else 0)) "failed write accounting"
      require ((← client.isConnected) == !terminal) "recoverable versus terminal lifecycle"
      require ((← client.pendingOperationCount) == 0) "gate released after operation"
      if terminal then
        let fresh ← try discard <| client.dbRead 1 1024 1; pure (none : Option IO.Error)
          catch error => pure (some error)
        require (fresh.map classifyClientError == some .disconnected) "fresh call cannot resurrect terminal client"
    client.disconnect
    require (!(← client.isConnected) && (← client.pendingOperationCount) == 0) "explicit close"
    IO.println s!"live correlation passed: {tokens.length} operations"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.LiveCorrelationTests
