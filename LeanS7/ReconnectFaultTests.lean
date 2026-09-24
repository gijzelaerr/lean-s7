import LeanS7.Client

namespace LeanS7.ReconnectFaultTests

private def require (value : Bool) (label : String) : IO Unit :=
  unless value do throw <| IO.userError s!"reconnect fault: {label}"

private def checkProgress (progress : WriteProgress) (multi succeeds replayed : Bool) : IO Unit := do
  let width := if multi then 2 else 1
  require (progress.attempts.size == width * (if succeeds then 2 else 1)) "phantom wire attempt"
  require (progress.acknowledged.size == (if succeeds then width else 0)) "acknowledgement count"
  require (progress.replayedUncertain.size == (if replayed then width else 0)) "original lost-ACK uncertainty"
  require (progress.uncertain.size == (if replayed then 0 else width)) "pending uncertainty count"
  require progress.rejected.isEmpty "setup rejection misattributed to write"
  for index in [:progress.attempts.size] do
    let some attempt := progress.attempts[index]? | throw <| IO.userError "missing attempt"
    let item := index % width
    require (attempt.location.range == {
      area := .dataBlocks, dbNumber := 1, start := item * 4, count := 1 }) "write range provenance"
    require (attempt.location.itemIndex == (if multi then some item else none) &&
      attempt.location.chunkByteOffset == 0) "write caller provenance"
    let expected := if index >= width then WriteAttemptOutcome.itemResult .success
      else if replayed then .replayedUnknown else .pending
    require (attempt.outcome == expected) "write chronology"

/-- Retry connect stages consume allowance, but are not wire operation attempts. -/
def runIntegration (host portString mode fault budgetString failuresString : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some budget := budgetString.toNat? | throw <| IO.userError "invalid budget"
  let some failures := failuresString.toNat? | throw <| IO.userError "invalid failures"
  require (port <= 65535 && budget <= 4 && failures <= 4) "campaign bounds"
  require (["read", "raw", "write", "multi"].contains mode) "mode"
  require (["cotp-eof", "setup-eof", "cotp-invalid", "setup-invalid", "setup-reject", "setup-shrink", "deadline"].contains fault) "fault"
  let transient := fault.endsWith "eof"
  let succeeds := transient && failures < budget
  let expectedKind := if budget == 0 || transient then ClientErrorKind.disconnected
    else if fault == "setup-reject" then .plcRejected
    else if fault == "deadline" then .timeout else .protocol
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port
    connectTimeoutMs := some 1500, operationTimeoutMs := some 1500
    transferReceiveTimeoutMs := some (if fault == "deadline" then 200 else 5000)
    reconnectRetries := budget, allowPotentiallyMutatingRetries := true }
  try
    if mode == "write" || mode == "multi" then
      let result ← if mode == "write" then client.writeAreaDetailed .dataBlocks 1 0 (bytes #[42])
        else do
          match ← client.writeMultiDetailed #[
              { range := { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 }, payload := bytes #[42] },
              { range := { area := .dataBlocks, dbNumber := 1, start := 4, count := 1 }, payload := bytes #[43] }] with
          | .ok (results, progress) =>
            require (results == #[.success, .success]) "multi item result"
            pure (.ok progress)
          | .error failure => pure (.error failure)
      match result with
      | .ok progress =>
        require succeeds "unexpected write recovery"
        checkProgress progress (mode == "multi") true true
      | .error failure =>
        require (!succeeds && failure.kind == expectedKind) s!"write failure kind: {repr failure.kind} expected {repr expectedKind}"
        checkProgress failure.progress (mode == "multi") false (budget > 0)
    else
      let outcome ← try
        if mode == "read" then require ((← client.dbRead 1 0 1) == bytes #[42]) "read payload"
        else
          let .ok request := S7.encodeAreaRead 10 {
            area := .dataBlocks, dbNumber := 1, start := 0, count := 1 }
            | throw <| IO.userError "raw encoding"
          let raw ← client.rawExchange 10 request
          let .ok response := S7.decodeResponse raw | throw <| IO.userError "raw response"
          let .ok payload := S7.decodeAreaRead 10 .dataBlocks 1 response | throw <| IO.userError "raw payload"
          require (payload == bytes #[42]) "raw payload value"
        pure true
      catch error =>
        require (!succeeds && classifyClientError error == expectedKind)
          s!"read/raw failure: {error} expected {repr expectedKind}"
        pure false
      require (outcome == succeeds) "read/raw outcome"
    require ((← client.isConnected) == succeeds) "post-operation lifecycle"
    unless succeeds do
      let rejected ← try discard <| client.dbRead 1 0 1; pure false
        catch error => pure (classifyClientError error == .disconnected)
      require rejected "fresh call resurrected failed operation"
    client.disconnect
    client.disconnect
    require ((← client.pendingOperationCount) == 0) "queue cleanup"
    IO.println s!"reconnect fault {mode}/{fault} budget={budget} failures={failures} passed"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.ReconnectFaultTests
