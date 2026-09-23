import LeanS7.Client

namespace LeanS7.RetryBudgetTests

private def require (value : Bool) (label : String) : IO Unit :=
  unless value do throw <| IO.userError s!"retry budget: {label}"

def run : IO Unit := do
  let budgets := (Array.range 65) ++ #[255,65536,4294967295]
  let kinds := #[ClientErrorKind.invalidInput, .protocol, .plcRejected, .timeout,
    .disconnected, .lifecycle, .transport, .other]
  let mut checked := 0
  for remaining in budgets do
    for closed in [false,true] do
      for kind in kinds do
        for safety in [RetrySafety.readOnly, .potentiallyMutating] do
          for allow in [false,true] do
            let eligible := !closed && remaining > 0 &&
              ([ClientErrorKind.timeout,.disconnected,.transport].contains kind) &&
              (safety == .readOnly || allow)
            let expected := if eligible then some (remaining - 1) else none
            require (retryBudgetAfter remaining closed kind safety allow == expected)
              s!"decision {remaining}/{closed}/{repr kind}/{repr safety}/{allow}"
            checked := checked + 1
  require (checked == 4352) "decision coverage"
  -- Repeated pure decisions stop exactly at zero, never wrap or replenish.
  for initial in [:65] do
    let mut remaining := initial
    let mut count := 0
    repeat
      match retryBudgetAfter remaining false .timeout .readOnly false with
      | none => break
      | some next =>
        require (next < remaining) "nondecreasing allowance"
        remaining := next
        count := count + 1
    require (count == initial && remaining == 0) "repeated decision accounting"
  IO.println s!"retry budget unit tests passed: {checked} decisions and 65 repeated chains"

def runIntegration (host portString mode budgetString dropsString : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some budget := budgetString.toNat? | throw <| IO.userError "invalid retry budget"
  let some drops := dropsString.toNat? | throw <| IO.userError "invalid drop count"
  require (port ≤ 65535 && budget ≤ 4 && drops ≤ 5) "invalid campaign bounds"
  require (["read","raw","raw-opt-in","write","write-opt-in"].contains mode) "invalid mode"
  let replay := mode == "read" || mode.endsWith "opt-in"
  let succeeds := drops == 0 || (replay && drops ≤ budget)
  let attempts := if succeeds then drops + 1 else if replay then budget + 1 else 1
  let client ← Client.connect {
    endpoint := .ipv4 address
    port := UInt16.ofNat port
    connectTimeoutMs := some 1000
    operationTimeoutMs := some 1000
    reconnectRetries := budget
    allowPotentiallyMutatingRetries := mode.endsWith "opt-in" }
  try
    if mode.startsWith "write" then
      match ← client.writeAreaDetailed .dataBlocks 1 0 (bytes #[42]) with
      | .ok progress =>
        require succeeds "write succeeded beyond allowance"
        require (progress.attempts.size == attempts && progress.acknowledged.size == 1 &&
          progress.replayedUncertain.size == drops && progress.uncertain.isEmpty)
          "successful replay uncertainty/count"
        for index in [:progress.attempts.size] do
          let some attempt := progress.attempts[index]? | throw <| IO.userError "missing replay attempt"
          require (attempt.location.itemIndex == none && attempt.location.chunkByteOffset == 0 &&
            attempt.location.range == { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 } &&
            attempt.outcome == (if index + 1 == attempts then .itemResult .success else .replayedUnknown))
            "successful replay chronology/provenance"
      | .error failure =>
        require (!succeeds && failure.kind == .disconnected) "write failure category"
        require (failure.progress.attempts.size == attempts && failure.progress.acknowledged.isEmpty &&
          failure.progress.replayedUncertain.size == attempts - 1 &&
          failure.progress.uncertain.size == 1) "exhausted write uncertainty/count"
        for index in [:failure.progress.attempts.size] do
          let some attempt := failure.progress.attempts[index]? | throw <| IO.userError "missing failed replay attempt"
          require (attempt.location.itemIndex == none && attempt.location.chunkByteOffset == 0 &&
            attempt.location.range == { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 } &&
            attempt.outcome == (if index + 1 == attempts then .pending else .replayedUnknown))
            "exhausted replay chronology/provenance"
    else
      let outcome ← try
        if mode == "read" then
          require ((← client.dbRead 1 0 1) == bytes #[42]) "read payload"
        else
          let .ok request := S7.encodeAreaRead 10 {
            area := .dataBlocks, dbNumber := 1, start := 0, count := 1 }
            | throw <| IO.userError "raw request encoding"
          let raw ← client.rawExchange 10 request
          let .ok response := S7.decodeResponse raw | throw <| IO.userError "raw response encoding"
          let .ok data := S7.decodeAreaRead 10 .dataBlocks 1 response
            | throw <| IO.userError "raw response payload decoding"
          require (data == bytes #[42]) "raw payload"
        pure true
      catch error =>
        require (!succeeds && classifyClientError error == .disconnected) "read/raw failure category"
        pure false
      require (outcome == succeeds) "read/raw result"
    require ((← client.isConnected) == succeeds) "post-operation lifecycle"
    if !succeeds then
      let rejected ← try discard <| client.dbRead 1 0 1; pure false
        catch error => pure (classifyClientError error == .disconnected)
      require rejected "fresh operation resurrected exhausted session"
    client.disconnect
    client.disconnect
    require ((← client.pendingOperationCount) == 0) "queue cleanup"
    IO.println s!"retry budget live {mode} allowance={budget} drops={drops} attempts={attempts} passed"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.RetryBudgetTests
