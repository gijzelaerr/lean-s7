import LeanS7.Client

namespace LeanS7.ConnectionBudgetTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def request : COTP.ConnectionRequest := {
  sourceReference := 1, callingTsap := 0x0100, calledTsap := 0x0102 }

/-- No DNS/network is needed to check expiry before starting a stage. -/
def run : IO Unit := do
  let expired := some (← IO.monoMsNow)
  let started ← IO.mkRef false
  let outcome ← try
    Transport.withDeadline expired "expired stage" (started.set true)
    pure false
  catch error => pure (classifyClientError error == .timeout)
  require (outcome && !(← started.get)) "expired connection budget started work"
  let resolution ← try
    discard <| Transport.resolveUntil (.hostname "must-not-resolve.invalid") 102 expired
    pure false
  catch error => pure (classifyClientError error == .timeout)
  require resolution "expired resolution budget reached DNS"
  let candidates ← try
    discard <| Transport.connectResolvedUntil #[] request expired
    pure false
  catch error => pure (classifyClientError error == .timeout)
  require candidates "expired candidates returned a non-budget error"
  -- Keep the shared-budget regression, without requiring a hosted scheduler
  -- to finish the successful stage inside a 40 ms margin. A fresh budget
  -- would allow the second stage; the original deadline must expire instead.
  let deadline ← Transport.receiveDeadline (some 3000)
  Transport.withDeadline deadline "first stage" (IO.sleep 1000)
  let second ← try
    Transport.withDeadline deadline "second stage" (IO.sleep 2500)
    pure false
  catch error => pure (classifyClientError error == .timeout)
  require second "second connection stage received a fresh budget"
  Transport.withDeadline none "disabled budget" (pure ())
  IO.println "total connection budget unit tests passed"

def runIntegration (host firstPortString secondPortString mode : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString (if host == "localhost" then "127.0.0.1" else host)
    | throw <| IO.userError "invalid host"
  let some firstPort := firstPortString.toNat? | throw <| IO.userError "invalid first port"
  let some secondPort := secondPortString.toNat? | throw <| IO.userError "invalid second port"
  let start ← IO.monoMsNow
  let expectedTimeout := mode == "combined" || mode == "operation" || mode == "candidate-budget"
  let expectedProtocol := mode == "candidate-protocol"
  -- Success controls include hostname resolution and hosted scheduling;
  -- only the rejection controls intentionally need the tight shared budget.
  let connectionBudget := if expectedTimeout || expectedProtocol then 250 else 3000
  let outcome ← try
    if mode.startsWith "candidate-" then
      let first : Std.Net.SocketAddress := .v4 <| Std.Net.SocketAddressV4.mk address (UInt16.ofNat firstPort)
      let second : Std.Net.SocketAddress := .v4 <| Std.Net.SocketAddressV4.mk address (UInt16.ofNat secondPort)
      let connection ← Transport.connectResolved #[first, first, second, second] request
        (some connectionBudget)
      Transport.disconnect connection (some 1000)
    else
      let client ← Client.connect {
        -- Rejection peers isolate COTP/setup budgets from uncontrolled DNS
        -- latency. Hostname resolution stays exercised by success controls.
        endpoint := if expectedTimeout then .ipv4 address else .hostname host,
        port := UInt16.ofNat firstPort
        connectTimeoutMs := if mode == "disabled" then none else some connectionBudget
        operationTimeoutMs := some (if mode == "operation" then 80 else 1000) }
      client.disconnect
    pure (none : Option IO.Error)
  catch error => pure (some error)
  let elapsed := (← IO.monoMsNow) - start
  match outcome with
  | none => require (!expectedTimeout && !expectedProtocol) "connection unexpectedly succeeded"
  | some error =>
      require (expectedTimeout || expectedProtocol) s!"valid connection failed: {error}"
      require (classifyClientError error == (if expectedTimeout then .timeout else .protocol))
        s!"connection budget changed error category: {error}"
      -- Deliberately generous: the strict evidence is the refused/withheld
      -- next-stage response, not exact scheduler timing on a loaded machine.
      require (elapsed < 1500) s!"connection timeout did not return promptly: {elapsed} ms"
  IO.println s!"connection budget case passed: {mode}/{elapsed} ms"

end LeanS7.ConnectionBudgetTests
