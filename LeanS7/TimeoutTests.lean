import LeanS7.Client

namespace LeanS7.TimeoutTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def run : IO Unit := do
  let a : Std.Net.SocketAddress := .v4 <| Std.Net.SocketAddressV4.mk (Std.Net.IPv4Addr.ofParts 127 0 0 1) 102
  let b : Std.Net.SocketAddress := .v4 <| Std.Net.SocketAddressV4.mk (Std.Net.IPv4Addr.ofParts 127 0 0 1) 103
  require (Transport.uniqueAddresses #[a, a, b, a, b] == #[a, b])
    "resolver dedup changed candidate order or distinct ports"
  for budget in #[none, some 0, some 1, some Transport.maximumTimeoutMs] do
    Transport.validateTimeoutMs budget
    let deadline ← Transport.receiveDeadline budget
    require (deadline.isSome == budget.isSome) "timeout optionality changed"
  for budget in #[Transport.maximumTimeoutMs + 1, 2^64, 2^100] do
    let rejected ← try
      Transport.validateTimeoutMs (some budget)
      pure false
    catch error => pure (classifyClientError error == .invalidInput)
    require rejected "timeout silently wrapped"
    for field in [:3] do
      let rejected ← try
        let client ← Client.connect {
          endpoint := .hostname "invalid.test", port := 1
          connectTimeoutMs := some (if field == 0 then budget else 1000)
          operationTimeoutMs := some (if field == 1 then budget else 1000)
          transferReceiveTimeoutMs := some (if field == 2 then budget else 1000) }
        client.disconnect
        pure false
      catch error => pure (classifyClientError error == .invalidInput)
      require rejected "invalid client timeout reached DNS/network IO"
  IO.println "timeout range tests passed"

def runIntegration (host portString mode : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let stalled := mode == "stalled"
  let count := if stalled then 4 else 24
  for index in [:count] do
    let expectedFailure := stalled || index % 3 == 1
    let outcome ← try
      let client ← Client.connect {
        endpoint := .hostname host, port := UInt16.ofNat port
        connectTimeoutMs := some (if stalled then 100 else Transport.maximumTimeoutMs)
        operationTimeoutMs := some 1000 }
      client.disconnect
      pure (none : Option IO.Error)
    catch error => pure (some error)
    match outcome with
    | none => require (!expectedFailure) "failed connection unexpectedly succeeded"
    | some error =>
        require expectedFailure s!"valid connection failed: {error}"
        require (classifyClientError error == (if stalled then .timeout else .protocol))
          s!"cleanup changed initiating error: {error}"
  IO.println s!"timeout cleanup passed: {mode}/{count} attempts"

end LeanS7.TimeoutTests
