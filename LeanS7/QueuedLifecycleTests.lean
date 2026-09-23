import LeanS7.Client

namespace LeanS7.QueuedLifecycleTests

open Std.Net

private def payload (index : Nat) : ByteArray :=
  ByteArray.mk <| (Array.range 700).map fun offset =>
    UInt8.ofNat ((index * 23 + offset * 31) % 256)

/-- The first reply remains held while this bounded diagnostic wait establishes
    actual gate entry, not merely task creation. Launching one task at a time
    establishes their FIFO admission order independently of worker scheduling. -/
private def awaitAdmission (client : Client) (expected : Nat) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 3000
  repeat
    let count ← client.pendingOperationCount
    if count == expected then return
    if count > expected then
      throw <| IO.userError s!"queue admission overshot {expected}: {count}"
    if (← IO.monoMsNow) >= deadline then
      throw <| IO.userError s!"queue admission timed out at {count}, expected {expected}"
    IO.sleep 1

private def requireRead (task : Task (Except IO.Error ByteArray))
    (index : Nat) (expectedError : Option ClientErrorKind) : IO Unit := do
  match ← IO.wait task with
  | .ok value =>
    if expectedError.isSome then
      throw <| IO.userError s!"queued read {index} unexpectedly succeeded"
    unless value == payload index do
      throw <| IO.userError s!"queued read {index} returned a mixed payload"
  | .error error =>
    unless expectedError == some (classifyClientError error) do
      throw <| IO.userError s!"queued read {index} unexpected error: {error}"

/-- Independent peers cover queued explicit closure, reconnect inside an active
    read, terminal decode failure, recoverable PLC/input rejection, and lost write
    acknowledgements. There is no public explicit reconnect operation: reconnect
    here is the read-only retry already admitted ahead of explicit disconnect. -/
def runIntegration (host portString mode : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid queued lifecycle port"
  let some address := IPv4Addr.ofString host | throw <| IO.userError "invalid queued lifecycle host"
  unless ["disconnect", "reconnect", "protocol", "plc", "invalid", "write-drop"].contains mode do
    throw <| IO.userError "invalid queued lifecycle mode"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port
    connectTimeoutMs := some 1000, operationTimeoutMs := some 3000
    transferReceiveTimeoutMs := some 10000, reconnectRetries := 1
  }
  try
    let first ← IO.asTask do
      if mode == "write-drop" then
        client.dbWrite 1 0 (ByteArray.mk #[42])
        pure ByteArray.empty
      else client.dbRead 1 0 700
    awaitAdmission client 1
    let _ ← (← IO.getStdin).getLine
    let middle ← IO.asTask <| client.dbRead 1
      (if mode == "invalid" then 0x200000 else 1000) 700
    awaitAdmission client 2
    let recovery ← IO.asTask do
      if mode == "protocol" then
        let _ ← client.readMulti #[{
          area := .dataBlocks, dbNumber := 1, start := 2000, count := 700
        }]
        pure ByteArray.empty
      else if mode == "write-drop" then
        let _ ← client.getPlcDateTime
        pure ByteArray.empty
      else client.dbRead 1 2000 700
    awaitAdmission client 3
    let closing ← IO.asTask client.disconnect
    awaitAdmission client 4
    let late ← IO.asTask <| client.dbRead 1 3000 700
    awaitAdmission client 5
    let closingAgain ← IO.asTask client.disconnect
    awaitAdmission client 6
    IO.println "queued lifecycle admitted 6"
    (← IO.getStdout).flush
    let poisoned := mode == "protocol" || mode == "write-drop"
    let firstError := if mode == "protocol" then some ClientErrorKind.protocol
      else if mode == "write-drop" then some ClientErrorKind.disconnected
      else if mode == "plc" then some ClientErrorKind.plcRejected else none
    requireRead first 0 firstError
    requireRead middle 1 (if poisoned then some .disconnected
      else if mode == "invalid" then some .invalidInput else none)
    requireRead recovery 2 (if poisoned then some .disconnected else none)
    for task in #[closing, closingAgain] do
      match ← IO.wait task with
      | .ok () => pure ()
      | .error error => throw error
    requireRead late 3 (some .disconnected)
    if ← client.isConnected then
      throw <| IO.userError "queued disconnect resurrected its client"
    unless (← client.pendingOperationCount) == 0 do
      throw <| IO.userError "completed lifecycle queue retained operations"
    -- Idempotence extends beyond the two concurrently admitted closes.
    client.disconnect
    unless (← client.pendingOperationCount) == 0 do
      throw <| IO.userError "idempotent disconnect retained an operation"
    IO.println s!"queued lifecycle {mode} passed"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.QueuedLifecycleTests
