import LeanS7.Client

namespace LeanS7.ConcurrencyTests

open Std.Net

private def payload (index : Nat) : ByteArray :=
  ByteArray.mk <| (Array.range 700).map fun offset => UInt8.ofNat ((index * 19 + offset * 37) % 256)

/-- The peer holds the first wire request until the process has launched the
    competing calls. The stdin/stdout barrier avoids timing-based scheduling. -/
def runIntegration (host portString mode : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid concurrency port"
  let some address := IPv4Addr.ofString host | throw <| IO.userError "invalid concurrency host"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port
    connectTimeoutMs := some 1000
    operationTimeoutMs := some 3000, transferReceiveTimeoutMs := some 10000
    reconnectRetries := if mode == "reconnect" then 1 else 0
  }
  try
    let first ← IO.asTask (client.dbRead 1 0 700)
    let _ ← (← IO.getStdin).getLine
    let rest ← (Array.range 15).mapM fun index =>
      IO.asTask (client.dbRead 1 ((index + 1) * 1000) 700)
    let closing ← if mode == "disconnect" then
      some <$> IO.asTask client.disconnect
      else pure none
    IO.println "concurrency calls launched"
    (← IO.getStdout).flush
    let mut successes := 0
    for index in [:16] do
      let task := if index == 0 then first else rest[index - 1]!
      match ← IO.wait task with
      | .ok value =>
        if mode == "failure" then throw <| IO.userError "failed connection returned a successful queued read"
        unless value == payload index do throw <| IO.userError "concurrent response/payload mixed"
        successes := successes + 1
      | .error error =>
        if mode == "success" || mode == "reconnect" then throw error
        let expected := if mode == "failure" && index == 0 then
          ClientErrorKind.protocol else .disconnected
        unless classifyClientError error == expected do
          throw <| IO.userError s!"unexpected queued failure: {error}"
    if let some task := closing then
      match ← IO.wait task with
      | .ok () => pure ()
      | .error error => throw error
    if mode == "success" || mode == "reconnect" then
      unless successes == 16 do throw <| IO.userError "lost concurrent operation"
    if mode == "disconnect" then
      unless successes >= 1 do throw <| IO.userError "disconnect interrupted its earlier active transfer"
    if mode == "failure" || mode == "disconnect" then
      if ← client.isConnected then throw <| IO.userError "closed connection resurrected"
    client.disconnect
    let late ← try
      let _ ← client.dbRead 1 0 1
      pure false
      catch error => pure (classifyClientError error == .disconnected)
    unless late do throw <| IO.userError "explicit disconnect allowed a later read"
    IO.println s!"concurrency {mode} passed"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.ConcurrencyTests
