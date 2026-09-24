import LeanS7.Client

namespace LeanS7.BlockInfoClientTests

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"block-info identity: {label}"

/-- Bounded live client observations, not an IO-equivalence or firmware proof. -/
def runIntegration (host portString scenario : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid block-info port"
  unless port > 0 && port ≤ 65535 &&
      ["zero", "max", "opaque", "mismatch", "preflight"].contains scenario do
    throw <| IO.userError "invalid block-info fixture"
  let client ← Client.connect {
    endpoint := .hostname host, port := UInt16.ofNat port,
    operationTimeoutMs := some 1000, reconnectRetries := 2,
    initialRequestReference := 0xffff
  }
  try
    if scenario == "preflight" then
      for number in [65536, 99999, 100000] do
        let outcome ← try discard <| client.getBlockInfo .dataBlock number
                          pure (none : Option IO.Error)
          catch error => pure (some error)
        check (outcome.map classifyClientError == some .invalidInput) "high number category"
        check ((← client.isConnected) && (← client.pendingOperationCount) == 0)
          "invalid input retains usable session and free gate"
    let number := if scenario == "zero" then 0 else if scenario == "max" then 65535 else 1
    let outcome ← try pure (.ok (← client.getBlockInfo .dataBlock number) : Except IO.Error S7.BlockInfo)
      catch error => pure (.error error)
    match outcome with
    | .ok info =>
        check (scenario != "mismatch" && info.number.toNat == number) "returned number"
        let (outer, subtype) := if scenario == "max" then (255, 255)
          else if scenario == "opaque" then (1, 165) else (0, 0)
        check (info.blockType.toNat == outer && info.subBlockType.toNat == subtype)
          "lossless independent type bytes"
        check ((← client.isConnected) && (← client.pendingOperationCount) == 0) "healthy cleanup"
    | .error error =>
        check (scenario == "mismatch" && classifyClientError error == .protocol) "mismatch category"
        check (!(← client.isConnected) && (← client.pendingOperationCount) == 0) "terminal cleanup"
        let fresh ← try discard <| client.getBlockInfo .dataBlock 1
                        pure (none : Option IO.Error)
          catch error => pure (some error)
        check (fresh.map classifyClientError == some .disconnected) "no terminal resurrection"
    client.disconnect
    IO.println s!"block-info identity passed: {scenario}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.BlockInfoClientTests
