import LeanS7.Client

namespace LeanS7.StatefulFaultIntegration

def run (host portString operation expected : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let client ← Client.connect {
    endpoint := .ipv4 address
    port := UInt16.ofNat port
    connectTimeoutMs := some 1000
    operationTimeoutMs := some 500
    transferReceiveTimeoutMs := some 2000
  }
  let error ← try
    if operation == "upload-compact" then
      let _ ← client.upload .dataBlock 7
      pure ()
    else if operation == "upload" then
      let _ ← client.fullUpload .dataBlock 7
      pure ()
    else
      let _ ← client.readSzl 0x0424 0
      pure ()
    pure (none : Option IO.Error)
  catch error => pure (some error)
  let some error := error | throw <| IO.userError "faulted conversation returned payload"
  let kind := classifyClientError error
  unless (if expected == "protocol" then kind == .protocol
    else kind == .disconnected || kind == .transport) do
    throw <| IO.userError s!"unexpected fault category {repr kind}: {error}"
  if ← client.isConnected then
    throw <| IO.userError "faulted conversation left connection usable"
  client.disconnect
  IO.println s!"stateful peer passed: {operation}/{expected}"

end LeanS7.StatefulFaultIntegration
