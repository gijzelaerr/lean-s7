import LeanS7.Client

namespace LeanS7.UserDataCompletionTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def run : IO Unit := do
  for payload in #[ByteArray.empty, bytes #[42], bytes (Array.range 255 |>.map UInt8.ofNat)] do
    let response : S7.UserDataResponse := {
      reference := 2, group := 7, subfunction := 1, sequence := 1,
      dataUnitReference := 1, hasMoreData := false, error := 0,
      returnCode := 255, transportSize := 9, payload }
    match S7.requireCompleteUserData response with
    | .ok actual => require (actual == payload) "complete USER_DATA payload changed"
    | .error error => throw <| IO.userError s!"complete USER_DATA rejected: {repr error}"
    match S7.requireCompleteUserData { response with hasMoreData := true } with
    | .error _ => pure ()
    | .ok _ => throw <| IO.userError "incomplete USER_DATA payload exposed"
  IO.println "USER_DATA completion model tests passed"

private def operation (client : Client) (service : String) : IO Unit := do
  match service with
  | "read-clock" =>
      let clock ← client.getPlcDateTime
      require (clock.year == 2026 && clock.month == 9 && clock.day == 23)
        "complete clock reply changed value"
  | "blocks" =>
      let counts ← client.listBlocks
      require (counts.dataBlocks == 1) "complete block-count reply changed value"
  | "set-clock" => client.setPlcDateTime {
      year := 2026, month := 9, day := 23, hour := 12, minute := 0, second := 0,
      millisecond := 0, weekday := 4 }
  | "set-password" => client.setSessionPassword "test"
  | "clear-password" => client.clearSessionPassword
  | _ => throw <| IO.userError "unknown completion test service"

def runIntegration (host portString service mode : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let client ← Client.connect {
    endpoint := .hostname host, port := UInt16.ofNat port,
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000,
    reconnectRetries := 1, allowPotentiallyMutatingRetries := true }
  try
    if mode == "complete" then
      operation client service
      require (← client.isConnected) "complete reply poisoned connection"
    else
      let error ← try
        operation client service
        pure (none : Option IO.Error)
      catch error => pure (some error)
      let some error := error | throw <| IO.userError "incomplete reply silently accepted"
      require (classifyClientError error == .protocol) "incomplete reply category changed"
      require (((toString error).splitOn "unexpected USER_DATA continuation").length > 1)
        "incomplete reply missed completion diagnostic"
      require (!(← client.isConnected)) "incomplete reply left connection usable"
      let later ← try
        client.dbWriteUInt8 1 0 99
        pure false
      catch error => pure (classifyClientError error == .disconnected)
      require later "later write escaped poisoned session"
    client.disconnect
    IO.println s!"USER_DATA completion passed: {service}/{mode}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.UserDataCompletionTests
