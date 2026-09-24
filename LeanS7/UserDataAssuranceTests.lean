import LeanS7.Client

namespace LeanS7.UserDataAssuranceTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def packet (group subfunction sequence unit flag transport code : UInt8)
    (payload : ByteArray) : ByteArray :=
  let parameters := bytes #[0, 1, 0x12, 8, 0x12, UInt8.lor 0x80 group,
    subfunction, sequence, unit, flag, 0, 0]
  let data := bytes #[code, transport] ++ uint16BE (UInt16.ofNat payload.size) ++ payload
  bytes #[0x32, 7, 0, 0, 0, 1, 0, 12] ++ uint16BE (UInt16.ofNat data.size) ++ parameters ++ data

def run : IO Unit := do
  let mut transportCases := 0
  for (group, subfunction) in #[(4, 1), (3, 2), (7, 1), (7, 2), (5, 1), (5, 2)] do
    for payload in #[ByteArray.empty, bytes #[0xde, 0xad]] do
      for transport in [:256] do
        let raw := packet group subfunction 0xff 0 0 (UInt8.ofNat transport) 0xff payload
        match S7.decodeUserDataResponse 1 group subfunction raw with
        | .ok response =>
          require (transport == 9 && response.payload == payload)
            "USER_DATA accepted a non-octet successful payload"
        | .error (.invalidField offset _) =>
          require (transport != 9 && offset == 23) "USER_DATA transport rejection changed"
        | _ => throw <| IO.userError "unexpected USER_DATA transport outcome"
        transportCases := transportCases + 1
  -- The service-scoped empty null acknowledgement has exactly one accepted
  -- transport discriminator. Nonempty and continuing forms are not ACKs.
  for (group, subfunction) in #[(7, 2), (5, 1), (5, 2)] do
    for transport in [:256] do
      for payload in #[ByteArray.empty, bytes #[0xaa]] do
        for flag in #[0, 1] do
          let raw := packet group subfunction 0 0 flag (UInt8.ofNat transport) 0x0a payload
          require ((S7.decodeUserDataResponse 1 group subfunction raw).toBool ==
            (transport == 0 && payload.isEmpty && flag == 0))
            "USER_DATA null acknowledgement extent/discriminator gate changed"
  for (group, subfunction) in #[(4, 1), (3, 2), (7, 1), (5, 3), (7, 3)] do
    require (!(S7.decodeUserDataResponse 1 group subfunction
      (packet group subfunction 0 0 0 0 0x0a ByteArray.empty)).toBool)
      "USER_DATA treated 0x0a as a universal success code"
  for (group, subfunction) in #[(4, 1), (7, 2), (5, 1)] do
    for code in [:256] do
      let transport := if code == 0x0a then 0 else 9
      require ((S7.decodeUserDataResponse 1 group subfunction
        (packet group subfunction 0 0 0 transport (UInt8.ofNat code) ByteArray.empty)).toBool ==
        (code == 0xff || (code == 0x0a && group != 4)))
        "USER_DATA successful return-code whitelist changed"
    for flag in [:256] do
      require ((S7.decodeUserDataResponse 1 group subfunction
        (packet group subfunction 0 0 (UInt8.ofNat flag) 9 0xff ByteArray.empty)).toBool ==
        (flag < 2)) "USER_DATA continuation flag whitelist changed"
  -- Parameter errors dominate even a syntactically perfect acknowledgement.
  for (group, subfunction) in #[(7, 2), (5, 1), (5, 2)] do
    let raw := (packet group subfunction 0 0 0 0 0x0a ByteArray.empty).set! 20 0x81
    match S7.decodeUserDataResponse 1 group subfunction raw with
    | .error (.remoteFailure 20 _) => pure ()
    | _ => throw <| IO.userError "USER_DATA null acknowledgement masked parameter error"
  -- Sequence and unit bytes are opaque: every byte is preserved, including
  -- zero, repeats, and wrap-looking values. Only identity changes reject.
  for sequence in [:256] do
    for unit in [:256] do
      let .ok response := S7.decodeUserDataResponse 1 4 1
          (packet 4 1 (UInt8.ofNat sequence) (UInt8.ofNat unit) 1 9 0xff ByteArray.empty)
        | throw <| IO.userError "USER_DATA rejected opaque metadata bytes"
      require (response.sequence.toNat == sequence && response.dataUnitReference.toNat == unit &&
        response.hasMoreData) "USER_DATA changed opaque metadata"
      require ((S7.correlateUserDataFragment none response).toOption == some (UInt8.ofNat unit))
        "USER_DATA rejected initial opaque unit identity"
      require ((S7.correlateUserDataFragment (some (UInt8.ofNat unit)) response).toBool)
        "USER_DATA rejected stable opaque unit identity"
      require (!(S7.correlateUserDataFragment (some (UInt8.ofNat ((unit + 1) % 256))) response).toBool)
        "USER_DATA accepted changed fragment identity"
  IO.println s!"USER_DATA assurance passed: {transportCases} payload transport cases, scoped null ACKs, and 65,536 opaque metadata pairs"

def runIntegration (host portString operation scenario : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid USER_DATA peer port"
  require (port < 65536) "USER_DATA peer port out of range"
  let client ← Client.connect {
    endpoint := .hostname host, port := UInt16.ofNat port,
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000,
    transferReceiveTimeoutMs := some 2000, reconnectRetries := 1,
    -- Normal correlation skips a bounded number of stale references. This
    -- case deliberately exhausts an allowance of zero with its first stale
    -- response instead of misclassifying a subsequent peer EOF as protocol.
    maxStaleResponses := if scenario == "stale-reference" then 0 else 4 }
  try
    let action : IO Unit := do
      if operation == "szl" then
        let actual ← client.readSzl 0x0424
        require (actual.recordLength == 2 && actual.recordCount == 4 &&
          actual.data == bytes #[1, 2, 3, 4, 5, 6, 7, 8]) "USER_DATA SZL fragment assembly changed"
      else if operation == "blocks" then
        let actual ← client.listBlocksOfType .dataBlock
        require (actual == #[{ number := 1, flags := 0x11, language := 0x22 },
          { number := 513, flags := 0x33, language := 0x44 }])
          "USER_DATA block fragment assembly changed"
      else if operation == "set-clock" then
        client.setPlcDateTime {
          year := 2024, month := 2, day := 29, hour := 23,
          minute := 59, second := 58, millisecond := 123, weekday := 1 }
      else if operation == "set-password" then client.setSessionPassword "12345678"
      else if operation == "clear-password" then client.clearSessionPassword
      else throw <| IO.userError "unknown USER_DATA peer operation"
    if scenario == "valid" || scenario == "zero-unit" || scenario == "octet-ack" then
      action
      require (← client.isConnected) "valid USER_DATA poisoned the session"
    else
      let rejected ← try action; pure false catch error => do
        require (classifyClientError error == .protocol) "malformed USER_DATA category changed"
        pure true
      require rejected "malformed USER_DATA was accepted"
      require (!(← client.isConnected)) "malformed USER_DATA left a usable session"
      let laterRejected ← try
        discard <| client.readSzl 0x0424
        pure false
      catch error => pure (classifyClientError error == .disconnected)
      require laterRejected "fresh USER_DATA read escaped poisoned session"
    client.disconnect
    IO.println s!"USER_DATA full-stack assurance passed: {operation}/{scenario}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.UserDataAssuranceTests
