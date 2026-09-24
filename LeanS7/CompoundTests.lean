import LeanS7.Client

namespace LeanS7.CompoundTests

private def bitArea (mode : String) : S7.Area :=
  if mode.startsWith "bit-input" then .processInputs
  else if mode.startsWith "bit-output" then .processOutputs else .dataBlocks

private def writeBit (client : Client) (mode : String) (bit : Nat) : IO Unit :=
  if bitArea mode == .dataBlocks then client.dbWriteBit 1 0 bit (!mode.endsWith "clear")
  else if mode.endsWith "clear" then client.cancelForceBit (bitArea mode) 0 bit
  else client.forceBit (bitArea mode) 0 bit true

private def readText (client : Client) (mode : String) : IO String :=
  if mode.startsWith "wstring" then client.dbReadWString 1 0
  else client.dbReadString 1 0

private def wait [Repr α] (task : Task (Except IO.Error α)) : IO α := do
  match ← IO.wait task with
  | .ok value => pure value
  | .error error => throw error

def runIntegration (host portString mode : String) (freshBudgetControl : Bool := false) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let deadlineCase := mode.endsWith "deadline"
  unless !freshBudgetControl || deadlineCase do
    throw <| IO.userError "fresh-budget control requires a deadline scenario"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port
    connectTimeoutMs := some 1000
    operationTimeoutMs := some (if deadlineCase then 6000 else 2000)
    transferReceiveTimeoutMs := some (if deadlineCase then 3000 else 6000)
    reconnectRetries := if mode == "bit-drop" then 1 else 0
    allowPotentiallyMutatingRetries := mode == "bit-drop"
  }
  try
    if mode.startsWith "bit-" && mode != "bit-drop" && !deadlineCase then
      let first ← IO.asTask (writeBit client mode 0)
      let _ ← (← IO.getStdin).getLine
      let rest ← (Array.range 7).mapM fun i => IO.asTask (writeBit client mode (i + 1))
      IO.println "compound calls launched"
      (← IO.getStdout).flush
      wait first
      for task in rest do wait task
      let area := bitArea mode
      let data ← client.readArea area (if area == .dataBlocks then 1 else 0) 0 1
      unless data == bytes #[if mode.endsWith "clear" then 0 else 255] do
        throw <| IO.userError "concurrent bit updates were lost"
    else if mode.endsWith "length-update" then
      let text ← readText client mode
      unless text == (if mode.startsWith "wstring" then "updated 🌍" else "updated") do
        throw <| IO.userError "valid current-length update was rejected or lost"
    else if mode == "string-success" || mode == "wstring-success" then
      let first ← IO.asTask (readText client mode)
      let _ ← (← IO.getStdin).getLine
      let competing ← IO.asTask (client.dbWriteUInt8 1 2000 99)
      IO.println "compound calls launched"
      (← IO.getStdout).flush
      let text ← wait first
      unless text == (if mode.startsWith "wstring" then "PLC 🚀" else "lean") do
        throw <| IO.userError "compound string value changed"
      wait competing
    else
      let error ← try
        if freshBudgetControl then
          -- Deliberately incorrect test-only substitute: separate public calls
          -- each obtain a fresh transfer budget. The peer must reject this.
          let headerSize := if mode.startsWith "bit-" then 1 else if mode.startsWith "wstring" then 4 else 2
          let header ← client.dbRead 1 0 headerSize
          if mode.startsWith "bit-" then client.dbWrite 1 0 (header.set! 0 (header[0]! ||| 1))
          else discard <| client.dbRead 1 0 222
        else if mode.startsWith "bit-" then writeBit client mode 0
        else discard <| readText client mode
        pure (none : Option IO.Error)
      catch error => pure (some error)
      let some error := error | throw <| IO.userError "compound fault unexpectedly succeeded"
      let kind := classifyClientError error
      if mode.endsWith "capacity-shrink" || mode.endsWith "capacity-grow" then
        unless ((toString error).splitOn "capacity changed during read").length > 1 do
          throw <| IO.userError s!"capacity change missed its specific diagnostic: {error}"
      unless (if deadlineCase then kind == .timeout else if mode == "bit-drop" then
        kind == .disconnected || kind == .transport else kind == .protocol) do
        throw <| IO.userError s!"unexpected compound failure {repr kind}: {error}"
      if ← client.isConnected then throw <| IO.userError "compound failure left session connected"
    client.disconnect
    IO.println s!"compound operation passed: {mode}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.CompoundTests
