import LeanS7.Client

namespace LeanS7.NativeInteropTests

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"native interop: {label}"

private def initial (db offset count : Nat) : ByteArray :=
  bytes <| (Array.range count).map fun index => UInt8.ofNat (db * 3 + (offset + index) * 17 + 3)

private def written (count : Nat) : ByteArray :=
  bytes <| (Array.range count).map fun index => UInt8.ofNat (index * 37 + 11)

private def multiPayload (index : Nat) : ByteArray :=
  bytes #[UInt8.ofNat index, UInt8.ofNat (index * 11), UInt8.ofNat (255 - index)]

/-- Exercises actual Client IO against a separately implemented native endpoint.
    Assertions are bounded regression evidence, not controller qualification. -/
def runIntegration (host portString pduString : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid native port"
  let some pdu := pduString.toNat? | throw <| IO.userError "invalid native PDU"
  unless port > 0 && port ≤ 65535 && [240, 480].contains pdu do
    throw <| IO.userError "invalid native test profile"
  let client ← Client.connect {
    endpoint := .hostname host, port := UInt16.ofNat port,
    operationTimeoutMs := some 3000, transferReceiveTimeoutMs := some 10000
  }
  try
    require ((← client.negotiatedPduLength).toNat == pdu) "negotiated PDU"
    for db in [1, 2] do
      require ((← client.dbRead (UInt16.ofNat db) 0 4096) == initial db 0 4096)
        s!"DB{db} full initial memory"
    client.dbWrite 1 1275 (written 1401)
    require ((← client.dbRead 1 1275 1401) == written 1401) "chunked write/read"
    client.dbWriteString 1 64 8 "éS7"
    require ((← client.dbReadString 1 64) == "éS7") "Latin-1 STRING"
    client.dbWriteWString 1 128 8 "A🌍é"
    require ((← client.dbReadWString 1 128) == "A🌍é") "surrogate WSTRING"
    client.dbWriteBit 1 200 3 true
    require (← client.dbReadBit 1 200 3) "bit update"
    let items : Array S7.WriteItem := (Array.range 40).map fun index => {
      range := { area := .dataBlocks, dbNumber := 2, start := 512 + index * 7, count := 3 }
      payload := multiPayload index
    }
    let statuses ← client.writeMulti items
    require (statuses.size == 40 && statuses.all (fun status => status == .success)) "batched writes"
    let results ← client.readMulti (items.map (·.range))
    require (results.size == 40) "batched read count"
    for (result, index) in results.zipIdx do
      require (result == .success (multiPayload index)) s!"batched read {index}"
    for (area, code) in [(S7.Area.processInputs, 0), (.processOutputs, 1), (.markers, 2)] do
      let expected := bytes <| (Array.range 512).map fun i => UInt8.ofNat (code * 31 + i * 13)
      require ((← client.readArea area 0 0 512) == expected) "process-image/marker read"
      client.writeArea area 0 33 (written 311)
      require ((← client.readArea area 0 33 311) == written 311) "process-image/marker write"
    let missing ← try
      discard <| client.dbRead 777 0 1
      pure (none : Option IO.Error)
      catch error => pure (some error)
    require (missing.map classifyClientError == some .plcRejected && (← client.isConnected))
      "missing DB rejection remains recoverable"
    require ((← client.dbRead 2 0 1) == initial 2 0 1) "reuse after rejection"
    for db in [1, 2] do
      let info ← client.getBlockInfo .dataBlock (UInt16.toNat db)
      require (info.number == db && info.blockType == 0 && info.subBlockType == 0x0a &&
        info.mc7Size == 4096 && info.loadSize == 4188) "native DB metadata profile"
    -- The official native server implements neither upload nor download: it
    -- answers every start-upload with a "need password" header error. That is
    -- independent evidence only for the refusal path: the client must surface a
    -- PLC rejection, keep the connection and not leave a pending operation.
    -- Positive upload/full-upload evidence still needs an implementing endpoint.
    for upload in [client.upload .dataBlock 1, client.fullUpload .dataBlock 1] do
      let refused ← try
        discard upload
        pure (none : Option IO.Error)
        catch error => pure (some error)
      require (refused.map classifyClientError == some .plcRejected && (← client.isConnected))
        s!"native upload refusal is a recoverable PLC rejection: {refused.map toString} connected={← client.isConnected}"
    require ((← client.dbRead 1 0 4) == initial 1 0 4) "reuse after upload refusal"
    let state ← client.getCpuState
    require (state == .running) "native CPU-state query"
    require ((← client.pendingOperationCount) == 0 && (← client.isConnected)) "final healthy lifecycle"
    client.disconnect
    IO.println s!"native endpoint client checks passed: PDU={pdu}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.NativeInteropTests
