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
    let state ← client.getCpuState
    require (state == .running) "native CPU-state query"
    require ((← client.pendingOperationCount) == 0 && (← client.isConnected)) "final healthy lifecycle"
    -- Management services the official native server implements. Each rejection
    -- closes the session (as for any failed exchange), so rejections use a fresh client.
    let fresh : IO Client := Client.connect {
      endpoint := .hostname host, port := UInt16.ofNat port,
      operationTimeoutMs := some 3000, transferReceiveTimeoutMs := some 10000 }
    let rejected (action : Client → IO Unit) : IO (Option ClientErrorKind) := do
      let c ← fresh
      try
        action c
        return none
      catch error =>
        return some (classifyClientError error)
      finally
        try c.disconnect catch _ => pure ()
    let szlShape (id : Nat) : IO (Nat × Nat × Nat) := do
      let szl ← client.readSzl (UInt16.ofNat id) 0
      return (szl.recordLength.toNat, szl.recordCount.toNat, szl.data.size)
    require ((← szlShape 0x0011) == (28, 4, 112)) "native SZL 0x0011 shape"
    require ((← szlShape 0x0012) == (2, 23, 46)) "native SZL 0x0012 shape"
    require ((← szlShape 0x0424) == (20, 1, 20)) "native SZL 0x0424 shape"
    -- The native server never fragments SZL: it truncates data to the negotiated PDU
    -- while the header still announces the full length. The client rejects that
    -- inconsistent response instead of returning a short table.
    for (id, announced) in [(0x0000, 224), (0x001c, 340)] do
      let outcome ← rejected fun c => discard <| c.readSzl (UInt16.ofNat id) 0
      if pdu == 480 then
        require outcome.isNone s!"native SZL 0x{String.ofList (Nat.toDigits 16 id)} at PDU 480"
        require ((← szlShape id).2.2 == announced) "native SZL full table"
      else
        require (outcome == some .protocol) "native truncated SZL accepted at PDU 240"
    for id in [0x0111, 0x0131, 0x0232] do
      require ((← rejected fun c => discard <| c.readSzl (UInt16.ofNat id) 0) == some .plcRejected)
        "native unavailable SZL is a PLC rejection"
    require ((← rejected fun c => discard <| c.readSzl 0x0f00 0) == some .protocol)
      "native malformed SZL 0x0f00 accepted"
    let counts ← client.listBlocks
    require (counts == { dataBlocks := 2 }) "native block counts"
    let blocks ← client.listBlocksOfType .dataBlock
    require (blocks.map (fun b => (b.number, b.flags, b.language)) == #[(1, 34, 5), (2, 34, 5)])
      "native DB list"
    for blockType in [S7.BlockType.organizationBlock, .function] do
      require ((← rejected fun c => discard <| c.listBlocksOfType blockType) == some .plcRejected)
        "native empty block-type list is a PLC rejection"
    let now ← client.getPlcDateTime
    require (now.year ≥ 2024 && now.year ≤ 2089 && now.month ≥ 1 && now.month ≤ 12 &&
      now.day ≥ 1 && now.day ≤ 31 && now.hour < 24 && now.minute < 60 && now.second < 60)
      "native clock fields"
    -- The server acknowledges a set-clock with a null acknowledgement and keeps its own time.
    client.setPlcDateTime { year := 2026, month := 10, day := 13, hour := 9, minute := 8, second := 7, weekday := 3 }
    client.setSessionPassword "ABC"
    client.clearSessionPassword
    client.plcStop
    require ((← client.getCpuState) == .stopped) "native stop"
    client.plcHotStart
    require ((← client.getCpuState) == .running) "native hot start"
    client.plcStop
    client.plcColdStart
    require ((← client.getCpuState) == .running) "native cold start"
    -- The official native server implements neither upload nor download: it answers
    -- every start-upload with a "need password" header error. That is independent
    -- evidence for the refusal path only: the client reports a PLC rejection and,
    -- as for every failed block upload, ends the session cleanly (terminal cleanup)
    -- with no pending operation. Positive upload/full-upload evidence still needs an
    -- endpoint that implements those services.
    let refused ← try
      discard <| client.upload .dataBlock 1
      pure (none : Option IO.Error)
      catch error => pure (some error)
    require (refused.map classifyClientError == some .plcRejected)
      s!"native upload refusal is a PLC rejection: {refused.map toString}"
    require (!(← client.isConnected) && (← client.pendingOperationCount) == 0)
      "native upload refusal ends the session with no pending operation"
    client.disconnect
    IO.println s!"native endpoint client checks passed: PDU={pdu}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.NativeInteropTests
