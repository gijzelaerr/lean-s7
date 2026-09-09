import LeanS7.Transport
import LeanS7.Advanced
import LeanS7.Value
import LeanS7.Chunking
import LeanS7.Lifecycle

namespace LeanS7

open Std.Net

structure ClientConfig where
  endpoint : Transport.Endpoint
  port : UInt16 := 102
  rack : Nat := 0
  slot : Nat := 2
  localTsap : UInt16 := 0x0100
  remoteTsap : Option UInt16 := none
  destinationReference : UInt16 := 0
  sourceReference : UInt16 := 1
  classOption : UInt8 := 0
  tpduSizeExponent : UInt8 := 0x0a
  connectTimeoutMs : Option Nat := some 5000
  operationTimeoutMs : Option Nat := some 5000
  reconnectRetries : Nat := 0
  maxStaleResponses : Nat := 4

structure Client where
  private connection : IO.Ref (Option Transport.Connection)
  private requestTail : IO.Ref (Task (Option Unit))
  private state : IO.Ref Lifecycle.State
  private config : ClientConfig
  pduLength : UInt16
  private currentPduLength : IO.Ref UInt16
  private nextReference : IO.Ref UInt16

private def orThrow [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError (reprStr error)

private def remoteTsap (rack slot : Nat) : IO UInt16 := do
  if rack > 7 then
    throw <| IO.userError s!"rack must be between 0 and 7, got {rack}"
  if slot > 31 then
    throw <| IO.userError s!"slot must be between 0 and 31, got {slot}"
  return UInt16.ofNat (0x0100 + rack * 32 + slot)

private def connectSession (config : ClientConfig) : IO (Transport.Connection × S7.SetupCommunication) := do
  let calledTsap ← match config.remoteTsap with
    | some tsap => pure tsap
    | none => remoteTsap config.rack config.slot
  let connection ← Transport.connect config.endpoint config.port {
    destinationReference := config.destinationReference
    sourceReference := config.sourceReference
    classOption := config.classOption
    callingTsap := config.localTsap
    calledTsap
    tpduSizeExponent := config.tpduSizeExponent
  } config.connectTimeoutMs
  try
    let reference : UInt16 := 1
    let request ← orThrow <| S7.encodeSetupCommunication reference
    Transport.sendData connection.socket request config.operationTimeoutMs
    let response ← orThrow <| S7.decodeResponse
      (← Transport.receiveData connection.socket config.operationTimeoutMs)
    let setup ← orThrow <| S7.decodeSetupCommunication reference response
    orThrow <| COTP.validateDataPayloadBudget connection.tpduSizeExponent
      setup.pduLength.toNat
    return (connection, setup)
  catch error =>
    try Transport.disconnect connection config.operationTimeoutMs catch _ => pure ()
    throw error

def Client.connect (config : ClientConfig) : IO Client := do
  let (session, setup) ← connectSession config
  let connection ← IO.mkRef (some session)
  let requestTail ← IO.mkRef (Task.pure (some ()))
  let state ← IO.mkRef Lifecycle.State.connected
  let currentPduLength ← IO.mkRef setup.pduLength
  let nextReference ← IO.mkRef 2
  return { connection, requestTail, state, config, pduLength := setup.pduLength, currentPduLength, nextReference }

private def Client.freshReference (client : Client) : IO UInt16 := do
  client.nextReference.modifyGet fun reference => (reference, reference + 1)

def Client.isConnected (client : Client) : IO Bool :=
  return (← client.state.get) == .connected

def Client.negotiatedPduLength (client : Client) : IO UInt16 :=
  client.currentPduLength.get

private def Client.applyLifecycleEvent (client : Client) (event : Lifecycle.Event) : IO Unit := do
  let accepted ← client.state.modifyGet fun current =>
    match Lifecycle.transition current event with
    | some next => (true, next)
    | none => (false, current)
  unless accepted do
    throw <| IO.userError s!"illegal S7 client lifecycle event {repr event}"

private def Client.closeCurrent (client : Client) : IO Unit := do
  let previous ← client.connection.modifyGet fun connection => (connection, none)
  if let some connection := previous then
    try Transport.disconnect connection client.config.operationTimeoutMs catch _ => pure ()
  client.applyLifecycleEvent .transportClosed

private def Client.exchangeBytesCurrent (client : Client) (reference : UInt16)
    (request : ByteArray) : IO ByteArray := do
  let some connection ← client.connection.get
    | throw <| IO.userError "S7 client is disconnected"
  Transport.sendData connection.socket request client.config.operationTimeoutMs
  let pduLength ← client.currentPduLength.get
  let deadline ← Transport.receiveDeadline client.config.operationTimeoutMs
  for _ in [0:client.config.maxStaleResponses + 1] do
    let response ← Transport.receiveDataUntil connection.socket deadline
      pduLength.toNat
    if (← orThrow <| S7.decodePduReference response) == reference then
      return response
  throw <| IO.userError s!"too many stale S7 responses while waiting for reference {reference}"

private def Client.exchangeCurrent (client : Client) (reference : UInt16)
    (request : ByteArray) : IO S7.Response := do
  orThrow <| S7.decodeResponse (← client.exchangeBytesCurrent reference request)

private def Client.reconnect (client : Client) : IO Unit := do
  client.closeCurrent
  let (connection, setup) ← connectSession client.config
  client.connection.set (some connection)
  client.applyLifecycleEvent .reconnected
  client.currentPduLength.set setup.pduLength

private partial def Client.exchangeWithRetries (client : Client) (reference : UInt16)
    (request : ByteArray) (remainingRetries : Nat) (reconnectFirst : Bool := false) : IO S7.Response := do
  try
    if reconnectFirst then
      client.reconnect
    client.exchangeCurrent reference request
  catch error =>
    client.closeCurrent
    if remainingRetries == 0 || (← client.state.get) == .closed then
      throw error
    client.exchangeWithRetries reference request (remainingRetries - 1) true

private partial def Client.exchangeBytesWithRetries (client : Client) (reference : UInt16)
    (request : ByteArray) (remainingRetries : Nat) (reconnectFirst : Bool := false) : IO ByteArray := do
  try
    if reconnectFirst then
      client.reconnect
    client.exchangeBytesCurrent reference request
  catch error =>
    client.closeCurrent
    if remainingRetries == 0 || (← client.state.get) == .closed then
      throw error
    client.exchangeBytesWithRetries reference request (remainingRetries - 1) true

private def Client.serialized (client : Client) (operation : IO α) : IO α := do
  let gate : IO.Promise Unit ← IO.Promise.new
  let previous ← client.requestTail.modifyGet fun previous => (previous, gate.result?)
  let task ← IO.bindTask previous fun _ =>
    IO.asTask do
      try operation
      finally gate.resolve ()
  match ← IO.wait task with
  | .ok value => return value
  | .error error => throw error

private def Client.exchange (client : Client) (reference : UInt16)
    (request : ByteArray) : IO S7.Response :=
  client.serialized <| client.exchangeWithRetries reference request client.config.reconnectRetries

/-- Exchange an already encoded S7 PDU. The caller supplies the PDU reference
    embedded in `request`; the response is returned without service decoding. -/
def Client.rawExchange (client : Client) (reference : UInt16) (request : ByteArray) : IO ByteArray := do
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| IO.userError s!"raw request exceeds negotiated PDU length {pduLength}"
  client.serialized <| client.exchangeBytesWithRetries reference request client.config.reconnectRetries

private def Client.exchangeUserData (client : Client) (reference : UInt16) (group subfunction : UInt8)
    (request : ByteArray) : IO S7.UserDataResponse :=
  client.serialized do
    let response ← client.exchangeBytesWithRetries reference request client.config.reconnectRetries
    orThrow <| S7.decodeUserDataResponse reference group subfunction response

private partial def Client.readSzlFragments (client : Client) (id index : UInt16)
    (fragmentNumber : Nat) (sequence : UInt8) (payload : ByteArray) : IO ByteArray := do
  if fragmentNumber >= 256 then
    throw <| IO.userError "SZL response exceeded the 256-fragment safety limit"
  let reference ← client.freshReference
  let request ← if fragmentNumber == 0 then
    orThrow <| S7.encodeReadSzl reference id index
  else
    orThrow <| S7.encodeReadSzlContinuation reference sequence
  let raw ← client.exchangeBytesWithRetries reference request
    (if fragmentNumber == 0 then client.config.reconnectRetries else 0)
  let response ← orThrow <| S7.decodeUserDataResponse reference S7.szlGroup
    S7.readSzlSubfunction raw
  let nextPayload ← if fragmentNumber == 0 then
    let (actualId, actualIndex, firstPayload) ← orThrow <| S7.decodeSzlFirst response
    if actualId != id || actualIndex != index then
      throw <| IO.userError s!"PLC returned SZL {actualId}/{actualIndex}, expected {id}/{index}"
    pure firstPayload
  else
    pure response.payload
  let accumulated := payload ++ nextPayload
  if accumulated.size > 16 * 1024 * 1024 then
    throw <| IO.userError "SZL response exceeded the 16 MiB safety limit"
  if response.hasMoreData then
    client.readSzlFragments id index (fragmentNumber + 1) response.sequence accumulated
  else
    return accumulated

def Client.readSzl (client : Client) (id : UInt16) (index : UInt16 := 0) : IO S7.Szl :=
  client.serialized do
    orThrow <| S7.decodeSzl id index (← client.readSzlFragments id index 0 0 ByteArray.empty)

def Client.readSzlList (client : Client) : IO (Array UInt16) := do
  let szl ← client.readSzl 0 0
  if szl.recordLength != 2 then
    throw <| IO.userError s!"SZL directory record length must be 2, got {szl.recordLength}"
  let mut cursor : Cursor := { data := szl.data }
  let mut result := #[]
  for _ in [0:szl.recordCount.toNat] do
    let (id, next) ← orThrow cursor.readUInt16BE
    cursor := next
    result := result.push id
  orThrow cursor.finish
  return result

def Client.getOrderCode (client : Client) : IO S7.OrderCode := do
  orThrow <| S7.parseOrderCode (← client.readSzl 0x0011 0)

def Client.getCpuInfo (client : Client) : IO S7.CpuInfo := do
  orThrow <| S7.parseCpuInfo (← client.readSzl 0x001c 0)

def Client.getCpInfo (client : Client) : IO S7.CpInfo := do
  orThrow <| S7.parseCpInfo (← client.readSzl 0x0131 1)

def Client.getProtection (client : Client) : IO S7.Protection := do
  orThrow <| S7.parseProtection (← client.readSzl 0x0232 4)

def Client.getCpuState (client : Client) : IO S7.CpuState := do
  orThrow <| S7.parseCpuState (← client.readSzl 0x0424 0)

def Client.getPlcDateTime (client : Client) : IO S7.PlcDateTime := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeReadClock reference
  let response ← client.exchangeUserData reference S7.clockGroup S7.readClockSubfunction request
  orThrow <| S7.decodePlcDateTime response.payload

def Client.setPlcDateTime (client : Client) (value : S7.PlcDateTime) : IO Unit := do
  let reference ← client.freshReference
  let payload ← orThrow <| S7.encodePlcDateTime value
  let request ← orThrow <| S7.encodeSetClock reference payload
  discard <| client.exchangeUserData reference S7.clockGroup S7.setClockSubfunction request

private def Client.plcControl (client : Client) (function : UInt8)
    (encode : UInt16 → Except S7.EncodeError ByteArray) : IO Unit := do
  let reference ← client.freshReference
  let request ← orThrow <| encode reference
  let response ← client.exchange reference request
  orThrow <| S7.decodePlcControl reference function response

def Client.plcHotStart (client : Client) : IO Unit :=
  client.plcControl S7.startFunction S7.encodePlcHotStart

def Client.plcColdStart (client : Client) : IO Unit :=
  client.plcControl S7.startFunction S7.encodePlcColdStart

def Client.plcStop (client : Client) : IO Unit :=
  client.plcControl S7.stopFunction S7.encodePlcStop

def Client.setSessionPassword (client : Client) (password : String) : IO Unit := do
  let reference ← client.freshReference
  let encoded ← orThrow <| S7.encodePassword password
  let request ← orThrow <| S7.encodeSetPassword reference encoded
  discard <| client.exchangeUserData reference S7.securityGroup S7.enterPasswordSubfunction request

def Client.clearSessionPassword (client : Client) : IO Unit := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeClearPassword reference
  discard <| client.exchangeUserData reference S7.securityGroup S7.clearPasswordSubfunction request

private partial def Client.userDataFragments (client : Client) (group subfunction : UInt8)
    (firstRequest : UInt16 → Except S7.EncodeError ByteArray) (fragmentNumber : Nat)
    (sequence : UInt8) (payload : ByteArray) : IO ByteArray := do
  if fragmentNumber >= 256 then
    throw <| IO.userError "USER_DATA response exceeded the 256-fragment safety limit"
  let reference ← client.freshReference
  let request ← if fragmentNumber == 0 then orThrow <| firstRequest reference
    else orThrow <| S7.encodeUserDataContinuation reference group subfunction sequence
  let raw ← client.exchangeBytesWithRetries reference request
    (if fragmentNumber == 0 then client.config.reconnectRetries else 0)
  let response ← orThrow <| S7.decodeUserDataResponse reference group subfunction raw
  let accumulated := payload ++ response.payload
  if accumulated.size > 16 * 1024 * 1024 then
    throw <| IO.userError "USER_DATA response exceeded the 16 MiB safety limit"
  if response.hasMoreData then
    client.userDataFragments group subfunction firstRequest (fragmentNumber + 1)
      response.sequence accumulated
  else return accumulated

def Client.listBlocks (client : Client) : IO S7.BlockCounts := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeListBlocks reference
  let response ← client.exchangeUserData reference S7.blocksInfoGroup
    S7.listBlocksSubfunction request
  orThrow <| S7.decodeBlockCounts response.payload

def Client.listBlocksOfType (client : Client) (blockType : S7.BlockType) :
    IO (Array S7.BlockEntry) :=
  client.serialized do
    let payload ← client.userDataFragments S7.blocksInfoGroup S7.listBlocksOfTypeSubfunction
      (fun reference => S7.encodeListBlocksOfType reference blockType) 0 0 ByteArray.empty
    orThrow <| S7.decodeBlockEntries payload

def Client.getBlockInfo (client : Client) (blockType : S7.BlockType) (number : Nat) :
    IO S7.BlockInfo := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeGetBlockInfo reference blockType number
  let response ← client.exchangeUserData reference S7.blocksInfoGroup S7.blockInfoSubfunction request
  orThrow <| S7.decodeBlockInfo response.payload

private partial def Client.uploadFragments (client : Client) (uploadId : UInt8)
    (fragmentNumber : Nat) (payload : ByteArray) : IO ByteArray := do
  if fragmentNumber >= 65536 then
    throw <| IO.userError "block upload exceeded the 65536-fragment safety limit"
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeUpload reference uploadId
  let response ← client.exchangeWithRetries reference request 0
  let fragment ← orThrow <| S7.decodeUploadFragment reference response
  let accumulated := payload ++ fragment.data
  if accumulated.size > 64 * 1024 * 1024 then
    throw <| IO.userError "block upload exceeded the 64 MiB safety limit"
  if fragment.isLast then return accumulated
  client.uploadFragments uploadId (fragmentNumber + 1) accumulated

private def Client.uploadBlockData (client : Client) (blockType : S7.BlockType)
    (number : Nat) : IO ByteArray :=
  client.serialized do
    let startReference ← client.freshReference
    let startRequest ← orThrow <| S7.encodeStartUpload startReference blockType number
    let startResponse ← client.exchangeWithRetries startReference startRequest client.config.reconnectRetries
    let upload ← orThrow <| S7.decodeStartUpload startReference startResponse
    let payload ← try client.uploadFragments upload.uploadId 0 ByteArray.empty
      catch error =>
        let endReference ← client.freshReference
        try
          let endRequest ← orThrow <| S7.encodeEndUpload endReference upload.uploadId
          discard <| client.exchangeWithRetries endReference endRequest 0
        catch _ => pure ()
        throw error
    let endReference ← client.freshReference
    let endRequest ← orThrow <| S7.encodeEndUpload endReference upload.uploadId
    let endResponse ← client.exchangeWithRetries endReference endRequest 0
    orThrow <| S7.decodeEndUpload endReference endResponse
    return payload

def Client.fullUpload (client : Client) (blockType : S7.BlockType) (number : Nat) : IO ByteArray :=
  client.uploadBlockData blockType number

def Client.upload (client : Client) (blockType : S7.BlockType) (number : Nat) : IO ByteArray := do
  let full ← client.uploadBlockData blockType number
  if full.size < 36 then
    throw <| IO.userError "full block upload omitted its 36-byte compact header"
  let (mc7Size, _) ← orThrow <| ({ data := full, offset := 34 } : Cursor).readUInt16BE
  if full.size < 36 + mc7Size.toNat then
    throw <| IO.userError s!"block upload contains fewer than {mc7Size} MC7 bytes"
  return full.extract 36 (36 + mc7Size.toNat)

private def Client.controlService (client : Client)
    (encode : UInt16 → Except S7.EncodeError ByteArray) : IO Unit :=
  client.plcControl S7.startFunction encode

def Client.deleteBlock (client : Client) (blockType : S7.BlockType) (number : Nat) : IO Unit :=
  client.controlService fun reference => S7.encodeDeleteBlock reference blockType number

def Client.compress (client : Client) : IO Unit :=
  client.controlService S7.encodeCompress

def Client.copyRamToRom (client : Client) : IO Unit :=
  client.controlService S7.encodeCopyRamToRom

private def Client.receiveServerJob (client : Client) : IO S7.JobPdu := do
  let some connection ← client.connection.get
    | throw <| IO.userError "S7 client is disconnected"
  let pduLength ← client.currentPduLength.get
  orThrow <| S7.decodeJobPdu
    (← Transport.receiveData connection.socket client.config.operationTimeoutMs pduLength.toNat)

private def Client.sendServerResponse (client : Client) (response : ByteArray) : IO Unit := do
  let some connection ← client.connection.get
    | throw <| IO.userError "S7 client is disconnected"
  Transport.sendData connection.socket response client.config.operationTimeoutMs

private partial def Client.serveDownloadFragments (client : Client) (blockData : ByteArray)
    (offset maxSlice fragmentNumber : Nat) : IO Unit := do
  if fragmentNumber >= 65536 then
    throw <| IO.userError "block download exceeded the 65536-fragment safety limit"
  let job ← client.receiveServerJob
  let (function, _) ← orThrow <| ({ data := job.parameters } : Cursor).readUInt8
  if function != S7.downloadFunction then
    throw <| IO.userError s!"expected PLC download request, got function {function}"
  let remaining := blockData.size - offset
  let size := min remaining maxSlice
  let isLast := size == remaining
  let response ← orThrow <| S7.encodeDownloadFragmentResponse job.reference isLast
    (blockData.extract offset (offset + size))
  client.sendServerResponse response
  unless isLast do
    client.serveDownloadFragments blockData (offset + size) maxSlice (fragmentNumber + 1)

/-- Download a complete load-memory block returned by `fullUpload`. Classic S7
    download is PLC-driven: after the initial request the PLC asks for each
    fragment, then the client inserts the transferred block. -/
def Client.downloadBlock (client : Client) (blockType : S7.BlockType) (number : Nat)
    (blockData : ByteArray) : IO Unit :=
  client.serialized do
    try
      if blockData.size < 36 then
        throw <| IO.userError "download data must contain a 36-byte compact block header"
      let (mc7Size, _) ← orThrow <| ({ data := blockData, offset := 34 } : Cursor).readUInt16BE
      if 36 + mc7Size.toNat > blockData.size then
        throw <| IO.userError "compact block header declares more MC7 data than supplied"
      let startReference ← client.freshReference
      let startRequest ← orThrow <| S7.encodeRequestDownload startReference blockType number
        blockData.size mc7Size.toNat
      let startResponse ← client.exchangeWithRetries startReference startRequest
        client.config.reconnectRetries
      orThrow <| S7.validateResponse startResponse startReference S7.requestDownloadFunction
      let pduLength ← client.negotiatedPduLength
      if pduLength.toNat <= 18 then
        throw <| IO.userError "negotiated PDU is too small for block download"
      client.serveDownloadFragments blockData 0 (pduLength.toNat - 18) 0
      let ended ← client.receiveServerJob
      let (endedFunction, _) ← orThrow <| ({ data := ended.parameters } : Cursor).readUInt8
      if endedFunction != S7.downloadEndedFunction then
        throw <| IO.userError s!"expected PLC download-ended request, got function {endedFunction}"
      client.sendServerResponse (← orThrow <| S7.encodeDownloadEndedResponse ended.reference)
      let insertReference ← client.freshReference
      let insertRequest ← orThrow <| S7.encodeInsertBlock insertReference blockType number
      let insertResponse ← client.exchangeWithRetries insertReference insertRequest 0
      orThrow <| S7.decodePlcControl insertReference S7.startFunction insertResponse
    catch error =>
      client.closeCurrent
      throw error

def Client.readForceTable (client : Client) : IO (Array S7.ForceEntry) := do
  orThrow <| S7.decodeForceTable (← client.readSzl 0x0025 0)

private def Client.readAreaChunk (client : Client) (range : S7.MemoryRange) :
    IO { data : ByteArray // data.size = range.count * range.area.elementSize } := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaRead reference range
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {pduLength}"
  let expectedSize := range.count * range.area.elementSize
  if expectedSize + 18 > pduLength.toNat then
    throw <| IO.userError s!"response would exceed negotiated PDU length {pduLength}"
  let response ← client.exchange reference request
  match hdecode : S7.decodeAreaRead reference range.area expectedSize response with
  | .error error => throw <| IO.userError (reprStr error)
  | .ok payload =>
      return ⟨payload, S7.decodeAreaRead_size reference range.area expectedSize response
        payload hdecode⟩

private def Client.writeAreaChunk (client : Client) (range : S7.MemoryRange)
    (payload : ByteArray) : IO Unit := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaWrite reference range payload
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {pduLength}"
  let response ← client.exchange reference request
  orThrow <| S7.decodeDbWrite reference response

private def Client.readAreaChunks (client : Client) (area : S7.Area)
    (dbNumber : UInt16) (start : Nat) (consumed : Nat) (chunks : List Nat)
    (result : Chunking.ReadAssembly area.elementSize consumed) :
    IO (Chunking.ReadAssembly area.elementSize (consumed + chunks.sum)) := do
  match hchunks : chunks with
  | [] => return (by simpa [hchunks] using result)
  | count :: rest =>
      let chunk ← client.readAreaChunk {
        area, dbNumber, start := result.nextStart start, count
      }
      let assembled ← client.readAreaChunks area dbNumber start (consumed + count)
        rest (result.append chunk)
      return (by simpa [hchunks, List.sum_cons, Nat.add_assoc] using assembled)

/-- Internal transfer result retains the byte-count proof through the IO loop. -/
private def Client.readAreaChecked (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start count : Nat) : IO { data : ByteArray // data.size = count * area.elementSize } := do
  if hzero : count = 0 then
    return ⟨ByteArray.empty, by simp [hzero]⟩
  let pduLength ← client.negotiatedPduLength
  let availableBytes := pduLength.toNat - 18
  let maxCount := min S7.maxSectionSize (availableBytes / area.elementSize)
  if hmaximum : maxCount = 0 then
    throw <| IO.userError s!"negotiated PDU length {pduLength} cannot hold a read item"
  else
    let assembled ← client.readAreaChunks area dbNumber start 0
      (Chunking.counts count maxCount) (Chunking.ReadAssembly.empty area.elementSize)
    return ⟨assembled.data, Chunking.ReadAssembly.complete_size count maxCount
      area.elementSize hmaximum assembled⟩

def Client.readArea (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start count : Nat) : IO ByteArray := do
  return (← client.readAreaChecked area dbNumber start count).val

private def Client.writeAreaChunks (client : Client) (area : S7.Area)
    (dbNumber : UInt16) (start offset : Nat) (payload : ByteArray)
    (chunks : List Nat) (hcoverage : offset + chunks.sum * area.elementSize = payload.size) :
    IO Unit := do
  match hchunks : chunks with
  | [] => pure ()
  | count :: rest =>
      let byteCount := count * area.elementSize
      have htail : offset + byteCount + rest.sum * area.elementSize = payload.size := by
        simpa [hchunks, byteCount, Nat.add_mul, Nat.add_assoc] using hcoverage
      let chunk := Chunking.writeSlice payload offset count area.elementSize (by omega)
      client.writeAreaChunk { area, dbNumber, start := start + offset, count } chunk.val
      client.writeAreaChunks area dbNumber start (offset + byteCount)
        payload rest htail

def Client.writeArea (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start : Nat) (payload : ByteArray) : IO Unit := do
  if payload.isEmpty then
    return
  if haligned : payload.size % area.elementSize ≠ 0 then
    throw <| IO.userError s!"payload size {payload.size} is not aligned to {area.elementSize}-byte elements"
  else
    have hsize : payload.size / area.elementSize * area.elementSize = payload.size := by
      have hmod : payload.size % area.elementSize = 0 := by omega
      have := Nat.div_add_mod payload.size area.elementSize
      simpa [hmod, Nat.mul_comm] using this
    let pduLength ← client.negotiatedPduLength
    let availableBytes := pduLength.toNat - 28
    let lengthLimitedBytes := if area.dataTransportSize == S7.octetTransportSize then
      S7.maxSectionSize
    else
      S7.maxSectionSize / 8
    let maxCount := min S7.maxSectionSize
      (min availableBytes lengthLimitedBytes / area.elementSize)
    if hmaximum : maxCount = 0 then
      throw <| IO.userError s!"negotiated PDU length {pduLength} cannot hold a write item"
    else
      client.writeAreaChunks area dbNumber start 0 payload
        (Chunking.counts (payload.size / area.elementSize) maxCount) (by
          simpa [Chunking.counts_sum _ _ hmaximum] using hsize)

def Client.dbRead (client : Client) (dbNumber : UInt16) (start size : Nat) : IO ByteArray :=
  client.readArea .dataBlocks dbNumber start size

def Client.dbWrite (client : Client) (dbNumber : UInt16) (start : Nat) (payload : ByteArray) : IO Unit :=
  client.writeArea .dataBlocks dbNumber start payload

def Client.inputsRead (client : Client) (start size : Nat) : IO ByteArray :=
  client.readArea .processInputs 0 start size

def Client.inputsWrite (client : Client) (start : Nat) (payload : ByteArray) : IO Unit :=
  client.writeArea .processInputs 0 start payload

def Client.outputsRead (client : Client) (start size : Nat) : IO ByteArray :=
  client.readArea .processOutputs 0 start size

def Client.outputsWrite (client : Client) (start : Nat) (payload : ByteArray) : IO Unit :=
  client.writeArea .processOutputs 0 start payload

def Client.markersRead (client : Client) (start size : Nat) : IO ByteArray :=
  client.readArea .markers 0 start size

def Client.markersWrite (client : Client) (start : Nat) (payload : ByteArray) : IO Unit :=
  client.writeArea .markers 0 start payload

def Client.countersRead (client : Client) (start count : Nat) : IO ByteArray :=
  client.readArea .counters 0 start count

def Client.countersWrite (client : Client) (start : Nat) (payload : ByteArray) : IO Unit :=
  client.writeArea .counters 0 start payload

def Client.timersRead (client : Client) (start count : Nat) : IO ByteArray :=
  client.readArea .timers 0 start count

def Client.timersWrite (client : Client) (start : Nat) (payload : ByteArray) : IO Unit :=
  client.writeArea .timers 0 start payload

def readResponseContribution (range : S7.MemoryRange) : Nat :=
  let size := range.count * range.area.elementSize
  4 + size + size % 2

def takeReadBatch (pduLength : Nat) : List S7.MemoryRange →
    Nat → Nat → Nat → List S7.MemoryRange → List S7.MemoryRange × List S7.MemoryRange
  | [], _, _, _, selected => (selected.reverse, [])
  | pending@(range :: rest), count, requestSize, responseSize, selected =>
      let nextRequestSize := requestSize + 12
      let nextResponseSize := responseSize + readResponseContribution range
      if range.count > 0 && count < S7.maxItemCount &&
          nextRequestSize ≤ pduLength && nextResponseSize ≤ pduLength then
        takeReadBatch pduLength rest (count + 1) nextRequestSize nextResponseSize (range :: selected)
      else
        (selected.reverse, pending)

/-- Read batching returns an order-preserving prefix and suffix partition: no
    requested range is lost, duplicated, or reordered. -/
theorem takeReadBatch_preserves_order (pduLength : Nat)
    (pending : List S7.MemoryRange) (count requestSize responseSize : Nat)
    (selected : List S7.MemoryRange) :
    let result := takeReadBatch pduLength pending count requestSize responseSize selected
    result.1 ++ result.2 = selected.reverse ++ pending := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simp [takeReadBatch]
  | cons range rest ih =>
      simp only [takeReadBatch]
      split
      · simpa [List.reverse_cons, List.append_assoc] using
          ih (count + 1) (requestSize + 12)
            (responseSize + readResponseContribution range) (range :: selected)
      · simp

/-- A read batch never exceeds the classic S7 item-count limit. -/
theorem takeReadBatch_count_le (pduLength : Nat)
    (pending : List S7.MemoryRange) (count requestSize responseSize : Nat)
    (selected : List S7.MemoryRange) (hselected : selected.length = count)
    (hcount : count ≤ S7.maxItemCount) :
    let result := takeReadBatch pduLength pending count requestSize responseSize selected
    result.1.length ≤ S7.maxItemCount := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeReadBatch, hselected] using hcount
  | cons range rest ih =>
      simp only [takeReadBatch]
      split
      case isTrue hcondition =>
        have hproperties := hcondition
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hproperties
        apply ih (count + 1) (requestSize + 12)
          (responseSize + readResponseContribution range) (range :: selected)
        · simp [hselected]
        · exact Nat.add_one_le_iff.mpr hproperties.1.1.2
      case isFalse =>
        simpa [hselected] using hcount

/-- The request size represented by a selected read batch stays within the
    negotiated PDU budget. -/
theorem takeReadBatch_request_size_le (pduLength base : Nat)
    (pending : List S7.MemoryRange) (count requestSize responseSize : Nat)
    (selected : List S7.MemoryRange) (hselected : selected.length = count)
    (hrequest : requestSize = base + 12 * count)
    (hrequestLe : requestSize ≤ pduLength) :
    let result := takeReadBatch pduLength pending count requestSize responseSize selected
    base + 12 * result.1.length ≤ pduLength := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeReadBatch, hselected, hrequest] using hrequestLe
  | cons range rest ih =>
      simp only [takeReadBatch]
      split
      case isTrue hcondition =>
        have hproperties := hcondition
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hproperties
        apply ih (count + 1) (requestSize + 12)
          (responseSize + readResponseContribution range) (range :: selected)
        · simp [hselected]
        · rw [hrequest]
          omega
        · exact hproperties.1.2
      case isFalse =>
        simpa [hselected, hrequest] using hrequestLe

def readResponseContributions (ranges : List S7.MemoryRange) : Nat :=
  (ranges.map readResponseContribution).sum

@[simp] theorem readResponseContributions_reverse (ranges : List S7.MemoryRange) :
    readResponseContributions ranges.reverse = readResponseContributions ranges := by
  simp [readResponseContributions, List.map_reverse, List.sum_reverse]

/-- The response size represented by a selected read batch stays within the
    negotiated PDU budget. -/
theorem takeReadBatch_response_size_le (pduLength base : Nat)
    (pending : List S7.MemoryRange) (count requestSize responseSize : Nat)
    (selected : List S7.MemoryRange)
    (hresponse : responseSize = base + readResponseContributions selected)
    (hresponseLe : responseSize ≤ pduLength) :
    let result := takeReadBatch pduLength pending count requestSize responseSize selected
    base + readResponseContributions result.1 ≤ pduLength := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeReadBatch, hresponse] using hresponseLe
  | cons range rest ih =>
      simp only [takeReadBatch]
      split
      case isTrue hcondition =>
        have hproperties := hcondition
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hproperties
        apply ih (count + 1) (requestSize + 12)
          (responseSize + readResponseContribution range) (range :: selected)
        · simp [readResponseContributions, hresponse]
          omega
        · exact hproperties.2
      case isFalse =>
        simpa [hresponse] using hresponseLe

/-- The read batch selected by the client fits both negotiated request and
    response budgets. -/
theorem takeReadBatch_fits (pduLength : Nat) (pending : List S7.MemoryRange)
    (hrequest : 12 ≤ pduLength) (hresponse : 14 ≤ pduLength) :
    let result := takeReadBatch pduLength pending 0 12 14 []
    12 + 12 * result.1.length ≤ pduLength ∧
      14 + readResponseContributions result.1 ≤ pduLength := by
  constructor
  · exact takeReadBatch_request_size_le pduLength 12 pending 0 12 14 []
      (by simp) (by simp) hrequest
  · exact takeReadBatch_response_size_le pduLength 14 pending 0 12 14 []
      (by simp [readResponseContributions]) hresponse

private def Client.readMultiBatch (client : Client) (ranges : Array S7.MemoryRange) : IO (Array S7.ReadItemResult) := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaReadMany reference ranges
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| IO.userError s!"multi-read request exceeds negotiated PDU length {pduLength}"
  let response ← client.exchange reference request
  orThrow <| S7.decodeAreaReadMany reference ranges response

private partial def Client.readMultiLoop (client : Client) (pending : List S7.MemoryRange)
    (results : Array S7.ReadItemResult) : IO (Array S7.ReadItemResult) := do
  match pending with
  | [] => return results
  | range :: rest =>
      let pduLength ← client.negotiatedPduLength
      let (batch, remaining) := takeReadBatch pduLength.toNat pending 0 12 14 []
      if batch.isEmpty then
        let payload ← client.readArea range.area range.dbNumber range.start range.count
        client.readMultiLoop rest (results.push (.success payload))
      else
        let batchResults ← client.readMultiBatch batch.toArray
        client.readMultiLoop remaining (results ++ batchResults)

def Client.readMulti (client : Client) (ranges : Array S7.MemoryRange) : IO (Array S7.ReadItemResult) :=
  client.readMultiLoop ranges.toList #[]

def writeRequestContribution (item : S7.WriteItem) : Nat :=
  12 + 4 + item.payload.size + item.payload.size % 2

def takeWriteBatch (pduLength : Nat) : List S7.WriteItem →
    Nat → Nat → Nat → List S7.WriteItem → List S7.WriteItem × List S7.WriteItem
  | [], _, _, _, selected => (selected.reverse, [])
  | pending@(item :: rest), count, requestSize, responseSize, selected =>
      let nextRequestSize := requestSize + writeRequestContribution item
      let nextResponseSize := responseSize + 1
      let expectedSize := item.range.count * item.range.area.elementSize
      if item.range.count > 0 && item.payload.size == expectedSize &&
          count < S7.maxItemCount && nextRequestSize ≤ pduLength && nextResponseSize ≤ pduLength then
        takeWriteBatch pduLength rest (count + 1) nextRequestSize nextResponseSize (item :: selected)
      else
        (selected.reverse, pending)

/-- Write batching returns an order-preserving prefix and suffix partition: no
    requested item is lost, duplicated, or reordered. -/
theorem takeWriteBatch_preserves_order (pduLength : Nat)
    (pending : List S7.WriteItem) (count requestSize responseSize : Nat)
    (selected : List S7.WriteItem) :
    let result := takeWriteBatch pduLength pending count requestSize responseSize selected
    result.1 ++ result.2 = selected.reverse ++ pending := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simp [takeWriteBatch]
  | cons item rest ih =>
      simp only [takeWriteBatch]
      split
      · simpa [List.reverse_cons, List.append_assoc] using
          ih (count + 1) (requestSize + writeRequestContribution item)
            (responseSize + 1) (item :: selected)
      · simp

/-- A write batch never exceeds the classic S7 item-count limit. -/
theorem takeWriteBatch_count_le (pduLength : Nat)
    (pending : List S7.WriteItem) (count requestSize responseSize : Nat)
    (selected : List S7.WriteItem) (hselected : selected.length = count)
    (hcount : count ≤ S7.maxItemCount) :
    let result := takeWriteBatch pduLength pending count requestSize responseSize selected
    result.1.length ≤ S7.maxItemCount := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeWriteBatch, hselected] using hcount
  | cons item rest ih =>
      simp only [takeWriteBatch]
      split
      case isTrue hcondition =>
        have hproperties := hcondition
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hproperties
        apply ih (count + 1) (requestSize + writeRequestContribution item)
          (responseSize + 1) (item :: selected)
        · simp [hselected]
        · exact Nat.add_one_le_iff.mpr hproperties.1.1.2
      case isFalse =>
        simpa [hselected] using hcount

def writeRequestContributions (items : List S7.WriteItem) : Nat :=
  (items.map writeRequestContribution).sum

@[simp] theorem writeRequestContributions_reverse (items : List S7.WriteItem) :
    writeRequestContributions items.reverse = writeRequestContributions items := by
  simp [writeRequestContributions, List.map_reverse, List.sum_reverse]

/-- The request size represented by a selected write batch stays within the
    negotiated PDU budget. -/
theorem takeWriteBatch_request_size_le (pduLength base : Nat)
    (pending : List S7.WriteItem) (count requestSize responseSize : Nat)
    (selected : List S7.WriteItem)
    (hrequest : requestSize = base + writeRequestContributions selected)
    (hrequestLe : requestSize ≤ pduLength) :
    let result := takeWriteBatch pduLength pending count requestSize responseSize selected
    base + writeRequestContributions result.1 ≤ pduLength := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeWriteBatch, hrequest] using hrequestLe
  | cons item rest ih =>
      simp only [takeWriteBatch]
      split
      case isTrue hcondition =>
        have hproperties := hcondition
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hproperties
        apply ih (count + 1) (requestSize + writeRequestContribution item)
          (responseSize + 1) (item :: selected)
        · simp [writeRequestContributions, hrequest]
          omega
        · exact hproperties.1.2
      case isFalse =>
        simpa [hrequest] using hrequestLe

/-- The response size represented by a selected write batch stays within the
    negotiated PDU budget. -/
theorem takeWriteBatch_response_size_le (pduLength base : Nat)
    (pending : List S7.WriteItem) (count requestSize responseSize : Nat)
    (selected : List S7.WriteItem) (hselected : selected.length = count)
    (hresponse : responseSize = base + count)
    (hresponseLe : responseSize ≤ pduLength) :
    let result := takeWriteBatch pduLength pending count requestSize responseSize selected
    base + result.1.length ≤ pduLength := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeWriteBatch, hselected, hresponse] using hresponseLe
  | cons item rest ih =>
      simp only [takeWriteBatch]
      split
      case isTrue hcondition =>
        have hproperties := hcondition
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hproperties
        apply ih (count + 1) (requestSize + writeRequestContribution item)
          (responseSize + 1) (item :: selected)
        · simp [hselected]
        · rw [hresponse]
          omega
        · exact hproperties.2
      case isFalse =>
        simpa [hselected, hresponse] using hresponseLe

/-- The write batch selected by the client fits both negotiated request and
    response budgets. -/
theorem takeWriteBatch_fits (pduLength : Nat) (pending : List S7.WriteItem)
    (hrequest : 12 ≤ pduLength) (hresponse : 14 ≤ pduLength) :
    let result := takeWriteBatch pduLength pending 0 12 14 []
    12 + writeRequestContributions result.1 ≤ pduLength ∧
      14 + result.1.length ≤ pduLength := by
  constructor
  · exact takeWriteBatch_request_size_le pduLength 12 pending 0 12 14 []
      (by simp [writeRequestContributions]) hrequest
  · exact takeWriteBatch_response_size_le pduLength 14 pending 0 12 14 []
      (by simp) (by simp) hresponse

private def Client.writeMultiBatch (client : Client) (items : Array S7.WriteItem) : IO (Array S7.WriteItemResult) := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaWriteMany reference items
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| IO.userError s!"multi-write request exceeds negotiated PDU length {pduLength}"
  let response ← client.exchange reference request
  orThrow <| S7.decodeAreaWriteMany reference items.size response

private partial def Client.writeMultiLoop (client : Client) (pending : List S7.WriteItem)
    (results : Array S7.WriteItemResult) : IO (Array S7.WriteItemResult) := do
  match pending with
  | [] => return results
  | item :: rest =>
      let expectedSize := item.range.count * item.range.area.elementSize
      if item.payload.size != expectedSize then
        throw <| IO.userError s!"multi-write payload size {item.payload.size} does not match expected {expectedSize}"
      let pduLength ← client.negotiatedPduLength
      let (batch, remaining) := takeWriteBatch pduLength.toNat pending 0 12 14 []
      if batch.isEmpty then
        client.writeArea item.range.area item.range.dbNumber item.range.start item.payload
        client.writeMultiLoop rest (results.push .success)
      else
        let batchResults ← client.writeMultiBatch batch.toArray
        client.writeMultiLoop remaining (results ++ batchResults)

def Client.writeMulti (client : Client) (items : Array S7.WriteItem) : IO (Array S7.WriteItemResult) :=
  client.writeMultiLoop items.toList #[]

def Client.dbReadUInt8 (client : Client) (dbNumber : UInt16) (start : Nat) : IO UInt8 := do
  orThrow <| Value.getUInt8 (← client.dbRead dbNumber start 1)

def Client.dbReadUInt16 (client : Client) (dbNumber : UInt16) (start : Nat) : IO UInt16 := do
  orThrow <| Value.getUInt16 (← client.dbRead dbNumber start 2)

def Client.dbReadUInt32 (client : Client) (dbNumber : UInt16) (start : Nat) : IO UInt32 := do
  orThrow <| Value.getUInt32 (← client.dbRead dbNumber start 4)

def Client.dbReadUInt64 (client : Client) (dbNumber : UInt16) (start : Nat) : IO UInt64 := do
  orThrow <| Value.getUInt64 (← client.dbRead dbNumber start 8)

def Client.dbReadInt8 (client : Client) (dbNumber : UInt16) (start : Nat) : IO Int8 := do
  orThrow <| Value.getInt8 (← client.dbRead dbNumber start 1)

def Client.dbReadInt16 (client : Client) (dbNumber : UInt16) (start : Nat) : IO Int16 := do
  orThrow <| Value.getInt16 (← client.dbRead dbNumber start 2)

def Client.dbReadInt32 (client : Client) (dbNumber : UInt16) (start : Nat) : IO Int32 := do
  orThrow <| Value.getInt32 (← client.dbRead dbNumber start 4)

def Client.dbReadInt64 (client : Client) (dbNumber : UInt16) (start : Nat) : IO Int64 := do
  orThrow <| Value.getInt64 (← client.dbRead dbNumber start 8)

def Client.dbReadReal (client : Client) (dbNumber : UInt16) (start : Nat) : IO Float32 := do
  orThrow <| Value.getReal (← client.dbRead dbNumber start 4)

def Client.dbReadLReal (client : Client) (dbNumber : UInt16) (start : Nat) : IO Float := do
  orThrow <| Value.getLReal (← client.dbRead dbNumber start 8)

def Client.dbReadBit (client : Client) (dbNumber : UInt16) (byteOffset bitIndex : Nat) : IO Bool := do
  orThrow <| Value.getBit (← client.dbRead dbNumber byteOffset 1) 0 bitIndex

def Client.dbWriteUInt8 (client : Client) (dbNumber : UInt16) (start : Nat) (value : UInt8) : IO Unit :=
  client.dbWrite dbNumber start (Value.putUInt8 value)

def Client.dbWriteUInt16 (client : Client) (dbNumber : UInt16) (start : Nat) (value : UInt16) : IO Unit :=
  client.dbWrite dbNumber start (Value.putUInt16 value)

def Client.dbWriteUInt32 (client : Client) (dbNumber : UInt16) (start : Nat) (value : UInt32) : IO Unit :=
  client.dbWrite dbNumber start (Value.putUInt32 value)

def Client.dbWriteUInt64 (client : Client) (dbNumber : UInt16) (start : Nat) (value : UInt64) : IO Unit :=
  client.dbWrite dbNumber start (Value.putUInt64 value)

def Client.dbWriteInt8 (client : Client) (dbNumber : UInt16) (start : Nat) (value : Int8) : IO Unit :=
  client.dbWrite dbNumber start (Value.putInt8 value)

def Client.dbWriteInt16 (client : Client) (dbNumber : UInt16) (start : Nat) (value : Int16) : IO Unit :=
  client.dbWrite dbNumber start (Value.putInt16 value)

def Client.dbWriteInt32 (client : Client) (dbNumber : UInt16) (start : Nat) (value : Int32) : IO Unit :=
  client.dbWrite dbNumber start (Value.putInt32 value)

def Client.dbWriteInt64 (client : Client) (dbNumber : UInt16) (start : Nat) (value : Int64) : IO Unit :=
  client.dbWrite dbNumber start (Value.putInt64 value)

def Client.dbWriteReal (client : Client) (dbNumber : UInt16) (start : Nat) (value : Float32) : IO Unit :=
  client.dbWrite dbNumber start (Value.putReal value)

def Client.dbWriteLReal (client : Client) (dbNumber : UInt16) (start : Nat) (value : Float) : IO Unit :=
  client.dbWrite dbNumber start (Value.putLReal value)

def Client.dbWriteBit (client : Client) (dbNumber : UInt16) (byteOffset bitIndex : Nat)
    (enabled : Bool) : IO Unit := do
  let current ← client.dbReadUInt8 dbNumber byteOffset
  let updated ← orThrow <| Value.setBit current bitIndex enabled
  client.dbWriteUInt8 dbNumber byteOffset updated

def Client.dbReadString (client : Client) (dbNumber : UInt16) (start : Nat) : IO String := do
  let header ← client.dbRead dbNumber start 2
  let maximum ← orThrow <| Value.getUInt8 header
  if maximum.toNat > Value.maxStringLength then
    throw <| IO.userError s!"invalid S7 STRING maximum length {maximum}"
  orThrow <| Value.decodeString (← client.dbRead dbNumber start (maximum.toNat + 2))

def Client.dbWriteString (client : Client) (dbNumber : UInt16) (start maximum : Nat)
    (value : String) : IO Unit := do
  client.dbWrite dbNumber start (← orThrow <| Value.encodeString maximum value)

def Client.dbReadWString (client : Client) (dbNumber : UInt16) (start : Nat) : IO String := do
  let header ← client.dbRead dbNumber start 4
  let maximum ← orThrow <| Value.getUInt16 header
  if maximum.toNat > Value.maxWStringLength then
    throw <| IO.userError s!"invalid S7 WSTRING maximum length {maximum}"
  orThrow <| Value.decodeWString (← client.dbRead dbNumber start (maximum.toNat * 2 + 4))

def Client.dbWriteWString (client : Client) (dbNumber : UInt16) (start maximum : Nat)
    (value : String) : IO Unit := do
  client.dbWrite dbNumber start (← orThrow <| Value.encodeWString maximum value)

/-- Write an input/output process-image bit. This is not a persistent CPU force
    table operation; a PLC scan may overwrite it. -/
def Client.forceBit (client : Client) (area : S7.Area) (byteOffset bit : Nat)
    (value : Bool) : IO Unit := do
  if area != .processInputs && area != .processOutputs then
    throw <| IO.userError "process-image bit override only supports input and output areas"
  let current ← client.readArea area 0 byteOffset 1
  let updated ← orThrow <| Value.setBit current[0]! bit value
  client.writeArea area 0 byteOffset (bytes #[updated])

def Client.cancelForceBit (client : Client) (area : S7.Area) (byteOffset bit : Nat) : IO Unit :=
  client.forceBit area byteOffset bit false

def Client.disconnect (client : Client) : IO Unit :=
  client.serialized do
    client.closeCurrent
    client.applyLifecycleEvent .disconnect

end LeanS7
