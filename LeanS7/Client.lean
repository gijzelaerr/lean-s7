import LeanS7.Transport
import LeanS7.ClientError
import LeanS7.Advanced
import LeanS7.Value
import LeanS7.Chunking
import LeanS7.MultiValidation
import LeanS7.Download
import LeanS7.Upload
import LeanS7.UserDataAssembly
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
  /-- Whole chunked read/write, multi-item, download, upload, SZL, and segmented
      USER_DATA receive budget, starting after
      the request enters the serialization gate. Does not cancel sends/connects. -/
  transferReceiveTimeoutMs : Option Nat := some 30000
  reconnectRetries : Nat := 0
  maxStaleResponses : Nat := 4
  /-- First post-handshake PDU reference. Primarily useful for deterministic
      wraparound and peer-correlation testing. -/
  initialRequestReference : UInt16 := 2

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
  | .error error => throw <| ClientError.protocol (reprStr error)

private def inputOrThrow [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| ClientError.invalidInput (reprStr error)

private def decodeOrThrow (result : Except DecodeError α) : IO α :=
  match result with
  | .ok value => pure value
  | .error (.remoteFailure _ message) => throw <| ClientError.plcRejected message
  | .error error => throw <| ClientError.protocol (reprStr error)

private def remoteTsap (rack slot : Nat) : IO UInt16 := do
  if rack > 7 then
    throw <| ClientError.invalidInput s!"rack must be between 0 and 7, got {rack}"
  if slot > 31 then
    throw <| ClientError.invalidInput s!"slot must be between 0 and 31, got {slot}"
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
    let request ← inputOrThrow <| S7.encodeSetupCommunication reference
    Transport.sendData connection.socket request config.operationTimeoutMs
    let response ← orThrow <| S7.decodeResponse
      (← Transport.receiveData connection.socket config.operationTimeoutMs)
    let setup ← decodeOrThrow <| S7.decodeSetupCommunication reference response
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
  let nextReference ← IO.mkRef config.initialRequestReference
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
    throw <| ClientError.lifecycle s!"illegal S7 client lifecycle event {repr event}"

private def Client.closeCurrent (client : Client) : IO Unit := do
  let previous ← client.connection.modifyGet fun connection => (connection, none)
  if let some connection := previous then
    try Transport.disconnect connection client.config.operationTimeoutMs catch _ => pure ()
  client.applyLifecycleEvent .transportClosed

private def Client.exchangeBytesCurrent (client : Client) (reference : UInt16)
    (request : ByteArray) (transferDeadline : Option Nat := none) : IO ByteArray := do
  Transport.checkReceiveDeadline transferDeadline
  let some connection ← client.connection.get
    | throw <| ClientError.disconnected "S7 client is disconnected"
  Transport.sendData connection.socket request client.config.operationTimeoutMs
  let pduLength ← client.currentPduLength.get
  let deadline := Transport.earlierReceiveDeadline
    (← Transport.receiveDeadline client.config.operationTimeoutMs) transferDeadline
  for _ in [0:client.config.maxStaleResponses + 1] do
    let response ← Transport.receiveDataUntil connection.socket deadline
      pduLength.toNat
    if (← orThrow <| S7.decodePduReference response) == reference then
      return response
  throw <| ClientError.protocol s!"too many stale S7 responses while waiting for reference {reference}"

private def Client.exchangeCurrent (client : Client) (reference : UInt16)
    (request : ByteArray) (transferDeadline : Option Nat := none) : IO S7.Response := do
  orThrow <| S7.decodeResponse (← client.exchangeBytesCurrent reference request transferDeadline)

private def Client.reconnect (client : Client) : IO Unit := do
  client.closeCurrent
  let previousPduLength ← client.currentPduLength.get
  let (connection, setup) ← connectSession client.config
  if setup.pduLength < previousPduLength then
    try Transport.disconnect connection client.config.operationTimeoutMs catch _ => pure ()
    throw <| ClientError.protocol
      s!"reconnected PDU length shrank from {previousPduLength} to {setup.pduLength}"
  client.connection.set (some connection)
  client.applyLifecycleEvent .reconnected
  client.currentPduLength.set setup.pduLength

private partial def Client.exchangeWithRetries (client : Client) (reference : UInt16)
    (request : ByteArray) (remainingRetries : Nat) (reconnectFirst : Bool := false)
    (transferDeadline : Option Nat := none) : IO S7.Response := do
  try
    Transport.checkReceiveDeadline transferDeadline
    if reconnectFirst then
      client.reconnect
    client.exchangeCurrent reference request transferDeadline
  catch error =>
    client.closeCurrent
    if remainingRetries == 0 || (← client.state.get) == .closed ||
        !isRetryableClientError error then
      throw error
    client.exchangeWithRetries reference request (remainingRetries - 1) true transferDeadline

private partial def Client.exchangeBytesWithRetries (client : Client) (reference : UInt16)
    (request : ByteArray) (remainingRetries : Nat) (reconnectFirst : Bool := false)
    (transferDeadline : Option Nat := none) : IO ByteArray := do
  try
    Transport.checkReceiveDeadline transferDeadline
    if reconnectFirst then
      client.reconnect
    client.exchangeBytesCurrent reference request transferDeadline
  catch error =>
    client.closeCurrent
    if remainingRetries == 0 || (← client.state.get) == .closed ||
        !isRetryableClientError error then
      throw error
    client.exchangeBytesWithRetries reference request (remainingRetries - 1) true transferDeadline

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
    throw <| ClientError.invalidInput s!"raw request exceeds negotiated PDU length {pduLength}"
  let embeddedReference ← inputOrThrow <| S7.decodePduReference request
  if embeddedReference != reference then
    throw <| ClientError.invalidInput
      s!"raw request embeds PDU reference {embeddedReference}, caller supplied {reference}"
  client.serialized <| client.exchangeBytesWithRetries reference request client.config.reconnectRetries

private def Client.exchangeUserData (client : Client) (reference : UInt16) (group subfunction : UInt8)
    (request : ByteArray) : IO S7.UserDataResponse :=
  client.serialized do
    let response ← client.exchangeBytesWithRetries reference request client.config.reconnectRetries
    decodeOrThrow <| S7.decodeUserDataResponse reference group subfunction response

private partial def Client.readSzlFragments (client : Client) (id index : UInt16)
    (state : UserDataAssembly.State (16 * 1024 * 1024) 256) (sequence : UInt8)
    (deadline : Option Nat) : IO ByteArray := do
  let reference ← client.freshReference
  let request ← if state.count == 0 then
    inputOrThrow <| S7.encodeReadSzl reference id index
  else
    inputOrThrow <| S7.encodeReadSzlContinuation reference sequence
  let raw ← client.exchangeBytesWithRetries reference request
    (if state.count == 0 then client.config.reconnectRetries else 0) false deadline
  let response ← decodeOrThrow <| S7.decodeUserDataResponse reference S7.szlGroup
    S7.readSzlSubfunction raw
  let nextPayload ← if state.count == 0 then
    let (actualId, actualIndex, firstPayload) ← orThrow <| S7.decodeSzlFirst response
    if actualId != id || actualIndex != index then
      throw <| ClientError.protocol s!"PLC returned SZL {actualId}/{actualIndex}, expected {id}/{index}"
    pure firstPayload
  else
    pure response.payload
  let step ← orThrow <| UserDataAssembly.accept state nextPayload response.hasMoreData
  if response.hasMoreData then
    client.readSzlFragments id index step.after response.sequence deadline
  else
    return step.after.data

def Client.readSzl (client : Client) (id : UInt16) (index : UInt16 := 0) : IO S7.Szl :=
  client.serialized do
    let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
    try
      orThrow <| S7.decodeSzl id index
        (← client.readSzlFragments id index (UserDataAssembly.empty _ _) 0 deadline)
    catch error =>
      client.closeCurrent
      throw error

def Client.readSzlList (client : Client) : IO (Array UInt16) := do
  let szl ← client.readSzl 0 0
  if szl.recordLength != 2 then
    throw <| ClientError.protocol s!"SZL directory record length must be 2, got {szl.recordLength}"
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
  let request ← inputOrThrow <| S7.encodeReadClock reference
  let response ← client.exchangeUserData reference S7.clockGroup S7.readClockSubfunction request
  orThrow <| S7.decodePlcDateTime response.payload

def Client.setPlcDateTime (client : Client) (value : S7.PlcDateTime) : IO Unit := do
  let reference ← client.freshReference
  let payload ← inputOrThrow <| S7.encodePlcDateTime value
  let request ← inputOrThrow <| S7.encodeSetClock reference payload
  discard <| client.exchangeUserData reference S7.clockGroup S7.setClockSubfunction request

private def Client.plcControl (client : Client) (function : UInt8)
    (encode : UInt16 → Except S7.EncodeError ByteArray) : IO Unit := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| encode reference
  let response ← client.exchange reference request
  decodeOrThrow <| S7.decodePlcControl reference function response

def Client.plcHotStart (client : Client) : IO Unit :=
  client.plcControl S7.startFunction S7.encodePlcHotStart

def Client.plcColdStart (client : Client) : IO Unit :=
  client.plcControl S7.startFunction S7.encodePlcColdStart

def Client.plcStop (client : Client) : IO Unit :=
  client.plcControl S7.stopFunction S7.encodePlcStop

def Client.setSessionPassword (client : Client) (password : String) : IO Unit := do
  let reference ← client.freshReference
  let encoded ← inputOrThrow <| S7.encodePassword password
  let request ← inputOrThrow <| S7.encodeSetPassword reference encoded
  discard <| client.exchangeUserData reference S7.securityGroup S7.enterPasswordSubfunction request

def Client.clearSessionPassword (client : Client) : IO Unit := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeClearPassword reference
  discard <| client.exchangeUserData reference S7.securityGroup S7.clearPasswordSubfunction request

private partial def Client.userDataFragments (client : Client) (group subfunction : UInt8)
    (firstRequest : UInt16 → Except S7.EncodeError ByteArray)
    (state : UserDataAssembly.State (16 * 1024 * 1024) 256)
    (sequence : UInt8) (deadline : Option Nat) : IO ByteArray := do
  let reference ← client.freshReference
  let request ← if state.count == 0 then inputOrThrow <| firstRequest reference
    else inputOrThrow <| S7.encodeUserDataContinuation reference group subfunction sequence
  let raw ← client.exchangeBytesWithRetries reference request
    (if state.count == 0 then client.config.reconnectRetries else 0) false deadline
  let response ← decodeOrThrow <| S7.decodeUserDataResponse reference group subfunction raw
  let step ← orThrow <| UserDataAssembly.accept state response.payload response.hasMoreData
  if response.hasMoreData then
    client.userDataFragments group subfunction firstRequest step.after response.sequence deadline
  else return step.after.data

def Client.listBlocks (client : Client) : IO S7.BlockCounts := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeListBlocks reference
  let response ← client.exchangeUserData reference S7.blocksInfoGroup
    S7.listBlocksSubfunction request
  orThrow <| S7.decodeBlockCounts response.payload

def Client.listBlocksOfType (client : Client) (blockType : S7.BlockType) :
    IO (Array S7.BlockEntry) :=
  client.serialized do
    let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
    try
      let payload ← client.userDataFragments S7.blocksInfoGroup S7.listBlocksOfTypeSubfunction
        (fun reference => S7.encodeListBlocksOfType reference blockType)
        (UserDataAssembly.empty _ _) 0 deadline
      orThrow <| S7.decodeBlockEntries payload
    catch error =>
      client.closeCurrent
      throw error

def Client.getBlockInfo (client : Client) (blockType : S7.BlockType) (number : Nat) :
    IO S7.BlockInfo := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeGetBlockInfo reference blockType number
  let response ← client.exchangeUserData reference S7.blocksInfoGroup S7.blockInfoSubfunction request
  orThrow <| S7.decodeBlockInfo response.payload

private def uploadSafetyLimit : Nat := 64 * 1024 * 1024

private partial def Client.uploadFragments (client : Client) (uploadId : UInt8)
    (fragmentNumber : Nat) (state : Upload.State uploadSafetyLimit) (deadline : Option Nat) :
    IO (Upload.State uploadSafetyLimit) := do
  if fragmentNumber >= 65536 then
    throw <| ClientError.protocol "block upload exceeded the 65536-fragment safety limit"
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeUpload reference uploadId
  let response ← client.exchangeWithRetries reference request 0 false deadline
  let fragment ← decodeOrThrow <| S7.decodeUploadFragment reference response
  let accepted ← decodeOrThrow <| Upload.accept state fragment
  if fragment.isLast then return accepted.after
  client.uploadFragments uploadId (fragmentNumber + 1) accepted.after deadline

private def Client.uploadBlockData (client : Client) (blockType : S7.BlockType)
    (number : Nat) : IO ByteArray :=
  client.serialized do
    try
      let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
      let startReference ← client.freshReference
      let startRequest ← inputOrThrow <| S7.encodeStartUpload startReference blockType number
      let startResponse ← client.exchangeWithRetries startReference startRequest
        client.config.reconnectRetries false deadline
      let upload ← decodeOrThrow <| S7.decodeStartUpload startReference startResponse
      let transferred ← try
        let ready ← decodeOrThrow <| Upload.start uploadSafetyLimit upload.loadSize
        client.uploadFragments upload.uploadId 0 ready deadline
      catch error =>
          let endReference ← client.freshReference
          try
            let endRequest ← inputOrThrow <| S7.encodeEndUpload endReference upload.uploadId
            let endResponse ← client.exchangeWithRetries endReference endRequest 0 false deadline
            decodeOrThrow <| S7.decodeEndUpload endReference endResponse
          catch _ => pure ()
          throw error
      let endReference ← client.freshReference
      let endRequest ← inputOrThrow <| S7.encodeEndUpload endReference upload.uploadId
      let endResponse ← client.exchangeWithRetries endReference endRequest 0 false deadline
      decodeOrThrow <| S7.decodeEndUpload endReference endResponse
      let completed ← decodeOrThrow <| Upload.finish transferred
      return completed.assembly.data
    catch error =>
      client.closeCurrent
      throw error

def Client.fullUpload (client : Client) (blockType : S7.BlockType) (number : Nat) : IO ByteArray :=
  client.uploadBlockData blockType number

def Client.upload (client : Client) (blockType : S7.BlockType) (number : Nat) : IO ByteArray := do
  let full ← client.uploadBlockData blockType number
  if full.size < 36 then
    throw <| ClientError.protocol "full block upload omitted its 36-byte compact header"
  let (mc7Size, _) ← orThrow <| ({ data := full, offset := 34 } : Cursor).readUInt16BE
  if full.size < 36 + mc7Size.toNat then
    throw <| ClientError.protocol s!"block upload contains fewer than {mc7Size} MC7 bytes"
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

private def Client.receiveServerJob (client : Client) (transferDeadline : Option Nat) : IO S7.JobPdu := do
  Transport.checkReceiveDeadline transferDeadline
  let some connection ← client.connection.get
    | throw <| ClientError.disconnected "S7 client is disconnected"
  let pduLength ← client.currentPduLength.get
  orThrow <| S7.decodeJobPdu
    (← Transport.receiveDataUntil connection.socket
      (Transport.earlierReceiveDeadline
        (← Transport.receiveDeadline client.config.operationTimeoutMs) transferDeadline) pduLength.toNat)

private def Client.sendServerResponse (client : Client) (response : ByteArray) : IO Unit := do
  let some connection ← client.connection.get
    | throw <| ClientError.disconnected "S7 client is disconnected"
  Transport.sendData connection.socket response client.config.operationTimeoutMs

private partial def Client.serveDownloadFragments (client : Client) (blockType : S7.BlockType)
    (number : Nat) (blockData : ByteArray) (state : Download.State blockData)
    (maxSlice fragmentNumber : Nat) (deadline : Option Nat) : IO (Download.State blockData) := do
  if fragmentNumber >= 65536 then
    throw <| ClientError.protocol "block download exceeded the 65536-fragment safety limit"
  let job ← client.receiveServerJob deadline
  decodeOrThrow <| S7.validateDownloadServiceRequest job S7.downloadFunction blockType number
  let some fragment := Download.nextFragment blockData state maxSlice
    | throw <| ClientError.protocol "unexpected PLC download fragment request"
  let isLast := fragment.after.phase == .awaitingEnd
  let response ← inputOrThrow <|
    S7.encodeDownloadFragmentResponse job.reference isLast fragment.chunk
  Transport.checkReceiveDeadline deadline
  client.sendServerResponse response
  if isLast then return fragment.after
  client.serveDownloadFragments blockType number blockData fragment.after maxSlice (fragmentNumber + 1) deadline

/-- Download a complete load-memory block returned by `fullUpload`. Classic S7
    download is PLC-driven: after the initial request the PLC asks for each
    fragment, then the client inserts the transferred block. -/
def Client.downloadBlock (client : Client) (blockType : S7.BlockType) (number : Nat)
    (blockData : ByteArray) : IO Unit :=
  client.serialized do
    try
      if blockData.size < 36 then
        throw <| ClientError.invalidInput "download data must contain a 36-byte compact block header"
      let (mc7Size, _) ← orThrow <| ({ data := blockData, offset := 34 } : Cursor).readUInt16BE
      if 36 + mc7Size.toNat > blockData.size then
        throw <| ClientError.invalidInput "compact block header declares more MC7 data than supplied"
      let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
      let startReference ← client.freshReference
      let startRequest ← inputOrThrow <| S7.encodeRequestDownload startReference blockType number
        blockData.size mc7Size.toNat
      let startResponse ← client.exchangeWithRetries startReference startRequest
        client.config.reconnectRetries false deadline
      decodeOrThrow <| S7.decodeRequestDownloadAck startReference startResponse
      let pduLength ← client.negotiatedPduLength
      if pduLength.toNat <= 18 then
        throw <| ClientError.protocol "negotiated PDU is too small for block download"
      let some ready := Download.acknowledge (Download.start blockData)
        | throw <| ClientError.lifecycle "download request acknowledgement was not accepted"
      let transferred ← client.serveDownloadFragments blockType number blockData ready
        (pduLength.toNat - 18) 0 deadline
      let ended ← client.receiveServerJob deadline
      decodeOrThrow <| S7.validateDownloadServiceRequest ended S7.downloadEndedFunction
        blockType number
      let some _ := Download.finish blockData transferred
        | throw <| ClientError.protocol "PLC ended an incomplete block download"
      Transport.checkReceiveDeadline deadline
      client.sendServerResponse (← inputOrThrow <| S7.encodeDownloadEndedResponse ended.reference)
      let insertReference ← client.freshReference
      let insertRequest ← inputOrThrow <| S7.encodeInsertBlock insertReference blockType number
      let insertResponse ← client.exchangeWithRetries insertReference insertRequest 0 false deadline
      decodeOrThrow <| S7.decodePlcControl insertReference S7.startFunction insertResponse
    catch error =>
      client.closeCurrent
      throw error

def Client.readForceTable (client : Client) : IO (Array S7.ForceEntry) := do
  orThrow <| S7.decodeForceTable (← client.readSzl 0x0025 0)

private def Client.readAreaChunk (client : Client) (range : S7.MemoryRange)
    (deadline : Option Nat) (retries : Nat) :
    IO { data : ByteArray // data.size = range.count * range.area.elementSize } := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeAreaRead reference range
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| ClientError.invalidInput s!"request exceeds negotiated PDU length {pduLength}"
  let expectedSize := range.count * range.area.elementSize
  if expectedSize + 18 > pduLength.toNat then
    throw <| ClientError.invalidInput s!"response would exceed negotiated PDU length {pduLength}"
  let response ← client.exchangeWithRetries reference request retries false deadline
  match hdecode : S7.decodeAreaRead reference range.area expectedSize response with
  | .error (.remoteFailure _ message) => throw <| ClientError.plcRejected message
  | .error error => throw <| ClientError.protocol (reprStr error)
  | .ok payload =>
      return ⟨payload, S7.decodeAreaRead_size reference range.area expectedSize response
        payload hdecode⟩

private def Client.writeAreaChunk (client : Client) (range : S7.MemoryRange)
    (payload : ByteArray) (deadline : Option Nat) (retries : Nat) : IO Unit := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeAreaWrite reference range payload
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| ClientError.invalidInput s!"request exceeds negotiated PDU length {pduLength}"
  let response ← client.exchangeWithRetries reference request retries false deadline
  decodeOrThrow <| S7.decodeDbWrite reference response

private def Client.readAreaChunks (client : Client) (area : S7.Area)
    (dbNumber : UInt16) (start : Nat) (consumed : Nat) (chunks : List Nat)
    (result : Chunking.ReadAssembly area.elementSize consumed) (deadline : Option Nat)
    (retries : Nat) :
    IO (Chunking.ReadAssembly area.elementSize (consumed + chunks.sum)) := do
  match hchunks : chunks with
  | [] => return (by simpa [hchunks] using result)
  | count :: rest =>
      let chunk ← client.readAreaChunk {
        area, dbNumber, start := result.nextStart start, count
      } deadline retries
      let assembled ← client.readAreaChunks area dbNumber start (consumed + count)
        rest (result.append chunk) deadline 0
      return (by simpa [hchunks, List.sum_cons, Nat.add_assoc] using assembled)

/-- Internal transfer result retains the byte-count proof through the IO loop. -/
private def Client.readAreaChecked (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start count : Nat) (deadline : Option Nat) (retries : Nat) :
    IO { data : ByteArray // data.size = count * area.elementSize } := do
  if hzero : count = 0 then
    return ⟨ByteArray.empty, by simp [hzero]⟩
  inputOrThrow <| MultiValidation.range { area, dbNumber, start, count }
  let pduLength ← client.negotiatedPduLength
  let maxCount := MultiValidation.readMaximum pduLength.toNat area
  if hmaximum : maxCount = 0 then
    throw <| ClientError.protocol s!"negotiated PDU length {pduLength} cannot hold a read item"
  else
    let assembled ← client.readAreaChunks area dbNumber start 0
      (Chunking.counts count maxCount) (Chunking.ReadAssembly.empty area.elementSize) deadline retries
    return ⟨assembled.data, Chunking.ReadAssembly.complete_size count maxCount
      area.elementSize hmaximum assembled⟩

def Client.readArea (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start count : Nat) : IO ByteArray := do
  client.serialized do
    let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
    return (← client.readAreaChecked area dbNumber start count deadline client.config.reconnectRetries).val

private def Client.writeAreaChunks (client : Client) (area : S7.Area)
    (dbNumber : UInt16) (start offset : Nat) (payload : ByteArray)
    (chunks : List Nat) (hcoverage : offset + chunks.sum * area.elementSize = payload.size)
    (deadline : Option Nat) (retries : Nat) :
    IO Unit := do
  match hchunks : chunks with
  | [] => pure ()
  | count :: rest =>
      let byteCount := count * area.elementSize
      have htail : offset + byteCount + rest.sum * area.elementSize = payload.size := by
        simpa [hchunks, byteCount, Nat.add_mul, Nat.add_assoc] using hcoverage
      let chunk := Chunking.writeSlice payload offset count area.elementSize (by omega)
      client.writeAreaChunk { area, dbNumber, start := start + offset, count } chunk.val deadline retries
      client.writeAreaChunks area dbNumber start (offset + byteCount)
        payload rest htail deadline 0

private def Client.writeAreaChecked (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start : Nat) (payload : ByteArray) (deadline : Option Nat) (retries : Nat) : IO Unit := do
  if payload.isEmpty then
    return
  if haligned : payload.size % area.elementSize ≠ 0 then
    throw <| ClientError.invalidInput
      s!"payload size {payload.size} is not aligned to {area.elementSize}-byte elements"
  else
    inputOrThrow <| MultiValidation.range {
      area, dbNumber, start, count := payload.size / area.elementSize
    }
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
      throw <| ClientError.protocol s!"negotiated PDU length {pduLength} cannot hold a write item"
    else
      client.writeAreaChunks area dbNumber start 0 payload
        (Chunking.counts (payload.size / area.elementSize) maxCount) (by
          simpa [Chunking.counts_sum _ _ hmaximum] using hsize) deadline retries

def Client.writeArea (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start : Nat) (payload : ByteArray) : IO Unit :=
  client.serialized do
    let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
    client.writeAreaChecked area dbNumber start payload deadline client.config.reconnectRetries

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
      if range.count > 0 && MultiValidation.readLengthRepresentable range && count < S7.maxItemCount &&
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

/-- Every selected read has a positive element count. -/
theorem takeReadBatch_positive (pduLength : Nat)
    (pending : List S7.MemoryRange) (count requestSize responseSize : Nat)
    (selected : List S7.MemoryRange)
    (hselected : ∀ range ∈ selected, 0 < range.count) :
    ∀ range ∈ (takeReadBatch pduLength pending count requestSize responseSize selected).1,
      0 < range.count := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeReadBatch] using hselected
  | cons range rest ih =>
    simp only [takeReadBatch]
    split
    case isTrue hcondition =>
      have hproperties := hcondition
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hproperties
      apply ih (count + 1) (requestSize + 12)
        (responseSize + readResponseContribution range) (range :: selected)
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | hmem
      · subst item
        exact hproperties.1.1.1.1
      · exact hselected item hmem
    case isFalse => simpa using hselected

/-- Every selected read can represent its successful response's length field. -/
theorem takeReadBatch_lengths (pduLength : Nat)
    (pending : List S7.MemoryRange) (count requestSize responseSize : Nat)
    (selected : List S7.MemoryRange)
    (hselected : ∀ range ∈ selected, MultiValidation.readLengthRepresentable range = true) :
    ∀ range ∈ (takeReadBatch pduLength pending count requestSize responseSize selected).1,
      MultiValidation.readLengthRepresentable range = true := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeReadBatch] using hselected
  | cons range rest ih =>
    simp only [takeReadBatch]
    split
    case isTrue hcondition =>
      have hproperties := hcondition
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hproperties
      apply ih (count + 1) (requestSize + 12)
        (responseSize + readResponseContribution range) (range :: selected)
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | hmem
      · subst item
        exact hproperties.1.1.1.2
      · exact hselected item hmem
    case isFalse => simpa using hselected

/-- A certificate for the exact read planner used by the client, including its
    unprocessed suffix. Budget accounting conservatively includes final padding. -/
structure ReadBatchPlan (pduLength : Nat) (pending : List S7.MemoryRange) where
  selected : List S7.MemoryRange
  remaining : List S7.MemoryRange
  partition : selected ++ remaining = pending
  countBound : selected.length ≤ S7.maxItemCount
  positive : ∀ range ∈ selected, 0 < range.count
  lengths : ∀ range ∈ selected, MultiValidation.readLengthRepresentable range = true
  budgets : 14 ≤ pduLength →
    12 + 12 * selected.length ≤ pduLength ∧
      14 + readResponseContributions selected ≤ pduLength

def planReadBatch (pduLength : Nat) (pending : List S7.MemoryRange) :
    ReadBatchPlan pduLength pending :=
  let result := takeReadBatch pduLength pending 0 12 14 []
  { selected := result.1, remaining := result.2
    partition := by simpa using takeReadBatch_preserves_order pduLength pending 0 12 14 []
    countBound := takeReadBatch_count_le pduLength pending 0 12 14 [] (by simp)
      (by decide)
    positive := takeReadBatch_positive pduLength pending 0 12 14 [] (by simp)
    lengths := takeReadBatch_lengths pduLength pending 0 12 14 [] (by simp)
    budgets := fun h => takeReadBatch_fits pduLength pending (by omega) h }

private def Client.readMultiBatch (client : Client) (ranges : Array S7.MemoryRange)
    (deadline : Option Nat) (retries : Nat) : IO (Array S7.ReadItemResult) := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeAreaReadMany reference ranges
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| ClientError.invalidInput
      s!"multi-read request exceeds negotiated PDU length {pduLength}"
  let response ← client.exchangeWithRetries reference request retries false deadline
  decodeOrThrow <| S7.decodeAreaReadMany reference ranges response

private def Client.readMultiChunks (client : Client) (range : S7.MemoryRange)
    (offset : Nat) (chunks : List Nat) (payload : ByteArray)
    (deadline : Option Nat) (retries : Nat) : IO S7.ReadItemResult := do
  match chunks with
  | [] => return .success payload
  | count :: rest =>
      let results ← client.readMultiBatch #[{ range with start := range.start + offset, count }] deadline retries
      match results[0]? with
      | some (S7.ReadItemResult.failure code) => return .failure code
      | some (S7.ReadItemResult.success fragment) =>
          client.readMultiChunks range (offset + count * range.area.elementSize)
            rest (payload ++ fragment) deadline 0
      | none => throw <| ClientError.protocol "singleton multi-read omitted its result"

private partial def Client.readMultiLoop (client : Client) (pending : List S7.MemoryRange)
    (results : Array S7.ReadItemResult) (deadline : Option Nat)
    (retries : Nat) : IO (Array S7.ReadItemResult) := do
  match pending with
  | [] => return results
  | range :: rest =>
      let pduLength ← client.negotiatedPduLength
      let plan := planReadBatch pduLength.toNat pending
      let batch := plan.selected
      let remaining := plan.remaining
      if batch.isEmpty then
        let maximum := MultiValidation.readMaximum pduLength.toNat range.area
        if maximum = 0 then
          throw <| ClientError.invalidInput "negotiated PDU cannot hold a multi-read item"
        let result ← client.readMultiChunks range 0 (Chunking.counts range.count maximum)
          ByteArray.empty deadline retries
        client.readMultiLoop rest (results.push result) deadline 0
      else
        let batchResults ← client.readMultiBatch batch.toArray deadline retries
        client.readMultiLoop remaining (results ++ batchResults) deadline 0

def Client.readMulti (client : Client) (ranges : Array S7.MemoryRange) : IO (Array S7.ReadItemResult) :=
  client.serialized do
    for range in ranges do
      inputOrThrow <| MultiValidation.range range
    let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
    try
      client.readMultiLoop ranges.toList #[] deadline client.config.reconnectRetries
    catch error =>
      client.closeCurrent
      throw error

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
          MultiValidation.readLengthRepresentable item.range &&
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

/-- Every selected write has a positive count and an exactly matching payload. -/
theorem takeWriteBatch_payloads (pduLength : Nat)
    (pending : List S7.WriteItem) (count requestSize responseSize : Nat)
    (selected : List S7.WriteItem)
    (hselected : ∀ item ∈ selected, 0 < item.range.count ∧
      item.payload.size = item.range.count * item.range.area.elementSize) :
    ∀ item ∈ (takeWriteBatch pduLength pending count requestSize responseSize selected).1,
      0 < item.range.count ∧
        item.payload.size = item.range.count * item.range.area.elementSize := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeWriteBatch] using hselected
  | cons item rest ih =>
    simp only [takeWriteBatch]
    split
    case isTrue hcondition =>
      have hproperties := hcondition
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hproperties
      apply ih (count + 1) (requestSize + writeRequestContribution item)
        (responseSize + 1) (item :: selected)
      intro next hnext
      rcases List.mem_cons.mp hnext with heq | hmem
      · subst next
        exact hproperties.1.1.1.1
      · exact hselected next hmem
    case isFalse => simpa using hselected

/-- Every selected write has a representable data-length field. -/
theorem takeWriteBatch_lengths (pduLength : Nat)
    (pending : List S7.WriteItem) (count requestSize responseSize : Nat)
    (selected : List S7.WriteItem)
    (hselected : ∀ item ∈ selected, MultiValidation.readLengthRepresentable item.range = true) :
    ∀ item ∈ (takeWriteBatch pduLength pending count requestSize responseSize selected).1,
      MultiValidation.readLengthRepresentable item.range = true := by
  induction pending generalizing count requestSize responseSize selected with
  | nil => simpa [takeWriteBatch] using hselected
  | cons item rest ih =>
    simp only [takeWriteBatch]
    split
    case isTrue hcondition =>
      have hproperties := hcondition
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hproperties
      apply ih (count + 1) (requestSize + writeRequestContribution item)
        (responseSize + 1) (item :: selected)
      intro next hnext
      rcases List.mem_cons.mp hnext with heq | hmem
      · subst next
        exact hproperties.1.1.1.2
      · exact hselected next hmem
    case isFalse => simpa using hselected

/-- A certificate for the exact write planner used by the client. -/
structure WriteBatchPlan (pduLength : Nat) (pending : List S7.WriteItem) where
  selected : List S7.WriteItem
  remaining : List S7.WriteItem
  partition : selected ++ remaining = pending
  countBound : selected.length ≤ S7.maxItemCount
  payloads : ∀ item ∈ selected, 0 < item.range.count ∧
    item.payload.size = item.range.count * item.range.area.elementSize
  lengths : ∀ item ∈ selected, MultiValidation.readLengthRepresentable item.range = true
  budgets : 14 ≤ pduLength →
    12 + writeRequestContributions selected ≤ pduLength ∧
      14 + selected.length ≤ pduLength

def planWriteBatch (pduLength : Nat) (pending : List S7.WriteItem) :
    WriteBatchPlan pduLength pending :=
  let result := takeWriteBatch pduLength pending 0 12 14 []
  { selected := result.1, remaining := result.2
    partition := by simpa using takeWriteBatch_preserves_order pduLength pending 0 12 14 []
    countBound := takeWriteBatch_count_le pduLength pending 0 12 14 [] (by simp)
      (by decide)
    payloads := takeWriteBatch_payloads pduLength pending 0 12 14 [] (by simp)
    lengths := takeWriteBatch_lengths pduLength pending 0 12 14 [] (by simp)
    budgets := fun h => takeWriteBatch_fits pduLength pending (by omega) h }

private def Client.writeMultiBatch (client : Client) (items : Array S7.WriteItem)
    (deadline : Option Nat) (retries : Nat) : IO (Array S7.WriteItemResult) := do
  let reference ← client.freshReference
  let request ← inputOrThrow <| S7.encodeAreaWriteMany reference items
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| ClientError.invalidInput
      s!"multi-write request exceeds negotiated PDU length {pduLength}"
  let response ← client.exchangeWithRetries reference request retries false deadline
  decodeOrThrow <| S7.decodeAreaWriteMany reference items.size response

private def Client.writeMultiChunks (client : Client) (item : S7.WriteItem)
    (offset : Nat) (chunks : List Nat) (deadline : Option Nat)
    (retries : Nat) : IO S7.WriteItemResult := do
  match chunks with
  | [] => return .success
  | count :: rest =>
      let byteCount := count * item.range.area.elementSize
      let chunk : S7.WriteItem := {
        range := { item.range with start := item.range.start + offset, count }
        payload := item.payload.extract offset (offset + byteCount)
      }
      let results ← client.writeMultiBatch #[chunk] deadline retries
      match results[0]? with
      | some (S7.WriteItemResult.failure code) => return .failure code
      | some S7.WriteItemResult.success => client.writeMultiChunks item (offset + byteCount) rest deadline 0
      | none => throw <| ClientError.protocol "singleton multi-write omitted its result"

private partial def Client.writeMultiLoop (client : Client) (pending : List S7.WriteItem)
    (results : Array S7.WriteItemResult) (deadline : Option Nat)
    (retries : Nat) : IO (Array S7.WriteItemResult) := do
  match pending with
  | [] => return results
  | item :: rest =>
      let pduLength ← client.negotiatedPduLength
      let plan := planWriteBatch pduLength.toNat pending
      let batch := plan.selected
      let remaining := plan.remaining
      if batch.isEmpty then
        let maximum := MultiValidation.writeMaximum pduLength.toNat item.range.area
        if maximum = 0 then
          throw <| ClientError.invalidInput "negotiated PDU cannot hold a multi-write item"
        let result ← client.writeMultiChunks item 0 (Chunking.counts item.range.count maximum) deadline retries
        client.writeMultiLoop rest (results.push result) deadline 0
      else
        let batchResults ← client.writeMultiBatch batch.toArray deadline retries
        client.writeMultiLoop remaining (results ++ batchResults) deadline 0

/-- Locally validate the whole request before sending any writes. Successful
    chunks preceding a PLC rejection remain written: this is not an atomic API. -/
def Client.writeMulti (client : Client) (items : Array S7.WriteItem) : IO (Array S7.WriteItemResult) :=
  client.serialized do
    if items.isEmpty then return #[]
    let pduLength ← client.negotiatedPduLength
    inputOrThrow <| MultiValidation.writes pduLength.toNat items
    let deadline ← Transport.receiveDeadline client.config.transferReceiveTimeoutMs
    try
      client.writeMultiLoop items.toList #[] deadline client.config.reconnectRetries
    catch error =>
      client.closeCurrent
      throw error

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
  if bitIndex > 7 then
    throw <| ClientError.invalidInput s!"bit index must be between 0 and 7, got {bitIndex}"
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
  if bitIndex > 7 then
    throw <| ClientError.invalidInput s!"bit index must be between 0 and 7, got {bitIndex}"
  let current ← client.dbReadUInt8 dbNumber byteOffset
  let updated ← inputOrThrow <| Value.setBit current bitIndex enabled
  client.dbWriteUInt8 dbNumber byteOffset updated

def Client.dbReadString (client : Client) (dbNumber : UInt16) (start : Nat) : IO String := do
  let header ← client.dbRead dbNumber start 2
  let maximum ← orThrow <| Value.getUInt8 header
  if maximum.toNat > Value.maxStringLength then
    throw <| ClientError.protocol s!"invalid S7 STRING maximum length {maximum}"
  orThrow <| Value.decodeString (← client.dbRead dbNumber start (maximum.toNat + 2))

def Client.dbWriteString (client : Client) (dbNumber : UInt16) (start maximum : Nat)
    (value : String) : IO Unit := do
  client.dbWrite dbNumber start (← inputOrThrow <| Value.encodeString maximum value)

def Client.dbReadWString (client : Client) (dbNumber : UInt16) (start : Nat) : IO String := do
  let header ← client.dbRead dbNumber start 4
  let maximum ← orThrow <| Value.getUInt16 header
  if maximum.toNat > Value.maxWStringLength then
    throw <| ClientError.protocol s!"invalid S7 WSTRING maximum length {maximum}"
  orThrow <| Value.decodeWString (← client.dbRead dbNumber start (maximum.toNat * 2 + 4))

def Client.dbWriteWString (client : Client) (dbNumber : UInt16) (start maximum : Nat)
    (value : String) : IO Unit := do
  client.dbWrite dbNumber start (← inputOrThrow <| Value.encodeWString maximum value)

/-- Write an input/output process-image bit. This is not a persistent CPU force
    table operation; a PLC scan may overwrite it. -/
def Client.forceBit (client : Client) (area : S7.Area) (byteOffset bit : Nat)
    (value : Bool) : IO Unit := do
  if area != .processInputs && area != .processOutputs then
    throw <| ClientError.invalidInput
      "process-image bit override only supports input and output areas"
  if bit > 7 then
    throw <| ClientError.invalidInput s!"bit index must be between 0 and 7, got {bit}"
  let current ← client.readArea area 0 byteOffset 1
  let updated ← inputOrThrow <| Value.setBit current[0]! bit value
  client.writeArea area 0 byteOffset (bytes #[updated])

def Client.cancelForceBit (client : Client) (area : S7.Area) (byteOffset bit : Nat) : IO Unit :=
  client.forceBit area byteOffset bit false

def Client.disconnect (client : Client) : IO Unit :=
  client.serialized do
    client.closeCurrent
    client.applyLifecycleEvent .disconnect

end LeanS7
