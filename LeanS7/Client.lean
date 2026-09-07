import LeanS7.Transport
import LeanS7.Management
import LeanS7.Value

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
  private closed : IO.Ref Bool
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
    return (connection, setup)
  catch error =>
    try Transport.disconnect connection config.operationTimeoutMs catch _ => pure ()
    throw error

def Client.connect (config : ClientConfig) : IO Client := do
  let (session, setup) ← connectSession config
  let connection ← IO.mkRef (some session)
  let requestTail ← IO.mkRef (Task.pure (some ()))
  let closed ← IO.mkRef false
  let currentPduLength ← IO.mkRef setup.pduLength
  let nextReference ← IO.mkRef 2
  return { connection, requestTail, closed, config, pduLength := setup.pduLength, currentPduLength, nextReference }

private def Client.freshReference (client : Client) : IO UInt16 := do
  client.nextReference.modifyGet fun reference => (reference, reference + 1)

def Client.isConnected (client : Client) : IO Bool :=
  return (← client.connection.get).isSome

def Client.negotiatedPduLength (client : Client) : IO UInt16 :=
  client.currentPduLength.get

private def Client.closeCurrent (client : Client) : IO Unit := do
  let previous ← client.connection.modifyGet fun connection => (connection, none)
  if let some connection := previous then
    try Transport.disconnect connection client.config.operationTimeoutMs catch _ => pure ()

private def Client.exchangeBytesCurrent (client : Client) (reference : UInt16)
    (request : ByteArray) : IO ByteArray := do
  let some connection ← client.connection.get
    | throw <| IO.userError "S7 client is disconnected"
  Transport.sendData connection.socket request client.config.operationTimeoutMs
  for _ in [0:client.config.maxStaleResponses + 1] do
    let response ← Transport.receiveData connection.socket client.config.operationTimeoutMs
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
  client.currentPduLength.set setup.pduLength

private partial def Client.exchangeWithRetries (client : Client) (reference : UInt16)
    (request : ByteArray) (remainingRetries : Nat) (reconnectFirst : Bool := false) : IO S7.Response := do
  try
    if reconnectFirst then
      client.reconnect
    client.exchangeCurrent reference request
  catch error =>
    client.closeCurrent
    if remainingRetries == 0 || (← client.closed.get) then
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
    if remainingRetries == 0 || (← client.closed.get) then
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

private def Client.readAreaChunk (client : Client) (range : S7.MemoryRange) : IO ByteArray := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaRead reference range
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {pduLength}"
  let expectedSize := range.count * range.area.elementSize
  if expectedSize + 18 > pduLength.toNat then
    throw <| IO.userError s!"response would exceed negotiated PDU length {pduLength}"
  let response ← client.exchange reference request
  orThrow <| S7.decodeAreaRead reference range.area expectedSize response

private def Client.writeAreaChunk (client : Client) (range : S7.MemoryRange)
    (payload : ByteArray) : IO Unit := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaWrite reference range payload
  let pduLength ← client.negotiatedPduLength
  if request.size > pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {pduLength}"
  let response ← client.exchange reference request
  orThrow <| S7.decodeDbWrite reference response

private partial def Client.readAreaLoop (client : Client) (area : S7.Area)
    (dbNumber : UInt16) (start remaining maxCount : Nat) (result : ByteArray) : IO ByteArray := do
  if remaining == 0 then
    return result
  let count := min remaining maxCount
  let chunk ← client.readAreaChunk { area, dbNumber, start, count }
  client.readAreaLoop area dbNumber (start + count * area.elementSize) (remaining - count)
    maxCount (result ++ chunk)

def Client.readArea (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start count : Nat) : IO ByteArray := do
  if count == 0 then
    return ByteArray.empty
  let pduLength ← client.negotiatedPduLength
  let availableBytes := pduLength.toNat - 18
  let maxCount := min S7.maxSectionSize (availableBytes / area.elementSize)
  if maxCount == 0 then
    throw <| IO.userError s!"negotiated PDU length {pduLength} cannot hold a read item"
  client.readAreaLoop area dbNumber start count maxCount ByteArray.empty

private partial def Client.writeAreaLoop (client : Client) (area : S7.Area)
    (dbNumber : UInt16) (start remaining maxCount offset : Nat) (payload : ByteArray) : IO Unit := do
  if remaining == 0 then
    return
  let count := min remaining maxCount
  let byteCount := count * area.elementSize
  let chunk := payload.extract offset (offset + byteCount)
  client.writeAreaChunk { area, dbNumber, start, count } chunk
  client.writeAreaLoop area dbNumber (start + byteCount) (remaining - count) maxCount
    (offset + byteCount) payload

def Client.writeArea (client : Client) (area : S7.Area) (dbNumber : UInt16)
    (start : Nat) (payload : ByteArray) : IO Unit := do
  if payload.isEmpty then
    return
  if payload.size % area.elementSize != 0 then
    throw <| IO.userError s!"payload size {payload.size} is not aligned to {area.elementSize}-byte elements"
  let pduLength ← client.negotiatedPduLength
  let availableBytes := pduLength.toNat - 28
  let lengthLimitedBytes := if area.dataTransportSize == S7.octetTransportSize then
    S7.maxSectionSize
  else
    S7.maxSectionSize / 8
  let maxCount := min S7.maxSectionSize
    (min availableBytes lengthLimitedBytes / area.elementSize)
  if maxCount == 0 then
    throw <| IO.userError s!"negotiated PDU length {pduLength} cannot hold a write item"
  client.writeAreaLoop area dbNumber start (payload.size / area.elementSize) maxCount 0 payload

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

private def readResponseContribution (range : S7.MemoryRange) : Nat :=
  let size := range.count * range.area.elementSize
  4 + size + size % 2

private def takeReadBatch (pduLength : Nat) : List S7.MemoryRange →
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

private def writeRequestContribution (item : S7.WriteItem) : Nat :=
  12 + 4 + item.payload.size + item.payload.size % 2

private def takeWriteBatch (pduLength : Nat) : List S7.WriteItem →
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

def Client.disconnect (client : Client) : IO Unit :=
  client.serialized do
    client.closed.set true
    client.closeCurrent

end LeanS7
