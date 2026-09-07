import LeanS7.Transport
import LeanS7.S7

namespace LeanS7

open Std.Net

structure ClientConfig where
  address : IPv4Addr
  port : UInt16 := 102
  rack : Nat := 0
  slot : Nat := 2
  localTsap : UInt16 := 0x0100

structure Client where
  private socket : Transport.Socket
  pduLength : UInt16
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

private def exchange (socket : Transport.Socket) (request : ByteArray) : IO S7.Response := do
  Transport.sendData socket request
  orThrow <| S7.decodeResponse (← Transport.receiveData socket)

def Client.connect (config : ClientConfig) : IO Client := do
  let calledTsap ← remoteTsap config.rack config.slot
  let socket ← Transport.connect config.address config.port {
    callingTsap := config.localTsap
    calledTsap
  }
  try
    let reference : UInt16 := 1
    let request ← orThrow <| S7.encodeSetupCommunication reference
    let response ← exchange socket request
    let setup ← orThrow <| S7.decodeSetupCommunication reference response
    let nextReference ← IO.mkRef 2
    return { socket, pduLength := setup.pduLength, nextReference }
  catch error =>
    try Transport.shutdown socket catch _ => pure ()
    throw error

private def Client.freshReference (client : Client) : IO UInt16 := do
  let reference ← client.nextReference.get
  client.nextReference.set (reference + 1)
  return reference

private def Client.readAreaChunk (client : Client) (range : S7.MemoryRange) : IO ByteArray := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaRead reference range
  if request.size > client.pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {client.pduLength}"
  let expectedSize := range.count * range.area.elementSize
  if expectedSize + 18 > client.pduLength.toNat then
    throw <| IO.userError s!"response would exceed negotiated PDU length {client.pduLength}"
  let response ← exchange client.socket request
  orThrow <| S7.decodeAreaRead reference range.area expectedSize response

private def Client.writeAreaChunk (client : Client) (range : S7.MemoryRange)
    (payload : ByteArray) : IO Unit := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeAreaWrite reference range payload
  if request.size > client.pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {client.pduLength}"
  let response ← exchange client.socket request
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
  let availableBytes := client.pduLength.toNat - 18
  let maxCount := min S7.maxSectionSize (availableBytes / area.elementSize)
  if maxCount == 0 then
    throw <| IO.userError s!"negotiated PDU length {client.pduLength} cannot hold a read item"
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
  let availableBytes := client.pduLength.toNat - 28
  let lengthLimitedBytes := if area.dataTransportSize == S7.octetTransportSize then
    S7.maxSectionSize
  else
    S7.maxSectionSize / 8
  let maxCount := min S7.maxSectionSize
    (min availableBytes lengthLimitedBytes / area.elementSize)
  if maxCount == 0 then
    throw <| IO.userError s!"negotiated PDU length {client.pduLength} cannot hold a write item"
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

def Client.disconnect (client : Client) : IO Unit :=
  Transport.shutdown client.socket

end LeanS7
