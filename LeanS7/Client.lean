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

def Client.dbRead (client : Client) (dbNumber : UInt16) (start size : Nat) : IO ByteArray := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeDbRead reference { dbNumber, start, size }
  if request.size > client.pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {client.pduLength}"
  if size + 18 > client.pduLength.toNat then
    throw <| IO.userError s!"response would exceed negotiated PDU length {client.pduLength}"
  let response ← exchange client.socket request
  orThrow <| S7.decodeDbRead reference response

def Client.dbWrite (client : Client) (dbNumber : UInt16) (start : Nat) (payload : ByteArray) : IO Unit := do
  let reference ← client.freshReference
  let request ← orThrow <| S7.encodeDbWrite reference dbNumber start payload
  if request.size > client.pduLength.toNat then
    throw <| IO.userError s!"request exceeds negotiated PDU length {client.pduLength}"
  let response ← exchange client.socket request
  orThrow <| S7.decodeDbWrite reference response

def Client.disconnect (client : Client) : IO Unit :=
  Transport.shutdown client.socket

end LeanS7
