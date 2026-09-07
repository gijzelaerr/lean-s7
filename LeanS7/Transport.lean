import Std.Async.TCP
import LeanS7.TPKT
import LeanS7.COTP

namespace LeanS7.Transport

open Std Std.Net Std.Async

abbrev Socket := TCP.Socket.Client

private def await (operation : Async α) : IO α := do
  let task ← operation.toIO
  task.block

private def orThrow [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError (reprStr error)

def sendBytes (socket : Socket) (data : ByteArray) : IO Unit :=
  await (socket.send data)

def receiveExact (socket : Socket) (count : Nat) : IO ByteArray := do
  let mut result := ByteArray.empty
  while result.size < count do
    let some chunk ← await (socket.recv? (count - result.size).toUInt64)
      | throw <| IO.userError s!"connection closed with {count - result.size} bytes still expected"
    if chunk.size == 0 then
      throw <| IO.userError "socket returned an empty chunk before EOF"
    result := result ++ chunk
  return result

def sendFrame (socket : Socket) (payload : ByteArray) : IO Unit := do
  let frame ← orThrow <| TPKT.encode { payload }
  sendBytes socket frame

def receiveFrame (socket : Socket) : IO ByteArray := do
  let header ← receiveExact socket TPKT.headerSize
  let cursor : Cursor := { data := header, offset := 2 }
  let (length, _) ← orThrow cursor.readUInt16BE
  if length.toNat < TPKT.headerSize then
    throw <| IO.userError s!"invalid TPKT frame length {length}"
  let payload ← receiveExact socket (length.toNat - TPKT.headerSize)
  let frame ← orThrow <| TPKT.decode (header ++ payload)
  return frame.payload

def sendData (socket : Socket) (payload : ByteArray) : IO Unit :=
  sendFrame socket (COTP.encodeData { payload })

def receiveData (socket : Socket) : IO ByteArray := do
  let payload ← receiveFrame socket
  let data ← orThrow <| COTP.decodeData payload
  if !data.endOfTransmission then
    throw <| IO.userError "segmented COTP data is not supported yet"
  return data.payload

def connect (address : IPv4Addr) (port : UInt16) (request : COTP.ConnectionRequest) : IO Socket := do
  let socket ← TCP.Socket.Client.mk
  await (socket.connect (SocketAddressV4.mk address port))
  socket.noDelay
  let connectionRequest := COTP.encodeConnectionRequest request
  sendFrame socket connectionRequest
  let confirmation ← receiveFrame socket
  discard <| orThrow (COTP.decodeConnectionConfirm confirmation)
  return socket

def shutdown (socket : Socket) : IO Unit :=
  await socket.shutdown

end LeanS7.Transport
