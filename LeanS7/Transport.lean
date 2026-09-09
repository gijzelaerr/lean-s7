import Std.Async.TCP
import Std.Async.DNS
import Std.Async.Timer
import LeanS7.TPKT
import LeanS7.COTP

namespace LeanS7.Transport

open Std Std.Net Std.Async

abbrev Socket := TCP.Socket.Client

inductive Endpoint where
  | ipv4 (address : IPv4Addr)
  | ipv6 (address : IPv6Addr)
  | hostname (name : String)

structure Connection where
  socket : Socket
  localReference : UInt16
  remoteReference : UInt16
  tpduSizeExponent : UInt8

private inductive TimeoutResult (α : Type) where
  | completed (result : Except IO.Error α)
  | timedOut

private instance : Nonempty (TimeoutResult α) := ⟨.timedOut⟩

private inductive ReceiveResult where
  | received (data : Option ByteArray)
  | timedOut

private def withTimeout (timeoutMs : Option Nat) (label : String) (operation : IO α) : IO α := do
  let some timeoutMs := timeoutMs | operation
  let result : IO.Promise (TimeoutResult α) ← IO.Promise.new
  let finished ← IO.mkRef false
  let operationTask ← IO.asTask operation
  let timerTask ← IO.asTask do IO.sleep (UInt32.ofNat timeoutMs)
  IO.chainTask operationTask fun value => do
    if ← finished.modifyGet fun done => (!done, true) then
      result.resolve (TimeoutResult.completed value)
  IO.chainTask timerTask fun _ => do
    if ← finished.modifyGet fun done => (!done, true) then
      result.resolve TimeoutResult.timedOut
  let some outcome ← IO.wait result.result?
    | throw <| IO.userError s!"{label} timeout waiter was cancelled"
  match outcome with
  | .completed (.ok value) =>
      IO.cancel timerTask
      return value
  | .completed (.error error) =>
      IO.cancel timerTask
      throw error
  | .timedOut =>
      IO.cancel operationTask
      throw <| IO.userError s!"{label} timed out after {timeoutMs} ms"

private def await (operation : Async α) : IO α := do
  let task ← operation.toIO
  task.block

private def orThrow [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError (reprStr error)

def sendBytes (socket : Socket) (data : ByteArray) (_timeoutMs : Option Nat := none) : IO Unit :=
  await (socket.send data)

private def receiveSome (socket : Socket) (count : Nat) (timeoutMs : Option Nat) : IO (Option ByteArray) := do
  let some timeoutMs := timeoutMs | await (socket.recv? count.toUInt64)
  let timer ← await (Selector.sleep (Std.Time.Millisecond.Offset.ofNat timeoutMs))
  let selected : Async ReceiveResult := Selectable.one #[
    .case (socket.recvSelector count.toUInt64) fun data => pure (ReceiveResult.received data),
    .case timer fun _ => pure ReceiveResult.timedOut
  ]
  match ← await selected with
  | .received data => return data
  | .timedOut => throw <| IO.userError s!"socket receive timed out after {timeoutMs} ms"

def receiveExact (socket : Socket) (count : Nat) (timeoutMs : Option Nat := none) : IO ByteArray := do
  let mut result := ByteArray.empty
  while result.size < count do
    let some chunk ← receiveSome socket (count - result.size) timeoutMs
      | throw <| IO.userError s!"connection closed with {count - result.size} bytes still expected"
    if chunk.size == 0 then
      throw <| IO.userError "socket returned an empty chunk before EOF"
    result := result ++ chunk
  return result

def sendFrame (socket : Socket) (payload : ByteArray) (timeoutMs : Option Nat := none) : IO Unit := do
  let frame ← orThrow <| TPKT.encode { payload }
  sendBytes socket frame timeoutMs

def receiveFrame (socket : Socket) (timeoutMs : Option Nat := none) : IO ByteArray := do
  let header ← receiveExact socket TPKT.headerSize timeoutMs
  let cursor : Cursor := { data := header, offset := 2 }
  let (length, _) ← orThrow cursor.readUInt16BE
  if length.toNat < TPKT.headerSize then
    throw <| IO.userError s!"invalid TPKT frame length {length}"
  let payload ← receiveExact socket (length.toNat - TPKT.headerSize) timeoutMs
  let frame ← orThrow <| TPKT.decode (header ++ payload)
  return frame.payload

def sendData (socket : Socket) (payload : ByteArray) (timeoutMs : Option Nat := none) : IO Unit :=
  sendFrame socket (COTP.encodeData { payload }) timeoutMs

private partial def receiveDataSegments (socket : Socket) (timeoutMs : Option Nat)
    (maximum : Nat) (state : COTP.Reassembly) : IO ByteArray := do
  let payload ← receiveFrame socket timeoutMs
  let segment ← orThrow <| COTP.decodeData payload
  let (state, complete) ← orThrow <| state.pushBounded segment maximum
  if complete then
    return state.payload
  receiveDataSegments socket timeoutMs maximum state

def receiveData (socket : Socket) (timeoutMs : Option Nat := none)
    (maxPayloadSize : Nat := 65535) : IO ByteArray :=
  receiveDataSegments socket timeoutMs maxPayloadSize {}

private def socketAddress (address : IPAddr) (port : UInt16) : SocketAddress :=
  match address with
  | .v4 address => SocketAddressV4.mk address port
  | .v6 address => SocketAddressV6.mk address port

def resolve (endpoint : Endpoint) (port : UInt16) (timeoutMs : Option Nat := none) : IO (Array SocketAddress) := do
  match endpoint with
  | .ipv4 address => return #[SocketAddressV4.mk address port]
  | .ipv6 address => return #[SocketAddressV6.mk address port]
  | .hostname name =>
      let addresses ← withTimeout timeoutMs "hostname resolution" <|
        await (DNS.getAddrInfo name (toString port))
      if addresses.isEmpty then
        throw <| IO.userError s!"hostname {name} resolved to no addresses"
      return addresses.map fun address => socketAddress address port

private def connectAddress (address : SocketAddress) (request : COTP.ConnectionRequest)
    (timeoutMs : Option Nat) : IO Connection := do
  let socket ← TCP.Socket.Client.mk
  try
    withTimeout timeoutMs "TCP connection" <| await (socket.connect address)
    socket.noDelay
    let connectionRequest := COTP.encodeConnectionRequest request
    sendFrame socket connectionRequest timeoutMs
    let confirmation ← orThrow <| COTP.decodeConnectionConfirm (← receiveFrame socket timeoutMs)
    let tpduSizeExponent ← orThrow <|
      COTP.negotiatedTpduSizeExponent request confirmation
    return {
      socket
      localReference := request.sourceReference
      remoteReference := confirmation.sourceReference
      tpduSizeExponent
    }
  catch error =>
    try await socket.shutdown catch _ => pure ()
    throw error

private def connectAddresses (addresses : List SocketAddress) (request : COTP.ConnectionRequest)
    (timeoutMs : Option Nat) : IO Connection := do
  match addresses with
  | [] => throw <| IO.userError "could not connect to any resolved address"
  | address :: rest =>
      try connectAddress address request timeoutMs
      catch error =>
        if rest.isEmpty then throw error
        connectAddresses rest request timeoutMs

def connect (endpoint : Endpoint) (port : UInt16) (request : COTP.ConnectionRequest)
    (timeoutMs : Option Nat := none) : IO Connection := do
  let addresses ← resolve endpoint port timeoutMs
  connectAddresses addresses.toList request timeoutMs

def disconnect (connection : Connection) (timeoutMs : Option Nat := none) : IO Unit := do
  try
    withTimeout timeoutMs "COTP disconnect" <|
      sendFrame connection.socket (COTP.encodeDisconnectRequest {
        destinationReference := connection.remoteReference
        sourceReference := connection.localReference
      })
  catch _ => pure ()
  withTimeout timeoutMs "socket shutdown" <| await connection.socket.shutdown

def shutdown (socket : Socket) : IO Unit :=
  await socket.shutdown

end LeanS7.Transport
