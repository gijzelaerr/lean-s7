import Std.Async.TCP
import Std.Async.DNS
import Std.Async.Timer
import LeanS7.ClientError
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

/-- Budgets must not silently wrap when passed to native timer APIs. -/
def maximumTimeoutMs : Nat := 4294967295

def validateTimeoutMs (timeoutMs : Option Nat) : IO Unit := do
  if let some timeout := timeoutMs then
    if timeout > maximumTimeoutMs then
      throw <| ClientError.invalidInput s!"timeout exceeds maximum {maximumTimeoutMs} ms: {timeout}"

private def await (operation : Async α) : IO α := do
  let task ← operation.toIO
  task.block

private def taskSelector (task : Task (Except IO.Error α)) : Selector (Except IO.Error α) := {
  tryFn := do
    if ← IO.hasFinished task then return some task.get
    else return none
  registerFn := fun waiter => do
    IO.chainTask task fun result =>
      waiter.race (pure ()) fun promise => promise.resolve (.ok result)
  unregisterFn := pure () }

private inductive ReceiveResult where
  | received (data : Option ByteArray)
  | timedOut

private def withTimeout (timeoutMs : Option Nat) (label : String) (operation : IO α) : IO α := do
  validateTimeoutMs timeoutMs
  let some timeoutMs := timeoutMs | operation
  let operationTask ← IO.asTask operation
  try
    let timer ← await (Selector.sleep (Std.Time.Millisecond.Offset.ofNat timeoutMs))
    let outcome ← await <| Selectable.one #[
      .case (taskSelector operationTask) fun value => pure (TimeoutResult.completed value),
      .case timer fun _ => pure TimeoutResult.timedOut ]
    match outcome with
    | .completed (.ok value) => return value
    | .completed (.error error) => throw error
    | .timedOut => throw <| ClientError.timeout s!"{label} timed out after {timeoutMs} ms"
  finally
    -- Native timer selection unregisters losing timers. Cancelling a task remains
    -- cooperative; socket owners must also shut down failed connections.
    IO.cancel operationTask

private def orThrow [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| ClientError.protocol (reprStr error)

def sendBytes (socket : Socket) (data : ByteArray) (_timeoutMs : Option Nat := none) : IO Unit :=
  await (socket.send data)

/-- One monotonic receive deadline, shared by fragments and stale responses. -/
def receiveDeadline (timeoutMs : Option Nat) : IO (Option Nat) := do
  validateTimeoutMs timeoutMs
  match timeoutMs with
  | none => return none
  | some timeout => return some ((← IO.monoMsNow) + timeout)

/-- Keep both an exchange's receive budget and a whole-transfer budget.
    `none` is an unbounded budget, not a fresh deadline. -/
def earlierReceiveDeadline (exchange transfer : Option Nat) : Option Nat :=
  match exchange, transfer with
  | none, other => other
  | other, none => other
  | some first, some second => some (min first second)

/-- Check before starting another exchange; this does not cancel socket sends
    or connection establishment already in progress. -/
def checkReceiveDeadline (deadline : Option Nat) : IO Unit := do
  if let some deadline := deadline then
    if (← IO.monoMsNow) ≥ deadline then
      throw <| ClientError.timeout "socket receive timed out: transfer deadline expired"

private def remainingReceiveTime (deadline : Option Nat) : IO (Option Nat) := do
  let some deadline := deadline | return none
  let now ← IO.monoMsNow
  if now ≥ deadline then
    throw <| ClientError.timeout "socket receive timed out: operation deadline expired"
  validateTimeoutMs (some (deadline - now))
  return some (deadline - now)

/-- Bound one connection stage by the remaining absolute monotonic budget.
    The deadline is checked again on completion. Task cancellation is cooperative;
    callers that own sockets must also shut them down on failure. -/
def withDeadline (deadline : Option Nat) (label : String) (operation : IO α) : IO α := do
  let result ← withTimeout (← remainingReceiveTime deadline) label operation
  discard <| remainingReceiveTime deadline
  return result

/-- Race an asynchronous native operation without creating a worker task that
    blocks on its promise. Cancellation remains cooperative, not a guarantee
    that the operating system operation itself has been cancelled. -/
private def awaitUntil (deadline : Option Nat) (label : String) (operation : Async α) : IO α := do
  let some timeoutMs ← remainingReceiveTime deadline | await operation
  let task ← operation.toIO
  try
    let timer ← await (Selector.sleep (Std.Time.Millisecond.Offset.ofNat timeoutMs))
    let outcome ← await <| Selectable.one #[
      .case (taskSelector task) fun value => pure (TimeoutResult.completed value),
      .case timer fun _ => pure TimeoutResult.timedOut ]
    match outcome with
    | .completed (.ok value) =>
        discard <| remainingReceiveTime deadline
        return value
    | .completed (.error error) => throw error
    | .timedOut => throw <| ClientError.timeout s!"{label} timed out after {timeoutMs} ms"
  finally
    IO.cancel task

private def receiveSome (socket : Socket) (count : Nat) (deadline : Option Nat) : IO (Option ByteArray) := do
  let timeoutMs ← remainingReceiveTime deadline
  let some timeoutMs := timeoutMs | await (socket.recv? count.toUInt64)
  let timer ← await (Selector.sleep (Std.Time.Millisecond.Offset.ofNat timeoutMs))
  let selected : Async ReceiveResult := Selectable.one #[
    .case (socket.recvSelector count.toUInt64) fun data => pure (ReceiveResult.received data),
    .case timer fun _ => pure ReceiveResult.timedOut
  ]
  match ← await selected with
  | .received data =>
      discard <| remainingReceiveTime deadline
      return data
  | .timedOut => throw <| ClientError.timeout s!"socket receive timed out after {timeoutMs} ms"

private def receiveExactUntil (socket : Socket) (count : Nat) (deadline : Option Nat) : IO ByteArray := do
  let mut result := ByteArray.empty
  while result.size < count do
    let some chunk ← receiveSome socket (count - result.size) deadline
      | throw <| ClientError.disconnected
          s!"connection closed with {count - result.size} bytes still expected"
    if chunk.size == 0 then
      throw <| ClientError.disconnected "socket returned an empty chunk before EOF"
    result := result ++ chunk
  return result

def receiveExact (socket : Socket) (count : Nat) (timeoutMs : Option Nat := none) : IO ByteArray := do
  receiveExactUntil socket count (← receiveDeadline timeoutMs)

def sendFrame (socket : Socket) (payload : ByteArray) (timeoutMs : Option Nat := none) : IO Unit := do
  let frame ← orThrow <| TPKT.encode { payload }
  sendBytes socket frame timeoutMs

private def receiveFrameUntil (socket : Socket) (deadline : Option Nat)
    (maxBodySize : Nat := TPKT.maxFrameSize - TPKT.headerSize)
    (bodyLimitDetail : String := "") : IO ByteArray := do
  let header ← receiveExactUntil socket TPKT.headerSize deadline
  let (version, _) ← orThrow <| (Cursor.readUInt8 { data := header })
  if version != TPKT.version then
    throw <| ClientError.protocol s!"unsupported TPKT version {version}"
  let cursor : Cursor := { data := header, offset := 2 }
  let (length, _) ← orThrow cursor.readUInt16BE
  if length.toNat < TPKT.minFrameSize then
    throw <| ClientError.protocol s!"invalid TPKT frame length {length}"
  if length.toNat - TPKT.headerSize > maxBodySize then
    throw <| ClientError.protocol s!"TPKT body exceeds receive limit {maxBodySize} {bodyLimitDetail}"
  let payload ← receiveExactUntil socket (length.toNat - TPKT.headerSize) deadline
  let frame ← orThrow <| TPKT.decode (header ++ payload)
  return frame.payload

def receiveFrame (socket : Socket) (timeoutMs : Option Nat := none) : IO ByteArray := do
  receiveFrameUntil socket (← receiveDeadline timeoutMs)

def sendData (socket : Socket) (payload : ByteArray) (timeoutMs : Option Nat := none) : IO Unit :=
  sendFrame socket (COTP.encodeData { payload }) timeoutMs

/-- Connection-handshake send with the same absolute budget as its reply. -/
def sendDataUntil (socket : Socket) (payload : ByteArray) (deadline : Option Nat) : IO Unit := do
  let frame ← orThrow <| TPKT.encode { payload := COTP.encodeData { payload } }
  awaitUntil deadline "S7 setup send" (socket.send frame)

private partial def receiveDataSegments (socket : Socket) (deadline : Option Nat)
    (maximum maxSegments : Nat) (state : COTP.Reassembly) : IO ByteArray := do
  if state.segments ≥ maxSegments then
    throw <| ClientError.protocol s!"COTP reassembly exceeds segment limit {maxSegments}"
  -- The supported class-0 DT header is exactly three bytes. Reject a declared
  -- over-budget body before awaiting it, rather than only after decoding it.
  let payload ← receiveFrameUntil socket deadline (maximum - state.payload.size + 3)
    s!"COTP reassembly exceeds payload limit {maximum}"
  let segment ← orThrow <| COTP.decodeData payload
  let (state, complete) ← orThrow <| state.pushResourceBounded segment maximum maxSegments
  if complete then
    return state.payload
  receiveDataSegments socket deadline maximum maxSegments state

/-- Receive one complete TSDU using an absolute `IO.monoMsNow` deadline.
    `none` disables the deadline; callers may reuse it while discarding stale PDUs.
    A separate finite segment budget still applies to empty and tiny fragments. -/
def receiveDataUntil (socket : Socket) (deadline : Option Nat)
    (maxPayloadSize : Nat := 65535) (maxSegments : Nat := 4096) : IO ByteArray :=
  receiveDataSegments socket deadline maxPayloadSize maxSegments {}

def receiveData (socket : Socket) (timeoutMs : Option Nat := none)
    (maxPayloadSize : Nat := 65535) (maxSegments : Nat := 4096) : IO ByteArray := do
  receiveDataUntil socket (← receiveDeadline timeoutMs) maxPayloadSize maxSegments

private def socketAddress (address : IPAddr) (port : UInt16) : SocketAddress :=
  match address with
  | .v4 address => SocketAddressV4.mk address port
  | .v6 address => SocketAddressV6.mk address port

/-- Resolver entries may repeat an endpoint for different socket/protocol kinds.
    Preserve candidate order without silently trying an identical peer twice. -/
def uniqueAddresses (addresses : Array SocketAddress) : Array SocketAddress :=
  addresses.foldl (init := #[]) fun selected address =>
    if selected.contains address then selected else selected.push address

def resolveUntil (endpoint : Endpoint) (port : UInt16) (deadline : Option Nat) : IO (Array SocketAddress) := do
  discard <| remainingReceiveTime deadline
  match endpoint with
  | .ipv4 address => return #[SocketAddressV4.mk address port]
  | .ipv6 address => return #[SocketAddressV6.mk address port]
  | .hostname name =>
      let addresses ← awaitUntil deadline "hostname resolution" <|
        DNS.getAddrInfo name (toString port)
      if addresses.isEmpty then
        throw <| IO.Error.noSuchThing none 0 s!"hostname {name} resolved to no addresses"
      return uniqueAddresses (addresses.map fun address => socketAddress address port)

def resolve (endpoint : Endpoint) (port : UInt16) (timeoutMs : Option Nat := none) : IO (Array SocketAddress) := do
  resolveUntil endpoint port (← receiveDeadline timeoutMs)

private def connectAddress (address : SocketAddress) (request : COTP.ConnectionRequest)
    (deadline : Option Nat) : IO Connection := do
  discard <| remainingReceiveTime deadline
  let socket ← TCP.Socket.Client.mk
  -- Unlike a `let mut` local, this must survive an exception inside `try`.
  let established ← IO.mkRef false
  try
    awaitUntil deadline "TCP connection" (socket.connect address)
    established.set true
    socket.noDelay
    let connectionRequest := COTP.encodeConnectionRequest request
    let frame ← orThrow <| TPKT.encode { payload := connectionRequest }
    awaitUntil deadline "COTP connection request" (socket.send frame)
    let confirmation ← orThrow <| COTP.decodeConnectionConfirm (← receiveFrameUntil socket deadline)
    let tpduSizeExponent ← orThrow <|
      COTP.negotiatedTpduSizeExponent request confirmation
    discard <| remainingReceiveTime deadline
    return {
      socket
      localReference := request.sourceReference
      remoteReference := confirmation.sourceReference
      tpduSizeExponent
    }
  catch error =>
    -- A failed TCP connect has no established write side to shut down.
    if ← established.get then
      try await socket.shutdown catch _ => pure ()
    throw error

private def connectAddresses (addresses : List SocketAddress) (request : COTP.ConnectionRequest)
    (deadline : Option Nat) : IO Connection := do
  match addresses with
  | [] => throw <| IO.Error.noSuchThing none 0 "could not connect to any resolved address"
  | address :: rest =>
      try connectAddress address request deadline
      catch error =>
        if rest.isEmpty || !isRetryableClientError error then throw error
        connectAddresses rest request deadline

/-- Deterministic candidate entry point for explicit address selection. All
    distinct candidates share one deadline. Transport failures permit fallback;
    malformed protocol responses do not. -/
def connectResolvedUntil (addresses : Array SocketAddress) (request : COTP.ConnectionRequest)
    (deadline : Option Nat) : IO Connection := do
  discard <| remainingReceiveTime deadline
  connectAddresses (uniqueAddresses addresses).toList request deadline

def connectResolved (addresses : Array SocketAddress) (request : COTP.ConnectionRequest)
    (timeoutMs : Option Nat := none) : IO Connection := do
  connectResolvedUntil addresses request (← receiveDeadline timeoutMs)

/-- Includes resolution, all TCP candidates, request send, and COTP confirmation
    in the same absolute connection budget. -/
def connectUntil (endpoint : Endpoint) (port : UInt16) (request : COTP.ConnectionRequest)
    (deadline : Option Nat) : IO Connection := do
  let addresses ← resolveUntil endpoint port deadline
  connectResolvedUntil addresses request deadline

def connect (endpoint : Endpoint) (port : UInt16) (request : COTP.ConnectionRequest)
    (timeoutMs : Option Nat := none) : IO Connection := do
  connectUntil endpoint port request (← receiveDeadline timeoutMs)

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
