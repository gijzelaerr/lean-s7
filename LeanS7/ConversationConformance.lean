import Lean.Data.Json
import LeanS7.Lifecycle
import LeanS7.RetryPolicy
import LeanS7.WriteProgress

namespace LeanS7.Conformance.Conversations
open Lean

/-- Portable primitive-level histories, not a formal model of networking or
    scheduler behavior. Wire exchanges use the actual classic S7 codecs. -/
inductive Event where
  | lifecycle (event : Lifecycle.Event)
  | retry (safety : RetrySafety) (allow : Bool) (kind : ClientErrorKind) (remaining : Nat)
  | send (reference : UInt16) (locations : Array WriteLocation)
  | acknowledge (reference : UInt16) (count : Nat) (codes : Array UInt8)
  | read (reference : UInt16) (range : S7.MemoryRange) (payload : ByteArray)

structure State where
  lifecycle : Lifecycle.State := .connected
  progress : WriteProgress.State := {}
  pendingReference : Option UInt16 := none

structure Case where
  id : String
  seed : Nat
  events : Array Event

private def stateName : Lifecycle.State → String
  | .connected => "connected"
  | .disconnected => "disconnected"
  | .closed => "closed"
private def lifecycleName : Lifecycle.Event → String
  | .transportClosed => "transport-closed"
  | .reconnected => "reconnected"
  | .disconnect => "disconnect"
private def kindName : ClientErrorKind → String
  | .invalidInput => "invalid-input"
  | .protocol => "protocol"
  | .plcRejected => "plc-rejected"
  | .timeout => "timeout"
  | .disconnected => "disconnected"
  | .lifecycle => "lifecycle"
  | .transport => "transport"
  | .other => "other"
private def errorOfKind : ClientErrorKind → IO.Error
  | .invalidInput => ClientError.invalidInput "corpus"
  | .protocol => ClientError.protocol "corpus"
  | .plcRejected => ClientError.plcRejected "corpus"
  | .timeout => ClientError.timeout "corpus"
  | .disconnected => ClientError.disconnected "corpus"
  | .lifecycle => ClientError.lifecycle "corpus"
  | .transport => .otherError 0 "corpus"
  | .other => .userError "corpus"
private def octets (data : ByteArray) : Json := toJson (data.toList.map UInt8.toNat)
private def rangeJson (range : S7.MemoryRange) : Json := Json.mkObj [
  ("db_number", toJson range.dbNumber.toNat), ("start", toJson range.start),
  ("count", toJson range.count)]
private def locationJson (location : WriteLocation) : Json := Json.mkObj [
  ("range", rangeJson location.range), ("item_index", toJson location.itemIndex),
  ("chunk_byte_offset", toJson location.chunkByteOffset)]
private def outcomeName : WriteAttemptOutcome → String
  | .pending => "pending"
  | .replayedUnknown => "replayed-unknown"
  | .globalRejected => "global-rejected"
  | .itemResult .success => "success"
  | .itemResult (.failure code) => s!"failure:{code.toNat}"
private def snapshot (state : State) : Json := Json.mkObj [
  ("lifecycle", toJson (stateName state.lifecycle)),
  ("attempts", Json.arr (state.progress.trace.map fun attempt => Json.mkObj [
    ("location", locationJson attempt.location), ("outcome", toJson (outcomeName attempt.outcome))]))]
private def accept : Json := Json.mkObj [("status", "accept")]
private def reject (category : String) : Json :=
  Json.mkObj [("status", "reject"), ("category", toJson category)]

private def payload (location : WriteLocation) : ByteArray :=
  ByteArray.mk ((Array.range location.range.count).map fun index =>
    UInt8.ofNat (location.range.start * 7 + index * 29))
private def request (reference : UInt16) (locations : Array WriteLocation) :
    Except S7.EncodeError ByteArray :=
  S7.encodeAreaWriteMany reference (locations.map fun location =>
    { range := location.range, payload := payload location })
private def acknowledgement (reference : UInt16) (count : Nat) (codes : Array UInt8) :
    Except S7.EncodeError ByteArray :=
  S7.encodeAckData reference (bytes #[5, UInt8.ofNat count]) (bytes codes)
private def readResponse (reference : UInt16) (data : ByteArray) : Except S7.EncodeError ByteArray :=
  S7.encodeAckData reference (bytes #[4, 1])
    (bytes #[255,4] ++ uint16BE (UInt16.ofNat (data.size * 8)) ++ data)

private def step (state : State) (event : Event) : State × Json := Id.run do
  match event with
  | .lifecycle event =>
      match Lifecycle.transition state.lifecycle event with
      | some next => return ({ state with lifecycle := next }, accept)
      | none => return (state, reject "lifecycle-transition")
  | .retry safety allow kind remaining =>
      let permitted := state.lifecycle != .closed && remaining > 0 &&
        isRetryableClientError (errorOfKind kind) && retryPermitted safety allow
      let next := if permitted && safety == .potentiallyMutating then
        { state with progress := state.progress.replay, pendingReference := none } else state
      return (next, Json.mkObj [("status", "accept"), ("permitted", toJson permitted)])
  | .send reference locations =>
      if state.lifecycle != .connected then return (state, reject "not-connected")
      let .ok _ := request reference locations | return (state, reject "request-codec")
      match state.progress.sent locations with
      | .ok next => return ({ state with progress := next, pendingReference := some reference }, accept)
      | .error _ => return (state, reject "write-progress")
  | .acknowledge reference count codes =>
      if state.lifecycle != .connected then return (state, reject "not-connected")
      let decoded : Except DecodeError (Array S7.WriteItemResult) := do
        let .ok packet := acknowledgement reference count codes
          | throw (.invalidField 0 "corpus ACK encoding")
        let response ← S7.decodeResponse packet
        S7.decodeAreaWriteMany (state.pendingReference.getD reference) state.progress.pending.size response
      let .ok results := decoded | return (state, reject "response-codec")
      match state.progress.acknowledge results with
      | .ok next => return ({ state with progress := next, pendingReference := none }, accept)
      | .error _ => return (state, reject "write-progress")
  | .read reference range data =>
      if state.lifecycle != .connected then return (state, reject "not-connected")
      if !state.progress.pending.isEmpty then return (state, reject "write-pending")
      let .ok _ := S7.encodeAreaReadMany reference #[range]
        | return (state, reject "request-codec")
      let decoded : Except DecodeError (Array S7.ReadItemResult) := do
        let .ok packet := readResponse reference data
          | throw (.invalidField 0 "corpus read encoding")
        let response ← S7.decodeResponse packet
        S7.decodeAreaReadMany reference #[range] response
      match decoded with
      | .ok _ => return (state, Json.mkObj [("status", "accept"), ("payload", octets data)])
      | .error _ => return (state, reject "response-codec")

private def wireJson (result : Except S7.EncodeError ByteArray) : Json :=
  match result with | .ok data => octets data | .error _ => Json.null
private def eventJson : Event → Json
  | .lifecycle event => Json.mkObj [("operation", "lifecycle"), ("event", toJson (lifecycleName event))]
  | .retry safety allow kind remaining => Json.mkObj [
      ("operation", "retry"), ("safety", toJson (if safety == .readOnly then "read-only" else "potentially-mutating")),
      ("allow_potentially_mutating", toJson allow), ("error_kind", toJson (kindName kind)),
      ("remaining", toJson remaining)]
  | .send reference locations => Json.mkObj [
      ("operation", "send"), ("reference", toJson reference.toNat),
      ("locations", Json.arr (locations.map locationJson)), ("request_pdu", wireJson (request reference locations))]
  | .acknowledge reference count codes => Json.mkObj [
      ("operation", "acknowledge"), ("reference", toJson reference.toNat),
      ("count", toJson count), ("codes", toJson (codes.map UInt8.toNat)),
      ("response_pdu", wireJson (acknowledgement reference count codes))]
  | .read reference range data => Json.mkObj [
      ("operation", "read"), ("reference", toJson reference.toNat), ("range", rangeJson range),
      ("payload", octets data), ("request_pdu", wireJson (S7.encodeAreaReadMany reference #[range])),
      ("response_pdu", wireJson (readResponse reference data))]

private def run (test : Case) : Array Json := Id.run do
  let mut state : State := {}
  let mut trace := #[]
  for event in test.events do
    let (next, result) := step state event
    state := next
    trace := trace.push (Json.mkObj [("result", result), ("snapshot", snapshot state)])
  return trace

private def casesFor (seed : Nat) : Array Case := Id.run do
  let range : S7.MemoryRange := {
    area := .dataBlocks
    dbNumber := 1
    start := seed % 64
    count := 1 + seed % 3 }
  let first : WriteLocation := { range, itemIndex := some 0 }
  let duplicate : WriteLocation := { range, itemIndex := some 1 }
  let chunk : WriteLocation := {
    range := { range with start := range.start + 212 }
    itemIndex := some 0
    chunkByteOffset := 212 }
  let reference := UInt16.ofNat (65534 + seed % 2)
  let nextReference := reference + 1
  let read := Event.read reference range (payload first)
  let send := Event.send reference #[first,duplicate]
  let acknowledge := Event.acknowledge reference 2 #[255,5]
  let closed := #[Event.lifecycle .disconnect, .read nextReference range (payload first),
    .lifecycle .reconnected]
  let mk := fun name events => ({ id := s!"{name}-seed-{seed}", seed, events } : Case)
  return #[
    mk "read-retry" (#[.lifecycle .transportClosed, .retry .readOnly false .timeout 1,
      .lifecycle .reconnected, read] ++ closed),
    mk "write-no-replay" (#[send, .lifecycle .transportClosed,
      .retry .potentiallyMutating false .disconnected 1, .lifecycle .disconnect,
      acknowledge, .retry .potentiallyMutating true .timeout 2]),
    mk "write-opt-in-replay" (#[send, .lifecycle .transportClosed,
      .retry .potentiallyMutating true .transport 1, .lifecycle .reconnected,
      send, acknowledge, read] ++ closed),
    mk "chunk-prefix-uncertain" (#[.send reference #[first], .acknowledge reference 1 #[255],
      .send nextReference #[chunk], .lifecycle .transportClosed,
      .retry .potentiallyMutating false .timeout 1, .lifecycle .disconnect]),
    mk "malformed-ack" (#[send, .acknowledge reference 2 #[255],
      .acknowledge nextReference 2 #[255,255],
      .lifecycle .transportClosed, .retry .potentiallyMutating true .protocol 1,
      .lifecycle .disconnect]),
    mk "duplicate-write-order" (#[send, acknowledge, .send nextReference #[duplicate,first],
      .acknowledge nextReference 2 #[3,255], read] ++ closed),
    mk "illegal-progress" (#[.send reference #[], send, .send nextReference #[chunk],
      .acknowledge reference 1 #[255], acknowledge] ++ closed),
    mk "retry-gates" (#[.retry .readOnly false .plcRejected 1, .retry .readOnly false .invalidInput 1,
      .retry .readOnly false .lifecycle 1, .retry .readOnly false .other 1,
      .retry .readOnly false .timeout 0, .retry .readOnly false .transport 2,
      .lifecycle .reconnected, .read reference range ByteArray.empty, read] ++ closed)
  ]

def cases : Array Case := (#[7,2026,65535,23063]).flatMap casesFor

def validate : IO Unit := do
  unless cases.size == 32 do throw <| IO.userError "conversation case coverage changed"
  for test in cases do
    let trace := run test
    unless trace.size == test.events.size do throw <| IO.userError s!"conversation trace omitted event: {test.id}"
    let mut state : State := {}
    for event in test.events do
      let (next, _) := step state event
      if state.lifecycle == .closed && next.lifecycle != .closed then
        throw <| IO.userError s!"conversation resurrected closed state: {test.id}"
      state := next
    unless state.lifecycle == .closed do throw <| IO.userError s!"conversation lacks terminal observation: {test.id}"
  let location : WriteLocation := { range := { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 } }
  let (after, _) := step {} (.send 1 #[location,location])
  let (disconnected, _) := step after (.lifecycle .transportClosed)
  let (noReplay, decision) := step disconnected (.retry .potentiallyMutating false .disconnected 1)
  unless noReplay.progress.trace.size == 2 && decision ==
      Json.mkObj [("status", "accept"), ("permitted", false)] do
    throw <| IO.userError "conversation conservative replay control differs"

def corpus : Json := Json.mkObj [
  ("schema_version", 1), ("protocol", "classic S7 primitive conversation histories"),
  ("cases", Json.arr (cases.map fun test => Json.mkObj [
    ("id", toJson test.id), ("seed", toJson test.seed),
    ("events", Json.arr (test.events.map eventJson)), ("expected_trace", Json.arr (run test))]))]

end LeanS7.Conformance.Conversations
