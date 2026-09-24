import Lean.Data.Json
import LeanS7.Lifecycle
import LeanS7.RetryPolicy
import LeanS7.WriteProgress

namespace LeanS7.Conformance.Sessions
open Lean

/-- Single-wire operational histories with observed reconnect stages. This is
    not a formal equivalence theorem about Client IO, scheduling, or PLC effects. -/
structure Config where
  write : Bool
  allow : Bool
  budget : Nat
  reference : UInt16
  locations : Array WriteLocation

inductive Event where
  | begin | send | reconnectSetup | reconnected | disconnect
  | failure (kind : ClientErrorKind)
  | response (pdu : ByteArray)

structure State where
  lifecycle : Lifecycle.State := .connected
  remaining : Nat := 0
  active : Option UInt16 := none
  phase : String := "idle"
  sends : Nat := 0
  progress : WriteProgress.State := {}

structure Case where
  id : String
  seed : Nat
  config : Config
  events : Array Event

private def kindName : ClientErrorKind → String
  | .invalidInput => "invalid-input" | .protocol => "protocol"
  | .plcRejected => "plc-rejected" | .timeout => "timeout"
  | .disconnected => "disconnected" | .lifecycle => "lifecycle"
  | .transport => "transport" | .other => "other"
private def stateName : Lifecycle.State → String
  | .connected => "connected" | .disconnected => "disconnected" | .closed => "closed"
private def octets (data : ByteArray) : Json := toJson (data.toList.map UInt8.toNat)
private def locationJson (location : WriteLocation) : Json := Json.mkObj [
  ("range", Json.mkObj [("db_number", toJson location.range.dbNumber.toNat),
    ("start", toJson location.range.start), ("count", toJson location.range.count)]),
  ("item_index", toJson location.itemIndex),
  ("chunk_byte_offset", toJson location.chunkByteOffset)]
private def outcomeName : WriteAttemptOutcome → String
  | .pending => "pending" | .replayedUnknown => "replayed-unknown"
  | .globalRejected => "global-rejected" | .itemResult .success => "success"
  | .itemResult (.failure code) => s!"failure:{code.toNat}"
private def snapshot (state : State) : Json := Json.mkObj [
  ("lifecycle", toJson (stateName state.lifecycle)),
  ("remaining", toJson state.remaining), ("active_reference", toJson (state.active.map UInt16.toNat)),
  ("phase", toJson state.phase), ("sends", toJson state.sends),
  ("attempts", Json.arr (state.progress.trace.map fun attempt => Json.mkObj [
    ("location", locationJson attempt.location), ("outcome", toJson (outcomeName attempt.outcome))]))]
private def accepted : Json := Json.mkObj [("status", "accept")]
private def rejected (category : String) : Json := Json.mkObj [
  ("status", "reject"), ("category", toJson category)]
private def payload (location : WriteLocation) : ByteArray :=
  ByteArray.mk ((Array.range location.range.count).map fun index =>
    UInt8.ofNat (location.range.start * 7 + index * 29))
private def request (config : Config) : Except S7.EncodeError ByteArray :=
  if config.write then S7.encodeAreaWriteMany config.reference
    (config.locations.map fun location => { range := location.range, payload := payload location })
  else S7.encodeAreaReadMany config.reference (config.locations.map (·.range))

private def failure (config : Config) (state : State) (kind : ClientErrorKind) : State × Json :=
  match retryBudgetAfter state.remaining (state.lifecycle == .closed) kind
      (if config.write then .potentiallyMutating else .readOnly) config.allow with
  | some remaining =>
    ({ state with
       remaining, lifecycle := .disconnected, phase := "reconnect-cotp",
       progress := if config.write && state.phase == "awaiting" then state.progress.replay else state.progress },
     Json.mkObj [("status", "accept"), ("retry", true)])
  | none =>
    ({ state with
       lifecycle := .disconnected, active := none, phase := "failed",
       progress := if config.write && kind == .plcRejected && state.phase == "awaiting"
         then state.progress.globalReject else state.progress },
     Json.mkObj [("status", "accept"), ("retry", false)])

private def step (config : Config) (state : State) (event : Event) : State × Json := Id.run do
  match event with
  | .begin =>
      if state.lifecycle != .connected then return (state, rejected "not-connected")
      if state.active.isSome then return (state, rejected "already-active")
      let .ok _ := request config | return (state, rejected "request-codec")
      return ({ state with
        remaining := config.budget, active := some config.reference,
        phase := "ready", sends := 0, progress := {} }, accepted)
  | .send =>
      if state.lifecycle != .connected || state.active.isNone || state.phase != "ready" then
        return (state, rejected "send-phase")
      let .ok progress := if config.write then state.progress.sent config.locations else .ok state.progress
        | return (state, rejected "write-progress")
      return ({ state with sends := state.sends + 1, phase := "awaiting", progress }, accepted)
  | .failure kind =>
      if state.active.isNone || !["awaiting", "reconnect-cotp", "reconnect-setup"].contains state.phase then
        return (state, rejected "failure-phase")
      return failure config state kind
  | .reconnectSetup =>
      if state.active.isNone || state.phase != "reconnect-cotp" then
        return (state, rejected "reconnect-phase")
      return ({ state with phase := "reconnect-setup" }, accepted)
  | .reconnected =>
      if state.active.isNone || state.phase != "reconnect-setup" || state.lifecycle != .disconnected then
        return (state, rejected "reconnect-phase")
      return ({ state with lifecycle := .connected, phase := "ready" }, accepted)
  | .response packet =>
      if state.lifecycle != .connected || state.active.isNone || state.phase != "awaiting" then
        return (state, rejected "response-phase")
      let decoded : Except DecodeError (Array S7.WriteItemResult) := do
        let response ← S7.decodeResponse packet
        if config.write then S7.decodeAreaWriteMany config.reference config.locations.size response
        else do
          discard <| S7.decodeAreaReadMany config.reference (config.locations.map (·.range)) response
          return #[]
      match decoded with
      | .error error =>
        let kind := match error with | .remoteFailure .. => ClientErrorKind.plcRejected | _ => .protocol
        let (next, _) := failure config state kind
        return (next, rejected "response-codec")
      | .ok results =>
        let .ok progress := if config.write then state.progress.acknowledge results else .ok state.progress
          | return (state, rejected "write-progress")
        return ({ state with active := none, phase := "completed", progress }, accepted)
  | .disconnect =>
      return ({ state with lifecycle := .closed, active := none, phase := "closed" }, accepted)

private def eventJson : Event → Json
  | .begin => Json.mkObj [("operation", "begin")]
  | .send => Json.mkObj [("operation", "send")]
  | .reconnectSetup => Json.mkObj [("operation", "reconnect-setup")]
  | .reconnected => Json.mkObj [("operation", "reconnected")]
  | .disconnect => Json.mkObj [("operation", "disconnect")]
  | .failure kind => Json.mkObj [("operation", "failure"), ("error_kind", toJson (kindName kind))]
  | .response packet => Json.mkObj [("operation", "response"), ("response_pdu", octets packet)]
private def run (test : Case) : Array Json := Id.run do
  let mut state : State := {}
  let mut trace := #[]
  for event in test.events do
    let (next, result) := step test.config state event
    state := next
    trace := trace.push (Json.mkObj [("result", result), ("snapshot", snapshot state)])
  return trace

private def response (config : Config) (reference : UInt16) (count : Nat) : ByteArray :=
  let data := if config.write then bytes ((Array.range config.locations.size).map fun _ => 255)
    else Id.run do
      let mut data := ByteArray.empty
      for index in [:config.locations.size] do
        let some location := config.locations[index]? | continue
        let content := payload location
        data := data ++ bytes #[255,4] ++ uint16BE (UInt16.ofNat (content.size * 8)) ++ content
        if index + 1 < config.locations.size && content.size % 2 == 1 then data := data.push 0
      return data
  match S7.encodeAckData reference (bytes #[if config.write then 5 else 4, UInt8.ofNat count]) data with
  | .ok packet => packet | .error _ => ByteArray.empty

private def casesFor (seed : Nat) : Array Case := Id.run do
  let first : WriteLocation := {
    range := { area := .dataBlocks, dbNumber := UInt16.ofNat (1 + seed % 3), start := seed % 64, count := 1 + seed % 3 }
    itemIndex := some 0 }
  let second : WriteLocation := { first with
    itemIndex := some 1,
    range := { first.range with start := first.range.start + 16 } }
  let config : Config := {
    write := false, allow := false, budget := seed % 3,
    reference := UInt16.ofNat (65535 + seed % 2), locations := #[first,second] }
  let endEvents := #[Event.disconnect, .begin, .send, .failure .timeout, .reconnectSetup, .reconnected]
  let mk := fun name cfg events => ({
    id := s!"{name}-seed-{seed}", seed, config := cfg,
    events := events ++ endEvents } : Case)
  let recovery := fun cfg => #[Event.reconnectSetup, .reconnected, .send,
    .response (response cfg cfg.reference cfg.locations.size)]
  let start := #[Event.begin, .begin, .send]
  let write := { config with write := true, allow := true, budget := 1 + seed % 2 }
  let noOpt := { write with allow := false, budget := 2 }
  let repeated := { write with budget := 2 }
  let malformed := { write with budget := 2 }
  let malformedPacket := response malformed
    (if seed % 2 == 0 then malformed.reference + 1 else malformed.reference)
    (if seed % 2 == 0 then malformed.locations.size else malformed.locations.size + 1)
  let mut exhaustEvents := start
  for index in [:config.budget + 1] do
    if index > 0 then exhaustEvents := exhaustEvents.push .reconnectSetup
    exhaustEvents := exhaustEvents.push (.failure .timeout)
  return #[
    mk "read-retry" config (start ++ #[.failure .disconnected] ++
      (if config.budget > 0 then recovery config else #[.begin, .send, .reconnected])),
    mk "write-opt-in" write (start ++ #[.failure .transport] ++ recovery write),
    mk "write-no-opt-in" noOpt (start ++ #[.failure .disconnected, .begin, .send]),
    mk "reconnect-before-resend" repeated (start ++ #[.failure .disconnected,
      .failure .transport, .reconnectSetup, .failure .disconnected, .begin, .send]),
    mk "malformed-ack" malformed (start ++ #[.response malformedPacket, .begin, .send]),
    mk "exhaustion" config (exhaustEvents ++ #[.begin, .send])]

def cases : Array Case := (#[7,2026,65535,23063]).flatMap casesFor

def validate : IO Unit := do
  unless cases.size == 24 do throw <| IO.userError "session case coverage changed"
  for test in cases do
    let .ok _ := request test.config | throw <| IO.userError s!"session request encoding {test.id}"
    let mut state : State := {}
    for event in test.events do
      let (next, _) := step test.config state event
      unless next.remaining <= test.config.budget do throw <| IO.userError "session budget grew"
      if state.active.isSome && next.remaining > state.remaining then
        throw <| IO.userError "active session replenished retry allowance"
      if state.lifecycle == .closed && next.lifecycle != .closed then
        throw <| IO.userError "closed session resurrected"
      state := next
    unless state.lifecycle == .closed && state.active.isNone do
      throw <| IO.userError s!"session terminal state {test.id}"
  -- Fixed model controls: failed reconnects consume allowance without sends or
  -- new write attempts; a later valid response cannot remove earlier uncertainty.
  let some test := (casesFor 7)[3]? | throw <| IO.userError "missing fixed session control"
  let mut state : State := {}
  for event in test.events[:9] do state := (step test.config state event).1
  unless state.remaining == 0 && state.sends == 1 && state.active.isNone &&
      state.phase == "failed" && state.progress.trace.size == 2 &&
      state.progress.snapshot.replayedUncertain.size == 2 do
    throw <| IO.userError "failed reconnect manufactured write attempts"
  let some recovered := (casesFor 7)[1]? | throw <| IO.userError "missing fixed replay control"
  let mut successState : State := {}
  for event in recovered.events[:8] do successState := (step recovered.config successState event).1
  unless successState.phase == "completed" && successState.active.isNone &&
      successState.sends == 2 && successState.progress.trace.size == 4 &&
      successState.progress.snapshot.replayedUncertain.size == 2 &&
      successState.progress.snapshot.acknowledged.size == 2 do
    throw <| IO.userError "successful replay erased uncertainty"

def corpus : Json := Json.mkObj [
  ("schema_version", 1), ("protocol", "classic S7 active request histories"),
  ("cases", Json.arr (cases.map fun test => Json.mkObj [
    ("id", toJson test.id), ("seed", toJson test.seed),
    ("config", Json.mkObj [("write", toJson test.config.write),
      ("safety", toJson (if test.config.write then "potentially-mutating" else "read-only")),
      ("allow_potentially_mutating", toJson test.config.allow),
      ("budget", toJson test.config.budget), ("reference", toJson test.config.reference.toNat),
      ("locations", Json.arr (test.config.locations.map locationJson)),
      ("request_pdu", match request test.config with | .ok packet => octets packet | .error _ => Json.null)]),
    ("events", Json.arr (test.events.map eventJson)), ("expected_trace", Json.arr (run test))]))]

end LeanS7.Conformance.Sessions
