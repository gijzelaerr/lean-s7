import LeanS7.S7
import LeanS7.ClientError

namespace LeanS7

structure WriteLocation where
  range : S7.MemoryRange
  /-- Original caller index for multi-item writes; scalar writes use `none`. -/
  itemIndex : Option Nat := none
  /-- Byte offset within the original logical payload, not an element offset. -/
  chunkByteOffset : Nat := 0
  deriving Repr, BEq

inductive WriteAttemptOutcome where
  | pending
  | itemResult (result : S7.WriteItemResult)
  | globalRejected
  | replayedUnknown
  deriving Repr, BEq

structure WriteAttempt where
  location : WriteLocation
  outcome : WriteAttemptOutcome := .pending
  deriving Repr, BEq

/-- One wire write, not necessarily one entire caller item. Ranges retain the
    address and element count; a successful prefix is never an atomic commit. -/
structure WriteAcknowledgement where
  range : S7.MemoryRange
  result : S7.WriteItemResult
  itemIndex : Option Nat := none
  chunkByteOffset : Nat := 0
  deriving Repr

structure WriteProgress where
  /-- Chronological per-wire-item attempts, preserving caller identity even for
      duplicate ranges. A replay produces a new entry at the same location. -/
  attempts : Array WriteAttempt := #[]
  acknowledged : Array WriteAcknowledgement := #[]
  /-- Scalar/global PLC rejections for which no per-item code is available. -/
  rejected : Array S7.MemoryRange := #[]
  /-- Earlier unacknowledged attempts preceding an explicitly permitted replay.
      A later acknowledgement or rejection cannot establish whether these earlier
      attempts changed the PLC. Repeated ranges retain repeated uncertain attempts. -/
  replayedUncertain : Array S7.MemoryRange := #[]
  /-- These requests may have reached the PLC but have no validated item result.
      This is uncertainty, not evidence of either success or rollback. -/
  uncertain : Array S7.MemoryRange := #[]
  deriving Repr

/-- Completed attempts are accumulated in reverse order with O(batch-size)
    work per exchange. Public arrays are materialized once at the boundary. -/
structure WriteProgress.State where
  history : List WriteAttempt := []
  pending : Array WriteLocation := #[]

def WriteProgress.State.sent (state : State) (locations : Array WriteLocation) :
    Except DecodeError State :=
  if !state.pending.isEmpty || locations.isEmpty then
    .error (.invalidField 0 "write progress cannot start an empty or overlapping attempt")
  else .ok { state with pending := locations }

private def WriteProgress.State.finish (state : State) (outcome : WriteAttemptOutcome) : State :=
  { history := (state.pending.map fun location => { location, outcome }).toList.reverse ++ state.history }

def WriteProgress.State.replay (state : State) : State := state.finish .replayedUnknown

def WriteProgress.State.globalReject (state : State) : State := state.finish .globalRejected

/-- The count must match exactly; errors do not silently clear uncertainty. -/
def WriteProgress.State.acknowledge (state : State) (results : Array S7.WriteItemResult) :
    Except DecodeError State :=
  if results.size != state.pending.size then
    .error (.invalidField 0 "write progress acknowledgement count differs from outstanding items")
  else .ok { history := ((state.pending.zip results).map fun (location, result) =>
    { location, outcome := .itemResult result }).toList.reverse ++ state.history }

def WriteProgress.State.trace (state : State) : Array WriteAttempt :=
  state.history.reverse.toArray ++ state.pending.map (fun location => { location })

def WriteProgress.State.snapshot (state : State) : WriteProgress := Id.run do
  let attempts := state.trace
  let mut progress : WriteProgress := { attempts }
  for attempt in attempts do
    match attempt.outcome with
    | .pending => progress := { progress with uncertain := progress.uncertain.push attempt.location.range }
    | .replayedUnknown =>
        progress := { progress with replayedUncertain := progress.replayedUncertain.push attempt.location.range }
    | .globalRejected =>
        progress := { progress with rejected := progress.rejected.push attempt.location.range }
    | .itemResult result =>
        progress := { progress with acknowledged := progress.acknowledged.push {
          range := attempt.location.range, result
          itemIndex := attempt.location.itemIndex
          chunkByteOffset := attempt.location.chunkByteOffset } }
  return progress

theorem WriteProgress.State.sent_preserves_history (state after : State) (locations : Array WriteLocation)
    (h : state.sent locations = .ok after) : after.history = state.history := by
  unfold sent at h
  split at h
  · contradiction
  · cases h; rfl

theorem WriteProgress.State.replay_history_locations (state : State) :
    state.replay.history.map (·.location) =
      state.pending.toList.reverse ++ state.history.map (·.location) := by
  simp [replay, finish, List.map_append, List.map_reverse, Array.toList_map, List.map_map,
    Function.comp_def]

theorem WriteProgress.State.acknowledge_order (state after : State)
    (results : Array S7.WriteItemResult) (h : state.acknowledge results = .ok after) :
    after.history = ((state.pending.zip results).map fun (location, result) =>
      { location, outcome := WriteAttemptOutcome.itemResult result }).toList.reverse ++ state.history := by
  unfold acknowledge at h
  split at h
  · contradiction
  · cases h; rfl

theorem WriteProgress.State.acknowledge_count (state after : State)
    (results : Array S7.WriteItemResult) (h : state.acknowledge results = .ok after) :
    results.size = state.pending.size := by
  by_cases heq : results.size = state.pending.size
  · exact heq
  · simp [acknowledge, heq] at h

structure WriteFailure where
  error : IO.Error
  progress : WriteProgress

def WriteFailure.kind (failure : WriteFailure) : ClientErrorKind :=
  classifyClientError failure.error

end LeanS7
