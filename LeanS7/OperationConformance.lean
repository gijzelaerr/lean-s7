import Lean.Data.Json
import LeanS7.Management
import LeanS7.Value
import LeanS7.RetryPolicy
import LeanS7.WriteProgress

namespace LeanS7.Conformance.Operations
open Lean

private def octets (data : ByteArray) : Json := toJson (data.toList.map UInt8.toNat)
private def reject (category : String) : Json :=
  Json.mkObj [("status", "reject"), ("category", toJson category)]
private def accepted (value : String) : Json :=
  Json.mkObj [("status", "accept"), ("value", toJson value)]

structure StringCase where
  id : String
  wide : Bool
  header : ByteArray
  body : ByteArray
  expected : Json

def stringCases : Array StringCase := #[
  ⟨"string-capacity-stable", false, bytes #[3,1], bytes #[3,1,65,0,0], accepted "A"⟩,
  ⟨"string-current-length-update", false, bytes #[3,1], bytes #[3,2,65,66,0], accepted "AB"⟩,
  ⟨"string-capacity-shrinks", false, bytes #[3,1], bytes #[2,1,65,0,0], reject "capacity-changed"⟩,
  ⟨"string-capacity-grows", false, bytes #[3,1], bytes #[4,1,65,0,0], reject "capacity-changed"⟩,
  ⟨"string-invalid-initial-current", false, bytes #[3,4], bytes #[3,1,65,0,0], reject "initial-header"⟩,
  ⟨"string-invalid-body-current", false, bytes #[3,1], bytes #[3,4,65,0,0], reject "value-codec"⟩,
  ⟨"wstring-capacity-stable", true, bytes #[0,2,0,1], bytes #[0,2,0,1,0,65,0,0], accepted "A"⟩,
  ⟨"wstring-current-length-update", true, bytes #[0,2,0,1], bytes #[0,2,0,2,0,65,0,66], accepted "AB"⟩,
  ⟨"wstring-capacity-shrinks", true, bytes #[0,2,0,1], bytes #[0,1,0,1,0,65,0,0], reject "capacity-changed"⟩,
  ⟨"wstring-capacity-grows", true, bytes #[0,2,0,1], bytes #[0,3,0,1,0,65,0,0], reject "capacity-changed"⟩,
  ⟨"wstring-invalid-initial-current", true, bytes #[0,2,0,3], bytes #[0,2,0,1,0,65,0,0], reject "initial-header"⟩,
  ⟨"wstring-unpaired-surrogate", true, bytes #[0,2,0,1], bytes #[0,2,0,1,216,0,0,0], reject "value-codec"⟩
]

/-- Pure mirror of the client's two-read guard, using the actual value codecs.
    IO serialization, deadlines, and retry behavior are outside this model. -/
private def stringResult (test : StringCase) : Json := Id.run do
  let headerSize := if test.wide then 4 else 2
  let readLength := fun (data : ByteArray) (offset : Nat) =>
    if test.wide then (Value.getUInt16 data offset).map UInt16.toNat
    else (Value.getUInt8 data offset).map UInt8.toNat
  let .ok maximum := readLength test.header 0 | return reject "initial-header"
  let .ok current := readLength test.header (headerSize / 2) | return reject "initial-header"
  let limit := if test.wide then Value.maxWStringLength else Value.maxStringLength
  if maximum > limit || current > maximum then return reject "initial-header"
  let .ok bodyMaximum := readLength test.body 0 | return reject "body-header"
  if bodyMaximum != maximum then return reject "capacity-changed"
  let result := if test.wide then Value.decodeWString test.body else Value.decodeString test.body
  match result with
  | .ok value => return accepted value
  | .error _ => return reject "value-codec"

structure UserDataCase where
  id : String
  group : UInt8
  subfunction : UInt8
  continuation : UInt8
  payload : ByteArray
  expected : Json

private def acceptedPayload (payload : ByteArray) : Json :=
  Json.mkObj [("status", "accept"), ("payload", octets payload)]

def userDataCases : Array UserDataCase := #[
  ⟨"clock-complete", 7,1,0,bytes #[0,1], acceptedPayload (bytes #[0,1])⟩,
  ⟨"clock-incomplete", 7,1,1,bytes #[0,1], reject "incomplete-single-response"⟩,
  ⟨"set-clock-incomplete", 7,2,1,ByteArray.empty, reject "incomplete-single-response"⟩,
  ⟨"set-password-incomplete", 5,1,1,ByteArray.empty, reject "incomplete-single-response"⟩,
  ⟨"clear-password-incomplete", 5,2,1,ByteArray.empty, reject "incomplete-single-response"⟩,
  ⟨"block-info-incomplete", 3,3,1,bytes #[0,1], reject "incomplete-single-response"⟩,
  ⟨"invalid-continuation-discriminator", 7,1,2,ByteArray.empty, reject "pdu-validation"⟩,
  ⟨"empty-complete-ack", 5,2,0,ByteArray.empty, acceptedPayload ByteArray.empty⟩
]

private def userDataPacket (test : UserDataCase) : ByteArray :=
  let params := bytes #[0,1,0x12,8,0x12,0x80 + test.group,test.subfunction,0,0,test.continuation,0,0]
  let data := bytes #[255,9] ++ uint16BE (UInt16.ofNat test.payload.size) ++ test.payload
  bytes #[0x32,7,0,0,0,1] ++ uint16BE 12 ++ uint16BE (UInt16.ofNat data.size) ++ params ++ data

private def userDataResult (test : UserDataCase) : Json :=
  match S7.decodeUserDataResponse 1 test.group test.subfunction (userDataPacket test) with
  | .error _ => reject "pdu-validation"
  | .ok response => match S7.requireCompleteUserData response with
    | .error _ => reject "incomplete-single-response"
    | .ok payload => acceptedPayload payload

private def range : S7.MemoryRange :=
  { area := .dataBlocks, dbNumber := 1, start := 16, count := 1 }
private def location (index : Option Nat) (offset : Nat := 0) : WriteLocation :=
  { range := { range with start := range.start + offset },
    itemIndex := index, chunkByteOffset := offset }
private def locationJson (loc : WriteLocation) : Json := Json.mkObj [
  ("range", Json.mkObj [("area", "data-blocks"), ("db_number", toJson loc.range.dbNumber.toNat),
    ("start", toJson loc.range.start), ("count", toJson loc.range.count)]),
  ("item_index", toJson loc.itemIndex), ("chunk_byte_offset", toJson loc.chunkByteOffset)]

inductive ProgressEvent where
  | send (locations : Array WriteLocation)
  | acknowledge (results : Array S7.WriteItemResult)
  | replay
  | globalReject

structure ProgressCase where
  id : String
  events : Array ProgressEvent
  outcomes : Array String
  indices : Array (Option Nat)
  offsets : Array Nat

def progressCases : Array ProgressCase := #[
  ⟨"duplicate-caller-ranges", #[.send #[location (some 0),location (some 1)],
    .acknowledge #[.success,.failure 5]], #["success","failure:5"], #[some 0,some 1], #[0,0]⟩,
  ⟨"chunk-prefix-then-uncertain", #[.send #[location (some 1)],.acknowledge #[.success],
    .send #[location (some 1) 212]], #["success","pending"], #[some 1,some 1], #[0,212]⟩,
  ⟨"replay-then-success", #[.send #[location (some 0)],.replay,.send #[location (some 0)],
    .acknowledge #[.success]], #["replayed-unknown","success"], #[some 0,some 0], #[0,0]⟩,
  ⟨"scalar-global-rejection", #[.send #[location none 424],.globalReject],
    #["global-rejected"], #[none], #[424]⟩,
  ⟨"replay-then-global-rejection", #[.send #[location (some 2)],.replay,
    .send #[location (some 2)],.globalReject], #["replayed-unknown","global-rejected"],
    #[some 2,some 2], #[0,0]⟩
]

private def outcomeName : WriteAttemptOutcome → String
  | .pending => "pending"
  | .replayedUnknown => "replayed-unknown"
  | .globalRejected => "global-rejected"
  | .itemResult .success => "success"
  | .itemResult (.failure code) => s!"failure:{code.toNat}"

private def progressResult (test : ProgressCase) : Except DecodeError WriteProgress := do
  let mut state : WriteProgress.State := {}
  for event in test.events do
    state ← match event with
      | .send locations => state.sent locations
      | .acknowledge results => state.acknowledge results
      | .replay => .ok state.replay
      | .globalReject => .ok state.globalReject
  return state.snapshot

private def resultJson : S7.WriteItemResult → Json
  | .success => Json.mkObj [("status", "success")]
  | .failure code => Json.mkObj [("status", "failure"), ("code", toJson code.toNat)]
private def eventJson : ProgressEvent → Json
  | .send locations => Json.mkObj [("operation", "send"), ("locations", Json.arr (locations.map locationJson))]
  | .acknowledge results => Json.mkObj [("operation", "acknowledge"), ("results", Json.arr (results.map resultJson))]
  | .replay => Json.mkObj [("operation", "replay")]
  | .globalReject => Json.mkObj [("operation", "global-reject")]

def validate : IO Unit := do
  unless retryPermitted .readOnly false && retryPermitted .readOnly true &&
      !(retryPermitted .potentiallyMutating false) && retryPermitted .potentiallyMutating true do
    throw <| IO.userError "operation retry policy differs from fixed conservative expectations"
  for test in stringCases do
    unless stringResult test == test.expected do throw <| IO.userError s!"string operation differs: {test.id}"
  for test in userDataCases do
    unless userDataResult test == test.expected do throw <| IO.userError s!"USER_DATA completion differs: {test.id}"
  for test in progressCases do
    let .ok progress := progressResult test | throw <| IO.userError s!"write progress rejected: {test.id}"
    unless progress.attempts.map (outcomeName ·.outcome) == test.outcomes &&
        progress.attempts.map (·.location.itemIndex) == test.indices &&
        progress.attempts.map (·.location.chunkByteOffset) == test.offsets do
      throw <| IO.userError s!"write progress order/provenance differs: {test.id}"

def corpus : Json := Json.mkObj [
  ("schema_version", 1), ("protocol", "classic S7 operation guards and write diagnostics"),
  ("string_read_cases", Json.arr (stringCases.map fun test => Json.mkObj [
    ("id", toJson test.id), ("encoding", toJson (if test.wide then "utf-16-be" else "latin-1")),
    ("initial_header", octets test.header), ("body", octets test.body), ("expected", test.expected)])),
  ("single_userdata_cases", Json.arr (userDataCases.map fun test => Json.mkObj [
    ("id", toJson test.id), ("reference", 1), ("group", toJson test.group.toNat),
    ("subfunction", toJson test.subfunction.toNat), ("pdu", octets (userDataPacket test)),
    ("expected", test.expected)])),
  ("retry_policy_cases", Json.arr ((#[false,true]).flatMap fun mutating =>
    (#[false,true]).map fun allow => Json.mkObj [
      ("id", toJson s!"retry-mutating-{mutating}-opt-in-{allow}"),
      ("safety", toJson (if mutating then "potentially-mutating" else "read-only")),
      ("allow_potentially_mutating", toJson allow),
      ("expected_permitted", toJson (retryPermitted (if mutating then .potentiallyMutating else .readOnly) allow))])),
  ("write_progress_cases", Json.arr (progressCases.map fun test => Json.mkObj [
    ("id", toJson test.id), ("events", Json.arr (test.events.map eventJson)),
    ("expected", match progressResult test with
      | .error _ => reject "progress-transition"
      | .ok progress => Json.mkObj [
        ("status", "accept"),
        ("attempts", Json.arr (progress.attempts.map fun attempt => Json.mkObj [
          ("location", locationJson attempt.location), ("outcome", toJson (outcomeName attempt.outcome))])),
        ("acknowledged_count", toJson progress.acknowledged.size),
        ("rejected_count", toJson progress.rejected.size),
        ("replayed_uncertain_count", toJson progress.replayedUncertain.size),
        ("uncertain_count", toJson progress.uncertain.size)])]))]

end LeanS7.Conformance.Operations
