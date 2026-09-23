import Lean.Data.Json
import LeanS7.Advanced
import LeanS7.UserDataAssembly
import LeanS7.ValueCodecAssurance

namespace LeanS7.Conformance.Sequences
open Lean

private def octets (value : ByteArray) : Json := toJson (value.toList.map UInt8.toNat)

structure MultiCase where
  id : String
  write : Bool
  data : ByteArray
  trailing : Bool := false

def multiCases : Array MultiCase := #[
  ⟨"mixed-read-odd-padding", false, bytes #[255,4,0,8,0xaa,0,5,0,0,0,255,4,0,16,0xbb,0xcc], false⟩,
  ⟨"mixed-read-missing-padding", false, bytes #[255,4,0,8,0xaa,5,0,0,0,255,4,0,16,0xbb,0xcc], true⟩,
  ⟨"mixed-read-trailing-byte", false, bytes #[255,4,0,8,0xaa,0,5,0,0,0,255,4,0,16,0xbb,0xcc,0], true⟩,
  ⟨"mixed-write-ordered-status", true, bytes #[255,5,255], false⟩,
  ⟨"mixed-write-missing-status", true, bytes #[255,5], true⟩,
  ⟨"mixed-write-trailing-status", true, bytes #[255,5,255,255], true⟩
]

private def ranges : Array S7.MemoryRange := #[
  { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 },
  { area := .dataBlocks, dbNumber := 1, start := 8, count := 1 },
  { area := .dataBlocks, dbNumber := 1, start := 16, count := 2 }
]

private def response (test : MultiCase) : S7.Response := {
  pduType := 3, reference := 1, errorClass := 0, errorCode := 0,
  parameters := bytes #[if test.write then 5 else 4, 3], data := test.data
}

private def multiResult (test : MultiCase) : Except DecodeError Json := do
  if test.write then
    let results ← S7.decodeAreaWriteMany 1 3 (response test)
    return Json.arr (results.map fun result => match result with
      | .success => Json.mkObj [("status", "success")]
      | .failure code => Json.mkObj [("status", "failure"), ("code", toJson code.toNat)])
  let results ← S7.decodeAreaReadMany 1 ranges (response test)
  return Json.arr (results.map fun result => match result with
    | .success payload => Json.mkObj [("status", "success"), ("payload", octets payload)]
    | .failure code => Json.mkObj [("status", "failure"), ("code", toJson code.toNat)])

structure ContinuationCase where
  id : String
  fragments : Array (ByteArray × Bool)
  maximum : Nat
  limit : Nat
  expected : Option ByteArray

def continuationCases : Array ContinuationCase := #[
  ⟨"three-fragment-ordered", #[(bytes #[0xaa], true), (bytes #[0xbb,0xcc], true), (bytes #[0xdd], false)], 4, 3, some (bytes #[0xaa,0xbb,0xcc,0xdd])⟩,
  ⟨"empty-middle-fragment", #[(bytes #[0xaa], true), (ByteArray.empty, true), (bytes #[0xbb], false)], 2, 3, some (bytes #[0xaa,0xbb])⟩,
  ⟨"fragment-after-completion", #[(bytes #[0xaa], false), (bytes #[0xbb], false)], 2, 2, none⟩,
  ⟨"continuation-byte-overflow", #[(bytes #[0xaa], true), (bytes #[0xbb], false)], 1, 2, none⟩,
  ⟨"continuation-fragment-limit", #[(ByteArray.empty, true), (ByteArray.empty, true)], 1, 2, none⟩,
  ⟨"continuation-not-completed", #[(bytes #[0xaa], true)], 2, 2, none⟩
]

private def fragmentPacket (index : Nat) (payload : ByteArray) (more : Bool) : ByteArray :=
  let parameters := bytes #[0,1,0x12,8,0x12,0x84,1,UInt8.ofNat index,0x22,
    if more then 1 else 0,0,0]
  let data := bytes #[255,9] ++ uint16BE (UInt16.ofNat payload.size) ++ payload
  bytes #[0x32,7,0,0,0,1] ++ uint16BE 12 ++ uint16BE (UInt16.ofNat data.size) ++ parameters ++ data

private def continuationResult (test : ContinuationCase) : Except DecodeError ByteArray := do
  let mut state := UserDataAssembly.empty test.maximum test.limit
  for index in [:test.fragments.size] do
    let (payload, more) := test.fragments[index]!
    let decoded ← S7.decodeUserDataResponse 1 4 1 (fragmentPacket index payload more)
    let step ← UserDataAssembly.accept state decoded.payload decoded.hasMoreData
    state := step.after
  if !state.complete then throw (.invalidField 0 "incomplete USER_DATA conversation")
  return state.data

def validate : IO Unit := do
  for test in multiCases do
    let actual := multiResult test
    if test.trailing then
      unless (match actual with | .error _ => true | _ => false) do
        throw <| IO.userError s!"multi conversation should reject: {test.id}"
    else
      let .ok values := actual | throw <| IO.userError s!"multi conversation failed: {test.id}"
      let expected := if test.write then Json.arr #[
        Json.mkObj [("status", "success")], Json.mkObj [("status", "failure"), ("code", 5)],
        Json.mkObj [("status", "success")]]
      else Json.arr #[
        Json.mkObj [("status", "success"), ("payload", octets (bytes #[0xaa]))],
        Json.mkObj [("status", "failure"), ("code", 5)],
        Json.mkObj [("status", "success"), ("payload", octets (bytes #[0xbb,0xcc]))]]
      unless values == expected do throw <| IO.userError s!"multi order differs: {test.id}"
  for test in continuationCases do
    let conforms := match continuationResult test, test.expected with
      | .ok actual, some expected => actual == expected
      | .error _, none => true
      | _, _ => false
    unless conforms do throw <| IO.userError s!"continuation conversation differs: {test.id}"

def multiJson : Json := Json.arr (multiCases.map fun test => Json.mkObj [
  ("id", toJson test.id), ("operation", toJson (if test.write then "write" else "read")),
  ("reference", 1),
  ("ranges", Json.arr (ranges.map fun range => Json.mkObj [
    ("area", "data-blocks"), ("db_number", 1), ("start", toJson range.start), ("count", toJson range.count)])),
  ("request_pdu", octets (match (if test.write then S7.encodeAreaWriteMany 1 #[
      { range := ranges[0], payload := bytes #[0xaa] },
      { range := ranges[1], payload := bytes #[0xee] },
      { range := ranges[2], payload := bytes #[0xbb,0xcc] }]
    else S7.encodeAreaReadMany 1 ranges) with
    | .ok packet => packet | .error _ => ByteArray.empty)),
  ("response_pdu", octets (match S7.encodeAckData 1 (response test).parameters test.data with
    | .ok packet => packet | .error _ => ByteArray.empty)),
  ("expected", match multiResult test with
    | .ok results => Json.mkObj [("status", "accept"), ("items", results)]
    | .error _ => Json.mkObj [("status", "reject")])])

def continuationJson : Json := Json.arr (continuationCases.map fun test => Json.mkObj [
  ("id", toJson test.id), ("reference", 1), ("expected_group", 4), ("expected_subfunction", 1),
  ("maximum_bytes", toJson test.maximum), ("maximum_fragments", toJson test.limit),
  ("response_pdus", Json.arr (test.fragments.mapIdx fun index pair =>
    octets (fragmentPacket index pair.1 pair.2))),
  ("expected", match test.expected with
    | some payload => Json.mkObj [("status", "accept"), ("payload", octets payload)]
    | none => Json.mkObj [("status", "reject")])])

end LeanS7.Conformance.Sequences
