import Lean.Data.Json
import LeanS7.S7
import LeanS7.Chunking
import LeanS7.Protocol

namespace LeanS7.Conformance.S7

open Lean

structure ResponseCase where
  id : String
  operation : String
  requestedSize : Nat
  parameters : ByteArray
  data : ByteArray
  payload : Option ByteArray

def responseCases : Array ResponseCase := #[
  ⟨"complete-read", "read", 4, bytes #[4, 1], bytes #[255, 4, 0, 32, 17, 34, 51, 68],
    some (bytes #[17, 34, 51, 68])⟩,
  ⟨"truncated-read", "read", 4, bytes #[4, 1], bytes #[255, 4, 0, 32, 170], none⟩,
  ⟨"short-declared-read", "read", 4, bytes #[4, 1], bytes #[255, 4, 0, 8, 170], none⟩,
  ⟨"trailing-read-data", "read", 1, bytes #[4, 1], bytes #[255, 4, 0, 8, 170, 187], none⟩,
  ⟨"complete-write", "write", 1, bytes #[5, 1], bytes #[255], some ByteArray.empty⟩,
  ⟨"write-answered-by-read", "write", 1, bytes #[4, 1], bytes #[255, 4, 0, 8, 170], none⟩
]

def wordCounts : List Nat := [231, 231, 38]
def wordByteStarts : List Nat := [0, 462, 924]
def wordPayload : ByteArray := bytes #[17, 34, 51, 68]

structure AddressCase where
  id : String
  area : LeanS7.S7.Area
  start : Nat
  wireAddress : Nat

/-- Compatibility vectors for the native Snap7 start-offset convention.
    Wireshark interprets timer/counter fields as numbers, not DB bit addresses. -/
def addressCases : Array AddressCase := #[
  ⟨"db-byte-16", .dataBlocks, 16, 128⟩,
  ⟨"counter-start-16", .counters, 16, 16⟩,
  ⟨"timer-start-16", .timers, 16, 16⟩,
  ⟨"counter-next-chunk-478", .counters, 478, 478⟩,
  ⟨"timer-next-chunk-478", .timers, 478, 478⟩
]

def addressPacket (test : AddressCase) : Except String ByteArray := do
  let packet ← (LeanS7.S7.encodeAreaRead 1 {
    area := test.area, dbNumber := if test.area == .dataBlocks then 1 else 0,
    start := test.start, count := 2
  }).mapError reprStr
  (LeanS7.TPKT.encode { payload := LeanS7.COTP.encodeData { payload := packet } }).mapError reprStr

private def octets (value : ByteArray) : Json :=
  toJson (value.data.map UInt8.toNat)

private def addressJson (test : AddressCase) : Json := Json.mkObj [
  ("id", toJson test.id), ("area", toJson test.area.code.toNat),
  ("start_bytes", toJson test.start), ("wire_address", toJson test.wireAddress),
  ("packet", octets (match addressPacket test with | .ok packet => packet | .error _ => ByteArray.empty))
]

private def responseJson (test : ResponseCase) : Json :=
  Json.mkObj [
    ("id", toJson test.id), ("operation", toJson test.operation),
    ("requested_bytes", toJson test.requestedSize),
    ("parameters", octets test.parameters), ("data", octets test.data),
    ("expected", match test.payload with
      | none => Json.mkObj [("status", "reject")]
      | some value => Json.mkObj [("status", "accept"), ("payload", octets value)])
  ]

/-- Validate fixed expectations against executable codecs before exporting them.
    WORD cases model byte arithmetic, not a Lean DB WORD API. -/
def validate : IO Unit := do
  for test in addressCases do
    let .ok packet := addressPacket test
      | throw <| IO.userError s!"address encoding failed: {test.id}"
    unless packet.extract 28 31 == uint24BE (UInt32.ofNat test.wireAddress) do
      throw <| IO.userError s!"wire address differs: {test.id}"
  for test in responseCases do
    let response : LeanS7.S7.Response := {
      pduType := 3, reference := 1, parameters := test.parameters, data := test.data,
      errorClass := 0, errorCode := 0
    }
    let result := if test.operation == "read" then
      LeanS7.S7.decodeAreaRead 1 .dataBlocks test.requestedSize response
    else do
      LeanS7.S7.decodeDbWrite 1 response
      pure ByteArray.empty
    let conforms := match result, test.payload with
      | .error _, none => true
      | .ok actual, some expected => actual == expected
      | _, _ => false
    unless conforms do throw <| IO.userError s!"S7 conformance failed: {test.id}"
  unless Chunking.counts 500 ((480 - 18) / 2) == wordCounts do
    throw <| IO.userError "WORD chunk counts differ"
  let (total, starts) := wordCounts.foldl (init := (0, [])) fun (offset, starts) count =>
    (offset + count * 2, starts ++ [offset])
  unless starts == wordByteStarts && total == 1000 &&
      wordCounts.all (fun count => 18 + count * 2 ≤ 480) do
    throw <| IO.userError "WORD chunk offsets or budgets differ"
  let payload := wordPayload
  let .ok packet := LeanS7.S7.encodeAreaWriteMany 1 #[{
    range := { area := .dataBlocks, dbNumber := 1, start := 0, count := 4 }, payload
  }] | throw <| IO.userError "multi-write encoding failed"
  unless packet.extract 28 packet.size == payload do
    throw <| IO.userError "multi-write payload differs"
  unless packet.extract 26 28 == uint16BE 32 do
    throw <| IO.userError "multi-write encoded bit length differs"

def corpus : Json := Json.mkObj [
  ("schema_version", 1), ("protocol", "classic S7 read/write semantics"),
  ("response_cases", Json.arr (responseCases.map responseJson)),
  ("address_cases", Json.arr (addressCases.map addressJson)),
  ("chunk_cases", Json.arr #[Json.mkObj [
    ("id", "word-read-pdu-480"), ("element_bytes", 2), ("count", 500),
    ("pdu_bytes", 480), ("response_overhead_bytes", 18),
    ("expected_counts", toJson wordCounts),
    ("expected_byte_starts", toJson wordByteStarts)]]),
  ("write_cases", Json.arr #[Json.mkObj [
    ("id", "two-word-multi-write"), ("element_bytes", 2), ("count", 2),
    ("payload", octets wordPayload),
    ("expected_payload", octets wordPayload)]])
]

end LeanS7.Conformance.S7
