import Lean.Data.Json
import LeanS7.Advanced
import LeanS7.UserDataAssembly

namespace LeanS7.Conformance.ManagementPdus
open Lean

structure DecoderCase where
  id : String
  reference : UInt16 := 1
  group : UInt8
  subfunction : UInt8
  pdu : ByteArray
  expected : Option S7.UserDataResponse
  category : String := "protocol"

private def octets (data : ByteArray) : Json := toJson (data.toList.map UInt8.toNat)

private def response (reference : UInt16) (group subfunction sequence unit flag transport code : UInt8)
    (payload : ByteArray) (error : UInt16 := 0) : ByteArray :=
  let parameters := bytes #[0,1,0x12,8,0x12,UInt8.lor 0x80 group,subfunction,sequence,unit,flag] ++
    uint16BE error
  let data := bytes #[code,transport] ++ uint16BE (UInt16.ofNat payload.size) ++ payload
  bytes #[0x32,7,0,0] ++ uint16BE reference ++ uint16BE 12 ++
    uint16BE (UInt16.ofNat data.size) ++ parameters ++ data

private def expected (group subfunction sequence unit flag transport code : UInt8)
    (payload : ByteArray) (reference : UInt16 := 1) : S7.UserDataResponse := {
  reference, group, subfunction, sequence, dataUnitReference := unit,
  hasMoreData := flag != 0, error := 0, returnCode := code, transportSize := transport, payload }

def decoderCases : Array DecoderCase := Id.run do
  let mut cases := #[]
  for (group,subfunction) in #[(4,1),(3,2),(7,1),(7,2),(5,1),(5,2)] do
    for transport in #[0,4,7,9,10,255] do
      for payload in #[ByteArray.empty,bytes #[0xaa,0xbb]] do
        cases := cases.push {
          id := s!"ff-{group}-{subfunction}-{transport}-{payload.size}", group, subfunction,
          pdu := response 1 group subfunction 255 0 0 transport 255 payload,
          expected := if transport == 9 then some (expected group subfunction 255 0 0 transport 255 payload)
            else none }
  for (group,subfunction) in #[(7,2),(5,1),(5,2)] do
    for transport in #[0,4,7,9,10,255] do
      for payload in #[ByteArray.empty,bytes #[0xaa]] do
        for flag in #[0,1] do
          cases := cases.push {
            id := s!"null-{group}-{subfunction}-{transport}-{payload.size}-{flag}", group, subfunction,
            pdu := response 1 group subfunction 0 0 flag transport 10 payload,
            expected := if transport == 0 && payload.isEmpty && flag == 0 then
              some (expected group subfunction 0 0 flag transport 10 payload) else none }
  for (group,subfunction) in #[(4,1),(3,2),(7,1)] do
    cases := cases.push {
      id := s!"null-unsupported-{group}-{subfunction}", group, subfunction,
      pdu := response 1 group subfunction 0 0 0 0 10 ByteArray.empty,
      expected := none, category := "plc-rejected" }
  let good := response 1 4 1 255 0 0 9 255 (bytes #[0xaa])
  cases := cases.push {
    id := "wrong-reference", group := 4, subfunction := 1,
    pdu := response 2 4 1 255 0 0 9 255 (bytes #[0xaa]), expected := none }
  cases := cases.push {
    id := "wrong-group", group := 4, subfunction := 1,
    pdu := response 1 3 1 255 0 0 9 255 (bytes #[0xaa]), expected := none }
  cases := cases.push {
    id := "wrong-subfunction", group := 4, subfunction := 1,
    pdu := response 1 4 2 255 0 0 9 255 (bytes #[0xaa]), expected := none }
  cases := cases.push {
    id := "parameter-error-before-null", group := 7, subfunction := 2,
    pdu := response 1 7 2 0 0 0 0 10 ByteArray.empty 0x8104,
    expected := none, category := "plc-rejected" }
  cases := cases.push {
    id := "invalid-continuation-flag", group := 4, subfunction := 1,
    pdu := response 1 4 1 255 0 2 9 255 (bytes #[0xaa]), expected := none }
  cases := cases.push {
    id := "trailing-packet", group := 4, subfunction := 1,
    pdu := good.push 0, expected := none }
  for length in [:good.size] do
    cases := cases.push {
      id := s!"truncated-{length}", group := 4, subfunction := 1,
      pdu := good.extract 0 length, expected := none }
  return cases

structure ConversationCase where
  id : String
  group : UInt8
  subfunction : UInt8
  unit : UInt8
  fault : String

def conversationCases : Array ConversationCase := Id.run do
  let mut cases := #[]
  for (group,subfunction) in #[(4,1),(3,2)] do
    for unit in #[0,81] do
      for fault in #["none","identity","transport","reference"] do
        cases := cases.push { id := s!"fragments-{group}-{unit}-{fault}", group, subfunction, unit, fault }
  return cases

private def sequences : Array UInt8 := #[255,0,0,128]

private def conversationRequest (test : ConversationCase) (index : Nat) :
    Except S7.EncodeError ByteArray :=
  let reference := UInt16.ofNat (65535 + index)
  if index == 0 then
    if test.group == 4 then S7.encodeReadSzl reference 0x0424 0
    else S7.encodeListBlocksOfType reference .dataBlock
  else S7.encodeUserDataContinuation reference test.group test.subfunction sequences[index - 1]!

/-- Independent literal wire layout checks the generated request fixtures,
    including every opaque previous-response token and wrapped reference. -/
private def requestWire (test : ConversationCase) (index : Nat) : ByteArray :=
  let parameters := if index == 0 then
    bytes #[0,1,0x12,4,0x11,UInt8.lor 0x40 test.group,test.subfunction,0]
  else bytes #[0,1,0x12,8,0x11,UInt8.lor 0x40 test.group,test.subfunction,
    sequences[index - 1]!,0,0,0,0]
  let data := if index != 0 then bytes #[10,0,0,0]
    else if test.group == 4 then bytes #[255,9,0,4,4,0x24,0,0]
    else bytes #[255,9,0,2,0x30,0x41]
  bytes #[0x32,7,0,0] ++ uint16BE (UInt16.ofNat (65535 + index)) ++
    uint16BE (UInt16.ofNat parameters.size) ++ uint16BE (UInt16.ofNat data.size) ++ parameters ++ data

private def fragment (test : ConversationCase) (index : Nat) : ByteArray :=
  let sequence := sequences[index]!
  let unit := if index == 2 && test.fault == "identity" then test.unit + 1 else test.unit
  let transport := if index == 2 && test.fault == "transport" then 4 else 9
  let reference := UInt16.ofNat (65535 + index + if index == 2 && test.fault == "reference" then 1 else 0)
  response reference test.group test.subfunction sequence unit (if index < 3 then 1 else 0)
    transport 255 (bytes #[UInt8.ofNat index, UInt8.ofNat (index + 16)])

private def conversation (test : ConversationCase) : Except DecodeError ByteArray := do
  let mut identity := none
  let mut state := UserDataAssembly.empty (16 * 1024 * 1024) 256
  for index in [:4] do
    let decoded ← S7.decodeUserDataResponse (UInt16.ofNat (65535 + index)) test.group test.subfunction
      (fragment test index)
    identity := some (← S7.correlateUserDataFragment identity decoded)
    let step ← UserDataAssembly.accept state decoded.payload decoded.hasMoreData
    state := step.after
  return state.data

private def category : DecodeError → String
  | .remoteFailure .. => "plc-rejected"
  | _ => "protocol"

def validate : IO Unit := do
  unless decoderCases.size == 180 && conversationCases.size == 16 do
    throw <| IO.userError "management corpus coverage changed"
  for test in decoderCases do
    match S7.decodeUserDataResponse test.reference test.group test.subfunction test.pdu, test.expected with
    | .ok actual, some value =>
      unless actual == value do throw <| IO.userError s!"management decode mismatch {test.id}"
    | .error error, none =>
      unless category error == test.category do throw <| IO.userError s!"management category mismatch {test.id}"
    | _, _ => throw <| IO.userError s!"management outcome mismatch {test.id}"
  for test in conversationCases do
    for index in [:4] do
      let .ok packet := conversationRequest test index
        | throw <| IO.userError s!"management request encoding rejected {test.id} step {index}"
      unless packet == requestWire test index do
        throw <| IO.userError s!"management request fixture mismatch {test.id} step {index}"
    match conversation test with
    | .ok data =>
      unless test.fault == "none" && data == bytes #[0,16,1,17,2,18,3,19] do
        throw <| IO.userError s!"management conversation mismatch {test.id}"
    | .error _ =>
      unless test.fault != "none" do throw <| IO.userError s!"management conversation rejected {test.id}"

private def decoderJson (test : DecoderCase) : Json := Json.mkObj [
  ("id",toJson test.id), ("reference",toJson test.reference.toNat),
  ("group",toJson test.group.toNat), ("subfunction",toJson test.subfunction.toNat),
  ("pdu",octets test.pdu), ("expected",match test.expected with
    | none => Json.mkObj [("status","reject"),("category",toJson test.category)]
    | some value => Json.mkObj [("status","accept"),("payload",octets value.payload),
        ("sequence",toJson value.sequence.toNat),("data_unit_reference",toJson value.dataUnitReference.toNat),
        ("has_more_data",toJson value.hasMoreData),("return_code",toJson value.returnCode.toNat),
        ("transport_size",toJson value.transportSize.toNat)])]

private def conversationJson (test : ConversationCase) : Json := Json.mkObj [
  ("id",toJson test.id),("group",toJson test.group.toNat),("subfunction",toJson test.subfunction.toNat),
  ("steps",Json.arr ((Array.range 4).map fun index =>
    let reference := UInt16.ofNat (65535 + index)
    let request := conversationRequest test index
    Json.mkObj [("reference",toJson reference.toNat),
      ("request_pdu",match request with | .ok packet => octets packet | .error _ => Json.null),
      ("response_pdu",octets (fragment test index))])),
  ("expected",if test.fault == "none" then Json.mkObj [("status","accept"),
    ("assembled_payload",octets (bytes #[0,16,1,17,2,18,3,19]))]
    else Json.mkObj [("status","reject"),("category","protocol"),("failed_step",2)])]

def corpus : Json := Json.mkObj [
  ("schema_version",1),("protocol","classic S7 management codec conversations"),
  ("decoder_cases",Json.arr (decoderCases.map decoderJson)),
  ("continuation_cases",Json.arr (conversationCases.map conversationJson))]

end LeanS7.Conformance.ManagementPdus
