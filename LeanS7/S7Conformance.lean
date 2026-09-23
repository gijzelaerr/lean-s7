import Lean.Data.Json
import LeanS7.S7
import LeanS7.Chunking
import LeanS7.Protocol
import LeanS7.Advanced
import LeanS7.SequenceConformance

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

structure UserDataExpected where
  payload : ByteArray
  sequence : UInt8
  hasMoreData : Bool

structure UserDataCase where
  id : String
  expectedGroup : UInt8
  expectedSubfunction : UInt8
  pdu : ByteArray
  expected : Option UserDataExpected

private def userDataPacket (parameters data : ByteArray) : ByteArray :=
  bytes #[0x32, 0x07, 0, 0, 0, 1] ++
    uint16BE (UInt16.ofNat parameters.size) ++ uint16BE (UInt16.ofNat data.size) ++
    parameters ++ data

private def userDataParameters (group subfunction sequence dataReference lastDataUnit : UInt8)
    (error : UInt16 := 0) : ByteArray :=
  bytes #[0, 1, 0x12, 8, 0x12, UInt8.lor 0x80 group, subfunction, sequence,
    dataReference, lastDataUnit] ++ uint16BE error

private def userDataItem (returnCode : UInt8) (payload : ByteArray)
    (declaredLength : Option Nat := none) : ByteArray :=
  bytes #[returnCode, 9] ++
    uint16BE (UInt16.ofNat (declaredLength.getD payload.size)) ++ payload

def userDataCases : Array UserDataCase := #[
  {
    id := "complete-szl"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 3 0x22 0)
      (userDataItem 0xff (bytes #[0x04, 0x24, 0, 0, 0, 4, 0, 1, 0, 0, 0, 8]))
    expected := some {
      payload := bytes #[0x04, 0x24, 0, 0, 0, 4, 0, 1, 0, 0, 0, 8]
      sequence := 3
      hasMoreData := false
    }
  },
  {
    id := "continuation-with-more-data"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 4 0x23 1)
      (userDataItem 0xff (bytes #[0xde, 0xad]))
    expected := some { payload := bytes #[0xde, 0xad], sequence := 4, hasMoreData := true }
  },
  {
    id := "invalid-continuation-flag-two"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 0 0 2)
      (userDataItem 0xff (bytes #[0xaa]))
    expected := none
  },
  {
    id := "invalid-continuation-flag-ff"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 0 0 0xff)
      (userDataItem 0xff (bytes #[0xaa]))
    expected := none
  },
  {
    id := "wrong-function-group"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 3 1 0 0 0)
      (userDataItem 0xff ByteArray.empty)
    expected := none
  },
  {
    id := "wrong-subfunction"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 2 0 0 0)
      (userDataItem 0xff ByteArray.empty)
    expected := none
  },
  {
    id := "userdata-error"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 0 0 0 0x8104)
      (userDataItem 0xff ByteArray.empty)
    expected := none
  },
  {
    id := "item-error"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 0 0 0)
      (userDataItem 0x0a ByteArray.empty)
    expected := none
  },
  {
    id := "truncated-userdata-payload"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 0 0 0)
      (userDataItem 0xff (bytes #[0xaa, 0xbb]) (some 4))
    expected := none
  },
  {
    id := "trailing-userdata-payload"
    expectedGroup := S7.szlGroup
    expectedSubfunction := S7.readSzlSubfunction
    pdu := userDataPacket (userDataParameters 4 1 0 0 0)
      (userDataItem 0xff (bytes #[0xaa, 0xbb]) (some 1))
    expected := none
  }
]

structure UploadExpected where
  payload : ByteArray
  isLast : Bool

structure UploadCase where
  id : String
  pdu : ByteArray
  expected : Option UploadExpected

private def ackDataPacket (parameters data : ByteArray) : ByteArray :=
  match S7.encodeAckData 1 parameters data with
  | .ok packet => packet
  | .error _ => ByteArray.empty

private def encodedPacket (result : Except S7.EncodeError ByteArray) : ByteArray :=
  match result with
  | .ok packet => packet
  | .error _ => ByteArray.empty

private def setClockPacket : ByteArray :=
  match S7.encodePlcDateTime {
      year := 2026, month := 9, day := 23, hour := 12, minute := 34,
      second := 56, millisecond := 789, weekday := 3
    } with
  | .error _ => ByteArray.empty
  | .ok payload => encodedPacket (S7.encodeSetClock 1 payload)

private def setPasswordPacket : ByteArray :=
  match S7.encodePassword "SECRET" with
  | .error _ => ByteArray.empty
  | .ok password => encodedPacket (S7.encodeSetPassword 1 password)

structure RequestCase where
  id : String
  operation : String
  packet : ByteArray

/-- Management and block-service request vectors. Each uses PDU reference 1. -/
def requestCases : Array RequestCase := #[
  ⟨"read-clock", "read_clock", encodedPacket (S7.encodeReadClock 1)⟩,
  ⟨"list-blocks", "list_blocks", encodedPacket (S7.encodeListBlocks 1)⟩,
  ⟨"list-data-blocks", "list_data_blocks",
    encodedPacket (S7.encodeListBlocksOfType 1 .dataBlock)⟩,
  ⟨"plc-stop", "plc_stop", encodedPacket (S7.encodePlcStop 1)⟩,
  ⟨"plc-hot-start", "plc_hot_start", encodedPacket (S7.encodePlcHotStart 1)⟩,
  ⟨"plc-cold-start", "plc_cold_start", encodedPacket (S7.encodePlcColdStart 1)⟩,
  ⟨"start-db-upload", "start_db_upload", encodedPacket (S7.encodeStartUpload 1 .dataBlock 1)⟩,
  ⟨"upload-fragment-request", "upload_fragment", encodedPacket (S7.encodeUpload 1 7)⟩,
  ⟨"end-upload", "end_upload", encodedPacket (S7.encodeEndUpload 1 7)⟩,
  ⟨"set-clock", "set_clock", setClockPacket⟩,
  ⟨"set-session-password", "set_password", setPasswordPacket⟩,
  ⟨"clear-session-password", "clear_password", encodedPacket (S7.encodeClearPassword 1)⟩,
  ⟨"get-db-info", "get_db_info", encodedPacket (S7.encodeGetBlockInfo 1 .dataBlock 1)⟩,
  ⟨"request-db-download", "request_db_download",
    encodedPacket (S7.encodeRequestDownload 1 .dataBlock 1 64 28)⟩,
  ⟨"download-fragment-response", "download_fragment_response",
    encodedPacket (S7.encodeDownloadFragmentResponse 1 false (bytes #[0xde, 0xad]))⟩,
  ⟨"final-download-fragment-response", "final_download_fragment_response",
    encodedPacket (S7.encodeDownloadFragmentResponse 1 true (bytes #[0xbe, 0xef]))⟩,
  ⟨"download-ended-response", "download_ended_response",
    encodedPacket (S7.encodeDownloadEndedResponse 1)⟩
]

def uploadCases : Array UploadCase := #[
  {
    id := "upload-fragment"
    pdu := ackDataPacket (bytes #[S7.uploadFunction, 1])
      (bytes #[0, 3, 0, 0xfb, 0xaa, 0xbb, 0xcc])
    expected := some { payload := bytes #[0xaa, 0xbb, 0xcc], isLast := false }
  },
  {
    id := "last-upload-fragment"
    pdu := ackDataPacket (bytes #[S7.uploadFunction, 0])
      (bytes #[0, 2, 0, 0xfb, 0xde, 0xad])
    expected := some { payload := bytes #[0xde, 0xad], isLast := true }
  },
  {
    id := "upload-invalid-marker"
    pdu := ackDataPacket (bytes #[S7.uploadFunction, 0])
      (bytes #[0, 2, 0, 0xfa, 0xde, 0xad])
    expected := none
  },
  {
    id := "upload-length-mismatch"
    pdu := ackDataPacket (bytes #[S7.uploadFunction, 0])
      (bytes #[0, 3, 0, 0xfb, 0xde, 0xad])
    expected := none
  },
  {
    id := "upload-wrong-function"
    pdu := ackDataPacket (bytes #[S7.startUploadFunction, 0])
      (bytes #[0, 2, 0, 0xfb, 0xde, 0xad])
    expected := none
  },
  {
    id := "upload-invalid-continuation-flag"
    pdu := ackDataPacket (bytes #[S7.uploadFunction, 2])
      (bytes #[0, 2, 0, 0xfb, 0xde, 0xad])
    expected := none
  },
  {
    id := "upload-invalid-continuation-flag-ff"
    pdu := ackDataPacket (bytes #[S7.uploadFunction, 0xff])
      (bytes #[0, 2, 0, 0xfb, 0xde, 0xad])
    expected := none
  }
]

structure BlockCountsCase where
  id : String
  payload : ByteArray
  expected : Option S7.BlockCounts

private def completeBlockCounts : ByteArray := bytes #[
  0x30, 0x38, 0, 1, 0x30, 0x45, 0, 2, 0x30, 0x43, 0, 3,
  0x30, 0x41, 0, 4, 0x30, 0x42, 0, 5, 0x30, 0x44, 0, 6,
  0x30, 0x46, 0, 7]

def blockCountsCases : Array BlockCountsCase := #[
  ⟨"complete-block-counts", completeBlockCounts, some {
    organizationBlocks := 1, functionBlocks := 2, functions := 3,
    dataBlocks := 4, systemDataBlocks := 5, systemFunctions := 6,
    systemFunctionBlocks := 7
  }⟩,
  ⟨"truncated-block-counts", completeBlockCounts.extract 0 27, none⟩,
  ⟨"duplicate-block-count-type",
    completeBlockCounts.extract 0 5 ++ bytes #[0x44] ++ completeBlockCounts.extract 6 28, none⟩,
  ⟨"duplicate-identical-block-count",
    completeBlockCounts.extract 0 4 ++ completeBlockCounts.extract 0 4 ++
      completeBlockCounts.extract 8 28, none⟩,
  ⟨"trailing-block-counts", completeBlockCounts ++ bytes #[0], none⟩,
  ⟨"unknown-block-count-type",
    bytes #[0x30, 0x39, 0, 1] ++ completeBlockCounts.extract 4 28, none⟩
]

structure BlockEntriesCase where
  id : String
  payload : ByteArray
  expected : Option (Array S7.BlockEntry)

def blockEntriesCases : Array BlockEntriesCase := #[
  ⟨"complete-block-list", bytes #[0, 1, 0x10, 2, 0x12, 0x34, 0x20, 3], some #[
    { number := 1, flags := 0x10, language := 2 },
    { number := 0x1234, flags := 0x20, language := 3 }
  ]⟩,
  ⟨"truncated-block-list", bytes #[0, 1, 0x10], none⟩,
  ⟨"trailing-block-list", bytes #[0, 1, 0x10, 2, 0xff], none⟩
]

structure BlockInfoCase where
  id : String
  payload : ByteArray
  expected : Option S7.BlockInfo

private def completeBlockInfo : ByteArray :=
  bytes #[0, 0x41, 0, 0, 0, 0, 0, 0, 0, 0xaa, 5, 0, 0, 1,
    0, 0, 1, 0, 0, 0, 0, 0,
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
    0, 0x10, 0, 0, 0, 0x20, 0, 0x30] ++
  "GIJS    LEAN    DB1     ".toUTF8 ++
  bytes #[0x12, 0, 0xbe, 0xef, 0, 0, 0, 0, 0, 0, 0, 0]

def blockInfoCases : Array BlockInfoCase := #[
  ⟨"complete-block-info", completeBlockInfo, some {
    blockType := 0x41, number := 1, language := 5, flags := 0xaa,
    mc7Size := 0x30, loadSize := 0x100, localDataSize := 0x20, sbbSize := 0x10,
    checksum := 0xbeef, version := 0x12,
    codeDateRaw := bytes #[1, 2, 3, 4, 5, 6],
    interfaceDateRaw := bytes #[7, 8, 9, 10, 11, 12],
    author := "GIJS", family := "LEAN", name := "DB1"
  }⟩,
  ⟨"truncated-block-info", completeBlockInfo.extract 0 77, none⟩,
  ⟨"trailing-block-info", completeBlockInfo ++ bytes #[0], none⟩
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

private def userDataJson (test : UserDataCase) : Json :=
  Json.mkObj [
    ("id", toJson test.id),
    ("expected_group", toJson test.expectedGroup.toNat),
    ("expected_subfunction", toJson test.expectedSubfunction.toNat),
    ("pdu", octets test.pdu),
    ("expected", match test.expected with
      | none => Json.mkObj [("status", "reject")]
      | some value => Json.mkObj [
          ("status", "accept"),
          ("payload", octets value.payload),
          ("sequence", toJson value.sequence.toNat),
          ("has_more_data", toJson value.hasMoreData)])
  ]

private def uploadJson (test : UploadCase) : Json :=
  Json.mkObj [
    ("id", toJson test.id),
    ("pdu", octets test.pdu),
    ("expected", match test.expected with
      | none => Json.mkObj [("status", "reject")]
      | some value => Json.mkObj [
          ("status", "accept"),
          ("payload", octets value.payload),
          ("is_last", toJson value.isLast)])
  ]

private def requestJson (test : RequestCase) : Json := Json.mkObj [
  ("id", toJson test.id),
  ("operation", toJson test.operation),
  ("expected_packet", octets test.packet)
]

private def blockCountsJson (counts : S7.BlockCounts) : Json := Json.mkObj [
  ("organization_blocks", toJson counts.organizationBlocks.toNat),
  ("function_blocks", toJson counts.functionBlocks.toNat),
  ("functions", toJson counts.functions.toNat),
  ("data_blocks", toJson counts.dataBlocks.toNat),
  ("system_data_blocks", toJson counts.systemDataBlocks.toNat),
  ("system_functions", toJson counts.systemFunctions.toNat),
  ("system_function_blocks", toJson counts.systemFunctionBlocks.toNat)
]

private def blockCountsCaseJson (test : BlockCountsCase) : Json := Json.mkObj [
  ("id", toJson test.id),
  ("payload", octets test.payload),
  ("expected", match test.expected with
    | none => Json.mkObj [("status", "reject")]
    | some counts => Json.mkObj [("status", "accept"), ("counts", blockCountsJson counts)])
]

private def blockEntryJson (entry : S7.BlockEntry) : Json := Json.mkObj [
  ("number", toJson entry.number.toNat),
  ("flags", toJson entry.flags.toNat),
  ("language", toJson entry.language.toNat)
]

private def blockEntriesCaseJson (test : BlockEntriesCase) : Json := Json.mkObj [
  ("id", toJson test.id),
  ("payload", octets test.payload),
  ("expected", match test.expected with
    | none => Json.mkObj [("status", "reject")]
    | some entries => Json.mkObj [
        ("status", "accept"), ("entries", Json.arr (entries.map blockEntryJson))])
]

private def blockInfoJson (info : S7.BlockInfo) : Json := Json.mkObj [
  ("block_type", toJson info.blockType.toNat), ("number", toJson info.number.toNat),
  ("language", toJson info.language.toNat), ("flags", toJson info.flags.toNat),
  ("mc7_size", toJson info.mc7Size.toNat), ("load_size", toJson info.loadSize.toNat),
  ("local_data_size", toJson info.localDataSize.toNat), ("sbb_size", toJson info.sbbSize.toNat),
  ("checksum", toJson info.checksum.toNat), ("version", toJson info.version.toNat),
  ("code_date", octets info.codeDateRaw), ("interface_date", octets info.interfaceDateRaw),
  ("author", toJson info.author), ("family", toJson info.family), ("name", toJson info.name)
]

private def blockInfoCaseJson (test : BlockInfoCase) : Json := Json.mkObj [
  ("id", toJson test.id), ("payload", octets test.payload),
  ("expected", match test.expected with
    | none => Json.mkObj [("status", "reject")]
    | some info => Json.mkObj [("status", "accept"), ("info", blockInfoJson info)])
]

/-- Validate fixed expectations against executable codecs before exporting them.
    WORD cases model byte arithmetic, not a Lean DB WORD API. -/
def validate : IO Unit := do
  Sequences.validate
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
  for test in userDataCases do
    let result := LeanS7.S7.decodeUserDataResponse 1 test.expectedGroup
      test.expectedSubfunction test.pdu
    let conforms := match result, test.expected with
      | .error _, none => true
      | .ok actual, some expected =>
          actual.payload == expected.payload && actual.sequence == expected.sequence &&
            actual.hasMoreData == expected.hasMoreData
      | _, _ => false
    unless conforms do
      throw <| IO.userError s!"S7 USER_DATA conformance failed: {test.id}"
  for test in uploadCases do
    let result := do
      let response ← LeanS7.S7.decodeResponse test.pdu
      LeanS7.S7.decodeUploadFragment 1 response
    let conforms := match result, test.expected with
      | .error _, none => true
      | .ok actual, some expected =>
          actual.data == expected.payload && actual.isLast == expected.isLast
      | _, _ => false
    unless conforms do
      throw <| IO.userError s!"S7 upload conformance failed: {test.id}"
  for test in requestCases do
    let referenceMatches := match LeanS7.S7.decodePduReference test.packet with
      | .ok reference => reference == 1
      | .error _ => false
    unless !test.packet.isEmpty && referenceMatches do
      throw <| IO.userError s!"S7 request conformance failed: {test.id}"
  for test in blockCountsCases do
    let result := S7.decodeBlockCounts test.payload
    let conforms := match result, test.expected with
      | .error _, none => true
      | .ok actual, some expected => actual == expected
      | _, _ => false
    unless conforms do
      throw <| IO.userError s!"S7 block-count conformance failed: {test.id}"
  for test in blockEntriesCases do
    let result := S7.decodeBlockEntries test.payload
    let conforms := match result, test.expected with
      | .error _, none => true
      | .ok actual, some expected => actual == expected
      | _, _ => false
    unless conforms do
      throw <| IO.userError s!"S7 block-list conformance failed: {test.id}"
  for test in blockInfoCases do
    let result := S7.decodeBlockInfo test.payload
    let conforms := match result, test.expected with
      | .error _, none => true
      | .ok actual, some expected => actual == expected
      | _, _ => false
    unless conforms do
      throw <| IO.userError s!"S7 block-info conformance failed: {test.id}"
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
  ("schema_version", 1), ("protocol", "classic S7 semantics"),
  ("multi_item_cases", Sequences.multiJson),
  ("userdata_conversation_cases", Sequences.continuationJson),
  ("response_cases", Json.arr (responseCases.map responseJson)),
  ("userdata_cases", Json.arr (userDataCases.map userDataJson)),
  ("upload_cases", Json.arr (uploadCases.map uploadJson)),
  ("request_cases", Json.arr (requestCases.map requestJson)),
  ("block_count_cases", Json.arr (blockCountsCases.map blockCountsCaseJson)),
  ("block_list_cases", Json.arr (blockEntriesCases.map blockEntriesCaseJson)),
  ("block_info_cases", Json.arr (blockInfoCases.map blockInfoCaseJson)),
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
