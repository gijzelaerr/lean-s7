import LeanS7.AdvancedDecoderAssurance

namespace LeanS7.AdvancedDecoderAssuranceTests

private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw <| IO.userError label

private def rejected {α ε : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

private def isExpected {α : Type} [BEq α] (actual : Except DecodeError α) (expected : α) : Bool :=
  match actual with | .ok result => result == expected | .error _ => false

private def blockTypes : Array S7.BlockType := #[.organizationBlock, .dataBlock,
  .systemDataBlock, .function, .systemFunction, .functionBlock, .systemFunctionBlock]

private def expectedCounts : S7.BlockCounts := {
  organizationBlocks := 0x1234, dataBlocks := 0x2345, systemDataBlocks := 0x3456,
  functions := 0x4567, systemFunctions := 0x5678, functionBlocks := 0x6789,
  systemFunctionBlocks := 0x789a
}

private def countRecord (index : Nat) : ByteArray :=
  bytes #[0x30, (blockTypes[index]?.getD .organizationBlock).code] ++
    uint16BE (UInt16.ofNat (0x1234 + index * 0x1111))

private def permutations : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | fuel + 1, remaining => remaining.flatMap fun value =>
      (permutations fuel (remaining.filter fun other => other != value)).map (value :: ·)

private def entryRecord (index : Nat) : ByteArray :=
  uint16BE (UInt16.ofNat (index * 257 + 3)) ++
    bytes #[UInt8.ofNat (index * 29), UInt8.ofNat (index * 71)]

private def blockInfo : ByteArray := bytes <| (List.range 78).toArray.map UInt8.ofNat

private def forceRecord (bit value : UInt8) : ByteArray :=
  bytes #[0x12, 0x34, 0xab, 0xcd, bit, value, 0xa5, 0x5a]

private def forceSzl (data : ByteArray) : S7.Szl := {
  id := 0x0025, index := 0, recordLength := 8,
  recordCount := UInt16.ofNat (data.size / 8), data
}

private def typedSzl (id : UInt16) (size : Nat) : S7.Szl := {
  id, index := 0, recordLength := UInt16.ofNat size, recordCount := 1,
  data := bytes <| (List.range size).toArray.map UInt8.ofNat
}

private def checkTyped (id : UInt16) (size : Nat)
    (parse : S7.Szl → Except DecodeError α) : IO Unit := do
  let good := typedSzl id size
  check (!rejected (parse good)) s!"typed SZL positive {id}"
  for short in [:size] do
    -- These are structurally coherent but too short for the typed fields.
    check (rejected <| parse (typedSzl id short)) s!"typed SZL truncated {id}/{short}"
  check (rejected <| parse { good with id := id + 1 }) "typed SZL wrong discriminator"
  for recordLength in [0, size - 1, size + 1, 65535] do
    check (rejected <| parse { good with recordLength := UInt16.ofNat recordLength })
      s!"typed SZL incoherent public record length {id}"
  for recordCount in [0, 2, 65535] do
    check (rejected <| parse { good with recordCount := UInt16.ofNat recordCount })
      s!"typed SZL incoherent public record count {id}"

/-- Exhaustive discriminator, permutation, bit/value, and malformed extent tests.
    Opaque bytes stay opaque: these tests do not invent constraints on flags,
    languages, force areas/reserved fields, or nonzero boolean encodings. -/
def run : IO Unit := do
  let counts := (List.range 7).foldl (fun wire index => wire ++ countRecord index) ByteArray.empty
  for order in permutations 7 (List.range 7) do
    let wire := order.foldl (fun wire index => wire ++ countRecord index) ByteArray.empty
    check (isExpected (S7.decodeBlockCounts wire) expectedCounts) "block-count permutation"
  for position in [:7] do
    for raw in [:256] do
      let code := UInt8.ofNat raw
      let changedPrefix := counts.set! (position * 4) code
      check ((isExpected (S7.decodeBlockCounts changedPrefix) expectedCounts) == (code == 0x30))
        s!"block-count marker {position}/{raw}"
      let discriminator := counts.set! (position * 4 + 1) code
      check ((isExpected (S7.decodeBlockCounts discriminator) expectedCounts) ==
        (code == (blockTypes[position]?.getD .organizationBlock).code))
        s!"block-count type or duplicate {position}/{raw}"
  for short in [:28] do
    check (rejected <| S7.decodeBlockCounts (counts.extract 0 short)) "truncated block-counts"
  for extra in [1:9] do
    check (rejected <| S7.decodeBlockCounts (counts ++ bytes (Array.replicate extra 0)))
      "trailing block-counts"
  for count in [:33] do
    let wire := (List.range count).foldl (fun wire index => wire ++ entryRecord index) ByteArray.empty
    let expected : Array S7.BlockEntry := (List.range count).toArray.map fun index => {
      number := UInt16.ofNat (index * 257 + 3), flags := UInt8.ofNat (index * 29),
      language := UInt8.ofNat (index * 71)
    }
    check (isExpected (S7.decodeBlockEntries wire) expected) s!"ordered block entries {count}"
    for size in [:wire.size] do
      let actual := S7.decodeBlockEntries (wire.extract 0 size)
      if size % 4 != 0 then
        check (rejected actual) "partial block-list record"
      else
        check (isExpected actual (expected.extract 0 (size / 4))) "aligned block-list prefix"
    for extra in [1, 2, 3] do
      check (rejected <| S7.decodeBlockEntries (wire ++ bytes (Array.replicate extra 0)))
        "partial appended block-list record"
  for raw in [:256] do
    let byte := UInt8.ofNat raw
    check (isExpected (S7.decodeBlockEntries (bytes #[0, 1, byte, byte, 0, 1, byte, byte])) #[
      { number := 1, flags := byte, language := byte },
      { number := 1, flags := byte, language := byte }]) "opaque flags/language and duplicate numbers"
  for short in [:78] do
    check (rejected <| S7.decodeBlockInfo (blockInfo.extract 0 short)) "truncated block metadata"
  for extra in [1:9] do
    check (rejected <| S7.decodeBlockInfo (blockInfo ++ bytes (Array.replicate extra 0)))
      "trailing block metadata"
  for raw in [:256] do
    let wire := blockInfo.set! 1 (UInt8.ofNat raw)
    match S7.decodeBlockInfo wire with
    | .error err => throw <| IO.userError s!"opaque block-info type rejected: {repr err}"
    | .ok result =>
      check (result.blockType == UInt8.ofNat raw && result.subBlockType == 11 &&
        result.codeDateRaw == bytes #[22, 23, 24, 25, 26, 27] &&
        result.interfaceDateRaw == bytes #[28, 29, 30, 31, 32, 33] &&
        result.number == 0x0c0d && result.loadSize == 0x0e0f1011 &&
        result.sbbSize == 0x2223 && result.localDataSize == 0x2627 && result.mc7Size == 0x2829 &&
        result.version == 66 && result.checksum == 0x4445) "block-info field offsets"
  for raw in [:256] do
    match S7.decodeBlockInfo (blockInfo.set! 11 (UInt8.ofNat raw)) with
    | .error err => throw <| IO.userError s!"opaque block-info subtype rejected: {repr err}"
    | .ok result =>
      check (result.blockType == 1 && result.subBlockType == UInt8.ofNat raw)
        "block-info distinct subtype field"
      check (isExpected (S7.correlateBlockInfo 0x0c0d result) result)
        "numeric correlation retains arbitrary subtype"
      for requested in [0, 1, 0x0c0c, 0x0c0e, 65535, 65536 + 0x0c0d, 99999] do
        check (rejected <| S7.correlateBlockInfo requested result)
          "block-info numeric mismatch or nontruncating high number"
  for number in [0, 1, 65534, 65535] do
    check (!(rejected <| S7.validateBlockInfoNumber number)) "supported block-info number"
  for number in [65536, 99999, 100000] do
    check (rejected <| S7.validateBlockInfoNumber number) "unsupported client block-info number"
  check (!(rejected <| S7.encodeGetBlockInfo 1 .dataBlock 99999))
    "five-digit low-level block-info request retained"
  check (rejected <| S7.encodeGetBlockInfo 1 .dataBlock 100000)
    "six-digit low-level block-info request rejected"
  for blockType in blockTypes do
    for (number, digits) in [(0, "00000"), (1, "00001"), (65535, "65535"), (99999, "99999")] do
      let expected := bytes #[0x32, 7, 0, 0, 0x12, 0x34, 0, 8, 0, 12,
        0, 1, 0x12, 4, 0x11, 0x43, 3, 0,
        0xff, 9, 0, 8, 0x30, blockType.code] ++ digits.toUTF8 ++ bytes #[0x41]
      match S7.encodeGetBlockInfo 0x1234 blockType number with
      | .ok actual => check (actual == expected) "native block-info ASCII number precedes final A"
      | .error err => throw <| IO.userError s!"block-info golden encoding rejected: {repr err}"
  for bit in [:256] do
    for value in [:256] do
      let wire := forceRecord (UInt8.ofNat bit) (UInt8.ofNat value)
      let actual := S7.decodeForceTable (forceSzl wire)
      if bit <= 7 then
        let expected : S7.ForceEntry := {
          areaCode := 0x1234, byteOffset := 0xabcd, bit := UInt8.ofNat bit, value := value != 0
        }
        check (isExpected actual #[expected]) "force-table bit/value"
      else
        check (rejected actual) "force-table invalid bit"
  let force := forceRecord 3 1 ++ forceRecord 7 0
  check (isExpected (S7.decodeForceTable (forceSzl force)) #[
    { areaCode := 0x1234, byteOffset := 0xabcd, bit := 3, value := true },
    { areaCode := 0x1234, byteOffset := 0xabcd, bit := 7, value := false }]) "force-table order"
  for size in [:force.size] do
    if size % 8 != 0 then
      check (rejected <| S7.decodeForceTable (forceSzl (force.extract 0 size))) "partial force entry"
  for id in [0, 0x24, 0x26, 0xffff] do
    check (rejected <| S7.decodeForceTable { forceSzl force with id }) "wrong force-table SZL"
  check (isExpected (S7.decodeForceTable (forceSzl ByteArray.empty)) #[]) "empty force-table"
  for recordLength in [0, 1, 7, 9, 16, 65535] do
    check (rejected <| S7.decodeForceTable { forceSzl force with recordLength })
      "inconsistent public force-table record length"
  for recordCount in [0, 1, 3, 65535] do
    check (rejected <| S7.decodeForceTable { forceSzl force with recordCount })
      "inconsistent public force-table record count"
  checkTyped 0x0011 26 S7.parseOrderCode
  checkTyped 0x001c 204 S7.parseCpuInfo
  checkTyped 0x0131 14 S7.parseCpInfo
  checkTyped 0x0232 12 S7.parseProtection
  checkTyped 0x0424 4 S7.parseCpuState
  -- The last three assembled bytes intentionally supply order-code versions,
  -- not the last three bytes of the first record (matching native Snap7).
  let order := { typedSzl 0x0011 52 with recordLength := 26, recordCount := 2 }
  match S7.parseOrderCode order with
  | .error err => throw <| IO.userError s!"multi-record order-code rejected: {repr err}"
  | .ok result => check (result.versionMajor == 49 && result.versionMinor == 50 &&
      result.versionPatch == 51) "order-code version source follows assembled extent"

end LeanS7.AdvancedDecoderAssuranceTests
