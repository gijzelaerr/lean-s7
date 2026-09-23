import LeanS7.S7Conformance
import LeanS7.Value
import LeanS7.UserDataAssembly

namespace LeanS7.ExpandedMutationTests

private def require (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"expanded mutation regression: {label}"

private def rejected (result : Except ε α) : Bool :=
  match result with | .error _ => true | .ok _ => false

/-- Every bit at every byte position, plus boundary substitutions. -/
private def mutations (packet : ByteArray) : Array (String × ByteArray) := Id.run do
  let mut result := #[]
  for index in [:packet.size] do
    for replacement in (#[0, 1, 2, 0x7f, 0x80, 0xff] : Array UInt8) do
      result := result.push (s!"byte {index} = {replacement}", packet.set! index replacement)
    for bit in [:8] do
      result := result.push (s!"byte {index}, bit {bit}",
        packet.set! index (UInt8.xor packet[index]! (UInt8.shiftLeft 1 (UInt8.ofNat bit))))
  return result

private def get (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error _ => throw <| IO.userError "could not create valid mutation seed"

private def exactBoundaries (name : String) (packet : ByteArray)
    (decode : ByteArray → Except ε α) : IO Nat := do
  require (!rejected (decode packet)) s!"{name}: valid seed"
  for length in [:packet.size] do
    require (rejected (decode (packet.extract 0 length))) s!"{name}: prefix {length}"
  for value in (#[0, 0xff] : Array UInt8) do
    require (rejected (decode (packet.push value))) s!"{name}: trailing {value}"
  return packet.size + 2

private def multiResponses : IO Nat := do
  let ranges : Array S7.MemoryRange := #[
    { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 },
    { area := .dataBlocks, dbNumber := 1, start := 1, count := 2 },
    { area := .dataBlocks, dbNumber := 1, start := 3, count := 3 }]
  let data := bytes #[0xff, 4, 0, 8, 0xaa, 0, 5, 0, 0, 0,
    0xff, 4, 0, 24, 0xbb, 0xcc, 0xdd]
  let packet ← get <| S7.encodeAckData 42 (bytes #[4, 3]) data
  let decode := fun raw => do S7.decodeAreaReadMany 42 ranges (← S7.decodeResponse raw)
  let mut count ← exactBoundaries "multi-read" packet decode
  for (label, changed) in mutations packet do
    if let .ok results := decode changed then
      require (results.size == ranges.size) s!"multi-read/{label}: result count"
      for index in [:ranges.size] do
        if let some (.success payload) := results[index]? then
          let some range := ranges[index]? | throw <| IO.userError "missing mutation range"
          require (payload.size == range.count) s!"multi-read/{label}: item {index} size"
    count := count + 1
  let packet ← get <| S7.encodeAckData 42 (bytes #[5, 3]) (bytes #[0xff, 5, 0xff])
  let decode := fun raw => do S7.decodeAreaWriteMany 42 3 (← S7.decodeResponse raw)
  count := count + (← exactBoundaries "multi-write" packet decode)
  for (label, changed) in mutations packet do
    if let .ok results := decode changed then
      require (results.size == 3) s!"multi-write/{label}: result count"
      for index in [:3] do
        let expected := if changed[14 + index]! == 0xff then S7.WriteItemResult.success
          else .failure changed[14 + index]!
        require (results[index]? == some expected) s!"multi-write/{label}: result order"
    count := count + 1
  return count

private def metadata : IO Nat := do
  let mut count := 0
  for seed in Conformance.S7.blockCountsCases do
    if let some _ := seed.expected then
      count := count + (← exactBoundaries "block-counts" seed.payload S7.decodeBlockCounts)
      for (label, changed) in mutations seed.payload do
        if let .ok _ := S7.decodeBlockCounts changed then
          let types := (List.range 7).map fun index => changed[index * 4 + 1]!
          require (types.eraseDups.length == 7) s!"block-counts/{label}: duplicate type"
        count := count + 1
  for seed in Conformance.S7.blockInfoCases do
    if let some _ := seed.expected then
      count := count + (← exactBoundaries "block-info" seed.payload S7.decodeBlockInfo)
      for (label, changed) in mutations seed.payload do
        if let .ok info := S7.decodeBlockInfo changed then
          let number ← get <| (Cursor.readUInt16BE { data := changed, offset := 12 }).map Prod.fst
          require (info.number == number && info.blockType == changed[1]! &&
            info.flags == changed[9]! && info.language == changed[10]!)
            s!"block-info/{label}: scalar fields"
          require (info.codeDateRaw == changed.extract 22 28 &&
            info.interfaceDateRaw == changed.extract 28 34) s!"block-info/{label}: raw date order"
        count := count + 1
  for seed in Conformance.S7.blockEntriesCases do
    if let some _ := seed.expected then
      -- Whole-record truncation remains a valid shorter list.
      for length in [:seed.payload.size + 2] do
        let changed := (seed.payload ++ bytes #[0xff]).extract 0 length
        require (rejected (S7.decodeBlockEntries changed) == (changed.size % 4 != 0))
          s!"block-list prefix {length}: record alignment"
        count := count + 1
      for (label, changed) in mutations seed.payload do
        let entries ← get <| S7.decodeBlockEntries changed
        require (entries.size * 4 == changed.size) s!"block-list/{label}: count"
        for index in [:entries.size] do
          let number ← get <| (Cursor.readUInt16BE { data := changed, offset := index * 4 }).map Prod.fst
          require (entries[index]!.number == number && entries[index]!.flags == changed[index * 4 + 2]!)
            s!"block-list/{label}: entry order"
        count := count + 1
  return count

private def clocks : IO Nat := do
  let mut count := 0
  for year in [1990, 2000, 2026, 2089] do
    let packet ← get <| S7.encodePlcDateTime {
      year, month := 2, day := if year == 2000 then 29 else 28,
      hour := 23, minute := 59, second := 59, millisecond := 999, weekday := 7 }
    count := count + (← exactBoundaries "clock" packet S7.decodePlcDateTime)
    for (label, changed) in mutations packet do
      if let .ok decoded := S7.decodePlcDateTime changed then
        require (!rejected decoded.validate) s!"clock/{label}: calendar validity"
        let encoded ← get <| S7.encodePlcDateTime decoded
        -- The leading two bytes are service metadata, not DATE_AND_TIME digits.
        require (encoded.extract 2 10 == changed.extract 2 10) s!"clock/{label}: BCD round trip"
      count := count + 1
  return count

private def strings : IO Nat := do
  let mut count := 0
  for value in ["", "A", "ABC", "éÿ"] do
    let packet ← get <| Value.encodeString 6 value
    for length in [:packet.size] do
      require (rejected (Value.decodeString (packet.extract 0 length))) "STRING truncated storage"
      count := count + 1
    for (label, changed) in mutations packet do
      if let .ok decoded := Value.decodeString changed then
        let encoded ← get <| Value.encodeString changed[0]!.toNat decoded
        require (encoded.extract 0 (2 + changed[1]!.toNat) ==
          changed.extract 0 (2 + changed[1]!.toNat)) s!"STRING/{label}: content/header round trip"
      count := count + 1
    require (match Value.decodeString (bytes #[0xee, 0xdd] ++ packet) 2 with
      | .ok decoded => decoded == value | .error _ => false)
      "STRING nonzero offset"
    require (rejected (Value.decodeString packet (packet.size + 1))) "STRING out-of-bounds offset"
    count := count + 2
  for value in ["", "A", "A🙂Ω", "🙂🙂"] do
    let packet ← get <| Value.encodeWString 8 value
    for length in [:packet.size] do
      require (rejected (Value.decodeWString (packet.extract 0 length))) "WSTRING truncated storage"
      count := count + 1
    for (label, changed) in mutations packet do
      if let .ok decoded := Value.decodeWString changed then
        let maximum ← get <| Value.getUInt16 changed
        let current ← get <| Value.getUInt16 changed 2
        let encoded ← get <| Value.encodeWString maximum.toNat decoded
        require (encoded.extract 0 (4 + current.toNat * 2) ==
          changed.extract 0 (4 + current.toNat * 2)) s!"WSTRING/{label}: UTF-16 round trip"
      count := count + 1
    require (match Value.decodeWString (bytes #[0xee, 0xdd] ++ packet) 2 with
      | .ok decoded => decoded == value | .error _ => false)
      "WSTRING nonzero offset"
    require (rejected (Value.decodeWString packet (packet.size + 1))) "WSTRING out-of-bounds offset"
    count := count + 2
  return count

private def sequences : IO Nat := do
  let mut count := 0
  for more0 in [false, true] do
    for more1 in [false, true] do
      for more2 in [false, true] do
        for size0 in [0, 1, 3, 4] do
          for size1 in [0, 1, 3, 4] do
            for size2 in [0, 1, 3, 4] do
              let mut state := UserDataAssembly.empty 5 3
              let mut expected := ByteArray.empty
              let mut stopped := false
              for (size, more) in [(size0, more0), (size1, more1), (size2, more2)] do
                let chunk := bytes (Array.replicate size (UInt8.ofNat state.count))
                let mustReject := stopped || expected.size + size > 5 ||
                  (more && state.count + 1 ≥ 3)
                let result := UserDataAssembly.accept state chunk more
                require (rejected result == mustReject) "continuation acceptance boundary"
                if let .ok step := result then
                  expected := expected ++ chunk
                  state := step.after
                  stopped := !more
                  require (state.data == expected && state.count ≤ 3 && state.data.size ≤ 5)
                    "continuation sequence order/bounds"
                count := count + 1
                if rejected result then break
  return count

def run : IO Unit := do
  let count := (← multiResponses) + (← metadata) + (← clocks) + (← strings) + (← sequences)
  IO.println s!"Expanded deterministic mutation checks passed ({count} cases)."

end LeanS7.ExpandedMutationTests
