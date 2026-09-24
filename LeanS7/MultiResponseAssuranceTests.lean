import LeanS7.MultiResponseAssurance

namespace LeanS7.MultiResponseAssuranceTests

private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw <| IO.userError label

private def response (function : UInt8) (count : Nat) (data : ByteArray) : S7.Response := {
  pduType := S7.ackDataType
  reference := 7
  parameters := bytes #[function, UInt8.ofNat count]
  data
  errorClass := 0
  errorCode := 0
}

private def rejected {α : Type} : Except DecodeError α → Bool
  | .error _ => true
  | .ok _ => false

private def range (area : S7.Area) (count : Nat) : S7.MemoryRange := {
  area, dbNumber := if area == .dataBlocks then 1 else 0, start := 0, count
}

private def payload (position size : Nat) : ByteArray :=
  bytes <| (List.range size).toArray.map fun offset => UInt8.ofNat (position * 29 + offset * 71)

private def readRecord (code transport : UInt8) (data : ByteArray) (more : Bool) : ByteArray :=
  let length := if transport == S7.octetTransportSize then data.size else data.size * 8
  bytes #[code, transport] ++ uint16BE (UInt16.ofNat length) ++ data ++
    if more && data.size % 2 != 0 then bytes #[0xa5] else ByteArray.empty

private def expectRead (ranges : Array S7.MemoryRange) (data : ByteArray)
    (expected : Array S7.ReadItemResult) (label : String) : IO Unit := do
  let actual := S7.decodeAreaReadMany 7 ranges (response S7.readFunction ranges.size data)
  check (match actual with | .ok results => results == expected | .error _ => false) label

private def expectWrite (count : Nat) (data : ByteArray)
    (expected : Array S7.WriteItemResult) (label : String) : IO Unit := do
  let actual := S7.decodeAreaWriteMany 7 count (response S7.writeFunction count data)
  check (match actual with | .ok results => results == expected | .error _ => false) label

/-- Ordered mixed-status responses, exact successful payload lengths, transport
    compatibility, truncation, count/parameter mismatch, and padding boundaries. -/
def run : IO Unit := do
  -- Every status byte in every possible result position, with distinct neighbors.
  -- 0xff alone succeeds; all other bytes remain position-preserving failures.
  for count in [1:21] do
    for position in [:count] do
      for number in [:256] do
        let wire := bytes <| (List.range count).toArray.map fun i =>
          if i == position then UInt8.ofNat number
          else if i % 2 == 0 then 0xff else UInt8.ofNat (i + 1)
        let expected := wire.data.map fun code =>
          if code == 0xff then S7.WriteItemResult.success else .failure code
        expectWrite count wire expected s!"write status {count}/{position}/{number}"
  for count in [1:21] do
    let data := payload count count
    for short in [:count] do
      check (rejected <| S7.decodeAreaWriteMany 7 count
        (response S7.writeFunction count (data.extract 0 short)))
        s!"write truncated statuses {count}/{short}"
    check (rejected <| S7.decodeAreaWriteMany 7 count
      (response S7.writeFunction count (data ++ bytes #[0xff])))
      s!"write trailing status {count}"
    check (rejected <| S7.decodeAreaWriteMany 7 count
      (response S7.writeFunction (count + 1) data)) s!"write mismatched count {count}"
  for count in [0, 21, 256, 65536] do
    check (rejected <| S7.decodeAreaWriteMany 7 count
      (response S7.writeFunction count ByteArray.empty)) s!"invalid write count {count}"
    check (rejected <| S7.decodeAreaReadMany 7
      ((List.replicate count (range .dataBlocks 1)).toArray)
      (response S7.readFunction count ByteArray.empty)) s!"invalid read count {count}"
  let areas : Array S7.Area := #[.processInputs, .processOutputs, .markers,
    .dataBlocks, .counters, .timers]
  for count in [1:21] do
    for mode in [:3] do
      let mut ranges := #[]
      let mut expected := #[]
      let mut wire := ByteArray.empty
      for position in [:count] do
        let area := areas[(position + mode) % areas.size]'(Nat.mod_lt _ (by decide))
        let elements := (position + mode) % 4
        let requested := range area elements
        let success := (position + mode) % 3 != 1
        let code := if success then 0xff else UInt8.ofNat (position + 1)
        -- Failed items may carry odd payloads too; their padding must not shift
        -- the next successful result. Padding content is intentionally opaque.
        let data := if success then payload position (elements * area.elementSize)
          else payload position (position % 2)
        let transport := if area.usesElementAddress && mode == 2 then S7.byteTransportSize
          else area.dataTransportSize
        ranges := ranges.push requested
        expected := expected.push <| if success then .success data else .failure code
        wire := wire ++ readRecord code transport data (position + 1 < count)
      expectRead ranges wire expected s!"ordered read {count}/{mode}"
      -- All strict prefixes and trailing bytes must fail, even if every item is
      -- a PLC failure. Successful decode cannot silently lose result positions.
      for short in [:wire.size] do
        check (rejected <| S7.decodeAreaReadMany 7 ranges
          (response S7.readFunction count (wire.extract 0 short)))
          s!"read truncated {count}/{mode}/{short}"
      check (rejected <| S7.decodeAreaReadMany 7 ranges
        (response S7.readFunction count (wire ++ bytes #[0])))
        s!"read trailing byte {count}/{mode}"
      check (rejected <| S7.decodeAreaReadMany 7 ranges
        (response S7.readFunction (count + 1) wire)) s!"read mismatched count {count}/{mode}"
  -- Exhaustive failed read status bytes before a successful odd-size item.
  for number in [:255] do
    let ranges := #[range .dataBlocks 1, range .markers 3]
    let data := payload 9 3
    let wire := readRecord (UInt8.ofNat number) 4 ByteArray.empty true ++
      readRecord 0xff 4 data false
    expectRead ranges wire #[.failure (UInt8.ofNat number), .success data]
      s!"read failure preserves following position {number}"
  -- Each area's accepted transport forms and exact requested element byte size.
  for area in areas do
    for count in [0, 1, 2, 3] do
      let requested := range area count
      let data := payload 5 (count * area.elementSize)
      let accepted := if area.usesElementAddress then #[S7.octetTransportSize, S7.byteTransportSize]
        else #[S7.byteTransportSize]
      for transport in accepted do
        expectRead #[requested] (readRecord 0xff transport data false) #[.success data]
          s!"transport compatibility {repr area}/{count}/{transport}"
        for wrongSize in [data.size + 1, data.size + 2] do
          let wire := readRecord 0xff transport (payload 5 wrongSize) false
          check (rejected <| S7.decodeAreaReadMany 7 #[requested]
            (response S7.readFunction 1 wire)) s!"read incorrect size {repr area}/{count}"
      for transport in [0, 1, 2, 3, 5, 7, 8, 10, 255] do
        let wire := readRecord 0xff (UInt8.ofNat transport) data false
        check (rejected <| S7.decodeAreaReadMany 7 #[requested]
          (response S7.readFunction 1 wire)) s!"read incorrect transport {repr area}/{transport}"
      -- Byte transport requires aligned bit lengths, also for counters/timers.
      let malformed := bytes #[0xff, 4] ++ uint16BE (UInt16.ofNat (data.size * 8 + 1)) ++ data
      check (rejected <| S7.decodeAreaReadMany 7 #[requested]
        (response S7.readFunction 1 malformed)) s!"unaligned read length {repr area}/{count}"
  let ranges := #[range .dataBlocks 1, range .dataBlocks 1]
  let first := readRecord 0xff 4 (bytes #[0x31]) false
  let second := readRecord 0xff 4 (bytes #[0x72]) false
  expectRead ranges (first ++ bytes #[0xff] ++ second) #[.success (bytes #[0x31]), .success (bytes #[0x72])]
    "nonzero inter-item padding is opaque"
  check (rejected <| S7.decodeAreaReadMany 7 ranges
    (response S7.readFunction 2 (first ++ second))) "missing inter-item padding"
  -- Correlation and parameter framing remain enforced around these contracts.
  for function in [0, 3, 5, 0xff] do
    check (rejected <| S7.decodeAreaReadMany 7 #[range .dataBlocks 1]
      (response function 1 (readRecord 0xff 4 (bytes #[1]) false))) "read wrong function"
  for function in [0, 3, 4, 0xff] do
    check (rejected <| S7.decodeAreaWriteMany 7 1 (response function 1 (bytes #[0xff])))
      "write wrong function"
  for parameters in [ByteArray.empty, bytes #[4], bytes #[4, 1, 0], bytes #[4, 0], bytes #[4, 2]] do
    check (rejected <| S7.decodeAreaReadMany 7 #[range .dataBlocks 1]
      { response 4 1 (readRecord 0xff 4 (bytes #[1]) false) with parameters })
      "read malformed parameters"
  for parameters in [ByteArray.empty, bytes #[5], bytes #[5, 1, 0], bytes #[5, 0], bytes #[5, 2]] do
    check (rejected <| S7.decodeAreaWriteMany 7 1
      { response 5 1 (bytes #[0xff]) with parameters }) "write malformed parameters"
  check (rejected <| S7.decodeAreaReadMany 8 #[range .dataBlocks 1]
    (response 4 1 (readRecord 0xff 4 (bytes #[1]) false))) "read mismatched reference"
  check (rejected <| S7.decodeAreaWriteMany 8 1 (response 5 1 (bytes #[0xff])))
    "write mismatched reference"

end LeanS7.MultiResponseAssuranceTests
