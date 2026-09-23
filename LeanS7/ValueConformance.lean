import Lean.Data.Json
import LeanS7.Value
import LeanS7.Management

namespace LeanS7.Conformance.Values
open Lean

/-- Compact byte specifications keep maximum-capacity strings portable without
    putting tens of thousands of padding zeros into the corpus. -/
private def octets (data : ByteArray) : Json := Id.run do
  let mut chunks : Array Json := #[]
  let mut pending : Array UInt8 := #[]
  let mut index := 0
  while index < data.size do
    let byte := data.data.getD index 0
    let mut stop := index + 1
    while stop < data.size && data.data.getD stop 0 == byte do
      stop := stop + 1
    if stop - index ≥ 8 then
      if !pending.isEmpty then
        chunks := chunks.push <| Json.mkObj [("bytes", toJson (pending.map UInt8.toNat))]
        pending := #[]
      chunks := chunks.push <| Json.mkObj [("repeat", Json.mkObj [
        ("byte", toJson byte.toNat), ("count", toJson (stop - index))])]
    else
      pending := pending ++ (data.extract index stop).data
    index := stop
  if !pending.isEmpty then
    chunks := chunks.push <| Json.mkObj [("bytes", toJson (pending.map UInt8.toNat))]
  return Json.mkObj [("chunks", Json.arr chunks)]

private def reject (category : String) : Json :=
  Json.mkObj [("status", "reject"), ("category", toJson category)]
private def accept (fields : List (String × Json)) : Json :=
  Json.mkObj (("status", toJson "accept") :: fields)
private def pre : ByteArray := bytes #[0x71,0x52,0x33]
private def suffix : ByteArray := bytes #[0xde,0xad]
private def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

structure IntegerCase where
  id : String
  codec : String
  pattern : Nat
  wire : ByteArray
  value : String
  truncated : Bool := false

private def integerData (test : IntegerCase) : ByteArray :=
  if test.truncated then pre ++ test.wire.extract 0 (test.wire.size - 1)
  else pre ++ (test.wire ++ suffix)

private def integerExpected (test : IntegerCase) : Json :=
  if test.truncated then reject "truncated-value"
  else accept [("encoded", octets test.wire), ("value", toJson test.value)]

private def integerResult (test : IntegerCase) : Json := Id.run do
  let data := integerData test
  let decoded : Except Value.Error String := match test.codec with
    | "uint8" => toString <$> Value.getUInt8 data pre.size
    | "uint16" => toString <$> Value.getUInt16 data pre.size
    | "uint32" => toString <$> Value.getUInt32 data pre.size
    | "uint64" => toString <$> Value.getUInt64 data pre.size
    | "int8" => toString <$> Value.getInt8 data pre.size
    | "int16" => toString <$> Value.getInt16 data pre.size
    | "int32" => toString <$> Value.getInt32 data pre.size
    | "int64" => toString <$> Value.getInt64 data pre.size
    | _ => .error (.invalidCharacter 0)
  let .ok value := decoded | return reject "truncated-value"
  let encoded := match test.codec with
    | "uint8" => Value.putUInt8 (UInt8.ofNat test.pattern)
    | "uint16" => Value.putUInt16 (UInt16.ofNat test.pattern)
    | "uint32" => Value.putUInt32 (UInt32.ofNat test.pattern)
    | "uint64" => Value.putUInt64 (UInt64.ofNat test.pattern)
    | "int8" => Value.putInt8 (UInt8.ofNat test.pattern).toInt8
    | "int16" => Value.putInt16 (UInt16.ofNat test.pattern).toInt16
    | "int32" => Value.putInt32 (UInt32.ofNat test.pattern).toInt32
    | "int64" => Value.putInt64 (UInt64.ofNat test.pattern).toInt64
    | _ => ByteArray.empty
  return accept [("encoded", octets encoded), ("value", toJson value)]

def integerCases : Array IntegerCase := Id.run do
  let golden : Array IntegerCase := #[
    ⟨"uint8-zero", "uint8", 0, bytes #[0], "0", false⟩,
    ⟨"uint8-maximum", "uint8", 255, bytes #[255], "255", false⟩,
    ⟨"uint16-byte-order", "uint16", 0x1234, bytes #[0x12,0x34], "4660", false⟩,
    ⟨"uint16-maximum", "uint16", 65535, bytes #[255,255], "65535", false⟩,
    ⟨"uint32-byte-order", "uint32", 0x12345678, bytes #[0x12,0x34,0x56,0x78], "305419896", false⟩,
    ⟨"uint32-maximum", "uint32", 4294967295, bytes #[255,255,255,255], "4294967295", false⟩,
    ⟨"uint64-byte-order", "uint64", 0x0123456789abcdef,
      bytes #[1,0x23,0x45,0x67,0x89,0xab,0xcd,0xef], "81985529216486895", false⟩,
    ⟨"uint64-maximum", "uint64", 18446744073709551615,
      bytes #[255,255,255,255,255,255,255,255], "18446744073709551615", false⟩,
    ⟨"int8-minimum", "int8", 128, bytes #[128], "-128", false⟩,
    ⟨"int8-maximum", "int8", 127, bytes #[127], "127", false⟩,
    ⟨"int16-minimum", "int16", 32768, bytes #[128,0], "-32768", false⟩,
    ⟨"int16-maximum", "int16", 32767, bytes #[127,255], "32767", false⟩,
    ⟨"int32-minimum", "int32", 2147483648, bytes #[128,0,0,0], "-2147483648", false⟩,
    ⟨"int32-maximum", "int32", 2147483647, bytes #[127,255,255,255], "2147483647", false⟩,
    ⟨"int64-minimum", "int64", 9223372036854775808,
      bytes #[128,0,0,0,0,0,0,0], "-9223372036854775808", false⟩,
    ⟨"int64-maximum", "int64", 9223372036854775807,
      bytes #[127,255,255,255,255,255,255,255], "9223372036854775807", false⟩,
    ⟨"int64-negative-one", "int64", 18446744073709551615,
      bytes #[255,255,255,255,255,255,255,255], "-1", false⟩ ]
  return golden ++ golden.map fun test =>
    { test with id := test.id ++ "-truncated", truncated := true }

structure StringCase where
  id : String
  wide : Bool
  maximum : Nat
  input : Option String
  wire : ByteArray
  expected : Json
  trailing : ByteArray := suffix

private def stringAccepted (wire : ByteArray) (value : String) (encode : Bool) : Json :=
  accept <| (if encode then [("encoded", octets wire)] else []) ++ [("value", toJson value)]

private def stringResult (test : StringCase) : Json := Id.run do
  let mut fields : List (String × Json) := []
  if let some input := test.input then
    let .ok encoded := if test.wide then Value.encodeWString test.maximum input
      else Value.encodeString test.maximum input | return reject "encode-value"
    fields := [("encoded", octets encoded)]
  let data := pre ++ (test.wire ++ test.trailing)
  let .ok value := if test.wide then Value.decodeWString data pre.size
    else Value.decodeString data pre.size | return reject "value-codec"
  return accept (fields ++ [("value", toJson value)])

private def stringRoundtrip (id : String) (wide : Bool) (maximum : Nat)
    (input : String) (wire : ByteArray) : StringCase :=
  { id, wide, maximum, input := some input, wire,
    expected := stringAccepted wire input true }
private def stringDecodeReject (id : String) (wide : Bool) (wire : ByteArray)
    (trailing : ByteArray := suffix) : StringCase :=
  { id, wide, maximum := 0, input := none, wire, trailing,
    expected := reject "value-codec" }
private def stringEncodeReject (id : String) (wide : Bool) (maximum : Nat)
    (input : String) : StringCase :=
  { id, wide, maximum, input := some input, wire := ByteArray.empty,
    expected := reject "encode-value" }

def stringCases : Array StringCase := #[
  stringRoundtrip "string-empty" false 0 "" (bytes #[0,0]),
  stringRoundtrip "string-latin1-nul" false 5
    (String.ofList [Char.ofNat 0,'A',Char.ofNat 127,Char.ofNat 255])
    (bytes #[5,4,0,65,127,255,0]),
  stringRoundtrip "string-maximum-padding" false 254 (String.singleton (Char.ofNat 255))
    (bytes #[254,1,255] ++ zeros 253),
  stringRoundtrip "string-full-capacity" false 254
    (String.ofList ((List.range 254).map Char.ofNat))
    (bytes #[254,254] ++ ByteArray.mk ((Array.range 254).map UInt8.ofNat)),
  stringRoundtrip "wstring-empty" true 0 "" (bytes #[0,0,0,0]),
  stringRoundtrip "wstring-first-astral" true 2 (String.singleton (Char.ofNat 0x10000))
    (bytes #[0,2,0,2,0xd8,0,0xdc,0]),
  stringRoundtrip "wstring-last-scalar" true 2 (String.singleton (Char.ofNat 0x10ffff))
    (bytes #[0,2,0,2,0xdb,255,0xdf,255]),
  stringRoundtrip "wstring-surrogate-pair" true 2 "😀"
    (bytes #[0,2,0,2,0xd8,0x3d,0xde,0]),
  stringRoundtrip "wstring-bmp-surrogate-gap" true 3
    (String.ofList [Char.ofNat 0xd7ff,Char.ofNat 0xe000,Char.ofNat 0xffff])
    (bytes #[0,3,0,3,0xd7,255,0xe0,0,255,255]),
  stringRoundtrip "wstring-embedded-nul" true 3
    (String.ofList ['A',Char.ofNat 0,'Z']) (bytes #[0,3,0,3,0,65,0,0,0,90]),
  stringRoundtrip "wstring-mixed-padding" true 6 "a😀漢"
    (bytes #[0,6,0,4,0,0x61,0xd8,0x3d,0xde,0,0x6f,0x22,0,0,0,0]),
  stringRoundtrip "wstring-maximum-padding" true Value.maxWStringLength "😀"
    (bytes #[0x3f,0xfe,0,2,0xd8,0x3d,0xde,0] ++ zeros ((Value.maxWStringLength - 2) * 2)),
  stringEncodeReject "string-capacity-overflow" false 255 "",
  stringEncodeReject "string-active-overflow" false 1 "ab",
  stringEncodeReject "string-non-latin1" false 2 "Ā",
  stringEncodeReject "wstring-capacity-overflow" true 16383 "",
  stringEncodeReject "wstring-unit-overflow" true 1 "😀",
  stringDecodeReject "string-short-header" false (bytes #[3]) ByteArray.empty,
  stringDecodeReject "string-short-allocation" false (bytes #[3,1,65,0]) ByteArray.empty,
  stringDecodeReject "string-current-overflow" false (bytes #[1,2,65]),
  stringDecodeReject "string-declared-overflow" false (bytes #[255,0]),
  stringDecodeReject "wstring-short-header" true (bytes #[0,3,0]) ByteArray.empty,
  stringDecodeReject "wstring-short-allocation" true (bytes #[0,3,0,1,0,65,0,0]) ByteArray.empty,
  stringDecodeReject "wstring-current-overflow" true (bytes #[0,1,0,2,0,65]),
  stringDecodeReject "wstring-declared-overflow" true (bytes #[0x3f,255,0,0]),
  stringDecodeReject "wstring-unpaired-high" true (bytes #[0,1,0,1,0xd8,0]),
  stringDecodeReject "wstring-unpaired-low" true (bytes #[0,1,0,1,0xdc,0]),
  stringDecodeReject "wstring-high-before-ascii" true (bytes #[0,2,0,2,0xd8,0,0,65]),
  stringDecodeReject "wstring-high-before-high" true (bytes #[0,2,0,2,0xd8,0,0xd8,1]),
  stringDecodeReject "wstring-trailing-low" true (bytes #[0,3,0,3,0xd8,0x3d,0xde,0,0xdc,0]) ]

private def dateJson (value : S7.PlcDateTime) : Json := Json.mkObj [
  ("year", toJson value.year), ("month", toJson value.month), ("day", toJson value.day),
  ("hour", toJson value.hour), ("minute", toJson value.minute), ("second", toJson value.second),
  ("millisecond", toJson value.millisecond), ("weekday", toJson value.weekday)]

structure ClockCase where
  id : String
  input : Option S7.PlcDateTime
  wire : ByteArray
  expected : Json

private def clockResult (test : ClockCase) : Json := Id.run do
  let mut fields : List (String × Json) := []
  if let some input := test.input then
    let .ok encoded := S7.encodePlcDateTime input | return reject "encode-clock"
    fields := [("encoded", octets encoded)]
  let .ok value := S7.decodePlcDateTime test.wire | return reject "clock-validation"
  return accept (fields ++ [("value", dateJson value)])

private def baseClock : S7.PlcDateTime := {
  year := 2026, month := 9, day := 23, hour := 12, minute := 34, second := 56,
  millisecond := 129, weekday := 3 }
private def baseClockWire : ByteArray := bytes #[0,0x19,0x26,0x09,0x23,0x12,0x34,0x56,0x12,0x93]

private def clockGolden (value : S7.PlcDateTime) : ByteArray :=
  let bcd := fun n => UInt8.ofNat ((n / 10) * 16 + n % 10)
  bytes #[0,0x19,bcd (value.year % 100),bcd value.month,bcd value.day,bcd value.hour,
    bcd value.minute,bcd value.second,bcd (value.millisecond / 10),
    UInt8.ofNat ((value.millisecond % 10) * 16 + value.weekday)]

def clockCases : Array ClockCase := Id.run do
  let mut cases : Array ClockCase := #[]
  let good : Array S7.PlcDateTime := #[
    { baseClock with
      year := 1990, month := 1, day := 1, hour := 0, minute := 0,
      second := 0, millisecond := 0, weekday := 1 },
    { baseClock with year := 1999, month := 12, day := 31, millisecond := 1 },
    { baseClock with year := 2000, month := 2, day := 29, millisecond := 9 },
    { baseClock with year := 2024, month := 2, day := 29, millisecond := 10 },
    { baseClock with millisecond := 99 }, { baseClock with millisecond := 100 },
    { baseClock with
      year := 2089, month := 12, day := 31, hour := 23, minute := 59,
      second := 59, millisecond := 999, weekday := 7 } ]
  for (value, index) in good.toList.zipIdx do
    let wire := clockGolden value
    cases := cases.push {
      id := s!"clock-roundtrip-{index}", input := some value, wire,
      expected := accept [("encoded", octets wire), ("value", dateJson value)] }
  for index in [2:9] do
    for digit in [10:16] do
      for high in #[false,true] do
        let byte := baseClockWire.data.getD index 0
        let invalid := UInt8.ofNat (if high then digit * 16 + byte.toNat % 16
          else byte.toNat / 16 * 16 + digit)
        let wire := baseClockWire.set! index invalid
        cases := cases.push {
          id := s!"clock-bcd-{index}-{high}-{digit}", input := none, wire,
          expected := reject "clock-validation" }
  for digit in [10:16] do
    cases := cases.push {
      id := s!"clock-millisecond-low-bcd-{digit}", input := none,
      wire := baseClockWire.set! 9 (UInt8.ofNat (digit * 16 + 3)),
      expected := reject "clock-validation" }
  for weekday in #[0,8,9,10,11,12,13,14,15] do
    cases := cases.push {
      id := s!"clock-weekday-{weekday}", input := none,
      wire := baseClockWire.set! 9 (UInt8.ofNat (0x90 + weekday)),
      expected := reject "clock-validation" }
  for count in [:10] do
    cases := cases.push {
      id := s!"clock-truncated-{count}", input := none,
      wire := baseClockWire.extract 0 count, expected := reject "clock-validation" }
  cases := cases.push {
    id := "clock-trailing-byte", input := none,
    wire := baseClockWire ++ bytes #[0], expected := reject "clock-validation" }
  let bad : Array S7.PlcDateTime := #[
    { baseClock with year := 1989 }, { baseClock with year := 2090 },
    { baseClock with year := 2001, month := 2, day := 29 },
    { baseClock with month := 4, day := 31 }, { baseClock with month := 0 },
    { baseClock with month := 13 }, { baseClock with day := 0 }, { baseClock with day := 32 },
    { baseClock with hour := 24 }, { baseClock with minute := 60 },
    { baseClock with second := 60 }, { baseClock with millisecond := 1000 },
    { baseClock with weekday := 0 }, { baseClock with weekday := 8 } ]
  for (value, index) in bad.toList.zipIdx do
    cases := cases.push {
      id := s!"clock-invalid-input-{index}", input := some value,
      wire := clockGolden value, expected := reject "encode-clock" }
    -- Out-of-range full years cannot be represented distinctly on the wire:
    -- e.g. 1989's two-digit 89 decodes as the supported year 2089.
    if 1990 ≤ value.year && value.year ≤ 2089 then
      cases := cases.push {
        id := s!"clock-invalid-decoded-{index}", input := none,
        wire := clockGolden value, expected := reject "clock-validation" }
  return cases

private def integerJson (test : IntegerCase) : Json := Json.mkObj [
  ("id", toJson test.id), ("codec", toJson test.codec), ("input_value", toJson test.value),
  ("data", octets (integerData test)), ("offset", toJson pre.size),
  ("expected", integerExpected test)]
private def stringJson (test : StringCase) : Json := Json.mkObj [
  ("id", toJson test.id), ("encoding", toJson (if test.wide then "utf-16-be" else "latin-1")),
  ("operation", toJson (if test.input.isSome then "roundtrip" else "decode")),
  ("maximum", toJson test.maximum), ("input_value", toJson test.input),
  ("data", octets (pre ++ (test.wire ++ test.trailing))), ("offset", toJson pre.size),
  ("expected", test.expected)]
private def clockJson (test : ClockCase) : Json := Json.mkObj [
  ("id", toJson test.id),
  ("operation", toJson (if test.input.isSome then "roundtrip" else "decode")),
  ("input_value", match test.input with | none => Json.null | some value => dateJson value),
  ("data", octets test.wire), ("expected", test.expected)]

def corpus : Json := Json.mkObj [
  ("schema_version", toJson (1 : Nat)), ("protocol", toJson "classic S7 typed values and clock"),
  ("integer_cases", Json.arr (integerCases.map integerJson)),
  ("string_codec_cases", Json.arr (stringCases.map stringJson)),
  ("clock_codec_cases", Json.arr (clockCases.map clockJson))]

def validate : IO Unit := do
  let mut ids : List String := []
  for test in integerCases do
    if ids.contains test.id then throw <| IO.userError s!"duplicate value case: {test.id}"
    ids := test.id :: ids
    unless integerResult test == integerExpected test do
      throw <| IO.userError s!"integer corpus expectation failed: {test.id}"
  for test in stringCases do
    if ids.contains test.id then throw <| IO.userError s!"duplicate value case: {test.id}"
    ids := test.id :: ids
    unless stringResult test == test.expected do
      throw <| IO.userError s!"string corpus expectation failed: {test.id}"
  for test in clockCases do
    if ids.contains test.id then throw <| IO.userError s!"duplicate value case: {test.id}"
    ids := test.id :: ids
    unless clockResult test == test.expected do
      throw <| IO.userError s!"clock corpus expectation failed: {test.id}"

end LeanS7.Conformance.Values
