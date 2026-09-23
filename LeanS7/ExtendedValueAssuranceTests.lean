import LeanS7.ValueCodecAssurance

namespace LeanS7.ExtendedValueAssuranceTests

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def value (result : Except Value.Error α) : IO α :=
  match result with
  | .ok item => pure item
  | .error error => throw <| IO.userError (reprStr error)

private def rejected (result : Except ε α) : Bool :=
  match result with | .error _ => true | .ok _ => false

private def pattern (size : Nat) (salt : Nat := 0) : ByteArray :=
  bytes <| (Array.range size).map fun index => UInt8.ofNat (index * 137 + salt)

private def checkFixed (encoded pre suffix : ByteArray) (read : ByteArray → Nat → Except Value.Error α)
    (expected : α) [BEq α] (name : String) : IO Unit := do
  ensure ((← value <| read (pre ++ (encoded ++ suffix)) pre.size) == expected)
    s!"{name} surrounded roundtrip failed at offset {pre.size}"
  for available in [:encoded.size] do
    ensure (rejected <| read (pre ++ encoded.extract 0 available) pre.size)
      s!"{name} accepted {available}/{encoded.size} bytes"
  ensure (rejected <| read (pre ++ encoded) (pre.size + encoded.size + 1))
    s!"{name} accepted offset beyond the buffer"

private def checkString (text : String) (maximum : Nat) (pre suffix : ByteArray) : IO Unit := do
  let encoded ← value <| Value.encodeString maximum text
  ensure (encoded.size == maximum + 2) "STRING allocation size differs from its capacity"
  ensure ((← value <| Value.decodeString (pre ++ (encoded ++ suffix)) pre.size) == text)
    "surrounded STRING roundtrip failed"
  ensure ((← value <| Value.getUInt8 encoded).toNat == maximum) "STRING capacity header changed"
  for available in [:encoded.size] do
    ensure (rejected <| Value.decodeString (pre ++ encoded.extract 0 available) pre.size)
      s!"STRING accepted truncated reserved storage: {available}/{encoded.size}"
  ensure (rejected <| Value.decodeString (pre ++ encoded) (pre.size + encoded.size + 1))
    "STRING accepted out-of-range offset"

private def checkWString (text : String) (maximum : Nat) (pre suffix : ByteArray) : IO Unit := do
  let encoded ← value <| Value.encodeWString maximum text
  ensure (encoded.size == maximum * 2 + 4) "WSTRING allocation size differs from UTF-16 capacity"
  ensure ((← value <| Value.decodeWString (pre ++ (encoded ++ suffix)) pre.size) == text)
    "surrounded WSTRING roundtrip failed"
  ensure ((← value <| Value.getUInt16 encoded).toNat == maximum) "WSTRING capacity header changed"
  for available in [:encoded.size] do
    ensure (rejected <| Value.decodeWString (pre ++ encoded.extract 0 available) pre.size)
      s!"WSTRING accepted truncated reserved storage: {available}/{encoded.size}"
  ensure (rejected <| Value.decodeWString (pre ++ encoded) (pre.size + encoded.size + 1))
    "WSTRING accepted out-of-range offset"

private def floatCases (pre suffix : ByteArray) : IO Unit := do
  -- The expected value is the interpretation of the bits actually encoded;
  -- there is deliberately no NaN equality or NaN-payload identity assertion.
  for bits in (#[0, 0x80000000, 1, 0x007fffff, 0x00800000, 0x3f800000,
      0x7f7fffff, 0x7f800000, 0xff800000, 0x7fc00001, 0x7f800001, 0xffc12345] : Array UInt32) do
    let number := Float32.ofBits bits
    let encoded := Value.putReal number
    let expected := Float32.ofBits (← value <| Value.getUInt32 encoded)
    let actual ← value <| Value.getReal (pre ++ (encoded ++ suffix)) pre.size
    ensure (actual.toBits == expected.toBits) "surrounded REAL bit interpretation changed"
    for available in [:4] do
      ensure (rejected <| Value.getReal (pre ++ encoded.extract 0 available) pre.size)
        "REAL accepted truncated bits"
  for bits in (#[0, 0x8000000000000000, 1, 0x000fffffffffffff, 0x0010000000000000,
      0x3ff0000000000000, 0x7fefffffffffffff, 0x7ff0000000000000,
      0xfff0000000000000, 0x7ff8000000000001, 0x7ff0000000000001,
      0xfff8123456789abc] : Array UInt64) do
    let number := Float.ofBits bits
    let encoded := Value.putLReal number
    let expected := Float.ofBits (← value <| Value.getUInt64 encoded)
    let actual ← value <| Value.getLReal (pre ++ (encoded ++ suffix)) pre.size
    ensure (actual.toBits == expected.toBits) "surrounded LREAL bit interpretation changed"
    for available in [:8] do
      ensure (rejected <| Value.getLReal (pre ++ encoded.extract 0 available) pre.size)
        "LREAL accepted truncated bits"

def run : IO Unit := do
  let edges32 : Array UInt32 := #[0, 1, 0xff, 0x100, 0xffff, 0x10000,
    0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff]
  let edges64 : Array UInt64 := #[0, 1, 0xffff, 0x10000, 0xffffffff, 0x100000000,
    0x7fffffffffffffff, 0x8000000000000000, 0xfffffffffffffffe, 0xffffffffffffffff]
  let generated32 := (Array.range 256).map fun index => UInt32.ofNat (index * 2654435761 + 2246822519)
  let generated64 := (Array.range 256).map fun index =>
    UInt64.ofNat (index * 11400714819323198485 + 14029467366897019727)
  let offsets := #[0, 1, 2, 3, 7, 8, 15, 31]
  let tails := #[0, 1, 7, 32]
  for offset in offsets do
    for tail in tails do
      let pre := pattern offset 19
      let suffix := pattern tail 211
      for unsigned in edges32 ++ generated32 do
        checkFixed (Value.putUInt32 unsigned) pre suffix (fun data start => Value.getUInt32 data start) unsigned "DWORD"
        checkFixed (Value.putInt32 unsigned.toInt32) pre suffix (fun data start => Value.getInt32 data start) unsigned.toInt32 "DINT"
      for unsigned in edges64 ++ generated64 do
        checkFixed (Value.putUInt64 unsigned) pre suffix (fun data start => Value.getUInt64 data start) unsigned "LWORD"
        checkFixed (Value.putInt64 unsigned.toInt64) pre suffix (fun data start => Value.getInt64 data start) unsigned.toInt64 "LINT"
      floatCases pre suffix
      checkString "" 0 pre suffix
      checkString "" 7 pre suffix
      checkString (String.ofList [Char.ofNat 0, Char.ofNat 0xff, 'A']) 7 pre suffix
      for text in #["", "A", "π", "漢", "😀", "A😀π", String.ofList [Char.ofNat 0x10000],
          String.ofList [Char.ofNat 0x10ffff], String.ofList [Char.ofNat 0]] do
        checkWString text 8 pre suffix
      checkWString "" 0 pre suffix
  let pre := pattern 5
  let suffix := pattern 3
  for codePoint in [:256] do
    let text := String.ofList [Char.ofNat codePoint]
    for maximum in #[1, 3, 254] do checkString text maximum pre suffix
  ensure (rejected <| Value.encodeString 255 "") "STRING accepted capacity 255"
  ensure (rejected <| Value.encodeString 1 "AB") "STRING accepted excess Latin1 content"
  for text in #["€", "😀"] do
    ensure (rejected <| Value.encodeString 254 text) "STRING accepted a non-Latin1 scalar"
  ensure (rejected <| Value.encodeWString 16383 "") "WSTRING accepted capacity 16383"
  ensure (rejected <| Value.encodeWString 1 "😀") "WSTRING counted astral content as one UTF-16 unit"
  checkWString "😀" 2 pre suffix
  checkWString (String.ofList [Char.ofNat 0x10ffff]) 2 pre suffix
  let latinLimit := String.ofList <| List.replicate 254 'ÿ'
  checkString latinLimit 254 pre suffix
  let wideLimit ← value <| Value.encodeWString 16382 "😀"
  ensure (wideLimit.size == 32768 && (← value <| Value.decodeWString wideLimit) == "😀")
    "maximum-capacity WSTRING failed"
  -- Malformed active UTF-16 is rejected, while unused storage is not decoded.
  let malformed : Array (List UInt16) := #[[0xd800], [0xdc00], [0xd800, 0x41],
    [0xd800, 0xd800], [0xdc00, 0xd800], [0xdbff, 0xe000]]
  for units in malformed do
    let body := units.foldl (fun out unit => out ++ uint16BE unit) ByteArray.empty
    let encoded := uint16BE (UInt16.ofNat units.length) ++ uint16BE (UInt16.ofNat units.length) ++ body
    ensure (rejected <| Value.decodeWString (pre ++ (encoded ++ suffix)) pre.size)
      "WSTRING accepted malformed active surrogate sequence"
  let unusedSurrogates := uint16BE 2 ++ uint16BE 0 ++ uint16BE 0xd800 ++ uint16BE 0xdc00
  ensure ((← value <| Value.decodeWString (pre ++ (unusedSurrogates ++ suffix)) pre.size) == "")
    "WSTRING interpreted unused UTF-16 storage"
  for malformedHeader in #[bytes #[2, 3, 0, 0, 0], bytes #[255, 0] ++ pattern 255] do
    ensure (rejected <| Value.decodeString (pre ++ (malformedHeader ++ suffix)) pre.size)
      "STRING accepted invalid header"
  for malformedHeader in #[uint16BE 2 ++ uint16BE 3 ++ pattern 6,
      uint16BE 16383 ++ uint16BE 0 ++ pattern 32766] do
    ensure (rejected <| Value.decodeWString (pre ++ (malformedHeader ++ suffix)) pre.size)
      "WSTRING accepted invalid header"
  IO.println "Extended value assurance: 32 surrounding layouts, DWORD/DINT/LWORD/LINT samples, IEEE edge bits, Latin1 and UTF-16 allocation/truncation tests passed"

end LeanS7.ExtendedValueAssuranceTests
