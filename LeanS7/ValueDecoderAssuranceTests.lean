import LeanS7.ValueDecoderAssurance

namespace LeanS7.ValueDecoderAssuranceTests

private def expect (actual expected : Except Value.Error String) (label : String) : IO Unit := do
  let same := match actual, expected with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false
  unless same do
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr actual}"

private def unitBytes (units : List UInt16) : ByteArray :=
  units.foldr (fun unit rest => uint16BE unit ++ rest) ByteArray.empty

private def wpacket (maximum : Nat) (units : List UInt16) (padding : ByteArray) : ByteArray :=
  uint16BE (UInt16.ofNat maximum) ++ uint16BE (UInt16.ofNat units.length) ++
    unitBytes units ++ padding

private def checkUnits (units : List UInt16) (expected : Except Value.Error String)
    (label : String) : IO Unit := do
  let pre := bytes #[0xff, 0x00, 0xda]
  let suffix := bytes #[0xdb, 0xff, 0xdc, 0x00, 0xff]
  expect (Value.decodeWString (wpacket units.length units ByteArray.empty)) expected label
  -- Malformed UTF16 in reserved padding and suffix must not affect interpretation.
  let padding := bytes #[0xd8, 0x00, 0xdc, 0x00]
  expect (Value.decodeWString (pre ++ (wpacket (units.length + 2) units padding ++ suffix))
    pre.size) expected s!"{label}: surrounding bytes"

private def invalid (offset : Nat) (message : String) : Except Value.Error String :=
  .error (.invalidUtf16 offset message)

/-- Exhaustive single UTF16 units, surrogate boundary pairs, malformed headers,
    incomplete allocations, offsets, and active/padding separation. -/
def run : IO Unit := do
  let pre := bytes #[0x71, 0x23, 0xab]
  for number in [:65536] do
    let unit := UInt16.ofNat number
    let expected := if number ≥ 0xd800 && number ≤ 0xdbff then
        invalid 0 "trailing high surrogate"
      else if number ≥ 0xdc00 && number ≤ 0xdfff then
        invalid 0 "unpaired low surrogate"
      else .ok (String.singleton (Char.ofNat number))
    checkUnits [unit] expected s!"single UTF16 unit {number}"
  for high in [0xd800:0xdc00] do
    for following in [0, 0xd7ff, 0xd800, 0xdbff, 0xe000, 0xffff] do
      let units := [UInt16.ofNat high, UInt16.ofNat following]
      checkUnits units (invalid 0 "high surrogate is not followed by a low surrogate")
        s!"invalid surrogate pair {high}/{following}"
      checkUnits (0x61 :: units) (invalid 1 "high surrogate is not followed by a low surrogate")
        s!"invalid surrogate pair after BMP {high}/{following}"
    for low in [0xdc00, 0xdc01, 0xdfff] do
      let scalar := 0x10000 + (high - 0xd800) * 0x400 + (low - 0xdc00)
      checkUnits [UInt16.ofNat high, UInt16.ofNat low]
        (.ok (String.singleton (Char.ofNat scalar))) s!"valid surrogate pair {high}/{low}"
  for low in [0xdc00:0xe000] do
    for high in [0xd800, 0xdbff] do
      let scalar := 0x10000 + (high - 0xd800) * 0x400 + (low - 0xdc00)
      checkUnits [UInt16.ofNat high, UInt16.ofNat low]
        (.ok (String.singleton (Char.ofNat scalar))) s!"valid surrogate pair {high}/{low}"
    checkUnits [0xd800, 0xdc00, UInt16.ofNat low] (invalid 2 "unpaired low surrogate")
      s!"unpaired low after valid pair {low}"
    checkUnits [0xd800, 0xdc00, UInt16.ofNat (low - 0x400)]
      (invalid 2 "trailing high surrogate") s!"trailing high after valid pair {low}"
  -- All malformed one-byte STRING header combinations, including capacity precedence.
  for maximum in [:256] do
    for current in [:256] do
      let packet := bytes #[UInt8.ofNat maximum, UInt8.ofNat current]
      if maximum > 254 then
        expect (Value.decodeString (pre ++ packet) pre.size)
          (.error (.invalidMaximumLength maximum 254)) s!"STRING capacity {maximum}/{current}"
      else if current > maximum then
        expect (Value.decodeString (pre ++ packet) pre.size)
          (.error (.invalidStringHeader current maximum)) s!"STRING current {maximum}/{current}"
      else if maximum > 0 then
        expect (Value.decodeString (pre ++ packet) pre.size)
          (.error (.decode (.unexpectedEnd (pre.size + 2) maximum 0)))
          s!"STRING missing allocation {maximum}/{current}"
      else
        expect (Value.decodeString (pre ++ packet) pre.size) (.ok "") "empty STRING"
  for number in [:256] do
    let packet := bytes #[1, 1, UInt8.ofNat number]
    expect (Value.decodeString (pre ++ packet) pre.size)
      (.ok (String.singleton (Char.ofNat number))) s!"Latin1 decode {number}"
  for maximum in [0, 1, 2, 16382, 16383, 32767, 65535] do
    for current in [0, 1, 2, 16382, 16383, 32767, 65535] do
      let packet := uint16BE (UInt16.ofNat maximum) ++ uint16BE (UInt16.ofNat current)
      if maximum > 16382 then
        expect (Value.decodeWString (pre ++ packet) pre.size)
          (.error (.invalidMaximumLength maximum 16382)) s!"WSTRING capacity {maximum}/{current}"
      else if current > maximum then
        expect (Value.decodeWString (pre ++ packet) pre.size)
          (.error (.invalidStringHeader current maximum)) s!"WSTRING current {maximum}/{current}"
      else if maximum > 0 then
        match Value.decodeWString (pre ++ packet) pre.size with
        | .error (.decode (.unexpectedEnd offset needed available)) =>
          unless offset == pre.size + 4 && available == 0 &&
              needed == (if current == 0 then maximum * 2 else 1) do
            throw <| IO.userError s!"WSTRING missing allocation {maximum}/{current}: wrong error"
        | other => throw <| IO.userError s!"WSTRING missing allocation accepted: {repr other}"
      else
        expect (Value.decodeWString (pre ++ packet) pre.size) (.ok "") "empty WSTRING"
  -- Active values fit, but at least one reserved byte is absent.
  for maximum in [1, 2, 3, 254] do
    let short := bytes #[UInt8.ofNat maximum, 0] ++
      ByteArray.mk (Array.replicate (maximum - 1) 0xff)
    expect (Value.decodeString (pre ++ short) pre.size)
      (.error (.decode (.unexpectedEnd (pre.size + 2) maximum (maximum - 1))))
      s!"STRING incomplete reserved allocation {maximum}"
  for maximum in [1, 2, 3, 16382] do
    let short := wpacket maximum [] (ByteArray.mk (Array.replicate (maximum * 2 - 1) 0xff))
    expect (Value.decodeWString (pre ++ short) pre.size)
      (.error (.decode (.unexpectedEnd (pre.size + 4) (maximum * 2) (maximum * 2 - 1))))
      s!"WSTRING incomplete reserved allocation {maximum}"
    let padding := ByteArray.mk (Array.replicate ((maximum - 1) * 2 - 1) 0xff)
    if maximum > 1 then
      expect (Value.decodeWString (pre ++ wpacket maximum [0x61] padding) pre.size)
        (.error (.decode (.unexpectedEnd (pre.size + 4) (maximum * 2) (maximum * 2 - 1))))
        s!"WSTRING nonempty incomplete reserved allocation {maximum}"
  for data in [ByteArray.empty, bytes #[0], bytes #[0, 0], bytes #[0, 0, 0]] do
    for offset in [0, data.size, data.size + 1, 100000, 4294967295] do
      if data.size < offset + 2 then
        match Value.decodeString data offset with
        | .error (.decode _) => pure ()
        | other => throw <| IO.userError s!"STRING truncated header accepted: {repr other}"
      match Value.decodeWString data offset with
      | .error (.decode _) => pure ()
      | other => throw <| IO.userError s!"WSTRING truncated header accepted: {repr other}"
  IO.println "Value decoder assurance: exhaustive UTF16 units, surrogate classes, headers, allocations, offsets, and padding isolation passed"

end LeanS7.ValueDecoderAssuranceTests
