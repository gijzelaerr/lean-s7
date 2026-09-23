import LeanS7.Value

namespace LeanS7.NonemptyStringAssuranceTests

private def rejected (result : Except α β) : Bool :=
  match result with | .error _ => true | .ok _ => false

private def checkString (pre suffix : ByteArray) (maximum : Nat) (value : String) : IO Unit := do
  let .ok encoded := Value.encodeString maximum value
    | throw <| IO.userError s!"Latin-1 encoding failed: {repr value}"
  unless encoded.size == maximum + 2 do
    throw <| IO.userError "STRING failed to reserve its full declared capacity"
  let .ok actual := Value.decodeString (pre ++ (encoded ++ suffix)) pre.size
    | throw <| IO.userError "surrounded nonempty STRING decoding failed"
  unless actual == value do
    throw <| IO.userError s!"surrounded nonempty STRING changed: {repr value}"
  if maximum > 0 then
    let truncated := encoded.extract 0 (encoded.size - 1)
    unless rejected (Value.decodeString (pre ++ truncated) pre.size) do
      throw <| IO.userError "STRING accepted incomplete declared storage"

private def checkWString (pre suffix : ByteArray) (maximum : Nat) (value : String) : IO Unit := do
  let .ok encoded := Value.encodeWString maximum value
    | throw <| IO.userError s!"Unicode encoding failed: {repr value}"
  unless encoded.size == maximum * 2 + 4 do
    throw <| IO.userError "WSTRING failed to reserve its full declared capacity"
  let .ok actual := Value.decodeWString (pre ++ (encoded ++ suffix)) pre.size
    | throw <| IO.userError "surrounded nonempty WSTRING decoding failed"
  unless actual == value do
    throw <| IO.userError s!"surrounded nonempty WSTRING changed: {repr value}"
  if maximum > 0 then
    let truncated := encoded.extract 0 (encoded.size - 1)
    unless rejected (Value.decodeWString (pre ++ truncated) pre.size) do
      throw <| IO.userError "WSTRING accepted incomplete declared storage"

def run : IO Unit := do
  let pre := bytes #[0x11,0x22,0x33,0x44,0x55]
  let suffix := bytes #[0xde,0xad,0xbe,0xef]
  -- Every supported Latin-1 code point, including embedded zero and 0xff.
  for number in [:256] do
    let value := String.singleton (Char.ofNat number)
    for maximum in #[1,2,254] do
      checkString pre suffix maximum value
  let latin1 := String.ofList ((List.range 254).map Char.ofNat)
  checkString pre suffix 254 latin1
  checkString (bytes #[]) (bytes #[]) 17 "classic S7"
  unless rejected (Value.encodeString 8 "Ā") do
    throw <| IO.userError "STRING accepted a non-Latin-1 character"
  unless rejected (Value.encodeString 1 "ab") do
    throw <| IO.userError "STRING accepted a value beyond capacity"
  -- All valid BMP code points; surrogate values are not Unicode characters.
  for number in [:65536] do
    if number < 0xd800 || number > 0xdfff then
      checkWString pre suffix 2 (String.singleton (Char.ofNat number))
  -- Exercise every high-surrogate value and every low-surrogate value, paired
  -- at both boundaries. Mixed values check active-unit rather than char counts.
  for part in [:1024] do
    for scalar in #[0x10000 + part * 1024, 0x10000 + part * 1024 + 1023,
        0x10000 + part, 0x10fc00 + part] do
      checkWString pre suffix 3 (String.singleton (Char.ofNat scalar))
  for value in #[String.ofList [Char.ofNat 0, 'S', '7', Char.ofNat 255], "Āλ漢字",
      "😀𝄞" ++ String.singleton (Char.ofNat 0x10ffff), "a😀漢𝄞z"] do
    checkWString pre suffix (Value.utf16Length value) value
    checkWString pre suffix (Value.utf16Length value + 7) value
  checkWString (bytes #[]) (bytes #[]) Value.maxWStringLength "S7😀"
  unless Value.utf16Length "a😀漢𝄞z" == 7 do
    throw <| IO.userError "supplementary Unicode length was not counted in UTF-16 units"
  unless rejected (Value.encodeWString 1 "😀") do
    throw <| IO.userError "WSTRING treated a surrogate pair as one capacity unit"
  for units in (#[#[0xd800], #[0xdc00], #[0xd800,0x0041], #[0xdc00,0xd800],
      #[0xd800,0xd800], #[0xdfff]] : Array (Array UInt16)) do
    let storage := units.foldl (fun data unit => data ++ uint16BE unit) (bytes #[])
    let malformed := uint16BE (UInt16.ofNat units.size) ++
      uint16BE (UInt16.ofNat units.size) ++ storage
    unless rejected (Value.decodeWString (pre ++ (malformed ++ suffix)) pre.size) do
      throw <| IO.userError "WSTRING accepted malformed UTF-16 surrogate content"
  IO.println "Nonempty string assurance: all Latin-1 and valid BMP values, 4,096 supplementary boundaries, mixed values, allocation and malformed-surrogate checks passed"

end LeanS7.NonemptyStringAssuranceTests
