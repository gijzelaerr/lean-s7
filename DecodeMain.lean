import LeanS7

/-! Decoder oracle for differential testing (`integration/python_snap7_fuzz.py`).
Reads one request per line from stdin (`-` stands for empty hex) and prints one verdict per line:

  userdata REF GROUP SUB HEX   -> accept SEQUENCE MORE PAYLOADHEX
  upload REF HEX               -> accept LAST PAYLOADHEX
  read REF SIZE HEX            -> accept PAYLOADHEX         (DB area, SIZE bytes)
  blockcounts HEX              -> accept O F C SF SC DB SDB (payload of a USER_DATA response)
  blocklist HEX                -> accept NUMBER NUMBER ...
  blockinfo HEX                -> accept NUMBER MC7 LOAD LOCAL SBB CHECKSUM VERSION FLAGS LANGUAGE
  clock HEX                    -> accept YEAR MONTH DAY HOUR MINUTE SECOND MILLISECOND WEEKDAY

Anything the decoders refuse prints `reject`. Not part of the library import graph. -/

open LeanS7

private def hexValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def fromHex (text : String) : Option ByteArray :=
  let digits := (if text == "-" then "" else text).toList
  if digits.length % 2 != 0 then none
  else
    let rec go : List Char → ByteArray → Option ByteArray
      | high :: low :: rest, acc => do
        let h ← hexValue high
        let l ← hexValue low
        go rest (acc.push (UInt8.ofNat (h * 16 + l)))
      | _, acc => some acc
    go digits ByteArray.empty

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

private def toHex (data : ByteArray) : String :=
  String.ofList <| data.toList.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

private def verdict (fields : List String) : String := String.intercalate " " ("accept" :: fields)

private def run (line : String) : String :=
  let parts := (line.splitOn " ").filter (· != "")
  let payload (text : String) : Option ByteArray := fromHex text
  match parts with
  | ["userdata", reference, group, sub, hex] =>
    match reference.toNat?, group.toNat?, sub.toNat?, payload hex with
    | some r, some g, some s, some pdu =>
      match S7.decodeUserDataResponse (UInt16.ofNat r) (UInt8.ofNat g) (UInt8.ofNat s) pdu with
      | .ok response => verdict [toString response.sequence, if response.hasMoreData then "1" else "0",
          toHex response.payload]
      | .error _ => "reject"
    | _, _, _, _ => "reject"
  | ["upload", reference, hex] =>
    match reference.toNat?, payload hex with
    | some r, some pdu =>
      match S7.decodeResponse pdu with
      | .error _ => "reject"
      | .ok response =>
        match S7.decodeUploadFragment (UInt16.ofNat r) response with
        | .ok fragment => verdict [if fragment.isLast then "1" else "0", toHex fragment.data]
        | .error _ => "reject"
    | _, _ => "reject"
  | ["read", reference, size, hex] =>
    match reference.toNat?, size.toNat?, payload hex with
    | some r, some n, some pdu =>
      match S7.decodeResponse pdu with
      | .error _ => "reject"
      | .ok response =>
        match S7.decodeAreaRead (UInt16.ofNat r) .dataBlocks n response with
        | .ok data => verdict [toHex data]
        | .error _ => "reject"
    | _, _, _ => "reject"
  | ["blockcounts", hex] =>
    match payload hex with
    | some data =>
      match S7.decodeBlockCounts data with
      | .ok c => verdict [toString c.organizationBlocks, toString c.functionBlocks, toString c.functions,
          toString c.systemFunctionBlocks, toString c.systemFunctions, toString c.dataBlocks,
          toString c.systemDataBlocks]
      | .error _ => "reject"
    | none => "reject"
  | ["blocklist", hex] =>
    match payload hex with
    | some data =>
      match S7.decodeBlockEntries data with
      | .ok entries => verdict (entries.toList.map fun e => toString e.number)
      | .error _ => "reject"
    | none => "reject"
  | ["blockinfo", hex] =>
    match payload hex with
    | some data =>
      match S7.decodeBlockInfo data with
      | .ok i => verdict [toString i.number, toString i.mc7Size, toString i.loadSize,
          toString i.localDataSize, toString i.sbbSize, toString i.checksum, toString i.version,
          toString i.flags, toString i.language]
      | .error _ => "reject"
    | none => "reject"
  | ["clock", hex] =>
    match payload hex with
    | some data =>
      match S7.decodePlcDateTime data with
      | .ok t => verdict [toString t.year, toString t.month, toString t.day, toString t.hour,
          toString t.minute, toString t.second, toString t.millisecond, toString t.weekday]
      | .error _ => "reject"
    | none => "reject"
  | _ => "reject"

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (run line.trimAscii.toString)
  stdout.flush
  return 0
