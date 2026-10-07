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

  enc readclock REF | listblocks REF | listblocksoftype REF TYPE | blockinfo REF TYPE NUMBER
  enc szl REF ID INDEX | szlnext REF SEQUENCE | dbread REF DB START SIZE
                               -> accept HEX (the encoded request PDU)
  enc download REF TYPE NUMBER LOADSIZE MC7SIZE | dlfrag REF LAST HEXPAYLOAD | dlended REF
  enc insert REF TYPE NUMBER
  dlreq FUNCTION TYPE NUMBER HEX -> accept (a PLC-sent download service job validates)
  enc startupload REF TYPE NUMBER | upload REF ID | endupload REF ID | plcstop REF | plchot REF | plccold REF | compress REF | copyramrom REF
  startupresp REF HEX | endupresp REF HEX | ctrlresp REF FUNCTION HEX -> accept (PLC acknowledgement decodes)

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


private def encoded (result : Except EncodeError ByteArray) : String :=
  match result with
  | .ok pdu => verdict [toHex pdu]
  | .error _ => "reject"

private def runEncode (parts : List String) : String :=
  let n (text : String) : Option Nat := text.toNat?
  match parts with
  | ["readclock", r] =>
    match n r with
    | some r => encoded (S7.encodeReadClock (UInt16.ofNat r))
    | none => "reject"
  | ["listblocks", r] =>
    match n r with
    | some r => encoded (S7.encodeListBlocks (UInt16.ofNat r))
    | none => "reject"
  | ["listblocksoftype", r, t] =>
    match n r, n t with
    | some r, some t =>
      match S7.BlockType.ofCode (UInt8.ofNat t) with
      | some blockType => encoded (S7.encodeListBlocksOfType (UInt16.ofNat r) blockType)
      | none => "reject"
    | _, _ => "reject"
  | ["blockinfo", r, t, number] =>
    match n r, n t, n number with
    | some r, some t, some number =>
      match S7.BlockType.ofCode (UInt8.ofNat t) with
      | some blockType => encoded (S7.encodeGetBlockInfo (UInt16.ofNat r) blockType number)
      | none => "reject"
    | _, _, _ => "reject"
  | ["szl", r, id, index] =>
    match n r, n id, n index with
    | some r, some id, some index =>
      encoded (S7.encodeReadSzl (UInt16.ofNat r) (UInt16.ofNat id) (UInt16.ofNat index))
    | _, _, _ => "reject"
  | ["szlnext", r, sequence] =>
    match n r, n sequence with
    | some r, some sequence => encoded (S7.encodeReadSzlContinuation (UInt16.ofNat r) (UInt8.ofNat sequence))
    | _, _ => "reject"
  | ["download", r, t, number, load, mc7] =>
    match n r, n t, n number, n load, n mc7 with
    | some r, some t, some number, some load, some mc7 =>
      match S7.BlockType.ofCode (UInt8.ofNat t) with
      | some blockType => encoded (S7.encodeRequestDownload (UInt16.ofNat r) blockType number load mc7)
      | none => "reject"
    | _, _, _, _, _ => "reject"
  | ["dlfrag", r, last, hex] =>
    match n r, n last, fromHex hex with
    | some r, some last, some payload =>
      encoded (S7.encodeDownloadFragmentResponse (UInt16.ofNat r) (last != 0) payload)
    | _, _, _ => "reject"
  | ["startupload", r, t, number] =>
    match n r, n t, n number with
    | some r, some t, some number =>
      match S7.BlockType.ofCode (UInt8.ofNat t) with
      | some blockType => encoded (S7.encodeStartUpload (UInt16.ofNat r) blockType number)
      | none => "reject"
    | _, _, _ => "reject"
  | ["upload", r, id] =>
    match n r, n id with
    | some r, some id => encoded (S7.encodeUpload (UInt16.ofNat r) (UInt8.ofNat id))
    | _, _ => "reject"
  | ["endupload", r, id] =>
    match n r, n id with
    | some r, some id => encoded (S7.encodeEndUpload (UInt16.ofNat r) (UInt8.ofNat id))
    | _, _ => "reject"
  | ["compress", r] =>
    match n r with
    | some r => encoded (S7.encodeCompress (UInt16.ofNat r))
    | none => "reject"
  | ["copyramrom", r] =>
    match n r with
    | some r => encoded (S7.encodeCopyRamToRom (UInt16.ofNat r))
    | none => "reject"
  | ["plcstop", r] =>
    match n r with
    | some r => encoded (S7.encodePlcStop (UInt16.ofNat r))
    | none => "reject"
  | ["plchot", r] =>
    match n r with
    | some r => encoded (S7.encodePlcHotStart (UInt16.ofNat r))
    | none => "reject"
  | ["plccold", r] =>
    match n r with
    | some r => encoded (S7.encodePlcColdStart (UInt16.ofNat r))
    | none => "reject"
  | ["dlended", r] =>
    match n r with
    | some r => encoded (S7.encodeDownloadEndedResponse (UInt16.ofNat r))
    | none => "reject"
  | ["insert", r, t, number] =>
    match n r, n t, n number with
    | some r, some t, some number =>
      match S7.BlockType.ofCode (UInt8.ofNat t) with
      | some blockType => encoded (S7.encodeInsertBlock (UInt16.ofNat r) blockType number)
      | none => "reject"
    | _, _, _ => "reject"
  | ["dbread", r, db, start, size] =>
    match n r, n db, n start, n size with
    | some r, some db, some start, some size =>
      encoded (S7.encodeDbRead (UInt16.ofNat r) { dbNumber := UInt16.ofNat db, start, size })
    | _, _, _, _ => "reject"
  | _ => "reject"

private def run (line : String) : String :=
  let parts := (line.splitOn " ").filter (· != "")
  let payload (text : String) : Option ByteArray := fromHex text
  match parts with
  | "enc" :: rest => runEncode rest
  | ["userdata", reference, group, sub, hex] =>
    match reference.toNat?, group.toNat?, sub.toNat?, payload hex with
    | some r, some g, some s, some pdu =>
      match S7.decodeUserDataResponse (UInt16.ofNat r) (UInt8.ofNat g) (UInt8.ofNat s) pdu with
      | .ok response => verdict [toString response.sequence, if response.hasMoreData then "1" else "0",
          toHex response.payload]
      | .error _ => "reject"
    | _, _, _, _ => "reject"
  | ["dlreq", function, t, number, hex] =>
    match function.toNat?, t.toNat?, number.toNat?, payload hex with
    | some f, some t, some number, some pdu =>
      match S7.BlockType.ofCode (UInt8.ofNat t), S7.decodeJobPdu pdu with
      | some blockType, .ok job =>
        match S7.validateDownloadServiceRequest job (UInt8.ofNat f) blockType number with
        | .ok _ => verdict []
        | .error _ => "reject"
      | _, _ => "reject"
    | _, _, _, _ => "reject"
  | ["startupresp", reference, hex] =>
    match reference.toNat?, payload hex with
    | some r, some pdu =>
      match S7.decodeResponse pdu with
      | .error _ => "reject"
      | .ok response =>
        match S7.decodeStartUpload (UInt16.ofNat r) response with
        | .ok start => verdict [toString start.uploadId, match start.loadSize with
            | some size => toString size
            | none => "-"]
        | .error _ => "reject"
    | _, _ => "reject"
  | ["endupresp", reference, hex] =>
    match reference.toNat?, payload hex with
    | some r, some pdu =>
      match S7.decodeResponse pdu with
      | .error _ => "reject"
      | .ok response =>
        match S7.decodeEndUpload (UInt16.ofNat r) response with
        | .ok _ => verdict []
        | .error _ => "reject"
    | _, _ => "reject"
  | ["ctrlresp", reference, function, hex] =>
    match reference.toNat?, function.toNat?, payload hex with
    | some r, some f, some pdu =>
      match S7.decodeResponse pdu with
      | .error _ => "reject"
      | .ok response =>
        match S7.decodePlcControl (UInt16.ofNat r) (UInt8.ofNat f) response with
        | .ok _ => verdict []
        | .error _ => "reject"
    | _, _, _ => "reject"
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
