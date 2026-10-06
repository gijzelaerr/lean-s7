import LeanS7

/-! Command-line front end for hands-on testing. Not part of the library import
graph (nothing imports this module). Read-only by default: every command that can
change controller state requires `--allow-write`. -/

open LeanS7 Std.Net


private def usage : String :=
  String.intercalate "\n" [
    "usage: lean-s7-cli --host HOST [--port N] [--rack N] [--slot N] [--timeout-ms N]",
    "                   [--allow-write] COMMAND",
    "",
    "read-only commands:",
    "  read db DB START (SIZE | --as TYPE)   read bytes or one typed value from a data block",
    "  read (i|q|m) START (SIZE | --as TYPE) read inputs, outputs or markers",
    "  info                                  order code, CPU, CP and protection information",
    "  state                                 CPU operating state",
    "  clock                                 PLC date and time",
    "  blocks list                           block counts by type",
    "  blocks info TYPE NUMBER               block metadata",
    "",
    "commands that need --allow-write (they can change controller state):",
    "  write db DB START (HEXBYTES | --as TYPE VALUE)",
    "  write (i|q|m) START (HEXBYTES | --as TYPE VALUE)",
    "  cpu (stop | hot-start | cold-start)",
    "  blocks delete TYPE NUMBER",
    "",
    "TYPE: u8 i8 u16 i16 u32 i32 u64 i64 real lreal bit:N   (write: integer types only)",
    "BLOCKTYPE: ob db sdb fc sfc fb sfb",
    "",
    "WARNING: lean-s7 is experimental and has not been validated against any physical",
    "controller. Do not use it on operating equipment without independent review."]

private structure Options where
  host : Option String := none
  port : Nat := 102
  rack : Nat := 0
  slot : Nat := 2
  timeoutMs : Nat := 5000
  allowWrite : Bool := false

private def parseNat (text : String) : Option Nat :=
  if text.startsWith "0x" || text.startsWith "0X" then
    (text.drop 2).toString.foldl (init := some 0) fun acc c =>
      acc.bind fun value =>
        if c.isDigit then some (value * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c && c ≤ 'f' then some (value * 16 + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c && c ≤ 'F' then some (value * 16 + (c.toNat - 'A'.toNat + 10))
        else none
  else text.toNat?

private def failWith (message : String) : IO α :=
  throw <| IO.userError message

private def natArg (label text : String) : IO Nat := do
  match parseNat text with
  | some value => pure value
  | none => failWith s!"{label} must be a nonnegative integer, got '{text}'"

private def endpointOfString (host : String) : Transport.Endpoint :=
  match IPv4Addr.ofString host with
  | some address => .ipv4 address
  | none => match IPv6Addr.ofString host with
    | some address => .ipv6 address
    | none => .hostname host

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

private def toHex (data : ByteArray) : String :=
  String.ofList <| data.toList.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

private def fromHex (text : String) : IO ByteArray := do
  let digits := text.toList.filter (fun c => c != ' ' && c != ':')
  if digits.length % 2 != 0 then failWith "hex data must have an even number of digits"
  let value (c : Char) : IO Nat :=
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else failWith s!"invalid hex digit '{c}'"
  let rec go : List Char → ByteArray → IO ByteArray
    | high :: low :: rest, acc => do
      go rest (acc.push (UInt8.ofNat ((← value high) * 16 + (← value low))))
    | _, acc => pure acc
  go digits ByteArray.empty

private def showBlockInfo (info : S7.BlockInfo) : String :=
  String.intercalate "
" [
    s!"number: {info.number}",
    s!"block type (outer byte): {info.blockType}",
    s!"sub block type: {info.subBlockType}",
    s!"language: {info.language}",
    s!"flags: {info.flags}",
    s!"MC7 size: {info.mc7Size}",
    s!"load size: {info.loadSize}",
    s!"local data size: {info.localDataSize}",
    s!"SBB size: {info.sbbSize}",
    s!"checksum: {info.checksum}",
    s!"version: {info.version}",
    s!"code date (raw): {toHex info.codeDateRaw}",
    s!"interface date (raw): {toHex info.interfaceDateRaw}",
    s!"author: {info.author}",
    s!"family: {info.family}",
    s!"name: {info.name}"]

private def parseBlockType (text : String) : IO S7.BlockType :=
  match text with
  | "ob" => pure .organizationBlock
  | "db" => pure .dataBlock
  | "sdb" => pure .systemDataBlock
  | "fc" => pure .function
  | "sfc" => pure .systemFunction
  | "fb" => pure .functionBlock
  | "sfb" => pure .systemFunctionBlock
  | _ => failWith s!"unknown block type '{text}' (use ob db sdb fc sfc fb sfb)"

/-- Size in bytes of a typed value, or the bit index for `bit:N`. -/
private def typeSize : String → Option Nat
  | "u8" | "i8" => some 1
  | "u16" | "i16" => some 2
  | "u32" | "i32" | "real" => some 4
  | "u64" | "i64" | "lreal" => some 8
  | text => if text.startsWith "bit:" then some 1 else none

private def showValue (type : String) (data : ByteArray) : IO String := do
  let ok {ε α} [Repr ε] [ToString α] (result : Except ε α) : IO String :=
    match result with
    | .ok value => pure (toString value)
    | .error error => failWith s!"decode failed: {reprStr error}"
  match type with
  | "u8" => ok (Value.getUInt8 data)
  | "i8" => ok (Value.getInt8 data)
  | "u16" => ok (Value.getUInt16 data)
  | "i16" => ok (Value.getInt16 data)
  | "u32" => ok (Value.getUInt32 data)
  | "i32" => ok (Value.getInt32 data)
  | "u64" => ok (Value.getUInt64 data)
  | "i64" => ok (Value.getInt64 data)
  | "real" => ok (Value.getReal data)
  | "lreal" => ok (Value.getLReal data)
  | text =>
    match (text.drop 4).toString.toNat? with
    | some bit => if bit < 8 then ok (Value.getBit data 0 bit) else failWith "bit index must be 0-7"
    | none => failWith s!"unknown type '{text}'"

private def encodeValue (type text : String) : IO ByteArray := do
  let some value := text.toInt?
    | failWith s!"value must be an integer, got '{text}'"
  let (low, high, put) : Int × Int × (Int → ByteArray) := match type with
    | "u8" => (0, 255, fun v => Value.putUInt8 (UInt8.ofNat v.toNat))
    | "i8" => (-128, 127, fun v => Value.putInt8 (Int8.ofInt v))
    | "u16" => (0, 65535, fun v => Value.putUInt16 (UInt16.ofNat v.toNat))
    | "i16" => (-32768, 32767, fun v => Value.putInt16 (Int16.ofInt v))
    | "u32" => (0, 4294967295, fun v => Value.putUInt32 (UInt32.ofNat v.toNat))
    | "i32" => (-2147483648, 2147483647, fun v => Value.putInt32 (Int32.ofInt v))
    | "u64" => (0, 18446744073709551615, fun v => Value.putUInt64 (UInt64.ofNat v.toNat))
    | "i64" => (-9223372036854775808, 9223372036854775807, fun v => Value.putInt64 (Int64.ofInt v))
    | _ => (1, 0, fun _ => ByteArray.empty)
  if low > high then failWith s!"typed writes support integer types only, got '{type}'"
  if value < low || value > high then failWith s!"{value} is out of range for {type}"
  pure (put value)

private def parseOptions : List String → Options → IO (Options × List String)
  | "--host" :: value :: rest, options => parseOptions rest { options with host := some value }
  | "--port" :: value :: rest, options => do
    parseOptions rest { options with port := ← natArg "--port" value }
  | "--rack" :: value :: rest, options => do
    parseOptions rest { options with rack := ← natArg "--rack" value }
  | "--slot" :: value :: rest, options => do
    parseOptions rest { options with slot := ← natArg "--slot" value }
  | "--timeout-ms" :: value :: rest, options => do
    parseOptions rest { options with timeoutMs := ← natArg "--timeout-ms" value }
  | "--allow-write" :: rest, options => parseOptions rest { options with allowWrite := true }
  | rest, options => pure (options, rest)

private def isMutating : List String → Bool
  | "write" :: _ => true
  | "cpu" :: _ => true
  | "blocks" :: "delete" :: _ => true
  | _ => false

private def areaOf : String → Option S7.Area
  | "i" => some .processInputs
  | "q" => some .processOutputs
  | "m" => some .markers
  | "db" => some .dataBlocks
  | _ => none

private def runCommand (client : Client) : List String → IO Unit
  | "read" :: areaText :: rest => do
    let some area := areaOf areaText | failWith s!"unknown area '{areaText}' (use db i q m)"
    let (dbNumber, rest) ← if area == .dataBlocks then
        match rest with
        | db :: rest => pure ((← natArg "DB" db), rest)
        | [] => failWith usage
      else pure (0, rest)
    let (start, spec) ← match rest with
      | start :: spec => pure ((← natArg "START" start), spec)
      | [] => failWith usage
    match spec with
    | [size] =>
      let data ← client.readArea area (UInt16.ofNat dbNumber) start (← natArg "SIZE" size)
      IO.println (toHex data)
    | ["--as", type] =>
      let some size := typeSize type | failWith s!"unknown type '{type}'"
      let data ← client.readArea area (UInt16.ofNat dbNumber) start size
      IO.println (← showValue type data)
    | _ => failWith usage
  | "write" :: areaText :: rest => do
    let some area := areaOf areaText | failWith s!"unknown area '{areaText}' (use db i q m)"
    let (dbNumber, rest) ← if area == .dataBlocks then
        match rest with
        | db :: rest => pure ((← natArg "DB" db), rest)
        | [] => failWith usage
      else pure (0, rest)
    let (start, spec) ← match rest with
      | start :: spec => pure ((← natArg "START" start), spec)
      | [] => failWith usage
    let payload ← match spec with
      | [hex] => fromHex hex
      | ["--as", type, value] => encodeValue type value
      | _ => failWith usage
    client.writeArea area (UInt16.ofNat dbNumber) start payload
    IO.println s!"wrote {payload.size} byte(s); the controller acknowledged the write"
  | ["info"] => do
    IO.println (repr (← client.getOrderCode))
    IO.println (repr (← client.getCpuInfo))
    IO.println (repr (← client.getCpInfo))
    IO.println (repr (← client.getProtection))
  | ["state"] => do IO.println (repr (← client.getCpuState))
  | ["clock"] => do IO.println (repr (← client.getPlcDateTime))
  | ["blocks", "list"] => do IO.println (repr (← client.listBlocks))
  | ["blocks", "info", type, number] => do
    IO.println (showBlockInfo (← client.getBlockInfo (← parseBlockType type) (← natArg "NUMBER" number)))
  | ["blocks", "delete", type, number] => do
    client.deleteBlock (← parseBlockType type) (← natArg "NUMBER" number)
    IO.println "block deleted"
  | ["cpu", "stop"] => do client.plcStop; IO.println "stop acknowledged"
  | ["cpu", "hot-start"] => do client.plcHotStart; IO.println "hot start acknowledged"
  | ["cpu", "cold-start"] => do client.plcColdStart; IO.println "cold start acknowledged"
  | _ => failWith usage

def main (args : List String) : IO UInt32 := do
  try
    if args.isEmpty || args.contains "--help" || args.contains "-h" then
      IO.println usage
      return 0
    let (options, command) ← parseOptions args {}
    let some host := options.host | failWith s!"--host is required\n\n{usage}"
    if options.port > 65535 then failWith "--port must be at most 65535"
    if command.isEmpty then failWith usage
    if isMutating command && !options.allowWrite then
      failWith "this command can change controller state; repeat it with --allow-write"
    IO.eprintln "lean-s7-cli: experimental; not validated against any physical controller."
    let client ← Client.connect {
      endpoint := endpointOfString host
      port := UInt16.ofNat options.port
      rack := options.rack
      slot := options.slot
      connectTimeoutMs := some options.timeoutMs
      operationTimeoutMs := some options.timeoutMs }
    try runCommand client command
    finally client.disconnect
    return 0
  catch error =>
    IO.eprintln s!"error: {error}"
    return 1
