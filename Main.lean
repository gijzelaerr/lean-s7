import LeanS7

open LeanS7 Std.Net

def runDemo : IO Unit := do
  match S7.encodeSetupCommunication 1 with
  | .error err => throw <| IO.userError s!"could not encode S7 request: {repr err}"
  | .ok s7 =>
      let cotp := COTP.encodeData { payload := s7 }
      match TPKT.encode { payload := cotp } with
      | .ok packet =>
          IO.println "lean-s7: classic S7 protocol foundation"
          IO.println s!"encoded a {packet.size}-byte TPKT/COTP/S7 setup-communication request"
      | .error err => throw <| IO.userError s!"could not encode connection request: {repr err}"

def runIntegration (host portString : String) : IO Unit := do
  let some address := IPv4Addr.ofString host
    | throw <| IO.userError s!"invalid IPv4 address: {host}"
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  if portNat > 65535 then
    throw <| IO.userError s!"TCP port is out of range: {portNat}"
  let client ← Client.connect { address, port := UInt16.ofNat portNat }
  try
    let initial ← client.dbRead 1 0 4
    unless initial == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
      throw <| IO.userError "python-snap7 emulator returned unexpected initial DB data"
    let written := bytes #[0xde, 0xad, 0xbe, 0xef]
    client.dbWrite 1 16 written
    let readBack ← client.dbRead 1 16 written.size
    unless readBack == written do
      throw <| IO.userError "DB write/read-back mismatch"
    let large := ByteArray.mk <| (Array.range 1200).map fun index => UInt8.ofNat (index * 37 + 11)
    client.dbWrite 1 512 large
    let largeReadBack ← client.dbRead 1 512 large.size
    unless largeReadBack == large do
      throw <| IO.userError "chunked DB write/read-back mismatch"
    let inputs ← client.inputsRead 0 4
    unless inputs == bytes #[0x11, 0x12, 0x13, 0x14] do
      throw <| IO.userError "process-input read mismatch"
    let outputValue := bytes #[0x21, 0x22, 0x23, 0x24]
    client.outputsWrite 0 outputValue
    unless (← client.outputsRead 0 outputValue.size) == outputValue do
      throw <| IO.userError "process-output write/read-back mismatch"
    let markerValue := bytes #[0x31, 0x32, 0x33, 0x34]
    client.markersWrite 0 markerValue
    unless (← client.markersRead 0 markerValue.size) == markerValue do
      throw <| IO.userError "marker write/read-back mismatch"
    let counterValue := bytes #[0x00, 0x41, 0x00, 0x42]
    client.countersWrite 0 counterValue
    unless (← client.countersRead 0 2) == counterValue do
      throw <| IO.userError "counter write/read-back mismatch"
    let timerValue := bytes #[0x00, 0x51, 0x00, 0x52]
    client.timersWrite 0 timerValue
    unless (← client.timersRead 0 2) == timerValue do
      throw <| IO.userError "timer write/read-back mismatch"
    client.dbWriteUInt8 1 2000 0xa5
    unless (← client.dbReadUInt8 1 2000) == 0xa5 do
      throw <| IO.userError "typed UInt8 DB access mismatch"
    client.dbWriteUInt16 1 2002 0x1234
    unless (← client.dbReadUInt16 1 2002) == 0x1234 do
      throw <| IO.userError "typed UInt16 DB access mismatch"
    client.dbWriteUInt32 1 2004 0x89abcdef
    unless (← client.dbReadUInt32 1 2004) == 0x89abcdef do
      throw <| IO.userError "typed UInt32 DB access mismatch"
    client.dbWriteUInt64 1 2008 0x0123456789abcdef
    unless (← client.dbReadUInt64 1 2008) == 0x0123456789abcdef do
      throw <| IO.userError "typed UInt64 DB access mismatch"
    let int8 := UInt8.toInt8 0x81
    let int16 := UInt16.toInt16 0x8123
    let int32 := UInt32.toInt32 0x81234567
    let int64 := UInt64.toInt64 0x8123456789abcdef
    client.dbWriteInt8 1 2016 int8
    client.dbWriteInt16 1 2018 int16
    client.dbWriteInt32 1 2020 int32
    client.dbWriteInt64 1 2024 int64
    unless (← client.dbReadInt8 1 2016) == int8 &&
        (← client.dbReadInt16 1 2018) == int16 &&
        (← client.dbReadInt32 1 2020) == int32 &&
        (← client.dbReadInt64 1 2024) == int64 do
      throw <| IO.userError "typed signed DB access mismatch"
    let real := Float32.ofBits 0x41480000
    client.dbWriteReal 1 2032 real
    unless (← client.dbReadReal 1 2032).toBits == real.toBits do
      throw <| IO.userError "typed REAL DB access mismatch"
    let lreal := Float.ofBits 0x400921fb54442d18
    client.dbWriteLReal 1 2036 lreal
    unless (← client.dbReadLReal 1 2036).toBits == lreal.toBits do
      throw <| IO.userError "typed LREAL DB access mismatch"
    client.dbWriteUInt8 1 2044 0xa0
    client.dbWriteBit 1 2044 0 true
    unless (← client.dbReadUInt8 1 2044) == 0xa1 && (← client.dbReadBit 1 2044 7) do
      throw <| IO.userError "bit write did not preserve neighboring DB bits"
    client.dbWriteString 1 2050 20 "lean-s7 café"
    unless (← client.dbReadString 1 2050) == "lean-s7 café" do
      throw <| IO.userError "S7 STRING DB access mismatch"
    client.dbWriteWString 1 2080 20 "PLC 🚀"
    unless (← client.dbReadWString 1 2080) == "PLC 🚀" do
      throw <| IO.userError "S7 WSTRING DB access mismatch"
    client.disconnect
    IO.println s!"lean-s7 integration passed against {host}:{portNat} (PDU {client.pduLength})"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def main (args : List String) : IO Unit := do
  match args with
  | ["integration", host, port] => runIntegration host port
  | [] => runDemo
  | _ => throw <| IO.userError "usage: lean-s7 [integration <IPv4 address> <port>]"
