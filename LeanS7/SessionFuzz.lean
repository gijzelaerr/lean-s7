import LeanS7.SessionConformance

namespace LeanS7.SessionFuzz
open Lean Conformance.Sessions

private def shape (value : Json) (keys : List String) : Except String Unit := do
  let fields ← value.getObj?
  let actual := fields.foldl (fun result key _ => key :: result) []
  if actual.length != keys.length || !keys.all (actual.contains ·) then
    throw "unsupported object shape"

private def nat (value : Json) (key : String) (maximum : Nat) : Except String Nat := do
  let number ← value.getObjValAs? Nat key
  if number > maximum then throw s!"{key} exceeds bound"
  return number

private def octets (value : Json) : Except String ByteArray := do
  let data ← value.getArr?
  if data.size > 65535 then throw "packet exceeds bound"
  let mut bytes := ByteArray.empty
  for byte in data do
    let number ← byte.getNat?
    if number > 255 then throw "invalid octet"
    bytes := bytes.push (UInt8.ofNat number)
  return bytes

private def location (value : Json) : Except String WriteLocation := do
  shape value ["range","item_index","chunk_byte_offset"]
  let range ← value.getObjVal? "range"
  shape range ["db_number","start","count"]
  let db ← nat range "db_number" 65535
  let start ← nat range "start" 0x1fffff
  let count ← nat range "count" 65535
  let index ← value.getObjVal? "item_index"
  let itemIndex ← if index.isNull then pure none else do
    let number ← index.getNat?
    if number > 0xffffffff then throw "item index exceeds bound"
    pure (some number)
  let offset ← nat value "chunk_byte_offset" 0xffffffff
  return {
    range := { area := .dataBlocks, dbNumber := UInt16.ofNat db, start, count },
    itemIndex, chunkByteOffset := offset }

private def config (value : Json) : Except String Config := do
  shape value ["write","safety","allow_potentially_mutating","budget","reference","locations","request_pdu"]
  let write ← value.getObjValAs? Bool "write"
  let safety ← value.getObjValAs? String "safety"
  if safety != (if write then "potentially-mutating" else "read-only") then
    throw "operation safety contradiction"
  let allow ← value.getObjValAs? Bool "allow_potentially_mutating"
  let budget ← nat value "budget" 16
  let reference ← nat value "reference" 65535
  let locations ← (← value.getObjVal? "locations").getArr?
  if locations.isEmpty || locations.size > 20 then throw "location count exceeds bound"
  let locations ← locations.mapM location
  let config : Config := { write, allow, budget, reference := UInt16.ofNat reference, locations }
  let encoded ← (request config).mapError (fun error => s!"invalid request: {repr error}")
  let supplied ← octets (← value.getObjVal? "request_pdu")
  if supplied != encoded then throw "request bytes do not match config"
  return config

private def event (value : Json) : Except String Event := do
  let operation ← value.getObjValAs? String "operation"
  match operation with
  | "begin" | "send" | "reconnect-setup" | "reconnected" | "disconnect" =>
    shape value ["operation"]
    return match operation with
      | "begin" => .begin | "send" => .send | "reconnect-setup" => .reconnectSetup
      | "reconnected" => .reconnected | _ => .disconnect
  | "response" =>
    shape value ["operation","response_pdu"]
    return .response (← octets (← value.getObjVal? "response_pdu"))
  | "failure" =>
    shape value ["operation","error_kind"]
    let kind ← value.getObjValAs? String "error_kind"
    let kind ← match kind with
      | "invalid-input" => pure ClientErrorKind.invalidInput | "protocol" => pure .protocol
      | "plc-rejected" => pure .plcRejected | "timeout" => pure .timeout
      | "disconnected" => pure .disconnected | "lifecycle" => pure .lifecycle
      | "transport" => pure .transport | "other" => pure .other
      | _ => throw "unknown failure kind"
    return .failure kind
  | _ => throw "unknown event"

/-- Bounded input adapter for differential fuzzing of the actual pure transition
    function and response codecs. It does not execute or prove Client socket IO. -/
def evaluate (input : Json) : Except String Json := do
  let cases ← input.getArr?
  if cases.isEmpty || cases.size > 64 then throw "batch size exceeds bound"
  let traces ← cases.mapM fun test => do
    shape test ["config","events"]
    let config ← config (← test.getObjVal? "config")
    let events ← (← test.getObjVal? "events").getArr?
    if events.isEmpty || events.size > 128 then throw "event count exceeds bound"
    return Json.arr (runEvents config (← events.mapM event))
  return Json.mkObj [("traces",Json.arr traces)]

def run : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.length > 1024 * 1024 then Except.error "input line exceeds bound"
      else Json.parse line >>= evaluate
    let json := match result with
      | .ok result => result
      | .error error => Json.mkObj [("error",toJson error)]
    output.putStrLn json.compress
    output.flush

end LeanS7.SessionFuzz
