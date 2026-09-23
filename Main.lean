import LeanS7
import LeanS7.MultiSemanticsTests
import LeanS7.ConcurrencyTests
import LeanS7.StatefulFaultIntegration
import LeanS7.RetryProgressTests
import LeanS7.CompoundTests
import LeanS7.WriteProvenanceTests
import LeanS7.UserDataCompletionTests
import LeanS7.TransportResourceTests
import LeanS7.TimeoutTests
import LeanS7.MixedOperationTests
import LeanS7.ResourceStressTests
import LeanS7.ConnectionBudgetTests
import LeanS7.QueuedLifecycleTests
import LeanS7.BoundaryOperationTests
import LeanS7.ClockCodecAssuranceTests
import LeanS7.OverlapOperationTests
import LeanS7.QueuedBatchTests
import LeanS7.RetryBudgetTests

open LeanS7 Std.Net

def multiResultsMatch : List S7.ReadItemResult → List ByteArray → Bool
  | [], [] => true
  | .success payload :: results, expected :: rest =>
      payload == expected && multiResultsMatch results rest
  | _, _ => false

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

def endpointOfString (host : String) : Transport.Endpoint :=
  match IPv4Addr.ofString host with
  | some address => .ipv4 address
  | none => match IPv6Addr.ofString host with
    | some address => .ipv6 address
    | none => .hostname host

def runIntegration (host portString : String) (testReconnect : Bool := false) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  if portNat > 65535 then
    throw <| IO.userError s!"TCP port is out of range: {portNat}"
  let client ← Client.connect {
    endpoint := endpointOfString host
    port := UInt16.ofNat portNat
    operationTimeoutMs := some 1000
    reconnectRetries := if testReconnect then 1 else 0
    maxStaleResponses := if testReconnect then 0 else 4
  }
  try
    unless ← client.isConnected do
      throw <| IO.userError "client did not report its connected state"
    let initial ← client.dbRead 1 0 4
    unless initial == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
      throw <| IO.userError "python-snap7 emulator returned unexpected initial DB data"
    let written := bytes #[0xde, 0xad, 0xbe, 0xef]
    client.dbWrite 1 16 written
    let readBack ← client.dbRead 1 16 written.size
    unless readBack == written do
      throw <| IO.userError "DB write/read-back mismatch"
    if testReconnect then
      client.disconnect
      unless !(← client.isConnected) do
        throw <| IO.userError "client remained connected after disconnect"
      IO.println s!"lean-s7 reconnect integration passed against {host}:{portNat}"
      return
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
    let elements := large.extract 0 1000
    for area in [S7.Area.counters, S7.Area.timers] do
      client.writeArea area 0 16 elements
      unless (← client.readArea area 0 16 500) == elements do
        throw <| IO.userError "chunked two-byte-element write/read-back mismatch"
    unless (← client.dbRead 1 512 0).isEmpty do
      throw <| IO.userError "empty read returned data"
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
    let multiItems : Array S7.WriteItem := (Array.range 25).map fun index =>
      let area := match index % 3 with
        | 0 => S7.Area.dataBlocks
        | 1 => S7.Area.markers
        | _ => S7.Area.processOutputs
      {
        range := {
          area
          dbNumber := if area == .dataBlocks then 1 else 0
          start := 100 + index
          count := 1
        }
        payload := bytes #[UInt8.ofNat (0x60 + index)]
      }
    let writeResults ← client.writeMulti multiItems
    unless writeResults.size == multiItems.size && writeResults.all (· == .success) do
      throw <| IO.userError "multi-write results were unsuccessful or out of order"
    let ranges := multiItems.map (·.range)
    let readResults ← client.readMulti ranges
    let expected := (Array.range 25).toList.map fun index => bytes #[UInt8.ofNat (0x60 + index)]
    unless multiResultsMatch readResults.toList expected do
      throw <| IO.userError "multi-read results were incorrect or out of order"
    let budgetItems : Array S7.WriteItem := (Array.range 8).map fun index =>
      {
        range := {
          area := .dataBlocks
          dbNumber := 1
          start := 2200 + index * 100
          count := 100
        }
        payload := ByteArray.mk <| Array.replicate 100 (UInt8.ofNat (0x90 + index))
      }
    unless (← client.writeMulti budgetItems).all (· == .success) do
      throw <| IO.userError "PDU-budgeted multi-write failed"
    let budgetResults ← client.readMulti (budgetItems.map (·.range))
    unless multiResultsMatch budgetResults.toList (budgetItems.toList.map (·.payload)) do
      throw <| IO.userError "PDU-budgeted multi-read failed"
    let concurrent ← (Array.range 16).mapM fun _ => IO.asTask (client.dbRead 1 0 4)
    for task in concurrent do
      match ← IO.wait task with
      | .ok payload => unless payload == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
          throw <| IO.userError "serialized concurrent read returned the wrong payload"
      | .error error => throw error
    let szlIds ← client.readSzlList
    unless szlIds.contains 0x001c && szlIds.contains 0x0424 do
      throw <| IO.userError "SZL directory omitted expected entries"
    let orderCode ← client.getOrderCode
    unless orderCode.code == "6ES7 315-2EH14-0AB0" &&
        orderCode.versionMajor == 3 && orderCode.versionMinor == 3 &&
        orderCode.versionPatch == 0 do
      throw <| IO.userError "order-code parsing mismatch"
    let cpuInfo ← client.getCpuInfo
    unless cpuInfo.asName == "SNAP7-SERVER" &&
        cpuInfo.moduleTypeName == "CPU 315-2 PN/DP" do
      throw <| IO.userError "CPU information parsing mismatch"
    let cpInfo ← client.getCpInfo
    unless cpInfo.maxPduLength == 480 && cpInfo.maxConnections == 32 &&
        cpInfo.maxMpiRate == 12000000 && cpInfo.maxBusRate == 100000000 do
      throw <| IO.userError "CP information parsing mismatch"
    let protection ← client.getProtection
    unless protection.selectorPosition == 1 && protection.modeSelector == 2 do
      throw <| IO.userError "CPU protection parsing mismatch"
    unless (← client.getCpuState) == .running do
      throw <| IO.userError "CPU did not initially report RUN"
    let clock ← client.getPlcDateTime
    unless clock.year == 2026 && clock.month == 9 && clock.day == 7 do
      throw <| IO.userError "PLC clock parsing mismatch"
    client.setPlcDateTime clock
    client.setSessionPassword "secret"
    client.clearSessionPassword
    client.plcStop
    unless (← client.getCpuState) == .stopped do
      throw <| IO.userError "PLC stop did not change emulator state"
    client.plcHotStart
    unless (← client.getCpuState) == .running do
      throw <| IO.userError "PLC hot start did not change emulator state"
    client.plcColdStart
    unless (← client.getCpuState) == .running do
      throw <| IO.userError "PLC cold start did not leave emulator in RUN"
    let blockCounts ← client.listBlocks
    unless blockCounts.dataBlocks == 1 do
      throw <| IO.userError "block-count query did not find DB1"
    let dbBlocks ← client.listBlocksOfType .dataBlock
    unless dbBlocks.size == 1 && dbBlocks[0]!.number == 1 do
      throw <| IO.userError "block-list query did not return DB1"
    let blockInfo ← client.getBlockInfo .dataBlock 1
    unless blockInfo.number == 1 && blockInfo.mc7Size == 4096 &&
        blockInfo.author == "SNAP7EMU" do
      throw <| IO.userError "block metadata parsing mismatch"
    let fullBlock ← client.fullUpload .dataBlock 1
    unless fullBlock.size == 4132 do
      throw <| IO.userError "fragmented full upload returned the wrong size"
    let mc7 ← client.upload .dataBlock 1
    unless mc7.size == 4096 && mc7.extract 0 4 == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
      throw <| IO.userError "fragmented MC7 upload returned the wrong data"
    let forces ← client.readForceTable
    unless forces.size == 2 && forces[0]!.areaCode == 0x81 && forces[0]!.value do
      throw <| IO.userError "force-table parsing mismatch"
    client.forceBit .processOutputs 8 3 true
    unless (← client.outputsRead 8 1) == bytes #[8] do
      throw <| IO.userError "process-image bit override failed"
    client.cancelForceBit .processOutputs 8 3
    unless (← client.outputsRead 8 1) == bytes #[0] do
      throw <| IO.userError "process-image bit override cancellation failed"
    client.compress
    client.copyRamToRom
    let rawReference : UInt16 := 0xf000
    let rawRequest ← match S7.encodeDbRead rawReference { dbNumber := 1, start := 0, size := 4 } with
      | .ok request => pure request
      | .error error => throw <| IO.userError s!"raw request encoding failed: {repr error}"
    let rawResponse ← client.rawExchange rawReference rawRequest
    let rawPayload ← match S7.decodeResponse rawResponse with
      | .ok response => match S7.decodeDbRead rawReference response with
        | .ok payload => pure payload
        | .error error => throw <| IO.userError s!"raw response data failed: {repr error}"
      | .error error => throw <| IO.userError s!"raw response decoding failed: {repr error}"
    unless rawPayload == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
      throw <| IO.userError "raw ISO exchange returned the wrong payload"
    let mismatchedRawRejected ← try
      discard <| client.rawExchange (rawReference + 1) rawRequest
      pure false
    catch error => pure (classifyClientError error == .invalidInput)
    unless mismatchedRawRejected do
      throw <| IO.userError "raw request/reference mismatch was not rejected as invalid input"
    let invalidBitRejected ← try
      discard <| client.dbReadBit 1 0 8
      pure false
    catch error => pure (classifyClientError error == .invalidInput)
    unless invalidBitRejected do
      throw <| IO.userError "invalid bit index was not rejected as invalid input"
    unless ← client.isConnected do
      throw <| IO.userError "local input validation disconnected the client"
    client.deleteBlock .function 99999
    client.disconnect
    unless !(← client.isConnected) do
      throw <| IO.userError "client remained connected after disconnect"
    let rejected ← try
      discard <| client.dbRead 1 0 1
      pure false
    catch _ => pure true
    unless rejected do
      throw <| IO.userError "explicitly disconnected client reconnected unexpectedly"
    IO.println s!"lean-s7 integration passed against {host}:{portNat} (PDU {client.pduLength})"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def expectConnectFailure (host portString : String) (expected : Option String := none) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let result : Except IO.Error Client ← try
    let client ← Client.connect {
        endpoint := endpointOfString host
        port := UInt16.ofNat portNat
        connectTimeoutMs := some 200
        operationTimeoutMs := some 200
      }
    pure (.ok client)
  catch error => pure (.error error)
  match result with
  | .error error =>
      let message := error.toString
      let expectedKind := if expected.isSome then ClientErrorKind.protocol else .timeout
      unless classifyClientError error == expectedKind do
        throw <| IO.userError
          s!"unexpected connection error category {repr (classifyClientError error)}: {message}"
      if let some expected := expected then
        unless (message.splitOn expected).length > 1 do
          throw <| IO.userError s!"unexpected connection failure: {message}"
      IO.println s!"lean-s7 connection rejection passed against {host}:{portNat}"
  | .ok client =>
      client.disconnect
      throw <| IO.userError "connection unexpectedly succeeded"

def runDownloadIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host
    port := UInt16.ofNat portNat
    operationTimeoutMs := some 1000
  }
  try
    let mc7 := ByteArray.mk <| (Array.range 600).map fun index => UInt8.ofNat (index * 29 + 7)
    let compact := ByteArray.mk (Array.replicate 34 0) ++ uint16BE (UInt16.ofNat mc7.size)
    client.downloadBlock .dataBlock 7 (compact ++ mc7)
    client.disconnect
    IO.println s!"lean-s7 PLC-driven download integration passed against {host}:{portNat}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def runDownloadInterruptionIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host
    port := UInt16.ofNat portNat
    operationTimeoutMs := some 1000
  }
  let mc7 := ByteArray.mk <| (Array.range 600).map fun index => UInt8.ofNat (index * 29 + 7)
  let compact := ByteArray.mk (Array.replicate 34 0) ++ uint16BE (UInt16.ofNat mc7.size)
  let outcome ← try
    client.downloadBlock .dataBlock 7 (compact ++ mc7)
    pure (none : Option IO.Error)
  catch error => pure (some error)
  match outcome with
  | none => throw <| IO.userError "interrupted block download unexpectedly succeeded"
  | some error =>
      unless classifyClientError error == .disconnected do
        throw <| IO.userError
          s!"unexpected download interruption category {repr (classifyClientError error)}: {error}"
  if ← client.isConnected then
    throw <| IO.userError "interrupted block download left the client connected"
  client.disconnect
  IO.println "block-download interruption passed"

def runDownloadRejectionIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host
    port := UInt16.ofNat portNat
    operationTimeoutMs := some 1000
  }
  let mc7 := ByteArray.mk <| (Array.range 600).map fun index => UInt8.ofNat (index * 29 + 7)
  let compact := ByteArray.mk (Array.replicate 34 0) ++ uint16BE (UInt16.ofNat mc7.size)
  let outcome ← try
    client.downloadBlock .dataBlock 7 (compact ++ mc7)
    pure (none : Option IO.Error)
  catch error => pure (some error)
  match outcome with
  | none => throw <| IO.userError "malformed PLC download service request unexpectedly succeeded"
  | some error =>
      unless classifyClientError error == .protocol do
        throw <| IO.userError
          s!"unexpected malformed download category {repr (classifyClientError error)}: {error}"
  if ← client.isConnected then
    throw <| IO.userError "malformed PLC download service request left the client connected"
  client.disconnect
  IO.println "malformed PLC download service request rejected"

def runUserDataInterruptionIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host
    port := UInt16.ofNat portNat
    operationTimeoutMs := some 1000
  }
  let outcome ← try
    discard <| client.listBlocksOfType .dataBlock
    pure (none : Option IO.Error)
  catch error => pure (some error)
  match outcome with
  | none => throw <| IO.userError "interrupted USER_DATA exchange unexpectedly succeeded"
  | some error =>
      unless classifyClientError error == .disconnected do
        throw <| IO.userError
          s!"unexpected USER_DATA interruption category {repr (classifyClientError error)}: {error}"
  if ← client.isConnected then
    throw <| IO.userError "interrupted USER_DATA exchange left the client connected"
  client.disconnect
  IO.println "USER_DATA continuation interruption passed"

def runReferenceWrapIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host
    port := UInt16.ofNat portNat
    operationTimeoutMs := some 1000
    initialRequestReference := 0xffff
  }
  try
    let before ← client.dbRead 1 0 1
    let after ← client.dbRead 1 1 1
    unless before == bytes #[0xaa] && after == bytes #[0xbb] do
      throw <| IO.userError "reference-wraparound reads returned incorrect data"
    client.disconnect
    IO.println "PDU-reference wraparound passed"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def runSegmentedIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host
    port := UInt16.ofNat portNat
    operationTimeoutMs := some 1000
  }
  try
    let payload ← client.dbRead 1 0 4
    unless payload == bytes #[0xde, 0xad, 0xbe, 0xef] do
      throw <| IO.userError "segmented COTP response returned the wrong payload"
    client.disconnect
    IO.println s!"lean-s7 segmented COTP integration passed against {host}:{portNat}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def runTransportFailureIntegration (host portString expected : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host, port := UInt16.ofNat portNat,
    operationTimeoutMs := some 300,
    reconnectRetries := if (expected.splitOn "too many stale").length > 1 then 1 else 0
  }
  try
    let outcome ← try
      let payload ← client.dbRead 1 0 (if expected == "accept" then 462 else 4)
      pure (.ok payload : Except IO.Error ByteArray)
    catch error => pure (.error error)
    match outcome with
    | .ok payload =>
        unless expected == "accept" && payload == ByteArray.mk (Array.replicate 462 0xaa) do
          throw <| IO.userError "invalid transport response was accepted"
    | .error error =>
        let message := error.toString
        let expectedKind := if (expected.splitOn "timed out").length > 1 then
          ClientErrorKind.timeout
        else if (expected.splitOn "bytes still expected").length > 1 then
          .disconnected
        else
          .protocol
        unless classifyClientError error == expectedKind do
          throw <| IO.userError
            s!"unexpected transport error category {repr (classifyClientError error)}: {message}"
        unless expected != "accept" && (message.splitOn expected).length > 1 do
          throw <| IO.userError s!"unexpected transport failure: {message}"
        if ← client.isConnected then
          throw <| IO.userError "failed exchange left the client connected"
    client.disconnect
    IO.println s!"transport case passed: {expected}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def runServiceRejectionIntegration (host portString operation expected : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host, port := UInt16.ofNat portNat,
    operationTimeoutMs := some 500,
    reconnectRetries := if (expected.splitOn "failed with code").length > 1 then 1 else 0
  }
  try
    let outcome ← try
      if operation == "szl" then
        discard <| client.readSzl 0x0424 0
      else if operation == "upload" then
        discard <| client.fullUpload .dataBlock 1
      else if operation == "userdata" then
        discard <| client.listBlocksOfType .dataBlock
      else
        throw <| IO.userError s!"unknown rejection operation: {operation}"
      pure (none : Option IO.Error)
    catch error => pure (some error)
    match outcome with
    | some error =>
        let message := error.toString
        let expectedKind := if (expected.splitOn "failed with code").length > 1 then
          ClientErrorKind.plcRejected
        else
          .protocol
        unless classifyClientError error == expectedKind do
          throw <| IO.userError
            s!"unexpected service error category {repr (classifyClientError error)}: {message}"
        unless (message.splitOn expected).length > 1 do
          throw <| IO.userError s!"unexpected service failure: {message}"
    | none => throw <| IO.userError "malformed service response was accepted"
    if ← client.isConnected then
      throw <| IO.userError "rejected service transfer left the client connected"
    client.disconnect
    IO.println s!"service rejection passed: {operation}: {expected}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def runReconnectShrinkIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host, port := UInt16.ofNat portNat,
    operationTimeoutMs := some 500, reconnectRetries := 1
  }
  let outcome ← try
    discard <| client.dbRead 1 0 300
    pure (none : Option IO.Error)
  catch error => pure (some error)
  match outcome with
  | some error =>
      let message := error.toString
      unless classifyClientError error == .protocol do
        throw <| IO.userError
          s!"unexpected reconnect error category {repr (classifyClientError error)}: {message}"
      unless (message.splitOn "reconnected PDU length shrank from 480 to 240").length > 1 do
        throw <| IO.userError s!"unexpected reconnect failure: {message}"
  | none => throw <| IO.userError "shrinking reconnect was accepted"
  if ← client.isConnected then
    throw <| IO.userError "rejected shrinking reconnect left the client connected"
  client.disconnect
  IO.println "shrinking reconnect rejection passed"

def runReconnectRecoveryIntegration (host portString : String) : IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let client ← Client.connect {
    endpoint := endpointOfString host, port := UInt16.ofNat portNat,
    operationTimeoutMs := some 500, reconnectRetries := 1
  }
  try
    let payload ← client.dbRead 1 0 4
    unless payload == bytes #[0xde, 0xad, 0xbe, 0xef] do
      throw <| IO.userError "reconnected read returned the wrong payload"
    client.disconnect
    IO.println "transport reconnect recovery passed"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def runTransferDeadlineIntegration (host portString operation operationMs transferMs expected : String) :
    IO Unit := do
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  let some operationTimeout := operationMs.toNat?
    | throw <| IO.userError s!"invalid operation timeout: {operationMs}"
  let transferTimeout ← if transferMs == "none" then pure none else do
    let some timeout := transferMs.toNat?
      | throw <| IO.userError s!"invalid transfer timeout: {transferMs}"
    pure (some timeout)
  let client ← Client.connect {
    endpoint := endpointOfString host, port := UInt16.ofNat portNat,
    operationTimeoutMs := some operationTimeout,
    connectTimeoutMs := some 1000,
    transferReceiveTimeoutMs := transferTimeout,
    reconnectRetries := if operation.endsWith "-retry" then 1 else 0
    allowPotentiallyMutatingRetries := operation == "write-retry"
  }
  try
    let outcome ← try
      if operation == "upload" then
        let payload ← client.fullUpload .dataBlock 1
        unless payload == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
          throw <| IO.userError "deadline upload returned incorrect bytes"
      else if operation == "szl" then
        let result ← client.readSzl 0x0424
        unless result.data == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
          throw <| IO.userError "deadline SZL returned incorrect bytes"
      else if operation == "userdata" then
        let result ← client.listBlocksOfType .dataBlock
        unless result.size == 1 && result[0]!.number == 1 do
          throw <| IO.userError "deadline USER_DATA returned incorrect result"
      else if operation == "read-invalid-range" then
        discard <| client.dbRead 1 (0x1fffff - 100) 1000
      else if operation == "write-invalid-range" then
        client.dbWrite 1 (0x1fffff - 100) (bytes (Array.replicate 1000 0xaa))
      else if operation == "read" || operation == "read-retry" || operation == "read-continuation-retry" then
        let payload ← client.dbRead 1 0 1000
        unless payload == bytes (Array.replicate 1000 0xaa) do
          throw <| IO.userError "deadline read returned incorrect bytes"
      else if operation == "write" || operation == "write-retry" || operation == "write-continuation-retry" then
        client.dbWrite 1 0 (bytes (Array.replicate 1000 0xaa))
      else if operation == "readmulti" then
        let ranges := (Array.range 4).map fun index =>
          ({ area := .dataBlocks, dbNumber := 1, start := index * 200, count := 200 } : S7.MemoryRange)
        let results ← client.readMulti ranges
        unless results == Array.replicate 4 (.success (bytes (Array.replicate 200 0xaa))) do
          throw <| IO.userError "deadline multi-read returned incorrect results"
      else if operation == "writemulti" then
        let items := (Array.range 4).map fun index =>
          let range : S7.MemoryRange :=
            { area := .dataBlocks, dbNumber := 1, start := index * 200, count := 200 }
          ({ range, payload := bytes (Array.replicate 200 0xaa) } : S7.WriteItem)
        let results ← client.writeMulti items
        unless results == Array.replicate 4 .success do
          throw <| IO.userError "deadline multi-write returned incorrect results"
      else if operation == "download" then
        let block := (bytes (Array.replicate 1000 0xaa)).set! 34 3 |>.set! 35 0xc4
        client.downloadBlock .dataBlock 1 block
      else throw <| IO.userError s!"unknown transfer: {operation}"
      pure (none : Option IO.Error)
    catch error => pure (some error)
    match outcome with
    | none => unless expected == "accept" do
        throw <| IO.userError "slow transfer unexpectedly completed"
    | some error =>
        let expectedKind := if expected == "invalid-input" then ClientErrorKind.invalidInput else .timeout
        unless (expected == "timeout" || expected == "invalid-input") &&
            classifyClientError error == expectedKind do
          throw <| IO.userError s!"unexpected transfer failure: {error}"
        if expected == "invalid-input" then
          unless ← client.isConnected do
            throw <| IO.userError "local range validation disconnected the client"
        else if ← client.isConnected then
          throw <| IO.userError "timed out transfer left the client connected"
    client.disconnect
    IO.println s!"transfer deadline passed: {operation}: {expected}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def runMultiBatchingIntegration (host portString pduString countString sizeString : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some pdu := pduString.toNat? | throw <| IO.userError "invalid PDU"
  let some count := countString.toNat? | throw <| IO.userError "invalid item count"
  let some size := sizeString.toNat? | throw <| IO.userError "invalid item size"
  let client ← Client.connect {
    endpoint := endpointOfString host, port := UInt16.ofNat port,
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000
  }
  try
    unless (← client.negotiatedPduLength).toNat == pdu do
      throw <| IO.userError "unexpected negotiated batch PDU"
    let ranges := (Array.range count).map fun index =>
      ({ area := .dataBlocks, dbNumber := 1, start := index * 256, count := size } : S7.MemoryRange)
    let items := ranges.mapIdx fun index range =>
      ({ range, payload := bytes (Array.replicate size (UInt8.ofNat index)) } : S7.WriteItem)
    let written ← client.writeMulti items
    let read ← client.readMulti ranges
    unless written.size == count && read.size == count do
      throw <| IO.userError "batching changed result count"
    for index in [:count] do
      let expectedWrite : S7.WriteItemResult :=
        if index % 7 == 3 then .failure 5 else .success
      let expectedRead : S7.ReadItemResult := if index % 7 == 3 then .failure 5
        else .success (bytes (Array.replicate size (UInt8.ofNat index)))
      unless written[index]? == some expectedWrite && read[index]? == some expectedRead do
        throw <| IO.userError s!"batching changed result order at {index}"
    client.disconnect
    IO.println s!"multi-batching passed: PDU {pdu}, items {count}, size {size}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def main (args : List String) : IO Unit := do
  match args with
  | ["integration", host, port] => runIntegration host port
  | ["integration-concurrency", host, port, mode] =>
      ConcurrencyTests.runIntegration host port mode
  | ["integration-compound", host, port, mode] =>
      CompoundTests.runIntegration host port mode
  | ["integration-queued-lifecycle", host, port, mode] =>
      QueuedLifecycleTests.runIntegration host port mode
  | ["integration-resource-stress", host, port] =>
      ResourceStressTests.runIntegration host port
  | ["integration-resource-stress", host, port, rounds] =>
      let some count := rounds.toNat? | throw <| IO.userError "invalid stress rounds"
      ResourceStressTests.runIntegration host port count
  | ["integration-connection-budget", host, firstPort, secondPort, mode] =>
      ConnectionBudgetTests.runIntegration host firstPort secondPort mode
  | ["integration-mixed-operations", host, port, plan] =>
      MixedOperationTests.runIntegration host port plan
  | ["integration-boundary-operations", host, port, pdu, plan] =>
      BoundaryOperationTests.runIntegration host port pdu plan
  | ["integration-overlap-operations", host, port, pdu, memorySize, plan] =>
      OverlapOperationTests.runIntegration host port pdu memorySize plan
  | ["integration-queued-batches", host, port, pdu, mode, sizes] =>
      QueuedBatchTests.runIntegration host port pdu mode sizes
  | ["integration-retry-budgets", host, port, mode, budget, drops] =>
      RetryBudgetTests.runIntegration host port mode budget drops
  | ["integration-clock-assurance", host, port, digit] =>
      ClockCodecAssuranceTests.runIntegration host port digit
  | ["integration-timeout-cleanup", host, port, mode] =>
      TimeoutTests.runIntegration host port mode
  | ["integration-transport-resources", host, port, mode] =>
      TransportResourceTests.runIntegration host port mode
  | ["integration-userdata-completion", host, port, service, mode] =>
      UserDataCompletionTests.runIntegration host port service mode
  | ["integration-write-provenance", host, port, mode] =>
      WriteProvenanceTests.runIntegration host port mode
  | ["integration-retry-progress", host, port, mode] =>
      RetryProgressTests.runIntegration host port mode
  | ["integration-stateful-fault", host, port, operation, expected] =>
      StatefulFaultIntegration.run host port operation expected
  | ["integration-multi-semantics", host, port, mode] =>
      MultiSemanticsTests.runIntegration host port mode
  | ["integration-multi-batching", host, port, pdu, count, size] =>
      runMultiBatchingIntegration host port pdu count size
  | ["integration-transfer-deadline", host, port, operation, operationMs, transferMs, expected] =>
      runTransferDeadlineIntegration host port operation operationMs transferMs expected
  | ["integration-reconnect", host, port] => runIntegration host port true
  | ["integration-download", host, port] => runDownloadIntegration host port
  | ["integration-download-interruption", host, port] =>
      runDownloadInterruptionIntegration host port
  | ["integration-download-rejection", host, port] =>
      runDownloadRejectionIntegration host port
  | ["integration-userdata-interruption", host, port] =>
      runUserDataInterruptionIntegration host port
  | ["integration-reference-wrap", host, port] =>
      runReferenceWrapIntegration host port
  | ["integration-segmented", host, port] => runSegmentedIntegration host port
  | ["integration-transport", host, port, expected] =>
      runTransportFailureIntegration host port expected
  | ["integration-service-rejection", host, port, operation, expected] =>
      runServiceRejectionIntegration host port operation expected
  | ["integration-reconnect-shrink", host, port] =>
      runReconnectShrinkIntegration host port
  | ["integration-reconnect-recovery", host, port] =>
      runReconnectRecoveryIntegration host port
  | ["expect-connect-failure", host, port] => expectConnectFailure host port
  | ["expect-connect-rejection", host, port, expected] =>
      expectConnectFailure host port (some expected)
  | [] => runDemo
  | _ => throw <| IO.userError "usage: lean-s7 [integration <host-or-address> <port>]"
