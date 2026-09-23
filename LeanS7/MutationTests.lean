import LeanS7.S7Conformance
import LeanS7.Conformance

namespace LeanS7.MutationTests

private def require (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"mutation regression: {label}"

private def rejected (result : Except ε α) : Bool :=
  match result with | .error _ => true | .ok _ => false

/-- Reproducible byte substitutions, including boundary values and bit flips.
    Mutations are not all malformed: acceptance is checked against invariants. -/
private def mutations (packet : ByteArray) : Array (String × ByteArray) := Id.run do
  let mut result := #[]
  for index in [:packet.size] do
    for replacement in (#[0, 1, 2, 0x7f, 0x80, 0xff] : Array UInt8) do
      result := result.push (s!"byte {index} = {replacement}", packet.set! index replacement)
    result := result.push (s!"flip byte {index}",
      packet.set! index (UInt8.xor packet[index]! 1))
  return result

private def testBoundaries (name : String) (packet : ByteArray)
    (decode : ByteArray → Except DecodeError α) : IO Nat := do
  require (!rejected (decode packet)) s!"{name}: valid seed"
  for length in [:packet.size] do
    require (rejected (decode (packet.extract 0 length))) s!"{name}: prefix {length}"
  for value in (#[0, 0xff] : Array UInt8) do
    require (rejected (decode (packet.push value))) s!"{name}: trailing {value}"
  return packet.size + 2

def run : IO Unit := do
  let mut count := 0
  for seed in Conformance.TPKT.decodeCases do
    if let .accept _ := seed.expected then
      let packet := seed.packet.materialize
      -- Exhaustive truncation of the 64 KiB seed would be quadratic work.
      if packet.size ≤ 512 then
        count := count + (← testBoundaries s!"TPKT/{seed.id}" packet TPKT.decode)
        for (label, changed) in mutations packet do
          if let .ok decoded := TPKT.decode changed then
            require (changed.size == TPKT.headerSize + decoded.payload.size)
              s!"TPKT/{seed.id}/{label}: exact size"
            require (changed[0]! == 3) s!"TPKT/{seed.id}/{label}: version"
          count := count + 1
  for seed in Conformance.COTP.decodeCases do
    if let .accept _ := seed.expected then
      let packet := seed.packet.materialize
      -- COTP has no payload-length field; a shorter payload remains valid.
      for length in [:3] do
        require (rejected (COTP.decodeData (packet.extract 0 length)))
          s!"COTP/{seed.id}: header prefix {length}"
        count := count + 1
      for (label, changed) in mutations packet do
        if let .ok decoded := COTP.decodeData changed then
          require (COTP.encodeData decoded == changed)
            s!"COTP/{seed.id}/{label}: canonical round trip"
        count := count + 1
  for seed in Conformance.S7.requestCases do
    if seed.packet[1]! == S7.jobType then
      count := count + (← testBoundaries s!"job/{seed.id}" seed.packet S7.decodeJob)
      for (label, changed) in mutations seed.packet do
        if let .ok decoded := S7.decodeJob changed then
          require (changed.size == S7.jobHeaderSize + decoded.parameters.size + decoded.data.size)
            s!"job/{seed.id}/{label}: exact sections"
          require (changed[0]! == S7.protocolId && changed[1]! == S7.jobType)
            s!"job/{seed.id}/{label}: discriminator"
        count := count + 1
  for seed in Conformance.S7.uploadCases do
    if let some _ := seed.expected then
      let decode := fun packet => do
        S7.decodeUploadFragment 1 (← S7.decodeResponse packet)
      count := count + (← testBoundaries s!"upload/{seed.id}" seed.pdu decode)
      for (label, changed) in mutations seed.pdu do
        if let .ok decoded := decode changed then
          require (changed[4]! == 0 && changed[5]! == 1)
            s!"upload/{seed.id}/{label}: correlation"
          require (changed[13]! == (if decoded.isLast then 0 else 1))
            s!"upload/{seed.id}/{label}: final flag"
          require (changed.size == 18 + decoded.data.size)
            s!"upload/{seed.id}/{label}: exact payload"
        count := count + 1
  for seed in Conformance.S7.userDataCases do
    if let some _ := seed.expected then
      let decode := S7.decodeUserDataResponse 1 seed.expectedGroup seed.expectedSubfunction
      count := count + (← testBoundaries s!"USER_DATA/{seed.id}" seed.pdu decode)
      for (label, changed) in mutations seed.pdu do
        if let .ok decoded := decode changed then
          require (changed[4]! == 0 && changed[5]! == 1)
            s!"USER_DATA/{seed.id}/{label}: correlation"
          require (changed[19]! == (if decoded.hasMoreData then 1 else 0))
            s!"USER_DATA/{seed.id}/{label}: continuation discriminator"
          require (changed.size == 26 + decoded.payload.size)
            s!"USER_DATA/{seed.id}/{label}: exact payload"
        count := count + 1
  IO.println s!"Deterministic mutation checks passed ({count} cases)."

end LeanS7.MutationTests
