import LeanS7.BitUpdateAssurance

namespace LeanS7.BitUpdateAssuranceTests

private def expect {α : Type} [BEq α] (result : Except Value.Error α) (expected : α)
    (label : String) : IO Unit := do
  let .ok actual := result
    | throw <| IO.userError s!"{label}: unexpectedly rejected"
  unless actual == expected do
    throw <| IO.userError s!"{label}: unexpected value"

private def expectInvalidIndex {α : Type} (result : Except Value.Error α) (index : Nat)
    (label : String) : IO Unit := do
  match result with
  | .error (.invalidBitIndex actual) =>
    unless actual == index do
      throw <| IO.userError s!"{label}: wrong rejected index"
  | _ => throw <| IO.userError s!"{label}: invalid bit index was not rejected first"

/-- Exhaust all input bytes and valid target bits; use arithmetic as an independent oracle. -/
def run : IO Unit := do
  let pre := bytes #[0x12, 0x34, 0x56]
  let suffix := bytes #[0x87, 0x65, 0x43, 0x21]
  for number in [:256] do
    let original := UInt8.ofNat number
    for target in [:8] do
      for enabled in [false, true] do
        let context := s!"bit update byte={number}, target={target}, enabled={enabled}"
        let .ok updated := Value.setBit original target enabled
          | throw <| IO.userError s!"{context}: valid update rejected"
        let weight := 2 ^ target
        let cleared := number - (number / weight % 2) * weight
        let expected := cleared + if enabled then weight else 0
        unless updated.toNat == expected do
          throw <| IO.userError s!"{context}: arithmetic update oracle mismatch"
        expect (Value.getBit (Value.putUInt8 updated) 0 target) enabled context
        expect (Value.getBit (pre ++ (Value.putUInt8 updated ++ suffix)) pre.size target)
          enabled s!"{context}: surrounded target readback"
        for other in [:8] do
          if other != target then
            let expectedOther := number / (2 ^ other) % 2 == 1
            expect (Value.getBit (Value.putUInt8 updated) 0 other) expectedOther
              s!"{context}: unrelated bit {other} changed"
            expect (Value.getBit (pre ++ (Value.putUInt8 updated ++ suffix)) pre.size other)
              expectedOther s!"{context}: surrounded unrelated bit {other} changed"
        expect (Value.setBit updated target enabled) updated s!"{context}: idempotence"
        let .ok opposite := Value.setBit original target (!enabled)
          | throw <| IO.userError s!"{context}: opposite update rejected"
        expect (Value.setBit opposite target enabled) updated s!"{context}: last write wins"
    for invalid in [8, 9, 255, 256, 65536, 4294967295] do
      for enabled in [false, true] do
        expectInvalidIndex (Value.setBit original invalid enabled) invalid
          s!"invalid bit {invalid} for byte {number}"
      for offset in [0, pre.size, 100000] do
        expectInvalidIndex (Value.getBit (pre ++ (Value.putUInt8 original ++ suffix)) offset invalid)
          invalid s!"invalid read bit {invalid} at offset {offset}"
        expectInvalidIndex (Value.getBit ByteArray.empty offset invalid) invalid
          s!"invalid read bit {invalid} in empty data"
  for valid in [:8] do
    match Value.getBit ByteArray.empty 0 valid with
    | .error (.decode _) => pure ()
    | _ => throw <| IO.userError s!"empty valid bit read {valid} did not reject the byte offset"
  IO.println "Bit update assurance: all 4,096 updates, unrelated bits, surrounding bytes, idempotence, overwrite, and invalid-index cases passed"

end LeanS7.BitUpdateAssuranceTests
