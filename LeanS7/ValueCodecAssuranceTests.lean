import LeanS7.ValueCodecAssurance
import LeanS7.SequenceConformance

namespace LeanS7.ValueCodecAssuranceTests

def run : IO Unit := do
  let pre := bytes #[0x11,0x22,0x33]
  let suffix := bytes #[0xde,0xad,0xbe,0xef]
  for number in [:65536] do
    let value := UInt16.ofNat number
    unless (match Value.getUInt16 (pre ++ (Value.putUInt16 value ++ suffix)) pre.size with
      | .ok actual => actual == value | .error _ => false) do
      throw <| IO.userError s!"surrounded WORD roundtrip failed: {number}"
    let signed := value.toInt16
    unless (match Value.getInt16 (pre ++ (Value.putInt16 signed ++ suffix)) pre.size with
      | .ok actual => actual == signed | .error _ => false) do
      throw <| IO.userError s!"surrounded INT roundtrip failed: {number}"
  for bits in (#[0,0x80000000,0x3f800000,0x7f800000,0xff800000,0x7fc00001] : Array UInt32) do
    let value := Float32.ofBits bits
    let .ok actual := Value.getReal (Value.putReal value)
      | throw <| IO.userError "REAL roundtrip failed"
    unless actual.toBits == (Float32.ofBits value.toBits).toBits do
      throw <| IO.userError "REAL bit interpretation changed"
  for bits in (#[0,0x8000000000000000,0x3ff0000000000000,0x7ff0000000000000,
      0xfff0000000000000,0x7ff8000000000001] : Array UInt64) do
    let value := Float.ofBits bits
    let .ok actual := Value.getLReal (Value.putLReal value)
      | throw <| IO.userError "LREAL roundtrip failed"
    unless actual.toBits == (Float.ofBits value.toBits).toBits do
      throw <| IO.userError "LREAL bit interpretation changed"
  Conformance.Sequences.validate
  IO.println "Value codec assurance: all 65,536 surrounded WORD/INT values and 12 conversation vectors passed"

end LeanS7.ValueCodecAssuranceTests
