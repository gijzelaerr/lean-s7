import LeanS7.S7

namespace LeanS7.MultiValidation

/-- Validate a logical range without imposing the per-packet count limit.
    Chunking may split the count, but cannot repair an invalid final address. -/
def range (value : S7.MemoryRange) : Except S7.EncodeError Unit := do
  S7.validateMemoryRange { value with count := 1 }
  if value.count = 0 then
    throw (.invalidSize value.count)
  if value.lastWireAddress > 0xffffff then
    throw (.addressTooLarge value.start)

def readMaximum (pduLength : Nat) (area : S7.Area) : Nat :=
  let lengthLimit := if area.dataTransportSize == S7.octetTransportSize then
    S7.maxSectionSize else S7.maxSectionSize / 8
  if pduLength < 24 then 0 else
    min S7.maxSectionSize (min (pduLength - 18) lengthLimit / area.elementSize)

/-- Successful read payloads use a UInt16 length, measured in bits for byte
    transport and in bytes for octet transport. PDU space alone is insufficient. -/
def readLengthRepresentable (range : S7.MemoryRange) : Bool :=
  let limit := if range.area.dataTransportSize == S7.octetTransportSize then
    S7.maxSectionSize else S7.maxSectionSize / 8
  range.count * range.area.elementSize ≤ limit

def writeMaximum (pduLength : Nat) (area : S7.Area) : Nat :=
  let lengthLimit := if area.dataTransportSize == S7.octetTransportSize then
    S7.maxSectionSize else S7.maxSectionSize / 8
  min S7.maxSectionSize (min (pduLength - 28) lengthLimit / area.elementSize)

/-- Validate every logical write before any packet is sent. This avoids local
    validation failures after earlier writes; remote writes are not atomic. -/
def writes (pduLength : Nat) (items : Array S7.WriteItem) : Except S7.EncodeError Unit := do
  for item in items do
    range item.range
    let expected := item.range.count * item.range.area.elementSize
    if item.payload.size != expected then
      throw (.invalidSize item.payload.size)
    if writeMaximum pduLength item.range.area = 0 then
      throw (.invalidSize pduLength)

end LeanS7.MultiValidation
