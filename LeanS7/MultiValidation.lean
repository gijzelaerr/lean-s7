import LeanS7.S7
import LeanS7.Chunking

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

/-- Counters and timers must be transferred in a single request. Their S7 address is
    a number, but the chunk planner advances every area by the bytes already
    transferred, which for these areas skips elements (500 counters from 16 are requested at
    16, 478 and 940), and the native Snap7 client and python-snap7 disagree about the correct
    step. Until a controller settles the addressing (gate H1) a longer transfer is rejected
    before any IO instead of risking reads or writes of the wrong elements. -/
def singleRequestOnly (area : S7.Area) : Bool :=
  area == .counters || area == .timers

/-- A counter or timer read must fit the negotiated PDU in one request. -/
def readFits (pduLength : Nat) (range : S7.MemoryRange) : Except S7.EncodeError Unit :=
  if singleRequestOnly range.area && readMaximum pduLength range.area < range.count then
    throw (.counterTimerSpansRequests range.count (readMaximum pduLength range.area))
  else
    pure ()

def writeMaximum (pduLength : Nat) (area : S7.Area) : Nat :=
  let lengthLimit := if area.dataTransportSize == S7.octetTransportSize then
    S7.maxSectionSize else S7.maxSectionSize / 8
  min S7.maxSectionSize (min (pduLength - 28) lengthLimit / area.elementSize)

/-- A counter or timer write must fit the negotiated PDU in one request. -/
def writeFits (pduLength : Nat) (range : S7.MemoryRange) : Except S7.EncodeError Unit :=
  if singleRequestOnly range.area && writeMaximum pduLength range.area < range.count then
    throw (.counterTimerSpansRequests range.count (writeMaximum pduLength range.area))
  else
    pure ()

/-- Validate every logical write before any packet is sent. This avoids local
    validation failures after earlier writes; remote writes are not atomic. -/
def writes (pduLength : Nat) (items : Array S7.WriteItem) : Except S7.EncodeError Unit := do
  for item in items do
    range item.range
    writeFits pduLength item.range
    let expected := item.range.count * item.range.area.elementSize
    if item.payload.size != expected then
      throw (.invalidSize item.payload.size)
    if writeMaximum pduLength item.range.area = 0 then
      throw (.invalidSize pduLength)

/-- An accepted counter or timer read is planned as exactly one request, so the unresolved
    chunk-advance rule is never exercised for these areas. -/
theorem readFits_single_request (pduLength : Nat) (range : S7.MemoryRange)
    (hfits : readFits pduLength range = .ok ()) (harea : singleRequestOnly range.area = true)
    (hpositive : 0 < range.count) :
    Chunking.counts range.count (readMaximum pduLength range.area) = [range.count] := by
  apply Chunking.counts_single _ _ hpositive
  by_cases hbig : readMaximum pduLength range.area < range.count
  · simp [readFits, harea, hbig] at hfits
  · omega

/-- The same holds for writes. -/
theorem writeFits_single_request (pduLength : Nat) (range : S7.MemoryRange)
    (hfits : writeFits pduLength range = .ok ()) (harea : singleRequestOnly range.area = true)
    (hpositive : 0 < range.count) :
    Chunking.counts range.count (writeMaximum pduLength range.area) = [range.count] := by
  apply Chunking.counts_single _ _ hpositive
  by_cases hbig : writeMaximum pduLength range.area < range.count
  · simp [writeFits, harea, hbig] at hfits
  · omega

end LeanS7.MultiValidation
