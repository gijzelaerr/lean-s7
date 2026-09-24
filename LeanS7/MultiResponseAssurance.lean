import LeanS7.S7

namespace LeanS7.S7

theorem ReadItemsMatch.getElem {ranges : List MemoryRange}
    {results : List ReadItemResult} (h : ReadItemsMatch ranges results)
    (i : Nat) (hr : i < ranges.length) (hs : i < results.length) :
    ReadItemMatches ranges[i] results[i] := by
  induction h generalizing i with
  | nil => simp at hr
  | cons head tail ih =>
    cases i with
    | zero => exact head
    | succ i => exact ih i (by simpa using hr) (by simpa using hs)

/-- The successful payload at index `i` has exactly the byte size of the caller's
    range at index `i`; preceding PLC failures do not shift this correspondence. -/
theorem decodeAreaReadMany_success_size (reference : UInt16)
    (ranges : Array MemoryRange) (response : Response) (results : Array ReadItemResult)
    (h : decodeAreaReadMany reference ranges response = .ok results)
    (i : Nat) (hr : i < ranges.size) (hs : i < results.size)
    (payload : ByteArray) (hitem : results[i] = .success payload) :
    payload.size = ranges[i].count * ranges[i].area.elementSize := by
  have hm := decodeAreaReadMany_matches reference ranges response results h
  have hp := hm.getElem i (by simpa using hr) (by simpa using hs)
  simpa [hitem, ReadItemMatches] using hp

/-- Every surfaced read failure is a genuine non-0xff status at its result index. -/
theorem decodeAreaReadMany_failure_code (reference : UInt16)
    (ranges : Array MemoryRange) (response : Response) (results : Array ReadItemResult)
    (h : decodeAreaReadMany reference ranges response = .ok results)
    (i : Nat) (hr : i < ranges.size) (hs : i < results.size)
    (code : UInt8) (hitem : results[i] = .failure code) : code ≠ 0xff := by
  have hm := decodeAreaReadMany_matches reference ranges response results h
  have hp := hm.getElem i (by simpa using hr) (by simpa using hs)
  simpa [hitem, ReadItemMatches] using hp

/-- Successful decoding consumes exactly the response's status-byte section. -/
theorem decodeAreaWriteMany_data_size (reference : UInt16) (expectedCount : Nat)
    (response : Response) (results : Array WriteItemResult)
    (h : decodeAreaWriteMany reference expectedCount response = .ok results) :
    response.data.size = expectedCount :=
  (decodeAreaWriteMany_contract reference expectedCount response results h).2.1

/-- Every write result is the return code at the same wire position, without
    filtering failures or treating the first success as a whole-batch ACK. -/
theorem decodeAreaWriteMany_status_order (reference : UInt16) (expectedCount : Nat)
    (response : Response) (results : Array WriteItemResult)
    (h : decodeAreaWriteMany reference expectedCount response = .ok results)
    (i : Nat) (hi : i < results.size) :
    ∃ hb : i < response.data.size,
      results[i] = WriteItemResult.ofReturnCode response.data[i] :=
  (decodeAreaWriteMany_contract reference expectedCount response results h).2.2 i hi

end LeanS7.S7
