import LeanS7.Client

namespace LeanS7.S7

/-- The actual encoded addresses have the exact parameter length used by the planner. -/
theorem encodeReadAddresses_size (ranges : List MemoryRange) (encoded : ByteArray)
    (hencode : encodeReadAddresses ranges = .ok encoded) :
    encoded.size = 12 * ranges.length := by
  induction ranges generalizing encoded with
  | nil => simp [encodeReadAddresses] at hencode; subst encoded; simp
  | cons range rest ih =>
    simp only [encodeReadAddresses] at hencode
    cases ha : encodeMemoryAddress range with
    | error error => simp [ha, bind, Except.bind] at hencode
    | ok address =>
      cases ht : encodeReadAddresses rest with
      | error error => simp [ha, ht, bind, Except.bind] at hencode
      | ok tail =>
        simp [ha, ht, bind, Except.bind, pure, Except.pure] at hencode
        subst encoded
        have := encodedMemoryAddress_size range address ha
        have := ih tail ht
        simp only [ByteArray.size_append, List.length_cons]
        omega

/-- Includes actual optional inter-item padding, bounded by the conservative
    padding charged for every item by the write planner. -/
theorem encodeWriteSections_bound (items : List WriteItem)
    (parameters data : ByteArray)
    (hencode : encodeWriteSections items = .ok (parameters, data)) :
    parameters.size + data.size ≤ LeanS7.writeRequestContributions items := by
  induction items generalizing parameters data with
  | nil =>
    simp [encodeWriteSections] at hencode
    rcases hencode with ⟨rfl, rfl⟩
    simp [LeanS7.writeRequestContributions]
  | cons item rest ih =>
    simp only [encodeWriteSections] at hencode
    cases ha : encodeMemoryAddress item.range with
    | error error => simp [ha, bind, Except.bind] at hencode
    | ok address =>
      simp only [ha, bind, Except.bind] at hencode
      split at hencode
      · contradiction
      split at hencode
      all_goals
        split at hencode
        · contradiction
        · cases ht : encodeWriteSections rest with
          | error error => simp [ht] at hencode
          | ok sections =>
            rcases sections with ⟨tailParameters, tailData⟩
            simp only [ht, pure, Except.pure] at hencode
            injection hencode with heq
            cases heq
            have hadd := encodedMemoryAddress_size item.range address ha
            have htail := ih tailParameters tailData ht
            simp only [LeanS7.writeRequestContributions, List.map_cons,
              List.sum_cons, LeanS7.writeRequestContribution] at *
            simp only [ByteArray.size_append, uint16BE_size]
            split
            · simp
              have hodd : item.payload.size % 2 ≠ 0 := by
                rename_i hp
                simp only [Bool.and_eq_true, bne_iff_ne] at hp
                exact hp.2
              omega
            · simp
              omega

theorem encodedAreaReadMany_size (reference : UInt16) (ranges : Array MemoryRange)
    (packet : ByteArray) (hencode : encodeAreaReadMany reference ranges = .ok packet) :
    packet.size = 12 + 12 * ranges.size := by
  simp only [encodeAreaReadMany] at hencode
  split at hencode
  · contradiction
  cases ha : encodeReadAddresses ranges.toList with
  | error error => simp [ha, bind, Except.bind] at hencode
  | ok addresses =>
    simp only [ha, bind, Except.bind] at hencode
    have hs := encodedJob_size _ packet hencode
    have haSize := encodeReadAddresses_size ranges.toList addresses ha
    simp [jobHeaderSize, haSize] at hs
    omega

theorem encodedAreaWriteMany_bound (reference : UInt16) (items : Array WriteItem)
    (packet : ByteArray) (hencode : encodeAreaWriteMany reference items = .ok packet) :
    packet.size ≤ 12 + LeanS7.writeRequestContributions items.toList := by
  simp only [encodeAreaWriteMany] at hencode
  split at hencode
  · contradiction
  cases ha : encodeWriteSections items.toList with
  | error error => simp [ha, bind, Except.bind] at hencode
  | ok sections =>
    rcases sections with ⟨parameters, data⟩
    simp only [ha, bind, Except.bind] at hencode
    have hs := encodedJob_size _ packet hencode
    have hb := encodeWriteSections_bound items.toList parameters data ha
    simp [jobHeaderSize] at hs
    omega

theorem encodedReadBatch_fits (reference : UInt16) (ranges : Array MemoryRange)
    (packet : ByteArray) (pduLength : Nat)
    (hencode : encodeAreaReadMany reference ranges = .ok packet)
    (hbudget : 12 + 12 * ranges.size ≤ pduLength) : packet.size ≤ pduLength := by
  rw [encodedAreaReadMany_size reference ranges packet hencode]
  exact hbudget

theorem encodedWriteBatch_fits (reference : UInt16) (items : Array WriteItem)
    (packet : ByteArray) (pduLength : Nat)
    (hencode : encodeAreaWriteMany reference items = .ok packet)
    (hbudget : 12 + LeanS7.writeRequestContributions items.toList ≤ pduLength) :
    packet.size ≤ pduLength :=
  Nat.le_trans (encodedAreaWriteMany_bound reference items packet hencode) hbudget

/-- Instantiates the actual request-size theorem with the client's read-plan
    certificate; the response-side budget remains the certificate's other conjunct. -/
theorem plannedReadBatch_fits (reference : UInt16) (pduLength : Nat)
    (pending : List MemoryRange) (plan : LeanS7.ReadBatchPlan pduLength pending)
    (packet : ByteArray) (hminimum : 14 ≤ pduLength)
    (hencode : encodeAreaReadMany reference plan.selected.toArray = .ok packet) :
    packet.size ≤ pduLength := by
  apply encodedReadBatch_fits reference plan.selected.toArray packet pduLength hencode
  simpa using (plan.budgets hminimum).1

/-- The conservative planner budget bounds the actual write request, including
    odd payload padding but excluding unnecessary padding after the last item. -/
theorem plannedWriteBatch_fits (reference : UInt16) (pduLength : Nat)
    (pending : List WriteItem) (plan : LeanS7.WriteBatchPlan pduLength pending)
    (packet : ByteArray) (hminimum : 14 ≤ pduLength)
    (hencode : encodeAreaWriteMany reference plan.selected.toArray = .ok packet) :
    packet.size ≤ pduLength := by
  apply encodedWriteBatch_fits reference plan.selected.toArray packet pduLength hencode
  simpa using (plan.budgets hminimum).1

end LeanS7.S7
