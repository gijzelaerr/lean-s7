namespace LeanS7.Correlation

/-- The pure decision core for one in-flight request on the serialized client
    connection. `Client.exchangeBytesCurrent` calls `step` for every received
    PDU; only the receive/send IO stays in `Client.lean`. -/
structure Waiting where
  /-- PDU reference of the one request whose reply is being awaited. -/
  expected : UInt16
  /-- How many replies for other references may still be skipped. -/
  staleAllowance : Nat
  deriving Repr, BEq

def Waiting.start (expected : UInt16) (maxStale : Nat) : Waiting :=
  { expected, staleAllowance := maxStale }

inductive Outcome where
  /-- The incoming PDU answers the awaited request. -/
  | deliver
  /-- The incoming PDU belongs to another reference and is discarded. -/
  | skipStale (next : Waiting)
  /-- A further mismatching PDU exceeds the stale-reply allowance. -/
  | tooManyStale
  deriving Repr, BEq

def step (waiting : Waiting) (incoming : UInt16) : Outcome :=
  if incoming == waiting.expected then .deliver
  else if waiting.staleAllowance == 0 then .tooManyStale
  else .skipStale { waiting with staleAllowance := waiting.staleAllowance - 1 }

/-- A reply is delivered exactly when its reference equals the awaited one. -/
theorem step_deliver_iff (waiting : Waiting) (incoming : UInt16) :
    step waiting incoming = .deliver ↔ incoming = waiting.expected := by
  unfold step
  by_cases h : incoming = waiting.expected
  · simp [h]
  · have hb : (incoming == waiting.expected) = false := by simpa using h
    rw [hb]
    simp only [Bool.false_eq_true, if_false]
    split <;> simp [h]

/-- A mismatching reply never completes the request. -/
theorem step_stale_not_delivered (waiting : Waiting) (incoming : UInt16)
    (h : incoming ≠ waiting.expected) : step waiting incoming ≠ .deliver := by
  intro hd
  exact h ((step_deliver_iff waiting incoming).1 hd)

/-- A skipped reply spends exactly one unit of the stale allowance and never
    changes which reference is awaited. -/
theorem step_skip_spends_allowance (waiting next : Waiting) (incoming : UInt16)
    (h : step waiting incoming = .skipStale next) :
    next.expected = waiting.expected ∧ next.staleAllowance + 1 = waiting.staleAllowance ∧
      incoming ≠ waiting.expected := by
  unfold step at h
  by_cases hm : incoming = waiting.expected
  · simp [hm] at h
  · by_cases hz : waiting.staleAllowance = 0
    · simp [hm, hz] at h
    · simp [hm, hz] at h
      subst h
      simp only [true_and]
      exact ⟨by omega, hm⟩

/-- With no allowance left, a mismatching reply is a protocol failure. -/
theorem step_exhausted (waiting : Waiting) (incoming : UInt16)
    (hallowance : waiting.staleAllowance = 0) (h : incoming ≠ waiting.expected) :
    step waiting incoming = .tooManyStale := by
  simp [step, h, hallowance]

inductive Scan where
  /-- `skipped` are the discarded stale references before the delivered reply. -/
  | delivered (skipped : List UInt16)
  | tooManyStale
  /-- The observed replies ended before a verdict. -/
  | awaiting
  deriving Repr, BEq

/-- Iterate `step` over a finite sequence of received references; this is the
    loop in `Client.exchangeBytesCurrent` with the receive IO abstracted away. -/
def scan : Waiting → List UInt16 → Scan
  | _, [] => .awaiting
  | waiting, incoming :: rest =>
    match step waiting incoming with
    | .deliver => .delivered []
    | .tooManyStale => .tooManyStale
    | .skipStale next =>
      match scan next rest with
      | .delivered skipped => .delivered (incoming :: skipped)
      | other => other

/-- Delivery is only ever to the awaited reference: the delivered reply is the
    first one carrying it, every earlier reply was a mismatching stale one, and
    no more than the allowance were skipped. -/
theorem scan_delivered (waiting : Waiting) (references skipped : List UInt16)
    (h : scan waiting references = .delivered skipped) :
    ∃ rest, references = skipped ++ waiting.expected :: rest ∧
      (∀ stale ∈ skipped, stale ≠ waiting.expected) ∧
      skipped.length ≤ waiting.staleAllowance := by
  induction references generalizing waiting skipped with
  | nil => simp [scan] at h
  | cons incoming tail ih =>
    unfold scan at h
    cases hs : step waiting incoming with
    | deliver =>
      rw [hs] at h
      simp only [Scan.delivered.injEq] at h
      subst h
      have heq := (step_deliver_iff waiting incoming).1 hs
      exact ⟨tail, by simp [heq], by simp, by simp⟩
    | tooManyStale => rw [hs] at h; simp at h
    | skipStale next =>
      rw [hs] at h
      simp only at h
      cases hr : scan next tail with
      | delivered inner =>
        rw [hr] at h
        simp only [Scan.delivered.injEq] at h
        subst h
        obtain ⟨hexp, hallow, hne⟩ := step_skip_spends_allowance waiting next incoming hs
        obtain ⟨rest, hrefs, hall, hlen⟩ := ih next inner hr
        refine ⟨rest, ?_, ?_, ?_⟩
        · rw [hexp] at hrefs
          simp [hrefs]
        · intro stale hmem
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact hne
          · rw [hexp] at hall
            exact hall stale hmem
        · simp only [List.length_cons]
          omega
      | tooManyStale => rw [hr] at h; simp at h
      | awaiting => rw [hr] at h; simp at h

/-- Exceeding the allowance is only reported after more than `staleAllowance`
    consecutive replies, none of which carried the awaited reference. -/
theorem scan_tooManyStale (waiting : Waiting) (references : List UInt16)
    (h : scan waiting references = .tooManyStale) :
    ∃ stale rest, references = stale ++ rest ∧
      stale.length = waiting.staleAllowance + 1 ∧
      ∀ reference ∈ stale, reference ≠ waiting.expected := by
  induction references generalizing waiting with
  | nil => simp [scan] at h
  | cons incoming tail ih =>
    unfold scan at h
    cases hs : step waiting incoming with
    | deliver => rw [hs] at h; simp at h
    | tooManyStale =>
      have hne : incoming ≠ waiting.expected := by
        intro heq
        have := (step_deliver_iff waiting incoming).2 heq
        rw [hs] at this
        cases this
      have hz : waiting.staleAllowance = 0 := by
        unfold step at hs
        by_cases hm : incoming = waiting.expected
        · simp [hm] at hs
        · by_cases hz : waiting.staleAllowance = 0
          · exact hz
          · simp [hm, hz] at hs
      refine ⟨[incoming], tail, rfl, by simp [hz], ?_⟩
      intro reference hmem
      simp at hmem
      subst hmem
      exact hne
    | skipStale next =>
      rw [hs] at h
      simp only at h
      cases hr : scan next tail with
      | delivered inner => rw [hr] at h; simp at h
      | tooManyStale =>
        obtain ⟨hexp, hallow, hne⟩ := step_skip_spends_allowance waiting next incoming hs
        obtain ⟨stale, rest, hrefs, hlen, hall⟩ := ih next hr
        refine ⟨incoming :: stale, rest, by simp [hrefs], ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro reference hmem
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact hne
          · rw [hexp] at hall
            exact hall reference hmem
      | awaiting => rw [hr] at h; simp at h

/-- Reference allocation is a single wrapping counter, shared by every public
    operation through `Client.freshReference`. -/
def nextReference (reference : UInt16) : UInt16 := reference + 1

/-- Reference carried by the `index`th request issued after `start`. -/
def allocated (start : UInt16) (index : Nat) : UInt16 :=
  start + UInt16.ofNat index

/-- The allocator hands out the references in sequence, including across the
    16-bit wrap. -/
theorem allocated_succ (start : UInt16) (index : Nat) :
    allocated start (index + 1) = nextReference (allocated start index) := by
  unfold allocated nextReference
  rw [Nat.add_comm index 1]
  simp [UInt16.ofNat_add]
  first | rfl | ac_rfl | (rw [← UInt16.add_assoc, ← UInt16.add_assoc, UInt16.add_comm start 1])

/-- Within one window of 65 536 requests every request gets a distinct
    reference. Beyond it references are reused, which is why the stale
    allowance (not an unbounded history) is what guards correlation. -/
theorem allocated_injective_window (start : UInt16) (i j : Nat)
    (hi : i < 65536) (hj : j < 65536) (h : allocated start i = allocated start j) :
    i = j := by
  unfold allocated at h
  have h' : UInt16.ofNat i = UInt16.ofNat j := by
    have := congrArg (fun x => x - start) h
    simpa using this
  have hi' := congrArg UInt16.toNat h'
  simp [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hi'
  exact hi'

/-- A reply carrying the reference of an earlier request is never delivered to
    a later request that is less than one reference window behind it, even when
    the 16-bit counter has wrapped in between. -/
theorem earlier_reply_not_delivered (start : UInt16) (i j : Nat) (maxStale : Nat)
    (hi : i < 65536) (hj : j < 65536) (hne : i ≠ j) :
    step (Waiting.start (allocated start j) maxStale) (allocated start i) ≠ .deliver := by
  apply step_stale_not_delivered
  intro h
  exact hne (allocated_injective_window start i j hi hj h)

end LeanS7.Correlation
