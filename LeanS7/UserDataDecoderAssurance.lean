import LeanS7.Management

namespace LeanS7.S7

set_option backward.split false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Accepted USER_DATA replies correlate with the caller's service and reference,
    and never expose a nonzero parameter error. This is an actual-decoder
    implication for arbitrary packets, not an encoder round trip. -/
theorem decodeUserDataResponse_correlation (reference : UInt16)
    (group subfunction : UInt8) (packet : ByteArray) (response : UserDataResponse)
    (h : decodeUserDataResponse reference group subfunction packet = .ok response) :
    response.reference = reference ∧ response.group = group ∧
      response.subfunction = subfunction ∧ response.error = 0 := by
  unfold decodeUserDataResponse at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h <;>
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h)
  all_goals
    simp only [Except.ok.injEq] at h
    subst response
    simp_all

set_option backward.split false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The only accepted data-header dialects are octet success and the exact
    complete empty null acknowledgement for the three supported services. -/
theorem decodeUserDataResponse_transport (reference : UInt16)
    (group subfunction : UInt8) (packet : ByteArray) (response : UserDataResponse)
    (h : decodeUserDataResponse reference group subfunction packet = .ok response) :
    (response.returnCode = 0xff ∧ response.transportSize = octetTransportSize) ∨
    (response.returnCode = 0x0a ∧
      supportsNullUserDataAcknowledgement group subfunction = true ∧
      response.transportSize = 0 ∧ response.payload.size = 0 ∧
      response.hasMoreData = false) := by
  unfold decodeUserDataResponse at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h <;>
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h)
  all_goals
    simp only [Except.ok.injEq] at h
    subst response
    simp_all
    try
      apply ByteArray.size_eq_zero_iff.mp
      exact Cursor.readBytes_size _ _ _ _ (by assumption)

private theorem read8_data (cursor : Cursor) (result : UInt8 × Cursor)
    (h : cursor.readUInt8 = .ok result) : result.2.data = cursor.data := by
  unfold Cursor.readUInt8 at h
  split at h
  · cases h; rfl
  · contradiction

private theorem read8_offset (cursor : Cursor) (result : UInt8 × Cursor)
    (h : cursor.readUInt8 = .ok result) : result.2.offset = cursor.offset + 1 := by
  unfold Cursor.readUInt8 at h
  split at h
  · cases h; rfl
  · contradiction

set_option backward.split false in
private theorem read16_data (cursor : Cursor) (result : UInt16 × Cursor)
    (h : cursor.readUInt16BE = .ok result) : result.2.data = cursor.data := by
  unfold Cursor.readUInt16BE at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  simp only [Except.ok.injEq] at h
  subst result
  exact (read8_data _ _ (by assumption)).trans (read8_data _ _ (by assumption))

set_option backward.split false in
private theorem read16_offset (cursor : Cursor) (result : UInt16 × Cursor)
    (h : cursor.readUInt16BE = .ok result) : result.2.offset = cursor.offset + 2 := by
  unfold Cursor.readUInt16BE at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  simp only [Except.ok.injEq] at h
  subst result
  rw [read8_offset _ _ (by assumption), read8_offset _ _ (by assumption)]
  try omega

private theorem readBytes_data (cursor : Cursor) (count : Nat)
    (result : ByteArray × Cursor) (h : cursor.readBytes count = .ok result) :
    result.2.data = cursor.data := by
  unfold Cursor.readBytes at h
  split at h
  · cases h; rfl
  · contradiction

private theorem readBytes_offset (cursor : Cursor) (count : Nat)
    (result : ByteArray × Cursor) (h : cursor.readBytes count = .ok result) :
    result.2.offset = cursor.offset + count := by
  unfold Cursor.readBytes at h
  split at h
  · cases h; rfl
  · contradiction

private theorem readBytes_length (cursor : Cursor) (count : Nat)
    (result : ByteArray × Cursor) (h : cursor.readBytes count = .ok result) :
    result.1.size = count := Cursor.readBytes_size cursor result.2 count result.1 h

private theorem finish_offset (cursor : Cursor) (result : Unit)
    (h : cursor.finish = .ok result) : cursor.offset = cursor.data.size := by
  unfold Cursor.finish at h
  split at h
  · assumption
  · contradiction

/-- A sequential witness for the data section consumed by the actual decoder. -/
structure UserDataPayloadWire (packet payload : ByteArray) where
  data : ByteArray
  returnCode : UInt8
  transportSize : UInt8
  payloadLength : UInt16
  sectionLength : UInt16
  afterReturn : Cursor
  afterTransport : Cursor
  afterLength : Cursor
  afterPayload : Cursor
  sectionStart : Cursor
  sectionEnd : Cursor
  payloadRead : afterLength.readBytes payloadLength.toNat = .ok (payload, afterPayload)
  lengthRead : afterTransport.readUInt16BE = .ok (payloadLength, afterLength)
  transportRead : afterReturn.readUInt8 = .ok (transportSize, afterTransport)
  returnRead : Cursor.readUInt8 { data } = .ok (returnCode, afterReturn)
  complete : afterPayload.finish = .ok ()
  sectionRead : sectionStart.readBytes sectionLength.toNat = .ok (data, sectionEnd)
  packetExtent : packet.size = jobHeaderSize + 12 + sectionLength.toNat

set_option backward.split false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Acceptance exposes the payload obtained by four sequential data-header
    bytes and a bounded payload read which finishes the complete data section. -/
theorem decodeUserDataResponse_payload_wire (reference : UInt16)
    (group subfunction : UInt8) (packet : ByteArray) (response : UserDataResponse)
    (h : decodeUserDataResponse reference group subfunction packet = .ok response) :
    Nonempty (UserDataPayloadWire packet response.payload) := by
  unfold decodeUserDataResponse at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  all_goals
    simp only [Except.ok.injEq] at h
    subst response
    rename_i _ dataLength _ hdeclared hparameterLength
      _ parameters hparameters _ dataSection hsection _ packetDone _
      _ parameterPrefix _ _ _ parameterDataLength _ _ _ method _ _ _ typeGroup _ _
      _ actualSubfunction _ _ _ sequence _ _ dataUnit _ _ lastUnit _ _
      _ errorCode _ _ parameterDone _ _ _
      _ returnItem hreturn _ transportItem htransport _ lengthItem hlength _ _ _
      _ payloadItem hpayload _ done hdone
    refine ⟨{
      data := dataSection.1, returnCode := returnItem.1, transportSize := transportItem.1,
      payloadLength := lengthItem.1, sectionLength := dataLength.1,
      afterReturn := returnItem.2, afterTransport := transportItem.2,
      afterLength := lengthItem.2, afterPayload := payloadItem.2,
      sectionStart := parameters.2, sectionEnd := dataSection.2,
      payloadRead := hpayload, lengthRead := hlength, transportRead := htransport,
      returnRead := hreturn, complete := ?_, sectionRead := hsection,
      packetExtent := ?_ }⟩
    · cases done; exact hdone
    · simp_all

theorem UserDataPayloadWire.extent {packet payload : ByteArray}
    (wire : UserDataPayloadWire packet payload) :
    packet.size = jobHeaderSize + 12 + 4 + payload.size := by
  have h0d := read8_data _ _ wire.returnRead
  have h0o := read8_offset _ _ wire.returnRead
  have h1d := read8_data _ _ wire.transportRead
  have h1o := read8_offset _ _ wire.transportRead
  have h2d := read16_data _ _ wire.lengthRead
  have h2o := read16_offset _ _ wire.lengthRead
  have h3d := readBytes_data _ _ _ wire.payloadRead
  have h3o := readBytes_offset _ _ _ wire.payloadRead
  have hf := finish_offset _ _ wire.complete
  have hp := Cursor.readBytes_size _ _ _ _ wire.payloadRead
  have hs := Cursor.readBytes_size _ _ _ _ wire.sectionRead
  have he := wire.packetExtent
  simp_all only
  omega

set_option backward.split false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Every accepted packet consists of exactly the ten-byte common header,
    twelve-byte parameter section and four-byte data header followed by the
    exposed payload. Neither a section nor the complete PDU has trailing bytes. -/
theorem decodeUserDataResponse_packet_size (reference : UInt16)
    (group subfunction : UInt8) (packet : ByteArray) (response : UserDataResponse)
    (h : decodeUserDataResponse reference group subfunction packet = .ok response) :
    packet.size = jobHeaderSize + 12 + 4 + response.payload.size := by
  obtain ⟨wire⟩ := decodeUserDataResponse_payload_wire reference group subfunction packet response h
  exact wire.extent

/-- Every byte with the USER_DATA response type in its high nibble is that type with
    its low nibble as the function group. -/
private theorem userDataTypeGroup_all : ∀ n, n < 256 →
    UInt8.land (UInt8.ofNat n) 0xf0 = 0x80 →
      UInt8.ofNat n = UInt8.lor 0x80 (UInt8.land (UInt8.ofNat n) 0x0f) := by
  decide +kernel

private theorem userDataTypeGroup (typeGroup : UInt8)
    (h : UInt8.land typeGroup 0xf0 = userDataResponseType) :
    UInt8.lor userDataResponseType (UInt8.land typeGroup 0x0f) = typeGroup := by
  have := userDataTypeGroup_all typeGroup.toNat typeGroup.toNat_lt
  rw [UInt8.ofNat_toNat] at this
  exact (this h).symm

set_option backward.split false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Canonical decoding of a USER_DATA response: re-encoding an accepted response
    reproduces the input with only the reserved word (offsets 2–3) cleared. -/
theorem decodeUserDataResponse_canonical (expectedReference : UInt16)
    (expectedGroup expectedSubfunction : UInt8) (pdu : ByteArray) (response : UserDataResponse)
    (h : decodeUserDataResponse expectedReference expectedGroup expectedSubfunction pdu =
      .ok response) :
    encodeUserDataResponse response = pdu.extract 0 2 ++ bytes #[0, 0] ++ pdu.extract 4 pdu.size := by
  unfold decodeUserDataResponse at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  all_goals
    simp only [Except.ok.injEq] at h
    subst response
  all_goals
    rename_i x0 r0 e0 hpid x1 r1 e1 htype x2 r2 e2 x3 r3 e3 href x4 r4 e4 x5 r5 e5 hsize hplen
      x6 r6 e6 x7 r7 e7 x8 r8 e8 x9 r9 e9 hhead x10 r10 e10 hpdl x11 r11 e11 hmethod
      x12 r12 e12 htg x13 r13 e13 hsub x14 r14 e14 x15 r15 e15 x16 r16 e16 hlast
      x17 r17 e17 x18 r18 e18 herr hdsize x19 r19 e19 x20 r20 e20 x21 r21 e21 hrc hnull hts
      x22 r22 e22 x23 r23 e23
    -- The outer cursor: header fields, then the parameter and data sections.
    obtain ⟨l0, d0, n0⟩ := Cursor.readUInt8_value _ _ _ e0
    rw [n0] at e1
    obtain ⟨l1, d1, n1⟩ := Cursor.readUInt8_value _ _ _ e1
    rw [n1] at e2
    obtain ⟨l2, d2, n2⟩ := Cursor.readUInt16BE_value _ _ _ e2
    rw [n2] at e3
    obtain ⟨l3, d3, n3⟩ := Cursor.readUInt16BE_value _ _ _ e3
    rw [n3] at e4
    obtain ⟨l4, d4, n4⟩ := Cursor.readUInt16BE_value _ _ _ e4
    rw [n4] at e5
    obtain ⟨l5, d5, n5⟩ := Cursor.readUInt16BE_value _ _ _ e5
    rw [n5] at e6
    have s6 := Cursor.readBytes_size _ _ _ _ e6
    obtain ⟨p6, n6⟩ := Cursor.readBytes_value _ _ _ _ e6
    rw [n6] at e7
    have s7 := Cursor.readBytes_size _ _ _ _ e7
    obtain ⟨p7, n7⟩ := Cursor.readBytes_value _ _ _ _ e7
    rw [n7] at e8
    have f8 := Cursor.finish_ok _ e8
    -- The parameter cursor.
    obtain ⟨p9, n9⟩ := Cursor.readBytes_value _ _ _ _ e9
    rw [n9] at e10
    obtain ⟨l10, d10, n10⟩ := Cursor.readUInt8_value _ _ _ e10
    rw [n10] at e11
    obtain ⟨l11, d11, n11⟩ := Cursor.readUInt8_value _ _ _ e11
    rw [n11] at e12
    obtain ⟨l12, d12, n12⟩ := Cursor.readUInt8_value _ _ _ e12
    rw [n12] at e13
    obtain ⟨l13, d13, n13⟩ := Cursor.readUInt8_value _ _ _ e13
    rw [n13] at e14
    obtain ⟨l14, d14, n14⟩ := Cursor.readUInt8_value _ _ _ e14
    rw [n14] at e15
    obtain ⟨l15, d15, n15⟩ := Cursor.readUInt8_value _ _ _ e15
    rw [n15] at e16
    obtain ⟨l16, d16, n16⟩ := Cursor.readUInt8_value _ _ _ e16
    rw [n16] at e17
    obtain ⟨l17, d17, n17⟩ := Cursor.readUInt16BE_value _ _ _ e17
    rw [n17] at e18
    have f18 := Cursor.finish_ok _ e18
    -- The data cursor.
    obtain ⟨l19, d19, n19⟩ := Cursor.readUInt8_value _ _ _ e19
    rw [n19] at e20
    obtain ⟨l20, d20, n20⟩ := Cursor.readUInt8_value _ _ _ e20
    rw [n20] at e21
    obtain ⟨l21, d21, n21⟩ := Cursor.readUInt16BE_value _ _ _ e21
    rw [n21] at e22
    have s22 := Cursor.readBytes_size _ _ _ _ e22
    obtain ⟨p22, n22⟩ := Cursor.readBytes_value _ _ _ _ e22
    rw [n22] at e23
    have f23 := Cursor.finish_ok _ e23
    simp only [Nat.zero_add, Nat.reduceAdd] at l0 l1 l2 l3 l4 l5 d0 d1 d2 d3 d4 d5 p6 p7 f8
    simp only [Nat.zero_add, Nat.reduceAdd] at p9 l10 l11 l12 l13 l14 l15 l16 l17
    simp only [Nat.zero_add, Nat.reduceAdd] at d10 d11 d12 d13 d14 d15 d16 d17 f18
    simp only [Nat.zero_add, Nat.reduceAdd] at l19 l20 l21 d19 d20 d21 p22 f23
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hpid htype hplen hhead hpdl hmethod herr
    simp only [jobHeaderSize, bne_iff_ne, ne_eq, Decidable.not_not] at hsize
    have hhead' : r9.fst = bytes #[0, 1, 18] := by
      have hb : (r9.fst == bytes #[0, 1, 18]) = true := by simpa [bne] using hhead
      exact ByteArray.ext (beq_iff_eq.mp (show (r9.fst.data == (bytes #[0, 1, 18]).data) = true
        from hb))
    -- The function group and the continuation flag, from the decoder's checks.
    have hgroup : UInt8.lor userDataResponseType expectedGroup = r12.fst := by
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at htg
      rw [← htg.2]
      exact userDataTypeGroup _ htg.1
    have hflag : (if (r16.fst != 0) = true then (1 : UInt8) else 0) = r16.fst := by
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hlast
      by_cases h0 : r16.fst = 0
      · simp [h0]
      · simp [hlast h0]
    -- The twelve parameter bytes.
    have hPmid : bytes #[8, userDataResponseMethod, r12.fst, r13.fst, r14.fst, r15.fst, r16.fst] =
        r6.fst.extract 3 10 := by
      rw [← hpdl, ← hmethod, ← d10, ← d11, ← d12, ← d13, ← d14, ← d15, ← d16]
      apply ByteArray.ext
      simp only [bytes, ByteArray.data_extract]
      apply Array.ext
      · simp; omega
      · intro i hi _
        simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Array.getElem_extract, ByteArray.getElem_eq_getElem_data]
    have hP : bytes #[0, 1, 0x12, 8, userDataResponseMethod,
          UInt8.lor userDataResponseType expectedGroup, r13.fst, r14.fst, r15.fst,
          if (r16.fst != 0) = true then 1 else 0] ++ uint16BE r17.fst = r6.fst := by
      rw [hgroup, hflag,
        show bytes #[0, 1, 0x12, 8, userDataResponseMethod, r12.fst, r13.fst, r14.fst, r15.fst,
            r16.fst] = bytes #[0, 1, 0x12] ++
            bytes #[8, userDataResponseMethod, r12.fst, r13.fst, r14.fst, r15.fst, r16.fst] from rfl,
        hPmid, ← hhead', p9, d17, ← ByteArray.extract_two_uint16BE _ 10 (by omega)]
      simp only [Nat.reduceAdd]
      rw [ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
        ByteArray.extract_append_extract_of_le _ (by omega) (by omega), f18,
        ByteArray.extract_zero_size]
    -- The data section.
    have hD : bytes #[r19.fst, r20.fst] ++ (uint16BE (UInt16.ofNat r22.fst.size) ++ r22.fst) =
        r7.fst := by
      rw [s22, UInt16.ofNat_toNat, d21, ← ByteArray.extract_two_uint16BE _ 2 (by omega), ← d19,
        ← d20, show bytes #[r7.fst[0], r7.fst[1]] = r7.fst.extract 0 2 from
          (ByteArray.extract_two r7.fst 0 (by omega)).symm, p22]
      simp only [Nat.reduceAdd]
      rw [ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
        ByteArray.extract_append_extract_of_le _ (by omega) (by omega), f23,
        ByteArray.extract_zero_size]
    have hlen : UInt16.ofNat (4 + r22.fst.size) = r5.fst := by
      rw [s22, f23, s7, UInt16.ofNat_toNat]
    -- The outer PDU.
    simp only [encodeUserDataResponse, ByteArray.append_assoc]
    rw [hD, ← @ByteArray.append_assoc _ (uint16BE r17.fst), hP, hlen, d5,
      ← ByteArray.extract_two_uint16BE _ 8 (by omega), ← hplen, d4,
      ← ByteArray.extract_two_uint16BE _ 6 (by omega), d3,
      ← ByteArray.extract_two_uint16BE _ 4 (by omega), p6, p7,
      show bytes #[protocolId, userDataType, 0, 0] =
        bytes #[protocolId, userDataType] ++ bytes #[0, 0] from rfl,
      ← hpid, ← htype, ← d0, ← d1,
      show bytes #[pdu[0], pdu[1]] = pdu.extract 0 2 from
        (ByteArray.extract_two pdu 0 (by omega)).symm]
    simp only [Nat.reduceAdd, ByteArray.append_assoc]
    rw [ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
      ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
      ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
      ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ← hsize]

end LeanS7.S7
