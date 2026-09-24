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

end LeanS7.S7
