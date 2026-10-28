import LeanS7.TPKT
import LeanS7.COTP
import LeanS7.S7

namespace LeanS7.Protocol

inductive EncodeError where
  | s7 (error : S7.EncodeError)
  | tpkt (error : TPKT.EncodeError)
  deriving Repr, BEq

/-- Encode a complete RFC 1006 / COTP / classic S7 job packet. -/
def encodeJob (job : S7.Job) : Except EncodeError ByteArray := do
  let s7 ← (S7.encodeJob job).mapError .s7
  (TPKT.encode { payload := COTP.encodeData { payload := s7 } }).mapError .tpkt

/-- Decode exactly one complete RFC 1006 / COTP / classic S7 job packet. -/
def decodeJob (packet : ByteArray) : Except DecodeError S7.Job := do
  let frame ← TPKT.decode packet
  let cotp ← COTP.decodeData frame.payload
  if !cotp.endOfTransmission then
    throw (.invalidField (TPKT.headerSize + 2)
      "segmented COTP data cannot be decoded as a complete S7 job")
  S7.decodeJob cotp.payload

/-- Encode a complete RFC 1006 / COTP / successful S7 ACK_DATA packet. -/
def encodeAckData (reference : UInt16) (parameters data : ByteArray) :
    Except EncodeError ByteArray := do
  let s7 ← (S7.encodeAckData reference parameters data).mapError .s7
  (TPKT.encode { payload := COTP.encodeData { payload := s7 } }).mapError .tpkt

/-- Encode a complete RFC 1006 / COTP / S7 ACK or ACK_DATA packet, error class and
    code included: the canonical form of the packets `decodeResponse` accepts. -/
def encodeResponse (response : S7.Response) : Except EncodeError ByteArray := do
  let s7 ← (S7.encodeResponse response).mapError .s7
  (TPKT.encode { payload := COTP.encodeData { payload := s7 } }).mapError .tpkt

/-- `encodeAckData` encodes the ACK_DATA packet with a clear error class and code. -/
theorem encodeAckData_eq_encodeResponse (reference : UInt16) (parameters data : ByteArray) :
    encodeAckData reference parameters data = encodeResponse {
      pduType := S7.ackDataType, reference, parameters, data, errorClass := 0, errorCode := 0 } := by
  simp only [encodeAckData, encodeResponse, S7.encodeAckData_eq_encodeResponse]

/-- Decode exactly one complete RFC 1006 / COTP / S7 response packet. -/
def decodeResponse (packet : ByteArray) : Except DecodeError S7.Response := do
  let frame ← TPKT.decode packet
  let cotp ← COTP.decodeData frame.payload
  if !cotp.endOfTransmission then
    throw (.invalidField (TPKT.headerSize + 2)
      "segmented COTP data cannot be decoded as a complete S7 response")
  S7.decodeResponse cotp.payload

/-- A packet budget that includes every framing header is sufficient to encode
    a complete job whose individual S7 sections fit their wire fields. -/
theorem encodeJob_succeeds (job : S7.Job)
    (hparameters : job.parameters.size ≤ S7.maxSectionSize)
    (hdata : job.data.size ≤ S7.maxSectionSize)
    (hpacket : TPKT.headerSize + 3 + S7.jobHeaderSize +
      job.parameters.size + job.data.size ≤ TPKT.maxFrameSize) :
    ∃ packet, encodeJob job = .ok packet := by
  let s7 := bytes #[S7.protocolId, S7.jobType, 0, 0] ++
    uint16BE job.reference ++ uint16BE (UInt16.ofNat job.parameters.size) ++
    uint16BE (UInt16.ofNat job.data.size) ++ job.parameters ++ job.data
  have hs7 : S7.encodeJob job = .ok s7 := by
    rw [S7.encodeJob, if_neg (Nat.not_lt.mpr hparameters),
      if_neg (Nat.not_lt.mpr hdata)]
    rfl
  let frame : TPKT.Frame := { payload := COTP.encodeData { payload := s7 } }
  have hs7Size : s7.size = S7.jobHeaderSize + job.parameters.size + job.data.size :=
    S7.encodedJob_size job s7 hs7
  have hframeSize : TPKT.headerSize + frame.payload.size ≤ TPKT.maxFrameSize := by
    simp [frame, COTP.encodedData_size, hs7Size] at hpacket ⊢
    omega
  have hframeMin : TPKT.minFrameSize ≤ TPKT.headerSize + frame.payload.size := by
    simp [frame, COTP.encodedData_size, hs7Size, TPKT.minFrameSize,
      TPKT.headerSize, S7.jobHeaderSize]
    omega
  obtain ⟨packet, ht⟩ := TPKT.encode_succeeds_of_size frame hframeMin hframeSize
  refine ⟨packet, ?_⟩
  rw [encodeJob, hs7]
  change Except.mapError EncodeError.tpkt (TPKT.encode frame) = .ok packet
  rw [ht]
  rfl

/-- Complete-stack encode/decode round trip for every S7 job that fits one TPKT
    frame. This composes the independently checked S7, COTP, and TPKT proofs. -/
theorem decodeJob_encodeJob (job : S7.Job) (packet : ByteArray)
    (hparameters : job.parameters.size ≤ S7.maxSectionSize)
    (hdata : job.data.size ≤ S7.maxSectionSize)
    (hpacket : TPKT.headerSize + 3 + S7.jobHeaderSize +
      job.parameters.size + job.data.size ≤ TPKT.maxFrameSize)
    (hencode : encodeJob job = .ok packet) :
    decodeJob packet = .ok job := by
  let s7 := bytes #[S7.protocolId, S7.jobType, 0, 0] ++
    uint16BE job.reference ++ uint16BE (UInt16.ofNat job.parameters.size) ++
    uint16BE (UInt16.ofNat job.data.size) ++ job.parameters ++ job.data
  have hs7 : S7.encodeJob job = .ok s7 := by
    rw [S7.encodeJob, if_neg (Nat.not_lt.mpr hparameters),
      if_neg (Nat.not_lt.mpr hdata)]
    rfl
  let cotp : COTP.Data := { payload := s7 }
  let frame : TPKT.Frame := { payload := COTP.encodeData cotp }
  have hs7Size : s7.size = S7.jobHeaderSize + job.parameters.size + job.data.size :=
    S7.encodedJob_size job s7 hs7
  have hframeSize : TPKT.headerSize + frame.payload.size ≤ TPKT.maxFrameSize := by
    simp [frame, cotp, COTP.encodedData_size, hs7Size] at hpacket ⊢
    omega
  have hframeMin : TPKT.minFrameSize ≤ TPKT.headerSize + frame.payload.size := by
    simp [frame, cotp, COTP.encodedData_size, hs7Size, TPKT.minFrameSize,
      TPKT.headerSize, S7.jobHeaderSize]
    omega
  have ht : TPKT.encode frame = .ok packet := by
    rw [encodeJob, hs7] at hencode
    change Except.mapError EncodeError.tpkt (TPKT.encode frame) = .ok packet at hencode
    cases htResult : TPKT.encode frame with
    | error error => simp [htResult, Except.mapError] at hencode
    | ok encoded =>
        have heq : encoded = packet := by
          simpa [htResult, Except.mapError] using hencode
        subst packet
        rfl
  rw [decodeJob, TPKT.decode_encode frame packet hframeMin hframeSize ht]
  change Except.bind (Except.ok frame) (fun decodedFrame => _) = _
  rw [Except.bind]
  rw [COTP.decodeData_encodeData cotp]
  change Except.bind (Except.ok cotp) (fun decodedCotp => _) = _
  rw [Except.bind]
  simp [cotp, S7.decodeJob_encodeJob job s7 hparameters hdata hs7]

/-- Complete-stack encode/decode round trip for every successful ACK_DATA
    response that fits one TPKT frame. -/
theorem decodeResponse_encodeAckData (reference : UInt16)
    (parameters data packet : ByteArray)
    (hparameters : parameters.size ≤ S7.maxSectionSize)
    (hdata : data.size ≤ S7.maxSectionSize)
    (hpacket : TPKT.headerSize + 3 + S7.responseHeaderSize +
      parameters.size + data.size ≤ TPKT.maxFrameSize)
    (hencode : encodeAckData reference parameters data = .ok packet) :
    decodeResponse packet = .ok {
      pduType := S7.ackDataType
      reference
      parameters
      data
      errorClass := 0
      errorCode := 0
    } := by
  let s7 := bytes #[S7.protocolId, S7.ackDataType, 0, 0] ++
    uint16BE reference ++ uint16BE (UInt16.ofNat parameters.size) ++
    uint16BE (UInt16.ofNat data.size) ++ bytes #[0, 0] ++ parameters ++ data
  have hs7 : S7.encodeAckData reference parameters data = .ok s7 := by
    rw [S7.encodeAckData, if_neg (Nat.not_lt.mpr hparameters),
      if_neg (Nat.not_lt.mpr hdata)]
    rfl
  let cotp : COTP.Data := { payload := s7 }
  let frame : TPKT.Frame := { payload := COTP.encodeData cotp }
  have hs7Size : s7.size = S7.responseHeaderSize + parameters.size + data.size :=
    S7.encodedAckData_size reference parameters data s7 hs7
  have hframeSize : TPKT.headerSize + frame.payload.size ≤ TPKT.maxFrameSize := by
    simp [frame, cotp, COTP.encodedData_size, hs7Size] at hpacket ⊢
    omega
  have hframeMin : TPKT.minFrameSize ≤ TPKT.headerSize + frame.payload.size := by
    simp [frame, cotp, COTP.encodedData_size, hs7Size, TPKT.minFrameSize,
      TPKT.headerSize, S7.responseHeaderSize]
    omega
  have ht : TPKT.encode frame = .ok packet := by
    rw [encodeAckData, hs7] at hencode
    change Except.mapError EncodeError.tpkt (TPKT.encode frame) = .ok packet at hencode
    cases htResult : TPKT.encode frame with
    | error error => simp [htResult, Except.mapError] at hencode
    | ok encoded =>
        have heq : encoded = packet := by
          simpa [htResult, Except.mapError] using hencode
        subst packet
        rfl
  rw [decodeResponse, TPKT.decode_encode frame packet hframeMin hframeSize ht]
  change Except.bind (Except.ok frame) (fun decodedFrame => _) = _
  rw [Except.bind, COTP.decodeData_encodeData cotp]
  change Except.bind (Except.ok cotp) (fun decodedCotp => _) = _
  rw [Except.bind]
  simp [cotp, S7.decodeResponse_encodeAckData reference parameters data s7
    hparameters hdata hs7]

/-- The TPKT payload of an accepted complete packet is the three-byte COTP data
    header with EOT set, followed by the S7 PDU. -/
private theorem decode_layers (packet : ByteArray) (frame : TPKT.Frame) (cotp : COTP.Data)
    (hframe : TPKT.decode packet = .ok frame) (hcotp : COTP.decodeData frame.payload = .ok cotp)
    (heot : cotp.endOfTransmission = true) :
    packet.size = 7 + cotp.payload.size ∧
      packet.extract 2 4 = uint16BE (UInt16.ofNat packet.size) ∧
      packet.extract 4 7 = bytes #[2, COTP.dataCode, 0x80] ∧
      packet.extract 11 packet.size = cotp.payload.extract 4 cotp.payload.size ∧
      TPKT.minFrameSize ≤ packet.size ∧ packet.size ≤ TPKT.maxFrameSize := by
  obtain ⟨hpay, hword, hmin, hmax⟩ := TPKT.decode_layout _ _ hframe
  have hcanon := COTP.decodeData_canonical _ _ hcotp
  have hpayload : packet.extract 4 packet.size =
      bytes #[2, COTP.dataCode, 0x80] ++ cotp.payload := by
    rw [← TPKT.headerSize, ← hpay, ← hcanon, COTP.encodeData, heot]
    rfl
  have hhead : (bytes #[2, COTP.dataCode, 0x80]).size = 3 := rfl
  have hpsize : packet.size = 7 + cotp.payload.size := by
    have := congrArg ByteArray.size hpayload
    rw [ByteArray.size_append, hhead, ByteArray.size_extract] at this
    simp only [TPKT.minFrameSize] at hmin
    omega
  refine ⟨hpsize, hword, ?_, ?_, hmin, hmax⟩
  · have := congrArg (fun b => b.extract 0 3) hpayload
    simp only [ByteArray.extract_extract] at this
    rw [ByteArray.extract_append_eq_left hhead.symm, Nat.min_eq_left (by omega)] at this
    exact this
  · have hr : (bytes #[2, COTP.dataCode, 0x80] ++ cotp.payload).extract 7
        (3 + cotp.payload.size) = cotp.payload.extract 4 cotp.payload.size :=
      ByteArray.extract_append_size_add (a := bytes #[2, COTP.dataCode, 0x80])
        (b := cotp.payload) (i := 4) (j := cotp.payload.size)
    have := congrArg (fun b => b.extract 7 (3 + cotp.payload.size)) hpayload
    simp only [ByteArray.extract_extract] at this
    rw [hr] at this
    rw [← this]
    congr 1 <;> omega

/-- Re-framing an S7 PDU whose size matches the accepted packet's reproduces the
    packet's TPKT and COTP headers. -/
private theorem reframe (packet s7 : ByteArray)
    (hsize : packet.size = 7 + s7.size)
    (hword : packet.extract 2 4 = uint16BE (UInt16.ofNat packet.size))
    (hcotpHeader : packet.extract 4 7 = bytes #[2, COTP.dataCode, 0x80])
    (hmin : TPKT.minFrameSize ≤ packet.size) (hmax : packet.size ≤ TPKT.maxFrameSize) :
    TPKT.encode { payload := COTP.encodeData { payload := s7 } } =
      .ok (bytes #[TPKT.version, 0] ++ packet.extract 2 7 ++ s7) := by
  have hlen : TPKT.headerSize + (COTP.encodeData { payload := s7 }).size = packet.size := by
    rw [COTP.encodedData_size]; show 4 + (3 + s7.size) = packet.size; omega
  simp only [TPKT.encode]
  rw [if_pos (by rw [hlen]; exact hmin), if_pos (by rw [hlen]; exact hmax), hlen, ← hword,
    ← ByteArray.extract_append_extract_of_le packet (i := 2) (j := 4) (k := 7) (by omega) (by omega),
    hcotpHeader]
  simp only [COTP.encodeData, ite_true, ByteArray.append_assoc]

/-- Canonical decoding of a complete job packet: re-encoding an accepted packet
    reproduces it with byte 1 (the TPKT reserved byte) and bytes 9–10 (the S7
    reserved word) cleared. Every other byte — TPKT length, COTP header, S7
    protocol and PDU type, reference, lengths and sections — is reproduced exactly. -/
theorem decodeJob_canonical (packet : ByteArray) (job : S7.Job)
    (h : decodeJob packet = .ok job) :
    encodeJob job = .ok (bytes #[TPKT.version, 0] ++ packet.extract 2 7 ++
      bytes #[S7.protocolId, S7.jobType, 0, 0] ++ packet.extract 11 packet.size) := by
  simp only [decodeJob, bind, Except.bind] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xf frame ef xc cotp ec heot
  obtain ⟨hpsize, hword, hcotpHeader, hs7tail, hmin, hmax⟩ :=
    decode_layers packet frame cotp ef ec (by simpa using heot)
  have hs7 := S7.decodeJob_canonical _ _ h
  have hs7size := S7.encodedJob_size _ _ hs7
  have hbytes4 : (bytes #[S7.protocolId, S7.jobType, 0, 0]).size = 4 := rfl
  simp only [S7.jobHeaderSize, ByteArray.size_append, hbytes4, ByteArray.size_extract] at hs7size
  simp only [encodeJob, hs7, Except.mapError, bind, Except.bind]
  rw [reframe packet _ (by rw [ByteArray.size_append, hbytes4, ByteArray.size_extract]; omega)
    hword hcotpHeader hmin hmax, hs7tail, ByteArray.append_assoc]
  simp only [ByteArray.append_assoc]

/-- Canonical decoding of a complete response packet: re-encoding an accepted
    ACK or ACK_DATA packet reproduces it with byte 1 (the TPKT reserved byte) and
    bytes 9–10 (the S7 reserved word) cleared. Every other byte, the error class
    and code included, is reproduced exactly. -/
theorem decodeResponse_canonical (packet : ByteArray) (response : S7.Response)
    (h : decodeResponse packet = .ok response) :
    encodeResponse response = .ok (bytes #[TPKT.version, 0] ++ packet.extract 2 7 ++
      bytes #[S7.protocolId, response.pduType, 0, 0] ++ packet.extract 11 packet.size) := by
  simp only [decodeResponse, bind, Except.bind] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xf frame ef xc cotp ec heot
  obtain ⟨hpsize, hword, hcotpHeader, hs7tail, hmin, hmax⟩ :=
    decode_layers packet frame cotp ef ec (by simpa using heot)
  have hs7 := S7.decodeResponse_canonical _ _ h
  have hs7size := S7.encodedResponse_size _ _ hs7
  have hbytes4 : (bytes #[S7.protocolId, response.pduType, 0, 0]).size = 4 := rfl
  simp only [S7.responseHeaderSize, ByteArray.size_append, hbytes4, ByteArray.size_extract] at hs7size
  simp only [encodeResponse, hs7, Except.mapError, bind, Except.bind]
  rw [reframe packet _ (by rw [ByteArray.size_append, hbytes4, ByteArray.size_extract]; omega)
    hword hcotpHeader hmin hmax, hs7tail, ByteArray.append_assoc]
  simp only [ByteArray.append_assoc]

end LeanS7.Protocol
