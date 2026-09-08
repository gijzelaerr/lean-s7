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

end LeanS7.Protocol
