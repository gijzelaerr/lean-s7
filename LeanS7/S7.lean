import LeanS7.Binary

namespace LeanS7.S7

def protocolId : UInt8 := 0x32
def jobType : UInt8 := 0x01
def ackType : UInt8 := 0x02
def ackDataType : UInt8 := 0x03
def readFunction : UInt8 := 0x04
def writeFunction : UInt8 := 0x05
def setupCommunicationFunction : UInt8 := 0xf0
def byteWordLength : UInt8 := 0x02
def counterWordLength : UInt8 := 0x1c
def timerWordLength : UInt8 := 0x1d
def byteTransportSize : UInt8 := 0x04
def octetTransportSize : UInt8 := 0x09
def jobHeaderSize : Nat := 10
def responseHeaderSize : Nat := 12
def maxSectionSize : Nat := 65535
def maxItemCount : Nat := 20

inductive EncodeError where
  | parametersTooLarge (size maximum : Nat)
  | dataTooLarge (size maximum : Nat)
  | invalidSize (size : Nat)
  | invalidPayloadSize (actual expected : Nat)
  | invalidDbNumber (dbNumber : UInt16)
  | misalignedAddress (start alignment : Nat)
  | addressTooLarge (start : Nat)
  /-- A counter or timer transfer needs more than one request (`count` elements, at most
      `maximum` per request); see `MultiValidation.singleRequestOnly`. -/
  | counterTimerSpansRequests (count maximum : Nat)
  deriving Repr, BEq

structure Job where
  reference : UInt16
  parameters : ByteArray
  data : ByteArray := ByteArray.empty
  deriving BEq

/-- Encode the common header and sections of an S7 job PDU. -/
def encodeJob (job : Job) : Except EncodeError ByteArray := do
  if job.parameters.size > maxSectionSize then
    throw (.parametersTooLarge job.parameters.size maxSectionSize)
  if job.data.size > maxSectionSize then
    throw (.dataTooLarge job.data.size maxSectionSize)
  let header := bytes #[protocolId, jobType, 0, 0] ++
    uint16BE job.reference ++
    uint16BE (UInt16.ofNat job.parameters.size) ++
    uint16BE (UInt16.ofNat job.data.size)
  return header ++ job.parameters ++ job.data

/-- Decode exactly one S7 job PDU. Trailing, truncated, and length-inconsistent
    inputs are rejected before either section is returned. -/
def decodeJob (pdu : ByteArray) : Except DecodeError Job := do
  let cursor : Cursor := { data := pdu }
  let (actualProtocolId, cursor) ← cursor.readUInt8
  if actualProtocolId != protocolId then
    throw (.invalidField 0 s!"expected S7 protocol ID 0x32, got {actualProtocolId}")
  let (pduType, cursor) ← cursor.readUInt8
  if pduType != jobType then
    throw (.invalidField 1 s!"expected S7 job, got {pduType}")
  let (_, cursor) ← cursor.readUInt16BE
  let (reference, cursor) ← cursor.readUInt16BE
  let (parameterLength, cursor) ← cursor.readUInt16BE
  let (dataLength, cursor) ← cursor.readUInt16BE
  let expected := jobHeaderSize + parameterLength.toNat + dataLength.toNat
  if expected != pdu.size then
    throw (.invalidField 6 s!"S7 section lengths require {expected} bytes, got {pdu.size}")
  let (parameters, cursor) ← cursor.readBytes parameterLength.toNat
  let (data, cursor) ← cursor.readBytes dataLength.toNat
  cursor.finish
  return { reference, parameters, data }

/-- A successfully encoded S7 job has exactly its header and section sizes. -/
theorem encodedJob_size (job : Job) (packet : ByteArray)
    (h : encodeJob job = .ok packet) :
    packet.size = jobHeaderSize + job.parameters.size + job.data.size := by
  by_cases hp : job.parameters.size ≤ maxSectionSize
  · by_cases hd : job.data.size ≤ maxSectionSize
    · rw [encodeJob, if_neg (Nat.not_lt.mpr hp), if_neg (Nat.not_lt.mpr hd)] at h
      injection h with hpacket
      subst packet
      simp [bytes, uint16BE, jobHeaderSize]
      change 4 + 2 + 2 + 2 = 10
      rfl
    · rw [encodeJob, if_neg (Nat.not_lt.mpr hp), if_pos (Nat.lt_of_not_ge hd)] at h
      contradiction
  · rw [encodeJob, if_pos (Nat.lt_of_not_ge hp)] at h
    contradiction

/-- Encoding and then decoding an S7 job returns its reference and sections. -/
theorem decodeJob_encodeJob (job : Job) (packet : ByteArray)
    (hparameters : job.parameters.size ≤ maxSectionSize)
    (hdata : job.data.size ≤ maxSectionSize)
    (hencode : encodeJob job = .ok packet) :
    decodeJob packet = .ok job := by
  rcases job with ⟨reference, parameters, data⟩
  let header := bytes #[protocolId, jobType, 0, 0] ++ uint16BE reference ++
    uint16BE (UInt16.ofNat parameters.size) ++
    uint16BE (UInt16.ofNat data.size)
  let pdu := header ++ parameters ++ data
  have hpacket : packet = pdu := by
    rw [encodeJob, if_neg (Nat.not_lt.mpr hparameters),
      if_neg (Nat.not_lt.mpr hdata)] at hencode
    exact Except.ok.inj hencode.symm
  rw [hpacket]
  have hpLt : parameters.size < 65536 := by
    simpa [maxSectionSize] using Nat.lt_succ_of_le hparameters
  have hdLt : data.size < 65536 := by
    simpa [maxSectionSize] using Nat.lt_succ_of_le hdata
  have hpRound : (UInt16.ofNat parameters.size).toNat = parameters.size := by
    simp [Nat.mod_eq_of_lt hpLt]
  have hdRound : (UInt16.ofNat data.size).toNat = data.size := by
    simp [Nat.mod_eq_of_lt hdLt]
  have hpduSize : pdu.size = jobHeaderSize + parameters.size + data.size := by
    simp [pdu, header, jobHeaderSize]
  have hread0 : Cursor.readUInt8 { data := pdu } =
      .ok (protocolId, { data := pdu, offset := 1 }) := by
    rw [Cursor.readUInt8_of_lt _ (by rw [hpduSize]; simp [jobHeaderSize]; omega)]
    congr 2 <;> simp [pdu, header, bytes]
  have hread1 : Cursor.readUInt8 { data := pdu, offset := 1 } =
      .ok (jobType, { data := pdu, offset := 2 }) := by
    rw [Cursor.readUInt8_of_lt _ (by rw [hpduSize]; simp [jobHeaderSize]; omega)]
    congr 2 <;> simp [pdu, header, bytes]
  have hreserved : Cursor.readUInt16BE { data := pdu, offset := 2 } =
      .ok (0, { data := pdu, offset := 4 }) := by
    have hfixed : bytes #[protocolId, jobType, 0, 0] =
        bytes #[protocolId, jobType] ++ uint16BE 0 := by
      change ByteArray.mk #[protocolId, jobType, 0, 0] =
        ByteArray.mk (#[protocolId, jobType] ++ #[0, 0])
      rfl
    simpa [pdu, header, hfixed, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, jobType])
        (uint16BE reference ++ uint16BE (UInt16.ofNat parameters.size) ++
          uint16BE (UInt16.ofNat data.size) ++ parameters ++ data) 0
  have href : Cursor.readUInt16BE { data := pdu, offset := 4 } =
      .ok (reference, { data := pdu, offset := 6 }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, jobType, 0, 0])
        (uint16BE (UInt16.ofNat parameters.size) ++
          uint16BE (UInt16.ofNat data.size) ++ parameters ++ data)
        reference
  have hpLength : Cursor.readUInt16BE { data := pdu, offset := 6 } =
      .ok (UInt16.ofNat parameters.size, { data := pdu, offset := 8 }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, jobType, 0, 0] ++ uint16BE reference)
        (uint16BE (UInt16.ofNat data.size) ++ parameters ++ data)
        (UInt16.ofNat parameters.size)
  have hdLength : Cursor.readUInt16BE { data := pdu, offset := 8 } =
      .ok (UInt16.ofNat data.size, { data := pdu, offset := 10 }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, jobType, 0, 0] ++ uint16BE reference ++
          uint16BE (UInt16.ofNat parameters.size))
        (parameters ++ data) (UInt16.ofNat data.size)
  have hpRead : Cursor.readBytes { data := pdu, offset := 10 }
      parameters.size = .ok
        (parameters, { data := pdu, offset := 10 + parameters.size }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readBytes_append header parameters data
  have hdRead : Cursor.readBytes
      { data := pdu, offset := 10 + parameters.size } data.size = .ok
        (data, { data := pdu, offset := 10 + parameters.size + data.size }) := by
    have h := Cursor.readBytes_append (header ++ parameters) data ByteArray.empty
    simp only [ByteArray.append_empty] at h
    rw [show header ++ parameters ++ data = pdu by rfl] at h
    have hheaderSize : header.size = 10 := by
      simp [header]
    simpa [hheaderSize] using h
  rw [decodeJob, hread0]
  change Except.bind (Except.ok
      (protocolId, ({ data := pdu, offset := 1 } : Cursor)))
    (fun protocolResult => _) = _
  rw [Except.bind]
  simp
  rw [hread1]
  change Except.bind (Except.ok
      (jobType, ({ data := pdu, offset := 2 } : Cursor)))
    (fun typeResult => _) = _
  rw [Except.bind]
  simp
  rw [hreserved]
  change Except.bind (Except.ok
      (0, ({ data := pdu, offset := 4 } : Cursor)))
    (fun reservedResult => _) = _
  rw [Except.bind]
  rw [href]
  change Except.bind (Except.ok
      (reference, ({ data := pdu, offset := 6 } : Cursor)))
    (fun referenceResult => _) = _
  rw [Except.bind]
  rw [hpLength]
  change Except.bind (Except.ok
      (UInt16.ofNat parameters.size, ({ data := pdu, offset := 8 } : Cursor)))
    (fun parameterLengthResult => _) = _
  rw [Except.bind]
  rw [hdLength]
  change Except.bind (Except.ok
      (UInt16.ofNat data.size, ({ data := pdu, offset := 10 } : Cursor)))
    (fun dataLengthResult => _) = _
  rw [Except.bind]
  simp [hpRound, hdRound, hpduSize, jobHeaderSize]
  rw [hpRead]
  change Except.bind (Except.ok
      (parameters, ({ data := pdu, offset := 10 + parameters.size } : Cursor)))
    (fun parametersResult => _) = _
  rw [Except.bind]
  rw [hdRead]
  change Except.bind (Except.ok
      (data, ({ data := pdu, offset := 10 + parameters.size + data.size } : Cursor)))
    (fun dataResult => _) = _
  rw [Except.bind]
  have hfinish : Cursor.finish
      ({ data := pdu, offset := 10 + parameters.size + data.size } : Cursor) =
      .ok () := by
    rw [Cursor.finish, if_pos (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [hpduSize]
      simp [jobHeaderSize])]
  rw [hfinish]
  rfl

structure SetupCommunication where
  maxAmqCaller : UInt16 := 1
  maxAmqCallee : UInt16 := 1
  pduLength : UInt16 := 480
  deriving Repr, BEq

def SetupCommunication.parameters (setup : SetupCommunication) : ByteArray :=
  bytes #[setupCommunicationFunction, 0] ++
    uint16BE setup.maxAmqCaller ++
    uint16BE setup.maxAmqCallee ++
    uint16BE setup.pduLength

@[simp] theorem SetupCommunication.parameters_size (setup : SetupCommunication) :
    setup.parameters.size = 8 := by
  simp [SetupCommunication.parameters]

def encodeSetupCommunication (reference : UInt16) (setup : SetupCommunication := {}) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters := setup.parameters }

/-- A setup-communication request always encodes and occupies exactly eighteen
    S7 bytes. -/
theorem encodeSetupCommunication_size (reference : UInt16)
    (setup : SetupCommunication) :
    ∃ packet, encodeSetupCommunication reference setup = .ok packet ∧
      packet.size = 18 := by
  let job : Job := { reference, parameters := setup.parameters }
  have hencode : encodeSetupCommunication reference setup = encodeJob job := by
    rfl
  have hsucceeds : ∃ packet, encodeJob job = .ok packet := by
    let packet := bytes #[protocolId, jobType, 0, 0] ++
      uint16BE reference ++ uint16BE 8 ++ uint16BE 0 ++ setup.parameters
    refine ⟨packet, ?_⟩
    rw [encodeJob, if_neg (by simp [job, maxSectionSize]),
      if_neg (by simp [job])]
    rfl
  obtain ⟨packet, hpacket⟩ := hsucceeds
  refine ⟨packet, hencode.trans hpacket, ?_⟩
  have hsize := encodedJob_size job packet hpacket
  simpa [job, jobHeaderSize] using hsize

/-- Decoding an encoded setup request preserves its reference and all three
    negotiation fields in the request parameters. -/
theorem decodeJob_encodeSetupCommunication (reference : UInt16)
    (setup : SetupCommunication) (packet : ByteArray)
    (hencode : encodeSetupCommunication reference setup = .ok packet) :
    decodeJob packet = .ok {
      reference
      parameters := setup.parameters
      data := ByteArray.empty
    } := by
  let job : Job := { reference, parameters := setup.parameters }
  apply decodeJob_encodeJob job packet (by simp [job, maxSectionSize]) (by simp [job])
  exact hencode

structure Response where
  pduType : UInt8
  reference : UInt16
  parameters : ByteArray
  data : ByteArray
  errorClass : UInt8
  errorCode : UInt8
  deriving BEq

/-- Encode a successful S7 ACK_DATA response. This is used when the peer sends
    a server-initiated job, such as a PLC-driven block download. -/
def encodeAckData (reference : UInt16) (parameters data : ByteArray) :
    Except EncodeError ByteArray := do
  if parameters.size > maxSectionSize then
    throw (.parametersTooLarge parameters.size maxSectionSize)
  if data.size > maxSectionSize then
    throw (.dataTooLarge data.size maxSectionSize)
  return bytes #[protocolId, ackDataType, 0, 0] ++ uint16BE reference ++
    uint16BE (UInt16.ofNat parameters.size) ++ uint16BE (UInt16.ofNat data.size) ++
    bytes #[0, 0] ++ parameters ++ data

/-- Encode any S7 ACK or ACK_DATA response, error class and code included. This
    is the canonical form of the responses `decodeResponse` accepts;
    `encodeAckData` is its successful ACK_DATA case
    (`encodeAckData_eq_encodeResponse`). -/
def encodeResponse (response : Response) : Except EncodeError ByteArray := do
  if response.parameters.size > maxSectionSize then
    throw (.parametersTooLarge response.parameters.size maxSectionSize)
  if response.data.size > maxSectionSize then
    throw (.dataTooLarge response.data.size maxSectionSize)
  return bytes #[protocolId, response.pduType, 0, 0] ++ uint16BE response.reference ++
    uint16BE (UInt16.ofNat response.parameters.size) ++
    uint16BE (UInt16.ofNat response.data.size) ++
    bytes #[response.errorClass, response.errorCode] ++ response.parameters ++ response.data

/-- `encodeAckData` encodes the ACK_DATA response with a clear error class and code. -/
theorem encodeAckData_eq_encodeResponse (reference : UInt16) (parameters data : ByteArray) :
    encodeAckData reference parameters data = encodeResponse {
      pduType := ackDataType, reference, parameters, data, errorClass := 0, errorCode := 0 } := by
  rfl

/-- A successful response encoding has exactly the response header and section
    sizes expected by the decoder. -/
theorem encodedResponse_size (response : Response) (packet : ByteArray)
    (h : encodeResponse response = .ok packet) :
    packet.size = responseHeaderSize + response.parameters.size + response.data.size := by
  by_cases hp : response.parameters.size ≤ maxSectionSize
  · by_cases hd : response.data.size ≤ maxSectionSize
    · rw [encodeResponse, if_neg (Nat.not_lt.mpr hp),
        if_neg (Nat.not_lt.mpr hd)] at h
      injection h with hpacket
      subst packet
      simp [responseHeaderSize]
    · rw [encodeResponse, if_neg (Nat.not_lt.mpr hp),
        if_pos (Nat.lt_of_not_ge hd)] at h
      contradiction
  · rw [encodeResponse, if_pos (Nat.lt_of_not_ge hp)] at h
    contradiction

/-- A successful ACK_DATA encoding has exactly the response header and section
    sizes expected by the decoder. -/
theorem encodedAckData_size (reference : UInt16) (parameters data packet : ByteArray)
    (h : encodeAckData reference parameters data = .ok packet) :
    packet.size = responseHeaderSize + parameters.size + data.size := by
  by_cases hp : parameters.size ≤ maxSectionSize
  · by_cases hd : data.size ≤ maxSectionSize
    · rw [encodeAckData, if_neg (Nat.not_lt.mpr hp),
        if_neg (Nat.not_lt.mpr hd)] at h
      injection h with hpacket
      subst packet
      simp [responseHeaderSize]
    · rw [encodeAckData, if_neg (Nat.not_lt.mpr hp),
        if_pos (Nat.lt_of_not_ge hd)] at h
      contradiction
  · rw [encodeAckData, if_pos (Nat.lt_of_not_ge hp)] at h
    contradiction

def decodeResponse (pdu : ByteArray) : Except DecodeError Response := do
  let cursor : Cursor := { data := pdu }
  let (actualProtocolId, cursor) ← cursor.readUInt8
  if actualProtocolId != protocolId then
    throw (.invalidField 0 s!"expected S7 protocol ID 0x32, got {actualProtocolId}")
  let (pduType, cursor) ← cursor.readUInt8
  if pduType != ackType && pduType != ackDataType then
    throw (.invalidField 1 s!"expected S7 ACK or ACK_DATA, got {pduType}")
  let (_, cursor) ← cursor.readUInt16BE
  let (reference, cursor) ← cursor.readUInt16BE
  let (parameterLength, cursor) ← cursor.readUInt16BE
  let (dataLength, cursor) ← cursor.readUInt16BE
  let (errorClass, cursor) ← cursor.readUInt8
  let (errorCode, cursor) ← cursor.readUInt8
  let expected := responseHeaderSize + parameterLength.toNat + dataLength.toNat
  if expected != pdu.size then
    throw (.invalidField 6 s!"S7 section lengths require {expected} bytes, got {pdu.size}")
  let (parameters, cursor) ← cursor.readBytes parameterLength.toNat
  let (data, cursor) ← cursor.readBytes dataLength.toNat
  cursor.finish
  return { pduType, reference, parameters, data, errorClass, errorCode }

/-- Encoding and then decoding a successful ACK_DATA response returns its
    reference and sections with a clear PLC status. -/
theorem decodeResponse_encodeAckData (reference : UInt16)
    (parameters data packet : ByteArray)
    (hparameters : parameters.size ≤ maxSectionSize)
    (hdata : data.size ≤ maxSectionSize)
    (hencode : encodeAckData reference parameters data = .ok packet) :
    decodeResponse packet = .ok {
      pduType := ackDataType
      reference
      parameters
      data
      errorClass := 0
      errorCode := 0
    } := by
  let header := bytes #[protocolId, ackDataType, 0, 0] ++ uint16BE reference ++
    uint16BE (UInt16.ofNat parameters.size) ++
    uint16BE (UInt16.ofNat data.size) ++ bytes #[0, 0]
  let pdu := header ++ parameters ++ data
  have hpacket : packet = pdu := by
    rw [encodeAckData, if_neg (Nat.not_lt.mpr hparameters),
      if_neg (Nat.not_lt.mpr hdata)] at hencode
    exact Except.ok.inj hencode.symm
  rw [hpacket]
  have hpLt : parameters.size < 65536 := by
    simpa [maxSectionSize] using Nat.lt_succ_of_le hparameters
  have hdLt : data.size < 65536 := by
    simpa [maxSectionSize] using Nat.lt_succ_of_le hdata
  have hpRound : (UInt16.ofNat parameters.size).toNat = parameters.size := by
    simp [Nat.mod_eq_of_lt hpLt]
  have hdRound : (UInt16.ofNat data.size).toNat = data.size := by
    simp [Nat.mod_eq_of_lt hdLt]
  have hpduSize : pdu.size = responseHeaderSize + parameters.size + data.size := by
    simp [pdu, header, responseHeaderSize]
  have hread0 : Cursor.readUInt8 { data := pdu } =
      .ok (protocolId, { data := pdu, offset := 1 }) := by
    rw [Cursor.readUInt8_of_lt _ (by rw [hpduSize]; simp [responseHeaderSize]; omega)]
    congr 2 <;> simp [pdu, header, bytes]
  have hread1 : Cursor.readUInt8 { data := pdu, offset := 1 } =
      .ok (ackDataType, { data := pdu, offset := 2 }) := by
    rw [Cursor.readUInt8_of_lt _ (by rw [hpduSize]; simp [responseHeaderSize]; omega)]
    congr 2 <;> simp [pdu, header, bytes]
  have hreserved : Cursor.readUInt16BE { data := pdu, offset := 2 } =
      .ok (0, { data := pdu, offset := 4 }) := by
    have hfixed : bytes #[protocolId, ackDataType, 0, 0] =
        bytes #[protocolId, ackDataType] ++ uint16BE 0 := by
      change ByteArray.mk #[protocolId, ackDataType, 0, 0] =
        ByteArray.mk (#[protocolId, ackDataType] ++ #[0, 0])
      rfl
    simpa [pdu, header, hfixed, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, ackDataType])
        (uint16BE reference ++ uint16BE (UInt16.ofNat parameters.size) ++
          uint16BE (UInt16.ofNat data.size) ++ bytes #[0, 0] ++ parameters ++ data) 0
  have href : Cursor.readUInt16BE { data := pdu, offset := 4 } =
      .ok (reference, { data := pdu, offset := 6 }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, ackDataType, 0, 0])
        (uint16BE (UInt16.ofNat parameters.size) ++
          uint16BE (UInt16.ofNat data.size) ++ bytes #[0, 0] ++ parameters ++ data)
        reference
  have hpLength : Cursor.readUInt16BE { data := pdu, offset := 6 } =
      .ok (UInt16.ofNat parameters.size, { data := pdu, offset := 8 }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, ackDataType, 0, 0] ++ uint16BE reference)
        (uint16BE (UInt16.ofNat data.size) ++ bytes #[0, 0] ++ parameters ++ data)
        (UInt16.ofNat parameters.size)
  have hdLength : Cursor.readUInt16BE { data := pdu, offset := 8 } =
      .ok (UInt16.ofNat data.size, { data := pdu, offset := 10 }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, ackDataType, 0, 0] ++ uint16BE reference ++
          uint16BE (UInt16.ofNat parameters.size))
        (bytes #[0, 0] ++ parameters ++ data) (UInt16.ofNat data.size)
  have herrorClass : Cursor.readUInt8 { data := pdu, offset := 10 } =
      .ok (0, { data := pdu, offset := 11 }) := by
    rw [Cursor.readUInt8_of_lt _ (by rw [hpduSize]; simp [responseHeaderSize]; omega)]
    congr 2 <;> simp [pdu, header, bytes, ByteArray.append_assoc]
  have herrorCode : Cursor.readUInt8 { data := pdu, offset := 11 } =
      .ok (0, { data := pdu, offset := 12 }) := by
    rw [Cursor.readUInt8_of_lt _ (by rw [hpduSize]; simp [responseHeaderSize]; omega)]
    congr 2 <;> simp [pdu, header, bytes, ByteArray.append_assoc]
  have hpRead : Cursor.readBytes { data := pdu, offset := 12 }
      parameters.size = .ok
        (parameters, { data := pdu, offset := 12 + parameters.size }) := by
    simpa [pdu, header, ByteArray.append_assoc] using
      Cursor.readBytes_append header parameters data
  have hdRead : Cursor.readBytes
      { data := pdu, offset := 12 + parameters.size } data.size = .ok
        (data, { data := pdu, offset := 12 + parameters.size + data.size }) := by
    have h := Cursor.readBytes_append (header ++ parameters) data ByteArray.empty
    simp only [ByteArray.append_empty] at h
    rw [show header ++ parameters ++ data = pdu by rfl] at h
    have hheaderSize : header.size = 12 := by simp [header]
    simpa [hheaderSize] using h
  rw [decodeResponse, hread0]
  change Except.bind (Except.ok
      (protocolId, ({ data := pdu, offset := 1 } : Cursor)))
    (fun protocolResult => _) = _
  rw [Except.bind]
  simp
  rw [hread1]
  change Except.bind (Except.ok
      (ackDataType, ({ data := pdu, offset := 2 } : Cursor)))
    (fun typeResult => _) = _
  rw [Except.bind]
  simp
  rw [hreserved]
  change Except.bind (Except.ok
      (0, ({ data := pdu, offset := 4 } : Cursor)))
    (fun reservedResult => _) = _
  rw [Except.bind, href]
  change Except.bind (Except.ok
      (reference, ({ data := pdu, offset := 6 } : Cursor)))
    (fun referenceResult => _) = _
  rw [Except.bind, hpLength]
  change Except.bind (Except.ok
      (UInt16.ofNat parameters.size, ({ data := pdu, offset := 8 } : Cursor)))
    (fun parameterLengthResult => _) = _
  rw [Except.bind, hdLength]
  change Except.bind (Except.ok
      (UInt16.ofNat data.size, ({ data := pdu, offset := 10 } : Cursor)))
    (fun dataLengthResult => _) = _
  rw [Except.bind, herrorClass]
  change Except.bind (Except.ok
      (0, ({ data := pdu, offset := 11 } : Cursor)))
    (fun errorClassResult => _) = _
  rw [Except.bind, herrorCode]
  change Except.bind (Except.ok
      (0, ({ data := pdu, offset := 12 } : Cursor)))
    (fun errorCodeResult => _) = _
  rw [Except.bind]
  simp [hpRound, hdRound, hpduSize, responseHeaderSize]
  rw [hpRead]
  change Except.bind (Except.ok
      (parameters, ({ data := pdu, offset := 12 + parameters.size } : Cursor)))
    (fun parametersResult => _) = _
  rw [Except.bind, hdRead]
  change Except.bind (Except.ok
      (data, ({ data := pdu, offset := 12 + parameters.size + data.size } : Cursor)))
    (fun dataResult => _) = _
  rw [Except.bind]
  have hfinish : Cursor.finish
      ({ data := pdu, offset := 12 + parameters.size + data.size } : Cursor) =
      .ok () := by
    rw [Cursor.finish, if_pos (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [hpduSize]
      simp [responseHeaderSize])]
  rw [hfinish]
  rfl

/-- Canonical decoding: re-encoding an accepted job reproduces the input with its
    reserved word (offsets 2–3) cleared. That word is the only input `decodeJob`
    ignores; the reference, both length fields and both sections are reproduced
    exactly. -/
theorem decodeJob_canonical (pdu : ByteArray) (job : Job) (h : decodeJob pdu = .ok job) :
    encodeJob job = .ok (bytes #[protocolId, jobType, 0, 0] ++ pdu.extract 4 pdu.size) := by
  simp only [decodeJob, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xa va ea hproto xb vb eb htype xc vc ec xd vd ed xe ve ee xf vf ef hlen xg vg eg xk vk ek xm vm em
  obtain ⟨la, da, na⟩ := Cursor.readUInt8_value _ _ _ ea
  rw [na] at eb
  obtain ⟨lb, db, nb⟩ := Cursor.readUInt8_value _ _ _ eb
  rw [nb] at ec
  obtain ⟨lc, dc, nc⟩ := Cursor.readUInt16BE_value _ _ _ ec
  rw [nc] at ed
  obtain ⟨ld, dd, nd⟩ := Cursor.readUInt16BE_value _ _ _ ed
  rw [nd] at ee
  obtain ⟨le, de, ne⟩ := Cursor.readUInt16BE_value _ _ _ ee
  rw [ne] at ef
  obtain ⟨lf, df, nf⟩ := Cursor.readUInt16BE_value _ _ _ ef
  rw [nf] at eg
  obtain ⟨pg, ng⟩ := Cursor.readBytes_value _ _ _ _ eg
  rw [ng] at ek
  obtain ⟨pk, nk⟩ := Cursor.readBytes_value _ _ _ _ ek
  rw [nk] at em
  have hfin := Cursor.finish_ok _ em
  injection h with h
  subst h
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
  simp only [jobHeaderSize] at hlen
  simp only at la lb lc ld le lf dd de df hfin pg pk
  have hP := ve.fst.toNat_lt
  have hD := vf.fst.toNat_lt
  have hgsize : vg.fst.size = ve.fst.toNat := by
    rw [pg, ByteArray.size_extract]; omega
  have hksize : vk.fst.size = vf.fst.toNat := by
    rw [pk, ByteArray.size_extract]; omega
  have href : uint16BE vd.fst = pdu.extract 4 6 := by
    rw [dd, ← ByteArray.extract_two_uint16BE pdu 4 (by omega)]
  have hplen : uint16BE (UInt16.ofNat vg.fst.size) = pdu.extract 6 8 := by
    rw [hgsize, UInt16.ofNat_toNat, de, ← ByteArray.extract_two_uint16BE pdu 6 (by omega)]
  have hdlen : uint16BE (UInt16.ofNat vk.fst.size) = pdu.extract 8 10 := by
    rw [hksize, UInt16.ofNat_toNat, df, ← ByteArray.extract_two_uint16BE pdu 8 (by omega)]
  simp only [encodeJob]
  rw [if_neg (by rw [hgsize, maxSectionSize]; omega), if_neg (by rw [hksize, maxSectionSize]; omega)]
  simp only [pure, Except.pure]
  rw [href, hplen, hdlen, pg, pk]
  simp only [ByteArray.append_assoc]
  rw [ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    show 0 + 1 + 1 + 2 + 2 + 2 + 2 + ve.fst.toNat + vf.fst.toNat = pdu.size by omega]

/-- Canonical decoding: re-encoding an accepted ACK or ACK_DATA response
    reproduces the input with its reserved word (offsets 2–3) cleared. That word
    is the only input `decodeResponse` ignores; the PDU type, reference, length
    fields, error class and code, and both sections are reproduced exactly. -/
theorem decodeResponse_canonical (pdu : ByteArray) (response : Response)
    (h : decodeResponse pdu = .ok response) :
    encodeResponse response =
      .ok (bytes #[protocolId, response.pduType, 0, 0] ++ pdu.extract 4 pdu.size) := by
  simp only [decodeResponse, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xa va ea hproto xb vb eb htype xc vc ec xd vd ed xe ve ee xf vf ef xg vg eg xh vh eh hlen xi vi ei xk vk ek xm vm em
  obtain ⟨la, da, na⟩ := Cursor.readUInt8_value _ _ _ ea
  rw [na] at eb
  obtain ⟨lb, db, nb⟩ := Cursor.readUInt8_value _ _ _ eb
  rw [nb] at ec
  obtain ⟨lc, dc, nc⟩ := Cursor.readUInt16BE_value _ _ _ ec
  rw [nc] at ed
  obtain ⟨ld, dd, nd⟩ := Cursor.readUInt16BE_value _ _ _ ed
  rw [nd] at ee
  obtain ⟨le, de, ne⟩ := Cursor.readUInt16BE_value _ _ _ ee
  rw [ne] at ef
  obtain ⟨lf, df, nf⟩ := Cursor.readUInt16BE_value _ _ _ ef
  rw [nf] at eg
  obtain ⟨lg, dg, ng⟩ := Cursor.readUInt8_value _ _ _ eg
  rw [ng] at eh
  obtain ⟨lh, dh, nh⟩ := Cursor.readUInt8_value _ _ _ eh
  rw [nh] at ei
  obtain ⟨pi, ni⟩ := Cursor.readBytes_value _ _ _ _ ei
  rw [ni] at ek
  obtain ⟨pk, nk⟩ := Cursor.readBytes_value _ _ _ _ ek
  rw [nk] at em
  have hfin := Cursor.finish_ok _ em
  injection h with h
  subst h
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
  simp only [responseHeaderSize] at hlen
  simp only at la lb lc ld le lf lg lh dd de df dg dh hfin pi pk ⊢
  have hP := ve.fst.toNat_lt
  have hD := vf.fst.toNat_lt
  have hisize : vi.fst.size = ve.fst.toNat := by
    rw [pi, ByteArray.size_extract]; omega
  have hksize : vk.fst.size = vf.fst.toNat := by
    rw [pk, ByteArray.size_extract]; omega
  have href : uint16BE vd.fst = pdu.extract 4 6 := by
    rw [dd, ← ByteArray.extract_two_uint16BE pdu 4 (by omega)]
  have hplen : uint16BE (UInt16.ofNat vi.fst.size) = pdu.extract 6 8 := by
    rw [hisize, UInt16.ofNat_toNat, de, ← ByteArray.extract_two_uint16BE pdu 6 (by omega)]
  have hdlen : uint16BE (UInt16.ofNat vk.fst.size) = pdu.extract 8 10 := by
    rw [hksize, UInt16.ofNat_toNat, df, ← ByteArray.extract_two_uint16BE pdu 8 (by omega)]
  have herror : bytes #[vg.fst, vh.fst] = pdu.extract 10 12 := by
    rw [← dg, ← dh, ByteArray.extract_two pdu 10 (by omega)]
    rfl
  simp only [encodeResponse]
  rw [if_neg (by rw [hisize, maxSectionSize]; omega), if_neg (by rw [hksize, maxSectionSize]; omega)]
  simp only [pure, Except.pure]
  rw [href, hplen, hdlen, herror, pi, pk]
  simp only [ByteArray.append_assoc]
  rw [ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    ByteArray.extract_append_extract_of_le pdu (by omega) (by omega),
    show 0 + 1 + 1 + 2 + 2 + 2 + 2 + 1 + 1 + ve.fst.toNat + vf.fst.toNat = pdu.size by omega]

def validateResponse (response : Response) (reference : UInt16) (function : UInt8) : Except DecodeError Unit := do
  if response.reference != reference then
    throw (.invalidField 4 s!"expected PDU reference {reference}, got {response.reference}")
  if response.errorClass != 0 || response.errorCode != 0 then
    throw (.remoteFailure 10 s!"PLC error {response.errorClass}:{response.errorCode}")
  let (actualFunction, _) ← ({ data := response.parameters } : Cursor).readUInt8
  if actualFunction != function then
    throw (.invalidField responseHeaderSize "unexpected S7 response function")

/-- A response with the wrong PDU reference is rejected before its PLC status
    or function parameters can be accepted. -/
theorem validateResponse_rejects_reference (response : Response)
    (reference : UInt16) (function : UInt8)
    (hreference : response.reference ≠ reference) :
    validateResponse response reference function = .error
      (.invalidField 4 s!"expected PDU reference {reference}, got {response.reference}") := by
  rw [validateResponse, if_pos (by simpa using hreference)]
  rfl

/-- Successful response validation proves request/response correlation. -/
theorem validateResponse_reference_eq (response : Response)
    (reference : UInt16) (function : UInt8)
    (hvalidate : validateResponse response reference function = .ok ()) :
    response.reference = reference := by
  by_cases hreference : response.reference = reference
  · exact hreference
  · rw [validateResponse_rejects_reference response reference function hreference]
      at hvalidate
    contradiction

/-- Successful response validation proves that the PLC-level error status is
    clear before any service-specific decoder exposes payload data. -/
theorem validateResponse_error_free (response : Response)
    (reference : UInt16) (function : UInt8)
    (hvalidate : validateResponse response reference function = .ok ()) :
    response.errorClass = 0 ∧ response.errorCode = 0 := by
  have hreference := validateResponse_reference_eq response reference function hvalidate
  constructor
  · by_cases hclass : response.errorClass = 0
    · exact hclass
    · rw [validateResponse, if_neg (by simp [hreference]),
        if_pos (by simp [hclass])] at hvalidate
      contradiction
  · by_cases hcode : response.errorCode = 0
    · exact hcode
    · by_cases hclass : response.errorClass = 0
      · rw [validateResponse, if_neg (by simp [hreference]),
          if_pos (by simp [hclass, hcode])] at hvalidate
        contradiction
      · rw [validateResponse, if_neg (by simp [hreference]),
          if_pos (by simp [hclass])] at hvalidate
        contradiction

/-- Successful response validation proves that the first parameter byte is the
    expected service discriminator. -/
theorem validateResponse_function_eq (response : Response)
    (reference : UInt16) (function : UInt8)
    (hvalidate : validateResponse response reference function = .ok ()) :
    ∃ cursor, Cursor.readUInt8 { data := response.parameters } =
      .ok (function, cursor) := by
  have hreference := validateResponse_reference_eq response reference function hvalidate
  have herrors := validateResponse_error_free response reference function hvalidate
  rw [validateResponse, if_neg (by simp [hreference]),
    if_neg (by simp [herrors.1, herrors.2])] at hvalidate
  cases hread : Cursor.readUInt8 { data := response.parameters } with
  | error error =>
      rw [hread] at hvalidate
      contradiction
  | ok result =>
      rcases result with ⟨actualFunction, cursor⟩
      rw [hread] at hvalidate
      by_cases hfunction : actualFunction = function
      · subst actualFunction
        exact ⟨cursor, rfl⟩
      · change (if actualFunction != function then
          Except.error (DecodeError.invalidField responseHeaderSize
            "unexpected S7 response function") else .ok ()) = .ok () at hvalidate
        rw [if_pos (by simpa using hfunction)] at hvalidate
        contradiction

/-- A validated response answers the request's reference with a clear error class
    and code, and its parameter section starts with the expected function code. -/
theorem validateResponse_exact (response : Response) (reference : UInt16) (function : UInt8)
    (h : validateResponse response reference function = .ok ()) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      ∃ hp : 0 < response.parameters.size, response.parameters[0] = function := by
  obtain ⟨herrorClass, herrorCode⟩ := validateResponse_error_free _ _ _ h
  obtain ⟨cursor, hread⟩ := validateResponse_function_eq _ _ _ h
  obtain ⟨hlt, hbyte, _⟩ := Cursor.readUInt8_value _ _ _ hread
  exact ⟨validateResponse_reference_eq _ _ _ h, herrorClass, herrorCode, hlt, hbyte⟩

/-- Check the protocol minimum needed by all supported S7 request and response
    headers before installing a negotiated PDU budget. -/
def validateSetupPduLength (pduLength : UInt16) : Except DecodeError Unit := do
  if pduLength < 240 then
    throw (.invalidField (responseHeaderSize + 6)
      s!"negotiated PDU length is too small: {pduLength}")

/-- Every accepted setup PDU length is at least the protocol minimum used by
    the client batching and chunking layers. -/
theorem validateSetupPduLength_lower_bound (pduLength : UInt16)
    (hvalidate : validateSetupPduLength pduLength = .ok ()) :
    240 ≤ pduLength.toNat := by
  by_cases hsmall : pduLength < 240
  · rw [validateSetupPduLength, if_pos hsmall] at hvalidate
    contradiction
  · have hnotlt : ¬pduLength.toNat < 240 := by
      simpa [UInt16.lt_iff_toNat_lt] using hsmall
    omega

def decodeSetupCommunication (reference : UInt16) (response : Response) : Except DecodeError SetupCommunication := do
  validateResponse response reference setupCommunicationFunction
  if response.parameters.size != 8 then
    throw (.invalidField responseHeaderSize "setup-communication parameters must be eight bytes")
  let cursor : Cursor := { data := response.parameters, offset := 2 }
  let (maxAmqCaller, cursor) ← cursor.readUInt16BE
  let (maxAmqCallee, cursor) ← cursor.readUInt16BE
  let (pduLength, cursor) ← cursor.readUInt16BE
  cursor.finish
  validateSetupPduLength pduLength
  return { maxAmqCaller, maxAmqCallee, pduLength }

inductive Area where
  | processInputs
  | processOutputs
  | markers
  | dataBlocks
  | counters
  | timers
  deriving Repr, BEq, DecidableEq

def Area.code : Area → UInt8
  | .processInputs => 0x81
  | .processOutputs => 0x82
  | .markers => 0x83
  | .dataBlocks => 0x84
  | .counters => 0x1c
  | .timers => 0x1d

def Area.wordLength : Area → UInt8
  | .counters => counterWordLength
  | .timers => timerWordLength
  | _ => byteWordLength

def Area.elementSize : Area → Nat
  | .counters | .timers => 2
  | _ => 1

def Area.usesElementAddress : Area → Bool
  | .counters | .timers => true
  | _ => false

def Area.dataTransportSize : Area → UInt8
  | .counters | .timers => octetTransportSize
  | _ => byteTransportSize

/-- The length field of a read item: bytes for the octet transport size, bits otherwise. -/
def readItemLength (transportSize : UInt8) (size : Nat) : Nat :=
  if transportSize == octetTransportSize then size else size * 8

/-- A memory-area range. `start` is a byte offset; timers and counters require
    two-byte alignment, while `count` is the number of timer/counter elements. -/
structure MemoryRange where
  area : Area
  dbNumber : UInt16
  start : Nat
  count : Nat
  deriving Repr, BEq

inductive ReadItemResult where
  | success (payload : ByteArray)
  | failure (returnCode : UInt8)
  deriving BEq

structure WriteItem where
  range : MemoryRange
  payload : ByteArray
  deriving BEq

inductive WriteItemResult where
  | success
  | failure (returnCode : UInt8)
  deriving Repr, BEq

def MemoryRange.wireAddress (range : MemoryRange) : Nat :=
  if range.area.usesElementAddress then range.start else range.start * 8

def MemoryRange.lastWireAddress (range : MemoryRange) : Nat :=
  if range.area.usesElementAddress then
    range.start + (range.count - 1) * range.area.elementSize
  else
    (range.start + range.count * range.area.elementSize - 1) * 8

/-- Validate every range condition needed before truncating counts and addresses
    to their fixed-width S7 wire fields. -/
def validateMemoryRange (range : MemoryRange) : Except EncodeError Unit := do
  if range.count = 0 ∨ range.count > maxSectionSize then
    throw (.invalidSize range.count)
  if range.area ≠ .dataBlocks ∧ range.dbNumber ≠ 0 then
    throw (.invalidDbNumber range.dbNumber)
  if range.area.usesElementAddress ∧ range.start % range.area.elementSize ≠ 0 then
    throw (.misalignedAddress range.start range.area.elementSize)
  if range.wireAddress > 0xffffff ∨ range.lastWireAddress > 0xffffff then
    throw (.addressTooLarge range.start)

/-- Successful range validation proves that no count or address information is
    truncated by the S7 memory-address wire representation. -/
theorem validateMemoryRange_invariants (range : MemoryRange)
    (hvalidate : validateMemoryRange range = .ok ()) :
    range.count ≠ 0 ∧
      range.count ≤ maxSectionSize ∧
      (range.area ≠ .dataBlocks → range.dbNumber = 0) ∧
      (range.area.usesElementAddress →
        range.start % range.area.elementSize = 0) ∧
      range.wireAddress ≤ 0xffffff ∧
      range.lastWireAddress ≤ 0xffffff := by
  simp only [validateMemoryRange] at hvalidate
  split at hvalidate <;> rename_i hsize
  · contradiction
  split at hvalidate <;> rename_i hdb
  · contradiction
  split at hvalidate <;> rename_i halignment
  · contradiction
  split at hvalidate <;> rename_i haddress
  · contradiction
  rcases not_or.mp hsize with ⟨hcount, hcountMax⟩
  rcases not_or.mp haddress with ⟨hwire, hlast⟩
  refine ⟨hcount, Nat.le_of_not_lt hcountMax, ?_, ?_,
    Nat.le_of_not_lt hwire, Nat.le_of_not_lt hlast⟩
  · intro harea
    by_cases hnumber : range.dbNumber = 0
    · exact hnumber
    · exact False.elim (hdb ⟨harea, hnumber⟩)
  · intro helements
    by_cases haligned : range.start % range.area.elementSize = 0
    · exact haligned
    · exact False.elim (halignment ⟨helements, haligned⟩)

def encodeMemoryAddress (range : MemoryRange) : Except EncodeError ByteArray := do
  validateMemoryRange range
  let dbNumber := if range.area == .dataBlocks then range.dbNumber else 0
  return bytes #[0x12, 0x0a, 0x10, range.area.wordLength] ++
    uint16BE (UInt16.ofNat range.count) ++ uint16BE dbNumber ++
    bytes #[range.area.code] ++ uint24BE (UInt32.ofNat range.wireAddress)

/-- Every successfully validated memory item occupies exactly twelve S7
    parameter bytes, matching the batch-budget accounting. -/
theorem encodedMemoryAddress_size (range : MemoryRange) (packet : ByteArray)
    (hencode : encodeMemoryAddress range = .ok packet) :
    packet.size = 12 := by
  rw [encodeMemoryAddress] at hencode
  cases hvalidate : validateMemoryRange range with
  | error error =>
      rw [hvalidate] at hencode
      contradiction
  | ok value =>
      have hvalue : value = () := Subsingleton.elim _ _
      subst value
      rw [hvalidate] at hencode
      injection hencode with hpacket
      rw [← hpacket]
      simp

def encodeAreaRead (reference : UInt16) (range : MemoryRange) : Except EncodeError ByteArray := do
  let address ← encodeMemoryAddress range
  encodeJob { reference, parameters := bytes #[readFunction, 1] ++ address }

/-- Every successful single-area read request occupies exactly 24 S7 bytes. -/
theorem encodedAreaRead_size (reference : UInt16) (range : MemoryRange)
    (packet : ByteArray) (hencode : encodeAreaRead reference range = .ok packet) :
    packet.size = 24 := by
  rw [encodeAreaRead] at hencode
  cases haddress : encodeMemoryAddress range with
  | error error =>
      rw [haddress] at hencode
      contradiction
  | ok address =>
      rw [haddress] at hencode
      have haddressSize := encodedMemoryAddress_size range address haddress
      have hsize := encodedJob_size {
        reference
        parameters := bytes #[readFunction, 1] ++ address
      } packet hencode
      simp [haddressSize, jobHeaderSize] at hsize
      omega

def encodeReadAddresses : List MemoryRange → Except EncodeError ByteArray
  | [] => .ok ByteArray.empty
  | range :: rest => do
      let address ← encodeMemoryAddress range
      let tail ← encodeReadAddresses rest
      return address ++ tail

def encodeAreaReadMany (reference : UInt16) (ranges : Array MemoryRange) : Except EncodeError ByteArray := do
  if ranges.isEmpty || ranges.size > maxItemCount then
    throw (.invalidSize ranges.size)
  let addresses ← encodeReadAddresses ranges.toList
  let parameters := bytes #[readFunction, UInt8.ofNat ranges.size] ++ addresses
  encodeJob { reference, parameters }

def encodeAreaWrite (reference : UInt16) (range : MemoryRange)
    (payload : ByteArray) : Except EncodeError ByteArray := do
  let address ← encodeMemoryAddress range
  let expectedSize := range.count * range.area.elementSize
  if payload.size != expectedSize then
    throw (.invalidPayloadSize payload.size expectedSize)
  let dataLength := if range.area.dataTransportSize == octetTransportSize then
    payload.size
  else
    payload.size * 8
  if dataLength > maxSectionSize then
    throw (.invalidSize payload.size)
  let data := bytes #[0, range.area.dataTransportSize] ++
    uint16BE (UInt16.ofNat dataLength) ++ payload
  encodeJob { reference, parameters := bytes #[writeFunction, 1] ++ address, data }

/-- Every successful single-area write request occupies its fixed 28-byte S7
    overhead plus the payload, matching the client transfer budget. -/
theorem encodedAreaWrite_size (reference : UInt16) (range : MemoryRange)
    (payload packet : ByteArray)
    (hencode : encodeAreaWrite reference range payload = .ok packet) :
    packet.size = 28 + payload.size := by
  rw [encodeAreaWrite] at hencode
  cases haddress : encodeMemoryAddress range with
  | error error =>
      rw [haddress] at hencode
      contradiction
  | ok address =>
      rw [haddress] at hencode
      change Except.bind (Except.ok address) (fun address =>
        if payload.size != range.count * range.area.elementSize then
          throw (.invalidPayloadSize payload.size
            (range.count * range.area.elementSize))
        else
          let dataLength := if range.area.dataTransportSize == octetTransportSize then
            payload.size
          else
            payload.size * 8
          if dataLength > maxSectionSize then
            throw (.invalidSize payload.size)
          else
            let data := bytes #[0, range.area.dataTransportSize] ++
              uint16BE (UInt16.ofNat dataLength) ++ payload
            encodeJob {
              reference
              parameters := bytes #[writeFunction, 1] ++ address
              data
            }) = .ok packet at hencode
      rw [Except.bind] at hencode
      split at hencode
      · contradiction
      split at hencode
      all_goals
        dsimp only at hencode
        split at hencode
        · contradiction
        · have haddressSize := encodedMemoryAddress_size range address haddress
          have hsize := encodedJob_size _ packet hencode
          simp [haddressSize, jobHeaderSize] at hsize
          omega

def encodeWriteSections : List WriteItem → Except EncodeError (ByteArray × ByteArray)
  | [] => .ok (ByteArray.empty, ByteArray.empty)
  | item :: rest => do
    let address ← encodeMemoryAddress item.range
    let expectedSize := item.range.count * item.range.area.elementSize
    if item.payload.size != expectedSize then
      throw (.invalidPayloadSize item.payload.size expectedSize)
    let dataLength := if item.range.area.dataTransportSize == octetTransportSize then
      item.payload.size
    else
      item.payload.size * 8
    if dataLength > maxSectionSize then
      throw (.invalidSize item.payload.size)
    let itemData := bytes #[0, item.range.area.dataTransportSize] ++
      uint16BE (UInt16.ofNat dataLength) ++ item.payload
    let padding := if !rest.isEmpty && item.payload.size % 2 != 0 then bytes #[0]
      else ByteArray.empty
    let (parameters, data) ← encodeWriteSections rest
    return (address ++ parameters, itemData ++ padding ++ data)

def encodeAreaWriteMany (reference : UInt16) (items : Array WriteItem) : Except EncodeError ByteArray := do
  if items.isEmpty || items.size > maxItemCount then
    throw (.invalidSize items.size)
  let (addresses, data) ← encodeWriteSections items.toList
  let parameters := bytes #[writeFunction, UInt8.ofNat items.size] ++ addresses
  encodeJob { reference, parameters, data }

structure DbRange where
  dbNumber : UInt16
  start : Nat
  size : Nat
  deriving Repr, BEq

def encodeDbRead (reference : UInt16) (range : DbRange) : Except EncodeError ByteArray := do
  encodeAreaRead reference {
    area := .dataBlocks
    dbNumber := range.dbNumber
    start := range.start
    count := range.size
  }

def encodeDbWrite (reference : UInt16) (dbNumber : UInt16) (start : Nat)
    (payload : ByteArray) : Except EncodeError ByteArray := do
  encodeAreaWrite reference {
    area := .dataBlocks
    dbNumber
    start
    count := payload.size
  } payload

def decodeAreaRead (reference : UInt16) (area : Area) (expectedSize : Nat)
    (response : Response) : Except DecodeError ByteArray := do
  validateResponse response reference readFunction
  if response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "expected one read response item")
  let parameterCursor : Cursor := { data := response.parameters, offset := 1 }
  let (itemCount, parameterCursor) ← parameterCursor.readUInt8
  parameterCursor.finish
  if itemCount != 1 then
    throw (.invalidField (responseHeaderSize + 1) "expected one read response item")
  if response.data.size < 4 then
    throw (.unexpectedEnd (responseHeaderSize + 2) 4 response.data.size)
  let cursor : Cursor := { data := response.data }
  let (returnCode, cursor) ← cursor.readUInt8
  if returnCode != 0xff then
    throw (.remoteFailure (responseHeaderSize + 2) s!"read item failed with code {returnCode}")
  let (transportSize, cursor) ← cursor.readUInt8
  let compatibleByteEncoding := area.usesElementAddress && transportSize == byteTransportSize
  if transportSize != area.dataTransportSize && !compatibleByteEncoding then
    throw (.invalidField (responseHeaderSize + 3) s!"unexpected read transport size {transportSize}")
  let (encodedLength, cursor) ← cursor.readUInt16BE
  let payloadSize ← if transportSize == octetTransportSize then
    pure encodedLength.toNat
  else if encodedLength.toNat % 8 != 0 then
    throw (.invalidField (responseHeaderSize + 4) "read response bit length is not byte aligned")
  else
    pure (encodedLength.toNat / 8)
  if payloadSize != expectedSize then
    throw (.invalidField (responseHeaderSize + 4)
      s!"expected {expectedSize} response bytes, got {payloadSize}")
  let (payload, cursor) ← cursor.readBytes payloadSize
  cursor.finish
  return payload

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Successful single-area reads expose exactly the caller's requested byte count. -/
theorem decodeAreaRead_size (reference : UInt16) (area : Area) (expectedSize : Nat)
    (response : Response) (payload : ByteArray)
    (h : decodeAreaRead reference area expectedSize response = .ok payload) :
    payload.size = expectedSize := by
  unfold decodeAreaRead at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  all_goals
    simp only [Except.ok.injEq] at h
    subst payload
    have hsize := Cursor.readBytes_size _ _ _ _ (by assumption)
    simp_all

private def validateItemParameters (response : Response) (reference : UInt16)
    (function : UInt8) (expectedCount : Nat) : Except DecodeError Unit := do
  validateResponse response reference function
  if response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "expected two-byte item response parameters")
  let cursor : Cursor := { data := response.parameters, offset := 1 }
  let (actualCount, cursor) ← cursor.readUInt8
  cursor.finish
  if actualCount.toNat != expectedCount then
    throw (.invalidField (responseHeaderSize + 1)
      s!"expected {expectedCount} response items, got {actualCount}")

private def responsePayloadSize (transportSize : UInt8) (encodedLength : UInt16)
    (offset : Nat) : Except DecodeError Nat := do
  if transportSize == octetTransportSize then
    return encodedLength.toNat
  if encodedLength.toNat % 8 != 0 then
    throw (.invalidField offset "response bit length is not byte aligned")
  return encodedLength.toNat / 8

private def decodeReadItems : List MemoryRange → Cursor → Except DecodeError (List ReadItemResult × Cursor)
  | [], cursor => pure ([], cursor)
  | range :: rest, cursor => do
      let itemOffset := responseHeaderSize + 2 + cursor.offset
      let (returnCode, cursor) ← cursor.readUInt8
      let (transportSize, cursor) ← cursor.readUInt8
      let (encodedLength, cursor) ← cursor.readUInt16BE
      let payloadSize ← responsePayloadSize transportSize encodedLength (itemOffset + 2)
      let (payload, cursor) ← cursor.readBytes payloadSize
      let cursor ← if !rest.isEmpty && payloadSize % 2 != 0 then
        let (_, cursor) ← cursor.readUInt8
        pure cursor
      else
        pure cursor
      let result ← if returnCode == 0xff then
        let compatibleByteEncoding := range.area.usesElementAddress && transportSize == byteTransportSize
        if transportSize != range.area.dataTransportSize && !compatibleByteEncoding then
          throw (.invalidField (itemOffset + 1) s!"unexpected read transport size {transportSize}")
        let expectedSize := range.count * range.area.elementSize
        if payloadSize != expectedSize then
          throw (.invalidField (itemOffset + 2)
            s!"expected {expectedSize} response bytes, got {payloadSize}")
        pure (.success payload)
      else
        pure (.failure returnCode)
      let (results, cursor) ← decodeReadItems rest cursor
      return (result :: results, cursor)

/-- An ordered read result either has the exact byte length requested at that
    position, or exposes a non-success PLC return code. -/
def ReadItemMatches (range : MemoryRange) : ReadItemResult → Prop
  | .success payload => payload.size = range.count * range.area.elementSize
  | .failure code => code ≠ 0xff

/-- Positional pairing without dropping or reordering failed response items. -/
inductive ReadItemsMatch : List MemoryRange → List ReadItemResult → Prop
  | nil : ReadItemsMatch [] []
  | cons {range result ranges results} : ReadItemMatches range result →
      ReadItemsMatch ranges results → ReadItemsMatch (range :: ranges) (result :: results)

theorem ReadItemsMatch.length_eq {ranges : List MemoryRange}
    {results : List ReadItemResult} (h : ReadItemsMatch ranges results) :
    ranges.length = results.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

theorem ReadItemsMatch.isEmpty_eq {ranges : List MemoryRange}
    {results : List ReadItemResult} (h : ReadItemsMatch ranges results) :
    ranges.isEmpty = results.isEmpty := by
  cases h <;> rfl

/-- One read item in wire order. All bytes come from sequential bounded reads,
    the exposed status/payload is the one just read, and only an inter-item odd
    payload consumes padding. Padding contents are deliberately unspecified. -/
def ReadItemWireStep (before after : Cursor) (more : Bool)
    (result : ReadItemResult) : Prop :=
  ∃ (code : UInt8) (c₁ : Cursor) (transport : UInt8) (c₂ : Cursor)
      (encodedLength : UInt16) (c₃ : Cursor) (payloadSize : Nat)
      (payload : ByteArray) (c₄ : Cursor),
    before.readUInt8 = .ok (code, c₁) ∧
    c₁.readUInt8 = .ok (transport, c₂) ∧
    c₂.readUInt16BE = .ok (encodedLength, c₃) ∧
    payloadSize = (if transport == octetTransportSize then encodedLength.toNat
      else encodedLength.toNat / 8) ∧
    (transport ≠ octetTransportSize → encodedLength.toNat % 8 = 0) ∧
    c₃.readBytes payloadSize = .ok (payload, c₄) ∧
    (if more && payloadSize % 2 != 0 then
      ∃ padding : UInt8, c₄.readUInt8 = .ok (padding, after)
    else after = c₄) ∧
    result = (if code == 0xff then .success payload else .failure code)

/-- Exact sequential wire correspondence, including failures: no decoded item
    can be reordered, duplicated, omitted, or sourced from a different payload. -/
inductive ReadItemsWireOrder : List ReadItemResult → Cursor → Cursor → Prop
  | nil (cursor : Cursor) : ReadItemsWireOrder [] cursor cursor
  | cons {result results before middle after} :
      ReadItemWireStep before middle (!results.isEmpty) result →
      ReadItemsWireOrder results middle after →
      ReadItemsWireOrder (result :: results) before after

private theorem responsePayloadSize_contract (transport : UInt8) (encodedLength : UInt16)
    (offset size : Nat) (h : responsePayloadSize transport encodedLength offset = .ok size) :
    size = (if transport == octetTransportSize then encodedLength.toNat
      else encodedLength.toNat / 8) ∧
      (transport ≠ octetTransportSize → encodedLength.toNat % 8 = 0) := by
  unfold responsePayloadSize at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  all_goals simp_all

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem decodeReadItems_matches (ranges : List MemoryRange)
    (cursor next : Cursor) (results : List ReadItemResult)
    (h : decodeReadItems ranges cursor = .ok (results, next)) :
    ReadItemsMatch ranges results := by
  induction ranges generalizing cursor next results with
  | nil =>
    simp [decodeReadItems, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩
    exact .nil
  | cons range rest ih =>
    unfold decodeReadItems at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    repeat' (first | contradiction | split at h)
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      apply ReadItemsMatch.cons
      · simp only [ReadItemMatches]
        first
        | have hsize := Cursor.readBytes_size _ _ _ _ (by assumption)
          simp_all
        | simp_all
      · exact ih _ _ _ (by assumption)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem decodeReadItems_wire_order (ranges : List MemoryRange)
    (cursor next : Cursor) (results : List ReadItemResult)
    (h : decodeReadItems ranges cursor = .ok (results, next)) :
    ReadItemsWireOrder results cursor next := by
  induction ranges generalizing cursor next results with
  | nil =>
    simp [decodeReadItems, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩
    exact .nil _
  | cons range rest ih =>
    unfold decodeReadItems at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    repeat' (first | contradiction | split at h)
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      apply ReadItemsWireOrder.cons
      · have hm := decodeReadItems_matches rest _ _ _ (by assumption)
        have hp := responsePayloadSize_contract _ _ _ _ (by assumption)
        refine ⟨_, _, _, _, _, _, _, _, _, by assumption, by assumption,
          by assumption, hp.1, hp.2, by assumption, ?_, ?_⟩
        · have he := hm.isEmpty_eq
          rw [← he]
          split
          all_goals first | contradiction | exact ⟨_, by assumption⟩ | rfl
        · simp_all
      · exact ih _ _ _ (by assumption)

/-- The exact bytes of one item of a multi-item read response. A successful item is
    the success code, its transport size (the area's own, or for counters and timers
    also the byte transport size), its length field and its payload. A failed item
    keeps its return code; its transport size, length word and payload bytes are not
    interpreted. An item that is not the last and has an odd payload is followed by
    one padding byte of any value. -/
def ReadItemBytes (range : MemoryRange) (more : Bool) : ReadItemResult → ByteArray → Prop
  | .success payload, item =>
    ∃ (transport : UInt8) (padding : ByteArray),
      (transport = range.area.dataTransportSize ∨
        (range.area.usesElementAddress = true ∧ transport = byteTransportSize)) ∧
      padding.size = (if more && payload.size % 2 != 0 then 1 else 0) ∧
      item = bytes #[0xff, transport] ++
        uint16BE (UInt16.ofNat (readItemLength transport payload.size)) ++ payload ++ padding
  | .failure code, item =>
    ∃ (transport : UInt8) (encodedLength : UInt16) (ignored padding : ByteArray),
      code ≠ 0xff ∧
      ignored.size = (if transport == octetTransportSize then encodedLength.toNat
        else encodedLength.toNat / 8) ∧
      (transport ≠ octetTransportSize → encodedLength.toNat % 8 = 0) ∧
      padding.size = (if more && ignored.size % 2 != 0 then 1 else 0) ∧
      item = bytes #[code, transport] ++ uint16BE encodedLength ++ ignored ++ padding

/-- The data section of a multi-item read response, item by item in request order. -/
inductive ReadItemsBytes : List MemoryRange → List ReadItemResult → ByteArray → Prop
  | nil : ReadItemsBytes [] [] ByteArray.empty
  | cons {range rest result results item data} :
      ReadItemBytes range (!rest.isEmpty) result item →
      ReadItemsBytes rest results data →
      ReadItemsBytes (range :: rest) (result :: results) (item ++ data)

/-- The bytes a read-item header and payload walk covers, up to any later stop. -/
private theorem readItem_extract (cursor c₁ c₂ c₃ c₄ : Cursor) (code transport : UInt8)
    (encodedLength : UInt16) (count : Nat) (payload : ByteArray) (stop : Nat)
    (e₁ : cursor.readUInt8 = .ok (code, c₁)) (e₂ : c₁.readUInt8 = .ok (transport, c₂))
    (e₃ : c₂.readUInt16BE = .ok (encodedLength, c₃))
    (e₄ : c₃.readBytes count = .ok (payload, c₄))
    (hstop : c₄.offset ≤ stop) :
    c₄.data = cursor.data ∧ c₄.offset = cursor.offset + 4 + count ∧ payload.size = count ∧
      cursor.data.extract cursor.offset stop =
        bytes #[code, transport] ++ uint16BE encodedLength ++ payload ++
          cursor.data.extract c₄.offset stop := by
  obtain ⟨l₁, d₁, n₁⟩ := Cursor.readUInt8_value _ _ _ e₁
  subst n₁
  obtain ⟨l₂, d₂, n₂⟩ := Cursor.readUInt8_value _ _ _ e₂
  subst n₂
  obtain ⟨l₃, d₃, n₃⟩ := Cursor.readUInt16BE_value _ _ _ e₃
  subst n₃
  obtain ⟨p₄, n₄⟩ := Cursor.readBytes_value _ _ _ _ e₄
  have hsize := Cursor.readBytes_size _ _ _ _ e₄
  obtain ⟨_, _, hbound⟩ := Cursor.readBytes_next _ _ _ _ e₄
  subst n₄
  simp only [Cursor.remaining] at hbound
  simp only at l₂ l₃ d₂ d₃ p₄ hstop
  refine ⟨rfl, by simp only <;> omega, hsize, ?_⟩
  simp only
  rw [p₄, d₃, ← d₁, ← d₂, ← ByteArray.extract_two_uint16BE _ _ (by omega),
    show bytes #[cursor.data[cursor.offset], cursor.data[cursor.offset + 1]] =
      cursor.data.extract cursor.offset (cursor.offset + 2) from
        (ByteArray.extract_two _ _ (by omega)).symm,
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-- One decoded read item followed by the rest of the walk is the item's canonical
    bytes followed by the rest's. -/
private theorem readItems_step (range : MemoryRange) (rest : List MemoryRange)
    (cursor c₁ c₂ c₃ c₄ c₅ next : Cursor) (code transport : UInt8) (encodedLength : UInt16)
    (count : Nat) (payload : ByteArray) (result : ReadItemResult)
    (results : List ReadItemResult)
    (e₁ : cursor.readUInt8 = .ok (code, c₁)) (e₂ : c₁.readUInt8 = .ok (transport, c₂))
    (e₃ : c₂.readUInt16BE = .ok (encodedLength, c₃))
    (e₄ : c₃.readBytes count = .ok (payload, c₄))
    (hcount : count = (if transport == octetTransportSize then encodedLength.toNat
      else encodedLength.toNat / 8))
    (haligned : transport ≠ octetTransportSize → encodedLength.toNat % 8 = 0)
    (hpad : c₅.data = c₄.data ∧
      c₅.offset = c₄.offset + (if !rest.isEmpty && count % 2 != 0 then 1 else 0) ∧
      c₅.offset ≤ c₄.data.size)
    (hresult : (code = 0xff ∧ (transport = range.area.dataTransportSize ∨
        (range.area.usesElementAddress = true ∧ transport = byteTransportSize)) ∧
        result = .success payload) ∨ (code ≠ 0xff ∧ result = .failure code))
    (hrest : next.data = c₅.data ∧ c₅.offset ≤ next.offset ∧
      ReadItemsBytes rest results (c₅.data.extract c₅.offset next.offset)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧
      ReadItemsBytes (range :: rest) (result :: results)
        (cursor.data.extract cursor.offset next.offset) := by
  obtain ⟨hpd, hpo, hpb⟩ := hpad
  obtain ⟨hnd, hle, hbytes⟩ := hrest
  obtain ⟨hd₄, ho₄, hsize, hextract⟩ :=
    readItem_extract cursor c₁ c₂ c₃ c₄ code transport encodedLength count payload
      next.offset e₁ e₂ e₃ e₄ (by split at hpo <;> omega)
  rw [hd₄] at hpb
  have hpadSize : (cursor.data.extract c₄.offset c₅.offset).size =
      (if !rest.isEmpty && count % 2 != 0 then 1 else 0) := by
    rw [ByteArray.size_extract, Nat.min_eq_left hpb, hpo]
    split <;> omega
  refine ⟨by rw [hnd, hpd, hd₄], by split at hpo <;> omega, ?_⟩
  rw [hextract, ← ByteArray.extract_append_extract_of_le cursor.data (j := c₅.offset)
    (by split at hpo <;> omega) hle]
  rw [hpd, hd₄] at hbytes
  rw [← ByteArray.append_assoc (a := bytes #[code, transport] ++ uint16BE encodedLength ++ payload)]
  refine .cons ?_ hbytes
  rcases hresult with ⟨rfl, hts, rfl⟩ | ⟨hcode, rfl⟩
  · refine ⟨transport, _, hts, by rw [hpadSize, hsize], ?_⟩
    have hlength : UInt16.ofNat (readItemLength transport payload.size) = encodedLength := by
      rw [hsize, hcount, readItemLength]
      by_cases hoct : transport = octetTransportSize
      · simp [hoct, UInt16.ofNat_toNat]
      · have hne : (transport == octetTransportSize) = false := by simpa using hoct
        rw [hne, if_neg (by simp), if_neg (by simp),
          Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (haligned hoct)), UInt16.ofNat_toNat]
    rw [hlength]
  · exact ⟨transport, encodedLength, payload, _, hcode, by rw [hsize, hcount], haligned,
      by rw [hpadSize, hsize], rfl⟩

private theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The bytes a successful item walk consumed are exactly the canonical item bytes. -/
private theorem decodeReadItems_bytes (ranges : List MemoryRange)
    (cursor next : Cursor) (results : List ReadItemResult)
    (h : decodeReadItems ranges cursor = .ok (results, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧
      ReadItemsBytes ranges results (cursor.data.extract cursor.offset next.offset) := by
  induction ranges generalizing cursor next results with
  | nil =>
    simp [decodeReadItems, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, Nat.le_refl _, ?_⟩
    rw [ByteArray.extract_eq_empty_iff.mpr (by omega)]
    exact .nil
  | cons range rest ih =>
    rw [decodeReadItems] at h
    try dsimp only at h
    obtain ⟨⟨code, c₁⟩, e₁, h⟩ := bind_eq_ok h
    try dsimp only at h
    obtain ⟨⟨transport, c₂⟩, e₂, h⟩ := bind_eq_ok h
    try dsimp only at h
    obtain ⟨⟨encodedLength, c₃⟩, e₃, h⟩ := bind_eq_ok h
    try dsimp only at h
    obtain ⟨count, eN, h⟩ := bind_eq_ok h
    try dsimp only at h
    obtain ⟨⟨payload, c₄⟩, e₄, h⟩ := bind_eq_ok h
    try dsimp only at h
    have hp := responsePayloadSize_contract _ _ _ _ eN
    obtain ⟨hd₃, ho₃, hl₃⟩ := Cursor.readUInt16BE_ok _ _ _ e₃
    obtain ⟨hd₄, ho₄, hl₄⟩ := Cursor.readBytes_next _ _ _ _ e₄
    have hbound : c₄.offset ≤ c₄.data.size := by
      have hs₃ : c₃.data.size = c₂.data.size := by rw [hd₃]
      have hs₄ : c₄.data.size = c₂.data.size := by rw [hd₄, hd₃]
      simp only [Cursor.remaining] at hl₄
      omega
    -- The transport-size check of a successful item, as a disjunction.
    have transport_ok : ¬(transport != range.area.dataTransportSize &&
        !(range.area.usesElementAddress && transport == byteTransportSize)) = true →
        (transport = range.area.dataTransportSize ∨
          (range.area.usesElementAddress = true ∧ transport = byteTransportSize)) := by
      intro hts
      simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Bool.and_eq_false_iff] at hts
      by_cases hc : transport = range.area.dataTransportSize
      · exact .inl hc
      · right; simpa [hc] using hts
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    repeat' (first | contradiction | split at h)
    · -- Padding byte, successful item.
      rename_i hcond xp vp ep hcode hts hsz xr vr er
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hpd, hpo, hpl⟩ := Cursor.readUInt8_ok _ _ _ ep
      exact readItems_step range rest cursor c₁ c₂ c₃ c₄ vp.snd vr.snd code transport
        encodedLength count payload _ vr.fst e₁ e₂ e₃ e₄ hp.1 hp.2
        ⟨hpd, by rw [if_pos hcond, hpo], by omega⟩
        (.inl ⟨by simpa using hcode, transport_ok hts, rfl⟩) (ih _ _ _ er)
    · -- Padding byte, failed item.
      rename_i hcond xp vp ep hcode xr vr er
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hpd, hpo, hpl⟩ := Cursor.readUInt8_ok _ _ _ ep
      exact readItems_step range rest cursor c₁ c₂ c₃ c₄ vp.snd vr.snd code transport
        encodedLength count payload _ vr.fst e₁ e₂ e₃ e₄ hp.1 hp.2
        ⟨hpd, by rw [if_pos hcond, hpo], by omega⟩
        (.inr ⟨by simpa using hcode, rfl⟩) (ih _ _ _ er)
    · -- No padding, successful item.
      rename_i hcond hcode hts hsz xr vr er
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact readItems_step range rest cursor c₁ c₂ c₃ c₄ c₄ vr.snd code transport
        encodedLength count payload _ vr.fst e₁ e₂ e₃ e₄ hp.1 hp.2
        ⟨rfl, by rw [if_neg hcond]; rfl, hbound⟩
        (.inl ⟨by simpa using hcode, transport_ok hts, rfl⟩) (ih _ _ _ er)
    · -- No padding, failed item.
      rename_i hcond hcode xr vr er
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact readItems_step range rest cursor c₁ c₂ c₃ c₄ c₄ vr.snd code transport
        encodedLength count payload _ vr.fst e₁ e₂ e₃ e₄ hp.1 hp.2
        ⟨rfl, by rw [if_neg hcond]; rfl, hbound⟩
        (.inr ⟨by simpa using hcode, rfl⟩) (ih _ _ _ er)

def decodeAreaReadMany (reference : UInt16) (ranges : Array MemoryRange)
    (response : Response) : Except DecodeError (Array ReadItemResult) := do
  if ranges.isEmpty || ranges.size > maxItemCount then
    throw (.invalidField responseHeaderSize s!"invalid expected item count {ranges.size}")
  validateItemParameters response reference readFunction ranges.size
  let (results, cursor) ← decodeReadItems ranges.toList { data := response.data }
  cursor.finish
  return results.toArray

set_option maxRecDepth 4096 in
/-- The actual multi-read decoder keeps every requested position, including PLC
    failures, and checks successful payload lengths against that position's range. -/
theorem decodeAreaReadMany_matches (reference : UInt16) (ranges : Array MemoryRange)
    (response : Response) (results : Array ReadItemResult)
    (h : decodeAreaReadMany reference ranges response = .ok results) :
    ReadItemsMatch ranges.toList results.toList := by
  unfold decodeAreaReadMany at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  simp only [Except.ok.injEq] at h
  subst results
  simpa using decodeReadItems_matches _ _ _ _ (by assumption)

/-- Successful multi-read decoding returns exactly one result per requested item. -/
theorem decodeAreaReadMany_size (reference : UInt16) (ranges : Array MemoryRange)
    (response : Response) (results : Array ReadItemResult)
    (h : decodeAreaReadMany reference ranges response = .ok results) :
    results.size = ranges.size := by
  have hm := decodeAreaReadMany_matches reference ranges response results h
  have hl := ReadItemsMatch.length_eq hm
  simpa using hl.symm

set_option maxRecDepth 4096 in
/-- Every actual multi-read result is backed by the sequential status/payload
    bytes in this response, and the sequence consumes the complete data section. -/
theorem decodeAreaReadMany_wire_order (reference : UInt16) (ranges : Array MemoryRange)
    (response : Response) (results : Array ReadItemResult)
    (h : decodeAreaReadMany reference ranges response = .ok results) :
    ∃ next : Cursor,
      ReadItemsWireOrder results.toList { data := response.data } next ∧
        next.finish = .ok () := by
  unfold decodeAreaReadMany at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  simp only [Except.ok.injEq] at h
  subst results
  have hw := decodeReadItems_wire_order _ _ _ _ (by assumption)
  refine ⟨_, by simpa using hw, ?_⟩
  · have hu : ∀ u : Unit, u = () := by intro u; cases u; rfl
    simpa only [hu] using (show _ = Except.ok _ from by assumption)

private def decodeWriteItems : Nat → Cursor → Except DecodeError (List WriteItemResult × Cursor)
  | 0, cursor => pure ([], cursor)
  | count + 1, cursor => do
      let (returnCode, cursor) ← cursor.readUInt8
      let result := if returnCode == 0xff then WriteItemResult.success else .failure returnCode
      let (results, cursor) ← decodeWriteItems count cursor
      return (result :: results, cursor)

/-- The byte-level mapping used by the actual write acknowledgement decoder. -/
def WriteItemResult.ofReturnCode (code : UInt8) : WriteItemResult :=
  if code == 0xff then .success else .failure code

private theorem multi_byte_read_shape (cursor next : Cursor) (code : UInt8)
    (h : cursor.readUInt8 = .ok (code, next)) :
    ∃ hbound : cursor.offset < cursor.data.size,
      code = cursor.data[cursor.offset] ∧ next.data = cursor.data ∧
        next.offset = cursor.offset + 1 := by
  unfold Cursor.readUInt8 at h
  split at h
  · cases h
    exact ⟨by assumption, rfl, rfl, rfl⟩
  · contradiction

private theorem decodeWriteItems_contract (count : Nat) (cursor next : Cursor)
    (results : List WriteItemResult)
    (h : decodeWriteItems count cursor = .ok (results, next)) :
    results.length = count ∧ next.data = cursor.data ∧
      next.offset = cursor.offset + count ∧
      ∀ i (hi : i < results.length), ∃ hb : cursor.offset + i < cursor.data.size,
        results[i] = WriteItemResult.ofReturnCode cursor.data[cursor.offset + i] := by
  induction count generalizing cursor next results with
  | zero =>
    simp [decodeWriteItems, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, by omega, fun i hi => by simp at hi⟩
  | succ count ih =>
    unfold decodeWriteItems at h
    cases hb : cursor.readUInt8 with
    | error error => simp [hb, bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨code, middle⟩
      cases ht : decodeWriteItems count middle with
      | error error => simp [hb, ht, bind, Except.bind] at h
      | ok pair =>
        rcases pair with ⟨tail, last⟩
        simp only [hb, ht, bind, Except.bind, pure, Except.pure] at h
        cases h
        obtain ⟨hbound, hcode, hdata, hoffset⟩ := multi_byte_read_shape _ _ _ hb
        obtain ⟨hlen, hlastData, hlastOffset, hitems⟩ := ih _ _ _ ht
        refine ⟨by simp [hlen], hlastData.trans hdata, by omega, ?_⟩
        intro i hi
        cases i with
        | zero =>
          refine ⟨by simpa using hbound, ?_⟩
          simp [WriteItemResult.ofReturnCode, hcode]
        | succ i =>
          have hi' : i < tail.length := by simpa using hi
          obtain ⟨hbound', hitem⟩ := hitems i hi'
          have heq : middle.offset + i = cursor.offset + (i + 1) := by omega
          refine ⟨by simpa [hdata, heq] using hbound', ?_⟩
          simpa [hdata, heq] using hitem

def decodeAreaWriteMany (reference : UInt16) (expectedCount : Nat)
    (response : Response) : Except DecodeError (Array WriteItemResult) := do
  if expectedCount == 0 || expectedCount > maxItemCount then
    throw (.invalidField responseHeaderSize s!"invalid expected item count {expectedCount}")
  validateItemParameters response reference writeFunction expectedCount
  let (results, cursor) ← decodeWriteItems expectedCount { data := response.data }
  cursor.finish
  return results.toArray

set_option maxRecDepth 4096 in
/-- Actual multi-write acknowledgements have one byte and one ordered result per
    requested item. Each result is exactly the status at the same wire position. -/
theorem decodeAreaWriteMany_contract (reference : UInt16) (expectedCount : Nat)
    (response : Response) (results : Array WriteItemResult)
    (h : decodeAreaWriteMany reference expectedCount response = .ok results) :
    results.size = expectedCount ∧ response.data.size = expectedCount ∧
      ∀ i (hi : i < results.size), ∃ hb : i < response.data.size,
        results[i] = WriteItemResult.ofReturnCode response.data[i] := by
  unfold decodeAreaWriteMany at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  simp only [Except.ok.injEq] at h
  subst results
  have hc := decodeWriteItems_contract _ _ _ _ (by assumption)
  rcases hc with ⟨hlen, hdata, hoffset, hitems⟩
  have hfinished : ∀ (cursor : Cursor) (u : Unit), cursor.finish = .ok u →
      cursor.offset = cursor.data.size := by
    intro cursor u hf
    unfold Cursor.finish at hf
    split at hf
    · assumption
    · contradiction
  have hend := hfinished _ _ (by assumption)
  refine ⟨by simpa using hlen, by simp_all, ?_⟩
  intro i hi
  obtain ⟨hb, hitem⟩ := hitems i (by simpa using hi)
  exact ⟨by simpa using hb, by simpa using hitem⟩

/-- The wire return code of a write result: the inverse of `WriteItemResult.ofReturnCode`. -/
def WriteItemResult.returnCode : WriteItemResult → UInt8
  | .success => 0xff
  | .failure code => code

theorem WriteItemResult.returnCode_ofReturnCode (code : UInt8) :
    (WriteItemResult.ofReturnCode code).returnCode = code := by
  unfold WriteItemResult.ofReturnCode
  split <;> rename_i h
  · simp only [beq_iff_eq] at h; simp [WriteItemResult.returnCode, h]
  · rfl

/-- A validated item-parameter section is the function code and the item count. -/
private theorem validateItemParameters_exact (response : Response) (reference : UInt16)
    (function : UInt8) (expectedCount : Nat)
    (h : validateItemParameters response reference function expectedCount = .ok ()) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      response.parameters = bytes #[function, UInt8.ofNat expectedCount] := by
  simp only [validateItemParameters, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xv vv ev hpsize xc vc ec xf vf ef hcount
  obtain ⟨href, hclass, hcode, _, hfun⟩ := validateResponse_exact _ _ _ ev
  obtain ⟨_, hcountByte, _⟩ := Cursor.readUInt8_value _ _ _ ec
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hpsize hcount
  refine ⟨href, hclass, hcode, ?_⟩
  conv => lhs; rw [← ByteArray.extract_zero_size (b := response.parameters), hpsize]
  rw [ByteArray.extract_two _ 0 (by omega)]
  simp only at hcountByte
  rw [hfun, hcountByte, ← hcount, UInt8.ofNat_toNat]
  rfl

set_option maxRecDepth 4096 in
/-- Canonical form of a multi-item write acknowledgement: the parameter section is
    the write function and the item count, and the data section is exactly one
    return code per item, in request order. Nothing in an accepted response is
    ignored except the header fields that `decodeResponse` itself ignores. -/
theorem decodeAreaWriteMany_canonical (reference : UInt16) (expectedCount : Nat)
    (response : Response) (results : Array WriteItemResult)
    (h : decodeAreaWriteMany reference expectedCount response = .ok results) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      response.parameters = bytes #[writeFunction, UInt8.ofNat expectedCount] ∧
      response.data = ByteArray.mk (results.map WriteItemResult.returnCode) := by
  obtain ⟨hsize, hdsize, hitems⟩ := decodeAreaWriteMany_contract _ _ _ _ h
  have hparams : validateItemParameters response reference writeFunction expectedCount = .ok () := by
    unfold decodeAreaWriteMany at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    repeat' (first | contradiction | split at h)
    assumption
  obtain ⟨href, hclass, hcode, hp⟩ := validateItemParameters_exact _ _ _ _ hparams
  refine ⟨href, hclass, hcode, hp, ?_⟩
  apply ByteArray.ext
  apply Array.ext
  · simp [hsize, hdsize]
  · intro i hi _
    obtain ⟨hb, hitem⟩ := hitems i (by simp at hi; omega)
    simp only [Array.getElem_map, hitem, WriteItemResult.returnCode_ofReturnCode]
    rfl

set_option maxRecDepth 4096 in
/-- Canonical form of a multi-item read response: the parameter section is the read
    function and the item count, and the data section is exactly the items'
    `ReadItemBytes` in request order. Successful items are fully determined up to the
    transport-size choice for counters and timers; a failed item fixes only its
    return code, and padding bytes after odd payloads may hold any value. -/
theorem decodeAreaReadMany_canonical (reference : UInt16) (ranges : Array MemoryRange)
    (response : Response) (results : Array ReadItemResult)
    (h : decodeAreaReadMany reference ranges response = .ok results) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      response.parameters = bytes #[readFunction, UInt8.ofNat ranges.size] ∧
      ReadItemsBytes ranges.toList results.toList response.data := by
  unfold decodeAreaReadMany at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  rename_i xv vv ev xr vr er xf vf ef
  obtain ⟨href, hclass, hcode, hp⟩ := validateItemParameters_exact _ _ _ _ ev
  obtain ⟨hnd, _, hbytes⟩ := decodeReadItems_bytes _ _ _ _ er
  have hfin := Cursor.finish_ok _ (by cases vf; exact ef)
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨href, hclass, hcode, hp, ?_⟩
  rw [hnd] at hfin
  simp only at hbytes hfin
  rwa [hfin, ByteArray.extract_zero_size] at hbytes

theorem decodeAreaWriteMany_size (reference : UInt16) (expectedCount : Nat)
    (response : Response) (results : Array WriteItemResult)
    (h : decodeAreaWriteMany reference expectedCount response = .ok results) :
    results.size = expectedCount :=
  (decodeAreaWriteMany_contract reference expectedCount response results h).1

def decodeDbRead (reference : UInt16) (response : Response) : Except DecodeError ByteArray := do
  validateResponse response reference readFunction
  if response.data.size < 4 then
    throw (.unexpectedEnd (responseHeaderSize + 2) 4 response.data.size)
  let lengthCursor : Cursor := { data := response.data, offset := 2 }
  let (bitLength, _) ← lengthCursor.readUInt16BE
  if bitLength.toNat % 8 != 0 then
    throw (.invalidField (responseHeaderSize + 4) "read response bit length is not byte aligned")
  decodeAreaRead reference .dataBlocks (bitLength.toNat / 8) response

def decodeDbWrite (reference : UInt16) (response : Response) : Except DecodeError Unit := do
  validateResponse response reference writeFunction
  if response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "expected one write response item")
  let parameterCursor : Cursor := { data := response.parameters, offset := 1 }
  let (itemCount, parameterCursor) ← parameterCursor.readUInt8
  parameterCursor.finish
  if itemCount != 1 then
    throw (.invalidField (responseHeaderSize + 1) "expected one write response item")
  if response.data.size != 1 then
    throw (.invalidField (responseHeaderSize + 2) "write item was not acknowledged")
  let (returnCode, dataCursor) ← ({ data := response.data } : Cursor).readUInt8
  dataCursor.finish
  if returnCode != 0xff then
    throw (.remoteFailure (responseHeaderSize + 2) s!"write item failed with code {returnCode}")

end LeanS7.S7
