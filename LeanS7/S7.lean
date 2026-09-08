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
      native_decide
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

def encodeSetupCommunication (reference : UInt16) (setup : SetupCommunication := {}) : Except EncodeError ByteArray :=
  let parameters := bytes #[setupCommunicationFunction, 0] ++
    uint16BE setup.maxAmqCaller ++
    uint16BE setup.maxAmqCallee ++
    uint16BE setup.pduLength
  encodeJob { reference, parameters }

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
      native_decide
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

def validateResponse (response : Response) (reference : UInt16) (function : UInt8) : Except DecodeError Unit := do
  if response.reference != reference then
    throw (.invalidField 4 s!"expected PDU reference {reference}, got {response.reference}")
  if response.errorClass != 0 || response.errorCode != 0 then
    throw (.invalidField 10 s!"PLC error {response.errorClass}:{response.errorCode}")
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

def encodeAreaReadMany (reference : UInt16) (ranges : Array MemoryRange) : Except EncodeError ByteArray := do
  if ranges.isEmpty || ranges.size > maxItemCount then
    throw (.invalidSize ranges.size)
  let mut parameters := bytes #[readFunction, UInt8.ofNat ranges.size]
  for range in ranges do
    parameters := parameters ++ (← encodeMemoryAddress range)
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

def encodeAreaWriteMany (reference : UInt16) (items : Array WriteItem) : Except EncodeError ByteArray := do
  if items.isEmpty || items.size > maxItemCount then
    throw (.invalidSize items.size)
  let mut parameters := bytes #[writeFunction, UInt8.ofNat items.size]
  let mut data := ByteArray.empty
  let mut index := 0
  for item in items do
    let address ← encodeMemoryAddress item.range
    parameters := parameters ++ address
    let expectedSize := item.range.count * item.range.area.elementSize
    if item.payload.size != expectedSize then
      throw (.invalidPayloadSize item.payload.size expectedSize)
    let dataLength := if item.range.area.dataTransportSize == octetTransportSize then
      item.payload.size
    else
      item.payload.size * 8
    if dataLength > maxSectionSize then
      throw (.invalidSize item.payload.size)
    data := data ++ bytes #[0, item.range.area.dataTransportSize] ++
      uint16BE (UInt16.ofNat dataLength) ++ item.payload
    if index + 1 < items.size && item.payload.size % 2 != 0 then
      data := data ++ bytes #[0]
    index := index + 1
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
    throw (.invalidField (responseHeaderSize + 2) s!"read item failed with code {returnCode}")
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

def decodeAreaReadMany (reference : UInt16) (ranges : Array MemoryRange)
    (response : Response) : Except DecodeError (Array ReadItemResult) := do
  if ranges.isEmpty || ranges.size > maxItemCount then
    throw (.invalidField responseHeaderSize s!"invalid expected item count {ranges.size}")
  validateItemParameters response reference readFunction ranges.size
  let (results, cursor) ← decodeReadItems ranges.toList { data := response.data }
  cursor.finish
  return results.toArray

private def decodeWriteItems : Nat → Cursor → Except DecodeError (List WriteItemResult × Cursor)
  | 0, cursor => pure ([], cursor)
  | count + 1, cursor => do
      let (returnCode, cursor) ← cursor.readUInt8
      let result := if returnCode == 0xff then WriteItemResult.success else .failure returnCode
      let (results, cursor) ← decodeWriteItems count cursor
      return (result :: results, cursor)

def decodeAreaWriteMany (reference : UInt16) (expectedCount : Nat)
    (response : Response) : Except DecodeError (Array WriteItemResult) := do
  if expectedCount == 0 || expectedCount > maxItemCount then
    throw (.invalidField responseHeaderSize s!"invalid expected item count {expectedCount}")
  validateItemParameters response reference writeFunction expectedCount
  let (results, cursor) ← decodeWriteItems expectedCount { data := response.data }
  cursor.finish
  return results.toArray

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
    throw (.invalidField (responseHeaderSize + 2) s!"write item failed with code {returnCode}")

end LeanS7.S7
