import LeanS7.Advanced
import LeanS7.Management

namespace LeanS7.S7

/-- Successful end-upload decoding proves correlation and the exact empty
    acknowledgement shape. -/
theorem decodeEndUpload_contract (reference : UInt16) (response : Response)
    (h : decodeEndUpload reference response = .ok ()) :
    response.reference = reference ∧ response.parameters.size = 1 ∧
      response.data.isEmpty = true := by
  have hv : validateResponse response reference endUploadFunction = .ok () := by
    cases hv : validateResponse response reference endUploadFunction with
    | error e => simp [decodeEndUpload, hv, bind, Except.bind] at h
    | ok u => cases u; rfl
  refine ⟨validateResponse_reference_eq _ _ _ hv, ?_⟩
  by_cases hs : response.parameters.size = 1 <;> by_cases hd : response.data.isEmpty = true <;>
    simp_all [decodeEndUpload, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Successful request-download acknowledgement proves correlation and the
    exact empty acknowledgement shape. -/
theorem decodeRequestDownloadAck_contract (reference : UInt16) (response : Response)
    (h : decodeRequestDownloadAck reference response = .ok ()) :
    response.reference = reference ∧ response.parameters.size = 1 ∧
      response.data.isEmpty = true := by
  have hv : validateResponse response reference requestDownloadFunction = .ok () := by
    cases hv : validateResponse response reference requestDownloadFunction with
    | error e => simp [decodeRequestDownloadAck, hv, bind, Except.bind] at h
    | ok u => cases u; rfl
  refine ⟨validateResponse_reference_eq _ _ _ hv, ?_⟩
  by_cases hs : response.parameters.size = 1 <;> by_cases hd : response.data.isEmpty = true <;>
    simp_all [decodeRequestDownloadAck, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Successful PLC-control decoding proves correlation, a one- or two-byte
    parameter section, and no data section. -/
theorem decodePlcControl_contract (reference : UInt16) (function : UInt8)
    (response : Response)
    (h : decodePlcControl reference function response = .ok ()) :
    response.reference = reference ∧
      (response.parameters.size = 1 ∨ response.parameters.size = 2) ∧
      response.data.isEmpty = true := by
  have hv : validateResponse response reference function = .ok () := by
    cases hv : validateResponse response reference function with
    | error e => simp [decodePlcControl, hv, bind, Except.bind] at h
    | ok u => cases u; rfl
  refine ⟨validateResponse_reference_eq _ _ _ hv, ?_⟩
  by_cases hs : response.parameters.size = 1 <;> by_cases hs2 : response.parameters.size = 2 <;>
    by_cases hd : response.data.isEmpty = true <;>
    simp_all [decodePlcControl, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Successful start-upload decoding proves correlation, one of the two
    supported parameter extents, and no data section. -/
theorem decodeStartUpload_contract (reference : UInt16) (response : Response)
    (result : StartUploadResponse)
    (h : decodeStartUpload reference response = .ok result) :
    response.reference = reference ∧
      (response.parameters.size = 8 ∨ response.parameters.size = 16) ∧
      response.data.isEmpty = true := by
  have hv : validateResponse response reference startUploadFunction = .ok () := by
    cases hv : validateResponse response reference startUploadFunction with
    | error e => simp [decodeStartUpload, hv, bind, Except.bind] at h
    | ok u => cases u; rfl
  refine ⟨validateResponse_reference_eq _ _ _ hv, ?_⟩
  by_cases hs : response.parameters.size = 8 <;> by_cases hs2 : response.parameters.size = 16 <;>
    by_cases hd : response.data.isEmpty = true <;>
    simp_all [decodeStartUpload, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Successful single-item DB-write decoding proves correlation and exact
    one-item parameter and one-byte data extents. -/
theorem decodeDbWrite_contract (reference : UInt16) (response : Response)
    (h : decodeDbWrite reference response = .ok ()) :
    response.reference = reference ∧ response.parameters.size = 2 ∧
      response.data.size = 1 := by
  have hv : validateResponse response reference writeFunction = .ok () := by
    cases hv : validateResponse response reference writeFunction with
    | error e => simp [decodeDbWrite, hv, bind, Except.bind] at h
    | ok u => cases u; rfl
  refine ⟨validateResponse_reference_eq _ _ _ hv, ?_⟩
  by_cases hs : response.parameters.size = 2 <;> by_cases hd : response.data.size = 1 <;>
    simp_all [decodeDbWrite, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      Cursor.readUInt8, Cursor.finish] <;> (split at h <;> simp at h)

/-- Successful setup-communication decoding proves correlation, the exact
    eight-byte parameter section, and the protocol-minimum PDU length. -/
theorem decodeSetupCommunication_contract (reference : UInt16) (response : Response)
    (result : SetupCommunication)
    (h : decodeSetupCommunication reference response = .ok result) :
    response.reference = reference ∧ response.parameters.size = 8 ∧
      240 ≤ result.pduLength.toNat := by
  have hv : validateResponse response reference setupCommunicationFunction = .ok () := by
    cases hv : validateResponse response reference setupCommunicationFunction with
    | error e => simp [decodeSetupCommunication, hv, bind, Except.bind] at h
    | ok u => cases u; rfl
  refine ⟨validateResponse_reference_eq _ _ _ hv, ?_⟩
  by_cases hs : response.parameters.size = 8
  · refine ⟨hs, ?_⟩
    have hp : validateSetupPduLength result.pduLength = .ok () := by
      simp [decodeSetupCommunication, hv, hs, bind, Except.bind, Cursor.readUInt16BE,
        Cursor.readUInt8, Cursor.finish] at h
      repeat' (split at h)
      all_goals first | (simp at h; done) | skip
      injection h with hr
      subst hr
      exact ‹validateSetupPduLength _ = _›
    exact validateSetupPduLength_lower_bound _ hp
  · simp [decodeSetupCommunication, hv, hs, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h

/-- A decoded SZL keeps its requested identity and its data section is exactly
    the size its own header declares; payloads with any other extent fail. -/
theorem decodeSzl_contract (id index : UInt16) (payload : ByteArray) (szl : Szl)
    (h : decodeSzl id index payload = .ok szl) :
    szl.id = id ∧ szl.index = index ∧
      szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  simp only [decodeSzl, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first | (simp at h; done) | skip
  all_goals first
    | (injection h with hr; subst hr; simp_all)
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›)

/-- A decoded upload fragment proves correlation, the two-byte parameter
    section, and that the data section is exactly a four-byte header plus the
    returned fragment bytes. -/
theorem decodeUploadFragment_contract (reference : UInt16) (response : Response)
    (fragment : UploadFragment)
    (h : decodeUploadFragment reference response = .ok fragment) :
    response.reference = reference ∧ response.parameters.size = 2 ∧
      response.data.size = fragment.data.size + 4 := by
  have hv : validateResponse response reference uploadFunction = .ok () := by
    cases hv : validateResponse response reference uploadFunction with
    | error e => simp [decodeUploadFragment, hv, bind, Except.bind] at h
    | ok u => cases u; rfl
  refine ⟨validateResponse_reference_eq _ _ _ hv, ?_⟩
  by_cases hs : response.parameters.size = 2
  · refine ⟨hs, ?_⟩
    simp only [decodeUploadFragment, hv, hs, bind, Except.bind, pure, Except.pure] at h
    repeat' (split at h)
    all_goals first | (simp at h; done) | skip
    all_goals first
      | (exfalso; simp_all; done)
      | (injection h with hr
         subst hr
         have h1 := Cursor.readBytes_size _ _ _ _ ‹Cursor.readBytes _ _ = _›
         simp_all <;> omega)
  · simp [decodeUploadFragment, hv, hs, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h

/-- The first SZL fragment decoder consumes exactly the four-byte identity header
    and returns every remaining payload byte. -/
theorem decodeSzlFirst_extent (response : UserDataResponse) (id index : UInt16)
    (rest : ByteArray) (h : decodeSzlFirst response = .ok (id, index, rest)) :
    response.payload.size = rest.size + 4 := by
  simp only [decodeSzlFirst, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (simp at h; done)
    | (injection h with hr
       have h1 := Cursor.readBytes_size _ _ _ _ ‹Cursor.readBytes _ _ = _›
       rename_i x3 v3 e3 x2 v2 e2 x1 v1 e1 x0 v0 e0
       obtain ⟨d1, o1, l1⟩ := Cursor.readUInt16BE_ok _ _ _ e3
       obtain ⟨d2, o2, l2⟩ := Cursor.readUInt16BE_ok _ _ _ e2
       unfold Cursor.remaining at h1
       simp only [Prod.mk.injEq] at hr
       simp only at d1 o1 l1
       have hrest : v1.fst = rest := hr.2.2
       rw [hrest] at h1
       have hsize : v2.snd.data.size = response.payload.size := by rw [d2, d1]
       have hsize' : v3.snd.data.size = response.payload.size := by rw [d1]
       omega)

/-- The compatibility job-PDU decoder is exactly the strict core job decoder. -/
theorem decodeJobPdu_eq (pdu : ByteArray) : decodeJobPdu pdu = decodeJob pdu := rfl

/-- A successful DB read is exactly a successful `decodeAreaRead` of the data-block
    area for the byte count its own response header declares, so the
    reference/extent/payload-size contracts of `decodeAreaRead` apply to it. -/
theorem decodeDbRead_reduces (reference : UInt16) (response : Response)
    (payload : ByteArray) (h : decodeDbRead reference response = .ok payload) :
    ∃ size, decodeAreaRead reference .dataBlocks size response = .ok payload := by
  simp only [decodeDbRead, bind, Except.bind] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | (exact ⟨_, h⟩)

end LeanS7.S7
