import LeanS7.Protocol
import LeanS7.Client
import LeanS7.Value
import LeanS7.BatchEncoderAssurance
import LeanS7.ValueCodecAssurance

namespace LeanS7

/-- The explicitly scoped, machine-checked safety contract for the implemented
    classic S7 protocol core. It does not claim coverage of S7comm Plus or
    controller-specific service semantics. -/
structure CoreProtocolAssurance : Prop where
  tpktCodec : ∀ frame packet,
    TPKT.minFrameSize ≤ TPKT.headerSize + frame.payload.size →
    TPKT.headerSize + frame.payload.size ≤ TPKT.maxFrameSize →
    TPKT.encode frame = .ok packet → TPKT.decode packet = .ok frame
  cotpReassemblyBudget : ∀ state next segment maximum complete,
    COTP.Reassembly.pushBounded state segment maximum = .ok (next, complete) →
      next.payload.size ≤ maximum
  cotpDataCodec : ∀ pdu : COTP.Data,
    COTP.decodeData (COTP.encodeData pdu) = .ok pdu
  cotpDisconnectCodec : ∀ request : COTP.DisconnectRequest,
    COTP.decodeDisconnectRequest (COTP.encodeDisconnectRequest request) = .ok request
  cotpSegmentOrder : ∀ (state : COTP.Reassembly) (segment : COTP.Data),
    (state.push segment).1.payload = state.payload ++ segment.payload
  cotpSegmentCompletion : ∀ (state : COTP.Reassembly) (segment : COTP.Data),
    (state.push segment).2 = true ↔ segment.endOfTransmission = true
  cotpConfirmationCorrelation : ∀ request confirmation,
    COTP.validateConnectionConfirm request confirmation = .ok () →
      confirmation.destinationReference = request.sourceReference ∧
      confirmation.classOption = request.classOption
  cotpPayloadBudget : ∀ exponent payloadSize,
    COTP.validateDataPayloadBudget exponent payloadSize = .ok () →
      3 + payloadSize ≤ COTP.tpduSize exponent
  uint8Codec : ∀ value, Value.getUInt8 (Value.putUInt8 value) = .ok value
  uint16Codec : ∀ value, Value.getUInt16 (Value.putUInt16 value) = .ok value
  uint32Codec : ∀ value, Value.getUInt32 (Value.putUInt32 value) = .ok value
  uint64Codec : ∀ value, Value.getUInt64 (Value.putUInt64 value) = .ok value
  int8Codec : ∀ value, Value.getInt8 (Value.putInt8 value) = .ok value
  int16Codec : ∀ value, Value.getInt16 (Value.putInt16 value) = .ok value
  int32Codec : ∀ value, Value.getInt32 (Value.putInt32 value) = .ok value
  int64Codec : ∀ value, Value.getInt64 (Value.putInt64 value) = .ok value
  surroundedWordCodec : ∀ pre suffix value,
    Value.getUInt16 (pre ++ (Value.putUInt16 value ++ suffix)) pre.size = .ok value
  surroundedIntCodec : ∀ pre suffix value,
    Value.getInt16 (pre ++ (Value.putInt16 value ++ suffix)) pre.size = .ok value
  realBitInterpretation : ∀ value,
    Value.getReal (Value.putReal value) = .ok (Float32.ofBits value.toBits)
  lrealBitInterpretation : ∀ value,
    Value.getLReal (Value.putLReal value) = .ok (Float.ofBits value.toBits)
  s7JobCodec : ∀ job packet,
    job.parameters.size ≤ S7.maxSectionSize →
    job.data.size ≤ S7.maxSectionSize →
    S7.encodeJob job = .ok packet → S7.decodeJob packet = .ok job
  s7ResponseCodec : ∀ reference parameters data packet,
    parameters.size ≤ S7.maxSectionSize →
    data.size ≤ S7.maxSectionSize →
    S7.encodeAckData reference parameters data = .ok packet →
      S7.decodeResponse packet = .ok {
        pduType := S7.ackDataType
        reference
        parameters
        data
        errorClass := 0
        errorCode := 0
      }
  completeJobCodec : ∀ job packet,
    job.parameters.size ≤ S7.maxSectionSize →
    job.data.size ≤ S7.maxSectionSize →
    TPKT.headerSize + 3 + S7.jobHeaderSize +
      job.parameters.size + job.data.size ≤ TPKT.maxFrameSize →
    Protocol.encodeJob job = .ok packet → Protocol.decodeJob packet = .ok job
  completeResponseCodec : ∀ reference parameters data packet,
    parameters.size ≤ S7.maxSectionSize →
    data.size ≤ S7.maxSectionSize →
    TPKT.headerSize + 3 + S7.responseHeaderSize +
      parameters.size + data.size ≤ TPKT.maxFrameSize →
    Protocol.encodeAckData reference parameters data = .ok packet →
      Protocol.decodeResponse packet = .ok {
        pduType := S7.ackDataType
        reference
        parameters
        data
        errorClass := 0
        errorCode := 0
      }
  setupRequestCodec : ∀ reference setup packet,
    S7.encodeSetupCommunication reference setup = .ok packet →
      S7.decodeJob packet = .ok {
        reference
        parameters := setup.parameters
        data := ByteArray.empty
      }
  userDataSize : ∀ reference parameters data packet,
    S7.encodeUserDataHeader reference parameters data = .ok packet →
      packet.size = S7.jobHeaderSize + parameters.size + data.size
  userDataReference : ∀ reference parameters data packet,
    parameters.size ≤ S7.maxSectionSize →
    data.size ≤ S7.maxSectionSize →
    S7.encodeUserDataHeader reference parameters data = .ok packet →
      S7.decodePduReference packet = .ok reference
  responseCorrelation : ∀ response reference function,
    S7.validateResponse response reference function = .ok () →
      response.reference = reference
  responseErrorFree : ∀ response reference function,
    S7.validateResponse response reference function = .ok () →
      response.errorClass = 0 ∧ response.errorCode = 0
  responseFunction : ∀ response reference function,
    S7.validateResponse response reference function = .ok () →
      ∃ cursor, Cursor.readUInt8 { data := response.parameters } =
        .ok (function, cursor)
  singleReadPayloadSize : ∀ reference area expectedSize response payload,
    S7.decodeAreaRead reference area expectedSize response = .ok payload →
      payload.size = expectedSize
  negotiatedPduMinimum : ∀ pduLength,
    S7.validateSetupPduLength pduLength = .ok () → 240 ≤ pduLength.toNat
  memoryRangeSafety : ∀ range,
    S7.validateMemoryRange range = .ok () →
      range.count ≠ 0 ∧
      range.count ≤ S7.maxSectionSize ∧
      (range.area ≠ .dataBlocks → range.dbNumber = 0) ∧
      (range.area.usesElementAddress →
        range.start % range.area.elementSize = 0) ∧
      range.wireAddress ≤ 0xffffff ∧
      range.lastWireAddress ≤ 0xffffff
  memoryAddressSize : ∀ range packet,
    S7.encodeMemoryAddress range = .ok packet → packet.size = 12
  singleReadSize : ∀ reference range packet,
    S7.encodeAreaRead reference range = .ok packet → packet.size = 24
  singleWriteSize : ∀ reference range payload packet,
    S7.encodeAreaWrite reference range payload = .ok packet →
      packet.size = 28 + payload.size
  downloadFragmentSize : ∀ reference isLast payload packet,
    S7.encodeDownloadFragmentResponse reference isLast payload = .ok packet →
      packet.size = S7.responseHeaderSize + 6 + payload.size
  downloadNoEarlyFragment : ∀ payload maximum,
    Download.nextFragment payload (Download.start payload) maximum = none
  downloadAckTransition : ∀ payload (state after : Download.State payload),
    Download.acknowledge state = some after →
      state.phase = .awaitingAck ∧ after.phase = .awaitingFragment ∧
        after.offset = state.offset
  downloadNoEarlyFinish : ∀ payload,
    Download.finish payload (Download.start payload) = none
  downloadNoIncompleteFinish : ∀ payload (state : Download.State payload),
    state.offset < payload.size → Download.finish payload state = none
  downloadFragmentOrder : ∀ payload (state : Download.State payload) maximum
      (fragment : Download.Fragment payload state maximum),
    payload.extract 0 fragment.after.offset =
      payload.extract 0 state.offset ++ fragment.chunk
  downloadFragmentBudget : ∀ payload (state : Download.State payload) maximum
      (fragment : Download.Fragment payload state maximum) reference isLast packet,
    S7.encodeDownloadFragmentResponse reference isLast fragment.chunk = .ok packet →
      packet.size ≤ maximum + 18
  downloadFinishExact : ∀ payload (state after : Download.State payload),
    Download.finish payload state = some after →
      state.offset = payload.size ∧ after.phase = .complete
  uploadAssemblyOrder : ∀ maximum (state after : Upload.Assembly maximum) chunk,
    state.append chunk = .ok after → after.data = state.data ++ chunk
  uploadAssemblyBound : ∀ maximum (state : Upload.Assembly maximum),
    state.data.size ≤ maximum
  uploadContinuationProgress : ∀ maximum (state : Upload.State maximum) fragment
      (step : Upload.Step state fragment),
    fragment.isLast = false → state.assembly.data.size < step.after.assembly.data.size
  uploadFinishPhase : ∀ maximum (state after : Upload.State maximum),
    Upload.finish state = .ok after →
      state.phase = .awaitingEnd ∧ after.phase = .complete
  uploadFinishExact : ∀ maximum (state after : Upload.State maximum) expected,
    state.expected = some expected → Upload.finish state = .ok after →
      after.assembly.data.size = expected
  userDataAssemblyOrder : ∀ maximum fragments
      (state : UserDataAssembly.State maximum fragments) chunk more
      (step : UserDataAssembly.Step state chunk more),
    step.after.data = state.data ++ chunk
  userDataAssemblyBounds : ∀ maximum fragments
      (state : UserDataAssembly.State maximum fragments),
    state.data.size ≤ maximum ∧ state.count ≤ fragments
  userDataFragmentProgress : ∀ maximum fragments
      (state : UserDataAssembly.State maximum fragments) chunk more
      (step : UserDataAssembly.Step state chunk more),
    state.count < step.after.count
  userDataContinuationRoom : ∀ maximum fragments
      (state : UserDataAssembly.State maximum fragments) chunk more
      (step : UserDataAssembly.Step state chunk more),
    more = true → step.after.count < fragments
  chunkCoverage : ∀ total maximum,
    maximum ≠ 0 → (Chunking.counts total maximum).sum = total
  chunkBounds : ∀ total maximum chunk,
    maximum ≠ 0 → chunk ∈ Chunking.counts total maximum →
      0 < chunk ∧ chunk ≤ maximum
  readAssemblyOrder : ∀ elementSize consumed count
      (state : Chunking.ReadAssembly elementSize consumed)
      (chunk : { data : ByteArray // data.size = count * elementSize }),
    (state.append chunk).data = state.data ++ chunk.val
  readAssemblyNextStart : ∀ elementSize consumed count
      (state : Chunking.ReadAssembly elementSize consumed)
      (chunk : { data : ByteArray // data.size = count * elementSize }) start,
    (state.append chunk).nextStart start = state.nextStart start + count * elementSize
  readAssemblyCompleteSize : ∀ total maximum elementSize,
    maximum ≠ 0 →
      ∀ state : Chunking.ReadAssembly elementSize (0 + (Chunking.counts total maximum).sum),
        state.data.size = total * elementSize
  writeSliceSize : ∀ payload offset count elementSize hbound,
    (Chunking.writeSlice payload offset count elementSize hbound).val.size = count * elementSize
  writeSlicesComplete : ∀ payload elementSize maximum,
    payload.size % elementSize = 0 → maximum ≠ 0 →
      Chunking.writeSlices payload elementSize 0
        (Chunking.counts (payload.size / elementSize) maximum) = payload
  readBatchOrder : ∀ pduLength pending count requestSize responseSize selected,
    let result := takeReadBatch pduLength pending count requestSize responseSize selected
    result.1 ++ result.2 = selected.reverse ++ pending
  readBatchCount : ∀ pduLength pending count requestSize responseSize selected,
    selected.length = count → count ≤ S7.maxItemCount →
      let result := takeReadBatch pduLength pending count requestSize responseSize selected
      result.1.length ≤ S7.maxItemCount
  readBatchBudget : ∀ pduLength pending,
    12 ≤ pduLength → 14 ≤ pduLength →
      let result := takeReadBatch pduLength pending 0 12 14 []
      12 + 12 * result.1.length ≤ pduLength ∧
        14 + readResponseContributions result.1 ≤ pduLength
  writeBatchBudget : ∀ pduLength pending,
    12 ≤ pduLength → 14 ≤ pduLength →
      let result := takeWriteBatch pduLength pending 0 12 14 []
      12 + writeRequestContributions result.1 ≤ pduLength ∧
        14 + result.1.length ≤ pduLength
  writeBatchOrder : ∀ pduLength pending count requestSize responseSize selected,
    let result := takeWriteBatch pduLength pending count requestSize responseSize selected
    result.1 ++ result.2 = selected.reverse ++ pending
  writeBatchCount : ∀ pduLength pending count requestSize responseSize selected,
    selected.length = count → count ≤ S7.maxItemCount →
      let result := takeWriteBatch pduLength pending count requestSize responseSize selected
      result.1.length ≤ S7.maxItemCount
  plannedReadPositive : ∀ pduLength pending range,
    range ∈ (planReadBatch pduLength pending).selected → 0 < range.count
  plannedWritePayloads : ∀ pduLength pending item,
    item ∈ (planWriteBatch pduLength pending).selected →
      0 < item.range.count ∧ item.payload.size = item.range.count * item.range.area.elementSize
  plannedReadLength : ∀ pduLength pending range,
    range ∈ (planReadBatch pduLength pending).selected →
      MultiValidation.readLengthRepresentable range = true
  plannedWriteLength : ∀ pduLength pending item,
    item ∈ (planWriteBatch pduLength pending).selected →
      MultiValidation.readLengthRepresentable item.range = true
  encodedReadPlanBudget : ∀ reference pduLength pending
      (plan : ReadBatchPlan pduLength pending) packet,
    14 ≤ pduLength → S7.encodeAreaReadMany reference plan.selected.toArray = .ok packet →
      packet.size ≤ pduLength
  encodedWritePlanBudget : ∀ reference pduLength pending
      (plan : WriteBatchPlan pduLength pending) packet,
    14 ≤ pduLength → S7.encodeAreaWriteMany reference plan.selected.toArray = .ok packet →
      packet.size ≤ pduLength
  writeTraceSendHistory : ∀ (state after : WriteProgress.State) locations,
    state.sent locations = .ok after → after.history = state.history
  writeTraceReplayLocations : ∀ state : WriteProgress.State,
    state.replay.history.map (·.location) =
      state.pending.toList.reverse ++ state.history.map (·.location)
  writeTraceAckCount : ∀ (state after : WriteProgress.State) results,
    state.acknowledge results = .ok after → results.size = state.pending.size
  singleUserDataCompletion : ∀ (response : S7.UserDataResponse) payload,
    S7.requireCompleteUserData response = .ok payload →
      response.hasMoreData = false ∧ payload = response.payload
  cotpResourceBytes : ∀ (state next : COTP.Reassembly) segment maximum maxSegments complete,
    state.pushResourceBounded segment maximum maxSegments = .ok (next, complete) →
      next.payload.size ≤ maximum
  cotpResourceSegments : ∀ (state next : COTP.Reassembly) segment maximum maxSegments complete,
    state.pushResourceBounded segment maximum maxSegments = .ok (next, complete) →
      next.segments = state.segments + 1 ∧ next.segments ≤ maxSegments
  surroundedDword : ∀ pre suffix value,
    Value.getUInt32 (pre ++ (Value.putUInt32 value ++ suffix)) pre.size = .ok value
  surroundedLword : ∀ pre suffix value,
    Value.getUInt64 (pre ++ (Value.putUInt64 value ++ suffix)) pre.size = .ok value
  surroundedDint : ∀ pre suffix value,
    Value.getInt32 (pre ++ (Value.putInt32 value ++ suffix)) pre.size = .ok value
  surroundedLint : ∀ pre suffix value,
    Value.getInt64 (pre ++ (Value.putInt64 value ++ suffix)) pre.size = .ok value
  surroundedRealBits : ∀ pre suffix value,
    Value.getReal (pre ++ (Value.putReal value ++ suffix)) pre.size = .ok (Float32.ofBits value.toBits)
  surroundedLrealBits : ∀ pre suffix value,
    Value.getLReal (pre ++ (Value.putLReal value ++ suffix)) pre.size = .ok (Float.ofBits value.toBits)
  stringAllocation : ∀ maximum value encoded,
    Value.encodeString maximum value = .ok encoded → encoded.size = maximum + 2
  wstringAllocation : ∀ maximum value encoded,
    Value.encodeWString maximum value = .ok encoded → encoded.size = maximum * 2 + 4
  stringRoundtrip : ∀ pre suffix maximum value,
    maximum ≤ Value.maxStringLength → value.toList.length ≤ maximum →
    (∀ character ∈ value.toList, character.toNat ≤ 255) →
    (Value.encodeString maximum value >>= fun encoded =>
      Value.decodeString (pre ++ (encoded ++ suffix)) pre.size) = .ok value
  wstringRoundtrip : ∀ pre suffix maximum value,
    maximum ≤ Value.maxWStringLength → Value.utf16Length value ≤ maximum →
    (Value.encodeWString maximum value >>= fun encoded =>
      Value.decodeWString (pre ++ (encoded ++ suffix)) pre.size) = .ok value
  disconnectTotal : ∀ state,
    Lifecycle.transition state .disconnect = some .closed
  closedLifecycleTerminal : ∀ event next,
    Lifecycle.transition .closed event = some next → next = .closed
  reconnectLegal : ∀ state next,
    Lifecycle.transition state .reconnected = some next →
      state = .disconnected ∧ next = .connected
  transportClosureSafety : ∀ state next,
    Lifecycle.transition state .transportClosed = some next →
      next ≠ .connected

/-- The implementation satisfies the complete formal contract stated by
    `CoreProtocolAssurance`. -/
theorem coreProtocolAssurance : CoreProtocolAssurance := by
  constructor
  · exact TPKT.decode_encode
  · exact COTP.Reassembly.pushBounded_size
  · exact COTP.decodeData_encodeData
  · exact COTP.decodeDisconnectRequest_encodeDisconnectRequest
  · exact COTP.Reassembly.push_payload
  · exact COTP.Reassembly.push_complete_iff
  · intro request confirmation hvalidate
    exact ⟨COTP.validateConnectionConfirm_destination_eq request confirmation hvalidate,
      COTP.validateConnectionConfirm_class_eq request confirmation hvalidate⟩
  · exact COTP.validateDataPayloadBudget_fits
  · exact Value.getUInt8_putUInt8
  · exact Value.getUInt16_putUInt16
  · exact Value.getUInt32_putUInt32
  · exact Value.getUInt64_putUInt64
  · exact Value.getInt8_putInt8
  · exact Value.getInt16_putInt16
  · exact Value.getInt32_putInt32
  · exact Value.getInt64_putInt64
  · exact Value.getUInt16_putUInt16_surrounded
  · exact Value.getInt16_putInt16_surrounded
  · exact Value.getReal_putReal_bits
  · exact Value.getLReal_putLReal_bits
  · exact S7.decodeJob_encodeJob
  · exact S7.decodeResponse_encodeAckData
  · exact Protocol.decodeJob_encodeJob
  · exact Protocol.decodeResponse_encodeAckData
  · exact S7.decodeJob_encodeSetupCommunication
  · exact S7.encodedUserDataHeader_size
  · exact S7.decodePduReference_encodeUserDataHeader
  · exact S7.validateResponse_reference_eq
  · exact S7.validateResponse_error_free
  · exact S7.validateResponse_function_eq
  · exact S7.decodeAreaRead_size
  · exact S7.validateSetupPduLength_lower_bound
  · exact S7.validateMemoryRange_invariants
  · exact S7.encodedMemoryAddress_size
  · exact S7.encodedAreaRead_size
  · exact S7.encodedAreaWrite_size
  · exact S7.encodedDownloadFragmentResponse_size
  · exact Download.no_fragment_before_ack
  · exact Download.acknowledge_transition
  · exact Download.no_finish_before_ack
  · exact Download.no_finish_before_complete
  · exact Download.fragment_prefix
  · exact Download.encoded_fragment_fits
  · exact Download.finish_complete
  · exact fun _ => Upload.Assembly.append_order
  · exact fun _ state => state.bounded
  · exact fun _ _ _ step => step.progress
  · exact fun _ => Upload.finish_phase
  · exact fun _ => Upload.finish_exact
  · exact fun _ _ _ _ _ step => step.order
  · exact fun _ _ state => ⟨state.bounded, state.countBounded⟩
  · exact fun _ _ _ _ _ step => UserDataAssembly.accepted_progress step
  · exact fun _ _ _ _ _ step => step.continuationRoom
  · exact Chunking.counts_sum
  · exact Chunking.counts_bounds
  · exact fun _ _ _ => Chunking.ReadAssembly.append_data
  · exact fun _ _ _ => Chunking.ReadAssembly.append_nextStart
  · exact Chunking.ReadAssembly.complete_size
  · intro payload offset count elementSize hbound
    exact (Chunking.writeSlice payload offset count elementSize hbound).property
  · exact Chunking.writeSlices_complete
  · exact takeReadBatch_preserves_order
  · exact takeReadBatch_count_le
  · exact takeReadBatch_fits
  · exact takeWriteBatch_fits
  · exact takeWriteBatch_preserves_order
  · exact takeWriteBatch_count_le
  · exact fun pdu pending => (planReadBatch pdu pending).positive
  · exact fun pdu pending => (planWriteBatch pdu pending).payloads
  · exact fun pdu pending => (planReadBatch pdu pending).lengths
  · exact fun pdu pending => (planWriteBatch pdu pending).lengths
  · exact S7.plannedReadBatch_fits
  · exact S7.plannedWriteBatch_fits
  · exact WriteProgress.State.sent_preserves_history
  · exact WriteProgress.State.replay_history_locations
  · exact WriteProgress.State.acknowledge_count
  · exact S7.requireCompleteUserData_complete
  · exact COTP.Reassembly.pushResourceBounded_size
  · exact COTP.Reassembly.pushResourceBounded_segments
  · exact Value.getUInt32_putUInt32_surrounded
  · exact Value.getUInt64_putUInt64_surrounded
  · exact Value.getInt32_putInt32_surrounded
  · exact Value.getInt64_putInt64_surrounded
  · exact Value.getReal_putReal_surrounded_bits
  · exact Value.getLReal_putLReal_surrounded_bits
  · exact Value.encodeString_size
  · exact Value.encodeWString_size
  · exact Value.decodeString_encodeString_surrounded
  · exact Value.decodeWString_encodeWString_surrounded
  · exact Lifecycle.transition_disconnect
  · exact Lifecycle.closed_is_terminal
  · exact Lifecycle.reconnect_transition
  · exact Lifecycle.transportClosed_not_connected

end LeanS7
