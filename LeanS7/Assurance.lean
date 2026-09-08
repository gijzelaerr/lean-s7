import LeanS7.Protocol
import LeanS7.Client
import LeanS7.Value

namespace LeanS7

/-- The explicitly scoped, machine-checked safety contract for the implemented
    classic S7 protocol core. It does not claim coverage of S7comm Plus or
    controller-specific service semantics. -/
structure CoreProtocolAssurance : Prop where
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
  responseCorrelation : ∀ response reference function,
    S7.validateResponse response reference function = .ok () →
      response.reference = reference
  responseErrorFree : ∀ response reference function,
    S7.validateResponse response reference function = .ok () →
      response.errorClass = 0 ∧ response.errorCode = 0
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
  chunkCoverage : ∀ total maximum,
    maximum ≠ 0 → (Chunking.counts total maximum).sum = total
  chunkBounds : ∀ total maximum chunk,
    maximum ≠ 0 → chunk ∈ Chunking.counts total maximum →
      0 < chunk ∧ chunk ≤ maximum
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
  disconnectTotal : ∀ state,
    Lifecycle.transition state .disconnect = some .closed
  closedLifecycleTerminal : ∀ event next,
    Lifecycle.transition .closed event = some next → next = .closed
  reconnectLegal : ∀ state next,
    Lifecycle.transition state .reconnected = some next →
      state = .disconnected ∧ next = .connected

/-- The implementation satisfies the complete formal contract stated by
    `CoreProtocolAssurance`. -/
theorem coreProtocolAssurance : CoreProtocolAssurance := by
  constructor
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
  · exact S7.decodeJob_encodeJob
  · exact S7.decodeResponse_encodeAckData
  · exact Protocol.decodeJob_encodeJob
  · exact Protocol.decodeResponse_encodeAckData
  · exact S7.decodeJob_encodeSetupCommunication
  · exact S7.validateResponse_reference_eq
  · exact S7.validateResponse_error_free
  · exact S7.validateSetupPduLength_lower_bound
  · exact S7.validateMemoryRange_invariants
  · exact S7.encodedMemoryAddress_size
  · exact S7.encodedAreaRead_size
  · exact S7.encodedAreaWrite_size
  · exact Chunking.counts_sum
  · exact Chunking.counts_bounds
  · exact takeReadBatch_preserves_order
  · exact takeReadBatch_count_le
  · exact takeReadBatch_fits
  · exact takeWriteBatch_fits
  · exact takeWriteBatch_preserves_order
  · exact takeWriteBatch_count_le
  · exact Lifecycle.transition_disconnect
  · exact Lifecycle.closed_is_terminal
  · exact Lifecycle.reconnect_transition

end LeanS7
