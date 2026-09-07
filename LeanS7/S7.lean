import LeanS7.Binary

namespace LeanS7.S7

def protocolId : UInt8 := 0x32
def jobType : UInt8 := 0x01
def setupCommunicationFunction : UInt8 := 0xf0
def jobHeaderSize : Nat := 10
def maxSectionSize : Nat := 65535

inductive EncodeError where
  | parametersTooLarge (size maximum : Nat)
  | dataTooLarge (size maximum : Nat)
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

end LeanS7.S7
