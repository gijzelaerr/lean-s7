import LeanS7.S7
import LeanS7.ClientError

namespace LeanS7

/-- One wire write, not necessarily one entire caller item. Ranges retain the
    address and element count; a successful prefix is never an atomic commit. -/
structure WriteAcknowledgement where
  range : S7.MemoryRange
  result : S7.WriteItemResult
  deriving Repr

structure WriteProgress where
  acknowledged : Array WriteAcknowledgement := #[]
  /-- Scalar/global PLC rejections for which no per-item code is available. -/
  rejected : Array S7.MemoryRange := #[]
  /-- Earlier unacknowledged attempts preceding an explicitly permitted replay.
      A later acknowledgement or rejection cannot establish whether these earlier
      attempts changed the PLC. Repeated ranges retain repeated uncertain attempts. -/
  replayedUncertain : Array S7.MemoryRange := #[]
  /-- These requests may have reached the PLC but have no validated item result.
      This is uncertainty, not evidence of either success or rollback. -/
  uncertain : Array S7.MemoryRange := #[]
  deriving Repr

structure WriteFailure where
  error : IO.Error
  progress : WriteProgress

def WriteFailure.kind (failure : WriteFailure) : ClientErrorKind :=
  classifyClientError failure.error

end LeanS7
