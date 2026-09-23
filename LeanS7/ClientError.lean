namespace LeanS7

/-- Stable categories for errors raised by the stateful client and transport.
    The underlying `IO.Error` remains available to retain its diagnostic text
    and operating-system error code. -/
inductive ClientErrorKind where
  | invalidInput
  | protocol
  | plcRejected
  | timeout
  | disconnected
  | lifecycle
  | transport
  | other
  deriving BEq, Repr

private def plcRejectedCode : UInt32 := 0xffffffff

/-- Classify both lean-s7 errors and native socket errors without inspecting
    rendered error messages. -/
def classifyClientError : IO.Error → ClientErrorKind
  | .invalidArgument .. => .invalidInput
  | .protocolError code .. => if code == plcRejectedCode then .plcRejected else .protocol
  | .timeExpired .. => .timeout
  | .resourceVanished .. => .disconnected
  | .illegalOperation .. => .lifecycle
  | .resourceBusy .. | .resourceExhausted .. | .inappropriateType ..
  | .unsupportedOperation .. | .hardwareFault .. | .unsatisfiedConstraints ..
  | .interrupted .. | .noFileOrDirectory .. | .permissionDenied ..
  | .alreadyExists .. | .noSuchThing .. | .otherError .. => .transport
  | .unexpectedEof => .disconnected
  | _ => .other

/-- Transport failures eligible for retry consideration. This does not establish
    replay safety: operation-aware policy must also permit resending the request. -/
def isRetryableClientError (error : IO.Error) : Bool :=
  match classifyClientError error with
  | .timeout | .disconnected | .transport => true
  | _ => false

namespace ClientError

def invalidInput (details : String) : IO.Error :=
  .invalidArgument none 0 details

def protocol (details : String) : IO.Error :=
  .protocolError 0 details

def plcRejected (details : String) : IO.Error :=
  .protocolError plcRejectedCode details

def timeout (details : String) : IO.Error :=
  .timeExpired 0 details

def disconnected (details : String) : IO.Error :=
  .resourceVanished 0 details

def lifecycle (details : String) : IO.Error :=
  .illegalOperation 0 details

end ClientError
end LeanS7
