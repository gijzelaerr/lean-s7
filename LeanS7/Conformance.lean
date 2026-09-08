import LeanS7.TPKT

namespace LeanS7.Conformance

/-- A compact, language-neutral description of bytes used by conformance vectors. -/
inductive ByteChunk where
  | hex (value : ByteArray)
  | repeat (value : UInt8) (count : Nat)
  deriving BEq

structure ByteSpec where
  chunks : Array ByteChunk
  deriving BEq

namespace ByteSpec

def materialize (spec : ByteSpec) : ByteArray :=
  spec.chunks.foldl (init := ByteArray.empty) fun result chunk =>
    match chunk with
    | .hex value => result ++ value
    | .repeat value count => result ++ ByteArray.mk (Array.replicate count value)

end ByteSpec

namespace TPKT

inductive EncodeExpectation where
  | accept (packet : ByteSpec)
  | reject (error : String)

structure EncodeCase where
  id : String
  payload : ByteSpec
  expected : EncodeExpectation

inductive DecodeExpectation where
  | accept (payload : ByteSpec)
  | reject (error : String)

structure DecodeCase where
  id : String
  packet : ByteSpec
  expected : DecodeExpectation

private def literal (value : ByteArray) : ByteSpec :=
  { chunks := #[.hex value] }

private def repeated (initial : ByteArray) (value : UInt8) (count : Nat) : ByteSpec :=
  { chunks := #[.hex initial, .repeat value count] }

def encodeCases : Array EncodeCase := #[
  {
    id := "minimum-valid"
    payload := literal (LeanS7.bytes #[0x02, 0xf0, 0x80])
    expected := .accept (literal (LeanS7.bytes #[0x03, 0x00, 0x00, 0x07, 0x02, 0xf0, 0x80]))
  },
  {
    id := "ordinary-payload"
    payload := literal (LeanS7.bytes #[0x02, 0xf0, 0x80, 0xde, 0xad])
    expected := .accept (literal
      (LeanS7.bytes #[0x03, 0x00, 0x00, 0x09, 0x02, 0xf0, 0x80, 0xde, 0xad]))
  },
  {
    id := "below-minimum"
    payload := literal (LeanS7.bytes #[0x02, 0xf0])
    expected := .reject "frame-too-small"
  },
  {
    id := "maximum-valid"
    payload := repeated ByteArray.empty 0xaa (LeanS7.TPKT.maxFrameSize - LeanS7.TPKT.headerSize)
    expected := .accept (repeated (LeanS7.bytes #[0x03, 0x00, 0xff, 0xff]) 0xaa
      (LeanS7.TPKT.maxFrameSize - LeanS7.TPKT.headerSize))
  },
  {
    id := "above-maximum"
    payload := repeated ByteArray.empty 0xaa
      (LeanS7.TPKT.maxFrameSize - LeanS7.TPKT.headerSize + 1)
    expected := .reject "frame-too-large"
  }
]

def decodeCases : Array DecodeCase := #[
  {
    id := "minimum-valid"
    packet := literal (LeanS7.bytes #[0x03, 0x00, 0x00, 0x07, 0x02, 0xf0, 0x80])
    expected := .accept (literal (LeanS7.bytes #[0x02, 0xf0, 0x80]))
  },
  {
    id := "reserved-input-is-ignored"
    packet := literal (LeanS7.bytes #[0x03, 0xff, 0x00, 0x07, 0x02, 0xf0, 0x80])
    expected := .accept (literal (LeanS7.bytes #[0x02, 0xf0, 0x80]))
  },
  {
    id := "unsupported-version"
    packet := literal (LeanS7.bytes #[0x04, 0x00, 0x00, 0x07, 0x02, 0xf0, 0x80])
    expected := .reject "invalid-version"
  },
  {
    id := "declared-length-below-minimum"
    packet := literal (LeanS7.bytes #[0x03, 0x00, 0x00, 0x06, 0x02, 0xf0])
    expected := .reject "length-below-minimum"
  },
  {
    id := "declared-length-mismatch"
    packet := literal (LeanS7.bytes #[0x03, 0x00, 0x00, 0x08, 0x02, 0xf0, 0x80])
    expected := .reject "length-mismatch"
  },
  {
    id := "truncated-header"
    packet := literal (LeanS7.bytes #[0x03, 0x00, 0x00])
    expected := .reject "unexpected-end"
  },
  {
    id := "maximum-valid"
    packet := repeated (LeanS7.bytes #[0x03, 0x00, 0xff, 0xff]) 0xaa
      (LeanS7.TPKT.maxFrameSize - LeanS7.TPKT.headerSize)
    expected := .accept (repeated ByteArray.empty 0xaa
      (LeanS7.TPKT.maxFrameSize - LeanS7.TPKT.headerSize))
  }
]

end TPKT
end LeanS7.Conformance
