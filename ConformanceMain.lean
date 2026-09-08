import Lean.Data.Json
import LeanS7.Conformance

open Lean
open LeanS7.Conformance

private def hexDigit (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('a'.toNat + value - 10)

private def byteHex (value : UInt8) : String :=
  String.ofList [hexDigit (value.toNat / 16), hexDigit (value.toNat % 16)]

private def bytesHex (value : ByteArray) : String :=
  value.data.foldl (init := "") fun result byte => result ++ byteHex byte

private def chunkJson : ByteChunk → Json
  | .hex value => Json.mkObj [("hex", bytesHex value)]
  | .repeat value count => Json.mkObj [
      ("repeat", Json.mkObj [("byte_hex", byteHex value), ("count", count)])
    ]

private def byteSpecJson (spec : ByteSpec) : Json :=
  Json.mkObj [("chunks", Json.arr (spec.chunks.map chunkJson))]

private def encodeExpectationJson : TPKT.EncodeExpectation → Json
  | .accept packet => Json.mkObj [
      ("status", "accept"),
      ("packet", byteSpecJson packet)
    ]
  | .reject error => Json.mkObj [("status", "reject"), ("error", error)]

private def encodeCaseJson (test : TPKT.EncodeCase) : Json :=
  Json.mkObj [
    ("id", test.id),
    ("payload", byteSpecJson test.payload),
    ("expected", encodeExpectationJson test.expected)
  ]

private def decodeExpectationJson : TPKT.DecodeExpectation → Json
  | .accept payload => Json.mkObj [
      ("status", "accept"),
      ("payload", byteSpecJson payload)
    ]
  | .reject error => Json.mkObj [("status", "reject"), ("error", error)]

private def decodeCaseJson (test : TPKT.DecodeCase) : Json :=
  Json.mkObj [
    ("id", test.id),
    ("packet", byteSpecJson test.packet),
    ("expected", decodeExpectationJson test.expected)
  ]

private def tpktCorpus : Json := Json.mkObj [
  ("schema_version", 1),
  ("protocol", "RFC 1006 TPKT"),
  ("encode_cases", Json.arr (TPKT.encodeCases.map encodeCaseJson)),
  ("decode_cases", Json.arr (TPKT.decodeCases.map decodeCaseJson))
]

private def cotpEncodeCaseJson (test : COTP.EncodeCase) : Json :=
  Json.mkObj [
    ("id", test.id),
    ("payload", byteSpecJson test.payload),
    ("end_of_transmission", test.endOfTransmission),
    ("expected", byteSpecJson test.expected)
  ]

private def cotpDecodeExpectationJson : COTP.DecodeExpectation → Json
  | .accept data => Json.mkObj [
      ("status", "accept"),
      ("payload", byteSpecJson data.payload),
      ("end_of_transmission", data.endOfTransmission)
    ]
  | .reject error => Json.mkObj [("status", "reject"), ("error", error)]

private def cotpDecodeCaseJson (test : COTP.DecodeCase) : Json :=
  Json.mkObj [
    ("id", test.id),
    ("packet", byteSpecJson test.packet),
    ("expected", cotpDecodeExpectationJson test.expected)
  ]

private def cotpCorpus : Json := Json.mkObj [
  ("schema_version", 1),
  ("protocol", "RFC 2126 COTP class 0 data TPDU"),
  ("encode_cases", Json.arr (COTP.encodeCases.map cotpEncodeCaseJson)),
  ("decode_cases", Json.arr (COTP.decodeCases.map cotpDecodeCaseJson))
]

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println (Json.pretty tpktCorpus 100)
  | ["cotp"] => IO.println (Json.pretty cotpCorpus 100)
  | _ => throw <| IO.userError "usage: lean-s7-conformance [cotp]"
