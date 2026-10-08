import LeanS7.Client

/-! Request encoders against the official native Snap7 client.

`integration/native_client_requests.py` points the pinned native client library at a
recording stub peer and stores the first request it sends for each operation (and the
follow-up it sends after a fragment that announces more data) in
`integration/native_client_requests.json`. The strings below are those PDUs with the PDU
reference zeroed. They come from an implementation independent of lean-s7, python-snap7
and the conformance corpus, so agreement here cannot be a shared assumption; the
`0x11`/`0x12` follow-up method error was exactly such a shared assumption.

Native encodings that lean-s7 deliberately does not mirror:
   - plc-status: lean-s7 reads the CPU state through SZL, not the native status request
   - read-db-bit-1.3: lean-s7 has no bit-addressed request; bits are a byte read-modify-write
   - read-db300-word-0x1fe: native reads words with the WORD transport size and an element count
   - write-db-bit-5.3: lean-s7 has no bit-addressed request; bits are a byte read-modify-write
   - write-mk-word: native writes words with the WORD transport size and an element count

This is evidence for the request bytes only, not controller qualification. -/

namespace LeanS7.NativeRequestTests

open LeanS7

private def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

private def hex (text : String) : ByteArray :=
  let rec go : List Char -> ByteArray -> ByteArray
    | high :: low :: rest, acc => go rest (acc.push (UInt8.ofNat (hexValue high * 16 + hexValue low)))
    | _, acc => acc
  go text.toList ByteArray.empty

private def bytes (values : Array UInt8) : ByteArray := ByteArray.mk values

private def same (label expected : String) (result : Except S7.EncodeError ByteArray) : IO Unit :=
  match result with
  | .ok actual =>
    unless actual == hex expected do
      throw <| IO.userError s!"native request vectors: {label} differs from the native client"
  | .error _ => throw <| IO.userError s!"native request vectors: {label} rejected"

def run : IO Unit := do
  same "block-info-DB-65535" "3207000000000008000c0001120411430300ff0900083041363535333541" (S7.encodeGetBlockInfo 0 .dataBlock 65535)
  same "block-info-DB-7" "3207000000000008000c0001120411430300ff0900083041303030303741" (S7.encodeGetBlockInfo 0 .dataBlock 7)
  same "block-info-FB-7" "3207000000000008000c0001120411430300ff0900083045303030303741" (S7.encodeGetBlockInfo 0 .functionBlock 7)
  same "block-info-FC-7" "3207000000000008000c0001120411430300ff0900083043303030303741" (S7.encodeGetBlockInfo 0 .function 7)
  same "block-info-OB-7" "3207000000000008000c0001120411430300ff0900083038303030303741" (S7.encodeGetBlockInfo 0 .organizationBlock 7)
  same "block-info-SDB-7" "3207000000000008000c0001120411430300ff0900083042303030303741" (S7.encodeGetBlockInfo 0 .systemDataBlock 7)
  same "block-info-SFB-7" "3207000000000008000c0001120411430300ff0900083046303030303741" (S7.encodeGetBlockInfo 0 .systemFunctionBlock 7)
  same "block-info-SFC-7" "3207000000000008000c0001120411430300ff0900083044303030303741" (S7.encodeGetBlockInfo 0 .systemFunction 7)
  same "clear-session-password" "3207000000000008000400011204114502000a000000" (S7.encodeClearPassword 0)
  same "compress" "3201000000000010000028000000000000fd0000055f47415242" (S7.encodeCompress 0)
  same "copy-ram-to-rom" "3201000000000012000028000000000000fd00024550055f4d4f4455" (S7.encodeCopyRamToRom 0)
  same "dbread-1-0-8" "320100000000000e00000401120a10020008000184000000" (S7.encodeDbRead 0 { dbNumber := 1, start := 0, size := 8 })
  same "delete-DB-7" "320100000000001a000028000000000000fd000a01003041303030303742055f44454c45" (S7.encodeDeleteBlock 0 .dataBlock 7)
  same "delete-FB-7" "320100000000001a000028000000000000fd000a01003045303030303742055f44454c45" (S7.encodeDeleteBlock 0 .functionBlock 7)
  same "delete-FC-7" "320100000000001a000028000000000000fd000a01003043303030303742055f44454c45" (S7.encodeDeleteBlock 0 .function 7)
  same "delete-OB-7" "320100000000001a000028000000000000fd000a01003038303030303742055f44454c45" (S7.encodeDeleteBlock 0 .organizationBlock 7)
  same "delete-SDB-7" "320100000000001a000028000000000000fd000a01003042303030303742055f44454c45" (S7.encodeDeleteBlock 0 .systemDataBlock 7)
  same "delete-SFB-7" "320100000000001a000028000000000000fd000a01003046303030303742055f44454c45" (S7.encodeDeleteBlock 0 .systemFunctionBlock 7)
  same "delete-SFC-7" "320100000000001a000028000000000000fd000a01003044303030303742055f44454c45" (S7.encodeDeleteBlock 0 .systemFunction 7)
  same "download-start" "320100000000002000001a00010000000000095f30413030303037500d31303030313238303030303136" (S7.encodeRequestDownload 0 .dataBlock 7 128 16)
  same "list-blocks" "3207000000000008000400011204114301000a000000" (S7.encodeListBlocks 0)
  same "list-blocks-of-type-DB" "320700000000000800060001120411430200ff0900023041" (S7.encodeListBlocksOfType 0 .dataBlock)
  same "list-blocks-of-type-FB" "320700000000000800060001120411430200ff0900023045" (S7.encodeListBlocksOfType 0 .functionBlock)
  same "list-blocks-of-type-FC" "320700000000000800060001120411430200ff0900023043" (S7.encodeListBlocksOfType 0 .function)
  same "list-blocks-of-type-OB" "320700000000000800060001120411430200ff0900023038" (S7.encodeListBlocksOfType 0 .organizationBlock)
  same "list-blocks-of-type-SDB" "320700000000000800060001120411430200ff0900023042" (S7.encodeListBlocksOfType 0 .systemDataBlock)
  same "list-blocks-of-type-SFB" "320700000000000800060001120411430200ff0900023046" (S7.encodeListBlocksOfType 0 .systemFunctionBlock)
  same "list-blocks-of-type-SFC" "320700000000000800060001120411430200ff0900023044" (S7.encodeListBlocksOfType 0 .systemFunction)
  same "multi-read" "320100000000001a00000402120a10020002000184000000120a10020003000284000020" (S7.encodeAreaReadMany 0 #[{ area := .dataBlocks, dbNumber := 1, start := 0, count := 2 }, { area := .dataBlocks, dbNumber := 2, start := 4, count := 3 }])
  same "multi-write" "320100000000001a000d0502120a10020002000184000000120a1002000300028400002000040010000000040018000000" (S7.encodeAreaWriteMany 0 #[{ range := { area := .dataBlocks, dbNumber := 1, start := 0, count := 2 }, payload := bytes #[0, 0] }, { range := { area := .dataBlocks, dbNumber := 2, start := 4, count := 3 }, payload := bytes #[0, 0, 0] }])
  same "plc-cold-start" "3201000000000016000028000000000000fd0002432009505f50524f4752414d" (S7.encodePlcColdStart 0)
  same "plc-hot-start" "3201000000000014000028000000000000fd000009505f50524f4752414d" (S7.encodePlcHotStart 0)
  same "plc-stop" "3201000000000010000029000000000009505f50524f4752414d" (S7.encodePlcStop 0)
  same "read-clock" "3207000000000008000400011204114701000a000000" (S7.encodeReadClock 0)
  same "read-ct-16" "320100000000000e00000401120a101c000200001c000010" (S7.encodeAreaRead 0 { area := .counters, dbNumber := 0, start := 16, count := 2 })
  same "read-db1-byte-16x2" "320100000000000e00000401120a10020002000184000080" (S7.encodeAreaRead 0 { area := .dataBlocks, dbNumber := 1, start := 16, count := 2 })
  same "read-mk-byte" "320100000000000e00000401120a10020004000083000320" (S7.encodeAreaRead 0 { area := .markers, dbNumber := 0, start := 100, count := 4 })
  same "read-pa-byte" "320100000000000e00000401120a10020004000082000038" (S7.encodeAreaRead 0 { area := .processOutputs, dbNumber := 0, start := 7, count := 4 })
  same "read-pe-byte" "320100000000000e00000401120a10020004000081000038" (S7.encodeAreaRead 0 { area := .processInputs, dbNumber := 0, start := 7, count := 4 })
  same "read-szl-0x0011-0" "320700000000000800080001120411440100ff09000400110000" (S7.encodeReadSzl 0 0x0011 0)
  same "read-szl-0x001c-3" "320700000000000800080001120411440100ff090004001c0003" (S7.encodeReadSzl 0 0x001c 3)
  same "read-szl-0x0424-0" "320700000000000800080001120411440100ff09000404240000" (S7.encodeReadSzl 0 0x0424 0)
  same "read-tm-16" "320100000000000e00000401120a101d000200001d000010" (S7.encodeAreaRead 0 { area := .timers, dbNumber := 0, start := 16, count := 2 })
  same "start-full-upload-DB-7" "320100000000001200001d00000000000000095f3041303030303741" (S7.encodeStartUpload 0 .dataBlock 7)
  same "start-upload-DB-7" "320100000000001200001d00000000000000095f3041303030303741" (S7.encodeStartUpload 0 .dataBlock 7)
  same "start-upload-FB-7" "320100000000001200001d00000000000000095f3045303030303741" (S7.encodeStartUpload 0 .functionBlock 7)
  same "start-upload-FC-7" "320100000000001200001d00000000000000095f3043303030303741" (S7.encodeStartUpload 0 .function 7)
  same "start-upload-OB-7" "320100000000001200001d00000000000000095f3038303030303741" (S7.encodeStartUpload 0 .organizationBlock 7)
  same "start-upload-SDB-7" "320100000000001200001d00000000000000095f3042303030303741" (S7.encodeStartUpload 0 .systemDataBlock 7)
  same "start-upload-SFB-7" "320100000000001200001d00000000000000095f3046303030303741" (S7.encodeStartUpload 0 .systemFunctionBlock 7)
  same "start-upload-SFC-7" "320100000000001200001d00000000000000095f3044303030303741" (S7.encodeStartUpload 0 .systemFunction 7)
  same "write-db1-byte-16x2" "320100000000000e00060501120a1002000200018400008000040010aabb" (S7.encodeAreaWrite 0 { area := .dataBlocks, dbNumber := 1, start := 16, count := 2 } (bytes #[0xaa, 0xbb]))
  match S7.encodePassword "abc" with
  | .ok encoded => same "set-session-password" "3207000000000008000c0001120411450100ff0900083437024277370242" (S7.encodeSetPassword 0 encoded)
  | .error _ => throw <| IO.userError "native request vectors: password set-session-password rejected"
  match S7.encodePassword "12345678" with
  | .ok encoded => same "set-session-password-8" "3207000000000008000c0001120411450100ff0900086467020662650008" (S7.encodeSetPassword 0 encoded)
  | .error _ => throw <| IO.userError "native request vectors: password set-session-password-8 rejected"
  let moment : S7.PlcDateTime := { year := 2026, month := 9, day := 24, hour := 12, minute := 34, second := 56, weekday := 5 }
  match S7.encodePlcDateTime moment with
  | .ok payload => same "set-clock" "3207000000000008000e0001120411470200ff09000a00192609241234560005" (S7.encodeSetClock 0 payload)
  | .error _ => throw <| IO.userError "native request vectors: clock payload rejected"
  same "list-blocks-of-type-DB follow-up" "320700000000000c0004000112081243027b000000000a000000" (S7.encodeUserDataContinuation 0 S7.blocksInfoGroup S7.listBlocksOfTypeSubfunction 0x7b)
  same "list-blocks-of-type-OB follow-up" "320700000000000c0004000112081243027b000000000a000000" (S7.encodeUserDataContinuation 0 S7.blocksInfoGroup S7.listBlocksOfTypeSubfunction 0x7b)
  same "read-szl-0x001c-3 follow-up" "320700000000000c0004000112081244017b000000000a000000" (S7.encodeReadSzlContinuation 0 0x7b)
  same "read-szl-0x0424-0 follow-up" "320700000000000c0004000112081244017b000000000a000000" (S7.encodeReadSzlContinuation 0 0x7b)
  IO.println "native client request vectors passed"

end LeanS7.NativeRequestTests
