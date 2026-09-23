import LeanS7.Client

open LeanS7

namespace BatchingTests

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def range (index count : Nat) (area : S7.Area := .dataBlocks) : S7.MemoryRange :=
  { area, dbNumber := if area == .dataBlocks then 1 else 0
    start := index * 2, count }

private def payload (size : Nat) : ByteArray := bytes (Array.replicate size 0xa5)

/-- Exercise the actual client planner, then independently encode its selected
    items. These executable checks complement, rather than replace, certificates. -/
def testPlans : IO Unit := do
  for budget in [0, 13, 14, 23, 24, 25, 35, 36, 37, 239, 240, 241, 479, 480] do
    for count in [0, 1, 2, 3, 5, 17, 111, 222, 223, 224, 225] do
      for area in [S7.Area.dataBlocks, .timers] do
        for length in [0, 1, 2, 19, 20, 21, 25, 41] do
          let ranges := (List.range length).map (fun index => range index count area)
          let reads := planReadBatch budget ranges
          check (reads.selected ++ reads.remaining == ranges) "read partition changed order"
          check (reads.selected.length ≤ 20) "read item count exceeded limit"
          if !reads.selected.isEmpty then
            match S7.encodeAreaReadMany 7 reads.selected.toArray with
            | .error err => throw <| IO.userError s!"selected read failed encoding: {repr err}"
            | .ok packet =>
              check (packet.size == 12 + 12 * reads.selected.length)
                "actual read encoding disagrees with planner accounting"
              check (packet.size ≤ budget) "actual read encoding exceeded PDU"
              check (14 + readResponseContributions reads.selected ≤ budget)
                "read response exceeded PDU"
          let items := ranges.map fun r =>
            ({ range := r, payload := payload (r.count * r.area.elementSize) } : S7.WriteItem)
          let writes := planWriteBatch budget items
          check (writes.selected ++ writes.remaining == items) "write partition changed order"
          check (writes.selected.length ≤ 20) "write item count exceeded limit"
          if !writes.selected.isEmpty then
            match S7.encodeAreaWriteMany 7 writes.selected.toArray with
            | .error err => throw <| IO.userError s!"selected write failed encoding: {repr err}"
            | .ok packet =>
              let lastPadding := match writes.selected.getLast? with
                | some item => item.payload.size % 2
                | none => 0
              check (packet.size + lastPadding == 12 + writeRequestContributions writes.selected)
                "actual write encoding disagrees with conservative planner accounting"
              check (packet.size ≤ budget) "actual write encoding exceeded PDU"
              check (14 + writes.selected.length ≤ budget) "write response exceeded PDU"
  let invalid : S7.WriteItem := { range := range 1 2, payload := payload 1 }
  let valid : S7.WriteItem := { range := range 0 1, payload := payload 1 }
  let stopped := planWriteBatch 480 [valid, invalid, valid]
  check (stopped.selected == [valid] && stopped.remaining == [invalid, valid])
    "invalid middle write was skipped or reordered"

private def rejected {α : Type} : Except DecodeError α → Bool
  | .error _ => true
  | .ok _ => false

def testMixedResponses : IO Unit := do
  let ranges := #[range 0 1, range 1 2, range 2 1]
  for failure in [0, 1, 3, 5, 10, 0xfe] do
    let response : S7.Response :=
      { pduType := 3, errorClass := 0, errorCode := 0
        reference := 7, parameters := bytes #[4, 3]
        data := bytes #[0xff, 4, 0, 8, 0xa1, 0,
          failure, 0, 0, 0, 0xff, 4, 0, 8, 0xb2] }
    let expected := #[S7.ReadItemResult.success (bytes #[0xa1]),
      .failure failure, .success (bytes #[0xb2])]
    check (match S7.decodeAreaReadMany 7 ranges response with
      | .ok actual => actual == expected | .error _ => false)
      "middle read failure changed subsequent result order"
    for size in List.range response.data.size do
      check (rejected (S7.decodeAreaReadMany 7 ranges
        { response with data := response.data.extract 0 size }))
        "truncated mixed read response was accepted"
    check (rejected (S7.decodeAreaReadMany 7 ranges
      { response with data := response.data ++ bytes #[0] })) "trailing read byte accepted"
    for count in [0, 1, 2, 4, 20, 255] do
      check (rejected (S7.decodeAreaReadMany 7 ranges
        { response with parameters := bytes #[4, count] })) "wrong read result count accepted"
    let write : S7.Response :=
      { pduType := 3, errorClass := 0, errorCode := 0
        reference := 7, parameters := bytes #[5, 3], data := bytes #[0xff, failure, 0xff] }
    check (match S7.decodeAreaWriteMany 7 3 write with
      | .ok actual => actual == #[.success, .failure failure, .success]
      | .error _ => false) "middle write failure changed subsequent result order"
    for size in [0, 1, 2] do
      check (rejected (S7.decodeAreaWriteMany 7 3
        { write with data := write.data.extract 0 size })) "truncated write results accepted"
    check (rejected (S7.decodeAreaWriteMany 7 3
      { write with data := write.data ++ bytes #[0xff] })) "trailing write result accepted"
    check (rejected (S7.decodeAreaWriteMany 8 3 write)) "wrong write reference accepted"

def run : IO Unit := do
  testPlans
  testMixedResponses

end BatchingTests
