import LeanS7.Management

namespace LeanS7.S7

/-- Clock encoding never truncates a valid value into a shorter payload. -/
theorem encodePlcDateTime_size (value : PlcDateTime) (payload : ByteArray)
    (encoded : encodePlcDateTime value = .ok payload) : payload.size = 10 := by
  unfold encodePlcDateTime at encoded
  cases validated : value.validate with
  | error error => simp [validated, bind, Except.bind] at encoded
  | ok result =>
    simp only [validated, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at encoded
    rw [← encoded]
    rfl

/-- All non-ten-byte inputs are rejected before attempting any field read. -/
theorem decodePlcDateTime_wrong_size (payload : ByteArray) (size : payload.size ≠ 10) :
    decodePlcDateTime payload = .error (.invalidField 0
      s!"clock payload must contain 10 bytes, got {payload.size}") := by
  simp [decodePlcDateTime, size, bind, Except.bind, throw, throwThe]
  rfl

/-- The packed millisecond digit is decimal, independently of all other bytes.
    In particular, otherwise-valid dates cannot mask an A–F high nibble. -/
theorem decodePlcDateTime_invalid_millisecond_digit
    (reserved header year month day hour minute second millis tail : UInt8)
    (invalid : tail.toNat / 16 > 9) :
    decodePlcDateTime (bytes #[reserved, header, year, month, day, hour,
      minute, second, millis, tail]) =
      .error (.invalidField 9 "invalid BCD millisecond digit") := by
  simp only [decodePlcDateTime, Cursor.readUInt8, Cursor.finish, bytes,
    ByteArray.size, bind, Except.bind, pure, Except.pure]
  simp [ByteArray.getElem_eq_getElem_data, -ByteArray.size_data, invalid, throw, throwThe]
  rfl

end LeanS7.S7
