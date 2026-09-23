import LeanS7.Value

namespace LeanS7.Value

/-- A DB WORD round trip at any byte offset, with arbitrary surrounding bytes. -/
theorem getUInt16_putUInt16_surrounded (pre suffix : ByteArray) (value : UInt16) :
    getUInt16 (pre ++ (putUInt16 value ++ suffix)) pre.size = .ok value := by
  unfold getUInt16
  simp only [putUInt16]
  change ((Cursor.readUInt16BE { data := pre ++ (uint16BE value ++ suffix), offset := pre.size }).mapError Error.decode >>=
    (fun pair => pure pair.1)) = _
  rw [Cursor.readUInt16BE_append_uint16BE]
  rfl

/-- Signed DB WORDs preserve two's-complement values even inside a larger DB. -/
theorem getInt16_putInt16_surrounded (pre suffix : ByteArray) (value : Int16) :
    getInt16 (pre ++ (putInt16 value ++ suffix)) pre.size = .ok value := by
  rw [getInt16, putInt16, getUInt16_putUInt16_surrounded]
  change Except.ok value.toUInt16.toInt16 = Except.ok value
  rw [Int16.toInt16_toUInt16]

/-- REAL decoding preserves the encoded bit interpretation, without assuming
    floating-point equality (which is inappropriate for NaNs). -/
theorem getReal_putReal_bits (value : Float32) :
    getReal (putReal value) = .ok (Float32.ofBits value.toBits) := by
  rw [getReal, putReal, getUInt32_putUInt32]
  rfl

theorem getLReal_putLReal_bits (value : Float) :
    getLReal (putLReal value) = .ok (Float.ofBits value.toBits) := by
  rw [getLReal, putLReal, getUInt64_putUInt64]
  rfl

end LeanS7.Value
