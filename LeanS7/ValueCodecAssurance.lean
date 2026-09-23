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

/-- DWORDs round trip at arbitrary offsets, independently of surrounding data. -/
theorem getUInt32_putUInt32_surrounded (pre suffix : ByteArray) (value : UInt32) :
    getUInt32 (pre ++ (putUInt32 value ++ suffix)) pre.size = .ok value := by
  unfold getUInt32
  simp only [putUInt32]
  change ((Cursor.readUInt32BE { data := pre ++ (uint32BE value ++ suffix), offset := pre.size }).mapError Error.decode >>=
    (fun pair => pure pair.1)) = _
  rw [Cursor.readUInt32BE_append_uint32BE]
  rfl

theorem getUInt64_putUInt64_surrounded (pre suffix : ByteArray) (value : UInt64) :
    getUInt64 (pre ++ (putUInt64 value ++ suffix)) pre.size = .ok value := by
  unfold getUInt64
  simp only [putUInt64]
  change ((Cursor.readUInt64BE { data := pre ++ (uint64BE value ++ suffix), offset := pre.size }).mapError Error.decode >>=
    (fun pair => pure pair.1)) = _
  rw [Cursor.readUInt64BE_append_uint64BE]
  rfl

theorem getInt32_putInt32_surrounded (pre suffix : ByteArray) (value : Int32) :
    getInt32 (pre ++ (putInt32 value ++ suffix)) pre.size = .ok value := by
  rw [getInt32, putInt32, getUInt32_putUInt32_surrounded]
  change Except.ok value.toUInt32.toInt32 = Except.ok value
  rw [Int32.toInt32_toUInt32]

theorem getInt64_putInt64_surrounded (pre suffix : ByteArray) (value : Int64) :
    getInt64 (pre ++ (putInt64 value ++ suffix)) pre.size = .ok value := by
  rw [getInt64, putInt64, getUInt64_putUInt64_surrounded]
  change Except.ok value.toUInt64.toInt64 = Except.ok value
  rw [Int64.toInt64_toUInt64]

/-- This states bit interpretation, not IEEE equality or NaN payload preservation. -/
theorem getReal_putReal_surrounded_bits (pre suffix : ByteArray) (value : Float32) :
    getReal (pre ++ (putReal value ++ suffix)) pre.size =
      .ok (Float32.ofBits value.toBits) := by
  rw [getReal, putReal, getUInt32_putUInt32_surrounded]
  rfl

theorem getLReal_putLReal_surrounded_bits (pre suffix : ByteArray) (value : Float) :
    getLReal (pre ++ (putLReal value ++ suffix)) pre.size =
      .ok (Float.ofBits value.toBits) := by
  rw [getLReal, putLReal, getUInt64_putUInt64_surrounded]
  rfl

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
