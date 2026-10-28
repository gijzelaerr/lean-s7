namespace LeanS7

/-- The packed-array traversal agrees with the underlying array's list view. -/
theorem byteArray_toList_data (data : ByteArray) : data.toList = data.data.toList := by
  have hloop (index : Nat) (accumulator : List UInt8) :
      ByteArray.toList.loop data index accumulator =
        accumulator.reverse ++ data.data.toList.drop index := by
    fun_induction ByteArray.toList.loop data index accumulator with
    | case1 index accumulator h ih =>
      rw [ih, List.reverse_cons]
      have hi : index < data.data.toList.length := by
        simpa only [Array.length_toList, ByteArray.size_data] using h
      rw [List.drop_eq_getElem_cons hi]
      simp only [List.append_assoc, List.singleton_append]
      congr 2
      simp only [Array.getElem_toList]
      change data.data[index]! = data.data[index]
      exact getElem!_pos data.data index (by simpa only [ByteArray.size_data] using h)
    | case2 index accumulator h =>
      have hi : data.data.toList.length ≤ index := by
        simp only [Array.length_toList, ByteArray.size_data]
        omega
      simp only [List.drop_eq_nil_of_le hi, List.append_nil]
  exact hloop 0 []

/-- A decoding failure with the byte offset at which it was detected. -/
inductive DecodeError where
  | unexpectedEnd (offset needed available : Nat)
  | invalidField (offset : Nat) (message : String)
  /-- A syntactically valid response in which the remote PLC reports failure. -/
  | remoteFailure (offset : Nat) (message : String)
  | trailingBytes (offset count : Nat)
  deriving Repr, BEq

/-- A cursor into immutable packet data. Reads advance by returning a new cursor. -/
structure Cursor where
  data : ByteArray
  offset : Nat := 0

namespace Cursor

def remaining (cursor : Cursor) : Nat :=
  cursor.data.size - cursor.offset

def readUInt8 (cursor : Cursor) : Except DecodeError (UInt8 × Cursor) :=
  if h : cursor.offset < cursor.data.size then
    let value := cursor.data[cursor.offset]'h
    .ok (value, { cursor with offset := cursor.offset + 1 })
  else
    .error (.unexpectedEnd cursor.offset 1 cursor.remaining)

def readUInt16BE (cursor : Cursor) : Except DecodeError (UInt16 × Cursor) := do
  let (high, cursor) ← cursor.readUInt8
  let (low, cursor) ← cursor.readUInt8
  return (UInt16.ofNat (high.toNat * 256 + low.toNat), cursor)

def readUInt24BE (cursor : Cursor) : Except DecodeError (UInt32 × Cursor) := do
  let (a, cursor) ← cursor.readUInt8
  let (b, cursor) ← cursor.readUInt8
  let (c, cursor) ← cursor.readUInt8
  return (UInt32.ofNat (a.toNat * 65536 + b.toNat * 256 + c.toNat), cursor)

def readUInt32BE (cursor : Cursor) : Except DecodeError (UInt32 × Cursor) := do
  let (high, cursor) ← cursor.readUInt16BE
  let (low, cursor) ← cursor.readUInt16BE
  return (UInt32.ofNat (high.toNat * 65536 + low.toNat), cursor)

def readUInt64BE (cursor : Cursor) : Except DecodeError (UInt64 × Cursor) := do
  let (high, cursor) ← cursor.readUInt32BE
  let (low, cursor) ← cursor.readUInt32BE
  return (UInt64.ofNat (high.toNat * 4294967296 + low.toNat), cursor)

def readBytes (cursor : Cursor) (count : Nat) : Except DecodeError (ByteArray × Cursor) :=
  if count ≤ cursor.remaining then
    let next := cursor.offset + count
    .ok (cursor.data.extract cursor.offset next, { cursor with offset := next })
  else
    .error (.unexpectedEnd cursor.offset count cursor.remaining)

def finish (cursor : Cursor) : Except DecodeError Unit :=
  if cursor.offset = cursor.data.size then
    .ok ()
  else
    .error (.trailingBytes cursor.offset cursor.remaining)

/-- A successful bounded read returns exactly the requested number of bytes. -/
theorem readBytes_size (cursor next : Cursor) (count : Nat) (payload : ByteArray)
    (h : cursor.readBytes count = .ok (payload, next)) : payload.size = count := by
  unfold readBytes at h
  split at h
  · cases h
    simp only [ByteArray.size_extract]
    unfold remaining at *
    omega
  · contradiction

/-- A successful byte read stays on the same data, advances exactly one byte and
    started inside the input. -/
theorem readUInt8_ok (cursor next : Cursor) (value : UInt8)
    (h : cursor.readUInt8 = .ok (value, next)) :
    next.data = cursor.data ∧ next.offset = cursor.offset + 1 ∧
      cursor.offset < cursor.data.size := by
  unfold readUInt8 at h
  split at h
  · injection h with h
    injection h with _ hn
    subst hn
    exact ⟨rfl, rfl, by assumption⟩
  · contradiction

/-- A successful bounded read stays on the same data and advances exactly the
    requested number of bytes. -/
theorem readBytes_next (cursor next : Cursor) (count : Nat) (payload : ByteArray)
    (h : cursor.readBytes count = .ok (payload, next)) :
    next.data = cursor.data ∧ next.offset = cursor.offset + count ∧
      count ≤ cursor.remaining := by
  unfold readBytes at h
  split at h
  · injection h with h
    injection h with _ hn
    subst hn
    exact ⟨rfl, rfl, by assumption⟩
  · contradiction

/-- A byte read succeeds when the cursor points inside the input. -/
theorem readUInt8_of_lt (cursor : Cursor) (h : cursor.offset < cursor.data.size) :
    cursor.readUInt8 = .ok (cursor.data[cursor.offset],
      { cursor with offset := cursor.offset + 1 }) := by
  simp [readUInt8, h]

/-- Two available bytes decode as a big-endian word and advance the cursor twice. -/
theorem readUInt16BE_of_available (cursor : Cursor)
    (h : cursor.offset + 2 ≤ cursor.data.size) :
    cursor.readUInt16BE = .ok (
      UInt16.ofNat (
        cursor.data[cursor.offset].toNat * 256 +
          cursor.data[cursor.offset + 1].toNat),
      { cursor with offset := cursor.offset + 2 }) := by
  rw [readUInt16BE, readUInt8_of_lt cursor (by omega)]
  change (do
    let result ← readUInt8 { cursor with offset := cursor.offset + 1 }
    pure (UInt16.ofNat (
      cursor.data[cursor.offset].toNat * 256 + result.fst.toNat), result.snd)) = _
  rw [readUInt8_of_lt _ (by simp; omega)]
  rfl

/-- A successful big-endian word read stays on the same data, advances exactly
    two bytes, and was fully inside the input. -/
theorem readUInt16BE_ok (cursor next : Cursor) (value : UInt16)
    (h : cursor.readUInt16BE = .ok (value, next)) :
    next.data = cursor.data ∧ next.offset = cursor.offset + 2 ∧
      cursor.offset + 2 ≤ cursor.data.size := by
  by_cases hl : cursor.offset + 2 ≤ cursor.data.size
  · rw [readUInt16BE_of_available cursor hl] at h
    injection h with h
    injection h with _ hn
    subst hn
    exact ⟨rfl, rfl, hl⟩
  · exfalso
    by_cases h1 : cursor.offset < cursor.data.size
    · have h2 : ¬(cursor.offset + 1 < cursor.data.size) := by omega
      simp [readUInt16BE, readUInt8, h1, h2, bind, Except.bind] at h
    · simp [readUInt16BE, readUInt8, h1, bind, Except.bind] at h

/-- Four available bytes decode as a big-endian double word and advance the
    cursor four positions. -/
theorem readUInt32BE_of_available (cursor : Cursor)
    (h : cursor.offset + 4 ≤ cursor.data.size) :
    cursor.readUInt32BE = .ok (
      UInt32.ofNat (
        (UInt16.ofNat (
          cursor.data[cursor.offset].toNat * 256 +
            cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
        (UInt16.ofNat (
          cursor.data[cursor.offset + 2].toNat * 256 +
            cursor.data[cursor.offset + 3].toNat)).toNat),
      { cursor with offset := cursor.offset + 4 }) := by
  rw [readUInt32BE, readUInt16BE_of_available cursor (by omega)]
  change (do
    let result ← readUInt16BE { cursor with offset := cursor.offset + 2 }
    pure (UInt32.ofNat (
      (UInt16.ofNat (
        cursor.data[cursor.offset].toNat * 256 +
          cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
        result.fst.toNat), result.snd)) = _
  rw [readUInt16BE_of_available _ (by simp; omega)]
  rfl

/-- Eight available bytes decode as a big-endian quad word and advance the
    cursor eight positions. -/
theorem readUInt64BE_of_available (cursor : Cursor)
    (h : cursor.offset + 8 ≤ cursor.data.size) :
    cursor.readUInt64BE = .ok (
      UInt64.ofNat (
        (UInt32.ofNat (
          (UInt16.ofNat (
            cursor.data[cursor.offset].toNat * 256 +
              cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
          (UInt16.ofNat (
            cursor.data[cursor.offset + 2].toNat * 256 +
              cursor.data[cursor.offset + 3].toNat)).toNat)).toNat * 4294967296 +
        (UInt32.ofNat (
          (UInt16.ofNat (
            cursor.data[cursor.offset + 4].toNat * 256 +
              cursor.data[cursor.offset + 5].toNat)).toNat * 65536 +
          (UInt16.ofNat (
            cursor.data[cursor.offset + 6].toNat * 256 +
              cursor.data[cursor.offset + 7].toNat)).toNat)).toNat),
      { cursor with offset := cursor.offset + 8 }) := by
  rw [readUInt64BE, readUInt32BE_of_available cursor (by omega)]
  change (do
    let result ← readUInt32BE { cursor with offset := cursor.offset + 4 }
    pure (UInt64.ofNat (
      (UInt32.ofNat (
        (UInt16.ofNat (
          cursor.data[cursor.offset].toNat * 256 +
            cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
        (UInt16.ofNat (
          cursor.data[cursor.offset + 2].toNat * 256 +
            cursor.data[cursor.offset + 3].toNat)).toNat)).toNat * 4294967296 +
        result.fst.toNat), result.snd)) = _
  rw [readUInt32BE_of_available _ (by simp; omega)]
  rfl

/-- A successful byte read returns the input byte at the cursor and advances one byte. -/
theorem readUInt8_value (cursor next : Cursor) (value : UInt8)
    (h : cursor.readUInt8 = .ok (value, next)) :
    ∃ hlt : cursor.offset < cursor.data.size,
      cursor.data[cursor.offset] = value ∧ next = { cursor with offset := cursor.offset + 1 } := by
  unfold readUInt8 at h
  split at h
  · rename_i hlt
    injection h with h
    injection h with hv hn
    exact ⟨hlt, hv, hn.symm⟩
  · contradiction

/-- A successful big-endian word read returns the two input bytes at the cursor
    and advances two bytes. -/
theorem readUInt16BE_value (cursor next : Cursor) (value : UInt16)
    (h : cursor.readUInt16BE = .ok (value, next)) :
    ∃ hl : cursor.offset + 2 ≤ cursor.data.size,
      value = UInt16.ofNat (cursor.data[cursor.offset].toNat * 256 +
        cursor.data[cursor.offset + 1].toNat) ∧
      next = { cursor with offset := cursor.offset + 2 } := by
  obtain ⟨_, _, hl⟩ := readUInt16BE_ok _ _ _ h
  rw [readUInt16BE_of_available cursor hl] at h
  injection h with h
  injection h with hv hn
  exact ⟨hl, hv.symm, hn.symm⟩

/-- A successful bounded read returns exactly the input bytes it covered. -/
theorem readBytes_value (cursor next : Cursor) (count : Nat) (payload : ByteArray)
    (h : cursor.readBytes count = .ok (payload, next)) :
    payload = cursor.data.extract cursor.offset (cursor.offset + count) ∧
      next = { cursor with offset := cursor.offset + count } := by
  unfold readBytes at h
  split at h
  · injection h with h
    injection h with hp hn
    exact ⟨hp.symm, hn.symm⟩
  · contradiction

/-- A successful finish means the cursor consumed the whole input. -/
theorem finish_ok (cursor : Cursor) (h : cursor.finish = .ok ()) :
    cursor.offset = cursor.data.size := by
  unfold finish at h
  split at h
  · assumption
  · contradiction

end Cursor

/-- An input splits at any position into the bytes before it and the bytes after it. -/
theorem ByteArray.eq_extract_append_extract (data : ByteArray) (position : Nat)
    (h : position ≤ data.size) :
    data = data.extract 0 position ++ data.extract position data.size := by
  rw [ByteArray.extract_append_extract]
  simp only [Nat.zero_le, Nat.min_eq_left, Nat.max_eq_right h]
  exact ByteArray.extract_zero_size.symm

def uint16BE (value : UInt16) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint16BE_size (value : UInt16) : (uint16BE value).size = 2 := by
  rfl

/-- The word a big-endian read builds from two bytes encodes back to those bytes. -/
theorem uint16BE_ofBytes (high low : UInt8) :
    uint16BE (UInt16.ofNat (high.toNat * 256 + low.toNat)) = ByteArray.mk #[high, low] := by
  have hh := high.toNat_lt
  have hl := low.toNat_lt
  have hn : (UInt16.ofNat (high.toNat * 256 + low.toNat)).toNat = high.toNat * 256 + low.toNat := by
    rw [UInt16.toNat_ofNat']
    omega
  have hhigh : UInt8.ofNat ((high.toNat * 256 + low.toNat) / 256) = high := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  have hlow : UInt8.ofNat (high.toNat * 256 + low.toNat) = low := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  simp only [uint16BE, hn, hhigh, hlow]

/-- Adjacent ranges of one input join into the range that spans both. -/
theorem ByteArray.extract_append_extract_of_le (data : ByteArray) {i j k : Nat}
    (hij : i ≤ j) (hjk : j ≤ k) :
    data.extract i j ++ data.extract j k = data.extract i k := by
  rw [ByteArray.extract_append_extract, Nat.min_eq_left hij, Nat.max_eq_right hjk]

/-- The single input byte at a position, as a one-byte range. -/
theorem ByteArray.extract_one (data : ByteArray) (position : Nat)
    (h : position < data.size) :
    data.extract position (position + 1) = ByteArray.mk #[data[position]] := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  apply Array.ext
  · simp; omega
  · intro i _ hi
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    simp only [Array.getElem_extract, Nat.add_zero]
    rfl

/-- The two input bytes at a position, as a two-byte range. -/
theorem ByteArray.extract_two (data : ByteArray) (position : Nat)
    (h : position + 2 ≤ data.size) :
    data.extract position (position + 2) =
      ByteArray.mk #[data[position], data[position + 1]] := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  apply Array.ext
  · simp; omega
  · intro i _ hi
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    simp only [Array.getElem_extract]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

/-- Two input bytes at a position are the big-endian encoding of the word a
    `Cursor.readUInt16BE` there returns. -/
theorem ByteArray.extract_two_uint16BE (data : ByteArray) (position : Nat)
    (h : position + 2 ≤ data.size) :
    data.extract position (position + 2) =
      uint16BE (UInt16.ofNat (data[position].toNat * 256 + data[position + 1].toNat)) := by
  rw [uint16BE_ofBytes, ByteArray.extract_two data position h]

/-- Encoding then reading a big-endian word returns the original value. -/
theorem readUInt16BE_uint16BE (value : UInt16) :
    Cursor.readUInt16BE { data := uint16BE value } =
      .ok (value, { data := uint16BE value, offset := 2 }) := by
  rw [Cursor.readUInt16BE_of_available _ (by
    change 2 ≤ (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp)]
  change Except.ok (UInt16.ofNat (
    (UInt8.ofNat (value.toNat / 256)).toNat * 256 +
      (UInt8.ofNat value.toNat).toNat),
    ({ data := uint16BE value, offset := 2 } : Cursor)) =
    Except.ok (value, ({ data := uint16BE value, offset := 2 } : Cursor))
  congr 2
  apply UInt16.toNat_inj.mp
  simp [UInt16.toNat_add, UInt16.toNat_mul, UInt8.toNat_ofNat']
  have h := UInt16.toNat_lt value
  omega

/-- A big-endian word can be read at the boundary between an arbitrary prefix
    and suffix. This is the compositional form used by protocol codec proofs. -/
theorem Cursor.readUInt16BE_append_uint16BE (pre suffix : ByteArray)
    (value : UInt16) :
    Cursor.readUInt16BE {
      data := pre ++ (uint16BE value ++ suffix)
      offset := pre.size
    } = .ok (value, {
      data := pre ++ (uint16BE value ++ suffix)
      offset := pre.size + 2
    }) := by
  let data := pre ++ (uint16BE value ++ suffix)
  rw [Cursor.readUInt16BE_of_available (cursor := { data, offset := pre.size }) (by
    dsimp only [data]
    rw [ByteArray.size_append, ByteArray.size_append]
    change pre.size + 2 ≤ pre.size + (2 + suffix.size)
    omega)]
  congr 2
  have hdata0 : pre.size < data.size := by
    dsimp only [data]
    rw [ByteArray.size_append, ByteArray.size_append]
    change pre.size < pre.size + (2 + suffix.size)
    omega
  have hdata1 : pre.size + 1 < data.size := by
    dsimp only [data]
    rw [ByteArray.size_append, ByteArray.size_append]
    change pre.size + 1 < pre.size + (2 + suffix.size)
    omega
  have hword0 : 0 < (uint16BE value).size := by
    change 0 < (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp
  have hword1 : 1 < (uint16BE value).size := by
    change 1 < (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp
  have hget0 : data[pre.size]'hdata0 = (uint16BE value)[0]'hword0 := by
    dsimp only [data]
    rw [ByteArray.getElem_append_right (by omega)]
    simp only [Nat.sub_self]
    rw [ByteArray.getElem_append_left hword0]
  have hget1 : data[pre.size + 1]'hdata1 = (uint16BE value)[1]'hword1 := by
    dsimp only [data]
    rw [ByteArray.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [ByteArray.getElem_append_left hword1]
  rw [hget0, hget1]
  have hround := readUInt16BE_uint16BE value
  rw [Cursor.readUInt16BE_of_available _ (by
    change 2 ≤ (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp)] at hround
  injection hround with hpair
  injection hpair with hvalue

/-- Reading the next complete byte segment returns that segment and leaves the
    cursor at the following boundary. -/
theorem Cursor.readBytes_append (pre value suffix : ByteArray) :
    Cursor.readBytes {
      data := pre ++ (value ++ suffix)
      offset := pre.size
    } value.size = .ok (value, {
      data := pre ++ (value ++ suffix)
      offset := pre.size + value.size
    }) := by
  let data := pre ++ (value ++ suffix)
  rw [Cursor.readBytes, if_pos (by simp [Cursor.remaining])]
  have hextract : data.extract pre.size (pre.size + value.size) = value := by
    dsimp only [data]
    rw [show (pre ++ (value ++ suffix)).extract pre.size
        (pre.size + value.size) = (value ++ suffix).extract 0 value.size by
      simpa using (ByteArray.extract_append_size_add
        (a := pre) (b := value ++ suffix) (i := 0) (j := value.size))]
    exact ByteArray.extract_append_eq_left rfl
  change Except.ok
    (data.extract pre.size (pre.size + value.size),
      ({ data, offset := pre.size + value.size } : Cursor)) = _
  rw [hextract]

def uint24BE (value : UInt32) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint24BE_size (value : UInt32) : (uint24BE value).size = 3 := by
  rfl

def uint32BE (value : UInt32) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[
    UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint32BE_size (value : UInt32) : (uint32BE value).size = 4 := by
  rfl

/-- Encoding then reading a big-endian double word returns the original value. -/
theorem readUInt32BE_uint32BE (value : UInt32) :
    Cursor.readUInt32BE { data := uint32BE value } =
      .ok (value, { data := uint32BE value, offset := 4 }) := by
  rw [Cursor.readUInt32BE_of_available _ (by simp)]
  congr 2
  apply UInt32.toNat_inj.mp
  simp only [uint32BE, ByteArray.getElem_eq_getElem_data]
  simp [UInt32.toNat_ofNat', UInt16.toNat_ofNat', UInt8.toNat_ofNat']
  have h := UInt32.toNat_lt value
  omega

def uint64BE (value : UInt64) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[
    UInt8.ofNat (n / 72057594037927936), UInt8.ofNat (n / 281474976710656),
    UInt8.ofNat (n / 1099511627776), UInt8.ofNat (n / 4294967296),
    UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint64BE_size (value : UInt64) : (uint64BE value).size = 8 := by
  rfl

set_option maxHeartbeats 800000 in
/-- Encoding then reading a big-endian quad word returns the original value. -/
theorem readUInt64BE_uint64BE (value : UInt64) :
    Cursor.readUInt64BE { data := uint64BE value } =
      .ok (value, { data := uint64BE value, offset := 8 }) := by
  rw [Cursor.readUInt64BE_of_available _ (by simp)]
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [uint64BE, ByteArray.getElem_eq_getElem_data]
  simp [UInt64.toNat_ofNat', UInt32.toNat_ofNat', UInt16.toNat_ofNat',
    UInt8.toNat_ofNat']
  have h := UInt64.toNat_lt value
  omega

/-- An in-bounds byte of a surrounded segment is independent of its neighbours. -/
theorem getElem_surrounded (pre value suffix : ByteArray) (index : Nat)
    (h : index < value.size) :
    (pre ++ (value ++ suffix))[pre.size + index]'(by simp; omega) = value[index] := by
  rw [ByteArray.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [ByteArray.getElem_append_left h]

/-- DWORD decoding is compositional at any byte offset. -/
theorem Cursor.readUInt32BE_append_uint32BE (pre suffix : ByteArray) (value : UInt32) :
    Cursor.readUInt32BE { data := pre ++ (uint32BE value ++ suffix), offset := pre.size } =
      .ok (value, { data := pre ++ (uint32BE value ++ suffix), offset := pre.size + 4 }) := by
  rw [Cursor.readUInt32BE_of_available _ (by simp)]
  have hround := readUInt32BE_uint32BE value
  rw [Cursor.readUInt32BE_of_available _ (by simp)] at hround
  have hget (index : Nat) (h : index < 4) :
      (pre ++ (uint32BE value ++ suffix))[pre.size + index]'(by simp; omega) =
        (uint32BE value)[index]'(by simp; omega) :=
    getElem_surrounded pre (uint32BE value) suffix index (by simpa using h)
  have h0 := hget 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, hget 1 (by omega), hget 2 (by omega), hget 3 (by omega)]
  injection hround with hpair
  injection hpair with hvalue
  rw [hvalue]

/-- LWORD decoding is compositional at any byte offset. -/
theorem Cursor.readUInt64BE_append_uint64BE (pre suffix : ByteArray) (value : UInt64) :
    Cursor.readUInt64BE { data := pre ++ (uint64BE value ++ suffix), offset := pre.size } =
      .ok (value, { data := pre ++ (uint64BE value ++ suffix), offset := pre.size + 8 }) := by
  rw [Cursor.readUInt64BE_of_available _ (by simp)]
  have hround := readUInt64BE_uint64BE value
  rw [Cursor.readUInt64BE_of_available _ (by simp)] at hround
  have hget (index : Nat) (h : index < 8) :
      (pre ++ (uint64BE value ++ suffix))[pre.size + index]'(by simp; omega) =
        (uint64BE value)[index]'(by simp; omega) :=
    getElem_surrounded pre (uint64BE value) suffix index (by simpa using h)
  have h0 := hget 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, hget 1 (by omega), hget 2 (by omega), hget 3 (by omega),
    hget 4 (by omega), hget 5 (by omega), hget 6 (by omega), hget 7 (by omega)]
  injection hround with hpair
  injection hpair with hvalue
  rw [hvalue]

def bytes (values : Array UInt8) : ByteArray :=
  ByteArray.mk values

@[simp] theorem bytes_size (values : Array UInt8) : (bytes values).size = values.size := by
  rfl

theorem Cursor.readUInt8_append_byte (pre suffix : ByteArray) (value : UInt8) :
    Cursor.readUInt8 { data := pre ++ (bytes #[value] ++ suffix), offset := pre.size } =
      .ok (value, { data := pre ++ (bytes #[value] ++ suffix), offset := pre.size + 1 }) := by
  rw [Cursor.readUInt8_of_lt _ (by simp [bytes_size]; omega)]
  have hget := getElem_surrounded pre (bytes #[value]) suffix 0 (by simp [bytes_size])
  simp only [Nat.add_zero] at hget
  rw [hget]
  rfl

end LeanS7
