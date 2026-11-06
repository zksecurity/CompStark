/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompPoly.Fields.Binary.BF64.Packed
public import CompStark.Sumcheck.IndexFold
/-! Packed word construction with proved machine-size stores. -/
@[expose] public section
namespace CompStark.Sumcheck
open BF64
/-- Every word offset in an addressable packed buffer has its exact machine value. -/
theorem wordOffset (n : Nat) (hn : 8 * n < USize.size) (i : USize) (hi : i.toNat < n) :
    (i * 8).toNat = 8 * i.toNat ∧ (i * 8 + 4).toNat = 8 * i.toNat + 4 := by
  have hsize : 2 ^ System.Platform.numBits = USize.size := rfl
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)
  have h4 : (4 : USize).toNat = 4 := USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)
  have hm : (i * 8).toNat = 8 * i.toNat := by
    rw [USize.toNat_mul, h8, hsize, Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨hm, ?_⟩
  rw [USize.toNat_add, hm, h4, hsize, Nat.mod_eq_of_lt (by omega)]
/-- Load a word using two bounded machine-size reads. -/
@[inline] def readWord (buffer : Packed.Buffer n) (i : USize) (hi : i.toNat < n)
    (hn : 8 * n < USize.size) : Word :=
  have hs : buffer.val.bytes.size = 8 * n := by rw [buffer.val.byteSize, buffer.property]
  let lo := buffer.val.bytes.ugetUInt32LE (i * 8) (by rw [(wordOffset n hn i hi).1, hs]; omega)
  let high := buffer.val.bytes.ugetUInt32LE (i * 8 + 4) (by rw [(wordOffset n hn i hi).2, hs]; omega)
  ⟨lo.toUInt64 ||| (high.toUInt64 <<< 32)⟩
/-- Machine-size reads recover the canonical packed word. -/
theorem readWord_eq (buffer : Packed.Buffer n) (i : USize) (hi : i.toNat < n)
    (hn : 8 * n < USize.size) :
    readWord buffer i hi hn = Packed.read buffer ⟨i.toNat, hi⟩ := by
  simp only [readWord, Packed.read, Packed.get, ByteArray.ugetUInt32LE,
    ByteArray.getUInt32LE, (wordOffset n hn i hi).1, (wordOffset n hn i hi).2]

/-- Store a word with two bounded native stores, preserving the fixed buffer size. -/
@[inline] def writeWord (buffer : Packed.Buffer n) (i : USize) (hi : i.toNat < n)
    (hn : 8 * n < USize.size) (value : Word) : Packed.Buffer n :=
  let off := i * 8
  have hs : buffer.val.bytes.size = 8 * n := by rw [buffer.val.byteSize, buffer.property]
  let first := buffer.val.bytes.usetUInt32LE off value.val.toUInt32 (by
    rw [(wordOffset n hn i hi).1, hs]; omega)
  let second := first.usetUInt32LE (off + 4) (value.val >>> 32).toUInt32 (by
    rw [ByteArray.size_usetUInt32LE, (wordOffset n hn i hi).2, hs]; omega)
  ⟨⟨n, second, by simp only [second, first, ByteArray.size_usetUInt32LE, hs]⟩, rfl⟩
/-- Native stores have exactly the canonical packed-buffer update. -/
theorem writeWord_eq (buffer : Packed.Buffer n) (i : USize) (hi : i.toNat < n)
    (hn : 8 * n < USize.size) (value : Word) :
    writeWord buffer i hi hn value = Packed.write buffer ⟨i.toNat, hi⟩ value := by
  rcases buffer with ⟨⟨n', bytes, hs⟩, hb⟩
  change n' = n at hb
  subst n'
  simp only [writeWord, Packed.write, Packed.set, ByteArray.usetUInt32LE,
    (wordOffset n hn i hi).1, (wordOffset n hn i hi).2]

/-- Fill fixed-size packed storage while specializing the coordinate function. -/
@[specialize] def fillWords (n : Nat) (hn : 8 * n < USize.size) (f : Fin n → Word) : Packed.Buffer n :=
  (List.finRange n).foldl (fun buffer i =>
    writeWord buffer i.val.toUSize (by
      rw [USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)]
      exact i.isLt) hn (f i)) ⟨Packed.zeros n, rfl⟩
/-- Machine-size packed construction equals the canonical coordinate buffer. -/
theorem fillWords_eq (n : Nat) (hn : 8 * n < USize.size) (f : Fin n → Word) :
    fillWords n hn f = Packed.ofFn n f := by
  have h (i : Fin n) : i.val.toUSize.toNat = i.val :=
    USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)
  simp only [fillWords, writeWord_eq, h, Packed.ofFn]
/-- Fill a word buffer with a specialized machine-indexed coordinate function. -/
@[specialize] def fillWordLoop (n : Nat) (hn : 8 * n < USize.size)
    (limit : USize) (hl : limit.toNat = n) (f : (i : USize) → i.toNat < n → Word)
    (i : USize) (buffer : Packed.Buffer n) : Packed.Buffer n :=
  if hi : i < limit then
    have hib : i.toNat < n := by rw [USize.lt_iff_toNat_lt, hl] at hi; exact hi
    fillWordLoop n hn limit hl f (i + 1) (writeWord buffer i hib hn (f i hib))
  else buffer
termination_by n - i.toNat
decreasing_by rw [index_successor limit i hi]; rw [USize.lt_iff_toNat_lt, hl] at hi; omega
/-- The word fill loop is the canonical ordered fold over its remaining coordinates. -/
theorem fillWordLoop_eq (n : Nat) (hn : 8 * n < USize.size)
    (limit : USize) (hl : limit.toNat = n) (f : (i : USize) → i.toNat < n → Word)
    (i : USize) (buffer : Packed.Buffer n) :
    fillWordLoop n hn limit hl f i buffer =
      ((List.finRange n).drop i.toNat).foldl (fun buffer j =>
        writeWord buffer j.val.toUSize (by
          rw [USize.toNat_ofNat_of_lt' (by have := j.isLt; omega)]; exact j.isLt) hn
          (f j.val.toUSize (by
            rw [USize.toNat_ofNat_of_lt' (by have := j.isLt; omega)]; exact j.isLt))) buffer := by
  fun_induction fillWordLoop n hn limit hl f i buffer with
  | case1 i buffer hi hib ih =>
    rw [List.drop_eq_getElem_cons (by simpa only [List.length_finRange] using hib), List.foldl_cons]
    simp only [List.getElem_finRange, Fin.val_cast, Nat.toUSize, USize.ofNat_toNat]
    rw [ih, index_successor limit i hi]
  | case2 i buffer hi =>
    have hb : (List.finRange n).length ≤ i.toNat := by
      rw [List.length_finRange]
      rw [USize.lt_iff_toNat_lt, hl] at hi
      omega
    rw [List.drop_eq_nil_of_le hb, List.foldl_nil]
/-- Materialize a complete packed word buffer using native indices. -/
@[specialize] def fillWordBuffer (n : Nat) (hn : 8 * n < USize.size)
    (f : (i : USize) → i.toNat < n → Word) : Packed.Buffer n :=
  fillWordLoop n hn n.toUSize (USize.toNat_ofNat_of_lt' (by omega)) f 0 ⟨Packed.zeros n, rfl⟩
/-- Machine-indexed construction agrees exactly with the canonical packed coordinate buffer. -/
theorem fillWordBuffer_eq (n : Nat) (hn : 8 * n < USize.size)
    (f : (i : USize) → i.toNat < n → Word) :
    fillWordBuffer n hn f = Packed.ofFn n (fun i =>
      f i.val.toUSize (by rw [USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)]; exact i.isLt)) := by
  rw [fillWordBuffer, fillWordLoop_eq]
  simp only [show (0 : USize).toNat = 0 from rfl, List.drop_zero]
  rw [← fillWords_eq n hn]
  rfl

end CompStark.Sumcheck
