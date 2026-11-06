/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Sumcheck.Fold
public import CompStark.Sumcheck.Buffer
@[expose] public section
namespace CompStark.Sumcheck
set_option backward.isDefEq.respectTransparency false
open BF64
/-- Contiguous coordinate planes of a fixed-length cubic-extension table. -/
structure PackedScalars (n : Nat) where
  /-- Constant-coordinate words. -/
  c0 : Packed.Buffer n
  /-- Linear-coordinate words. -/
  c1 : Packed.Buffer n
  /-- Quadratic-coordinate words. -/
  c2 : Packed.Buffer n
/-- Allocate zeroed coordinate planes. -/
def PackedScalars.zeros (n : Nat) : PackedScalars n :=
  ⟨⟨Packed.zeros n, rfl⟩, ⟨Packed.zeros n, rfl⟩, ⟨Packed.zeros n, rfl⟩⟩
/-- Read one extension scalar using machine-size indices. -/
@[inline] def PackedScalars.read (table : PackedScalars n) (i : USize) (hi : i.toNat < n)
    (hn : 8 * n < USize.size) : WordExt3 :=
  ⟨readWord table.c0 i hi hn, readWord table.c1 i hi hn, readWord table.c2 i hi hn⟩
/-- Read a scalar with an explicit padding value outside the stored prefix. -/
@[inline] def PackedScalars.getD (table : PackedScalars n) (hn : 8 * n < USize.size)
    (i : USize) (padding : WordExt3) : WordExt3 :=
  if hi : i < n.toUSize then
    table.read i (by
      rw [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt' (by omega)] at hi
      exact hi) hn
  else padding
/-- Store one extension scalar in its three coordinate planes. -/
@[inline] def PackedScalars.write (table : PackedScalars n) (i : USize) (hi : i.toNat < n)
    (hn : 8 * n < USize.size) (value : WordExt3) : PackedScalars n :=
  ⟨writeWord table.c0 i hi hn value.c0, writeWord table.c1 i hi hn value.c1,
    writeWord table.c2 i hi hn value.c2⟩
/-- A packed extension update changes exactly its indexed scalar. -/
theorem PackedScalars.read_write (table : PackedScalars n) (i j : USize) (hi : i.toNat < n)
    (hj : j.toNat < n) (hn : 8 * n < USize.size) (value : WordExt3) :
    (table.write i hi hn value).read j hj hn = if i = j then value else table.read j hj hn := by
  have he : (⟨i.toNat, hi⟩ : Fin n) = ⟨j.toNat, hj⟩ ↔ i = j := by
    simp only [Fin.ext_iff, USize.toNat_inj]
  simp only [PackedScalars.read, PackedScalars.write, readWord_eq, writeWord_eq,
    Packed.read_write, he]
  split_ifs <;> rfl
/-- A machine-size successor below an addressable limit cannot wrap. -/
theorem successor_nat (n : Nat) (hn : 8 * n < USize.size) (i : USize) (hi : i.toNat < n) :
    (i + 1).toNat = i.toNat + 1 := by
  have hs : 2 ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, show (1 : USize).toNat = 1 from
    USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size), hs,
    Nat.mod_eq_of_lt (by omega)]
/-- Fill packed scalar planes with an entirely machine-indexed native loop. -/
@[specialize] def fillScalarsLoop (n : Nat) (hn : 8 * n < USize.size)
    (limit : USize) (hl : limit.toNat = n) (f : (i : USize) → i.toNat < n → WordExt3)
    (i : USize) (table : PackedScalars n) : PackedScalars n :=
  if hi : i < limit then
    have hib : i.toNat < n := by rw [USize.lt_iff_toNat_lt, hl] at hi; exact hi
    fillScalarsLoop n hn limit hl f (i + 1) (table.write i hib hn (f i hib))
  else table
termination_by n - i.toNat
decreasing_by rw [successor_nat n hn i hib]; omega
/-- Readback of the complete packed fill loop, including its already-filled prefix. -/
theorem fillScalarsLoop_read (n : Nat) (hn : 8 * n < USize.size) (limit : USize)
    (hl : limit.toNat = n) (f : (i : USize) → i.toNat < n → WordExt3)
    (i j : USize) (hj : j.toNat < n) (table : PackedScalars n) :
    (fillScalarsLoop n hn limit hl f i table).read j hj hn =
      if i.toNat ≤ j.toNat then f j hj else table.read j hj hn := by
  fun_induction fillScalarsLoop n hn limit hl f i table with
  | case1 i table hi hib ih =>
    rw [ih, successor_nat n hn i hib, PackedScalars.read_write]
    by_cases h : i = j
    · subst j
      simp only [Nat.not_succ_le_self, ↓reduceIte, le_refl]
    · have hne : i.toNat ≠ j.toNat := fun he => h (USize.toNat_inj.mp he)
      simp only [h, ↓reduceIte]
      split_ifs <;> first | rfl | omega
  | case2 i table hi =>
    have hle : n ≤ i.toNat := by
      rw [USize.lt_iff_toNat_lt, hl] at hi
      omega
    simp only [show ¬i.toNat ≤ j.toNat by omega, ↓reduceIte]
/-- Materialize a scalar coordinate function into packed planes. -/
@[specialize] def fillScalars (n : Nat) (hn : 8 * n < USize.size)
    (f : (i : USize) → i.toNat < n → WordExt3) : PackedScalars n :=
  fillScalarsLoop n hn n.toUSize (USize.toNat_ofNat_of_lt' (by omega)) f 0 (PackedScalars.zeros n)
/-- Every scalar read from the complete fill is the defining scalar. -/
theorem fillScalars_read (n : Nat) (hn : 8 * n < USize.size)
    (f : (i : USize) → i.toNat < n → WordExt3) (i : USize) (hi : i.toNat < n) :
    (fillScalars n hn f).read i hi hn = f i hi := by
  rw [fillScalars, fillScalarsLoop_read]
  simp only [show (0 : USize).toNat = 0 from rfl, Nat.zero_le, ↓reduceIte]
/-- Copy an existing scalar array into contiguous coordinate planes. -/
def PackedScalars.ofArray (values : Array WordExt3) (hn : 8 * values.size < USize.size) :
    PackedScalars values.size :=
  fillScalars values.size hn fun i hi => values.uget i hi
/-- Packing an array preserves every scalar exactly. -/
theorem PackedScalars.read_ofArray (values : Array WordExt3) (hn : 8 * values.size < USize.size)
    (i : USize) (hi : i.toNat < values.size) :
    (PackedScalars.ofArray values hn).read i hi hn = values[i.toNat] := by
  rw [PackedScalars.ofArray, fillScalars_read]
  rfl
/-- Expose a packed scalar table in logical coordinate order. -/
def PackedScalars.toArray (values : PackedScalars n) (hn : 8 * n < USize.size) : Array WordExt3 :=
  Array.ofFn fun i : Fin n => values.read i.val.toUSize (by
    rw [USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)]; exact i.isLt) hn
/-- Unpacking has the declared scalar-table length. -/
@[simp] theorem PackedScalars.size_toArray (values : PackedScalars n) (hn : 8 * n < USize.size) :
    (values.toArray hn).size = n := Array.size_ofFn
/-- Every array coordinate is precisely the corresponding machine-indexed packed read. -/
theorem PackedScalars.getElem_toArray (values : PackedScalars n) (hn : 8 * n < USize.size)
    (i : USize) (hi : i.toNat < n) :
    (values.toArray hn)[i.toNat]'(by simpa only [PackedScalars.size_toArray] using hi) =
      values.read i hi hn := by
  simp only [PackedScalars.toArray, Array.getElem_ofFn, USize.ofNat_toNat]
/-- Padded machine reads have exactly the logical array's optional-index semantics. -/
theorem PackedScalars.getD_eq (table : PackedScalars n) (hn : 8 * n < USize.size)
    (i : USize) (padding : WordExt3) :
    table.getD hn i padding = ((table.toArray hn)[i.toNat]?).getD padding := by
  have hsize : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' (by omega)
  unfold PackedScalars.getD
  split
  · rename_i hi
    have hib : i.toNat < n := by rw [USize.lt_iff_toNat_lt, hsize] at hi; exact hi
    rw [Array.getElem?_eq_getElem (by simpa only [PackedScalars.size_toArray] using hib)]
    exact (PackedScalars.getElem_toArray table hn i hib).symm
  · rename_i hi
    have hib : n ≤ i.toNat := by rw [USize.lt_iff_toNat_lt, hsize] at hi; omega
    rw [Array.getElem?_eq_none (by simpa only [PackedScalars.size_toArray] using hib)]
    rfl

/-- The complete packed-array round trip is exact, including empty arrays. -/
theorem PackedScalars.toArray_ofArray (values : Array WordExt3) (hn : 8 * values.size < USize.size) :
    (PackedScalars.ofArray values hn).toArray hn = values := by
  apply Array.ext
  · exact PackedScalars.size_toArray ..
  · intro i hi hj
    have hu : i.toUSize.toNat = i := USize.toNat_ofNat_of_lt' (by omega)
    have huj : i.toUSize.toNat < values.size := by rw [hu]; exact hj
    simpa only [hu] using (PackedScalars.getElem_toArray (PackedScalars.ofArray values hn) hn i.toUSize huj).trans
      (PackedScalars.read_ofArray values hn i.toUSize huj)

/-- The low and high source indices of an interleaved fold pair use exact machine arithmetic. -/
theorem packedPairIndices (rows width n : Nat) (hn : 8 * n < USize.size)
    (hp : 2 * rows * width ≤ n) (i : USize) (hi : i.toNat < rows * width) :
    (2 * i - i % width.toUSize).toNat = 2 * (i.toNat / width) * width + i.toNat % width ∧
      (2 * i - i % width.toUSize + width.toUSize).toNat =
        (2 * (i.toNat / width) + 1) * width + i.toNat % width := by
  have hw : 0 < width := by
    by_contra hz
    have he : width = 0 := by omega
    simp only [he, Nat.mul_zero] at hi
    omega
  have hr : 0 < rows := by
    by_contra hz
    have he : rows = 0 := by omega
    simp only [he, Nat.zero_mul] at hi
    omega
  have hwidth : width ≤ rows * width := by exact Nat.le_mul_of_pos_left width hr
  have hu : width.toUSize.toNat = width := USize.toNat_ofNat_of_lt' (by nlinarith)
  have hs : 2 ^ System.Platform.numBits = USize.size := rfl
  have h2 : (2 : USize).toNat = 2 := USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)
  have htwice : (2 * i).toNat = 2 * i.toNat := by
    rw [USize.toNat_mul, h2, hs, Nat.mod_eq_of_lt (by nlinarith)]
  have hmod : (i % width.toUSize).toNat = i.toNat % width := by rw [USize.toNat_mod, hu]
  have hle : i % width.toUSize ≤ 2 * i := by
    rw [USize.le_iff_toNat_le, htwice, hmod]
    have := Nat.mod_le i.toNat width
    omega
  have hlo : (2 * i - i % width.toUSize).toNat = 2 * i.toNat - i.toNat % width := by
    rw [USize.toNat_sub_of_le _ _ hle, htwice, hmod]
  have hpairs := pairIndex_lt rows width ⟨i.toNat, hi⟩
  dsimp only at hpairs
  have hm := Nat.mod_add_div i.toNat width
  have he : 2 * i.toNat - i.toNat % width =
      2 * (i.toNat / width) * width + i.toNat % width := by
    have heq : 2 * (i.toNat / width) * width = 2 * (width * (i.toNat / width)) := by ring
    rw [heq]
    omega
  refine ⟨hlo.trans he, ?_⟩
  rw [USize.toNat_add, hlo, hu, hs, Nat.mod_eq_of_lt (by nlinarith [hpairs.2])]
  nlinarith
/-- Fold an interleaved scalar prefix into packed coordinate planes. -/
def foldPacked (r : Prepared) (rows width n : Nat) (table : PackedScalars n)
    (hn : 8 * n < USize.size) (hp : 2 * rows * width ≤ n) : PackedScalars (rows * width) :=
  fillScalars (rows * width) (by nlinarith [hp]) fun i hi =>
    let low := 2 * i - i % width.toUSize
    let high := low + width.toUSize
    have bounds := pairIndex_lt rows width ⟨i.toNat, hi⟩
    r.interpolate
      (table.read low (by rw [(packedPairIndices rows width n hn hp i hi).1]; dsimp only at *; omega) hn)
      (table.read high (by rw [(packedPairIndices rows width n hn hp i hi).2]; dsimp only at *; omega) hn)
/-- Every packed fold coordinate is the exact prepared affine restriction of the source pair. -/
theorem foldPacked_read (r : Prepared) (rows width n : Nat) (table : PackedScalars n)
    (hn : 8 * n < USize.size) (hp : 2 * rows * width ≤ n) (i : USize) (hi : i.toNat < rows * width) :
    (foldPacked r rows width n table hn hp).read i hi (by nlinarith [hp]) =
      r.interpolate
        (table.read (2 * i - i % width.toUSize)
          (by have := pairIndex_lt rows width ⟨i.toNat, hi⟩; rw [(packedPairIndices rows width n hn hp i hi).1]; dsimp only at *; omega) hn)
        (table.read (2 * i - i % width.toUSize + width.toUSize)
          (by have := pairIndex_lt rows width ⟨i.toNat, hi⟩; rw [(packedPairIndices rows width n hn hp i hi).2]; dsimp only at *; omega) hn) := by
  rw [foldPacked, fillScalars_read]

/-- Unpacking a packed fold gives exactly the scalar-array fold on the consumed prefix. -/
theorem foldPacked_toArray (r : Prepared) (rows width n : Nat) (table : PackedScalars n)
    (hn : 8 * n < USize.size) (hp : 2 * rows * width ≤ n) :
    (foldPacked r rows width n table hn hp).toArray (by nlinarith [hp]) =
      (fold r rows width (Vector.ofFn fun i => (table.toArray hn)[i.val]!)).toArray := by
  apply Array.ext
  · simp only [PackedScalars.size_toArray, Vector.size_toArray]
  · intro i hi hj
    have hib : i < rows * width := by simpa only [PackedScalars.size_toArray] using hi
    have hu : i.toUSize.toNat = i := USize.toNat_ofNat_of_lt' (by nlinarith [hp])
    have hiu : i.toUSize.toNat < rows * width := by rw [hu]; exact hib
    have indices := packedPairIndices rows width n hn hp i.toUSize hiu
    have hr := PackedScalars.getElem_toArray (foldPacked r rows width n table hn hp)
      (by nlinarith [hp]) i.toUSize hiu
    simp only [hu] at hr
    rw [hr, foldPacked_read]
    simp only [fold, Vector.getElem_toArray, Vector.getElem_ofFn]
    congr 1
    · rw [← PackedScalars.getElem_toArray, getElem!_pos _ _ (by
        simp only [PackedScalars.size_toArray]; have hpair := pairIndex_lt rows width ⟨i, hib⟩; dsimp only at hpair; omega)]
      simp only [indices.1, hu]
    · rw [← PackedScalars.getElem_toArray, getElem!_pos _ _ (by
        simp only [PackedScalars.size_toArray]; have hpair := pairIndex_lt rows width ⟨i, hib⟩; dsimp only at hpair; omega)]
      simp only [indices.2, hu]

/-- The packed implementation refines affine restriction in the specification extension field. -/
theorem foldPacked_refines (r : WordExt3) (rows width n : Nat) (table : PackedScalars n)
    (hn : 8 * n < USize.size) (hp : 2 * rows * width ≤ n) (i : USize) (hi : i.toNat < rows * width) :
    ((foldPacked (prepare r) rows width n table hn hp).read i hi (by nlinarith [hp])).toField =
      (1 - r.toField) *
        (table.read (2 * i - i % width.toUSize)
          (by have := pairIndex_lt rows width ⟨i.toNat, hi⟩; rw [(packedPairIndices rows width n hn hp i hi).1]; dsimp only at *; omega) hn).toField +
      r.toField *
        (table.read (2 * i - i % width.toUSize + width.toUSize)
          (by have := pairIndex_lt rows width ⟨i.toNat, hi⟩; rw [(packedPairIndices rows width n hn hp i hi).2]; dsimp only at *; omega) hn).toField := by
  rw [foldPacked_read, toField_interpolate]

end CompStark.Sumcheck
