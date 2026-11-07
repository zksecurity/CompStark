/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sumcheck.Preparation
public import CompPoly.Fields.Binary.BF64.WordExt3Proofs

/-! Shared-challenge folds of interleaved cubic-extension tables. The width is the
number of adjacent columns in each row; a high-variable fold uses one pair of rows.
Prepared byte maps are shared by every column and row of a round. -/

@[expose] public section
namespace CompStark.Sumcheck
set_option maxRecDepth 4096
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
open BF64

/-- Six-map Karatsuba multiplication for a fixed cubic-extension multiplier. -/
@[inline] def multiplyMaps (c0 c1 c2 c01 c02 c12 : Word.ByteMap) (a : WordExt3) : WordExt3 :=
  let p0 := mapMul c0 a.c0
  let p1 := mapMul c1 a.c1
  let p2 := mapMul c2 a.c2
  let p01 := Word.add (Word.add (mapMul c01 (Word.add a.c0 a.c1)) p0) p1
  let p02 := Word.add (Word.add (mapMul c02 (Word.add a.c0 a.c2)) p0) p2
  let p12 := Word.add (Word.add (mapMul c12 (Word.add a.c1 a.c2)) p1) p2
  ⟨Word.add p0 p12, Word.add (Word.add p01 p12) p2,
    Word.add (Word.add p02 p1) p2⟩

/-- Certified six-map multiplication by a shared cubic-extension scalar. -/
structure Prepared where
  /-- The common multiplier represented by the maps. -/
  scalar : WordExt3
  /-- Constant-coordinate multiplier. -/
  c0 : Word.ByteMap
  /-- Linear-coordinate multiplier. -/
  c1 : Word.ByteMap
  /-- Quadratic-coordinate multiplier. -/
  c2 : Word.ByteMap
  /-- Constant-plus-linear Karatsuba multiplier. -/
  c01 : Word.ByteMap
  /-- Constant-plus-quadratic Karatsuba multiplier. -/
  c02 : Word.ByteMap
  /-- Linear-plus-quadratic Karatsuba multiplier. -/
  c12 : Word.ByteMap
  /-- Every lookup product is multiplication by the represented scalar. -/
  correct : ∀ a, multiplyMaps c0 c1 c2 c01 c02 c12 a = WordExt3.mul scalar a

/-- Prepare a challenge once, independently of the table shape. -/
def prepare (r : WordExt3) : Prepared :=
  ⟨r, byteMap r.c0, byteMap r.c1, byteMap r.c2,
    byteMap (Word.add r.c0 r.c1), byteMap (Word.add r.c0 r.c2),
    byteMap (Word.add r.c1 r.c2), by
      intro a
      have hm (x y : Word) : (Word.ByteMap.ofScalar x).mul y = Word.mulMasked x y := by
        apply Word.toField_injective
        rw [Word.ByteMap.toField_mul, Word.toField_mulMasked]
      simp only [multiplyMaps, byteMap_eq, mapMul_eq, WordExt3.mul, hm]⟩

/-- Multiply by the prepared challenge, using six lookup products. -/
@[inline] def Prepared.mul (r : Prepared) (a : WordExt3) : WordExt3 :=
  multiplyMaps r.c0 r.c1 r.c2 r.c01 r.c02 r.c12 a

/-- Every certified prepared multiplier agrees with its represented scalar. -/
theorem Prepared.mul_correct (r : Prepared) (a : WordExt3) :
    r.mul a = WordExt3.mul r.scalar a := r.correct a

/-- Prepared multiplication agrees with the word extension kernel. -/
theorem prepared_mul_eq (r a : WordExt3) : (prepare r).mul a = WordExt3.mul r a :=
  (prepare r).mul_correct a

/-- Prepared multiplication refines the specification extension field. -/
@[simp] theorem toField_prepared_mul (r a : WordExt3) :
    ((prepare r).mul a).toField = r.toField * a.toField := by
  rw [prepared_mul_eq, WordExt3.toField_mul]

/-- Characteristic-two interpolation with a shared prepared challenge. -/
@[inline] def Prepared.interpolate (r : Prepared) (a b : WordExt3) : WordExt3 :=
  WordExt3.add a (r.mul (WordExt3.add a b))

/-- Equal endpoints have zero slope and need no prepared-map loads. -/
@[inline] def Prepared.interpolateShared (r : Prepared) (a b : WordExt3) : WordExt3 :=
  let slope := WordExt3.add a b
  let product := if slope.c0.val == 0 && slope.c1.val == 0 && slope.c2.val == 0 then
    (⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩ : WordExt3) else r.mul slope
  WordExt3.add a product

/-- Skipping zero slopes preserves interpolation for every certified prepared multiplier. -/
theorem Prepared.interpolateShared_eq (r : Prepared) (a b : WordExt3) :
    r.interpolateShared a b = r.interpolate a b := by
  unfold interpolateShared
  dsimp only
  split
  · rename_i h
    have same : WordExt3.add a b = ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩ := by
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      generalize WordExt3.add a b = slope at h ⊢
      rcases slope with ⟨⟨a0⟩, ⟨a1⟩, ⟨a2⟩⟩
      rcases h with ⟨⟨h0, h1⟩, h2⟩
      cases h0; cases h1; cases h2
      rfl
    apply WordExt3.toField_injective
    simp only [interpolate, same, WordExt3.toField_add, r.mul_correct,
      WordExt3.toField_mul]
    change _ = _ + _ * 0
    rw [mul_zero]
    rfl
  · rfl

/-- Native shared-challenge interpolation skips every equal endpoint pair. -/
@[csimp] theorem Prepared.interpolate_code : @Prepared.interpolate = @Prepared.interpolateShared := by
  funext r a b
  exact (r.interpolateShared_eq a b).symm

/-- Word interpolation is the affine line through its two endpoints. -/
@[simp] theorem toField_interpolate (r a b : WordExt3) :
    ((prepare r).interpolate a b).toField =
      (1 - r.toField) * a.toField + r.toField * b.toField := by
  simp only [Prepared.interpolate, WordExt3.toField_add, toField_prepared_mul]
  rw [CharTwo.sub_eq_add]
  ring

/-- Both source coordinates of an interleaved pair lie in the input table. -/
theorem pairIndex_lt (rows width : Nat) (i : Fin (rows * width)) :
    2 * (i.val / width) * width + i.val % width < 2 * rows * width ∧
      (2 * (i.val / width) + 1) * width + i.val % width < 2 * rows * width := by
  have hw : 0 < width := by have := i.isLt; nlinarith
  have hq : i.val / width < rows := (Nat.div_lt_iff_lt_mul hw).mpr i.isLt
  have hm := Nat.mod_lt i.val hw
  have hmul := Nat.mul_le_mul_right width (show i.val / width + 1 ≤ rows by omega)
  constructor <;> nlinarith

/-- Fold adjacent pairs of rows, preserving the columns within each row. -/
def fold (r : Prepared) (rows width : Nat) (table : Vector WordExt3 (2 * rows * width)) :
    Vector WordExt3 (rows * width) :=
  Vector.ofFn fun i =>
    r.interpolate
      (table[2 * (i.val / width) * width + i.val % width]'(pairIndex_lt rows width i).1)
      (table[(2 * (i.val / width) + 1) * width + i.val % width]'(pairIndex_lt rows width i).2)

/-- Every folded coordinate is precisely the specification affine restriction. -/
theorem fold_refines (r : WordExt3) (rows width : Nat)
    (table : Vector WordExt3 (2 * rows * width)) (i : Fin (rows * width)) :
    ((fold (prepare r) rows width table)[i]).toField =
      (1 - r.toField) *
        (table[2 * (i.val / width) * width + i.val % width]'(pairIndex_lt rows width i).1).toField +
        r.toField *
          (table[(2 * (i.val / width) + 1) * width + i.val % width]'(pairIndex_lt rows width i).2).toField := by
  simp only [fold, Fin.getElem_fin, Vector.getElem_ofFn, toField_interpolate]

end CompStark.Sumcheck
