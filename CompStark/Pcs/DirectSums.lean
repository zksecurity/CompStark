/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.NativeRound
public import CompStark.Sumcheck.WordProductProofs
public import CompStark.Pcs.BasisColumn

/-! Specialized extension-coordinate accumulators for sumcheck messages and final Basis lifting. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Specialize zero and unit base factors before entering mixed multiplication. -/
@[inline] def roundBaseProduct (a : Word) (b : WordExt3) : WordExt3 :=
  if a.val = 0 then 0 else if a.val = 1 then b else WordExt3.mulScalar b a

/-- Return the concrete word zero without constructing a field-equivalence value. -/
@[inline] def roundBaseProductScalar (a : Word) (b : WordExt3) : WordExt3 :=
  if a.val = 0 then ⟨⟨0⟩,⟨0⟩,⟨0⟩⟩ else if a.val = 1 then b else WordExt3.mulScalar b a

/-- Concrete zero dispatch preserves the complete mixed product. -/
@[csimp] theorem roundBaseProduct_code : roundBaseProduct = roundBaseProductScalar := by
  rfl

/-- Base-factor specialization retains the complete mixed product. -/
theorem roundBaseProduct_eq (a : Word) (b : WordExt3) :
    roundBaseProduct a b = WordExt3.mulScalar b a := by
  unfold roundBaseProduct
  split
  · rename_i h
    have ha : a = ⟨0⟩ := by cases a; exact congrArg Word.mk h
    rw [ha]
    apply WordExt3.toField_injective
    rw [WordExt3.toField_mulScalar]
    change (0 : BF64.Ext3) = (0 : BF64) • b.toField
    exact (zero_smul _ _).symm
  · split
    · rename_i h
      have ha : a = ⟨1⟩ := by cases a; exact congrArg Word.mk h
      rw [ha]
      apply WordExt3.toField_injective
      rw [WordExt3.toField_mulScalar]
      change b.toField = (1 : BF64) • b.toField
      exact (one_smul _ _).symm
    · rfl

/-- Specialize base factors and use five base products for full extension factors. -/
@[inline] def roundProduct (a b : WordExt3) : WordExt3 :=
  if a.c1.val = 0 ∧ a.c2.val = 0 then roundBaseProduct a.c0 b
  else if b.c1.val = 0 ∧ b.c2.val = 0 then roundBaseProduct b.c0 a
  else Sumcheck.extMulFive a b

/-- Shape-directed message multiplication equals the reference extension product. -/
theorem roundProduct_eq (a b : WordExt3) : roundProduct a b = WordExt3.mul a b := by
  have baseValue (a : WordExt3) (h : a.c1.val = 0 ∧ a.c2.val = 0) :
      a.toField = (algebraMap BF64 BF64.Ext3) a.c0.toField := by
    rcases a with ⟨a0, ⟨a1⟩, ⟨a2⟩⟩
    rcases h with ⟨h1,h2⟩
    dsimp only at h1 h2
    subst a1; subst a2
    rfl
  unfold roundProduct
  split
  · rename_i h
    rw [roundBaseProduct_eq]
    apply WordExt3.toField_injective
    rw [WordExt3.toField_mulScalar, Algebra.smul_def, WordExt3.toField_mul, baseValue a h]
  · split
    · rename_i h
      rw [roundBaseProduct_eq]
      apply WordExt3.toField_injective
      rw [WordExt3.toField_mulScalar, Algebra.smul_def, WordExt3.toField_mul, baseValue b h]
      exact mul_comm _ _
    · exact Sumcheck.extMulFive_eq a b

/-- Accumulate extension coordinates without retaining a list of product records. -/
@[specialize] def sumExtLoop (count : Nat) (f : Fin count → WordExt3)
    (left : Nat) (bound : left ≤ count) (a b c : UInt64) : WordExt3 :=
  match left with
  | 0 => ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩
  | left+1 =>
    let v := f ⟨left, by omega⟩
    sumExtLoop count f left (by omega) (a ^^^ v.c0.val) (b ^^^ v.c1.val) (c ^^^ v.c2.val)
termination_by structural left

/-- The three native accumulators retain exactly the remaining finite extension sum. -/
theorem sumExtLoop_refines (count : Nat) (f : Fin count → WordExt3)
    (left : Nat) (bound : left ≤ count) (a b c : UInt64) :
    (sumExtLoop count f left bound a b c).toField =
      (⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ : WordExt3).toField + ∑ i : Fin left, (f ⟨i.val, by omega⟩).toField := by
  induction left generalizing a b c with
  | zero =>
    rw [sumExtLoop]
    simp only [Fin.sum_univ_zero, add_zero]
  | succ left ih =>
    rw [sumExtLoop, ih, Fin.sum_univ_castSucc]
    change (WordExt3.add ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ (f ⟨left, by omega⟩)).toField + _ = _
    rw [WordExt3.toField_add]
    ac_rfl

/-- Sum one complete finite family with three native coordinate accumulators. -/
@[inline] def sumExt (count : Nat) (f : Fin count → WordExt3) : WordExt3 :=
  sumExtLoop count f count (Nat.le_refl _) 0 0 0

/-- The direct sum is exactly the existing certified word-list accumulation. -/
theorem sumExt_eq (count : Nat) (f : Fin count → WordExt3) :
    sumExt count f = sumWords (List.ofFn f) := by
  apply WordExt3.toField_injective
  rw [sumExt, sumExtLoop_refines]
  change 0 + (∑ i : Fin count, (f i).toField) = _
  simp only [zero_add, sumWords_refines, List.map_ofFn, Function.comp_apply, List.sum_ofFn]

/-- Project compact point windows directly into three native coordinate accumulators. -/
def BasisWindow.projectAtDirect {cols : Nat} (w : BasisWindow cols) (f : Fin cols → Word) : WordExt3 :=
  sumExt w.count fun i => WordExt3.mulScalar w.values[i]
    (f ⟨w.start+i.val, by have := i.isLt; have := w.fits; omega⟩)

/-- Direct compact point projections preserve their exact weighted sums. -/
@[csimp] theorem BasisWindow.projectAt_code : @BasisWindow.projectAt = @BasisWindow.projectAtDirect := by
  funext cols w f
  unfold BasisWindow.projectAt BasisWindow.projectAtDirect
  rw [sumExt_eq]

/-- Author both quadratic message coefficients with direct coordinate accumulation. -/
def roundCoefficientsDirect (rows width : Nat) (table weights : Vector WordExt3 (2*rows*width)) :
    Vector WordExt3 2 :=
  let low := roundLow rows width
  let high := roundHigh rows width
  #v[sumExt (rows*width) (fun i => roundProduct table[low i] weights[low i]),
    sumExt (rows*width) (fun i => roundProduct (WordExt3.add table[low i] table[high i])
      (WordExt3.add weights[low i] weights[high i]))]

/-- Direct message accumulation preserves both exact native quadratic coefficients. -/
@[csimp] theorem roundCoefficients_code : @roundCoefficients = @roundCoefficientsDirect := by
  funext rows width table weights
  unfold roundCoefficients roundCoefficientsDirect
  dsimp only
  simp only [roundProduct_eq, sumExt_eq]

/-- Lift compact point and binary factors without allocating their complete product list. -/
def liftColumnsDirect (cols terms : Nat) (a : Vector WordExt3 terms)
    (columns : Vector (BasisColumn cols) terms) : Vector WordExt3 cols :=
  Vector.ofFn fun i => sumExt terms (fun t => columns[t].scaleAt a[t] i)

/-- Direct compact reconstruction retains every final Basis weight coordinate. -/
@[csimp] theorem liftColumns_code : @liftColumns = @liftColumnsDirect := by
  funext cols terms a columns
  unfold liftColumns liftColumnsDirect
  simp only [sumExt_eq]

/-- Read one of the twenty-four physical bytes of an extension word. -/
@[inline] def coordinateByte (a : WordExt3) (byte : Fin 24) : UInt8 :=
  ((mapLimb a ⟨byte.val/8, by omega⟩).val >>> (8*(byte.val%8)).toUInt64).toUInt8

/-- A selected physical byte retains exactly its eight polynomial-basis bits. -/
theorem coordinateByte_bit (a : WordExt3) (byte : Fin 24) (bit : Fin 8) :
    (coordinateByte a byte).toNat.testBit bit.val =
      packedBit (mapLimb a ⟨(8*byte.val+bit.val)/64, by omega⟩).val
        ⟨(8*byte.val+bit.val)%64, by omega⟩ := by
  have quotient : (8*byte.val+bit.val)/64 = byte.val/8 := by omega
  have remainder : (8*byte.val+bit.val)%64 = 8*(byte.val%8)+bit.val := by omega
  rw [packedBit_eq]
  change _ = (mapLimb a ⟨(8*byte.val+bit.val)/64, _⟩).val.toNat.testBit _
  simp only [coordinateByte, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.toUInt64, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, bit.isLt, decide_true, Bool.true_and,
    quotient, remainder]
  have shift : 8*(byte.val%8) < 64 := by omega
  rw [Nat.mod_eq_of_lt (show 8*(byte.val%8) < 2^64 by omega), Nat.mod_eq_of_lt shift,
    Nat.testBit_shiftRight]

/-- Tabulate the images of all possible bytes at each physical byte position. -/
def prepareCoordinates (weights : Vector WordExt3 192) : Vector (Vector WordExt3 256) 24 :=
  Vector.ofFn fun byte => Vector.ofFn fun digit => sumExt 8 fun bit =>
    if digit.val.testBit bit.val then weights[8*byte.val+bit.val] else ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

/-- Apply a shared binary-linear map with twenty-four byte-table reads. -/
def applyCoordinateBytes (tables : Vector (Vector WordExt3 256) 24) (a : WordExt3) : WordExt3 :=
  sumExt 24 fun byte => tables[byte][(coordinateByte a byte).toNat]'(coordinateByte a byte).toNat_lt

/-- Prepared byte application equals every selected binary-coordinate image. -/
theorem applyCoordinateBytes_eq (weights : Vector WordExt3 192) (a : WordExt3) :
    applyCoordinateBytes (prepareCoordinates weights) a = applyCoordinates weights a := by
  apply WordExt3.toField_injective
  have sumField (n : Nat) (f : Fin n → WordExt3) :
      (sumExt n f).toField = ∑ i, (f i).toField := by
    rw [sumExt, sumExtLoop_refines]
    exact zero_add _
  rw [applyCoordinateBytes, sumField, applyCoordinates, coordinateLoop_refines]
  change _ = 0 + _
  rw [zero_add, ← (finProdFinEquiv : Fin 24 × Fin 8 ≃ Fin 192).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro byte _
  simp only [prepareCoordinates, Fin.getElem_fin, Vector.getElem_ofFn, sumField]
  apply Finset.sum_congr rfl
  intro bit _
  rw [coordinateByte_bit]
  have index : (finProdFinEquiv (byte,bit)).val = 8*byte.val+bit.val := by
    simp only [finProdFinEquiv, Equiv.coe_fn_mk]
    omega
  simp only [index]
  split <;> rfl

/-- Share byte images across every input of one binary-linear map. -/
def liftPointBinaryBytes (cols count : Nat) (points : Vector (BasisWindow cols) count)
    (values : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) : Vector WordExt3 cols :=
  let binary := prepareCoordinates (Vector.ofFn fun bit : Fin 192 => a[count+bit.val])
  Vector.ofFn fun i => WordExt3.add
    (sumExt count fun t => (BasisColumn.point points[t]).scaleAt a[t.val] i)
    (applyCoordinateBytes binary values[i])

/-- Reconstruct physical point windows and one shared binary-coordinate tensor. -/
def liftPointBinary (cols count : Nat) (points : Vector (BasisWindow cols) count)
    (values : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) : Vector WordExt3 cols :=
  let binary := Vector.ofFn fun bit : Fin 192 => a[count+bit.val]
  Vector.ofFn fun i => WordExt3.add
    (sumExt count fun t => (BasisColumn.point points[t]).scaleAt a[t.val] i)
    (applyCoordinates binary values[i])

/-- Shared binary-coordinate reconstruction preserves the complete compact-factor lift. -/
theorem liftPointBinary_eq (cols count : Nat) (points : Vector (BasisWindow cols) count)
    (values : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) :
    liftPointBinary cols count points values a =
      liftColumns cols (count+192) a
        (points.map BasisColumn.point ++ Vector.ofFn (fun bit : Fin 192 => BasisColumn.binary values bit)) := by
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  simp only [liftPointBinary, liftColumns, Vector.getElem_ofFn, WordExt3.toField_add,
    sumExt_eq, sumWords_refines, List.map_ofFn, Function.comp_apply, List.sum_ofFn,
    applyCoordinates, coordinateLoop_refines]
  change _ + (0 + _) = _
  rw [zero_add, Fin.sum_univ_add]
  apply congrArg₂ HAdd.hAdd
  · apply Finset.sum_congr rfl
    intro t _
    simp only [Fin.val_castAdd, Vector.getElem_append_left t.isLt, Vector.getElem_map, Fin.getElem_fin]
  · apply Finset.sum_congr rfl
    intro bit _
    change _ = ((points.map BasisColumn.point ++ Vector.ofFn (fun bit : Fin 192 => BasisColumn.binary values bit))[count+bit.val].scaleAt a[count+bit.val] ⟨i, hi⟩).toField
    rw [Vector.getElem_append_right _ (by omega)]
    simp only [Vector.getElem_ofFn, Fin.getElem_fin,
      Nat.add_sub_cancel_left, BasisColumn.scaleAt]
    split <;> rfl

/-- Byte images preserve the complete point and binary-tensor reconstruction. -/
@[csimp] theorem liftPointBinary_code : @liftPointBinary = @liftPointBinaryBytes := by
  funext cols count points values a
  simp only [liftPointBinary, liftPointBinaryBytes, applyCoordinateBytes_eq]

end CompStark.Pcs
