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
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Specialize zero and unit base factors before entering mixed multiplication. -/
@[inline] def roundBaseProduct (a : Word) (b : WordExt3) : WordExt3 :=
  if a.val = 0 then 0 else if a.val = 1 then b else WordExt3.mulScalar b a

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

end CompStark.Pcs
