/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Copyright (c) 2026 leanEthereum.
Adapted from leanEthereum/leanMultisig, crates/pcs/src/stack_open/basis.rs and whir.rs.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.MixedDot

/-! Joint survivor construction and unreduced adjacent-pair messages. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxHeartbeats 1000000

/-- Two materialized survivor vectors and their compressed quadratic message. -/
structure PairSurvivors (rows : Nat) where
  /-- Restricted witness. -/
  table : Vector WordExt3 (2*rows)
  /-- Reconstructed weights. -/
  weights : Vector WordExt3 (2*rows)
  /-- Constant and quadratic message coefficients. -/
  message : Vector WordExt3 2

/-- Visit each adjacent pair once, retaining unreduced message coordinates in scalar arguments. -/
@[specialize] def survivorLoop (rows : Nat) (f b : Fin (2*rows) → WordExt3)
    (left : Nat) (bound : left ≤ rows) (table weights : Vector WordExt3 (2*rows))
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) : PairSurvivors rows :=
  match left with
  | 0 => ⟨table, weights, #v[(⟨⟨a0,a1⟩,⟨a2,a3⟩,⟨a4,a5⟩⟩ : MixedWide).reduce,
      (⟨⟨b0,b1⟩,⟨b2,b3⟩,⟨b4,b5⟩⟩ : MixedWide).reduce]⟩
  | left+1 =>
    let lo : Fin (2*rows) := ⟨2*left,by omega⟩
    let hi : Fin (2*rows) := ⟨2*left+1,by omega⟩
    let f0 := f lo
    let f1 := f hi
    let w0 := b lo
    let w1 := b hi
    let u := MixedWide.mul f0 w0
    let v := MixedWide.mul (WordExt3.add f0 f1) (WordExt3.add w0 w1)
    survivorLoop rows f b left (by omega)
      ((table.set lo f0).set hi f1) ((weights.set lo w0).set hi w1)
      (a0 ^^^ u.c0.lo) (a1 ^^^ u.c0.hi) (a2 ^^^ u.c1.lo) (a3 ^^^ u.c1.hi)
      (a4 ^^^ u.c2.lo) (a5 ^^^ u.c2.hi)
      (b0 ^^^ v.c0.lo) (b1 ^^^ v.c0.hi) (b2 ^^^ v.c1.lo) (b3 ^^^ v.c1.hi)
      (b4 ^^^ v.c2.lo) (b5 ^^^ v.c2.hi)
termination_by structural left

/-- The fused traversal writes exactly the visited witness coordinates. -/
theorem survivorLoop_table (rows : Nat) (f b : Fin (2*rows) → WordExt3)
    (left : Nat) (bound : left ≤ rows) (table weights : Vector WordExt3 (2*rows))
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) (i : Fin (2*rows)) :
    (survivorLoop rows f b left bound table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5).table[i] =
      if i.val < 2*left then f i else table[i] := by
  induction left generalizing table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 with
  | zero =>
    rw [survivorLoop]
    simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]
  | succ left ih =>
    rw [survivorLoop, ih]
    simp only [Fin.getElem_fin, Vector.getElem_set]
    split_ifs <;> (try congr 1) <;> (try apply Fin.ext) <;> omega

/-- The fused traversal writes exactly the visited weight coordinates. -/
theorem survivorLoop_weights (rows : Nat) (f b : Fin (2*rows) → WordExt3)
    (left : Nat) (bound : left ≤ rows) (table weights : Vector WordExt3 (2*rows))
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) (i : Fin (2*rows)) :
    (survivorLoop rows f b left bound table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5).weights[i] =
      if i.val < 2*left then b i else weights[i] := by
  induction left generalizing table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 with
  | zero =>
    rw [survivorLoop]
    simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]
  | succ left ih =>
    rw [survivorLoop, ih]
    simp only [Fin.getElem_fin, Vector.getElem_set]
    split_ifs <;> (try congr 1) <;> (try apply Fin.ext) <;> omega

/-- Deferred coefficient 0 sums exactly the visited adjacent products. -/
theorem survivorLoop_message0 (rows : Nat) (f b : Fin (2*rows) → WordExt3)
    (left : Nat) (bound : left ≤ rows) (table weights : Vector WordExt3 (2*rows))
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) :
    (survivorLoop rows f b left bound table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5).message[0].toField =
      (⟨⟨a0,a1⟩,⟨a2,a3⟩,⟨a4,a5⟩⟩ : MixedWide).reduce.toField +
        ∑ i : Fin left, (f ⟨2*i.val,by omega⟩).toField * (b ⟨2*i.val,by omega⟩).toField := by
  induction left generalizing table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 with
  | zero =>
    simp only [survivorLoop, Fin.sum_univ_zero, add_zero]
    rfl
  | succ left ih =>
    rw [survivorLoop, ih, Fin.sum_univ_castSucc]
    change (MixedWide.add (⟨⟨a0,a1⟩,⟨a2,a3⟩,⟨a4,a5⟩⟩ : MixedWide) _).reduce.toField + _ = _
    rw [MixedWide.reduce_add, WordExt3.toField_add, MixedWide.reduce_mul, WordExt3.toField_mul]
    simp only [Fin.val_castSucc, Fin.val_last]
    ac_rfl

/-- Deferred coefficient 1 sums exactly the visited adjacent products. -/
theorem survivorLoop_message1 (rows : Nat) (f b : Fin (2*rows) → WordExt3)
    (left : Nat) (bound : left ≤ rows) (table weights : Vector WordExt3 (2*rows))
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : UInt64) :
    (survivorLoop rows f b left bound table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5).message[1].toField =
      (⟨⟨b0,b1⟩,⟨b2,b3⟩,⟨b4,b5⟩⟩ : MixedWide).reduce.toField +
        ∑ i : Fin left, ((f ⟨2*i.val,by omega⟩).toField + (f ⟨2*i.val+1,by omega⟩).toField) *
          ((b ⟨2*i.val,by omega⟩).toField + (b ⟨2*i.val+1,by omega⟩).toField) := by
  induction left generalizing table weights a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 with
  | zero =>
    simp only [survivorLoop, Fin.sum_univ_zero, add_zero]
    rfl
  | succ left ih =>
    rw [survivorLoop, ih, Fin.sum_univ_castSucc]
    change (MixedWide.add (⟨⟨b0,b1⟩,⟨b2,b3⟩,⟨b4,b5⟩⟩ : MixedWide) _).reduce.toField + _ = _
    rw [MixedWide.reduce_add, WordExt3.toField_add, MixedWide.reduce_mul, WordExt3.toField_mul]
    simp only [WordExt3.toField_add, Fin.val_castSucc, Fin.val_last]
    ac_rfl

/-- Finish both survivors and their adjacent message in one traversal. -/
@[inline] def materializePairs (rows : Nat) (f b : Fin (2*rows) → WordExt3) : PairSurvivors rows :=
  survivorLoop rows f b rows (Nat.le_refl _) (Vector.replicate _ 0) (Vector.replicate _ 0)
    0 0 0 0 0 0 0 0 0 0 0 0

/-- Complete fused witness materialization is exact at every coordinate. -/
theorem materializePairs_table (rows : Nat) (f b : Fin (2*rows) → WordExt3) :
    (materializePairs rows f b).table = Vector.ofFn f := by
  apply Vector.ext
  intro i hi
  simpa only [materializePairs, Fin.getElem_fin, hi, ite_true, Vector.getElem_ofFn]
    using survivorLoop_table rows f b rows (Nat.le_refl _) (Vector.replicate _ 0) (Vector.replicate _ 0)
      0 0 0 0 0 0 0 0 0 0 0 0 ⟨i,hi⟩

/-- Complete fused weight materialization is exact at every coordinate. -/
theorem materializePairs_weights (rows : Nat) (f b : Fin (2*rows) → WordExt3) :
    (materializePairs rows f b).weights = Vector.ofFn b := by
  apply Vector.ext
  intro i hi
  simpa only [materializePairs, Fin.getElem_fin, hi, ite_true, Vector.getElem_ofFn]
    using survivorLoop_weights rows f b rows (Nat.le_refl _) (Vector.replicate _ 0) (Vector.replicate _ 0)
      0 0 0 0 0 0 0 0 0 0 0 0 ⟨i,hi⟩

/-- Both compressed coefficients equal the complete adjacent round. -/
theorem materializePairs_message (rows : Nat) (f b : Fin (2*rows) → WordExt3) :
    (materializePairs rows f b).message =
      roundCoefficients rows 1 ((Vector.ofFn f).cast (by omega)) ((Vector.ofFn b).cast (by omega)) := by
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  have cases : i = 0 ∨ i = 1 := by omega
  have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  rcases cases with rfl | rfl
  · rw [materializePairs, survivorLoop_message0, roundCoefficients_constant]
    simp only [MixedWide.reduce_zero, z, zero_add, Nat.mul_one,
      roundLow, Nat.div_one, Nat.mod_one, Nat.add_zero, Fin.getElem_fin, Vector.getElem_cast, Vector.getElem_ofFn]
    exact Fintype.sum_equiv (finCongr (Nat.mul_one rows)).symm _ _ (fun _ => rfl)
  · rw [materializePairs, survivorLoop_message1, roundCoefficients_quadratic]
    simp only [MixedWide.reduce_zero, z, zero_add, Nat.mul_one,
      roundLow, roundHigh, Nat.div_one, Nat.mod_one, Nat.add_zero, Fin.getElem_fin, Vector.getElem_cast, Vector.getElem_ofFn]
    exact Fintype.sum_equiv (finCongr (Nat.mul_one rows)).symm _ _ (fun _ => rfl)

end CompStark.Pcs
