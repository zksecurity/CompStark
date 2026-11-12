/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-! Streaming finite sums without materializing a list of summands. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs

/-- Retain the accumulator when the next summand is zero. -/
def addNonzero {R : Type} [AddMonoid R] [DecidableEq R] (a b : R) : R :=
  if b = 0 then a else a+b

/-- Skipping a zero summand preserves exact addition. -/
theorem addNonzero_eq {R : Type} [AddMonoid R] [DecidableEq R] (a b : R) :
    addNonzero a b = a+b := by
  unfold addNonzero
  split_ifs with zero
  · rw [zero, add_zero]
  · rfl

/-- Accumulate a bounded coordinate interval in increasing order. -/
def sumLoop {R : Type} [AddCommMonoid R] [DecidableEq R] {size : Nat} (values : Fin size → R) :
    (count start : Nat) → start+count ≤ size → R → R
  | 0, _, _, accumulated => accumulated
  | count+1, start, h, accumulated =>
    sumLoop values count (start+1) (by omega) (addNonzero accumulated (values ⟨start,by omega⟩))

/-- Streaming accumulation equals the interval's exact finite sum. -/
theorem sumLoop_eq {R : Type} [AddCommMonoid R] [DecidableEq R] {size : Nat} (values : Fin size → R)
    (count start : Nat) (h : start+count ≤ size) (accumulated : R) :
    sumLoop values count start h accumulated =
      accumulated + ∑ i : Fin count, values ⟨start+i.val,by omega⟩ := by
  induction count generalizing start accumulated with
  | zero => simp only [sumLoop.eq_1, Fin.sum_univ_zero, add_zero]
  | succ count ih =>
    rw [sumLoop.eq_2, ih, addNonzero_eq, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, add_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    change start + (1+i.val) = start + (i.val+1)
    omega

/-- Sum a numeric finite family with one running accumulator. -/
def sumFin {R : Type} [AddCommMonoid R] [DecidableEq R] {size : Nat} (values : Fin size → R) : R :=
  sumLoop values size 0 (by omega) 0

/-- Streaming a complete finite family preserves its mathematical sum. -/
theorem sumFin_eq {R : Type} [AddCommMonoid R] [DecidableEq R] {size : Nat} (values : Fin size → R) :
    sumFin values = ∑ i, values i := by
  simp only [sumFin, sumLoop_eq, zero_add]

end CompStark.Pcs
