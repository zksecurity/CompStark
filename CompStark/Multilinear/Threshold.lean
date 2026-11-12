/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.Executable

/-! Multilinear threshold selectors evaluated without expanding their Boolean table. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 8192

@[expose] public section
namespace CompStark.Multilinear
open CompStark.Keccak.Gkr

/-- Evaluate the selector for numeric cube indices greater than or equal to a cutoff. -/
def threshold {R : Type} [CommRing R] : (n : Nat) → Nat → (Fin n → R) → R
  | 0, cutoff, _ => if cutoff = 0 then 1 else 0
  | n+1, cutoff, point =>
    let last := point (Fin.last n)
    if cutoff ≤ 2^n then
      last + (1-last) * threshold n cutoff (fun i => point i.castSucc)
    else last * threshold n (cutoff-2^n) (fun i => point i.castSucc)

/-- Threshold evaluation is the exact sum of the selected equality weights. -/
theorem threshold_eq {R : Type} [CommRing R] (n cutoff : Nat) (point : Fin n → R) :
    threshold n cutoff point =
      ∑ i : Fin (2^n), if cutoff ≤ i.val then eqWeight point i.val else 0 := by
  induction n generalizing cutoff with
  | zero =>
    change (if cutoff = 0 then (1 : R) else 0) =
      ∑ i : Fin 1, if cutoff ≤ i.val then (1 : R) else 0
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.le_zero]
  | succ n ih =>
    rw [threshold.eq_2, cube_sum]
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero]
    have low (i : Fin (2^n)) : eqWeight point i.val =
        eqWeight (fun j : Fin n => point j.castSucc) i.val * (1-point (Fin.last n)) := by
      simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, ite_true] using eqWeight_last point i 0
    have high (i : Fin (2^n)) : eqWeight point (i.val+2^n) =
        eqWeight (fun j : Fin n => point j.castSucc) i.val * point (Fin.last n) := by
      simpa only [Fin.val_one, Nat.mul_one, one_ne_zero, ite_false] using eqWeight_last point i 1
    simp_rw [low, high]
    split_ifs with small
    · have all (i : Fin (2^n)) : cutoff ≤ i.val+2^n := by omega
      simp only [all, ite_true, ← Finset.sum_mul, eqWeight_sum, one_mul]
      rw [ih]
      have distribute : (∑ i : Fin (2^n), if cutoff ≤ i.val then
          eqWeight (fun j : Fin n => point j.castSucc) i.val * (1-point (Fin.last n)) else 0) =
          (∑ i : Fin (2^n), if cutoff ≤ i.val then eqWeight (fun j : Fin n => point j.castSucc) i.val else 0) *
            (1-point (Fin.last n)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp only [zero_mul]
      rw [distribute]
      ring
    · have none (i : Fin (2^n)) : ¬ cutoff ≤ i.val := by have := i.isLt; omega
      have selected (i : Fin (2^n)) : (cutoff ≤ i.val+2^n) ↔ (cutoff-2^n ≤ i.val) := by omega
      simp only [none, ite_false, Finset.sum_const_zero, zero_add, selected]
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp only [mul_zero, mul_comm]

/-- Ring maps commute with threshold evaluation. -/
theorem threshold_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (n cutoff : Nat) (point : Fin n → R) :
    f (threshold n cutoff point) = threshold n cutoff (fun i => f (point i)) := by
  induction n generalizing cutoff with
  | zero =>
    simp only [threshold.eq_1]
    split_ifs <;> simp only [map_one, map_zero]
  | succ n ih =>
    simp only [threshold.eq_2]
    split_ifs <;> simp only [map_add, map_mul, map_sub, map_one, ih]

end CompStark.Multilinear
