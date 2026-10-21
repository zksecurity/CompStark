/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompPoly.Univariate.NTTFast.Permutation
public import CompPoly.Univariate.NTTFast.Packed.BitReversal
public import Mathlib.LinearAlgebra.Lagrange

/-! # Points of the two-adic domains

Facts about the points the verifier evaluates at, in the spec field `Challenge.Spec EF`:

* bit reversal: `reverseBits` is CompPoly's `bitRevNat`, an involution below `2 ^ bits` that
  reverses concatenated bit groups block by block (`reverseBits_concat`);
* the two-adic generators: entry `i 2 ^ la + k` of a domain in bit-reversed order is the point
  `k` of a coset of the subgroup of order `2 ^ la` (`twoAdicGen_pow_concat`), and these points
  are distinct (`groupPoints_injective`);
* `lagrange` through distinct points holding the values of a polynomial of smaller degree is that
  polynomial's value (`toSpec_lagrange`), and Horner's rule evaluates a coefficient list
  (`toSpec_horner_list`);
* `unflatten` reads back the extension elements of their flattened coordinates.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri Polynomial

/-! ### Bit reversal -/

/-- The accumulator form of bit reversal is CompPoly's. -/
theorem reverseBitsGo_eq (bits : Nat) :
    ∀ i acc, reverseBitsGo bits i acc = CompPoly.CPolynomial.NTT.Transform.bitRevAcc bits i acc :=
        by
  induction bits with
  | zero => intro i acc; rfl
  | succ bits ih =>
    intro i acc
    rw [reverseBitsGo, CompPoly.CPolynomial.NTT.Transform.bitRevAcc, ih, Nat.mul_comm acc 2]

/-- `reverseBits` is CompPoly's `bitRevNat`. -/
theorem reverseBits_eq (i bits : Nat) :
    reverseBits i bits = CompPoly.CPolynomial.NTT.Transform.bitRevNat bits i := by
  rw [reverseBits, reverseBitsGo_eq, CompPoly.CPolynomial.NTT.Transform.bitRevAcc_eq,
    Nat.zero_mul, Nat.zero_add]

theorem reverseBits_concat (la m i k : Nat) (hk : k < 2 ^ la) :
    reverseBits (i * 2 ^ la + k) (m + la) = 2 ^ m * reverseBits k la + reverseBits i m := by
  rw [reverseBits_eq, reverseBits_eq, reverseBits_eq, Nat.mul_comm i]
  exact CompPoly.CPolynomial.NTTFast.Packed.bitRevNat_concat m la i k hk

theorem reverseBits_lt (i bits : Nat) : reverseBits i bits < 2 ^ bits := by
  rw [reverseBits_eq]; exact CompPoly.CPolynomial.NTT.Transform.bitRevNat_lt _ _

theorem reverseBits_reverseBits {i bits : Nat} (hi : i < 2 ^ bits) :
    reverseBits (reverseBits i bits) bits = i := by
  rw [reverseBits_eq, reverseBits_eq]
  exact CompPoly.CPolynomial.NTT.Transform.bitRevNat_involutive bits i hi

theorem reverseBits_injective {i j bits : Nat} (hi : i < 2 ^ bits) (hj : j < 2 ^ bits)
    (h : reverseBits i bits = reverseBits j bits) : i = j := by
  rw [← reverseBits_reverseBits hi, h, reverseBits_reverseBits hj]

theorem reverseBitsGo_zero : ∀ b, reverseBitsGo b 0 0 = 0
  | 0 => rfl
  | b + 1 => by
    rw [reverseBitsGo, Nat.zero_div, Nat.zero_mod, Nat.zero_mul]
    exact reverseBitsGo_zero b

theorem reverseBits_zero (b : Nat) : reverseBits 0 b = 0 := reverseBitsGo_zero b

/-- Reversing `k < 2 ^ la` in `m + la` bits shifts its reversal in `la` bits up by `m`. -/
theorem reverseBits_low (la m k : Nat) (hk : k < 2 ^ la) :
    reverseBits k (m + la) = 2 ^ m * reverseBits k la := by
  have := reverseBits_concat la m 0 k hk
  rwa [Nat.zero_mul, Nat.zero_add, reverseBits_zero, Nat.add_zero] at this

/-! ### The two-adic generators -/

section Generators
variable {F : Type} [BaseField F]

theorem twoAdicGen_pow_ne_zero (n : Nat) (hn : n ≤ twoAdicity F) (e : Nat) :
    twoAdicGen (F := F) n ^ e ≠ 0 :=
  pow_ne_zero _ (BaseField.twoAdicGen_ne_zero n hn)

/-- Entry `i 2 ^ la + k` of the domain of order `2 ^ (m + la)` in bit-reversed order is the
group point `start · g ^ bitrev k`, `start` entry `i` of the folded domain's square roots. -/
theorem twoAdicGen_pow_concat (la m i k : Nat) (hml : m + la ≤ twoAdicity F) (hk : k < 2 ^ la) :
    twoAdicGen (F := F) (m + la) ^ reverseBits (i * 2 ^ la + k) (m + la) =
      twoAdicGen (m + la) ^ reverseBits i m * twoAdicGen la ^ reverseBits k la := by
  rw [reverseBits_concat la m i k hk, pow_add, pow_mul, Nat.add_comm m la,
    BaseField.twoAdicGen_pow la m (by omega), mul_comm]

theorem twoAdicGen_pow_pow (la m r : Nat) (hml : m + la ≤ twoAdicity F) :
    (twoAdicGen (F := F) (m + la) ^ r) ^ 2 ^ la = twoAdicGen m ^ r := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, BaseField.twoAdicGen_pow m la hml]

/-- The point of entry `k < 2 ^ la` of the domain of order `2 ^ (m + la)`, bit-reversed. -/
theorem twoAdicGen_pow_low (la m k : Nat) (hml : m + la ≤ twoAdicity F) (hk : k < 2 ^ la) :
    twoAdicGen (F := F) (m + la) ^ reverseBits k (m + la) = twoAdicGen la ^ reverseBits k la := by
  rw [reverseBits_low la m k hk, pow_mul, Nat.add_comm m la,
    BaseField.twoAdicGen_pow la m (by omega)]

/-- A group's points `start · g ^ bitrev k` are distinct. -/
theorem groupPoints_injective (la : Nat) (start : F) (hla : la ≤ twoAdicity F) (hs : start ≠ 0) :
    ∀ a < 2 ^ la, ∀ b < 2 ^ la, start * powF (twoAdicGen la) (reverseBits a la) =
      start * powF (twoAdicGen la) (reverseBits b la) → a = b := by
  intro a ha b hb h
  rw [powF_eq, powF_eq] at h
  exact reverseBits_injective ha hb ((BaseField.isPrimitiveRoot_twoAdicGen la hla).pow_inj
    (reverseBits_lt _ _) (reverseBits_lt _ _) (mul_left_cancel₀ hs h))

end Generators

/-! ### Values in the spec field -/

section Spec
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "L" => Challenge.Spec EF

theorem isPrimitiveRoot_algebraMap (n : Nat) (hn : n ≤ twoAdicity F) :
    IsPrimitiveRoot (algebraMap F L (twoAdicGen n)) (2 ^ n) :=
  (BaseField.isPrimitiveRoot_twoAdicGen n hn).map_of_injective (algebraMap F L).injective

theorem toSpec_foldl_add_range (n : Nat) (f : Nat → EF) (a : EF) :
    Challenge.toSpec ((List.range n).foldl (fun acc k ↦ acc + f k) a) =
      Challenge.toSpec a + ∑ k ∈ Finset.range n, Challenge.toSpec (f k) := by
  induction n with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Challenge.toSpec_add,
      ih, Finset.sum_range_succ, add_assoc]

theorem toSpec_foldl_weight (n : Nat) (gx : Nat → F) (x : F) (c d : Nat → EF) (a : EF) :
    Challenge.toSpec ((List.range n).foldl (fun w k ↦ if gx k == x then w else w * c k * d k) a) =
      Challenge.toSpec a * ∏ k ∈ Finset.range n,
        if gx k = x then 1 else Challenge.toSpec (c k) * Challenge.toSpec (d k) := by
  induction n with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.prod_range_zero, mul_one]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.prod_range_succ, ← mul_assoc, ← ih]
    by_cases h : gx n = x
    · simp only [h, beq_self_eq_true, ite_true, mul_one]
    · simp only [beq_iff_eq, h, ite_false, Challenge.toSpec_mul, mul_assoc]

/-- `lagrange` through distinct points `gx k`, `k < n`, holding the values of `q` of degree below
`n`, is `q`'s value. -/
theorem toSpec_lagrange (n : Nat) (gx : Nat → F) (gy : Nat → EF) (z : EF) (q : L[X])
    (hinj : ∀ i < n, ∀ j < n, gx i = gx j → i = j) (hdeg : q.degree < n)
    (hq : ∀ i < n, Challenge.toSpec (gy i) = q.eval (algebraMap F L (gx i))) :
    Challenge.toSpec (lagrange ((List.range n).map gx) ((List.range n).map gy) z) =
      q.eval (Challenge.toSpec z) := by
  unfold lagrange
  rw [List.zip_map']
  dsimp only
  split
  · rename_i x y hfind
    have hp := List.find?_some hfind
    obtain ⟨k, hk, hxy⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rw [beq_iff_eq] at hp
    rw [hp, Ext.ofBase, Challenge.toSpec_ofBase', hq k (List.mem_range.mp hk)]
  · simp only [List.foldl_map]
    rw [toSpec_foldl_add_range, Challenge.toSpec_zero, zero_add]
    simp only [Challenge.toSpec_mul]
    have hinj' : Set.InjOn (fun k ↦ algebraMap F L (gx k)) (Finset.range n : Set Nat) :=
      fun i hi j hj h ↦ hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
        ((algebraMap F L).injective h)
    rw [Lagrange.eq_interpolate_of_eval_eq (r := fun k ↦ Challenge.toSpec (gy k)) hinj'
      (by rwa [Finset.card_range]) (fun i hi ↦ (hq i (Finset.mem_range.mp hi)).symm),
      Lagrange.interpolate_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [eval_mul, eval_C, Lagrange.basis, eval_prod]
    congr 1
    rw [toSpec_foldl_weight, Challenge.toSpec_one, one_mul, ← Finset.mul_prod_erase _ _ hk,
      ite_eq_left rfl, one_mul]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    obtain ⟨hjk, hj⟩ := Finset.mem_erase.mp hj
    rw [ite_eq_right (fun h ↦ hjk (hinj _ (Finset.mem_range.mp hj) _ (Finset.mem_range.mp hk) h)),
      Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C]
    simp only [Challenge.toSpec_sub, Ext.ofBase, Challenge.toSpec_ofBase', map_inv₀, map_sub]
    ring

theorem toSpec_horner_list (l : List EF) (x : EF) :
    Challenge.toSpec (l.foldr (fun c acc ↦ acc * x + c) 0) =
      ∑ k ∈ Finset.range l.length, Challenge.toSpec (l.getD k 0) * Challenge.toSpec x ^ k := by
  induction l with
  | nil => rw [List.foldr_nil, Challenge.toSpec_zero, List.length_nil, Finset.sum_range_zero]
  | cons c l ih =>
    rw [List.foldr_cons, Challenge.toSpec_add, Challenge.toSpec_mul, ih, List.length_cons,
      Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ, mul_assoc]

theorem degree_sum_C_mul_X_pow_lt (N : Nat) (c : Nat → L) :
    (∑ n ∈ Finset.range N, C (c n) * X ^ n).degree < (N : WithBot Nat) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [coeff_C_mul_X_pow, ite_eq_right (by have := Finset.mem_range.mp hn; omega)]

theorem natDegree_lt_of_degree {p : L[X]} {n : Nat} (hp : p.degree < (n : WithBot Nat))
    (hn : 0 < n) : p.natDegree < n := by
  by_cases h0 : p = 0
  · rw [h0, natDegree_zero]; exact hn
  · exact (natDegree_lt_iff_degree_lt h0).mpr hp

/-- `d` coefficients at a time read back extension elements. -/
theorem unflatten_append (x : EF) (xs : List F) :
    unflatten (Ext.coeffs x ++ xs) = x :: unflatten xs := by
  have hd : 0 < Challenge.d EF := (Challenge.params EF).d_pos
  have hl : (Ext.coeffs x).length = Challenge.d EF := Challenge.length_coeffs x
  unfold unflatten
  rw [show (Ext.coeffs x ++ xs).length / Challenge.d EF = xs.length / Challenge.d EF + 1 by
    rw [List.length_append, hl, Nat.add_comm, Nat.add_div_right _ hd],
    List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · conv_rhs => rw [← Challenge.ofCoeffs_coeffs x]
    congr 1
    refine List.ext_getElem (by rw [List.length_map, List.length_range, hl]) fun j h1 _ ↦ ?_
    rw [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, Nat.mul_zero, Nat.zero_add,
      List.getD_append _ _ _ _ (by rw [hl]; exact h1), List.getD_eq_getElem]
  · refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply]
    congr 1
    refine List.map_congr_left fun j hj ↦ ?_
    rw [List.mem_range] at hj
    rw [List.getD_append_right _ _ _ _ (by rw [hl]; nlinarith), hl]
    congr 1
    rw [Nat.mul_succ]
    omega

theorem unflatten_flatMap (l : List EF) : unflatten (l.flatMap Ext.coeffs) = l := by
  induction l with
  | nil => simp only [unflatten, List.flatMap_nil, List.length_nil, Nat.zero_div, List.range_zero,
      List.map_nil]
  | cons x l ih => rw [List.flatMap_cons, unflatten_append, ih]

end Spec

theorem toList_getD {α : Type} (a : Array α) (k : Nat) (d : α) :
    a.toList.getD k d = a.getD k d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

end CompStark.Stark
