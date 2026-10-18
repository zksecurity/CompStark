/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Field
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Batch inversion inverts

`batchInv` computes every inverse from one inversion and prefix products. When no element is
zero they are the true inverses (`batchInv_eq`). The statement goes through any injective map
into a field that respects products, inverses and one, so it covers the base field and the
extension through `toSpec`.
-/

@[expose] public section
namespace CompStark.Stark

/-- The prefix products of the first loop. -/
theorem prefixProducts {K L : Type*} [Mul K] [One K] [Monoid L] (φ : K → L) (hmul : ∀ a b, φ (a * b) = φ a * φ b) :
    ∀ (l : List K) (pre : Array K) (acc : K),
      let r := l.foldl (fun b a ↦ (b.1.push b.2, b.2 * a)) (pre, acc)
      r.1.size = pre.size + l.length ∧ (∀ i < pre.size, r.1.getD i 1 = pre.getD i 1) ∧
        (∀ i < l.length, φ (r.1.getD (pre.size + i) 1) = φ acc * ((l.take i).map φ).prod) ∧
        φ r.2 = φ acc * (l.map φ).prod
  | [], pre, acc => by
    refine ⟨by simp only [List.foldl_nil, List.length_nil, Nat.add_zero], fun _ _ ↦ rfl,
      fun i hi ↦ absurd hi (Nat.not_lt_zero _), ?_⟩
    simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | x :: l, pre, acc => by
    obtain ⟨h1, h2, h3, h4⟩ := prefixProducts φ hmul l (pre.push acc) (acc * x)
    simp only [List.foldl_cons] at h1 h2 h3 h4 ⊢
    refine ⟨by rw [h1, Array.size_push, List.length_cons]; omega, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
    · rw [h2 i (by rw [Array.size_push]; omega), Array.getD_eq_getD_getElem?,
        Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]
    · cases i with
      | zero =>
        rw [Nat.add_zero, h2 _ (by rw [Array.size_push]; omega), Array.getD_eq_getD_getElem?,
          Array.getElem?_push_size, Option.getD_some, List.take_zero, List.map_nil,
          List.prod_nil, mul_one]
      | succ i =>
        have := h3 i (by rw [List.length_cons] at hi; omega)
        have e : (pre.push acc).size + i = pre.size + (i + 1) := by rw [Array.size_push]; omega
        rw [e] at this
        rw [this, hmul, List.take_succ_cons, List.map_cons, List.prod_cons, mul_assoc]
    · rw [h4, hmul, List.map_cons, List.prod_cons, mul_assoc]

theorem batchInv_eq {K L : Type*} [Mul K] [Inv K] [One K] [Field L] (φ : K → L)
    (hinj : Function.Injective φ) (hmul : ∀ a b, φ (a * b) = φ a * φ b)
    (hinv : ∀ a, φ a⁻¹ = (φ a)⁻¹) (hone : φ 1 = 1) (xs : Array K) (hx : ∀ x ∈ xs, φ x ≠ 0) :
    batchInv xs = xs.map (·⁻¹) := by
  simp only [batchInv, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl, pure_bind,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← Array.foldl_toList, Array.emptyWithCapacity_eq]
  obtain ⟨hP1, -, hP3, hP4⟩ := prefixProducts φ hmul xs.toList #[] 1
  generalize List.foldl (fun b a ↦ (b.1.push b.2, b.2 * a)) (#[], 1) xs.toList = P at hP1 hP3 hP4
  simp only [Array.size_empty, Nat.zero_add, Array.length_toList, hone, one_mul] at hP1 hP3 hP4
  -- `pp i` is the product of the first `i` elements' images.
  let pp (i : Nat) : L := ((xs.toList.take i).map φ).prod
  have hpp (i : Nat) (hi : i < xs.size) : pp (i + 1) = pp i * φ xs[i] := by
    simp only [pp, List.take_add_one, List.map_append, List.prod_append, Array.getElem?_toList,
      Array.getElem?_eq_getElem hi, Option.toList_some, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  have hne (i : Nat) : pp i ≠ 0 := by
    refine List.prod_ne_zero fun h ↦ ?_
    obtain ⟨x, hx', e⟩ := List.mem_map.mp h
    exact hx x (Array.mem_toList_iff.mp (List.mem_of_mem_take hx')) e
  have hpre (i : Nat) (hi : i < xs.size) : φ (P.1.getD i 1) = pp i := hP3 i hi
  have hacc : φ P.2 = pp xs.size := by
    rw [hP4]
    show _ = ((xs.toList.take xs.size).map φ).prod
    rw [List.take_of_length_le (by rw [Array.length_toList])]
  -- The second loop, after `k` steps, has set entries `n - k, …, n - 1` to the inverses.
  have hloop : ∀ k ≤ xs.size,
      let Q := (List.range' 0 k).foldl (fun b a ↦ (b.1 * xs.getD (xs.size - 1 - a) 1,
        b.2.set! (xs.size - 1 - a) (b.1 * P.1.getD (xs.size - 1 - a) 1)))
        (P.2⁻¹, Array.replicate xs.size 1)
      φ Q.1 = (pp (xs.size - k))⁻¹ ∧ Q.2.size = xs.size ∧
        ∀ i (hi : i < xs.size), xs.size - k ≤ i → φ (Q.2.getD i 1) = (φ xs[i])⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by rw [List.range'_zero, List.foldl_nil, hinv, hacc, Nat.sub_zero],
        Array.size_replicate, fun i hi h ↦ absurd h (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
        Nat.one_mul]
      have hi : xs.size - 1 - k < xs.size := by omega
      have e : xs.size - k = xs.size - 1 - k + 1 := by omega
      rw [e, hpp _ hi] at h1
      refine ⟨?_, by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, h2],
        fun i hi' h ↦ ?_⟩
      · rw [hmul, h1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some,
          mul_inv, mul_assoc, inv_mul_cancel₀ (hx _ (Array.getElem_mem hi)), mul_one,
          show xs.size - (k + 1) = xs.size - 1 - k by omega]
      · rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
        split
        · rename_i hj
          subst hj
          simp only [h2, hi, ite_true, Option.getD_some]
          rw [hmul, h1, hpre _ hi, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hne _),
            one_mul]
        · rw [← Array.getD_eq_getD_getElem?]
          exact h3 i hi' (by omega)
  obtain ⟨-, h2, h3⟩ := hloop xs.size (Nat.le_refl _)
  show ((List.foldl (α := K × Array K) (β := Nat) _ _ _).2 : Array K) = _
  apply Array.ext
  · rw [h2, Array.size_map]
  · intro i hi1 hi2
    rw [Array.size_map] at hi2
    apply hinj
    have := h3 i hi2 (by omega)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi1, Option.getD_some] at this
    rw [this, Array.getElem_map, hinv]

end CompStark.Stark
