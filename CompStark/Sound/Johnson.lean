/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Decoding
public import ArkLib.Data.Finset.PairwiseIntersection

/-! # The Johnson bound on the list size

`Setup.listSize S ι δ` counts tuples of polynomials of degree at most `n` agreeing with one tuple
of words on a common set of at least `(1 - δ) N` points. Two distinct such tuples agree on at most
`n` points of `L` (`card_le_of_eqOn`), so their agreement sets meet in at most `n` points. The
pairwise-intersection count (ArkLib's `Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le`, at
the agreement `⌈(1 - δ) N⌉`, `lt_of_johnson`) then bounds the list by
`(a - rate) / (a² - rate)` for `a = 1 - δ > √rate` (`listSize_le_johnson`).
For example `rate = 1/16`, `δ = 1/2` gives `7/3`, so at most `2`.

Below the unique-decoding radius `(1 - rate) / 2` two agreement sets meet in more than `n` points,
so the list has at most one element (`listSize_le_one`).
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

local notation "𝔽" => KoalaBear.Field

variable {EF : Type} [Challenge EF]

/-- The points of `L` in `𝔽` are distinct. -/
theorem basePoint_injective (S : Setup EF) :
    Function.Injective fun i : S.Point ↦ basePoint (S.logN + S.params.logBlowup) i := by
  intro i j h
  apply S.domain.injective
  rw [domain_eq, domain_eq]
  exact congrArg (algebraMap 𝔽 (Challenge.Spec EF)) h

/-- Distinct tuples of polynomials of degree at most `n` agree on at most `n` points of `L`. -/
theorem card_le_of_eqOn (S : Setup EF) {ι : Type} (p q : ι → 𝔽[X])
    (hp : ∀ k, (p k).natDegree ≤ S.n) (hq : ∀ k, (q k).natDegree ≤ S.n) (hpq : p ≠ q)
    (U : Finset S.Point)
    (hU : ∀ i ∈ U, ∀ k, (p k).eval (basePoint (S.logN + S.params.logBlowup) i) =
      (q k).eval (basePoint (S.logN + S.params.logBlowup) i)) :
    U.card ≤ S.n := by
  classical
  by_contra hlt
  refine hpq (funext fun k ↦ ?_)
  refine eq_of_degree_sub_lt_of_eval_finset_eq
    (U.image fun i : S.Point ↦ basePoint (S.logN + S.params.logBlowup) i) ?_ ?_
  · rw [Finset.card_image_of_injective _ (basePoint_injective S)]
    refine (degree_le_natDegree).trans_lt ?_
    have : (p k - q k).natDegree ≤ S.n := (natDegree_sub_le _ _).trans (max_le (hp k) (hq k))
    exact_mod_cast (show _ < U.card by omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hU i hi k

/-- A set all of whose finite subsets have at most `ℓ` elements has `ncard` at most `ℓ`. -/
theorem ncard_le_of_finset {α : Type} (s : Set α) (ℓ : Nat)
    (h : ∀ t : Finset α, ↑t ⊆ s → t.card ≤ ℓ) : s.ncard ≤ ℓ := by
  by_cases hs : s.Finite
  · rw [Set.ncard_eq_toFinset_card s hs]
    exact h _ (Set.Finite.coe_toFinset hs).subset
  · rw [Set.Infinite.ncard hs]
    exact Nat.zero_le ℓ

/-- The real inequality behind the Johnson bound: with agreement `A ≥ x` and `c` tuples,
`c (A² - N n) ≤ N (A - n)` forces `c < ℓ + 1` once `N (x - n) < (ℓ + 1) (x² - N n)`. -/
theorem lt_of_johnson (N n A x c ℓ : ℝ) (hn : 0 ≤ n) (hnN : n ≤ N) (hx : 0 ≤ x)
    (hxA : x ≤ A) (hpos : N * n < x ^ 2)
    (hℓ : N * (x - n) < (ℓ + 1) * (x ^ 2 - N * n))
    (hc : c * (A ^ 2 - N * n) ≤ N * (A - n)) : c < ℓ + 1 := by
  have hxpos : 0 < x := by
    rcases hx.eq_or_lt with h | h
    · rw [← h] at hpos
      nlinarith
    · exact h
  have hgap : 0 < x ^ 2 - N * n := by linarith
  have hgapA : 0 < A ^ 2 - N * n := by nlinarith
  -- `N (x² - N n) ≤ 2 x N (x - n)`, as `(x - n)² + n (N - n) ≥ 0`.
  have hsq : N * (x ^ 2 - N * n) ≤ 2 * x * (N * (x - n)) := by
    nlinarith [sq_nonneg (x - n), mul_nonneg hn (sub_nonneg.mpr hnN)]
  have h2x : N < (ℓ + 1) * (2 * x) := by
    have : N * (x ^ 2 - N * n) < (ℓ + 1) * (2 * x) * (x ^ 2 - N * n) := by
      nlinarith [mul_lt_mul_of_pos_left hℓ (by linarith : (0 : ℝ) < 2 * x)]
    exact lt_of_mul_lt_mul_right this hgap.le
  -- `(ℓ + 1) (y² - N n) - N (y - n)` is positive at `x` and grows up to `A`.
  have hgA : N * (A - n) < (ℓ + 1) * (A ^ 2 - N * n) := by
    have hmono : 0 ≤ (A - x) * ((ℓ + 1) * (A + x) - N) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  by_contra hge
  push Not at hge
  nlinarith [mul_le_mul_of_nonneg_right hge hgapA.le]

/-- Each tuple in the list, with an agreement set. -/
noncomputable def agreeSet (S : Setup EF) {ι : Type} (δ : ℝ) (words : ι → S.Point → 𝔽)
    (p : ι → 𝔽[X]) : Finset S.Point :=
  open Classical in if h : Agree S δ words p then h.choose else ∅

/-- The agreement set of a tuple in the list is large and the tuple agrees with the words on it. -/
theorem agreeSet_spec (S : Setup EF) {ι : Type} (δ : ℝ) (words : ι → S.Point → 𝔽)
    (p : ι → 𝔽[X]) (h : Agree S δ words p) :
    ((agreeSet S δ words p).card : ℝ) ≥ S.size * (1 - δ) ∧
      ∀ i ∈ agreeSet S δ words p, ∀ k,
        words k i = (p k).eval (basePoint (S.logN + S.params.logBlowup) i) := by
  simp only [agreeSet, h, ↓reduceDIte]
  exact h.choose_spec

/-- The agreement sets of two distinct tuples in the list meet in at most `n` points. -/
theorem card_inter_agreeSet_le (S : Setup EF) {ι : Type} (δ : ℝ) (words : ι → S.Point → 𝔽)
    (p q : ι → 𝔽[X]) (hp : (∀ k, (p k).natDegree ≤ S.n) ∧ Agree S δ words p)
    (hq : (∀ k, (q k).natDegree ≤ S.n) ∧ Agree S δ words q) (hpq : p ≠ q) :
    (agreeSet S δ words p ∩ agreeSet S δ words q).card ≤ S.n := by
  refine card_le_of_eqOn S p q hp.1 hq.1 hpq _ fun i hi k ↦ ?_
  rw [Finset.mem_inter] at hi
  rw [← (agreeSet_spec S δ words p hp.2).2 i hi.1 k, (agreeSet_spec S δ words q hq.2).2 i hi.2 k]

/-- The Johnson bound: for `δ < 1 - √rate`, the list has at most `ℓ` tuples once
`(1 - δ - rate) / ((1 - δ)² - rate) < ℓ + 1`. -/
theorem listSize_le_johnson (S : Setup EF) (ι : Type) [Fintype ι] [DecidableEq ι] (δ : ℝ)
    (hδ : δ < 1 - √S.rate) (ℓ : Nat)
    (hℓ : 1 - δ - S.rate < (ℓ + 1) * ((1 - δ) ^ 2 - S.rate)) :
    S.listSize ι δ ≤ ℓ := by
  classical
  refine Finset.sup_le fun words _ ↦ ncard_le_of_finset _ ℓ fun Fs hFs ↦ ?_
  have hmem (p) (hp : p ∈ Fs) : (∀ k, (p k).natDegree ≤ S.n) ∧ Agree S δ words p := hFs hp
  have hNpos : (0 : ℝ) < S.size := by exact_mod_cast Nat.two_pow_pos _
  have hrate : (S.n : ℝ) = S.size * S.rate := by rw [Setup.rate, mul_div_cancel₀ _ hNpos.ne']
  have ha : 0 ≤ 1 - δ := (Real.sqrt_nonneg _).trans (by linarith)
  have hsq : S.rate < (1 - δ) ^ 2 := Real.lt_sq_of_sqrt_lt (by linarith)
  have hrate0 : 0 ≤ S.rate := div_nonneg (Nat.cast_nonneg _) hNpos.le
  have hrate1 : S.rate ≤ 1 := div_le_one_of_le₀
    (by exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.le_add_right _ _)) hNpos.le
  -- `rate ≤ √rate < 1 - δ`, so the agreement `N (1 - δ)` exceeds `n`.
  have hnx : (S.n : ℝ) ≤ S.size * (1 - δ) := by
    rw [hrate]
    refine mul_le_mul_of_nonneg_left ?_ hNpos.le
    have hs := Real.sq_sqrt hrate0
    have hs1 : √S.rate ≤ 1 := Real.sqrt_le_one.mpr hrate1
    nlinarith [Real.sqrt_nonneg S.rate]
  set x : ℝ := S.size * (1 - δ)
  set A : Nat := ⌈x⌉₊
  have hxA : x ≤ A := Nat.le_ceil x
  have hpos : (S.size : ℝ) * S.n < x ^ 2 := by
    rw [hrate, show x ^ 2 = S.size * (S.size * (1 - δ) ^ 2) by ring]
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hsq hNpos) hNpos
  have hnA : S.n ≤ A := by exact_mod_cast hnx.trans hxA
  have hposA : S.size * S.n < A * A := by
    have : (S.size : ℝ) * S.n < A * A := by nlinarith [mul_nonneg hNpos.le ha]
    exact_mod_cast this
  have hcount := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le Fs (agreeSet S δ words)
    A S.n hnA (by rwa [Fintype.card_fin])
    (fun p hp ↦ Nat.ceil_le.mpr (agreeSet_spec S δ words p (hmem p hp).2).1)
    (fun p hp q hq hpq ↦ card_inter_agreeSet_le S δ words p q (hmem p hp) (hmem q hq) hpq)
  rw [Fintype.card_fin] at hcount
  have hreal : (Fs.card : ℝ) * ((A : ℝ) ^ 2 - S.size * S.n) ≤ S.size * (A - S.n) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcount
    rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hposA.le, Nat.cast_sub hnA, Nat.cast_mul,
      Nat.cast_mul, ← sq] at this
  -- `hℓ` times `N²`.
  have hℓ' : (S.size : ℝ) * (x - S.n) < (ℓ + 1) * (x ^ 2 - S.size * S.n) := by
    have := mul_lt_mul_of_pos_left hℓ (mul_pos hNpos hNpos)
    rw [hrate]
    linarith
  have := lt_of_johnson S.size S.n A x Fs.card ℓ (Nat.cast_nonneg _)
    (by exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.le_add_right _ _))
    (mul_nonneg hNpos.le ha) hxA hpos hℓ' hreal
  exact Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Below the unique-decoding radius `(1 - rate) / 2` the list has at most one tuple. -/
theorem listSize_le_one (S : Setup EF) (ι : Type) [Fintype ι] [DecidableEq ι] (δ : ℝ)
    (hδ : δ < (1 - S.rate) / 2) : S.listSize ι δ ≤ 1 := by
  classical
  refine Finset.sup_le fun words _ ↦ ncard_le_of_finset _ 1 fun Fs hFs ↦ ?_
  have hmem (p) (hp : p ∈ Fs) : (∀ k, (p k).natDegree ≤ S.n) ∧ Agree S δ words p := hFs hp
  refine Finset.card_le_one.mpr fun p hp q hq ↦ ?_
  by_contra hpq
  have hle := card_inter_agreeSet_le S δ words p q (hmem p hp) (hmem q hq) hpq
  have hunion := Finset.card_union_add_card_inter (agreeSet S δ words p) (agreeSet S δ words q)
  have huniv : (agreeSet S δ words p ∪ agreeSet S δ words q).card ≤ S.size :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have hP := (agreeSet_spec S δ words p (hmem p hp).2).1
  have hQ := (agreeSet_spec S δ words q (hmem q hq).2).1
  have hNpos : (0 : ℝ) < S.size := by exact_mod_cast Nat.two_pow_pos _
  have hrate : (S.n : ℝ) = S.size * S.rate := by rw [Setup.rate, mul_div_cancel₀ _ hNpos.ne']
  have hsum : ((agreeSet S δ words p).card : ℝ) + (agreeSet S δ words q).card ≤
      S.size + S.n := by
    have : (agreeSet S δ words p).card + (agreeSet S δ words q).card ≤ S.size + S.n := by omega
    exact_mod_cast this
  have : (S.size : ℝ) * S.rate < S.size * (2 * (1 - δ) - 1) :=
    mul_lt_mul_of_pos_left (by linarith) hNpos
  nlinarith

end CompStark.Sound
