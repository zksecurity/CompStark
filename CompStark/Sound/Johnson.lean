/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Decoding
public import Mathlib.Algebra.Order.Chebyshev

/-! # The Johnson bound on the list size

`Setup.listSize S ι δ` counts tuples of polynomials of degree at most `n` agreeing with one tuple
of words on a common set of at least `(1 - δ) N` points. Two distinct such tuples agree on at most
`n` points of `L` (`card_le_of_eqOn`), so their agreement sets meet in at most `n` points. The
pairwise-intersection count (`card_mul_le_of_inter_card_le`, after ArkLib's
`Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le`, with a real agreement) then bounds the
list by `(a - rate) / (a² - rate)` for `a = 1 - δ > √rate` (`listSize_le_johnson`).
For example `rate = 1/16`, `δ = 1/2` gives `7/3`, so at most `2`.

Below the unique-decoding radius `(1 - rate) / 2` two agreement sets meet in more than `n` points,
so the list has at most one element (`listSize_le_one`).
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

local notation "𝔽" => KoalaBear.Field

/-- The points of `L` in `𝔽` are distinct. -/
theorem basePoint_injective (S : Setup) :
    Function.Injective fun i : S.Point ↦ basePoint (S.logN + S.params.logBlowup) i := by
  intro i j h
  apply S.domain.injective
  rw [domain_eq, domain_eq]
  exact congrArg (algebraMap 𝔽 KoalaBear.Ext4) h

/-- Distinct tuples of polynomials of degree at most `n` agree on at most `n` points of `L`. -/
theorem card_le_of_eqOn (S : Setup) {ι : Type} (p q : ι → 𝔽[X])
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

/-- The Cauchy–Schwarz incidence count behind the Johnson bound (after ArkLib's
`Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le`, with a real agreement `a`): `L` sets of
at least `a` points of an `N`-point type, pairwise meeting in at most `d` points, `d ≤ a`, satisfy
`L (a² - N d) ≤ N (a - d)`. -/
theorem card_mul_le_of_inter_card_le {κ ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Finset κ) (S : κ → Finset ι) (a d : ℝ) (hd : 0 ≤ d) (hda : d ≤ a)
    (hclose : ∀ x ∈ T, a ≤ (S x).card)
    (hpair : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → (((S x) ∩ (S y)).card : ℝ) ≤ d) :
    (T.card : ℝ) * (a ^ 2 - Fintype.card ι * d) ≤ Fintype.card ι * (a - d) := by
  classical
  set L : ℝ := (T.card : ℝ)
  set n : ℝ := (Fintype.card ι : ℝ)
  -- `deg i` counts the sets containing `i`.
  let deg (i : ι) : ℝ := ∑ x ∈ T, if i ∈ S x then (1 : ℝ) else 0
  set tot : ℝ := ∑ x ∈ T, ((S x).card : ℝ)
  set sq2 : ℝ := ∑ x ∈ T, ∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ)
  have hcard (s : Finset ι) : (s.card : ℝ) = ∑ i : ι, if i ∈ s then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hsum : tot = ∑ i : ι, deg i := by
    simp only [tot, deg, hcard]
    exact Finset.sum_comm
  have hsquares : sq2 = ∑ i : ι, deg i ^ 2 := by
    simp only [sq2, deg, hcard, sq, Finset.sum_mul_sum, Finset.mem_inter, ite_zero_mul_ite_zero,
      mul_one]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm
  have hZlower : L * a ≤ tot := by
    have h := Finset.sum_le_sum hclose
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hQupper : sq2 ≤ tot + L * (L - 1) * d := by
    have hrow (x) (hx : x ∈ T) :
        ∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ) ≤ (S x).card + (L - 1) * d := by
      rw [← Finset.add_sum_erase T _ hx, Finset.inter_self]
      have h := Finset.sum_le_card_nsmul (T.erase x) (fun y ↦ (((S x) ∩ (S y)).card : ℝ)) d
        fun y hy ↦ hpair x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      rw [nsmul_eq_mul, Finset.card_erase_of_mem hx,
        Nat.cast_sub (Finset.card_pos.mpr ⟨x, hx⟩), Nat.cast_one] at h
      linarith
    calc sq2 ≤ ∑ x ∈ T, (((S x).card : ℝ) + (L - 1) * d) := Finset.sum_le_sum hrow
      _ = tot + L * (L - 1) * d := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
  have hCauchy : tot ^ 2 ≤ n * sq2 := by
    rw [hsum, hsquares]
    exact sq_sum_le_card_mul_sum_sq
  have hn : 0 ≤ n := Nat.cast_nonneg _
  rcases (show (0 : ℝ) ≤ L from Nat.cast_nonneg _).eq_or_lt with hL | hL
  · rw [← hL, zero_mul]
    exact mul_nonneg hn (sub_nonneg.mpr hda)
  by_cases hsmall : L * a ≤ n
  · have hL1 : 1 ≤ L := by
      have : 1 ≤ T.card := by
        have h : (0 : ℝ) < (T.card : ℝ) := hL
        exact_mod_cast h
      show (1 : ℝ) ≤ (T.card : ℝ)
      exact_mod_cast this
    have ha : 0 ≤ a := hd.trans hda
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hsmall),
      mul_nonneg (mul_nonneg hn hd) (sub_nonneg.mpr hL1)]
  · push Not at hsmall
    have hmono : (L * a) ^ 2 - n * (L * a) ≤ tot ^ 2 - n * tot := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hZlower) (by linarith : 0 ≤ tot + L * a - n)]
    have hkey : tot ^ 2 - n * tot ≤ n * (L * (L - 1) * d) := by
      nlinarith [mul_le_mul_of_nonneg_left hQupper hn]
    have : L * (L * (a ^ 2 - n * d)) ≤ L * (n * (a - d)) := by nlinarith
    exact le_of_mul_le_mul_left this hL

/-- Each tuple in the list, with an agreement set. -/
noncomputable def agreeSet (S : Setup) {ι : Type} (δ : ℝ) (words : ι → S.Point → 𝔽)
    (p : ι → 𝔽[X]) : Finset S.Point :=
  open Classical in if h : Agree S δ words p then h.choose else ∅

theorem agreeSet_spec (S : Setup) {ι : Type} (δ : ℝ) (words : ι → S.Point → 𝔽)
    (p : ι → 𝔽[X]) (h : Agree S δ words p) :
    ((agreeSet S δ words p).card : ℝ) ≥ S.size * (1 - δ) ∧
      ∀ i ∈ agreeSet S δ words p, ∀ k,
        words k i = (p k).eval (basePoint (S.logN + S.params.logBlowup) i) := by
  simp only [agreeSet, h, ↓reduceDIte]
  exact h.choose_spec

/-- The agreement sets of two distinct tuples in the list meet in at most `n` points. -/
theorem card_inter_agreeSet_le (S : Setup) {ι : Type} (δ : ℝ) (words : ι → S.Point → 𝔽)
    (p q : ι → 𝔽[X]) (hp : (∀ k, (p k).natDegree ≤ S.n) ∧ Agree S δ words p)
    (hq : (∀ k, (q k).natDegree ≤ S.n) ∧ Agree S δ words q) (hpq : p ≠ q) :
    (agreeSet S δ words p ∩ agreeSet S δ words q).card ≤ S.n := by
  refine card_le_of_eqOn S p q hp.1 hq.1 hpq _ fun i hi k ↦ ?_
  rw [Finset.mem_inter] at hi
  rw [← (agreeSet_spec S δ words p hp.2).2 i hi.1 k, (agreeSet_spec S δ words q hq.2).2 i hi.2 k]

/-- The Johnson bound: for `δ < 1 - √rate`, the list has at most `ℓ` tuples once
`(1 - δ - rate) / ((1 - δ)² - rate) < ℓ + 1`. -/
theorem listSize_le_johnson (S : Setup) (ι : Type) [Fintype ι] [DecidableEq ι] (δ : ℝ)
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
  have hcount := card_mul_le_of_inter_card_le Fs (agreeSet S δ words) (S.size * (1 - δ)) S.n
    (Nat.cast_nonneg _) hnx (fun p hp ↦ (agreeSet_spec S δ words p (hmem p hp).2).1)
    (fun p hp q hq hpq ↦ by
      exact_mod_cast card_inter_agreeSet_le S δ words p q (hmem p hp) (hmem q hq) hpq)
  rw [Fintype.card_fin] at hcount
  -- Divided by `N²`, `hcount` reads `|Fs| ((1 - δ)² - rate) ≤ 1 - δ - rate`.
  have hN2 : (0 : ℝ) < S.size * S.size := mul_pos hNpos hNpos
  have hlt : (Fs.card : ℝ) * (S.size * S.size * ((1 - δ) ^ 2 - S.rate)) <
      (ℓ + 1) * (S.size * S.size * ((1 - δ) ^ 2 - S.rate)) := by
    have := mul_lt_mul_of_pos_left hℓ hN2
    rw [hrate] at hcount
    nlinarith
  have := lt_of_mul_lt_mul_right hlt (mul_pos hN2 (by linarith)).le
  exact Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Below the unique-decoding radius `(1 - rate) / 2` the list has at most one tuple. -/
theorem listSize_le_one (S : Setup) (ι : Type) [Fintype ι] [DecidableEq ι] (δ : ℝ)
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
