/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.CurveBW
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-! # Mutual correlated agreement of the powers curve below the unique-decoding radius

`mcaError_powers_le`: for a Reed–Solomon code `C` of length `n` and a radius `δ` within its unique
decoding radius, the mutual correlated-agreement error of the powers generator
`x ↦ (1, x, …, x^k)` is at most `k n / |F|` ([BCIKS20] Theorem 1.6, unique-decoding case).

Fix words `U₀, …, U_k` and call `x` bad if `w_x = ∑ⱼ xʲ Uⱼ` agrees with a codeword `c` on a set
`T` of at least `(1 - δ) n` points on which some `Uⱼ` agrees with no codeword. If more than `k n`
values are bad, then more than `k n` points of the curve are `δ`-close to `C`, and correlated
agreement for curves (`curve_correlatedAgreement`) gives codewords `vⱼ` that agree with the `Uⱼ`
off a set `D` of at most `δ n` coordinates. For a bad `x`, `c` and `V = ∑ⱼ xʲ vⱼ` agree on `T \ D`,
of at least `n - 2δn ≥ deg` points, so `c = V`. Some point `i ∈ T` lies in `D`, as otherwise
every `Uⱼ = vⱼ` on `T`; there `∑ⱼ xʲ (Uⱼ(i) - vⱼ(i)) = 0`, so `x` is a root of a nonzero
polynomial of degree at most `k` attached to `i ∈ D`. Hence at most `k |D| ≤ k n` values are bad.
-/

@[expose] public section
namespace CompStark.Sound
open NNReal Finset Polynomial ProximityGap CurveBW CoreDefinitions LinearCode Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]

omit [Fintype F] [NeZero n] in
/-- A codeword of the Reed–Solomon code of degree below `deg` that vanishes on `deg` points is
zero. -/
theorem eq_zero_of_vanish {deg : ℕ} {domain : Fin n ↪ F} {c : Fin n → F}
    (hc : c ∈ ReedSolomon.code domain deg) (A : Finset (Fin n)) (hA : deg ≤ A.card)
    (hz : ∀ i ∈ A, c i = 0) : c = 0 := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hc
  have hp0 : p = 0 := by
    by_contra hne
    have hdeg : p.natDegree < deg := (natDegree_lt_iff_degree_lt hne).mpr (mem_degreeLT.mp hp)
    have hsub : A.map domain ⊆ p.roots.toFinset := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
      rw [Multiset.mem_toFinset, mem_roots hne]
      exact hz i hi
    have := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    rw [Finset.card_map] at this
    exact absurd ((this.trans (card_roots' p)).trans_lt hdeg) (not_lt.mpr hA)
  subst hp0
  exact map_zero _

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- The word on a powers curve at `x` is the curve point of ArkLib's `polynomialCurveEval`. -/
theorem powers_sum_eq {k : ℕ} (U : Fin (k + 1) → Fin n → F) (x : F) :
    (fun i ↦ ∑ j, univariatePowersGenerator F k x j • U j i) =
      Curve.polynomialCurveEval (F := F) (A := F) U x := by
  funext i
  simp only [Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply]

/-- At most `k n` values `x` make the powers curve through `U` an MCA event. -/
theorem card_isMCA_powers_le {deg : ℕ} (hdeg_pos : 0 < deg) (hdeg_le : deg ≤ n)
    {domain : Fin n ↪ F} (k : ℕ) {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ReedSolomon.code domain deg : Set (Fin n → F)))
    (U : Fin (k + 1) → Fin n → F) [DecidablePred fun x ↦
      IsMCA (univariatePowersGenerator F k) (ReedSolomon.code domain deg) x U δ] :
    (Finset.univ.filter fun x ↦
      IsMCA (univariatePowersGenerator F k) (ReedSolomon.code domain deg) x U δ).card ≤
      k * n := by
  classical
  set B := Finset.univ.filter fun x ↦
    IsMCA (univariatePowersGenerator F k) (ReedSolomon.code domain deg) x U δ
  set e : ℕ := Nat.floor (δ * n)
  have : NeZero deg := ⟨by omega⟩
  have hBW : 2 * e < n - deg + 1 := by
    simpa [e] using ProximityGap.RS_BW_bound_of_le_relUDR (deg := deg) (domain := domain)
      (δ := δ) (by simpa using hdeg_le) hδ
  -- An MCA event's agreement set has at least `n - e` points.
  have hTcard {T : Finset (Fin n)} (hT : (T.card : ℝ) ≥ (Fintype.card (Fin n) : ℝ) * (1 - δ)) :
      n - e ≤ T.card := by
    apply (Code.relDist_floor_bound_iff_complement_bound n T.card δ).2
    rw [Fintype.card_fin] at hT
    rcases le_total δ 1 with h1 | h1
    · rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub h1, NNReal.coe_natCast,
        NNReal.coe_natCast, NNReal.coe_one, mul_comm]
      exact hT
    · rw [tsub_eq_zero_of_le h1, zero_mul]
      exact zero_le
  by_cases hB : B.card ≤ k * n
  · exact hB
  -- More than `k n` bad values: the words have correlated agreement.
  have hsub : B ⊆ coeffs_of_close_proximity_curve (F := F) δ U
      (ReedSolomon.toFinset domain deg) := by
    intro x hx
    obtain ⟨T, hT, hmem, -⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨c, hc, hcv⟩ := Submodule.mem_map.mp hmem
    simp only [coeffs_of_close_proximity_curve, Set.mem_toFinset, Set.mem_ofPred_eq]
    have hset : (ReedSolomon.toFinset domain deg : Set (Fin n → F)) =
        (ReedSolomon.code domain deg : Set (Fin n → F)) := by
      simp only [ReedSolomon.toFinset, ReedSolomon.RScodeSet, Set.coe_toFinset]
    rw [hset]
    refine le_trans (Code.relDistFromCode_le_relDist_to_mem
      (u := Curve.polynomialCurveEval (F := F) (A := F) U x)
      (C := (ReedSolomon.code domain deg : Set (Fin n → F))) (v := c) hc) ?_
    have hle : δᵣ(Curve.polynomialCurveEval (F := F) (A := F) U x, c) ≤ δ := by
      rw [Code.relCloseToWord_iff_exists_agreementCols]
      refine ⟨T, by rw [Fintype.card_fin]; exact hTcard hT, fun i ↦ ⟨fun hi ↦ ?_, fun hne hi ↦
        hne ?_⟩⟩ <;>
      · have h := congrFun hcv ⟨i, hi⟩
        simp only [LinearMap.funLeft_apply, projectedWord, Set.domRestrict_apply] at h
        rw [← powers_sum_eq]
        exact h.symm
    exact_mod_cast hle
  obtain ⟨-, v, hv, -, hD⟩ := curve_correlatedAgreement (l := k) hdeg_pos hdeg_le hδ
    (u := U) (by rw [mul_comm]; exact (not_le.mp hB).trans_le (Finset.card_le_card hsub))
  set D : Finset (Fin n) := Finset.univ.filter fun i ↦ ∃ j, U j i ≠ v j i
  have hDe : D.card ≤ e := Nat.le_floor (by exact_mod_cast hD)
  -- Each bad value is a root of the nonzero polynomial of some coordinate of `D`.
  let p (i : Fin n) : F[X] := curveParamPoly (fun j i ↦ U j i - v j i) i
  have hp0 {i : Fin n} (hi : i ∈ D) : p i ≠ 0 := by
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
    intro h0
    have hc := congrArg (fun q ↦ q.coeff j) h0
    simp only [p, curveParamPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
    rw [Finset.sum_eq_single j (fun b _ hb ↦ by
      rw [ite_eq_right (fun h ↦ hb (Fin.ext h.symm)), mul_zero]) (by simp)] at hc
    simp only [ite_true, mul_one] at hc
    exact hj (sub_eq_zero.mp hc)
  have hroots : B ⊆ D.biUnion fun i ↦ (p i).roots.toFinset := by
    intro x hx
    obtain ⟨T, hT, hmem, j, hj⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨c, hc, hcv⟩ := Submodule.mem_map.mp hmem
    have hcT (i : Fin n) (hi : i ∈ T) :
        c i = Curve.polynomialCurveEval (F := F) (A := F) U x i := by
      have h := congrFun hcv ⟨i, hi⟩
      simp only [LinearMap.funLeft_apply, projectedWord, Set.domRestrict_apply] at h
      rw [← powers_sum_eq]
      exact h
    set V := Curve.polynomialCurveEval (F := F) (A := F) v x
    have hV : V ∈ ReedSolomon.code domain deg :=
      Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hv j)
    have hUV (i : Fin n) (hi : i ∉ D) :
        Curve.polynomialCurveEval (F := F) (A := F) U x i = V i := by
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_not] at hi
      simp only [V, Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, hi]
    -- `c = V`: they agree on `T \ D`, of at least `deg` points.
    have hcV : c = V := by
      have h0 := eq_zero_of_vanish (Submodule.sub_mem _ hc hV) (T \ D) (by
        have h1 := hTcard hT
        have h2 := Finset.le_card_sdiff D T
        omega) (fun i hi ↦ by
          obtain ⟨hiT, hiD⟩ := Finset.mem_sdiff.mp hi
          rw [Pi.sub_apply, hcT i hiT, hUV i hiD, sub_self])
      exact sub_eq_zero.mp h0
    -- Some point of `T` lies in `D`.
    obtain ⟨i, hiT, hiD⟩ : ∃ i ∈ T, i ∈ D := by
      by_contra hall
      push Not at hall
      refine hj (Submodule.mem_map.mpr ⟨v j, hv j, funext fun i ↦ ?_⟩)
      have hi := hall i.1 i.2
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_not] at hi
      simp only [LinearMap.funLeft_apply, projectedWord, Set.domRestrict_apply, hi]
    refine Finset.mem_biUnion.mpr ⟨i, hiD, ?_⟩
    rw [Multiset.mem_toFinset, mem_roots (hp0 hiD), IsRoot.def, curveParamPoly_eval]
    have h := hcT i hiT
    rw [hcV] at h
    simp only [V, Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, h, sub_self]
  calc B.card ≤ (D.biUnion fun i ↦ (p i).roots.toFinset).card := Finset.card_le_card hroots
    _ ≤ ∑ i ∈ D, (p i).roots.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ D, k := Finset.sum_le_sum fun i _ ↦
        ((Multiset.toFinset_card_le _).trans (card_roots' _)).trans (curveParamPoly_natDegree_le _ _)
    _ = D.card * k := Finset.sum_const_nat fun _ _ ↦ rfl
    _ ≤ k * n := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left k ((Finset.card_le_univ D).trans_eq (Fintype.card_fin n))

/-- **Powers MCA below the unique-decoding radius** ([BCIKS20] Theorem 1.6, unique-decoding
case): the mutual correlated-agreement error of `x ↦ (1, x, …, x^k)` for a Reed–Solomon code of
length `n` is at most `k n / |F|`. -/
theorem mcaError_powers_le [SampleableType F] {deg : ℕ} (hdeg_pos : 0 < deg) (hdeg_le : deg ≤ n)
    {domain : Fin n ↪ F} (k : ℕ) {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ReedSolomon.code domain deg : Set (Fin n → F))) :
    mcaError (univariatePowersGenerator F k) (ReedSolomon.code domain deg) δ ≤
      ((k * n : ℕ) : ENNReal) / Fintype.card F := by
  classical
  refine iSup_le fun U ↦ ?_
  rw [SampleableType.prEvent_uniformSample]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (card_isMCA_powers_le hdeg_pos hdeg_le k hδ U))
    _

end CompStark.Sound
