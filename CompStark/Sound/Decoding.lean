/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Decoding: the claimed values are the decoded polynomials' values

Let `f` be an opened word over `𝔽` with point `z ∉ 𝔽` and claimed value `y`, and let its DEEP
component `(y - f(x)) / (z - x)` agree with a codeword `h` (degree below `n`) on a set `T` of
`|T| ≥ N (1 - δ)` points, `δ` within the unique-decoding radius, so `2 |T| ≥ N + n + 1`. Then:

1. `f` agrees on `T` with `P = y - (z - X) h`, of degree at most `n`, and `P(z) = y`
   (`eval_deepPoly_eq`, `z - x ≠ 0` as `x ∈ 𝔽`).
2. Projecting `P`'s coefficients to `𝔽` by an `𝔽`-linear left inverse of `𝔽 → 𝕂` gives a
   polynomial `Q ∈ 𝔽[X]` of degree at most `n` that agrees with `f` on `T` (`exists_baseAgree`).
3. The decoded polynomial `D` is at least as close to `f` as `Q`, so it disagrees with `f` on at
   most `N - |T|` points and agrees with `P` on at least `2 |T| - N ≥ n + 1` points of `T`
   (`card_agree_closest`). Both have degree at most `n`, so `P = D` and `y = P(z) = D(z)`
   (`claimed_eq_decoded`).

This needs `N > n`, i.e. a positive blowup: with `logBlowup = 0` every word on `L` is a codeword,
so every DEEP component is near the code whatever the claimed value, and `DecodingStep` fails
(`not_decodingStep`). `decodingStep` takes `0 < logBlowup` as a hypothesis.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4

/-! ### Polynomials over `𝕂` that take base values -/

/-- A polynomial over `𝕂` of degree at most `n` that takes values in `𝔽` at the points of `T`
agrees there with a polynomial over `𝔽` of degree at most `n`. -/
theorem exists_baseAgree {ι : Type} (pts : ι → 𝔽) (f : ι → 𝔽) (T : Finset ι) (n : Nat)
    (P : 𝕂[X]) (hP : P.natDegree ≤ n)
    (hT : ∀ i ∈ T, P.eval (algebraMap 𝔽 𝕂 (pts i)) = algebraMap 𝔽 𝕂 (f i)) :
    ∃ Q : 𝔽[X], Q ∈ degreeLT 𝔽 (n + 1) ∧ ∀ i ∈ T, Q.eval (pts i) = f i := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap 𝔽 𝕂).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap 𝔽 𝕂).injective)
  have hπa (a : 𝔽) : π (algebraMap 𝔽 𝕂 a) = a := LinearMap.congr_fun hπ a
  refine ⟨∑ k ∈ Finset.range (n + 1), C (π (P.coeff k)) * Polynomial.X ^ k, ?_, fun i hi ↦ ?_⟩
  · rw [degreeLT_succ_eq_degreeLE]
    refine Submodule.sum_mem _ fun k hk ↦ ?_
    rw [mem_degreeLE]
    exact (degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast Finset.mem_range_succ_iff.mp hk)
  · have h := congrArg π (hT i hi)
    rw [hπa, eval_eq_sum_range' (Nat.lt_succ_of_le hP), map_sum] at h
    rw [← h, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, ← map_pow, mul_comm (P.coeff k), ← Algebra.smul_def,
      LinearMap.map_smul, smul_eq_mul, mul_comm]

/-! ### The closest polynomial -/

/-- The closest polynomial has degree below `m`. -/
theorem closestPolynomial_mem {ι : Type} [Fintype ι] (m : Nat) (pts : ι → 𝔽) (w : ι → 𝔽) :
    closestPolynomial m pts w ∈ degreeLT 𝔽 m :=
  ((degreeLTEquiv 𝔽 m).symm _).2

/-- The closest polynomial is at least as close to the word as any polynomial of degree below
`m`. -/
theorem hammingDist_closestPolynomial_le {ι : Type} [Fintype ι] (m : Nat) (pts : ι → 𝔽)
    (w : ι → 𝔽) (Q : 𝔽[X]) (hQ : Q ∈ degreeLT 𝔽 m) :
    hammingDist w (fun i ↦ (closestPolynomial m pts w).eval (pts i)) ≤
      hammingDist w (fun i ↦ Q.eval (pts i)) := by
  have h := (Classical.choose_spec ((Finset.univ : Finset (Fin m → 𝔽)).exists_min_image
    (fun c ↦ hammingDist w fun i ↦ ((degreeLTEquiv 𝔽 m).symm c : 𝔽[X]).eval (pts i))
    Finset.univ_nonempty)).2 (degreeLTEquiv 𝔽 m ⟨Q, hQ⟩) (Finset.mem_univ _)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- If `Q` of degree below `m` agrees with `w` on `T`, the closest polynomial agrees with `w` on
at least `2 |T| - |ι|` points of `T`. -/
theorem card_agree_closest {ι : Type} [Fintype ι] [DecidableEq ι] (m : Nat) (pts : ι → 𝔽)
    (w : ι → 𝔽) (T : Finset ι) (Q : 𝔽[X]) (hQ : Q ∈ degreeLT 𝔽 m)
    (hT : ∀ i ∈ T, Q.eval (pts i) = w i) :
    2 * T.card ≤ Fintype.card ι +
      (T.filter fun i ↦ (closestPolynomial m pts w).eval (pts i) = w i).card := by
  have hle := hammingDist_closestPolynomial_le m pts w Q hQ
  have hQd : hammingDist w (fun i ↦ Q.eval (pts i)) ≤ (Finset.univ \ T).card := by
    refine Finset.card_le_card fun i hi ↦ ?_
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ i, fun hiT ↦ hi.2 (hT i hiT).symm⟩
  have hDd : (T.filter fun i ↦ ¬ (closestPolynomial m pts w).eval (pts i) = w i).card ≤
      hammingDist w (fun i ↦ (closestPolynomial m pts w).eval (pts i)) := by
    refine Finset.card_le_card fun i hi ↦ ?_
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ i, fun h ↦ hi.2 h.symm⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := T)
    (fun i ↦ (closestPolynomial m pts w).eval (pts i) = w i)
  have hc : (Finset.univ \ T).card + T.card = Fintype.card ι := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T), Finset.card_univ]
  omega

/-! ### One opened word -/

/-- `L`'s points are those of `basePoint` in `𝕂`. -/
theorem domain_eq (S : Setup) (i : S.Point) :
    S.domain i = algebraMap 𝔽 𝕂 (basePoint (S.logN + S.params.logBlowup) i) := by
  simp only [Setup.domain, cosetDomain,
    Domain.CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    Domain.CosetFftDomain.subgroupUnit, subgroupHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_mk0, Units.val_pow_eq_pow_val, IsUnit.unit_spec, toAdd_ofAdd, basePoint, lift,
    map_mul, map_pow]

/-- The polynomial `y - (z - X) h` takes the value `f(x)` where the DEEP component equals
`h(x)`. -/
theorem eval_deepPoly_eq (f z y x h : 𝕂) (hx : z - x ≠ 0) (hh : (y - f) / (z - x) = h) :
    (C y - (C z - Polynomial.X) * C h).eval x = f := by
  rw [div_eq_iff hx] at hh
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  rw [mul_comm, ← hh]
  ring

/-- `y - (z - X) h` has degree at most `n` for `h` of degree below `n`, `n ≥ 1`. -/
theorem natDegree_deepPoly_le (z y : 𝕂) (h : 𝕂[X]) (n : Nat) (hn : 1 ≤ n)
    (hh : h ∈ degreeLT 𝕂 n) : (C y - (C z - Polynomial.X) * h).natDegree ≤ n := by
  have hzX : (C z - Polynomial.X).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_C]; exact Nat.zero_le 1) natDegree_X_le)
  have hh' : h.natDegree + 1 ≤ n := by
    rcases eq_or_ne h 0 with rfl | h0
    · rw [natDegree_zero]
      exact hn
    · exact (natDegree_lt_iff_degree_lt h0).mpr (mem_degreeLT.mp hh)
  refine (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_C]; exact Nat.zero_le n) ?_)
  exact (natDegree_mul_le).trans (by omega)

/-- The closeness `|T| ≥ N (1 - δ)` within the unique-decoding radius gives
`2 |T| ≥ N + n + 1`, when `N > n`. -/
theorem two_mul_card_ge (S : Setup) (hN : S.n < S.size) (δ : NNReal)
    (hδ : δ ≤ S.uniqueDecodingRadius) (t : Nat) (ht : (t : ℝ) ≥ S.size * (1 - δ)) :
    S.size + S.n + 1 ≤ 2 * t := by
  have hNpos : (0 : ℝ) < S.size := by exact_mod_cast Nat.two_pow_pos _
  have hδ' : (δ : ℝ) ≤ ((S.size - S.n - 1 : Nat) : ℝ) / 2 / S.size := by
    have := NNReal.coe_le_coe.mpr hδ
    simpa only [Setup.uniqueDecodingRadius, NNReal.coe_div, NNReal.coe_natCast,
      NNReal.coe_ofNat] using this
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), le_div_iff₀ hNpos] at hδ'
  have : (S.size : ℝ) + S.n + 1 ≤ 2 * t := by nlinarith
  exact_mod_cast this

/-- A word whose DEEP component at `z ∉ 𝔽` with claimed value `y` is `δ`-near the code, `δ`
within the unique-decoding radius and `N > n`, has `y` as its decoded polynomial's value at
`z`. -/
theorem claimed_eq_decoded (S : Setup) (hN : S.n < S.size) (δ : NNReal)
    (hδ : δ ≤ S.uniqueDecodingRadius) (f : S.Point → 𝔽) (z y : 𝕂) (hz : OutsideBase z)
    (hnear : Near S δ (deepComponent S f z y)) : y = aeval z (decoded S f) := by
  classical
  obtain ⟨T, hT, u, hu, hTu⟩ := hnear
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hu
  set pts : S.Point → 𝔽 := fun i ↦ basePoint (S.logN + S.params.logBlowup) i
  set P : 𝕂[X] := C y - (C z - Polynomial.X) * h
  have hPdeg : P.natDegree ≤ S.n := natDegree_deepPoly_le z y h S.n Nat.one_le_two_pow hh
  have hPT (i) (hi : i ∈ T) : P.eval (algebraMap 𝔽 𝕂 (pts i)) = algebraMap 𝔽 𝕂 (f i) := by
    have hx : z - algebraMap 𝔽 𝕂 (pts i) ≠ 0 := fun h0 ↦ hz ⟨pts i, (sub_eq_zero.mp h0).symm⟩
    have hdeep := hTu i hi
    simp only [deepComponent, ReedSolomon.evalOnPoints, LinearMap.coe_mk,
      AddHom.coe_mk, Function.Embedding.coeFn_mk, domain_eq] at hdeep
    have := eval_deepPoly_eq _ z y _ _ hx hdeep
    simpa only [P, eval_sub, eval_mul, eval_C, eval_X] using this
  obtain ⟨Q, hQ, hQT⟩ := exists_baseAgree pts f T S.n P hPdeg hPT
  set D := decoded S f
  set A := T.filter fun i ↦ D.eval (pts i) = f i
  have hcard : 2 * T.card ≤ S.size + A.card := by
    have := card_agree_closest (S.n + 1) pts f T Q hQ hQT
    rwa [Fintype.card_fin] at this
  have h2 := two_mul_card_ge S hN δ hδ T.card hT
  have hDdeg : D.natDegree ≤ S.n := by
    have := closestPolynomial_mem (S.n + 1) pts f
    rwa [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le] at this
  have hPD : P = D.map (algebraMap 𝔽 𝕂) := by
    have hinj : Set.InjOn (fun i ↦ algebraMap 𝔽 𝕂 (pts i)) A := by
      intro i _ j _ hij
      exact (S.domain).injective (by rw [domain_eq, domain_eq]; exact hij)
    refine eq_of_degree_sub_lt_of_eval_finset_eq (A.image fun i ↦ algebraMap 𝔽 𝕂 (pts i)) ?_ ?_
    · rw [Finset.card_image_of_injOn hinj]
      refine (degree_le_natDegree).trans_lt ?_
      have : (P - D.map (algebraMap 𝔽 𝕂)).natDegree ≤ S.n :=
        (natDegree_sub_le _ _).trans (max_le hPdeg (natDegree_map_le.trans hDdeg))
      exact_mod_cast (show _ < A.card by omega)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at hi
      rw [hPT i hi.1, eval_map_algebraMap, aeval_algebraMap_apply, coe_aeval_eq_eval, hi.2]
  have hPz : P.eval z = y := by
    simp only [P, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul, sub_zero]
  rw [← hPz, hPD, eval_map_algebraMap]

/-! ### The opened words -/

/-- `ζ ω_n` lies outside the base field with `ζ`. -/
theorem outsideBase_mul_rootOfUnity (S : Setup) (ζ : 𝕂) (hζ : OutsideBase ζ) :
    OutsideBase (ζ * rootOfUnity S.logN) := by
  rintro ⟨a, ha⟩
  set w : 𝔽 := Montgomery.Native32.FastField.toField (twoAdicGen S.logN)
  have hw : rootOfUnity S.logN = algebraMap 𝔽 𝕂 w := rfl
  have hω : rootOfUnity S.logN ≠ 0 :=
    (isPrimitiveRoot_lift S.logN (by have := S.valid.twoAdic; omega)).ne_zero
      (Nat.two_pow_pos S.logN).ne'
  refine hζ ⟨a * w⁻¹, ?_⟩
  rw [map_mul, map_inv₀, ha, ← hw]
  exact mul_inv_cancel_right₀ hω ζ

/-- **The decoding step**, for a positive blowup. -/
theorem decodingStep (S : Setup) (hblowup : 0 < S.params.logBlowup) : DecodingStep S := by
  intro δ hδ prover α ζ hζ hnear
  have hN : S.n < S.size :=
    Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_add_of_pos_right hblowup)
  have hdec := claimed_eq_decoded S hN δ hδ
  have hζω := outsideBase_mul_rootOfUnity S ζ hζ
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, fun c e ↦ ?_⟩
  · refine hdec (prover.trace j) ζ _ hζ (hnear (prover.trace j, ζ, _) ?_)
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  · refine hdec (prover.trace j) _ _ hζω (hnear (prover.trace j, ζ * rootOfUnity S.logN, _) ?_)
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  · refine hdec (prover.quotient α c e) ζ _ hζ (hnear (prover.quotient α c e, ζ, _) ?_)
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, List.mem_finRange c,
      List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩⟩)

/-! ### Without blowup -/

/-- `𝕂` has elements outside the base field. -/
theorem exists_outsideBase : ∃ ζ : 𝕂, OutsideBase ζ := by
  by_contra h
  have hs : Function.Surjective (algebraMap 𝔽 𝕂) := fun ζ ↦
    not_not.mp fun hζ ↦ h ⟨ζ, hζ⟩
  have hle := Fintype.card_le_of_surjective _ hs
  rw [CompPoly.Extension.Ext.card_ext] at hle
  simp only [CompPoly.Extension.BinomialParams.toExtensionParams_q, KoalaBear.ext4Params_q,
    CompPoly.Extension.BinomialParams.toExtensionParams_d, KoalaBear.ext4Params_d, ZMod.card] at hle
  have h1 : 1 < KoalaBear.fieldSize := by decide
  generalize KoalaBear.fieldSize = q at hle h1
  have := Nat.pow_lt_pow_right h1 (by norm_num : 1 < 4)
  rw [pow_one] at this
  omega

/-- Without blowup, `N = n` and every word on `L` is a codeword. -/
theorem near_zero_of_logBlowup_eq_zero (S : Setup) (h0 : S.params.logBlowup = 0)
    (w : S.Point → 𝕂) : Near S 0 w := by
  classical
  have hinj : Set.InjOn (fun i : S.Point ↦ S.domain i) (Finset.univ : Finset S.Point) :=
    fun i _ j _ hij ↦ (S.domain).injective hij
  refine ⟨Finset.univ, ?_, w, Submodule.mem_map.mpr ⟨Lagrange.interpolate Finset.univ
    (fun i : S.Point ↦ S.domain i) w, ?_, funext fun i ↦ ?_⟩, fun _ _ ↦ rfl⟩
  · simp only [Finset.card_univ, Fintype.card_fin, sub_zero, mul_one,
      Nat.cast_pow, Nat.cast_ofNat, ge_iff_le, le_refl]
  · rw [mem_degreeLT]
    have := Lagrange.degree_interpolate_lt (r := w) hinj
    rw [Finset.card_univ, Fintype.card_fin] at this
    have hn : S.n = 2 ^ (S.logN + S.params.logBlowup) := by rw [h0, Nat.add_zero]
    rwa [hn]
  · exact Lagrange.eval_interpolate_at_node w hinj (Finset.mem_univ i)

/-- Without blowup, `DecodingStep` fails: a prover claiming a wrong value is near the code. -/
theorem not_decodingStep (S : Setup) (h0 : S.params.logBlowup = 0) : ¬ DecodingStep S := by
  intro hD
  obtain ⟨ζ, hζ⟩ := exists_outsideBase
  let y : 𝕂 := aeval ζ (decoded S fun _ ↦ 0) + 1
  let prover : Prover S :=
    { trace := fun _ _ ↦ 0, quotient := fun _ _ _ _ ↦ 0,
      openings := fun _ _ ↦ ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ _ ↦ y⟩ }
  have c0 : Fin S.chunks := ⟨0, Nat.two_pow_pos _⟩
  have h := (hD 0 zero_le prover 0 ζ hζ fun _ _ ↦
    near_zero_of_logBlowup_eq_zero S h0 _).2.2 c0 0
  exact one_ne_zero (add_eq_left.mp h)

end CompStark.Sound
