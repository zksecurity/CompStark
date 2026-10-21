/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Decoding: the claimed values are those of polynomials close to the words

Let the DEEP components of the opened words agree with codewords on a common set of at least
`N (1 - δ) + 2` points, `δ < 1 - rate`. Drop the at most two points of `L` equal to `ζ` or
`ζ ω_n`, where the DEEP quotients divide by zero: the rest, `T`, has `|T| ≥ N (1 - δ) > n` points
(`card_le_card_filter_add_two`). For an opened word `f` with point `z` and claimed value `y`,
whose DEEP component `(y - f(x)) / (z - x)` agrees on `T` with a codeword `h` (degree below `n`):

1. `f` agrees on `T` with `P = y - (z - X) h`, of degree at most `n`, and `P(z) = y`
   (`eval_deepPoly_eq`, `z - x ≠ 0` for `x ∈ T`).
2. Projecting `P`'s coefficients to `F` gives `Q ∈ F[X]` of degree at most `n` that agrees with
   `f` on `T` (`exists_baseAgree`); `P` and `Q` agree on `|T| > n` points, so `P = Q` and
   `Q(z) = y` (`exists_basePoly`).

A trace column is opened at `ζ` and `ζ ω_n`; both polynomials agree with it on `T`, so they are
equal (`eq_of_agree`). No unique decoding is needed.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Polynomials over `𝕂` that take base values -/

/-- A polynomial over `𝕂` of degree at most `n` that takes values in `F` at the points of `T`
agrees there with a polynomial over `F` of degree at most `n`. -/
theorem exists_baseAgree {ι : Type} (pts : ι → F) (f : ι → F) (T : Finset ι) (n : Nat)
    (P : 𝕂[X]) (hP : P.natDegree ≤ n)
    (hT : ∀ i ∈ T, P.eval (algebraMap F 𝕂 (pts i)) = algebraMap F 𝕂 (f i)) :
    ∃ Q : F[X], Q ∈ degreeLT F (n + 1) ∧ ∀ i ∈ T, Q.eval (pts i) = f i := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F 𝕂).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F 𝕂).injective)
  have hπa (a : F) : π (algebraMap F 𝕂 a) = a := LinearMap.congr_fun hπ a
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

/-! ### One opened word -/

/-- `L`'s points are those of `basePoint` in `𝕂`. -/
theorem domain_eq (S : Setup EF) (i : S.Point) :
    S.domain i = algebraMap F 𝕂 (basePoint (S.logN + S.params.logBlowup) i) := by
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

/-- Two polynomials over `𝕂` of degree at most `n` that agree at the points of `T`, `|T| > n`,
are equal. -/
theorem eq_of_agree (S : Setup EF) (T : Finset S.Point) (hT : S.n < T.card) (P Q : 𝕂[X])
    (hP : P.natDegree ≤ S.n) (hQ : Q.natDegree ≤ S.n)
    (h : ∀ i ∈ T, P.eval (S.domain i) = Q.eval (S.domain i)) : P = Q := by
  classical
  refine eq_of_degree_sub_lt_of_eval_finset_eq (T.image fun i ↦ S.domain i) ?_ ?_
  · rw [Finset.card_image_of_injective _ (S.domain).injective]
    refine (degree_le_natDegree).trans_lt ?_
    have : (P - Q).natDegree ≤ S.n := (natDegree_sub_le _ _).trans (max_le hP hQ)
    exact_mod_cast (show _ < T.card by omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact h i hi

/-- A word whose DEEP component at `z` with claimed value `y` agrees with a codeword on `T`,
`|T| > n` and `z` off `T`, agrees on `T` with a polynomial over `F` of degree at most `n` whose
value at `z` is `y`. -/
theorem exists_basePoly (S : Setup EF) (T : Finset S.Point) (hT : S.n < T.card)
    (f : S.Point → F) (z y : 𝕂) (hz : ∀ i ∈ T, z ≠ S.domain i)
    (hnear : ∃ u ∈ S.code, ∀ i ∈ T, deepComponent S f z y i = u i) :
    ∃ Q : F[X], Q.natDegree ≤ S.n ∧
      (∀ i ∈ T, f i = Q.eval (basePoint (S.logN + S.params.logBlowup) i)) ∧ aeval z Q = y := by
  obtain ⟨u, hu, hTu⟩ := hnear
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hu
  set pts : S.Point → F := fun i ↦ basePoint (S.logN + S.params.logBlowup) i
  set P : 𝕂[X] := C y - (C z - Polynomial.X) * h
  have hPdeg : P.natDegree ≤ S.n := natDegree_deepPoly_le z y h S.n Nat.one_le_two_pow hh
  have hPT (i) (hi : i ∈ T) : P.eval (algebraMap F 𝕂 (pts i)) = algebraMap F 𝕂 (f i) := by
    have hx : z - algebraMap F 𝕂 (pts i) ≠ 0 := sub_ne_zero.mpr (domain_eq S i ▸ hz i hi)
    have hdeep := hTu i hi
    simp only [deepComponent, ReedSolomon.evalOnPoints, LinearMap.coe_mk,
      AddHom.coe_mk, Function.Embedding.coeFn_mk, domain_eq] at hdeep
    have := eval_deepPoly_eq _ z y _ _ hx hdeep
    simpa only [P, eval_sub, eval_mul, eval_C, eval_X] using this
  obtain ⟨Q, hQ, hQT⟩ := exists_baseAgree pts f T S.n P hPdeg hPT
  have hQdeg : Q.natDegree ≤ S.n := by
    rwa [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le] at hQ
  have hPQ : P = Q.map (algebraMap F 𝕂) := by
    refine eq_of_agree S T hT _ _ hPdeg (natDegree_map_le.trans hQdeg) fun i hi ↦ ?_
    rw [domain_eq, hPT i hi, eval_map_algebraMap, aeval_algebraMap_apply, coe_aeval_eq_eval,
      hQT i hi]
  refine ⟨Q, hQdeg, fun i hi ↦ (hQT i hi).symm, ?_⟩
  have hPz : P.eval z = y := by
    simp only [P, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul, sub_zero]
  rw [← hPz, hPQ, eval_map_algebraMap]

/-! ### The opened words -/

/-- Dropping the points of `T` where `L` meets `z` or `z'` loses at most two points. -/
theorem card_le_card_filter_add_two (S : Setup EF) (T : Finset S.Point) (z z' : 𝕂) :
    T.card ≤ (T.filter fun i ↦ S.domain i ≠ z ∧ S.domain i ≠ z').card + 2 := by
  classical
  have hone (w : 𝕂) : (Finset.univ.filter fun i : S.Point ↦ S.domain i = w).card ≤ 1 :=
    Finset.card_le_one.mpr fun i hi j hj ↦ (S.domain).injective
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hsub : (T.filter fun i ↦ ¬ (S.domain i ≠ z ∧ S.domain i ≠ z')) ⊆
      (Finset.univ.filter fun i : S.Point ↦ S.domain i = z) ∪
        Finset.univ.filter fun i : S.Point ↦ S.domain i = z' := by
    intro i hi
    simp only [Finset.mem_filter, ne_eq, not_and_or, not_not] at hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi.2
  have h := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (hone z) (hone z')))
  rw [← Finset.card_filter_add_card_filter_not
    (fun i ↦ S.domain i ≠ z ∧ S.domain i ≠ z')]
  omega

/-- A set of at least `(1 - δ) N` points, `δ < 1 - rate`, has more than `n` points. -/
theorem lt_card_of_rate (S : Setup EF) (δ : ℝ) (hδ : δ < 1 - S.rate) (t : Nat)
    (ht : (t : ℝ) ≥ S.size * (1 - δ)) : S.n < t := by
  have hNpos : (0 : ℝ) < S.size := by exact_mod_cast Nat.two_pow_pos _
  have hn : (S.n : ℝ) = S.size * S.rate := by
    rw [Setup.rate, mul_div_cancel₀ _ hNpos.ne']
  have : (S.n : ℝ) < t := by
    rw [hn]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left (by linarith) hNpos) ht
  exact_mod_cast this

/-- Each opened word's DEEP component is one of the components. -/
theorem near_of_mem {S : Setup EF} (p : Prover S) (α ζ : 𝕂) (T : Finset S.Point)
    (hnear : ∀ k, ∃ u ∈ S.code, ∀ i ∈ T, components p α ζ k i = u i)
    (w : (S.Point → F) × 𝕂 × 𝕂) (hw : w ∈ openedWords p α ζ) :
    ∃ u ∈ S.code, ∀ i ∈ T, deepComponent S w.1 w.2.1 w.2.2 i = u i := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
  have hlen : (openedWords p α ζ).length = S.numOpened := by
    simp only [openedWords, List.length_append, List.length_map, List.length_finRange,
      List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul, Setup.numOpened]
    ring
  exact hnear ⟨k, hlen ▸ hk⟩

/-- **The decoding step.** -/
theorem decodingStep (S : Setup EF) : DecodingStep S := by
  intro δ hδ prover α ζ _ hnear
  obtain ⟨T₀, hT₀card, hT₀near⟩ := hnear
  set T := T₀.filter fun i ↦ S.domain i ≠ ζ ∧ S.domain i ≠ ζ * rootOfUnity S.logN
  have hTcard : (T.card : ℝ) ≥ S.size * (1 - δ) := by
    have h : (T₀.card : ℝ) ≤ T.card + 2 := by
      exact_mod_cast card_le_card_filter_add_two S T₀ ζ (ζ * rootOfUnity S.logN)
    have hN : (S.size : ℝ) ≠ 0 := by positivity
    have : (S.size : ℝ) * (1 - (δ - 2 / S.size)) = S.size * (1 - δ) + 2 := by
      field_simp
      ring
    linarith
  have hT := lt_card_of_rate S δ hδ T.card hTcard
  have hmem := near_of_mem prover α ζ T fun k ↦ by
    obtain ⟨u, hu, hk⟩ := hT₀near k
    exact ⟨u, hu, fun i hi ↦ hk i (Finset.mem_filter.mp hi).1⟩
  have hζ (i) (hi : i ∈ T) : ζ ≠ S.domain i := ((Finset.mem_filter.mp hi).2.1).symm
  have hζω (i) (hi : i ∈ T) : ζ * rootOfUnity S.logN ≠ S.domain i :=
    ((Finset.mem_filter.mp hi).2.2).symm
  have htr (j : Fin S.air.width) := exists_basePoly S T hT (prover.trace j) ζ _ hζ
    (hmem (prover.trace j, ζ, _) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))))
  have hnx (j : Fin S.air.width) := exists_basePoly S T hT (prover.trace j) _ _ hζω
    (hmem (prover.trace j, ζ * rootOfUnity S.logN, _) (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))))
  have hqu (c : Fin S.chunks) (e : Fin (Challenge.d EF)) := exists_basePoly S T hT
    (prover.quotient α c e) ζ _
    hζ (hmem (prover.quotient α c e, ζ, _) (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨c, List.mem_finRange c, List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩⟩)))
  choose trace htdeg htT htz using htr
  choose next hndeg hnT hnz using hnx
  choose quotient hqdeg hqT hqz using hqu
  have hnext (j : Fin S.air.width) : next j = trace j := by
    refine map_injective (algebraMap F 𝕂) (algebraMap F 𝕂).injective
      (eq_of_agree S T hT _ _ (natDegree_map_le.trans (hndeg j))
        (natDegree_map_le.trans (htdeg j)) fun i hi ↦ ?_)
    rw [domain_eq, eval_map_algebraMap, eval_map_algebraMap, aeval_algebraMap_apply,
      aeval_algebraMap_apply, coe_aeval_eq_eval, ← hnT j i hi, ← htT j i hi]
  refine ⟨trace, quotient, htdeg, ⟨T, hTcard, fun i hi j ↦ htT j i hi⟩, hqdeg,
    ⟨T, hTcard, fun i hi ce ↦ hqT ce.1 ce.2 i hi⟩, ?_⟩
  have hnz' (j : Fin S.air.width) := hnext j ▸ hnz j
  generalize prover.openings α ζ = o at htz hnz' hqz
  cases o
  simp only [trueOpenings, Openings.mk.injEq]
  exact ⟨funext fun j ↦ (htz j).symm, funext fun j ↦ (hnz' j).symm,
    funext fun c ↦ funext fun e ↦ (hqz c e).symm⟩

end CompStark.Sound
