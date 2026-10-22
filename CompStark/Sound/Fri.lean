/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps

/-! # FRI rejects far words

`friAcceptanceWith_le`: FRI with injected inputs accepts with probability at most `friErrorWith`
if the word, or an injected input, is `δ`-far from its code. This is `FriGame.acceptance_le` on
`L` with Plonky3's schedule (`friRounds`), whose code before the folds has degree `n`
(`degree_friRounds`).

Every domain FRI's folds reach from `L = g ⟨ω⟩` is a coset `c ⟨ω'⟩` of a two-adic subgroup, `ω'`
the base field's generator of its order (`IsLevel`): the folds square the points. A
Reed–Solomon code on a coset depends only on the subgroup, as a set of words indexed by the
powers of `ω'` (`agrees_cosetDomain_of_isLevel`): so an injected input close to its code on the
domain where FRI injects it is close to its code on its own domain `g ⟨ω'⟩`.

`friStep`: the STARK's FRI, without injected inputs. `friAtMostOne`: acceptance is at most `1`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial Domain FriGame FriInject

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
variable {lookups : List (Lookup F)}

local notation "𝕂" => Challenge.Spec EF

/-- Plonky3's arities sum to the number of halvings they fold away. -/
theorem sum_folds (m : Nat) : ∀ r, ((folds m r).map (fun x : ℕ+ ↦ x.val)).sum = r
  | 0 => by rw [folds]; rfl
  | r + 1 => by
    have h := sum_folds m (r + 1 - max 1 (min m (r + 1)))
    rw [folds]
    change max 1 (min m (r + 1)) +
      ((folds m (r + 1 - max 1 (min m (r + 1)))).map (fun x : ℕ+ ↦ x.val)).sum = r + 1
    rw [h]
    omega

/-- A word at relative distance below `δ` from a codeword is `δ`-near the code. -/
theorem near_of_relHammingDist_lt (S : Setup EF lookups) (δ : ℝ) (w u : S.Point → 𝕂)
    (hu : u ∈ S.code)
    (h : (Code.relHammingDist w u : ℝ) < δ) : Near S δ w := by
  classical
  refine ⟨Finset.univ.filter fun i ↦ w i = u i, ?_, u, hu, fun i hi ↦ (Finset.mem_filter.mp hi).2⟩
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : S.Point ↦ w i = u i)
  have hd : hammingDist w u = (Finset.univ.filter fun i ↦ ¬ w i = u i).card := rfl
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hpos : (0 : ℝ) < S.size := by exact_mod_cast Nat.two_pow_pos _
  simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast, Fintype.card_fin] at h
  rw [← hd] at hcard
  have hpos' : (0 : ℝ) < (2 ^ (S.logN + S.params.logBlowup) : Nat) := hpos
  rw [div_lt_iff₀ hpos'] at h
  have hcard' : (({i | w i = u i} : Finset S.Point).card : ℝ) + (hammingDist w u : ℝ) =
      (2 ^ (S.logN + S.params.logBlowup) : Nat) := by exact_mod_cast hcard
  change _ ≥ ((2 ^ (S.logN + S.params.logBlowup) : Nat) : ℝ) * (1 - δ)
  linarith

/-- Plonky3's arities for a positive number of halvings are nonempty. -/
theorem folds_cons (m r : Nat) (hr : r ≠ 0) : ∃ f fs, folds m r = f :: fs := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [folds]
  exact ⟨_, _, rfl⟩

/-! ### The domains of the folds -/

/-- The points of the coset domain of `2 ^ n` points: `g ω_n ^ i`. -/
theorem cosetDomain_apply (n : Nat) (hn : n ≤ twoAdicity F) (i : Fin (2 ^ n)) :
    cosetDomain (EF := EF) n hn i = lift gen * lift (twoAdicGen n) ^ (i : ℕ) := by
  simp only [cosetDomain, Domain.CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    Domain.CosetFftDomain.subgroupUnit, subgroupHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_mk0, Units.val_pow_eq_pow_val, IsUnit.unit_spec, toAdd_ofAdd]

/-- A domain of `2 ^ m` points is a coset `c ⟨ω_m⟩` of the two-adic subgroup of its order. -/
def IsLevel {m : ℕ} (D : SmoothCosetFftDomain m 𝕂) : Prop :=
  m ≤ twoAdicity F ∧ ∃ c : 𝕂, c ≠ 0 ∧ ∀ x : Fin (2 ^ m), D x = c * lift (twoAdicGen m) ^ (x : ℕ)

theorem isLevel_cosetDomain (n : Nat) (hn : n ≤ twoAdicity F) :
    IsLevel (cosetDomain (EF := EF) n hn) := by
  refine ⟨hn, lift gen, ?_, fun x ↦ cosetDomain_apply n hn x⟩
  rw [lift, ne_eq, map_eq_zero_iff _ (algebraMap F 𝕂).injective]
  exact BaseField.gen_ne_zero

/-- `ω_m ^ 2 ^ k = ω_(m - k)` in `𝕂`. -/
theorem lift_twoAdicGen_pow (m k : ℕ) (hk : k ≤ m) (hm : m ≤ twoAdicity F) :
    lift (EF := EF) (twoAdicGen m) ^ 2 ^ k = lift (twoAdicGen (m - k)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [← map_pow, BaseField.twoAdicGen_pow j k hm, Nat.add_sub_cancel]

/-- The folds keep cosets of two-adic subgroups: the subdomain of `c ⟨ω_m⟩` by `2 ^ k` is
`c ^ 2 ^ k ⟨ω_(m - k)⟩`. -/
theorem isLevel_subdomain {m : ℕ} (D : SmoothCosetFftDomain m 𝕂) (k : ℕ) (hD : IsLevel D) :
    IsLevel (D.subdomain k) := by
  obtain ⟨hm, c, hc, hD⟩ := hD
  refine ⟨by omega, c ^ 2 ^ k, pow_ne_zero _ hc, fun y ↦ ?_⟩
  have hy : y.val < 2 ^ m :=
    lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))
  have hfold : CosetFftDomainClass.sqFoldMapGen (i := k) (⟨y.val, hy⟩ : Fin (2 ^ m)) = y :=
    Fin.ext (Nat.mod_eq_of_lt y.isLt)
  have key : (D.subdomain k) y = D ⟨y.val, hy⟩ ^ 2 ^ k := by
    rw [← CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := D), hfold]
  rw [key, hD, mul_pow, ← pow_mul, mul_comm (y.val), pow_mul]
  change c ^ 2 ^ k * (lift (twoAdicGen m) ^ 2 ^ k) ^ (y : ℕ) =
    c ^ 2 ^ k * lift (twoAdicGen (m - k)) ^ (y : ℕ)
  by_cases hk : k ≤ m
  · rw [lift_twoAdicGen_pow m k hk hm]
  · have h1 : (2 : ℕ) ^ (m - k) = 1 := by rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
    have h0 : (y : ℕ) = 0 := Nat.lt_one_iff.mp (lt_of_lt_of_eq y.isLt h1)
    rw [h0, pow_zero, pow_zero]

/-- A word close to the Reed–Solomon code on a coset `c ⟨ω_m⟩` is close to it on the coset
`g ⟨ω_m⟩`: the codes are the same words, a polynomial `p` on the one being `p (c / g · X)` on
the other. -/
theorem agrees_cosetDomain_of_isLevel {m : ℕ} (D : SmoothCosetFftDomain m 𝕂) (hD : IsLevel D)
    (deg : ℕ) (hdeg : 0 < deg) (ρ : ℝ) (w : Fin (2 ^ m) → 𝕂) (h : Agrees D deg ρ w) :
    Agrees (cosetDomain (EF := EF) m hD.1) deg ρ w := by
  obtain ⟨hm, c, hc, hDc⟩ := hD
  obtain ⟨T, hT, v, hv, hvT⟩ := h
  have : NeZero deg := ⟨hdeg.ne'⟩
  obtain ⟨p, hp, rfl⟩ := ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero.mp hv
  have hg : lift (EF := EF) gen ≠ 0 := by
    rw [lift, ne_eq, map_eq_zero_iff _ (algebraMap F 𝕂).injective]
    exact BaseField.gen_ne_zero
  set q := p.comp (Polynomial.C (c / lift gen) * Polynomial.X)
  have hq : q.natDegree < deg := by
    refine lt_of_le_of_lt (natDegree_comp_le.trans ?_) hp
    have : (Polynomial.C (c / lift (EF := EF) gen) * Polynomial.X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    exact (Nat.mul_le_mul_left _ this).trans (Nat.mul_one _).le
  refine ⟨T, hT, _, ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt hq, fun x hx ↦ ?_⟩
  rw [← hvT x hx]
  change q.eval (cosetDomain (EF := EF) m hm x) = p.eval (D x)
  simp only [q, eval_comp, eval_mul, eval_C, eval_X]
  congr 1
  rw [cosetDomain_apply, hDc]
  field_simp

/-- A word agreeing with the code on `(1 - δ) N` points is `δ`-near. -/
theorem near_of_agrees (S : Setup EF lookups) (δ : ℝ) (w : S.Point → 𝕂)
    (h : Agrees S.domain S.n (1 - δ) w) : Near S δ w := by
  obtain ⟨T, hT, v, hv, hvT⟩ := h
  refine ⟨T, ?_, v, hv, fun x hx ↦ (hvT x hx).symm⟩
  rw [ge_iff_le, Setup.size, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
  exact hT

/-! ### FRI's rounds on `L` -/

/-- The code before FRI's folds on `L` has degree `n`. -/
theorem degree_friRounds (S : Setup EF lookups) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (heights : List ℕ)
    (hfit : Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights) :
    (S.friRounds words heights).degree (2 ^ S.params.logFinalPolyLen) = S.n := by
  have hf := S.valid.finalPolyFits
  rw [Setup.friRounds, Rounds.degree_schedule S.valid.folds words _ _ _ _ (by omega) (by omega)
    hfit, ← pow_add]
  congr 1
  omega

/-- **FRI rejects far words.** If the word is not `δ`-near the code, or an injected input is not
`δ`-close to its code on its own coset domain, FRI accepts with probability at most
`friErrorWith`. -/
theorem friAcceptanceWith_le (S : Setup EF lookups) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (heights : List ℕ)
    (hfit : Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights)
    (word : S.Point → 𝕂) (δ : NNReal)
    (hfar : ¬ Near S δ word ∨ ∃ m ∈ heights, ∀ hm : m ≤ twoAdicity F,
      ¬ Agrees (cosetDomain (EF := EF) m hm) (2 ^ (m - S.params.logBlowup)) (1 - δ) (words m)) :
    friAcceptanceWith S words heights word ≤ friErrorWith S heights δ := by
  have hf := S.valid.finalPolyFits
  have herr : friErrorWith S heights δ =
      FriGame.error S.domain (S.friRounds words heights) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries δ := by
    simp only [friErrorWith, FriGame.error, Setup.friRounds]
    refine iInf_congr fun loss ↦ ?_
    obtain ⟨h1, h2, -⟩ := Rounds.foldError_schedule_congr S.params.maxLogArity
      (S.params.logFinalPolyLen + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen) δ loss
      (fun _ _ ↦ 0) words _ _ S.domain heights
    rw [h1, h2]
  rw [herr]
  refine acceptance_le _ _ _ _ _ _ _ fun ⟨hw, hin⟩ ↦ ?_
  rcases hfar with hfar | ⟨m, hm, hfar⟩
  · rw [degree_friRounds S words heights hfit] at hw
    exact hfar (near_of_agrees S δ word hw)
  · obtain ⟨D, hD, hagree⟩ := Rounds.agrees_of_inputsAgree S.valid.folds words _ _
      (fun D ↦ IsLevel D) (fun D k hD ↦ isLevel_subdomain D k hD) (S.logN + S.params.logBlowup)
      _ S.domain heights (by omega) (Nat.sub_le _ _) hfit (isLevel_cosetDomain _ _) hin m hm
    refine hfar hD.1 ?_
    have hdeg : 2 ^ (m - (S.params.logFinalPolyLen + S.params.logBlowup)) *
        2 ^ S.params.logFinalPolyLen = 2 ^ (m - S.params.logBlowup) := by
      rw [← pow_add]
      congr 1
      have := (hfit.2 m hm).1
      omega
    rw [hdeg] at hagree
    exact agrees_cosetDomain_of_isLevel D hD _ (Nat.two_pow_pos _) _ _ hagree

/-- FRI accepts a word that is not `δ`-near the code with probability at most `friError`. -/
theorem friStep (S : Setup EF lookups) : FriStep S := fun δ w hw ↦
  friAcceptanceWith_le S _ [] (Rounds.fits_nil _ _) w δ (Or.inl hw)

/-- FRI accepts with probability at most `1`. -/
theorem friAtMostOne (S : Setup EF lookups) : FriAtMostOne S :=
  fun w ↦ acceptance_le_one _ _ _ _ _ w

end CompStark.Sound
