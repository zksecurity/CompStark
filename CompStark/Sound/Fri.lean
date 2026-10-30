/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps

/-! # FRI's codes on `L` and the domains it reaches

FRI on `L` with Plonky3's schedule (`friRounds`) tests the code of degree `n` (`degree_friRounds`):
a word agreeing with it is near the code (`near_of_agrees`).

Every domain FRI's folds reach from `L = g ⟨ω⟩` is a coset `c ⟨ω'⟩` of a two-adic subgroup, `ω'`
the base field's generator of its order (`IsLevel`): the folds square the points; so is the
subgroup `⟨ω⟩` itself (`subgroupDomain`), FRI's domain in Plonky3's coordinate. A Reed–Solomon
code on a coset depends only on the subgroup, as a set of words indexed by the powers of `ω'`
(`code_le_of_isLevel`): so an injected input close to its code on the domain where FRI injects
it is close to its code on its own domain `g ⟨ω'⟩` (`agrees_cosetDomain_of_isLevel`), and a
codeword on its own domain is one on every domain the folds reach.
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

/-- The points of the subgroup domain of `2 ^ n` points: `ω_n ^ i`. -/
theorem subgroupDomain_apply (n : Nat) (hn : n ≤ twoAdicity F) (i : Fin (2 ^ n)) :
    subgroupDomain (EF := EF) n hn i = lift (twoAdicGen n) ^ (i : ℕ) := by
  simp only [subgroupDomain, Domain.CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    Domain.CosetFftDomain.subgroupUnit, subgroupHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_one, one_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, toAdd_ofAdd]

theorem isLevel_subgroupDomain (n : Nat) (hn : n ≤ twoAdicity F) :
    IsLevel (subgroupDomain (EF := EF) n hn) :=
  ⟨hn, 1, one_ne_zero, fun x ↦ by rw [subgroupDomain_apply, one_mul]⟩

/-- The Reed–Solomon codes on two cosets `c ⟨ω_m⟩` and `c' ⟨ω_m⟩` are the same words: a polynomial
`p` on the one is `p (c / c' · X)` on the other, of no larger degree. -/
theorem code_le_of_isLevel {m : ℕ} {D D' : SmoothCosetFftDomain m 𝕂} (hD : IsLevel D)
    (hD' : IsLevel D') (deg : ℕ) :
    ReedSolomon.code (D : Fin (2 ^ m) ↪ 𝕂) deg ≤ ReedSolomon.code (D' : Fin (2 ^ m) ↪ 𝕂) deg := by
  obtain ⟨-, c, hc, hDc⟩ := hD
  obtain ⟨-, c', hc', hDc'⟩ := hD'
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
  set q := p.comp (Polynomial.C (c / c') * Polynomial.X)
  refine Submodule.mem_map.mpr ⟨q, ?_, funext fun x ↦ ?_⟩
  · rw [Polynomial.mem_degreeLT] at hp ⊢
    by_cases hp0 : p = 0
    · simp only [q, hp0, Polynomial.zero_comp, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe deg
    have hlin : (Polynomial.C (c / c') * Polynomial.X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    have hq : q.natDegree ≤ p.natDegree :=
      natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlin).trans (Nat.mul_one _).le)
    refine lt_of_le_of_lt (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hq)) ?_
    rwa [Polynomial.degree_eq_natDegree hp0] at hp
  · change q.eval (D' x) = p.eval (D x)
    simp only [q, eval_comp, eval_mul, eval_C, eval_X]
    congr 1
    rw [hDc', hDc]
    field_simp

/-- A word close to the Reed–Solomon code on a coset `c ⟨ω_m⟩` is close to it on the coset
`g ⟨ω_m⟩`, which has the same codewords (`code_le_of_isLevel`). -/
theorem agrees_cosetDomain_of_isLevel {m : ℕ} (D : SmoothCosetFftDomain m 𝕂) (hD : IsLevel D)
    (deg : ℕ) (ρ : ℝ) (w : Fin (2 ^ m) → 𝕂) (h : Agrees D deg ρ w) :
    Agrees (cosetDomain (EF := EF) m hD.1) deg ρ w := by
  obtain ⟨T, hT, v, hv, hvT⟩ := h
  exact ⟨T, hT, v, code_le_of_isLevel hD (isLevel_cosetDomain m hD.1) deg hv, hvT⟩

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

end CompStark.Sound
