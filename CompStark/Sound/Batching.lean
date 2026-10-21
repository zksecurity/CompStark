/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps
public import CompStark.Sound.CurveCA

/-! # The batching step

`batchingStep`: if `m` words `ws` are not `δ'`-near the code on a common set, the set of `a` for
which `∑ₖ aᵏ ws k` is `δ`-near the code has density at most `batchingErrorOf S m δ δ'`. This is
immediate from the definition of `batchingErrorOf` as a supremum over the words.

`batchingError_le_mcaError` bounds the error at a single radius by the mutual
correlated-agreement error of the powers generator, by inclusion of events. If the combination
agrees with a codeword on a set `T` of at least `N (1 - δ)` points, its projection to `T` lies in
the projected code; some `ws k` projected to `T` does not, as otherwise the words would be near
the code on the common set `T`. So `a` lies in the event `IsMCA` of the powers generator for the
family `ws`, whose uniform probability is the event's density, and at most the supremum
`mcaError` over families.

The error only decreases as the radius `δ'` of the common set grows (`batchingError_anti`).

`batchingError_le_curve` bounds the error with proximity loss `δ < δ'` in the unique-decoding
range by correlated agreement for curves (`CompStark/Sound/CurveCA.lean`):
`(m - 1) · max(T₁, T₂) / |𝕂|`. A combination `δ`-near the code is within relative distance `δ` of it,
and words jointly `δ'`-close to the code are near it on a common set.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop CoreDefinitions LinearCode

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- A combination `δ`-near the code, of words not near the code on a common set, is an MCA event
for the powers generator. -/
theorem isMCA_of_near (S : Setup EF) (δ : NNReal) {M : Nat} (ws : Fin (M + 1) → S.Point → 𝕂)
    (hfar : ¬ NearTogether S δ ws) (a : 𝕂)
    (hnear : Near S δ fun i ↦ ∑ k : Fin (M + 1), a ^ (k : Nat) * ws k i) :
    IsMCA (univariatePowersGenerator 𝕂 M) S.code a ws δ := by
  obtain ⟨T, hT, u, hu, hagree⟩ := hnear
  refine ⟨T, by rwa [Fintype.card_fin], ?_, ?_⟩
  · refine Submodule.mem_map.mpr ⟨u, hu, funext fun i ↦ ?_⟩
    simp only [LinearMap.funLeft_apply, projectedWord, Set.domRestrict_apply, smul_eq_mul]
    exact (hagree i.1 i.2).symm
  · by_contra hall
    simp only [not_exists, not_not] at hall
    refine hfar ⟨T, hT, fun k ↦ ?_⟩
    obtain ⟨v, hv, heq⟩ := Submodule.mem_map.mp (hall k)
    exact ⟨v, hv, fun i hi ↦ (congrFun heq ⟨i, hi⟩).symm⟩

open Classical in
/-- The density of `a` making a combination of `M + 1` words not near on a common set `δ`-near
is at most the MCA error of the powers generator. -/
theorem density_near_le_mcaError (S : Setup EF) (δ : NNReal) {M : Nat}
    (ws : Fin (M + 1) → S.Point → 𝕂) :
    ((Finset.univ.filter fun a : 𝕂 ↦
        Near S δ (fun i ↦ ∑ k : Fin (M + 1), a ^ (k : Nat) * ws k i) ∧
        ¬ NearTogether S δ ws).card : ENNReal)
      / Fintype.card 𝕂 ≤ mcaError (univariatePowersGenerator 𝕂 M) S.code δ := by
  refine le_iSup_of_le ws ?_
  rw [SampleableType.prEvent_uniformSample]
  apply ENNReal.div_le_div_right
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro a
  simp only [Finset.mem_filter_univ]
  exact fun ⟨hnear, hfar⟩ ↦ isMCA_of_near S δ ws hfar a hnear

/-- An empty family of words is near the code on a common set. -/
theorem nearTogether_of_isEmpty (S : Setup EF) (δ : NNReal) {ι : Type} [IsEmpty ι]
    (ws : ι → S.Point → 𝕂) : NearTogether S δ ws := by
  refine ⟨Finset.univ, ?_, isEmptyElim⟩
  rw [Finset.card_univ, Fintype.card_fin, ge_iff_le]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (sub_le_self 1 δ.2)

/-- At a single radius, the batching error of `m` words is at most the mutual
correlated-agreement error of the powers `1, a, …, a ^ (m - 1)`. -/
theorem batchingError_le_mcaError (S : Setup EF) (m : Nat) (δ : NNReal) :
    batchingErrorOf S m δ δ ≤ mcaError (univariatePowersGenerator 𝕂 (m - 1)) S.code δ := by
  unfold batchingErrorOf
  cases m with
  | zero =>
    refine iSup_le fun ws ↦ ?_
    simp only [nearTogether_of_isEmpty S δ ws, not_true_eq_false, and_false,
      Finset.filter_false, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div, zero_le]
  | succ M => exact iSup_le fun ws ↦ density_near_le_mcaError S δ ws

/-- Words near on a common set at a radius are near on it at every larger radius. -/
theorem NearTogether.mono {S : Setup EF} {ι : Type} {δ δ' : ℝ} (h : δ ≤ δ')
    {ws : ι → S.Point → 𝕂} (hnear : NearTogether S δ ws) : NearTogether S δ' ws := by
  obtain ⟨T, hT, hws⟩ := hnear
  refine ⟨T, le_trans ?_ hT, hws⟩
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

/-- The batching error decreases as the radius of the common set grows. -/
theorem batchingError_anti (S : Setup EF) (m : Nat) (δ : NNReal) {δ' δ'' : ℝ} (h : δ' ≤ δ'') :
    batchingErrorOf S m δ δ'' ≤ batchingErrorOf S m δ δ' := by
  classical
  refine iSup_le fun ws ↦ le_iSup_of_le ws (ENNReal.div_le_div_right (Nat.cast_le.mpr
    (Finset.card_le_card fun a ↦ ?_)) _)
  simp only [Finset.mem_filter_univ]
  exact fun ⟨hnear, hfar⟩ ↦ ⟨hnear, fun h' ↦ hfar (NearTogether.mono h h')⟩

open Classical in
/-- Batching by powers keeps words that are not near on a common set far, except with
probability `batchingError`. -/
theorem batchingStep (S : Setup EF) : BatchingStep S := by
  intro m δ δ' ws hfar
  refine le_trans (le_of_eq ?_) (le_iSup (fun ws : Fin m → S.Point → 𝕂 ↦
    ((Finset.univ.filter fun a : 𝕂 ↦
      Near S δ (fun i ↦ ∑ k : Fin m, a ^ (k : Nat) * ws k i) ∧
      ¬ NearTogether S δ' ws).card : ENNReal) / Fintype.card 𝕂) ws)
  simp only [hfar, not_false_eq_true, and_true]

/-- A word `δ`-near the code is within relative distance `δ` of it. -/
theorem relDist_le_of_near (S : Setup EF) (δ : NNReal) (w : S.Point → 𝕂) (h : Near S δ w) :
    δᵣ(w, (S.code : Set (S.Point → 𝕂))) ≤ δ := by
  classical
  obtain ⟨T, hT, c, hc, hagree⟩ := h
  rw [Code.relDistFromCode_le_iff_distFromCode_le]
  refine (Code.closeToCode_iff_closeToCodeword_of_minDist (u := w)
    (C := (S.code : Set (S.Point → 𝕂))) (e := _)).2 ⟨c, hc, ?_⟩
  have hsub : Code.disagreementCols w c ⊆ Tᶜ := fun i hi =>
    Finset.mem_compl.mpr fun hiT => (Code.mem_disagreementCols.mp hi) (hagree i hiT)
  rw [Code.hammingDist_eq_disagreementCols_card]
  refine (Finset.card_le_card hsub).trans (Nat.le_floor ?_)
  have hTle : T.card ≤ S.size := (Finset.card_le_univ T).trans_eq (Fintype.card_fin _)
  rw [Finset.card_compl, Fintype.card_fin]
  have : ((S.size - T.card : ℕ) : ℝ) ≤ δ * S.size := by
    rw [Nat.cast_sub hTle]
    linarith
  exact_mod_cast this

/-- Words jointly `δ`-close to the code are near it on a common set. -/
theorem nearTogether_of_jointProximity (S : Setup EF) (δ : NNReal) {ι : Type} [Fintype ι]
    (ws : ι → S.Point → 𝕂)
    (h : Code.jointProximity (C := (S.code : Set (S.Point → 𝕂))) (u := ws) δ) :
    NearTogether S δ ws := by
  obtain ⟨T, hT, v, hv⟩ := (Code.jointAgreement_iff_jointProximity _ _ _).2 h
  refine ⟨T, ?_, fun k => ⟨v k, (hv k).1, fun i hi => ((Finset.mem_filter.mp
    ((hv k).2 hi)).2).symm⟩⟩
  have hT' : ((1 - δ : NNReal) : ℝ) * S.size ≤ T.card := by
    rw [Fintype.card_fin] at hT
    exact_mod_cast hT
  rw [NNReal.coe_sub_def, NNReal.coe_one] at hT'
  have := mul_le_mul_of_nonneg_right (le_max_left (1 - (δ : ℝ)) 0)
    (Nat.cast_nonneg (α := ℝ) S.size)
  rw [ge_iff_le, mul_comm]
  linarith

-- The linter recurses too deeply on membership in `Finset.univ : Finset 𝕂`.
set_option linter.constructorNameAsVariable false in
/-- **Batching error from curve CA.** In the unique-decoding range, with proximity loss
`δ < δ'`, the batching error of `m` words is at most `(m - 1) · max(T₁, T₂) / |𝕂|`,
`T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))`, `T₂ = δ' / (δ' - δ)` (`card_goodCoeffs_le`). -/
theorem batchingError_le_curve (S : Setup EF) (m : Nat) (δ : NNReal) (δ' : ℝ)
    (h_ud : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / S.size) (h_pos : 0 < δ) (h_lt : δ < δ') :
    batchingErrorOf S m δ δ' ≤
      ENNReal.ofReal ((m - 1 : ℕ) *
        max ((1 - S.rate - δ) / (δ * (1 - S.rate - 2 * δ))) (δ' / (δ' - δ))) /
        Fintype.card 𝕂 := by
  classical
  obtain ⟨δ', rfl⟩ : ∃ δ'' : NNReal, (δ'' : ℝ) = δ' :=
    ⟨δ'.toNNReal, Real.coe_toNNReal _ (le_trans δ.2 h_lt.le)⟩
  replace h_lt : δ < δ' := by exact_mod_cast h_lt
  unfold batchingErrorOf
  cases m with
  | zero =>
    refine iSup_le fun ws ↦ ?_
    simp only [nearTogether_of_isEmpty S δ' ws, not_true_eq_false, and_false,
      Finset.filter_false, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div, zero_le]
  | succ M =>
    refine iSup_le fun ws ↦ ENNReal.div_le_div_right ?_ _
    by_cases hnt : NearTogether S δ' ws
    · simp only [hnt, not_true_eq_false, and_false, Finset.filter_false, Finset.card_empty,
        Nat.cast_zero, zero_le]
    let dom : S.Point ↪ 𝕂 := ⟨fun i ↦ S.domain i, (S.domain).injective⟩
    have hpq : ∀ a : 𝕂, Near S δ (fun i ↦ ∑ k : Fin (M + 1), a ^ (k : Nat) * ws k i) →
        δᵣ(CurveCA.curveWord ws a, ReedSolomon.code dom S.n) ≤ δ := fun a hn => by
      have hw : (fun i ↦ ∑ k : Fin (M + 1), a ^ (k : Nat) * ws k i) =
          CurveCA.curveWord ws a := funext fun i => (CurveCA.curveWord_apply ws a i).symm
      rw [hw] at hn
      exact relDist_le_of_near S δ _ hn
    have hsub : (Finset.univ.filter fun a : 𝕂 ↦
        Near S δ (fun i ↦ ∑ k : Fin (M + 1), a ^ (k : Nat) * ws k i) ∧
        ¬ NearTogether S δ' ws) ⊆ CurveCA.goodCoeffs dom S.n ws δ :=
by
      intro a ha
      rw [Finset.mem_filter_univ] at ha
      unfold CurveCA.goodCoeffs
      rw [Finset.mem_filter_univ]
      exact hpq a ha.1
    have hcard : (Fintype.card S.Point : ℝ) = S.size := by
      rw [Fintype.card_fin]
    have hbound := CurveCA.card_goodCoeffs_le dom S.n M ws δ δ'
      (by rw [hcard]; exact h_ud) h_pos h_lt
      (fun hj => hnt (nearTogether_of_jointProximity S δ' ws hj))
    rw [hcard] at hbound
    rw [Nat.add_sub_cancel]
    calc _ ≤ ((CurveCA.goodCoeffs dom S.n ws δ).card : ENNReal) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ = ENNReal.ofReal ((CurveCA.goodCoeffs dom S.n ws δ).card : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end CompStark.Sound
