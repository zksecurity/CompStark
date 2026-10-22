/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.SecurityCalculator
public import CompStark.Sound.BatchNumbersNi

/-! # The security calculator's bounds

Each term of the calculator (`CompStark/SecurityCalculator.lean`) bounds its error term: the
bounds of `CompStark/Sound/Numbers.lean`, `NumbersNi.lean` and `BatchNumbersNi.lean`, cast to the
calculator's rationals for `|F| = p`. `knowledgeError_le_bound`, `roundError_le_bound`,
`Batch.knowledgeError_le_bound` and `Batch.roundError_le_bound` collect them.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable {p : ℕ}

/-! ### Casts -/

/-- A rational over `|𝕂| = p ^ d`. -/
theorem ofReal_div_card_eq (hp : Nat.card F = p) (x : ℚ) :
    ENNReal.ofReal (x : ℝ) / (Fintype.card 𝕂 : ENNReal) =
      ENNReal.ofReal ((x / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  rw [← ENNReal.ofReal_natCast (Fintype.card 𝕂), ← ENNReal.ofReal_div_of_pos hK, card_eq, hp]
  push_cast
  rfl

/-- An integer over `|𝕂| = p ^ d`. -/
theorem natCast_div_card_eq (hp : Nat.card F = p) (n : ℕ) :
    (n : ENNReal) / (Fintype.card 𝕂 : ENNReal) =
      ENNReal.ofReal (((n : ℚ) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  rw [← ofReal_div_card_eq hp, Rat.cast_natCast, ENNReal.ofReal_natCast]

/-- `powFraction` for `|F| = p`. -/
theorem powFraction_eq (hp : Nat.card F = p) (bits : ℕ) :
    powFraction F bits = ENNReal.ofReal (powFractionQ p bits : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp ▸ Nat.card_pos
  rw [powFraction, powFractionQ, hp, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast p,
    ← ENNReal.ofReal_div_of_pos hp0]
  push_cast
  rfl

theorem powFractionQ_nonneg (bits : ℕ) : 0 ≤ (powFractionQ p bits : ℝ) := by
  rw [Rat.cast_nonneg, powFractionQ]
  positivity

/-- A rational at most `2 ^ (-bits)`. -/
theorem ofReal_le_inv_two_pow {x : ℚ} {bits : ℕ} (h : x ≤ 1 / 2 ^ bits) :
    ENNReal.ofReal (x : ℝ) ≤ (2 ^ bits : ENNReal)⁻¹ := by
  rw [inv_two_pow_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at this
  rwa [one_div] at this

theorem le_maxQ {x : ℚ} : ∀ {l : List ℚ}, x ∈ l → x ≤ maxQ l
  | _ :: _, .head _ => le_max_left _ _
  | _ :: _, .tail _ h => (le_maxQ h).trans (le_max_right _ _)

theorem maxQ_nonneg : ∀ l : List ℚ, 0 ≤ maxQ l
  | [] => le_rfl
  | _ :: l => (maxQ_nonneg l).trans (le_max_right _ _)

/-- A rational term over `|𝕂|`, cast, is at most the cast of a larger one. -/
theorem ofReal_div_le {x y : ℚ} (h : x ≤ y) (K : ℚ) (hK : 0 ≤ K) :
    ENNReal.ofReal ((x / K : ℚ) : ℝ) ≤ ENNReal.ofReal ((y / K : ℚ) : ℝ) :=
  ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (div_le_div_of_nonneg_right h hK))

section Analysis
variable (A : Analysis)

theorem lossyBound_nonneg {ρ : ℚ} (hA : A.Valid ρ) : 0 ≤ A.lossyBound ρ :=
  le_trans (div_nonneg (by linarith [hA.1, hA.2.1]) hA.2.1.le) (le_max_right _ _)

/-- The lossy bound for `δ` and `loss` equal to the analysis'. -/
theorem lossyBound_eq (b : ℕ) (δ loss : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hloss : (loss : ℝ) = A.loss) :
    LossyMca.lossyBound 1 (2 ^ b) δ (δ + loss) loss = (A.lossyBound (1 / 2 ^ b) : ℝ) := by
  simp only [LossyMca.lossyBound, Analysis.lossyBound, Analysis.curveT₁, NNReal.coe_add, hδ,
    hloss]
  push_cast
  rfl

end Analysis


theorem le_maxTerms {x : String × ℚ} : ∀ {l : List (String × ℚ)}, x ∈ l → x.2 ≤ maxTerms l
  | _ :: _, .head _ => le_max_left _ _
  | _ :: _, .tail _ h => (le_maxTerms h).trans (le_max_right _ _)

/-- Grinding's fraction times a term. -/
theorem powFraction_mul_le_ofReal (hp : Nat.card F = p) (bits : ℕ) {e : ENNReal} {x : ℚ}
    (h : e ≤ ENNReal.ofReal (x : ℝ)) :
    powFraction F bits * e ≤ ENNReal.ofReal ((powFractionQ p bits * x : ℚ) : ℝ) := by
  rw [powFraction_eq hp, Rat.cast_mul, ENNReal.ofReal_mul (powFractionQ_nonneg bits)]
  gcongr

/-! ### One setup -/

section Setup
variable {lookups : List (Lookup F)} (S : Iop.Setup EF lookups) (A : Analysis)

theorem rateQ_eq : (S.rateQ : ℝ) = S.rate := by
  rw [rate_eq, Iop.Setup.rateQ]
  push_cast
  rfl

theorem card_pow_pos (hp : Nat.card F = p) : (0 : ℚ) < (p : ℚ) ^ Challenge.d EF := by
  have : 0 < p := hp ▸ Nat.card_pos
  positivity

/-- `δ` of a valid analysis as a real. -/
theorem valid_real (hA : A.Valid S.rateQ) (δ : ℝ≥0) (hδ : (δ : ℝ) = A.δ) :
    0 < δ ∧ (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / 2 ^ A.t := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_pos, hδ]
    exact_mod_cast hA.1
  · have := (Rat.cast_le (K := ℝ)).mpr hA.2.2.2
    rw [← rateQ_eq, hδ]
    push_cast at this ⊢
    exact this

/-- `δ'` of a valid analysis as a real. -/
theorem udr_real (hA : A.Valid S.rateQ) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') :
    (δ' : ℝ) < (1 - S.rate) / 2 := by
  have := (Rat.cast_lt (K := ℝ)).mpr hA.2.2.1
  rw [← rateQ_eq, hδ']
  push_cast at this ⊢
  exact this

/-- `δ'` of a valid analysis is below `1 - rate`, as the soundness theorems ask. -/
theorem lt_one_sub_rate (hA : A.Valid S.rateQ) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') :
    (δ' : ℝ) < 1 - S.rate := by
  have h := udr_real S A hA δ' hδ'
  have : S.rate ≤ 1 := by
    rw [rate_eq]
    exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
  linarith

/-- FRI's radius of a valid analysis. -/
theorem coe_toNNReal_δ {ρ : ℚ} (hA : A.Valid ρ) : ((Real.toNNReal A.δ : ℝ≥0) : ℝ) = A.δ :=
  Real.coe_toNNReal _ (by exact_mod_cast hA.1.le)

/-- The radii of a fitting analysis as reals. -/
theorem fits_real (hA : S.Fits A) (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    (δ : ℝ) ≤ δ' - 2 / S.size ∧ (δ' : ℝ) < (1 - S.rate) / 2 := by
  refine ⟨?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).mpr hA.2.2
    rw [hδ, hδ']
    push_cast at this ⊢
    exact this
  · exact udr_real S A hA.2.1 δ' hδ'

theorem batchingNum_nonneg (m : ℕ) (hA : S.Fits A) : 0 ≤ S.batchingNum A m := by
  unfold Iop.Setup.batchingNum
  split_ifs with h
  · refine le_min (by positivity) (mul_nonneg (by positivity) (le_max_of_le_right ?_))
    exact div_nonneg (by linarith [hA.2.1.1]) (by linarith)
  · positivity

theorem queryDensity_nonneg (hA : A.Valid S.rateQ) : 0 ≤ S.queryDensity A := by
  have hρ : 0 ≤ S.rateQ := by rw [Iop.Setup.rateQ]; positivity
  have := hA.2.2.2
  have : (0 : ℚ) ≤ 1 / 2 ^ A.t := by positivity
  have : 0 ≤ ((S.logN - S.params.logFinalPolyLen : ℕ) : ℚ) * A.loss :=
    mul_nonneg (by positivity) hA.2.1.le
  unfold Iop.Setup.queryDensity
  linarith

theorem friFoldsNum_nonneg (hA : A.Valid S.rateQ) (injected : ℕ) :
    0 ≤ S.friFoldsNum A injected := by
  have := lossyBound_nonneg A hA
  unfold Iop.Setup.friFoldsNum
  positivity

/-- Constraint folding. -/
theorem foldingError_le_calc (hp : Nat.card F = p) (δ' : ℝ≥0)
    (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) :
    foldingError S δ' ≤
      ENNReal.ofReal ((((S.numConstraints - 1 : ℕ) : ℚ) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
  (foldingError_le_of_le S δ' hδ').trans (natCast_div_card_eq hp _).le

/-- The out-of-domain point. -/
theorem outOfDomainError_le_calc (hp : Nat.card F = p) (δ' : ℝ≥0)
    (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) :
    outOfDomainError S δ' ≤ ENNReal.ofReal
      ((((S.identityDegree + S.n : ℕ) : ℚ) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
  (outOfDomainError_le_of_le S δ' hδ').trans (natCast_div_card_eq hp _).le

/-- Batching `m` words: the powers MCA bound, and the curve bound for `δ < δ' - 2/N`. -/
theorem batchingErrorOf_le_calc (hp : Nat.card F = p) (m : ℕ) (hA : S.Fits A) (δ δ' : ℝ≥0)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    batchingErrorOf S m δ ((δ' : ℝ) - 2 / S.size) ≤
      ENNReal.ofReal ((S.batchingNum A m / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  obtain ⟨hle, hud⟩ := fits_real S A hA δ δ' hδ hδ'
  have h0 := (valid_real S A hA.2.1 δ hδ).1
  have hN : (0 : ℝ) ≤ 1 / S.size := by positivity
  have hN2 : (2 : ℝ) / S.size = 2 * (1 / S.size) := by ring
  have hmca : batchingErrorOf S m δ ((δ' : ℝ) - 2 / S.size) ≤ ENNReal.ofReal
      (((((m - 1) * S.size : ℕ) : ℚ) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
    have hNn : 2 ^ S.params.logBlowup * S.n ≤ S.size := by
      rw [Iop.Setup.n, Iop.Setup.size, pow_add, mul_comm]
    have : NeZero S.n := ⟨(Nat.two_pow_pos _).ne'⟩
    refine (batchingError_anti S m δ hle).trans ((batchingError_le_mcaError S m δ).trans ?_)
    rw [← natCast_div_card_eq hp]
    exact mcaError_powers_le (Nat.two_pow_pos _)
      ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans hNn) _
      (le_relUDR _ (by rw [Fintype.card_fin]; exact hNn) δ
        (mul_le_of_le_udr S δ (by linarith)))
  unfold Iop.Setup.batchingNum
  split_ifs with hlt
  · have hltR : (δ : ℝ) < δ' - 2 / S.size := by
      have := (Rat.cast_lt (K := ℝ)).mpr hlt
      rw [hδ, hδ']
      push_cast at this ⊢
      exact this
    have hcurve := batchingError_le_curve S m δ _ (by linarith) h0 hltR
    have hK := (card_pow_pos (EF := EF) hp).le
    rw [← min_div_div_right hK, Rat.cast_min, ENNReal.ofReal_min]
    refine le_min hmca (hcurve.trans (le_of_eq ?_))
    rw [← ofReal_div_card_eq hp, ← rateQ_eq, hδ, hδ']
    unfold Analysis.curveT₁
    push_cast
    rfl
  · exact hmca

/-- FRI with injected inputs at heights of at least `2 ^ t` points. -/
theorem friErrorWith_le_calc (hp : Nat.card F = p) (harity : S.params.maxLogArity = 1)
    (hA : A.Valid S.rateQ) (heights : List ℕ)
    (hfit : FriGame.Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights) (ht : ∀ m ∈ heights, A.t ≤ m) (δ : ℝ≥0)
    (hδ : (δ : ℝ) = A.δ) :
    friErrorWith S heights δ ≤ ENNReal.ofReal
      ((S.friFoldsNum A heights.length / (p : ℚ) ^ Challenge.d EF +
        S.queryDensity A ^ S.params.numQueries : ℚ) : ℝ) := by
  obtain ⟨h0, hδt⟩ := valid_real S A hA δ hδ
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.2.1
  set loss := Real.toNNReal A.loss
  have hloss : (loss : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have h := friErrorWith_le_lossy S harity A.t heights hfit ht δ (δ + loss) loss hδt h0
    (lt_add_of_pos_right _ (Real.toNNReal_pos.mpr hl0)) (Real.toNNReal_pos.mpr hl0)
  have hq0 := queryDensity_nonneg S A hA
  have hq : ((Real.toNNReal (1 - δ + (S.logN - S.params.logFinalPolyLen : ℕ) * loss) ^
      S.params.numQueries : ℝ≥0) : ENNReal) =
      ENNReal.ofReal ((S.queryDensity A ^ S.params.numQueries : ℚ) : ℝ) := by
    rw [ENNReal.coe_pow, Rat.cast_pow, ENNReal.ofReal_pow (by exact_mod_cast hq0)]
    congr 2
    rw [hδ, hloss, Iop.Setup.queryDensity]
    push_cast
    rfl
  have hfold : ENNReal.ofReal (((S.logN + S.params.logBlowup - A.t + heights.length : ℕ) : ℝ) *
      LossyMca.lossyBound 1 (2 ^ S.params.logBlowup) δ (δ + loss) loss) /
        (Fintype.card 𝕂 : ENNReal) + ((2 ^ A.t : ℕ) : ENNReal) / (Fintype.card 𝕂 : ENNReal) =
      ENNReal.ofReal ((S.friFoldsNum A heights.length / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
    have hK := card_pow_pos (EF := EF) hp
    have hL : 0 ≤ A.lossyBound (1 / 2 ^ S.params.logBlowup) := lossyBound_nonneg A hA
    rw [lossyBound_eq A _ δ loss hδ hloss, natCast_div_card_eq hp,
      show (((S.logN + S.params.logBlowup - A.t + heights.length : ℕ) : ℝ) *
        (A.lossyBound (1 / 2 ^ S.params.logBlowup) : ℝ)) =
        ((((S.logN + S.params.logBlowup - A.t + heights.length : ℕ) : ℚ) *
          A.lossyBound (1 / 2 ^ S.params.logBlowup) : ℚ) : ℝ) by push_cast; rfl,
      ofReal_div_card_eq hp, ← ENNReal.ofReal_add
        (Rat.cast_nonneg.mpr (div_nonneg (mul_nonneg (by positivity) hL) hK.le)) (by positivity)]
    congr 1
    rw [Iop.Setup.friFoldsNum, Iop.Setup.rateQ]
    push_cast
    ring
  rw [hq, hfold] at h
  have hK := card_pow_pos (EF := EF) hp
  have hF := friFoldsNum_nonneg S A hA heights.length
  refine h.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (Rat.cast_nonneg.mpr (div_nonneg hF hK.le))
    (Rat.cast_nonneg.mpr (pow_nonneg hq0 _))]
  push_cast
  rfl

/-- The knowledge error is at most the calculator's bound. -/
theorem knowledgeError_le_bound (hp : Nat.card F = p) (hA : S.Fits A) (δ δ' : ℝ≥0)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    knowledgeError S δ δ' ≤ ENNReal.ofReal (S.knowledgeErrorBound p A : ℝ) := by
  have hud := (fits_real S A hA δ δ' hδ hδ').2
  have h1 := foldingError_le_calc S hp δ' hud
  have h2 := outOfDomainError_le_calc S hp δ' hud
  have h3 := batchingErrorOf_le_calc S A hp S.numOpened hA δ δ' hδ hδ'
  have h4 := friErrorWith_le_calc S A hp hA.1 hA.2.1 [] (FriGame.Rounds.fits_nil _ _)
    (fun _ h ↦ absurd h List.not_mem_nil) δ hδ
  have hK := card_pow_pos (EF := EF) hp
  have hb := batchingNum_nonneg S A S.numOpened hA
  have hq := queryDensity_nonneg S A hA.2.1
  refine (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans (le_of_eq ?_)
  have h3' : (0 : ℝ) ≤ ((S.batchingNum A S.numOpened / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg hb hK.le)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) h3',
    ← ENNReal.ofReal_add (add_nonneg (by positivity) h3') (Rat.cast_nonneg.mpr
      (add_nonneg (div_nonneg (friFoldsNum_nonneg S A hA.2.1 _) hK.le) (pow_nonneg hq _)))]
  congr 1
  rw [Iop.Setup.knowledgeErrorBound, Iop.Setup.knowledgeErrorTerms]
  simp only [sumTerms, List.foldr, List.length_nil]
  push_cast
  ring

/-- The round error is at most the calculator's bound. -/
theorem roundError_le_bound (S : Iop.Setup EF) (hp : Nat.card F = p) (hA : S.Fits A)
    (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    roundError S δ δ' ≤ ENNReal.ofReal (S.roundErrorBound p A : ℝ) := by
  have hud := (fits_real S A hA δ δ' hδ hδ').2
  obtain ⟨h0, hδt⟩ := valid_real S A hA.2.1 δ hδ
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.2.1.2.1
  set loss := Real.toNNReal A.loss
  have hloss : (loss : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have hT {x : String × ℚ} (h : x ∈ S.roundErrorTerms p A) :
      ENNReal.ofReal (x.2 : ℝ) ≤ ENNReal.ofReal (S.roundErrorBound p A : ℝ) :=
    ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (le_maxTerms h))
  refine (iInf_le _ loss).trans (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))
  · exact (foldingError_le_calc S hp δ' hud).trans (hT (.head _))
  · exact (powFraction_mul_le_ofReal hp _ (outOfDomainError_le_calc S hp δ' hud)).trans
      (hT (.tail _ (.head _)))
  · exact (powFraction_mul_le_ofReal hp _
      (batchingErrorOf_le_calc S A hp S.numOpened hA δ δ' hδ hδ')).trans
      (hT (.tail _ (.tail _ (.head _))))
  · refine (powFraction_mul_le_ofReal hp _ ((friFoldError_le S hA.1 A.t δ (δ + loss) loss hδt h0
      (lt_add_of_pos_right _ (Real.toNNReal_pos.mpr hl0)) (Real.toNNReal_pos.mpr hl0)).trans
        (le_of_eq ?_))).trans (hT (.tail _ (.tail _ (.tail _ (.head _)))))
    rw [lossyBound_eq A _ δ loss hδ hloss, ← ofReal_div_card_eq hp]
    push_cast
    rfl
  · have hq0 := queryDensity_nonneg S A hA.2.1
    have hp0 : (0 : ℚ) ≤ 1 / p := by positivity
    refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    rw [friQueryError_eq S hA.1, hp, hδ, hloss, Rat.cast_pow,
      ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (add_nonneg hq0 hp0))]
    congr 2
    rw [Iop.Setup.queryDensity]
    push_cast
    rfl

end Setup

/-! ### Batches -/

section Batch
variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups) (A : Analysis)

theorem groupNumOpened_eq (m : ℕ) : S.groupNumOpened m = S.groupNumOpenedL m := by
  rw [Iop.Batch.Setup.groupNumOpened, Finset.sum_filter, Fin.sum_univ_def]
  rfl

theorem le_maxInstances (f : Fin S.k → ℚ) (i : Fin S.k) : f i ≤ S.maxInstances f :=
  le_maxQ (List.mem_map_of_mem (List.mem_finRange i))

theorem fits_instance (hA : S.Fits A) (i : Fin S.k) : (S.instanceSetup i).Fits A :=
  ⟨hA.1, hA.2.1, hA.2.2.1 i (List.mem_finRange i)⟩

/-- `δ'` of a fitting analysis is below `1 - rate`, as the soundness theorems ask. -/
theorem batch_lt_one_sub_rate (hA : S.Fits A) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') :
    (δ' : ℝ) < 1 - S.rate := by
  have := lt_one_sub_rate S.domainSetup A hA.2.1 δ' hδ'
  rwa [Batch.rate_instanceSetup] at this

/-- The lookup challenges. -/
theorem lookupError_le_calc (hp : Nat.card F = p) (hA : S.Fits A) (δ' : ℝ≥0)
    (hδ' : (δ' : ℝ) = A.δ') :
    S.lookupError δ' ≤
      ENNReal.ofReal ((S.lookupNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  rw [Iop.Batch.Setup.lookupError]
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _).trans (natCast_div_card_eq hp _).le
  exact (Nat.mul_le_mul_right _ (Finset.prod_le_one fun i _ ↦ listSize_le_one
    (S.instanceSetup i) _ δ' (udr_real (S.instanceSetup i) A hA.2.1 δ' hδ'))).trans
      (by rw [one_mul])

/-- Instance `i`'s constraint folding, out-of-domain and batching terms. -/
theorem instance_le_calc (hp : Nat.card F = p) (hA : S.Fits A) (δ δ' : ℝ≥0)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') (i : Fin S.k) :
    foldingError (S.instanceSetup i) δ' ≤
        ENNReal.ofReal ((S.foldingNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) ∧
      outOfDomainError (S.instanceSetup i) δ' ≤
        ENNReal.ofReal ((S.outOfDomainNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) ∧
      batchingErrorOf (S.instanceSetup i) (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
          ((δ' : ℝ) - 2 / (S.instanceSetup i).size) ≤
        ENNReal.ofReal ((S.maxInstances (S.batchingNum A) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  have hfi := fits_instance S A hA i
  have hud := (fits_real _ A hfi δ δ' hδ hδ').2
  have hK := (card_pow_pos (EF := EF) hp).le
  refine ⟨(foldingError_le_calc _ hp δ' hud).trans (ofReal_div_le (le_maxInstances S
      (fun i ↦ (((S.instanceSetup i).numConstraints - 1 : ℕ) : ℚ)) i) _ hK),
    (outOfDomainError_le_calc _ hp δ' hud).trans (ofReal_div_le (le_maxInstances S
      (fun i ↦ (((S.instanceSetup i).identityDegree + (S.instanceSetup i).n : ℕ) : ℚ)) i) _ hK),
    ?_⟩
  rw [groupNumOpened_eq]
  exact (batchingErrorOf_le_calc _ A hp _ hfi δ δ' hδ hδ').trans
    (ofReal_div_le (le_maxInstances S (S.batchingNum A) i) _ hK)

/-- The batch's knowledge error is at most the calculator's bound. -/
theorem batchKnowledgeError_le_bound (hp : Nat.card F = p) (hA : S.Fits A) (δ δ' : ℝ≥0)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.knowledgeError S δ δ' ≤ ENNReal.ofReal (S.knowledgeErrorBound p A : ℝ) := by
  have hK := card_pow_pos (EF := EF) hp
  have h1 := lookupError_le_calc S A hp hA δ' hδ'
  have h2 : (⨆ i, S.instanceError δ δ' i) ≤
      ENNReal.ofReal ((S.foldingNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) +
        ENNReal.ofReal ((S.outOfDomainNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) +
        ENNReal.ofReal ((S.maxInstances (S.batchingNum A) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    iSup_le fun i ↦ by
      obtain ⟨a, b, c⟩ := instance_le_calc S A hp hA δ δ' hδ hδ' i
      exact add_le_add (add_le_add a b) c
  have h3 := friErrorWith_le_calc S.domainSetup A hp hA.1 hA.2.1 S.friHeights
    (fits_friHeights S) hA.2.2.2 δ hδ
  have hq := queryDensity_nonneg S.domainSetup A hA.2.1
  have hF := friFoldsNum_nonneg S.domainSetup A hA.2.1 S.friHeights.length
  have ha : (0 : ℝ) ≤ ((S.lookupNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg (by unfold Iop.Batch.Setup.lookupNum; positivity) hK.le)
  have hb : (0 : ℝ) ≤ ((S.foldingNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg (maxQ_nonneg _) hK.le)
  have hc : (0 : ℝ) ≤ ((S.outOfDomainNum / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg (maxQ_nonneg _) hK.le)
  have hd : (0 : ℝ) ≤ ((S.maxInstances (S.batchingNum A) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg (maxQ_nonneg _) hK.le)
  have he : (0 : ℝ) ≤ ((S.domainSetup.friFoldsNum A S.friHeights.length /
      (p : ℚ) ^ Challenge.d EF + S.domainSetup.queryDensity A ^ S.params.numQueries : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (add_nonneg (div_nonneg hF hK.le) (pow_nonneg hq _))
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add hb hc, ← ENNReal.ofReal_add (add_nonneg hb hc) hd,
    ← ENNReal.ofReal_add ha (add_nonneg (add_nonneg hb hc) hd),
    ← ENNReal.ofReal_add (add_nonneg ha (add_nonneg (add_nonneg hb hc) hd)) he]
  congr 1
  rw [Iop.Batch.Setup.knowledgeErrorBound, Iop.Batch.Setup.knowledgeErrorTerms]
  simp only [sumTerms, List.foldr]
  push_cast
  ring

/-- The batch's round error is at most the calculator's bound. -/
theorem batchRoundError_le_bound (hp : Nat.card F = p) (hA : S.Fits A) (δ δ' : ℝ≥0)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.roundError S δ δ' ≤ ENNReal.ofReal (S.roundErrorBound p A : ℝ) := by
  obtain ⟨h0, hδt⟩ := valid_real S.domainSetup A hA.2.1 δ hδ
  rw [Batch.rate_instanceSetup] at hδt
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.2.1.2.1
  set loss := Real.toNNReal A.loss
  have hloss : (loss : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have hT {x : String × ℚ} (h : x ∈ S.roundErrorTerms p A) :
      ENNReal.ofReal (x.2 : ℝ) ≤ ENNReal.ofReal (S.roundErrorBound p A : ℝ) :=
    ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (le_maxTerms h))
  have hi := instance_le_calc S A hp hA δ δ' hδ hδ'
  refine (iInf_le _ loss).trans
    (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))))
  · exact (powFraction_mul_le_ofReal hp _ (lookupError_le_calc S A hp hA δ' hδ')).trans
      (hT (.head _))
  · exact (iSup_le fun i ↦ (hi i).1).trans (hT (.tail _ (.head _)))
  · exact (powFraction_mul_le_ofReal hp _ (iSup_le fun i ↦ (hi i).2.1)).trans
      (hT (.tail _ (.tail _ (.head _))))
  · exact (powFraction_mul_le_ofReal hp _ (iSup_le fun i ↦ (hi i).2.2)).trans
      (hT (.tail _ (.tail _ (.tail _ (.head _)))))
  · refine (powFraction_mul_le_ofReal hp _ ((Batch.friFoldErrorB_le S hA.1 A.t hA.2.2.2 δ (δ + loss)
      loss hδt h0 (lt_add_of_pos_right _ (Real.toNNReal_pos.mpr hl0))
        (Real.toNNReal_pos.mpr hl0)).trans (le_of_eq ?_))).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    rw [lossyBound_eq A _ δ loss hδ hloss, ← ofReal_div_card_eq hp]
    push_cast
    rfl
  · have hq0 := queryDensity_nonneg S.domainSetup A hA.2.1
    have hp0 : (0 : ℚ) ≤ 1 / p := by positivity
    refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    rw [Batch.friQueryErrorB_eq S hA.1, hp, hδ, hloss, Rat.cast_pow,
      ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (add_nonneg hq0 hp0))]
    congr 2
    rw [Iop.Setup.queryDensity]
    push_cast
    rfl

end Batch

end CompStark.Sound
