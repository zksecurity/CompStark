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
calculator's rationals for `|F| = p`, with the list sizes at `δ'` at most the calculator's list
bound (`listSize_le_listBound`: `listSize_le_one` below the unique-decoding radius,
`listSize_le_johnson` up to the Johnson radius). `knowledgeError_le_bound`, `roundError_le_bound`,
`batchKnowledgeError_le_bound` and `batchRoundError_le_bound` collect them.
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

/-- A real cast of a rational over `|𝕂| = p ^ d`. -/
theorem ofReal_div_card_eq' (hp : Nat.card F = p) (x : ℚ) :
    ENNReal.ofReal ((x : ℝ) / Fintype.card 𝕂) =
      ENNReal.ofReal ((x / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_div_of_pos hK, ENNReal.ofReal_natCast, ofReal_div_card_eq hp]

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

theorem le_maxTerms {x : String × ℚ} : ∀ {l : List (String × ℚ)}, x ∈ l → x.2 ≤ maxTerms l
  | _ :: _, .head _ => le_max_left _ _
  | _ :: _, .tail _ h => (le_maxTerms h).trans (le_max_right _ _)

/-- Grinding's fraction times a term. -/
theorem powFraction_mul_le_ofReal (hp : Nat.card F = p) (bits : ℕ) {e : ENNReal} {x : ℚ}
    (h : e ≤ ENNReal.ofReal (x : ℝ)) :
    powFraction F bits * e ≤ ENNReal.ofReal ((powFractionQ p bits * x : ℚ) : ℝ) := by
  rw [powFraction_eq hp, Rat.cast_mul, ENNReal.ofReal_mul (powFractionQ_nonneg bits)]
  gcongr

/-! ### The analysis -/

section Analysis
variable (A : Analysis)

theorem lossyBound_nonneg {ρ' : ℚ} (hA : A.Valid ρ') (ρ : ℚ) : 0 ≤ A.lossyBound ρ :=
  le_trans (div_nonneg (by linarith [hA.1, hA.2.1]) hA.2.1.le) (le_max_right _ _)

/-- The lossy bound for `δ` and `loss` equal to the analysis'. -/
theorem lossyBound_eq (b : ℕ) (δ loss : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hloss : (loss : ℝ) = A.loss) :
    LossyMca.lossyBound 1 (2 ^ b) δ (δ + loss) loss = (A.lossyBound (1 / 2 ^ b) : ℝ) := by
  simp only [LossyMca.lossyBound, Analysis.lossyBound, Analysis.curveT₁, NNReal.coe_add, hδ,
    hloss]
  push_cast
  rfl

theorem levelBound_nonneg (B : McaBound) (lb : ℕ) (f : ℕ × ℕ × Bool) {ρ : ℚ}
    (hA : A.Valid ρ) : 0 ≤ A.levelBound B lb f := by
  have hl := lossyBound_nonneg A hA (1 / 2 ^ lb)
  have hc := B.count_nonneg (2 ^ f.2.1) (2 ^ (f.2.1 - lb)) (FriGame.Rounds.foldWords f) A.δ
  unfold Analysis.levelBound
  dsimp only
  split_ifs
  · exact le_min (by positivity) hc
  · exact hc

/-- `2 ^ lb · deg = 2 ^ m` makes `deg = 2 ^ (m - lb)`. -/
theorem eq_two_pow_sub {lb m deg : ℕ} (h : 2 ^ lb * deg = 2 ^ m) : deg = 2 ^ (m - lb) := by
  have hdeg : 0 < deg := Nat.pos_of_ne_zero fun h0 ↦ by
    rw [h0, mul_zero] at h
    exact (Nat.two_pow_pos m).ne' h.symm
  have hlb : lb ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp
    (h ▸ Nat.le_mul_of_pos_right _ hdeg)
  refine Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos lb) ?_
  rw [h, ← pow_add, Nat.add_sub_cancel' hlb]

/-- The calculator's level bounds bound the folds of a plan that the MCA bound `B` admits, for `δ`
and `loss` equal to the analysis'. -/
theorem foldBounds_calc (B : McaBound) (hB : B.Holds) (lb : ℕ) (hA : A.Valid (1 / 2 ^ lb))
    (δ loss : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hloss : (loss : ℝ) = A.loss)
    (plan : List (ℕ × ℕ × Bool)) (hadm : A.Admits B lb plan) :
    FoldBounds 𝕂 (2 ^ lb) δ loss (fun f ↦ (A.levelBound B lb f : ℝ)) plan := by
  intro f hf
  refine ⟨Rat.cast_nonneg.mpr (levelBound_nonneg A B lb f hA), fun D deg hdeg ↦ ?_⟩
  have hdeg' := eq_two_pow_sub hdeg
  subst hdeg'
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  have hmca := mcaLevel_le B hB D (FriGame.Rounds.foldWords f) _ A.δ δ loss hδ loss.coe_nonneg
    (hadm f hf)
  unfold Analysis.levelBound
  dsimp only
  split_ifs with hl
  · have h0 : 0 < δ := by rw [← NNReal.coe_pos, hδ]; exact_mod_cast hA.1
    have hl0 : 0 < loss := by rw [← NNReal.coe_pos, hloss]; exact_mod_cast hA.2.1
    have hlossy := lossyLevel_le D (FriGame.Rounds.foldWords f) (2 ^ lb) _ hdeg δ (δ + loss) loss
      (by
        have := (Rat.cast_le (K := ℝ)).mpr hl
        rw [hδ]
        push_cast at this ⊢
        exact this)
      h0 (lt_add_of_pos_right _ hl0) (NNReal.coe_pos.mpr hl0)
    rw [lossyBound_eq A lb δ loss hδ hloss] at hlossy
    rw [Rat.cast_min, ← min_div_div_right hK.le, ENNReal.ofReal_min]
    refine le_min (hlossy.trans (le_of_eq ?_)) hmca
    push_cast
    rfl
  · exact hmca

/-- A sum of rationals over a plan, cast. -/
theorem cast_sum_map (q : ℕ × ℕ × Bool → ℚ) (plan : List (ℕ × ℕ × Bool)) :
    (((plan.map q).sum : ℚ) : ℝ) = (plan.map fun f ↦ (q f : ℝ)).sum := by
  rw [Rat.cast_list_sum, List.map_map]
  rfl

/-- The largest of rationals over a plan, cast. -/
theorem cast_maxQ_map (q : ℕ × ℕ × Bool → ℚ) :
    ∀ plan : List (ℕ × ℕ × Bool), ((maxQ (plan.map q) : ℚ) : ℝ) = planMax (fun f ↦ (q f : ℝ)) plan
  | [] => by simp only [List.map_nil, maxQ, List.foldr_nil, Rat.cast_zero, planMax]
  | f :: plan => by
    have ih := cast_maxQ_map q plan
    simp only [planMax, maxQ] at ih ⊢
    rw [List.map_cons, List.foldr_cons, Rat.cast_max, ih, List.map_cons, List.foldr_cons]

end Analysis

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

/-- `δ'` of a valid analysis is below the Johnson radius `1 - √rate`. -/
theorem lt_johnson (hA : A.Valid S.rateQ) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') :
    (δ' : ℝ) < 1 - √S.rate := by
  have h1 : (δ' : ℝ) < 1 := by rw [hδ']; exact_mod_cast hA.2.2.2.1
  have h2 : S.rate < (1 - (δ' : ℝ)) ^ 2 := by
    rw [← rateQ_eq, hδ']
    exact_mod_cast hA.2.2.2.2
  have := (Real.sqrt_lt' (by linarith)).mpr h2
  linarith

/-- `δ'` of a valid analysis is below `1 - rate`, as the soundness theorems ask. -/
theorem lt_one_sub_rate (hA : A.Valid S.rateQ) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') :
    (δ' : ℝ) < 1 - S.rate := by
  have h := lt_johnson S A hA δ' hδ'
  have h0 : 0 ≤ S.rate := by rw [rate_eq]; positivity
  have h1 : S.rate ≤ 1 := by
    rw [rate_eq]
    exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
  have : S.rate ≤ √S.rate := Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

/-- The lists at `δ'` have at most the calculator's list bound of elements: at most one below the
unique-decoding radius, and the Johnson bound up to the Johnson radius. -/
theorem listSize_le_listBound (hA : A.Valid S.rateQ) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ')
    (ι : Type) [Fintype ι] [DecidableEq ι] : S.listSize ι δ' ≤ A.listBound S.rateQ := by
  unfold Analysis.listBound
  split_ifs with h
  · refine listSize_le_one S ι δ' ?_
    rw [← rateQ_eq, hδ']
    exact_mod_cast h
  · refine listSize_le_johnson S ι δ' (lt_johnson S A hA δ' hδ') _ ?_
    have hD : (0 : ℚ) < (1 - A.δ') ^ 2 - S.rateQ := by linarith [hA.2.2.2.2]
    have hx := Nat.lt_floor_add_one ((1 - A.δ' - S.rateQ) / ((1 - A.δ') ^ 2 - S.rateQ))
    rw [div_lt_iff₀ hD] at hx
    have := (Rat.cast_lt (K := ℝ)).mpr hx
    rw [← rateQ_eq, hδ']
    push_cast at this ⊢
    exact this

/-- The permutation trace's list at `δ'` has at most the calculator's bound of elements. -/
theorem permListSize_le (hA : A.Valid S.rateQ) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') :
    S.permListSize δ' ≤ S.shape.permListBound S.params.logBlowup A := by
  cases lookups with
  | nil => exact le_rfl
  | cons l ls => exact listSize_le_listBound S A hA δ' hδ' _

/-- FRI's radius of a valid analysis. -/
theorem coe_toNNReal_δ {ρ : ℚ} (hA : A.Valid ρ) : ((Real.toNNReal A.δ : ℝ≥0) : ℝ) = A.δ :=
  Real.coe_toNNReal _ (by exact_mod_cast hA.1.le)

/-- `δ ≤ δ'`, as reals. -/
theorem le_real {ρ : ℚ} (hA : A.Valid ρ) (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ)
    (hδ' : (δ' : ℝ) = A.δ') : (δ : ℝ) ≤ δ' := by
  rw [hδ, hδ']
  exact_mod_cast hA.2.2.1

theorem batchingNum_nonneg (c : Shape) (lb : ℕ) (B : McaBound) (m : ℕ)
    (hA : A.Valid (1 / 2 ^ lb)) : 0 ≤ c.batchingNum lb B A m := by
  have hc := B.count_nonneg (2 ^ (c.logN + lb)) (2 ^ c.logN) (m - 1) A.δ
  unfold Shape.batchingNum
  dsimp only
  split_ifs with h
  · refine le_min hc (mul_nonneg (by positivity) (le_max_of_le_right ?_))
    exact div_nonneg (by linarith [hA.1, h.1]) (by linarith [h.1])
  · exact hc

theorem queryDensity_nonneg (hA : A.Valid S.rateQ) (heights : List ℕ) :
    0 ≤ S.queryDensity A heights := by
  have hρ : 0 ≤ S.rateQ := by rw [Iop.Setup.rateQ]; positivity
  have := hA.2.2.1
  have := hA.2.2.2.1
  have : 0 ≤ ((S.friPlan heights).length : ℚ) * A.loss := mul_nonneg (by positivity) hA.2.1.le
  unfold Iop.Setup.queryDensity
  linarith

theorem friFoldsNum_nonneg (B : McaBound) (hA : A.Valid S.rateQ) (heights : List ℕ) :
    0 ≤ S.friFoldsNum B A heights := by
  refine List.sum_nonneg fun x hx ↦ ?_
  obtain ⟨f, -, rfl⟩ := List.mem_map.mp hx
  exact levelBound_nonneg A B _ f hA

/-- Constraint folding. -/
theorem foldingError_le_calc (hp : Nat.card F = p) (hA : A.Valid S.rateQ) (δ' : ℝ≥0)
    (hδ' : (δ' : ℝ) = A.δ') :
    foldingError S δ' ≤ ENNReal.ofReal
      ((S.shape.foldingNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
  (foldingError_le_of_listSize S δ' _ _ (listSize_le_listBound S A hA δ' hδ' _)
    (permListSize_le S A hA δ' hδ')).trans (natCast_div_card_eq hp _).le

/-- The out-of-domain point. -/
theorem outOfDomainError_le_calc (hp : Nat.card F = p) (hA : A.Valid S.rateQ) (δ' : ℝ≥0)
    (hδ' : (δ' : ℝ) = A.δ') :
    outOfDomainError S δ' ≤
      ENNReal.ofReal ((S.shape.outOfDomainNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF :
        ℚ) : ℝ) :=
  (outOfDomainError_le_of_listSize S δ' _ (listSize_le_listBound S A hA δ' hδ' _)).trans
    (natCast_div_card_eq hp _).le

/-- Batching `m` words: the MCA bound `B`'s count where it admits the trace's code, and the curve
bound for `δ < δ'` and `δ ≤ (1 - rate) / 2 - 1/N`. -/
theorem batchingErrorOf_le_calc (hp : Nat.card F = p) (B : McaBound) (hB : B.Holds) (m : ℕ)
    (hA : A.Valid S.rateQ) (hadm : B.admits S.size S.n A.δ)
    (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    batchingErrorOf S m δ δ' ≤
      ENNReal.ofReal ((S.shape.batchingNum S.params.logBlowup B A m /
        (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  have hle' := le_real A hA δ δ' hδ hδ'
  have h0 : 0 < δ := by rw [← NNReal.coe_pos, hδ]; exact_mod_cast hA.1
  have hmca : batchingErrorOf S m δ δ' ≤ ENNReal.ofReal
      ((B.count S.size S.n (m - 1) A.δ / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
    refine (batchingError_anti S m δ hle').trans ((batchingError_le_mcaError S m δ).trans ?_)
    rw [← ofReal_div_card_eq' hp]
    have h := hB 𝕂 S.size S.n (m - 1) ⟨fun i ↦ S.domain i, (S.domain).injective⟩ A.δ hadm
    rw [← hδ] at h
    exact h
  unfold Shape.batchingNum
  dsimp only [Iop.Setup.shape]
  split_ifs with hlt
  · have hltR : (δ : ℝ) < δ' := by
      have := (Rat.cast_lt (K := ℝ)).mpr hlt.1
      rw [hδ, hδ']
      push_cast at this ⊢
      exact this
    have hudN : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / S.size := by
      have := (Rat.cast_le (K := ℝ)).mpr hlt.2
      rw [hδ, rate_eq]
      push_cast at this ⊢
      exact this
    have hcurve := batchingError_le_curve S m δ _ hudN h0 hltR
    have hK := (card_pow_pos (EF := EF) hp).le
    rw [← min_div_div_right hK, Rat.cast_min, ENNReal.ofReal_min]
    refine le_min hmca (hcurve.trans (le_of_eq ?_))
    rw [← ofReal_div_card_eq hp, rate_eq, hδ, hδ']
    unfold Analysis.curveT₁
    push_cast
    rfl
  · exact hmca

/-- FRI with injected inputs at any arity, with an MCA bound `B` that admits its folds. -/
theorem friErrorWith_le_calc (hp : Nat.card F = p) (B : McaBound) (hB : B.Holds)
    (hA : A.Valid S.rateQ) (heights : List ℕ)
    (hfit : FriGame.Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights)
    (hadm : A.Admits B S.params.logBlowup (S.friPlan heights)) (δ : ℝ≥0) (hδ : (δ : ℝ) = A.δ) :
    friErrorWith S heights δ ≤ ENNReal.ofReal
      ((S.friFoldsNum B A heights / (p : ℚ) ^ Challenge.d EF +
        S.queryDensity A heights ^ S.params.numQueries : ℚ) : ℝ) := by
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.2.1
  set loss := Real.toNNReal A.loss
  have hloss : (loss : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have h := friErrorWith_le S heights hfit δ loss _
    (foldBounds_calc A B hB _ hA δ loss hδ hloss _ hadm)
  have hq0 := queryDensity_nonneg S A hA heights
  have hq : ((Real.toNNReal (1 - δ + (S.friPlan heights).length * loss) ^
      S.params.numQueries : ℝ≥0) : ENNReal) =
      ENNReal.ofReal ((S.queryDensity A heights ^ S.params.numQueries : ℚ) : ℝ) := by
    rw [ENNReal.coe_pow, Rat.cast_pow, ENNReal.ofReal_pow (by exact_mod_cast hq0)]
    congr 2
    rw [hδ, hloss, Iop.Setup.queryDensity]
    push_cast
    rfl
  have hfold : ENNReal.ofReal (((S.friPlan heights).map fun f ↦
      (A.levelBound B S.params.logBlowup f : ℝ)).sum / Fintype.card 𝕂) =
      ENNReal.ofReal ((S.friFoldsNum B A heights / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
    rw [← cast_sum_map, ofReal_div_card_eq' hp]
    rfl
  change friErrorWith S heights δ ≤ ENNReal.ofReal (((S.friPlan heights).map fun f ↦
    (A.levelBound B S.params.logBlowup f : ℝ)).sum / Fintype.card 𝕂) + ((Real.toNNReal
      (1 - δ + (S.friPlan heights).length * loss) ^ S.params.numQueries : ℝ≥0) : ENNReal) at h
  rw [hq, hfold] at h
  have hK := card_pow_pos (EF := EF) hp
  have hF := friFoldsNum_nonneg S A B hA heights
  refine h.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (Rat.cast_nonneg.mpr (div_nonneg hF hK.le))
    (Rat.cast_nonneg.mpr (pow_nonneg hq0 _))]
  push_cast
  rfl

/-- The knowledge error is at most the calculator's bound with an MCA bound `B` that holds. -/
theorem knowledgeError_le_bound (hp : Nat.card F = p) (B : McaBound) (hB : B.Holds)
    (hA : S.Fits B A) (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    knowledgeError S δ δ' ≤ ENNReal.ofReal (S.knowledgeErrorBound p B A : ℝ) := by
  have h1 := foldingError_le_calc S A hp hA.1 δ' hδ'
  have h2 := outOfDomainError_le_calc S A hp hA.1 δ' hδ'
  have h3 := batchingErrorOf_le_calc S A hp B hB S.shape.numOpened hA.1 hA.2.1 δ δ' hδ
    hδ'
  have h4 := friErrorWith_le_calc S A hp B hB hA.1 [] (FriGame.Rounds.fits_nil _ _) hA.2.2 δ hδ
  have hK := card_pow_pos (EF := EF) hp
  have hb := batchingNum_nonneg A S.shape S.params.logBlowup B S.shape.numOpened hA.1
  have hq := queryDensity_nonneg S A hA.1 []
  have h1' : (0 : ℝ) ≤
      ((S.shape.foldingNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg (by unfold Shape.foldingNum; positivity) hK.le)
  have h2' : (0 : ℝ) ≤
      ((S.shape.outOfDomainNum S.params.logBlowup A / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg (by unfold Shape.outOfDomainNum; positivity) hK.le)
  have h3' : (0 : ℝ) ≤
      ((S.shape.batchingNum S.params.logBlowup B A S.shape.numOpened /
        (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg hb hK.le)
  refine (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add h1' h2', ← ENNReal.ofReal_add (add_nonneg h1' h2') h3',
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg h1' h2') h3') (Rat.cast_nonneg.mpr
      (add_nonneg (div_nonneg (friFoldsNum_nonneg S A B hA.1 _) hK.le) (pow_nonneg hq _)))]
  congr 1
  rw [Iop.Setup.knowledgeErrorBound, Iop.Setup.knowledgeErrorTerms,
    Iop.Setup.knowledgeErrorTermsOf]
  simp only [sumTerms, List.foldr]
  push_cast
  ring

/-- The round error is at most the calculator's bound with an MCA bound `B` that holds. -/
theorem roundError_le_bound (S : Iop.Setup EF) [S.Folds] (hp : Nat.card F = p) (B : McaBound)
    (hB : B.Holds) (hA : S.Fits B A) (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ)
    (hδ' : (δ' : ℝ) = A.δ') :
    roundError S δ δ' ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) := by
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.1.2.1
  set loss := Real.toNNReal A.loss
  have hloss : (loss : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have hT {x : String × ℚ} (h : x ∈ S.roundErrorTerms p B A) :
      ENNReal.ofReal (x.2 : ℝ) ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) :=
    ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (le_maxTerms h))
  refine (iInf_le _ loss).trans (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))
  · exact (foldingError_le_calc S A hp hA.1 δ' hδ').trans (hT (.head _))
  · exact (powFraction_mul_le_ofReal hp _ (outOfDomainError_le_calc S A hp hA.1 δ' hδ')).trans
      (hT (.tail _ (.head _)))
  · exact (powFraction_mul_le_ofReal hp _
      (batchingErrorOf_le_calc S A hp B hB S.numOpened hA.1 hA.2.1 δ δ' hδ hδ')).trans
      (hT (.tail _ (.tail _ (.head _))))
  · refine (powFraction_mul_le_ofReal hp _ ((friFoldError_le S δ loss _
      (foldBounds_calc A B hB _ hA.1 δ loss hδ hloss _ hA.2.2)).trans
        (le_of_eq ?_))).trans (hT (.tail _ (.tail _ (.tail _ (.head _)))))
    rw [← cast_maxQ_map, ofReal_div_card_eq' hp]
    rfl
  · have hq0 := queryDensity_nonneg S A hA.1 []
    have hp0 : (0 : ℚ) ≤ 1 / p := by positivity
    refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    rw [friQueryError_eq S, hp, hδ, hloss, Rat.cast_pow,
      ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (add_nonneg hq0 hp0))]
    congr 2
    rw [Iop.Setup.queryDensity]
    push_cast
    rfl

/-- Without FRI folds, the round error is at most the calculator's bound with an MCA bound `B`
that holds. -/
theorem roundError0_le_bound (S : Iop.Setup EF) (hp : Nat.card F = p) (B : McaBound)
    (hB : B.Holds) (hA : S.Fits B A) (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ)
    (hδ' : (δ' : ℝ) = A.δ') :
    roundError0 S δ δ' ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) := by
  have hT {x : String × ℚ} (h : x ∈ S.roundErrorTerms p B A) :
      ENNReal.ofReal (x.2 : ℝ) ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) :=
    ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (le_maxTerms h))
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · exact (foldingError_le_calc S A hp hA.1 δ' hδ').trans (hT (.head _))
  · exact (powFraction_mul_le_ofReal hp _ (outOfDomainError_le_calc S A hp hA.1 δ' hδ')).trans
      (hT (.tail _ (.head _)))
  · exact (powFraction_mul_le_ofReal hp _
      (batchingErrorOf_le_calc S A hp B hB S.numOpened hA.1 hA.2.1 δ δ' hδ hδ')).trans
      (hT (.tail _ (.tail _ (.head _))))
  · have hd1 : A.δ < 1 := lt_of_le_of_lt hA.1.2.2.1 hA.1.2.2.2.1
    have hp0 : (0 : ℚ) ≤ 1 / p := by positivity
    have hl : (0 : ℚ) ≤ ((S.friPlan []).length : ℚ) * A.loss := mul_nonneg (by positivity)
      hA.1.2.1.le
    refine (powFraction_mul_le_ofReal hp _ ?_).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    have h0 : (0 : ℝ) ≤ 1 - δ + 1 / Nat.card F := by
      rw [hδ, hp]
      have : (A.δ : ℝ) < 1 := by exact_mod_cast hd1
      positivity
    rw [friQueryError0, ← ENNReal.ofReal_pow h0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Rat.cast_pow]
    refine pow_le_pow_left₀ h0 ?_ _
    rw [hδ, hp, Iop.Setup.queryDensity]
    push_cast
    have : (0 : ℝ) ≤ ((S.friPlan []).length : ℝ) * (A.loss : ℝ) := by exact_mod_cast hl
    linarith

end Setup

/-! ### Shapes -/

section Shape

/-- The largest of `f` over a list is at most a bound on each. -/
theorem foldl_max_le {α : Type} (f : α → ℕ) (B : ℕ) :
    ∀ (l : List α) (m : ℕ), m ≤ B → (∀ x ∈ l, f x ≤ B) → l.foldl (fun m x ↦ max m (f x)) m ≤ B
  | [], _, hm, _ => hm
  | x :: l, _, hm, h => foldl_max_le f B l _ (max_le hm (h x List.mem_cons_self))
      fun y hy ↦ h y (List.mem_cons_of_mem _ hy)

/-- Without lookups, constraints whose degree profiles fit the quotient's chunks
(`Air.ProfileFits`) have the identity degree `n (chunks + 1)`. -/
theorem identityDegree_eq_of_profileFits (T : Iop.Setup EF)
    (h : T.air.ProfileFits (T.air.logQuotientChunks T.logN)) :
    T.identityDegree = T.n * (T.chunks + 1) := by
  rw [Iop.Setup.identityDegree_nil]
  refine max_eq_right (foldl_max_le _ _ _ _ (Nat.zero_le _) fun c hc ↦ ?_)
  have hle := c.degBound_le_profile (T.n + 1) (T.air.periodicDegree T.n)
    fun i ↦ (T.air.periodicDegree_le _ i).trans (Nat.le_succ _)
  obtain ⟨h1, h2⟩ := h c hc
  have hn : 1 ≤ T.n := Nat.one_le_two_pow
  rw [Nat.add_sub_cancel] at hle
  refine hle.trans ?_
  rw [Iop.Setup.chunks_nil, mul_comm T.n]
  have : c.degProfile.2 ≤ c.degProfile.2 * T.n := Nat.le_mul_of_pos_right _ hn
  nlinarith

/-- The shape of a setup without lookups whose constraints' degree profiles fit its chunks. -/
theorem shape_eq_of_profileFits (T : Iop.Setup EF)
    (h : T.air.ProfileFits (T.air.logQuotientChunks T.logN)) :
    T.shape = ⟨T.air.constraints.length, T.n * (T.chunks + 1), T.numOpened, false, T.logN⟩ := by
  rw [Iop.Setup.shape, identityDegree_eq_of_profileFits T h]
  rfl

/-- The calculator's certificate from a setup's shape `c`. -/
theorem secure_of_shape {lookups : List (Lookup F)} (S : Iop.Setup EF lookups) {c : Shape}
    (hc : S.shape = c) {B : McaBound} {A : Analysis} {bits : ℕ}
    (h : S.Fits B A ∧ sumTerms (S.knowledgeErrorTermsOf c p B A) ≤ 1 / 2 ^ bits) :
    S.Secure p B A bits := by
  rwa [Iop.Setup.Secure, Iop.Setup.knowledgeErrorBound, Iop.Setup.knowledgeErrorTerms, hc]

/-- The calculator's certificate per oracle answer from a setup's shape `c`. -/
theorem secureRo_of_shape (S : Iop.Setup EF) {c : Shape} (hc : S.shape = c) {B : McaBound}
    {A : Analysis} {bits : ℕ}
    (h : S.Fits B A ∧ maxTerms (S.roundErrorTermsOf c p B A) ≤ 1 / 2 ^ bits) :
    S.SecureRo p B A bits := by
  rwa [Iop.Setup.SecureRo, Iop.Setup.roundErrorBound, Iop.Setup.roundErrorTerms, hc]

end Shape

/-! ### Batches -/

section Batch
variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups) (B : McaBound) (A : Analysis)

/-- The opened words of instance `i`'s domain size, from the shapes. -/
theorem groupNumOpened_eq (i : Fin S.k) :
    S.groupNumOpened (S.logN i + S.params.logBlowup) = groupNumOpenedOf S.shapes (S.logN i) := by
  rw [Iop.Batch.Setup.groupNumOpened, Finset.sum_filter, Fin.sum_univ_def, groupNumOpenedOf,
    Iop.Batch.Setup.shapes, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ ↦ ?_
  simp only [Function.comp_apply, Iop.Setup.shape, Nat.add_right_cancel_iff]

theorem shape_mem (i : Fin S.k) : (S.instanceSetup i).shape ∈ S.shapes :=
  List.mem_map_of_mem (List.mem_finRange i)

theorem le_maxQ_shapes (f : Shape → ℚ) (i : Fin S.k) :
    f (S.instanceSetup i).shape ≤ maxQ (S.shapes.map f) :=
  le_maxQ (List.mem_map_of_mem (shape_mem S i))

/-- Instance `i`'s conditions of a fitting analysis. -/
theorem fits_instance (hA : S.Fits B A) (i : Fin S.k) :
    A.Valid (S.instanceSetup i).rateQ ∧
      B.admits (S.instanceSetup i).size (S.instanceSetup i).n A.δ :=
  ⟨hA.1, hA.2.1 i (List.mem_finRange i)⟩

/-- `δ'` of a fitting analysis is below `1 - rate`, as the soundness theorems ask. -/
theorem batch_lt_one_sub_rate (hA : S.Fits B A) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') :
    (δ' : ℝ) < 1 - S.rate := by
  have := lt_one_sub_rate S.domainSetup A hA.1 δ' hδ'
  rwa [Batch.rate_instanceSetup] at this

/-- The lookup challenges. -/
theorem lookupError_le_calc (hp : Nat.card F = p) (hA : S.Fits B A) (δ' : ℝ≥0)
    (hδ' : (δ' : ℝ) = A.δ') :
    S.lookupError δ' ≤ ENNReal.ofReal
      ((((A.listBound S.domainSetup.rateQ ^ S.k * S.lookupCount : ℕ) : ℚ) /
        (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  rw [Iop.Batch.Setup.lookupError]
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _ ?_)) _).trans
    (natCast_div_card_eq hp _).le
  refine (Finset.prod_le_pow_card _ _ _ fun i _ ↦ ?_).trans_eq (by rw [Finset.card_fin])
  exact listSize_le_listBound (S.instanceSetup i) A (fits_instance S B A hA i).1 δ' hδ' _

/-- Instance `i`'s constraint folding, out-of-domain and batching terms. -/
theorem instance_le_calc (hp : Nat.card F = p) (hB : B.Holds) (hA : S.Fits B A) (δ δ' : ℝ≥0)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') (i : Fin S.k) :
    foldingError (S.instanceSetup i) δ' ≤ ENNReal.ofReal
        ((maxQ (S.shapes.map (·.foldingNum S.params.logBlowup A)) / (p : ℚ) ^ Challenge.d EF :
          ℚ) : ℝ) ∧
      outOfDomainError (S.instanceSetup i) δ' ≤ ENNReal.ofReal
        ((maxQ (S.shapes.map (·.outOfDomainNum S.params.logBlowup A)) /
          (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) ∧
      batchingErrorOf (S.instanceSetup i) (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
          δ' ≤ ENNReal.ofReal
        ((maxQ (S.shapes.map fun c ↦ c.batchingNum S.params.logBlowup B A
          (groupNumOpenedOf S.shapes c.logN)) / (p : ℚ) ^ Challenge.d EF : ℚ) : ℝ) := by
  have hfi := fits_instance S B A hA i
  have hK := (card_pow_pos (EF := EF) hp).le
  refine ⟨(foldingError_le_calc _ A hp hfi.1 δ' hδ').trans
      (ofReal_div_le (le_maxQ_shapes S (·.foldingNum S.params.logBlowup A) i) _ hK),
    (outOfDomainError_le_calc _ A hp hfi.1 δ' hδ').trans
      (ofReal_div_le (le_maxQ_shapes S (·.outOfDomainNum S.params.logBlowup A) i) _ hK), ?_⟩
  rw [groupNumOpened_eq]
  exact (batchingErrorOf_le_calc _ A hp B hB _ hfi.1 hfi.2 δ δ' hδ hδ').trans
    (ofReal_div_le (le_maxQ_shapes S (fun c ↦ c.batchingNum S.params.logBlowup B A
      (groupNumOpenedOf S.shapes c.logN)) i) _ hK)

/-- The batch's knowledge error is at most the calculator's bound with an MCA bound `B` that
holds. -/
theorem batchKnowledgeError_le_bound (hp : Nat.card F = p) (hB : B.Holds) (hA : S.Fits B A)
    (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.knowledgeError S δ δ' ≤ ENNReal.ofReal (S.knowledgeErrorBound p B A : ℝ) := by
  have hK := card_pow_pos (EF := EF) hp
  set lb := S.params.logBlowup
  set K := (p : ℚ) ^ Challenge.d EF
  set a := (((A.listBound S.domainSetup.rateQ ^ S.k * S.lookupCount : ℕ) : ℚ) / K : ℚ)
  set b := maxQ (S.shapes.map (·.foldingNum lb A)) / K
  set c := maxQ (S.shapes.map (·.outOfDomainNum lb A)) / K
  set d := maxQ (S.shapes.map fun c ↦ c.batchingNum lb B A (groupNumOpenedOf S.shapes c.logN)) /
    K
  set e := S.domainSetup.friFoldsNum B A S.friHeights / K +
    S.domainSetup.queryDensity A S.friHeights ^ S.params.numQueries
  have h1 := lookupError_le_calc S B A hp hA δ' hδ'
  have h2 : (⨆ i, S.instanceError δ δ' i) ≤
      ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (d : ℝ) :=
    iSup_le fun i ↦ by
      obtain ⟨x, y, z⟩ := instance_le_calc S B A hp hB hA δ δ' hδ hδ' i
      exact add_le_add (add_le_add x y) z
  have h3 := friErrorWith_le_calc S.domainSetup A hp B hB hA.1 S.friHeights (fits_friHeights S)
    hA.2.2 δ hδ
  have hq := queryDensity_nonneg S.domainSetup A hA.1 S.friHeights
  have hF := friFoldsNum_nonneg S.domainSetup A B hA.1 S.friHeights
  have ha : (0 : ℝ) ≤ (a : ℝ) := Rat.cast_nonneg.mpr (div_nonneg (by positivity) hK.le)
  have hb : (0 : ℝ) ≤ (b : ℝ) := Rat.cast_nonneg.mpr (div_nonneg (maxQ_nonneg _) hK.le)
  have hc : (0 : ℝ) ≤ (c : ℝ) := Rat.cast_nonneg.mpr (div_nonneg (maxQ_nonneg _) hK.le)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Rat.cast_nonneg.mpr (div_nonneg (maxQ_nonneg _) hK.le)
  have he : (0 : ℝ) ≤ (e : ℝ) :=
    Rat.cast_nonneg.mpr (add_nonneg (div_nonneg hF hK.le) (pow_nonneg hq _))
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add hb hc, ← ENNReal.ofReal_add (add_nonneg hb hc) hd,
    ← ENNReal.ofReal_add ha (add_nonneg (add_nonneg hb hc) hd),
    ← ENNReal.ofReal_add (add_nonneg ha (add_nonneg (add_nonneg hb hc) hd)) he]
  congr 1
  rw [Iop.Batch.Setup.knowledgeErrorBound, Iop.Batch.Setup.knowledgeErrorTerms,
    Iop.Batch.Setup.knowledgeErrorTermsOf]
  simp only [sumTerms, List.foldr, a, b, c, d, e, K, lb]
  push_cast
  ring

/-- The batch's round error is at most the calculator's bound with an MCA bound `B` that holds. -/
theorem batchRoundError_le_bound (hp : Nat.card F = p) (hB : B.Holds) (hA : S.Fits B A)
    (δ δ' : ℝ≥0) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.roundError S δ δ' ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) := by
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.1.2.1
  set loss := Real.toNNReal A.loss
  have hloss : (loss : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have hT {x : String × ℚ} (h : x ∈ S.roundErrorTerms p B A) :
      ENNReal.ofReal (x.2 : ℝ) ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) :=
    ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (le_maxTerms h))
  have hi := instance_le_calc S B A hp hB hA δ δ' hδ hδ'
  refine (iInf_le _ loss).trans
    (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))))
  · exact (powFraction_mul_le_ofReal hp _ (lookupError_le_calc S B A hp hA δ' hδ')).trans
      (hT (.head _))
  · exact (iSup_le fun i ↦ (hi i).1).trans (hT (.tail _ (.head _)))
  · exact (powFraction_mul_le_ofReal hp _ (iSup_le fun i ↦ (hi i).2.1)).trans
      (hT (.tail _ (.tail _ (.head _))))
  · exact (powFraction_mul_le_ofReal hp _ (iSup_le fun i ↦ (hi i).2.2)).trans
      (hT (.tail _ (.tail _ (.tail _ (.head _)))))
  · refine (powFraction_mul_le_ofReal hp _ ((Batch.friFoldErrorB_le S δ loss _
      (foldBounds_calc A B hB _ hA.1 δ loss hδ hloss _ hA.2.2)).trans (le_of_eq ?_))).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    rw [← cast_maxQ_map, ofReal_div_card_eq' hp]
    rfl
  · have hq0 := queryDensity_nonneg S.domainSetup A hA.1 S.friHeights
    have hp0 : (0 : ℚ) ≤ 1 / p := by positivity
    refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    rw [Batch.friQueryErrorB_eq S, hp, hδ, hloss, Rat.cast_pow,
      ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (add_nonneg hq0 hp0))]
    congr 2
    rw [Iop.Setup.queryDensity]
    push_cast
    rfl

end Batch

/-! ### Batch statements -/

section Statement
variable (C : Iop.Batch.Statement F) (B : McaBound) (A : Analysis)

theorem le_foldr_max_nat : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: _, _, .tail _ h => (le_foldr_max_nat h).trans (le_max_right _ _)

theorem maxQ_le_maxQ {l l' : List ℚ} (h : ∀ x ∈ l, ∃ y ∈ l', x ≤ y) : maxQ l ≤ maxQ l' := by
  induction l with
  | nil => exact maxQ_nonneg l'
  | cons x l ih =>
    obtain ⟨y, hy, hxy⟩ := h x List.mem_cons_self
    exact max_le (hxy.trans (le_maxQ hy)) (ih fun z hz ↦ h z (List.mem_cons_of_mem _ hz))

theorem maxTerms_le {ε : ℚ} (h0 : 0 ≤ ε) : ∀ {l : List (String × ℚ)}, (∀ x ∈ l, x.2 ≤ ε) →
    maxTerms l ≤ ε
  | [], _ => h0
  | x :: l, h => max_le (h x List.mem_cons_self)
      (maxTerms_le h0 fun y hy ↦ h y (List.mem_cons_of_mem _ hy))

theorem powFractionQ_nonneg' (p bits : ℕ) : 0 ≤ powFractionQ p bits := by
  unfold powFractionQ
  positivity

/-- Batching grows with the number of words, for a valid analysis. -/
theorem batchingNum_mono (c : Shape) (lb : ℕ) (hA : A.Valid (1 / 2 ^ lb)) {m m' : ℕ}
    (h : m ≤ m') : c.batchingNum lb B A m ≤ c.batchingNum lb B A m' := by
  have hc : B.count (2 ^ (c.logN + lb)) (2 ^ c.logN) (m - 1) A.δ ≤
      B.count (2 ^ (c.logN + lb)) (2 ^ c.logN) (m' - 1) A.δ :=
    B.count_mono _ _ _ (Nat.sub_le_sub_right h 1)
  unfold Shape.batchingNum
  dsimp only
  split_ifs with hd
  · refine min_le_min hc (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.sub_le_sub_right h 1) (le_max_of_le_right ?_))
    exact div_nonneg (by linarith [hA.1, hd.1]) (by linarith [hd.1])
  · exact hc

variable (EF)

/-- **The calculator's batch statement bound is every admitted vector's.** If the calculator
certifies `bits` bits per oracle answer for the statement `C`, it does for the batch at every
vector of lengths the verifier admits. -/
theorem _root_.CompStark.Iop.Batch.Statement.secureRo_setupAt {p : ℕ} {B : McaBound}
    {A : Analysis} {bits : ℕ} (h : C.SecureRo EF p B A bits) (n : Fin C.k → ℕ)
    (hn : C.Admits n) : (C.setupAt EF n hn).SecureRo p B A bits := by
  obtain ⟨⟨hA, hBs, hBf⟩, hb⟩ := h
  set S := C.setupAt EF n hn with hS
  have hadm : ∀ i, C.admits i (n i) = true := (C.admits_iff n).mpr hn
  have hlt : ∀ i, n i < twoAdicity F + 1 := fun i ↦ by
    have := (hn.sound i).twoAdic; omega
  have hshapeAt : ∀ i, (S.instanceSetup i).shape ∈ C.shapesAt EF i := fun i ↦ by
    refine List.mem_flatMap.mpr ⟨n i, List.mem_range.mpr (hlt i), ?_⟩
    rw [dif_pos (hadm i)]
    exact List.mem_singleton.mpr rfl
  have hsub : ∀ c ∈ S.shapes, c ∈ C.allShapes EF := fun c hc ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
    exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hshapeAt i⟩
  have ha : 0 < C.params.maxLogArity := (S.valid S.top).folds
  have htop : S.logN S.top + C.params.logBlowup ≤ twoAdicity F := (S.valid S.top).twoAdic
  have hfit := fits_friHeights S
  have hplan : ∀ f ∈ S.domainSetup.friPlan S.friHeights, f ∈ C.foldPlans := fun f hf ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := FriGame.Rounds.mem_plan ha _ _ _ hfit f hf
    obtain ⟨la, m, inj⟩ := f
    change 1 ≤ la at h1
    change la ≤ C.params.maxLogArity at h2
    change C.params.logFinalPolyLen + C.params.logBlowup ≤ m at h3
    change m < S.logN S.top + C.params.logBlowup at h4
    refine List.mem_flatMap.mpr ⟨la, List.mem_range'_1.mpr ⟨h1, by omega⟩,
      List.mem_flatMap.mpr ⟨m, List.mem_range'_1.mpr ⟨h3, by omega⟩, ?_⟩⟩
    cases inj
    exacts [List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self]
  have hgroup : ∀ l, groupNumOpenedOf S.shapes l ≤ C.groupBound EF := fun l ↦ by
    calc groupNumOpenedOf S.shapes l ≤ (S.shapes.map (·.numOpened)).sum :=
          List.sum_le_sum fun c _ ↦ by split <;> omega
      _ ≤ C.groupBound EF := by
          rw [Iop.Batch.Setup.shapes, List.map_map]
          exact List.sum_le_sum fun i _ ↦ le_foldr_max_nat (List.mem_map_of_mem (hshapeAt i))
  have hlc : S.lookupCount ≤ C.lookupCountMax := by
    have hT : S.numInteractions ≤ ((List.finRange C.k).map fun i ↦
        2 ^ C.maxLength i * ((C.lookups i).map (·.tuples.length)).sum).sum := by
      rw [Iop.Batch.Setup.numInteractions, Fin.sum_univ_def]
      refine List.sum_le_sum fun i _ ↦ Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos ?_)
      exact le_foldr_max_nat (List.mem_filter.mpr ⟨List.mem_range.mpr (hlt i), hadm i⟩)
    unfold Iop.Batch.Setup.lookupCount Iop.Batch.Statement.lookupCountMax
    exact Nat.add_le_add hT (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hT 1))
  refine ⟨⟨hA, fun i _ ↦ hBs _ (hsub _ (shape_mem S i)), fun f hf ↦ hBf f (hplan f hf)⟩, ?_⟩
  have hK : (0 : ℚ) ≤ (p : ℚ) ^ Challenge.d EF := by positivity
  have hC : ∀ x ∈ C.roundErrorTerms EF p B A, x.2 ≤ 1 / 2 ^ bits := fun x hx ↦
    (le_maxTerms hx).trans hb
  have hmaxS : ∀ f : Shape → ℚ, maxQ (S.shapes.map f) ≤ maxQ ((C.allShapes EF).map f) :=
    fun f ↦ maxQ_le_maxQ fun x hx ↦ by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact ⟨_, List.mem_map_of_mem (hsub c hc), le_rfl⟩
  refine maxTerms_le (by positivity) fun x hx ↦ ?_
  simp only [Iop.Batch.Setup.roundErrorTerms, Iop.Batch.Setup.roundErrorTermsOf, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · refine le_trans ?_ (hC _ (.head _))
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (Nat.mul_le_mul_left _ hlc)) hK) (powFractionQ_nonneg' _ _)
  · exact le_trans (div_le_div_of_nonneg_right (hmaxS _) hK) (hC _ (.tail _ (.head _)))
  · exact le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hmaxS _) hK)
      (powFractionQ_nonneg' _ _)) (hC _ (.tail _ (.tail _ (.head _))))
  · refine le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (maxQ_le_maxQ fun x hx ↦ ?_) hK) (powFractionQ_nonneg' _ _))
      (hC _ (.tail _ (.tail _ (.tail _ (.head _)))))
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact ⟨_, List.mem_map_of_mem
      (f := fun c ↦ c.batchingNum C.params.logBlowup B A (C.groupBound EF)) (hsub c hc),
      batchingNum_mono B A c C.params.logBlowup hA (hgroup _)⟩
  · refine le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (maxQ_le_maxQ fun x hx ↦ ?_) hK) (powFractionQ_nonneg' _ _))
      (hC _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    exact ⟨_, List.mem_map_of_mem (hplan f hf), le_rfl⟩
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ (powFractionQ_nonneg' _ _))
      (hC _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    have hA' : A.Valid S.domainSetup.rateQ := hA
    have hq0 := queryDensity_nonneg S.domainSetup A hA' S.friHeights
    have hlen : (S.domainSetup.friPlan S.friHeights).length ≤ S.logN S.top +
        C.params.logBlowup - (C.params.logFinalPolyLen + C.params.logBlowup) :=
      FriGame.Rounds.length_plan_le ha _ _ _ hfit
    refine pow_le_pow_left₀ (add_nonneg hq0 (by positivity)) ?_ _
    unfold Iop.Setup.queryDensity
    have hl : ((S.domainSetup.friPlan S.friHeights).length : ℚ) ≤
        ((twoAdicity F - (C.params.logFinalPolyLen + C.params.logBlowup) : ℕ) : ℚ) :=
      Nat.cast_le.mpr (le_trans hlen (by omega))
    have := mul_le_mul_of_nonneg_right hl hA.2.1.le
    linarith

end Statement

end CompStark.Sound
