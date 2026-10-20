/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Numbers
public import CompStark.NonInteractiveError

/-! # Bounds on the round errors of one random-oracle answer

The terms of `roundError` (`CompStark/NonInteractiveError.lean`) at FRI arity `2`, with the
extractor's radius below the unique-decoding radius, as in `CompStark/Sound/Numbers.lean`:

* constraint folding, out of domain and batching as for the knowledge error;
* each FRI fold: the lossy bound `max(T₁, T₂, δ_int / loss)` on a domain of at least `2 ^ t`
  points, the powers MCA bound `|L'| < 2 ^ t` on a smaller one (`friFoldError_le`);
* FRI's queries: `(1 - δ + #folds · loss + 1/p) ^ numQueries` (`friQueryError_eq`).

`roundError_le` collects them at one proximity loss.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4

/-- A schedule of arity `2` everywhere folds once per round: `i` folds precede fold `i`. -/
theorem foldingPrefix_ones {k : ℕ} (s : Fin (k + 1) → ℕ+) (hs : ∀ j, s j = 1) (i : Fin (k + 2)) :
    Fri.Spec.foldingPrefix s i = i := by
  induction i using Fin.induction with
  | zero => rw [Fri.Spec.foldingPrefix_zero, Fin.val_zero]
  | succ i ih =>
    rw [Fri.Spec.foldingPrefix_succ, ih, hs, PNat.one_coe, Fin.val_succ, Fin.val_castSucc]

/-- One fold of a schedule of arity `2` at rate `1/c` and a radius `δ ≤ (1 - 1/c) / 2 - 1 / 2 ^ t`:
the lossy bound if its domain has at least `2 ^ t` points, the powers MCA bound below. -/
theorem foldingErrorLossy_ones_le {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂} (c : ℕ)
    (hc : 0 < c) (s : Fin (k + 1) → ℕ+) (hs : ∀ j, s j = 1) (d : ℕ+) (i : Fin (k + 1))
    (h : c * (2 ^ (∑ j, (s j).val) * d.val) = 2 ^ N) (t : ℕ) (δ δ_int loss : ℝ≥0)
    (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ) (h_lt : δ < δ_int)
    (h_loss : 0 < loss) :
    (Fri.Spec.foldingErrorLossy (ω := ω) s d δ loss i : ENNReal) ≤
      ENNReal.ofReal (max (LossyMca.lossyBound 1 c δ δ_int loss) (2 ^ t)) /
        (Fintype.card 𝕂 : ENNReal) := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hpre := foldingPrefix_ones s hs i.castSucc
  rw [Fin.val_castSucc] at hpre
  by_cases hj : t + i + 1 ≤ N
  · refine (foldingErrorLossy_le c s d i h δ δ_int loss ?_ h_pos h_lt h_loss).trans ?_
    · rw [hpre, hs, PNat.one_coe]
      have hpow : (2 : ℝ) ^ t ≤ ((2 ^ (N - i - 1) : ℕ) : ℝ) := by
        push_cast
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have := one_div_le_one_div_of_le (by positivity) hpow
      linarith
    · rw [hs, PNat.one_coe, pow_one, show ((2 : ℝ) - 1) = 1 by norm_num, one_mul,
        ENNReal.ofReal_div_of_pos hK, ENNReal.ofReal_natCast]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  · have hudr : (δ : ℝ) * (2 * c) ≤ c - 1 := by
      have h2 : (0 : ℝ) < 1 / 2 ^ t := by positivity
      have h3 : ((1 - 1 / c) / 2 : ℝ) * (2 * c) = c - 1 := by field_simp
      nlinarith
    refine (foldingErrorLossy_le_foldingError _ _ i _ _ loss.coe_nonneg).trans
      ((foldingError_le c hc _ _ i h δ hudr).trans ?_)
    rw [hpre, hs, PNat.one_coe, pow_one, Nat.add_one_sub_one, one_mul, ← ENNReal.ofReal_natCast]
    refine ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans' ?_)) _
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- At arity `2`, Plonky3's schedule halves `logN - logFinalPolyLen` times. -/
theorem foldArities_eq (S : Setup) (harity : S.params.maxLogArity = 1) :
    S.foldArities = List.replicate (S.logN - S.params.logFinalPolyLen) 1 := by
  rw [Setup.foldArities, harity, folds_one]

/-- At arity `2`, FRI folds `logN - logFinalPolyLen` times. -/
theorem lastFold_add_one (S : Setup) (harity : S.params.maxLogArity = 1) :
    S.lastFold + 1 = S.logN - S.params.logFinalPolyLen := by
  have := S.folds
  rw [Setup.lastFold, foldArities_eq S harity, List.length_replicate]
  omega

/-- At arity `2`, every fold halves. -/
theorem schedule_eq_one (S : Setup) (harity : S.params.maxLogArity = 1) (j : Fin (S.lastFold + 1)) :
    S.schedule j = 1 := by
  rw [Setup.schedule, foldArities_eq S harity, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split_ifs <;> rfl

/-- The largest error of FRI's folds at arity `2`, at a proximity loss `loss > 0` and a radius
`δ ≤ (1 - rate) / 2 - 1 / 2 ^ t`: `max(T₁, T₂, δ_int / loss, 2 ^ t) / |𝕂|` for any
`δ_int > δ`. -/
theorem friFoldError_le (S : Setup) (harity : S.params.maxLogArity = 1) (t : ℕ)
    (δ δ_int loss : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ)
    (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    ⨆ i, friFoldError S δ loss i ≤
      ENNReal.ofReal (max (LossyMca.lossyBound 1 (2 ^ S.params.logBlowup) δ δ_int loss)
        (2 ^ t)) / (Fintype.card 𝕂 : ENNReal) := by
  refine iSup_le fun i ↦ ?_
  have hs := schedule_eq_one S harity
  have hsum : ∑ j, (S.schedule j).val = S.logN - S.params.logFinalPolyLen := by
    simp only [hs, PNat.one_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    exact lastFold_add_one S harity
  have hfin := S.valid.finalPolyFits
  refine foldingErrorLossy_ones_le (2 ^ S.params.logBlowup) (Nat.two_pow_pos _) _ hs _ i ?_ t
    δ δ_int loss ?_ h_pos h_lt h_loss
  · change 2 ^ S.params.logBlowup * (2 ^ _ * 2 ^ S.params.logFinalPolyLen) = _
    rw [hsum, ← pow_add, ← pow_add]
    congr 1
    omega
  · rw [rate_eq] at hδ
    push_cast
    exact hδ

/-- FRI's queries at arity `2`: `(1 - δ + #folds · loss + 1/p) ^ numQueries`. -/
theorem friQueryError_eq (S : Setup) (harity : S.params.maxLogArity = 1) (δ loss : ℝ≥0) :
    friQueryError S δ loss =
      ENNReal.ofReal (1 - δ + (S.logN - S.params.logFinalPolyLen : ℕ) * loss +
        1 / KoalaBear.fieldSize) ^ S.params.numQueries := by
  rw [friQueryError, ← lastFold_add_one S harity, ZMod.card,
    min_eq_right (by nlinarith [loss.coe_nonneg])]
  congr 2
  push_cast
  ring

/-- No grinding: a proof-of-work sample of `0` bits always vanishes. -/
theorem powFraction_zero : powFraction 0 = 1 := by
  rw [powFraction, ZMod.card, KoalaBear.fieldSize]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- `powFraction` as a fraction of `p`. -/
theorem powFraction_eq (bits : ℕ) :
    powFraction bits = ((127 * 2 ^ (24 - bits) + 1 : ℕ) : ENNReal) / KoalaBear.fieldSize := by
  rw [powFraction, ZMod.card]

/-- The round errors at FRI arity `2`, FRI at `δ` and the extractor at `δ'` below the
unique-decoding radius, `δ < δ' - 2/N`, at one proximity loss `loss > 0` and a fold threshold
`2 ^ t`: constraint folding, out of domain, the curve bound for batching
(`batchingError_le_curve`), FRI's folds (`friFoldError_le`, `δ_int = δ + loss`) and FRI's
queries (`friQueryError_eq`). -/
theorem roundError_le (S : Setup) (harity : S.params.maxLogArity = 1) (t : ℕ)
    (δ δ' loss : ℝ≥0) (h_ud : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / S.size)
    (h_udt : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ)
    (h_lt : (δ : ℝ) < δ' - 2 / S.size) (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) (h_loss : 0 < loss) :
    roundError S δ δ' ≤
      (max ((S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal)) <|
      max ((S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal)) <|
      max (ENNReal.ofReal ((S.numOpened - 1 : ℕ) *
          max ((1 - S.rate - δ) / (δ * (1 - S.rate - 2 * δ)))
            ((δ' - 2 / S.size) / (δ' - 2 / S.size - δ))) / Fintype.card 𝕂) <|
      max (powFraction S.params.commitPowBits *
          (ENNReal.ofReal (max (LossyMca.lossyBound 1 (2 ^ S.params.logBlowup) δ (δ + loss) loss)
            (2 ^ t)) / Fintype.card 𝕂))
        (powFraction S.params.queryPowBits *
          ENNReal.ofReal (1 - δ + (S.logN - S.params.logFinalPolyLen : ℕ) * loss +
            1 / KoalaBear.fieldSize) ^ S.params.numQueries)) := by
  refine (iInf_le _ loss).trans ?_
  rw [← friQueryError_eq S harity]
  gcongr
  · exact foldingError_le_of_le S δ' hδ'
  · exact outOfDomainError_le_of_le S δ' hδ'
  · exact batchingError_le_curve S δ _ h_ud h_pos h_lt
  · exact friFoldError_le S harity t δ (δ + loss) loss h_udt h_pos
      (lt_add_of_pos_right _ h_loss) h_loss

/-! ### The numbers -/

/-- A radius `3/8 - 2 ^ (-a)`, as a real number. -/
theorem coe_three_eighths_sub (k : ℤ) (a : ℕ) (hk : k = -a) (ha : 2 ≤ a) :
    ((3 / 8 - 2 ^ k : NNReal) : ℝ) = 3 / 8 - 1 / 2 ^ a := by
  subst hk
  rw [NNReal.coe_sub, zpow_neg, zpow_natCast]
  · push_cast
    ring
  · rw [zpow_neg, zpow_natCast, ← NNReal.coe_le_coe]
    push_cast
    have : (2 : ℝ) ^ 2 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 2 ^ 2) this
    norm_num at this ⊢
    linarith

/-- An integer over `|𝕂| = p ^ 4` is at most `2 ^ (-100)` if it is as a real number. -/
theorem nat_div_card_le (A : ℕ) (h : (A : ℝ) / 2130706433 ^ 4 ≤ (2 ^ 100 : ℝ)⁻¹) :
    (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) ≤ (2 ^ 100 : ENNReal)⁻¹ := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by rw [card_eq]; positivity
  rw [← ENNReal.ofReal_natCast A, ← ENNReal.ofReal_natCast (Fintype.card 𝕂),
    ← ENNReal.ofReal_div_of_pos hK, inv_two_pow_eq, card_eq]
  exact ENNReal.ofReal_le_ofReal h

/-- A real number over `|𝕂| = p ^ 4` is at most `2 ^ (-100)` if it is as a real number. -/
theorem ofReal_div_card_le (b : ℝ) (h : b / 2130706433 ^ 4 ≤ (2 ^ 100 : ℝ)⁻¹) :
    ENNReal.ofReal b / (Fintype.card 𝕂 : ENNReal) ≤ (2 ^ 100 : ENNReal)⁻¹ := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by rw [card_eq]; positivity
  rw [← ENNReal.ofReal_natCast (Fintype.card 𝕂), ← ENNReal.ofReal_div_of_pos hK, inv_two_pow_eq,
    card_eq]
  exact ENNReal.ofReal_le_ofReal h

/-- A round with grinding, `powFraction bits` times `y ^ l`, is at most `2 ^ (-100)` if it is as
a real number. -/
theorem powFraction_mul_le (bits l : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (h : (127 * 2 ^ (24 - bits) + 1 : ℕ) / 2130706433 * y ^ l ≤ (2 ^ 100 : ℝ)⁻¹) :
    powFraction bits * ENNReal.ofReal y ^ l ≤ (2 ^ 100 : ENNReal)⁻¹ := by
  rw [powFraction_eq, KoalaBear.fieldSize, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_natCast (2 ^ 31 - 2 ^ 24 + 1), ← ENNReal.ofReal_div_of_pos (by norm_num),
    ← ENNReal.ofReal_pow hy, ← ENNReal.ofReal_mul (by positivity), inv_two_pow_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  norm_num at h ⊢
  exact h

end CompStark.Sound
