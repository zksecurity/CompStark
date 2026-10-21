/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.PowersMca
public import CompStark.Sound.Johnson
public import CompStark.Sound.Fri
public import CompStark.Sound.Batching
public import CompStark.Sound.LossyMca

/-! # Bounds on the knowledge error's terms below the unique-decoding radius

At FRI arity `2`, with the extractor's radius below the unique-decoding radius `(1 - rate) / 2`,
each term of the knowledge error is an integer over `|𝕂|`, except FRI's queries and the curve
bounds on batching and FRI's large folds:

* the candidate lists have at most one element (`listSize_le_one`), so the constraint-folding and
  out-of-domain terms are at most `#constraints - 1` and `identityDegree + n`;
* every code involved, the trace's and each folded FRI code, has the rate `1 / 2 ^ logBlowup`, so
  a radius below `(1 - rate) / 2` is within its relative unique-decoding radius (`le_relUDR`), and
  the powers MCA bound `mcaError_powers_le` gives `(numOpened - 1) N` for batching at a single
  radius (`batchingError_le_mcaError`, and so at every larger one, `batchingError_anti`) and `|L'|`
  for a fold onto the domain `L'`;
* batching at `δ < δ'' = δ' - 2/N` is at most `(numOpened - 1) max(T₁, T₂)`
  (`batchingError_le_curve`);
* FRI at a proximity loss `loss > 0` (`friError_le_lossy`): a fold onto a domain `L'` with
  `δ ≤ (1 - rate) / 2 - 1 / |L'|` has lossy MCA error at most `max(T₁, T₂, δ_int / loss)`
  (`lossyMcaError_line_le`, any `δ_int > δ`), independent of `|L'|`; the smaller domains, below a
  threshold `2 ^ t`, take the lossless bound `|L'|` and sum to at most `2 ^ t`; the queries
  contribute `(1 - δ + #folds · loss) ^ numQueries`.

`knowledgeError_le_of_le` (the MCA bound) and `knowledgeError_le_curve` (the curve bound) collect
the terms other than FRI's; `numbers_le` and `numbers_curve_le` close the arithmetic for
`CompStark/Security.lean`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal ProximityGap CoreDefinitions Code

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF


/-- At rate at most `1/c`, a radius `θ ≤ (1 - 1/c) / 2` is within the relative unique-decoding
radius of a Reed–Solomon code. -/
theorem le_relUDR {ι : Type} [Fintype ι] {F : Type} [Field F] [DecidableEq F]
    {domain : ι ↪ F} {deg : ℕ} [NeZero deg] (c : ℕ) (h : c * deg ≤ Fintype.card ι) (θ : ℝ≥0)
    (hθ : (θ : ℝ) * (2 * c) ≤ c - 1) :
    θ ≤ relativeUniqueDecodingRadius (ReedSolomon.code domain deg : Set (ι → F)) := by
  have hdeg := NeZero.pos deg
  have hc : 1 ≤ c := by
    by_contra hc0
    have : c = 0 := by omega
    subst this
    have := θ.coe_nonneg
    norm_num at hθ
  have hcard : (0 : ℝ≥0) < Fintype.card ι := by
    exact_mod_cast (show 0 < Fintype.card ι from lt_of_lt_of_le (by positivity) h)
  have hle : deg ≤ Fintype.card ι := le_trans (Nat.le_mul_of_pos_left _ hc) h
  rw [relativeUniqueDecodingRadius, dist_eq_minDist, ReedSolomon.minDist_of_le hle,
    Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, div_div, le_div_iff₀ (by positivity),
    ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_sub hle]
  push_cast
  have h' : (c * deg : ℝ) ≤ Fintype.card ι := by exact_mod_cast h
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hθ hk
  nlinarith

/-- The degree of FRI's code after fold `i` is a `c`-th of its domain when the initial code's
is. -/
theorem mul_foldingDegree_eq {N k : ℕ} (c : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
    (i : Fin (k + 1)) (h : c * (2 ^ (∑ j, (s j).val) * d.val) = 2 ^ N) :
    c * Fri.Spec.foldingDegree s d i.succ =
      2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) := by
  have hq := Fri.Spec.foldingPrefix_le s i.succ
  rw [Fri.Spec.foldingPrefix_succ] at hq
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · rw [zero_mul] at h
      exact absurd h.symm (Nat.two_pow_pos N).ne'
    · exact hc
  have hsN : ∑ j, (s j).val ≤ N := by
    by_contra hlt
    have : 2 ^ N < 2 ^ (∑ j, (s j).val) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ (∑ j, (s j).val) ≤ c * (2 ^ (∑ j, (s j).val) * d.val) :=
      (Nat.le_mul_of_pos_right _ d.pos).trans (Nat.le_mul_of_pos_left _ hc)
    omega
  set q := Fri.Spec.foldingPrefix s i.castSucc + (s i).val
  have hpq : N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val = N - q := by omega
  rw [hpq, Fri.Spec.foldingDegree, Fri.Spec.foldingPrefix_succ]
  refine Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos q) ?_
  rw [← pow_add, Nat.sub_add_cancel (by omega)]
  calc c * (2 ^ (∑ j, (s j).val - q) * d.val) * 2 ^ q
      = c * (2 ^ (∑ j, (s j).val - q + q) * d.val) := by rw [pow_add]; ring
    _ = c * (2 ^ (∑ j, (s j).val) * d.val) := by rw [Nat.sub_add_cancel hq]
    _ = 2 ^ N := h

/-- One FRI fold's error at rate `1/c` and a radius `θ ≤ (1 - 1/c) / 2`: the powers MCA bound
`(2 ^ s - 1) |L'| / |𝕂|` on the folded domain `L'`. -/
theorem foldingError_le {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂} (c : ℕ) (hc : 0 < c)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1))
    (h : c * (2 ^ (∑ j, (s j).val) * d.val) = 2 ^ N) (θ : ℝ≥0) (hθ : (θ : ℝ) * (2 * c) ≤ c - 1) :
    (Fri.Spec.foldingError (ω := ω) s d (θ : ℝ) i : ENNReal) ≤
      ((2 ^ (s i).val - 1) * 2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) : ℕ) /
        (Fintype.card 𝕂 : ENNReal) := by
  have hc' := (mul_foldingDegree_eq c s d i h).le
  have : NeZero (Fri.Spec.foldingDegree s d i.succ) := ⟨(Fri.Spec.foldingDegree_pos s d _).ne'⟩
  have hle : Fri.Spec.foldingDegree s d i.succ ≤
      2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) :=
    (Nat.le_mul_of_pos_left _ hc).trans hc'
  unfold Fri.Spec.foldingError
  rw [ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact mcaError_powers_le (Fri.Spec.foldingDegree_pos s d _) hle _
    (le_relUDR c (by rw [Fintype.card_fin]; exact hc') θ hθ)

/-- A nonnegative proximity loss can only lower a fold's error. -/
theorem foldingErrorLossy_le_foldingError {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1)) (θ loss : ℝ) (hloss : 0 ≤ loss) :
    (Fri.Spec.foldingErrorLossy (ω := ω) s d θ loss i : ENNReal) ≤
      Fri.Spec.foldingError (ω := ω) s d θ i := by
  unfold Fri.Spec.foldingErrorLossy Fri.Spec.foldingError
  rw [ENNReal.coe_toNNReal (lossyMcaError_ne_top _ _ _ _),
    ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact lossyMcaError_le_mcaError _ _ _ hloss

/-- `lossyBound` depends on the code only through its rate. -/
theorem lossyBound_congr {k n k' n' : ℕ} (h : (k : ℝ) / n = (k' : ℝ) / n') (δ_fld δ_int : ℝ≥0)
    (loss : ℝ) :
    LossyMca.lossyBound k n δ_fld δ_int loss = LossyMca.lossyBound k' n' δ_fld δ_int loss := by
  rw [LossyMca.lossyBound, LossyMca.lossyBound, h]

/-- One FRI fold's error at rate `1/c` on a folded domain `L'` with
`θ ≤ (1 - 1/c) / 2 - 1 / |L'|`: the lossy bound `(2 ^ s - 1) max(T₁, T₂, δ_int / loss) / |𝕂|`,
independent of `|L'|`. -/
theorem foldingErrorLossy_le {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂} (c : ℕ)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1))
    (h : c * (2 ^ (∑ j, (s j).val) * d.val) = 2 ^ N) (θ δ_int : ℝ≥0) (loss : ℝ)
    (hθ : (θ : ℝ) ≤ (1 - 1 / c) / 2 -
      1 / (2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) : ℕ))
    (h_pos : 0 < θ) (h_lt : θ < δ_int) (h_loss : 0 < loss) :
    (Fri.Spec.foldingErrorLossy (ω := ω) s d θ loss i : ENNReal) ≤
      ENNReal.ofReal ((2 ^ (s i).val - 1) * LossyMca.lossyBound 1 c θ δ_int loss /
        Fintype.card 𝕂) := by
  have hc' := mul_foldingDegree_eq c s d i h
  have hc : 0 < c := Nat.pos_of_ne_zero fun hc ↦ by
    rw [hc, zero_mul] at hc'
    exact (Nat.two_pow_pos _).ne' hc'.symm
  have hrate : (Fri.Spec.foldingDegree s d i.succ : ℝ) /
      (Fintype.card (Fin (2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val))) : ℝ) =
      ((1 : ℕ) : ℝ) / (c : ℕ) := by
    rw [Fintype.card_fin, ← hc', Nat.cast_mul, Nat.cast_one]
    have : (0 : ℝ) < c := by exact_mod_cast hc
    have : (0 : ℝ) < Fri.Spec.foldingDegree s d i.succ := by
      exact_mod_cast Fri.Spec.foldingDegree_pos s d _
    field_simp
  unfold Fri.Spec.foldingErrorLossy
  rw [ENNReal.coe_toNNReal (lossyMcaError_ne_top _ _ _ _), ← lossyBound_congr hrate]
  refine LossyMca.lossyMcaError_fold_le _ _ _ θ δ_int loss ?_ h_pos h_lt h_loss
  rw [hrate, Fintype.card_fin, Nat.cast_one]
  exact hθ

/-- Folding by arity `2` halves `r` times. -/
theorem folds_one : ∀ r, folds 1 r = List.replicate r 1
  | 0 => by rw [folds]; rfl
  | r + 1 => by
    rw [folds, List.replicate_succ]
    congr 1
    rw [show r + 1 - max 1 (min 1 (r + 1)) = r by omega]
    exact folds_one r

theorem foldsAt_replicate (m : ℕ) (j : Fin ((List.replicate m (1 : ℕ+)).length + 1)) :
    foldsAt 1 (List.replicate m 1) j = 1 := by
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    simp only [foldsAt, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
      List.getElem_replicate]

/-- At arity `2`, `i` folds precede fold `i`. -/
theorem foldingPrefix_replicate (m : ℕ) (i : Fin ((List.replicate m (1 : ℕ+)).length + 2)) :
    Fri.Spec.foldingPrefix (foldsAt 1 (List.replicate m 1)) i = i := by
  induction i using Fin.induction with
  | zero => rw [Fri.Spec.foldingPrefix_zero, Fin.val_zero]
  | succ i ih =>
    rw [Fri.Spec.foldingPrefix_succ, ih, foldsAt_replicate, PNat.one_coe, Fin.val_succ,
      Fin.val_castSucc]

/-- The folds onto domains smaller than `2 ^ t` sum to at most `2 ^ t`: with `r ≤ N` folds,
`2 ^ min (N - r) t` more still fit. -/
theorem sum_small_add_le (N t : ℕ) : ∀ r, r ≤ N →
    ∑ j ∈ Finset.range r, (if t + j + 1 ≤ N then 0 else 2 ^ (N - j - 1)) +
      2 ^ min (N - r) t ≤ 2 ^ t
  | 0, _ => by
    rw [Finset.sum_range_zero, zero_add]
    exact Nat.pow_le_pow_right two_pos (min_le_right _ _)
  | r + 1, h => by
    have ih := sum_small_add_le N t r (by omega)
    rw [Finset.sum_range_succ]
    obtain ⟨a, ha⟩ : ∃ a, N - r = a + 1 := ⟨N - r - 1, by omega⟩
    rw [show N - (r + 1) = a by omega, show N - r - 1 = a by omega]
    rw [ha] at ih
    by_cases hta : t + r + 1 ≤ N
    · rw [ite_eq_left hta, add_zero, min_eq_right (by omega)]
      rwa [min_eq_right (by omega)] at ih
    · rw [ite_eq_right hta, min_eq_left (by omega), add_assoc, ← two_mul, ← pow_succ']
      by_cases hat : a + 1 ≤ t
      · rwa [min_eq_left hat] at ih
      · rw [min_eq_right (by omega)] at ih
        rw [show a + 1 = t by omega]
        exact ih

/-- At most `N - t` folds are onto domains of at least `2 ^ t` points. -/
theorem card_large_le (N t r : ℕ) :
    ((Finset.range r).filter fun j ↦ t + j + 1 ≤ N).card ≤ N - t := by
  refine (Finset.card_le_card fun j hj ↦ ?_).trans (Finset.card_range (N - t)).le
  rw [Finset.mem_filter] at hj
  exact Finset.mem_range.mpr (by omega)

/-- FRI's error with arity `2` and `m + 1` folds at rate `1/c`, from lossy correlated agreement
at a proximity loss `loss > 0`, for a radius `δ ≤ (1 - 1/c) / 2 - 1 / 2 ^ t`: the at most `N - t`
folds onto domains of at least `2 ^ t` points contribute the lossy bound
`max(T₁, T₂, δ_int / loss) / |𝕂|` each, the smaller ones the powers MCA bound, their domains
`2 ^ t` together, and the queries `(1 - δ + (m + 1) loss) ^ l`. -/
theorem friErrorOf_replicate_le {N : ℕ} (ω : Domain.SmoothCosetFftDomain N 𝕂) (m : ℕ)
    (logFinal l : ℕ) (c t : ℕ) (hc : 0 < c) (δ δ_int loss : ℝ≥0)
    (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ) (h_lt : δ < δ_int)
    (h_loss : 0 < loss) (h : c * 2 ^ (m + 1 + logFinal) = 2 ^ N) :
    friErrorOf ω (List.replicate (m + 1) 1) logFinal l δ ≤
      ENNReal.ofReal ((N - t : ℕ) * LossyMca.lossyBound 1 c δ δ_int loss) /
          (Fintype.card 𝕂 : ENNReal) +
        (2 ^ t : ℕ) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ + (m + 1) * loss) ^ l : ℝ≥0) : ENNReal) := by
  have hsum : ∑ j, (foldsAt 1 (List.replicate m 1) j).val = m + 1 := by
    simp only [foldsAt_replicate, PNat.one_coe, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, List.length_replicate, smul_eq_mul, mul_one]
  have hh : c * (2 ^ (∑ j, (foldsAt 1 (List.replicate m 1) j).val) *
      (finalDegree logFinal).val) = 2 ^ N := by
    change c * (2 ^ _ * 2 ^ logFinal) = 2 ^ N
    rw [hsum, ← pow_add]
    exact h
  have hdom : 2 ^ (∑ j, (foldsAt 1 (List.replicate m 1) j).val) * (finalDegree logFinal).val ≤
      2 ^ N := (Nat.le_mul_of_pos_left _ hc).trans hh.le
  have hmN : m + 1 ≤ N := by
    by_contra hlt
    have : 2 ^ N < 2 ^ (m + 1 + logFinal) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := Nat.le_mul_of_pos_left (2 ^ (m + 1 + logFinal)) hc
    omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hudr : (δ : ℝ) * (2 * c) ≤ c - 1 := by
    have h2 : (0 : ℝ) < 1 / 2 ^ t := by positivity
    have h3 : ((1 - 1 / c) / 2 : ℝ) * (2 * c) = c - 1 := by field_simp
    nlinarith
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  set B := LossyMca.lossyBound 1 c δ δ_int loss
  rw [List.replicate_succ]
  simp only [friErrorOf, hdom, ↓reduceIte]
  refine (iInf_le _ loss).trans ?_
  simp only [Fri.Spec.soundnessErrorLossy, ENNReal.coe_add, ENNReal.ofNNReal_finsetSum]
  refine add_le_add ?_ (le_of_eq ?_)
  · -- Each fold: the lossy bound on large domains, the powers MCA bound on small ones.
    have hfold : ∀ j : Fin ((List.replicate m (1 : ℕ+)).length + 1),
        (Fri.Spec.foldingErrorLossy (ω := ω) (foldsAt 1 (List.replicate m 1))
          (finalDegree logFinal) δ loss j : ENNReal) ≤
        if t + j + 1 ≤ N then ENNReal.ofReal B / Fintype.card 𝕂
        else ((2 ^ (N - j - 1) : ℕ) : ENNReal) / Fintype.card 𝕂 := by
      intro j
      split_ifs with hj
      · refine (foldingErrorLossy_le c _ _ j hh δ δ_int loss ?_ h_pos h_lt h_loss).trans
          (le_of_eq ?_)
        · simp only [foldingPrefix_replicate, foldsAt_replicate, PNat.one_coe,
            Fin.val_castSucc]
          have hpow : (2 : ℝ) ^ t ≤ ((2 ^ (N - j - 1) : ℕ) : ℝ) := by
            push_cast
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have := one_div_le_one_div_of_le (by positivity) hpow
          linarith
        · simp only [foldsAt_replicate, PNat.one_coe, pow_one]
          rw [show ((2 : ℝ) - 1) = 1 by norm_num, one_mul, ENNReal.ofReal_div_of_pos hK,
            ENNReal.ofReal_natCast]
      · refine (foldingErrorLossy_le_foldingError _ _ j _ _ loss.coe_nonneg).trans
          ((foldingError_le c hc _ _ j hh δ hudr).trans (le_of_eq ?_))
        simp only [foldsAt_replicate, foldingPrefix_replicate, PNat.one_coe, pow_one,
          Nat.add_one_sub_one, one_mul, Fin.val_castSucc]
    refine (Finset.sum_le_sum fun j _ ↦ hfold j).trans ?_
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ if t + j + 1 ≤ N then ENNReal.ofReal B /
      Fintype.card 𝕂 else ((2 ^ (N - j - 1) : ℕ) : ENNReal) / Fintype.card 𝕂),
      List.length_replicate, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
      ← ENNReal.sum_div, ← Nat.cast_sum]
    refine add_le_add ?_ (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _)
    · rw [← mul_div_assoc]
      refine ENNReal.div_le_div_right ?_ _
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      exact mul_le_mul_left (Nat.cast_le.mpr (card_large_le N t (m + 1))) _
    · have := sum_small_add_le N t (m + 1) hmN
      rw [Finset.sum_filter] at *
      calc ∑ j ∈ Finset.range (m + 1), (if ¬ t + j + 1 ≤ N then 2 ^ (N - j - 1) else 0)
          = ∑ j ∈ Finset.range (m + 1), (if t + j + 1 ≤ N then 0 else 2 ^ (N - j - 1)) :=
            Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> rfl
        _ ≤ 2 ^ t := le_trans (Nat.le_add_right _ _) this
  · -- The queries: `min` picks the larger loss `(m + 1) loss`.
    congr 2
    simp only [List.length_replicate]
    rw [min_eq_right (by nlinarith [loss.coe_nonneg])]
    congr 1
    ring

/-! ### The terms of a setup -/

/-- The rate is `1 / 2 ^ logBlowup`. -/
theorem rate_eq (S : Setup EF) : S.rate = 1 / 2 ^ S.params.logBlowup := by
  rw [Setup.rate, Setup.n, Setup.size, pow_add]
  push_cast
  field_simp

/-- Below the unique-decoding radius `(1 - rate) / 2`, with `c = 2 ^ logBlowup`. -/
theorem mul_le_of_le_udr (S : Setup EF) (δ : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) :
    (δ : ℝ) * (2 * (2 ^ S.params.logBlowup : ℕ)) ≤ (2 ^ S.params.logBlowup : ℕ) - 1 := by
  rw [rate_eq, le_div_iff₀ two_pos] at hδ
  have hc : (0 : ℝ) < 2 ^ S.params.logBlowup := by positivity
  have h1 := mul_le_mul_of_nonneg_right hδ hc.le
  have h2 : (1 - 1 / (2 : ℝ) ^ S.params.logBlowup) * 2 ^ S.params.logBlowup =
      2 ^ S.params.logBlowup - 1 := by field_simp
  push_cast
  nlinarith

/-- Below the unique-decoding radius, the lists have at most one element. -/
theorem foldingError_le_of_le (S : Setup EF) (δ : ℝ≥0) (hδ : (δ : ℝ) < (1 - S.rate) / 2) :
    foldingError S δ ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  calc S.listSize (Fin S.air.width) δ * (S.air.constraints.length - 1)
      ≤ 1 * (S.air.constraints.length - 1) :=
        Nat.mul_le_mul_right _ (listSize_le_one S _ δ hδ)
    _ = _ := one_mul _

/-- The out-of-domain term below the unique-decoding radius. -/
theorem outOfDomainError_le_of_le (S : Setup EF) (δ : ℝ≥0) (hδ : (δ : ℝ) < (1 - S.rate) / 2) :
    outOfDomainError S δ ≤
      (S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  have h := Nat.mul_le_mul_right S.identityDegree (Nat.mul_le_mul
    (listSize_le_one S (Fin S.air.width) δ hδ)
    (listSize_le_one S (Fin S.chunks × Fin (Challenge.d EF)) δ hδ))
  omega

/-- The batching term at a single radius below the unique-decoding radius: the powers MCA bound
`(numOpened - 1) N / |𝕂|`. -/
theorem batchingError_le_of_le (S : Setup EF) (δ : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) :
    batchingError S δ δ ≤ ((S.numOpened - 1) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  have hN : 2 ^ S.params.logBlowup * S.n ≤ S.size := by
    rw [Setup.n, Setup.size, pow_add, mul_comm]
  have hb := S.blowup
  have : NeZero S.n := ⟨(Nat.two_pow_pos _).ne'⟩
  refine (batchingError_le_mcaError S δ).trans ?_
  exact mcaError_powers_le (Nat.two_pow_pos _)
    ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans hN) _
    (le_relUDR _ (by rw [Fintype.card_fin]; exact hN) δ (mul_le_of_le_udr S δ hδ))

/-- FRI's term at arity `2` from lossy correlated agreement, at a proximity loss `loss > 0` and a
radius `δ ≤ (1 - rate) / 2 - 1 / 2 ^ t`: the at most `log₂ N - t` folds onto domains of at least
`2 ^ t` points contribute `max(T₁, T₂, δ_int / loss) / |𝕂|` each (`lossyMcaError_line_le`, any
`δ_int > δ`), the smaller ones `2 ^ t / |𝕂|` together, and the queries
`(1 - δ + #folds · loss) ^ numQueries`. -/
theorem friError_le_lossy (S : Setup EF) (harity : S.params.maxLogArity = 1) (t : ℕ)
    (δ δ_int loss : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ)
    (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    friError S δ ≤
      ENNReal.ofReal ((S.logN + S.params.logBlowup - t : ℕ) *
          LossyMca.lossyBound 1 (2 ^ S.params.logBlowup) δ δ_int loss) /
          (Fintype.card 𝕂 : ENNReal) +
        (2 ^ t : ℕ) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ + (S.logN - S.params.logFinalPolyLen : ℕ) * loss) ^
          S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hlt := S.folds
  obtain ⟨m, hm⟩ : ∃ m, S.logN - S.params.logFinalPolyLen = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  rw [friError, harity, hm, folds_one, Nat.cast_add, Nat.cast_one]
  refine friErrorOf_replicate_le _ _ _ _ _ _ (Nat.two_pow_pos _) _ _ _ ?_ h_pos h_lt h_loss ?_
  · rw [rate_eq] at hδ
    push_cast
    exact hδ
  · rw [show m + 1 + S.params.logFinalPolyLen = S.logN by omega, ← pow_add, add_comm]

/-- The knowledge error with FRI at `δ` and the extractor at `δ' ≥ δ + 2/N` below the
unique-decoding radius, with the MCA bound for batching: one integer over `|𝕂|`, and FRI's
error. -/
theorem knowledgeError_le_of_le (S : Setup EF) (δ δ' : ℝ≥0) (hδ : (δ : ℝ) ≤ δ' - 2 / S.size)
    (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) :
    knowledgeError S δ δ' ≤
      ((S.air.constraints.length - 1) + (S.identityDegree + S.n) +
        (S.numOpened - 1) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) + friError S δ := by
  have hδu : (δ : ℝ) ≤ (1 - S.rate) / 2 :=
    hδ.trans ((sub_le_self _ (by positivity)).trans hδ'.le)
  calc knowledgeError S δ δ'
      ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          (S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          ((S.numOpened - 1) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) + friError S δ :=
        add_le_add (add_le_add (add_le_add (foldingError_le_of_le S δ' hδ')
          (outOfDomainError_le_of_le S δ' hδ')) ((batchingError_anti S δ hδ).trans
            (batchingError_le_of_le S δ hδu))) le_rfl
    _ = _ := by
        simp only [ENNReal.div_add_div_same, Nat.cast_add]

/-- The knowledge error with FRI at `δ` and the extractor at `δ'` below the unique-decoding
radius, `δ < δ' - 2/N`, with the curve bound for batching at `δ' - 2/N`
(`batchingError_le_curve`), and FRI's error. -/
theorem knowledgeError_le_curve (S : Setup EF) (δ δ' : ℝ≥0)
    (h_ud : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / S.size) (h_pos : 0 < δ)
    (h_lt : (δ : ℝ) < δ' - 2 / S.size) (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) :
    knowledgeError S δ δ' ≤
      ((S.air.constraints.length - 1) + (S.identityDegree + S.n) : ℕ) /
          (Fintype.card 𝕂 : ENNReal) +
        ENNReal.ofReal ((S.numOpened - 1 : ℕ) *
          max ((1 - S.rate - δ) / (δ * (1 - S.rate - 2 * δ)))
            ((δ' - 2 / S.size) / (δ' - 2 / S.size - δ))) /
          Fintype.card 𝕂 +
        friError S δ := by
  calc knowledgeError S δ δ'
      ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          (S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          ENNReal.ofReal ((S.numOpened - 1 : ℕ) *
            max ((1 - S.rate - δ) / (δ * (1 - S.rate - 2 * δ)))
              ((δ' - 2 / S.size) / (δ' - 2 / S.size - δ))) /
            Fintype.card 𝕂 + friError S δ :=
        add_le_add (add_le_add (add_le_add (foldingError_le_of_le S δ' hδ')
          (outOfDomainError_le_of_le S δ' hδ'))
            (batchingError_le_curve S δ _ h_ud h_pos h_lt)) le_rfl
    _ = _ := by
        simp only [Nat.cast_add, ENNReal.div_add_div_same]

/-! ### The numbers -/

/-- `|𝕂| = p ^ d`. -/
theorem card_eq : (Fintype.card 𝕂 : ℝ) = (Fintype.card F : ℝ) ^ Challenge.d EF := by
  rw [Challenge.card_spec, Nat.cast_pow]

/-- The terms of a knowledge error bound as one real number. -/
theorem terms_eq (A T : ℕ) (b c y : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hy : 0 ≤ y) (l : ℕ) :
    (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) + ENNReal.ofReal b / Fintype.card 𝕂 +
        (ENNReal.ofReal c / Fintype.card 𝕂 + (T : ENNReal) / Fintype.card 𝕂 +
          ((Real.toNNReal y ^ l : ℝ≥0) : ENNReal)) =
      ENNReal.ofReal ((A + b + c + T) / Fintype.card 𝕂 + y ^ l) := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by
    rw [card_eq]; exact pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  have hpow : ((Real.toNNReal y ^ l : ℝ≥0) : ENNReal) = ENNReal.ofReal (y ^ l) := by
    rw [ENNReal.ofReal_pow hy, ENNReal.coe_pow]
    rfl
  rw [hpow, ← ENNReal.ofReal_natCast A, ← ENNReal.ofReal_natCast T,
    ← ENNReal.ofReal_natCast (Fintype.card 𝕂), ← ENNReal.ofReal_div_of_pos hK,
    ← ENNReal.ofReal_div_of_pos hK, ← ENNReal.ofReal_div_of_pos hK,
    ← ENNReal.ofReal_div_of_pos hK, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- `2 ^ (-bits)` as a real number. -/
theorem inv_two_pow_eq (bits : ℕ) : (2 ^ bits : ENNReal)⁻¹ = ENNReal.ofReal (2 ^ bits)⁻¹ := by
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_inv_of_pos (by positivity)]

/-- The terms of a knowledge error bound with the curve bound on batching, bounded term by term
by `A₀`, `b₀`, `c₀`, `T₀` over `|𝕂| = p ^ d` and `y₀ ^ l`, are at most `2 ^ (-bits)` if those
bounds are. -/
theorem numbers_curve_le {bits : ℕ} (A A₀ T T₀ l : ℕ) (b b₀ c c₀ y y₀ : ℝ) (hA : A ≤ A₀)
    (hb : b ≤ b₀)
    (hc : c ≤ c₀) (hT : T ≤ T₀) (hy : y ≤ y₀) (hb₀ : 0 ≤ b₀) (hc₀ : 0 ≤ c₀) (hy₀ : 0 ≤ y₀)
    (h : (A₀ + b₀ + c₀ + T₀) / (Fintype.card F : ℝ) ^ Challenge.d EF + y₀ ^ l ≤ (2 ^ bits : ℝ)⁻¹) :
    (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) + ENNReal.ofReal b / Fintype.card 𝕂 +
        (ENNReal.ofReal c / Fintype.card 𝕂 + (T : ENNReal) / Fintype.card 𝕂 +
          ((Real.toNNReal y ^ l : ℝ≥0) : ENNReal)) ≤
      (2 ^ bits : ENNReal)⁻¹ := by
  calc (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) + ENNReal.ofReal b / Fintype.card 𝕂 +
        (ENNReal.ofReal c / Fintype.card 𝕂 + (T : ENNReal) / Fintype.card 𝕂 +
          ((Real.toNNReal y ^ l : ℝ≥0) : ENNReal))
      ≤ (A₀ : ENNReal) / (Fintype.card 𝕂 : ENNReal) + ENNReal.ofReal b₀ / Fintype.card 𝕂 +
        (ENNReal.ofReal c₀ / Fintype.card 𝕂 + (T₀ : ENNReal) / Fintype.card 𝕂 +
          ((Real.toNNReal y₀ ^ l : ℝ≥0) : ENNReal)) := by
        gcongr
    _ = ENNReal.ofReal ((A₀ + b₀ + c₀ + T₀) / Fintype.card 𝕂 + y₀ ^ l) :=
        terms_eq _ _ _ _ _ hb₀ hc₀ hy₀ _
    _ ≤ (2 ^ bits : ENNReal)⁻¹ := by
        rw [inv_two_pow_eq, card_eq]
        exact ENNReal.ofReal_le_ofReal h

/-- `numbers_curve_le` with the MCA bound on batching, part of the integer `A`. -/
theorem numbers_le {bits : ℕ} (A A₀ T T₀ l : ℕ) (c c₀ y y₀ : ℝ) (hA : A ≤ A₀) (hc : c ≤ c₀)
    (hT : T ≤ T₀)
    (hy : y ≤ y₀) (hc₀ : 0 ≤ c₀) (hy₀ : 0 ≤ y₀)
    (h : (A₀ + c₀ + T₀) / (Fintype.card F : ℝ) ^ Challenge.d EF + y₀ ^ l ≤ (2 ^ bits : ℝ)⁻¹) :
    (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) +
        (ENNReal.ofReal c / Fintype.card 𝕂 + (T : ENNReal) / Fintype.card 𝕂 +
          ((Real.toNNReal y ^ l : ℝ≥0) : ENNReal)) ≤
      (2 ^ bits : ENNReal)⁻¹ := by
  have h' := numbers_curve_le A A₀ T T₀ l 0 0 c c₀ y y₀ hA le_rfl hc hT hy le_rfl hc₀ hy₀
    (by rwa [add_zero])
  rwa [ENNReal.ofReal_zero, ENNReal.zero_div, add_zero] at h'

end CompStark.Sound
