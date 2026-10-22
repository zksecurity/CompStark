/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.NumbersNi
public import CompStark.BatchNonInteractiveError
public import CompStark.Sound.BatchAssembly
public import CompStark.Sound.BatchRbr

/-! # Bounds on the batch round errors of one random-oracle answer

The terms of the batch `roundError` (`CompStark/BatchNonInteractiveError.lean`) at FRI arity `2`,
with the extractor's radius below the unique-decoding radius, as for the STARK
(`CompStark/Sound/NumbersNi.lean`):

* constraint folding, out of domain and batching at the worst instance, as for the batch
  knowledge error;
* each FRI fold: on a domain of at least `2 ^ t` points the lossy bound, twice for a fold that
  injects a shorter instance's word (`levelError_le`), and the powers MCA bound `|L'| < 2 ^ t` on
  a smaller one (`foldErrorAt_schedule_one_le`, `friFoldErrorB_le`);
* FRI's queries: `(1 - δ + #folds · loss + 1/p) ^ numQueries`.

`batchRoundError_le` collects them at one proximity loss.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal FriGame ProximityGap CoreDefinitions Code

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Every fold's error of Plonky3's schedule at arity `2` and rate `1/c` (`c d = 2 ^ logFinal`),
with inputs injected at heights of at least `2 ^ t` points: at most `max(2 B, 2 ^ t) / |𝕂|`, `B`
the lossy bound. -/
theorem foldErrorAt_schedule_one_le (c t : ℕ) (hc : 0 < c) (d logFinal : ℕ)
    (hd : c * d = 2 ^ logFinal) (δ δ_int loss : ℝ≥0)
    (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ) (h_lt : δ < δ_int)
    (h_loss : 0 < loss) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂) :
    ∀ (fuel n : ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂) (heights : List ℕ) (j : ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Rounds.Fits logFinal n heights →
      (∀ m ∈ heights, t ≤ m) →
      (Rounds.schedule 1 logFinal words fuel n heights).foldErrorAt d δ loss j ω ≤
        ENNReal.ofReal (max (2 * LossyMca.lossyBound 1 c δ δ_int loss) (2 ^ t) /
          Fintype.card 𝕂)
  | 0, n, ω, heights, j, hn, hfuel, hfit, ht => by
    rw [Rounds.schedule, Rounds.foldErrorAt]
    exact bot_le
  | fuel + 1, n, ω, heights, j, hn, hfuel, hfit, ht => by
    by_cases hfin : n ≤ logFinal
    · rw [Rounds.schedule, ite_eq_left hfin, Rounds.foldErrorAt]
      exact bot_le
    have hB : 0 ≤ LossyMca.lossyBound 1 c δ δ_int loss :=
      le_trans (by positivity) (le_max_right _ _)
    have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
    have hla := Rounds.logArity_one (by omega) hfit
    have hdeg (h : List ℕ) (hf : Rounds.Fits logFinal (n - 1) h) :
        c * (Rounds.schedule 1 logFinal words fuel (n - 1) h).degree d = 2 ^ (n - 1) := by
      rw [Rounds.degree_schedule Nat.one_pos words d fuel _ h (by omega) (by omega) hf,
        mul_left_comm, hd, ← pow_add]
      congr 1
      omega
    -- one level: `M ≤ 2` words, and `M = 1` below `2 ^ t` points
    have hlevel (M : ℕ) (hM : M ≤ 2) (hMt : M = 1 ∨ t ≤ n - 1) (h : List ℕ)
        (hf : Rounds.Fits logFinal (n - 1) h) :
        lossyMcaError (univariatePowersGenerator 𝕂 M)
          (ReedSolomon.code ((ω.subdomain 1 : Domain.SmoothCosetFftDomain (n - 1) 𝕂) :
            Fin (2 ^ (n - 1)) ↪ 𝕂) ((Rounds.schedule 1 logFinal words fuel (n - 1) h).degree d))
          δ loss ≤ ENNReal.ofReal (max (2 * LossyMca.lossyBound 1 c δ δ_int loss) (2 ^ t) /
            Fintype.card 𝕂) := by
      refine (levelError_le (ω.subdomain 1) M c t _ hc (hdeg h hf) δ δ_int loss hδ h_pos h_lt
        h_loss).trans ?_
      split_ifs with hm
      · refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hK.le)
        refine le_trans ?_ (le_max_left _ _)
        have : (M : ℝ) ≤ 2 := by exact_mod_cast hM
        nlinarith
      · have hM1 : M = 1 := by omega
        subst hM1
        rw [one_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (Fintype.card 𝕂),
          ← ENNReal.ofReal_div_of_pos hK]
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hK.le)
        refine le_trans ?_ (le_max_right _ _)
        push_cast
        exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [Rounds.schedule, ite_eq_right hfin]
    match heights, hfit, ht, hla, j with
    | [], hfit, ht, hla, j =>
      cases j with
      | zero =>
        simp only [Rounds.foldErrorAt]
        rw [hla]
        exact hlevel _ (by norm_num) (Or.inl rfl) [] (Rounds.fits_nil _ _)
      | succ j =>
        simp only [Rounds.foldErrorAt]
        rw [hla]
        exact foldErrorAt_schedule_one_le c t hc d logFinal hd δ δ_int loss hδ h_pos h_lt h_loss
          words fuel (n - 1) _ [] j (by omega) (by omega) (Rounds.fits_nil _ _)
          fun _ h ↦ absurd h List.not_mem_nil
    | m :: rest, hfit, ht, hla, j =>
      by_cases hm : m = n - Rounds.logArity 1 logFinal n (m :: rest)
      · simp only [ite_eq_left hm]
        have hm' := hm
        rw [hla] at hm'
        have hfr := Rounds.fits_of_eq hfit hm'
        cases j with
        | zero =>
          simp only [Rounds.foldErrorAt]
          rw [hla]
          exact hlevel _ (by norm_num) (Or.inr (hm' ▸ ht m List.mem_cons_self)) rest hfr
        | succ j =>
          simp only [Rounds.foldErrorAt]
          rw [hla]
          exact foldErrorAt_schedule_one_le c t hc d logFinal hd δ δ_int loss hδ h_pos h_lt h_loss
            words fuel (n - 1) _ rest j (by omega) (by omega) hfr
            fun m' h ↦ ht m' (List.mem_cons_of_mem _ h)
      · simp only [ite_eq_right hm]
        have hm' := hm
        rw [hla] at hm'
        have h3 := Rounds.logArity_le_cons 1 logFinal n m rest
        have hfr := Rounds.fits_cons_of_ne hfit (by omega) hm'
        cases j with
        | zero =>
          simp only [Rounds.foldErrorAt]
          rw [hla]
          exact hlevel _ (by norm_num) (Or.inl rfl) _ hfr
        | succ j =>
          simp only [Rounds.foldErrorAt]
          rw [hla]
          exact foldErrorAt_schedule_one_le c t hc d logFinal hd δ δ_int loss hδ h_pos h_lt h_loss
            words fuel (n - 1) _ _ j (by omega) (by omega) hfr ht

namespace Batch
variable (S : Iop.Batch.Setup EF)

/-- The largest error of FRI's folds on the batch at arity `2`, at a proximity loss `loss > 0`
and a radius `δ ≤ (1 - rate) / 2 - 1 / 2 ^ t`, the shorter instances' domains of at least `2 ^ t`
points: `max(2 B, 2 ^ t) / |𝕂|`, `B = max(T₁, T₂, δ_int / loss)` for any `δ_int > δ`. -/
theorem friFoldErrorB_le (harity : S.params.maxLogArity = 1) (t : ℕ)
    (ht : ∀ m ∈ S.friHeights, t ≤ m) (δ δ_int loss : ℝ≥0)
    (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ) (h_lt : δ < δ_int)
    (h_loss : 0 < loss) :
    ⨆ j, Iop.Batch.friFoldError S δ loss j ≤
      ENNReal.ofReal (max (2 * LossyMca.lossyBound 1 (2 ^ S.params.logBlowup) δ δ_int loss)
        (2 ^ t)) / Fintype.card 𝕂 := by
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  rw [← ENNReal.ofReal_natCast (Fintype.card 𝕂), ← ENNReal.ofReal_div_of_pos hK]
  refine iSup_le fun j ↦ ?_
  have hf := S.folds S.top
  have hb := (S.valid S.top).blowup
  rw [Iop.Batch.friFoldError, Iop.Batch.Setup.friRounds, Iop.Setup.friRounds]
  change (Rounds.schedule S.params.maxLogArity _ _ _ _ _).foldErrorAt _ _ _ _ _ ≤ _
  rw [harity]
  refine foldErrorAt_schedule_one_le (2 ^ S.params.logBlowup) t (Nat.two_pow_pos _) _ _
    (by rw [← pow_add, add_comm]) δ δ_int loss ?_ h_pos h_lt h_loss _ _ _ _ _ j
    (by change S.params.logFinalPolyLen + S.params.logBlowup ≤ S.logN S.top + S.params.logBlowup
        omega) (Nat.sub_le _ _) (fits_friHeights S) ht
  push_cast
  exact hδ

/-- FRI's queries on the batch at arity `2`: `(1 - δ + #folds · loss + 1/p) ^ numQueries`, the
tallest instance's `logN - logFinalPolyLen` folds. -/
theorem friQueryErrorB_eq (harity : S.params.maxLogArity = 1) (δ loss : ℝ≥0) :
    Iop.Batch.friQueryError S δ loss =
      ENNReal.ofReal (1 - δ + (S.logN S.top - S.params.logFinalPolyLen : ℕ) * loss +
        1 / Nat.card F) ^ S.params.numQueries := by
  have hf := S.folds S.top
  rw [Iop.Batch.friQueryError, Iop.Batch.Setup.friRounds, Iop.Setup.friRounds]
  change ENNReal.ofReal (1 - δ + ((Rounds.schedule S.params.maxLogArity _ _ _ _ _).numFolds : ℕ) *
    loss + 1 / Nat.card F) ^ _ = _
  rw [harity, Rounds.numFolds_schedule_one _ _ _ _ (by
    change S.params.logFinalPolyLen + S.params.logBlowup ≤ S.logN S.top + S.params.logBlowup
    omega) (Nat.sub_le _ _) (fits_friHeights S)]
  have : S.logN S.top + S.params.logBlowup - (S.params.logFinalPolyLen + S.params.logBlowup) =
      S.logN S.top - S.params.logFinalPolyLen := by omega
  rw [this]

/-- The batch round errors at FRI arity `2`, FRI at `δ` and the extractor at `δ'` below the
unique-decoding radius, `δ < δ' - 2/N` on every domain, at one proximity loss `loss > 0` and a fold
threshold `2 ^ t` below the shorter domains: every instance's constraint-folding integer at most
`A₁` and out-of-domain integer at most `A₂`, the curve bound on batching every instance's domain
size at most `b`, FRI's folds (`friFoldErrorB_le`, `δ_int = δ + loss`) and queries
(`friQueryErrorB_eq`), all but the first credited with their grinding. -/
theorem batchRoundError_le (harity : S.params.maxLogArity = 1) (t : ℕ)
    (ht : ∀ m ∈ S.friHeights, t ≤ m) (δ δ' loss : ℝ≥0) (A₁ A₂ : ℕ) (b : ℝ)
    (hA₁ : ∀ i, (S.air i).constraints.length - 1 ≤ A₁)
    (hA₂ : ∀ i, (S.instanceSetup i).identityDegree + (S.instanceSetup i).n ≤ A₂)
    (hb : ∀ i, ((S.groupNumOpened (S.logN i + S.params.logBlowup) - 1 : ℕ) *
      max ((1 - S.rate - δ) / (δ * (1 - S.rate - 2 * δ)))
        ((δ' - 2 / (S.instanceSetup i).size) / (δ' - 2 / (S.instanceSetup i).size - δ))) ≤ b)
    (h_ud : ∀ i, (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / (S.instanceSetup i).size)
    (h_udt : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ)
    (h_lt : ∀ i, (δ : ℝ) < δ' - 2 / (S.instanceSetup i).size)
    (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) (h_loss : 0 < loss) :
    Iop.Batch.roundError S δ δ' ≤
      (max ((A₁ : ENNReal) / (Fintype.card 𝕂 : ENNReal)) <|
      max (powFraction F S.params.oodPowBits * ((A₂ : ENNReal) / (Fintype.card 𝕂 : ENNReal))) <|
      max (powFraction F S.params.batchPowBits * (ENNReal.ofReal b / Fintype.card 𝕂)) <|
      max (powFraction F S.params.commitPowBits * (ENNReal.ofReal
          (max (2 * LossyMca.lossyBound 1 (2 ^ S.params.logBlowup) δ (δ + loss) loss) (2 ^ t)) /
            Fintype.card 𝕂))
        (powFraction F S.params.queryPowBits *
          ENNReal.ofReal (1 - δ + (S.logN S.top - S.params.logFinalPolyLen : ℕ) * loss +
            1 / Nat.card F) ^ S.params.numQueries)) := by
  refine (iInf_le _ loss).trans ?_
  rw [← friQueryErrorB_eq S harity]
  have hrate (i : Fin S.k) : (S.instanceSetup i).rate = S.rate := rate_instanceSetup S i
  gcongr
  · refine iSup_le fun i ↦ (foldingError_le_of_le _ δ' (by rw [hrate]; exact hδ')).trans ?_
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (hA₁ i)) _
  · refine iSup_le fun i ↦ (outOfDomainError_le_of_le _ δ' (by rw [hrate]; exact hδ')).trans ?_
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (hA₂ i)) _
  · refine iSup_le fun i ↦ (batchingError_le_curve (S.instanceSetup i) _ δ _
      (by rw [hrate]; exact h_ud i) h_pos (h_lt i)).trans ?_
    refine ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal ?_) _
    rw [hrate]
    exact hb i
  · exact friFoldErrorB_le S harity t ht δ (δ + loss) loss h_udt h_pos
      (lt_add_of_pos_right _ h_loss) h_loss

end Batch

end CompStark.Sound
