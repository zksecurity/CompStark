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

The terms of the batch `roundError` (`CompStark/BatchNonInteractiveError.lean`) at any FRI arity,
with FRI's radius at most the unique-decoding radius, as for the STARK
(`CompStark/Sound/NumbersNi.lean`):

* constraint folding, out of domain and batching at the worst instance, as for the batch
  knowledge error;
* each FRI fold, injecting the shorter instances' words: at most the largest level bound of the
  plan of the batch's folds (`foldErrorAt_schedule_le`, `friFoldErrorB_le`);
* FRI's queries: `(1 - δ + #folds · loss + 1/p) ^ numQueries`, one fold per entry of the plan
  (`friQueryErrorB_eq`).

`CompStark/Sound/Calculator.lean` collects them at one proximity loss.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal FriGame ProximityGap CoreDefinitions Code

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Every fold's error of Plonky3's schedule at any arity and rate `1/c` (`c d = 2 ^ logFinal`), for
`δ ≤ (1 - 1/c) / 2`: at most the largest level bound of the plan over `|𝕂|`. -/
theorem foldErrorAt_schedule_le (c : ℕ) (hc : 0 < c) (a : ℕ) (ha : 0 < a) (d logFinal : ℕ)
    (hd : c * d = 2 ^ logFinal) (δ δ_int : ℝ≥0) (loss : ℝ) (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2)
    (h_pos : 0 < δ) (h_lt : δ < δ_int) (h_loss : 0 < loss) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂) :
    ∀ (fuel n : ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂) (heights : List ℕ) (j : ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Rounds.Fits logFinal n heights →
      (Rounds.schedule a logFinal words fuel n heights).foldErrorAt d δ loss j ω ≤
        ENNReal.ofReal (planMax c δ δ_int loss (Rounds.plan a logFinal fuel n heights) /
          Fintype.card 𝕂)
  | 0, n, ω, heights, j, hn, hfuel, hfit => by
    rw [Rounds.schedule, Rounds.foldErrorAt]
    exact bot_le
  | fuel + 1, n, ω, heights, j, hn, hfuel, hfit => by
    by_cases hfin : n ≤ logFinal
    · rw [Rounds.schedule, ite_eq_left hfin, Rounds.foldErrorAt]
      exact bot_le
    have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
    have h1 := Rounds.one_le_logArity ha (by omega) hfit
    have h2 := Rounds.logArity_le a logFinal n heights
    -- fold `0` onto `2 ^ (n - la)` points, or a later one
    have hstep (la : ℕ) (hla1 : 1 ≤ la) (hla2 : la ≤ n - logFinal) (M : ℕ) (inj : Bool)
        (hM : M = Rounds.foldWords (la, n - la, inj)) (h : List ℕ)
        (hf : Rounds.Fits logFinal (n - la) h) :
        lossyMcaError (univariatePowersGenerator 𝕂 M)
            (ReedSolomon.code ((ω.subdomain la : Domain.SmoothCosetFftDomain (n - la) 𝕂) :
              Fin (2 ^ (n - la)) ↪ 𝕂) ((Rounds.schedule a logFinal words fuel (n - la) h).degree d))
            δ loss ≤
          ENNReal.ofReal (planMax c δ δ_int loss
            ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h) / Fintype.card 𝕂) ∧
        ∀ j, (Rounds.schedule a logFinal words fuel (n - la) h).foldErrorAt d δ loss j
            (ω.subdomain la) ≤
          ENNReal.ofReal (planMax c δ δ_int loss
            ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h) / Fintype.card 𝕂) := by
      have hdeg : c * (Rounds.schedule a logFinal words fuel (n - la) h).degree d =
          2 ^ (n - la) := by
        rw [Rounds.degree_schedule ha words d fuel _ h (by omega) (by omega) hf, mul_left_comm,
          hd, ← pow_add]
        congr 1
        omega
      refine ⟨(levelError_le (ω.subdomain la) M c _ hc hdeg δ δ_int loss hδ h_pos h_lt
        h_loss).trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hK.le)),
        fun j ↦ (foldErrorAt_schedule_le c hc a ha d logFinal hd δ δ_int loss hδ h_pos h_lt
          h_loss words fuel (n - la) (ω.subdomain la) h j (by omega) (by omega) hf).trans
          (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_right _ _) hK.le))⟩
      rw [hM]
      exact le_planMax c δ δ_int loss List.mem_cons_self
    rw [Rounds.schedule, ite_eq_right hfin]
    match heights, hfit, h1, h2, j with
    | [], hfit, h1, h2, j =>
      have h := hstep _ h1 h2 _ false (foldWords_false _ _).symm [] (Rounds.fits_nil _ _)
      simp only [Rounds.plan, ite_eq_right hfin]
      cases j with
      | zero => exact h.1
      | succ j => exact h.2 j
    | m :: rest, hfit, h1, h2, j =>
      have h3 := Rounds.logArity_le_cons a logFinal n m rest
      by_cases hm : m = n - Rounds.logArity a logFinal n (m :: rest)
      · have h := hstep _ h1 h2 _ true (foldWords_true _ _).symm rest (Rounds.fits_of_eq hfit hm)
        simp only [ite_eq_left hm, Rounds.plan, ite_eq_right hfin]
        cases j with
        | zero => exact h.1
        | succ j => exact h.2 j
      · have h := hstep _ h1 h2 _ false (foldWords_false _ _).symm _
          (Rounds.fits_cons_of_ne hfit h3 hm)
        simp only [ite_eq_right hm, Rounds.plan, ite_eq_right hfin]
        cases j with
        | zero => exact h.1
        | succ j => exact h.2 j

namespace Batch
variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)

/-- The plan of the batch's FRI: Plonky3's schedule from the tallest domain, injecting at the
shorter instances' domain sizes. -/
abbrev friPlan : List (ℕ × ℕ × Bool) :=
  Rounds.plan S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup) S.logTop
    S.logTop S.friHeights

/-- The largest error of FRI's folds on the batch at any arity, for `δ ≤ (1 - rate) / 2` and a
proximity loss `loss > 0`: the largest level bound of its plan over `|𝕂|`, for any `δ_int > δ`. -/
theorem friFoldErrorB_le (δ δ_int loss : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) (h_pos : 0 < δ)
    (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    ⨆ j, Iop.Batch.friFoldError S δ loss j ≤
      ENNReal.ofReal (planMax (2 ^ S.params.logBlowup) δ δ_int loss (friPlan S) /
        Fintype.card 𝕂) := by
  refine iSup_le fun j ↦ ?_
  have hf := S.folds S.top
  have hn : S.params.logFinalPolyLen + S.params.logBlowup ≤ S.logTop := by
    change _ ≤ S.logN S.top + S.params.logBlowup
    omega
  rw [Iop.Batch.friFoldError, Iop.Batch.Setup.friRounds, Iop.Setup.friRounds]
  refine foldErrorAt_schedule_le (2 ^ S.params.logBlowup) (Nat.two_pow_pos _) _
    (S.valid S.top).folds _ _ (by rw [← pow_add, add_comm]) δ δ_int loss ?_ h_pos h_lt h_loss _ _
    _ _ _ j hn (Nat.sub_le _ _) (fits_friHeights S)
  rw [Iop.Batch.Setup.rate] at hδ
  push_cast
  exact hδ

/-- FRI's queries on the batch at any arity: `(1 - δ + #folds · loss + 1/p) ^ numQueries`, one
fold per entry of the plan. -/
theorem friQueryErrorB_eq (δ loss : ℝ≥0) :
    Iop.Batch.friQueryError S δ loss =
      ENNReal.ofReal (1 - δ + (friPlan S).length * loss + 1 / Nat.card F) ^
        S.params.numQueries := by
  rw [Iop.Batch.friQueryError, Iop.Batch.Setup.friRounds, Iop.Setup.friRounds,
    FriGame.Rounds.numFolds_schedule]

end Batch

end CompStark.Sound
