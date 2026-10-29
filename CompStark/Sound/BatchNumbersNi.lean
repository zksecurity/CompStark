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

The terms of the batch `roundError` (`CompStark/BatchNonInteractiveError.lean`) at any FRI arity
and any radius, as for the STARK (`CompStark/Sound/NumbersNi.lean`):

* constraint folding, out of domain and batching at the worst instance, as for the batch
  knowledge error;
* each FRI fold, injecting the shorter instances' words: at most the largest of bounds on the folds
  of the batch's plan (`foldErrorAt_schedule_le`, `friFoldErrorB_le`);
* FRI's queries: `(1 - δ + #folds · loss + 1/p) ^ numQueries`, one fold per entry of the plan
  (`friQueryErrorB_eq`).

`CompStark/Sound/Calculator.lean` collects them at one proximity loss.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal FriGame ProximityGap CoreDefinitions Code

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Every fold's error of Plonky3's schedule at any arity and rate `1/c` (`c d = 2 ^ logFinal`): at
most the largest of bounds `g` on the folds of its plan, over `|𝕂|`. -/
theorem foldErrorAt_schedule_le (c : ℕ) (a : ℕ) (ha : 0 < a) (d logFinal : ℕ)
    (hd : c * d = 2 ^ logFinal) (δ loss : ℝ) (g : ℕ × ℕ × Bool → ℝ)
    (words : (m : ℕ) → Fin (2 ^ m) → 𝕂) :
    ∀ (fuel n : ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂) (heights : List ℕ) (j : ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Rounds.Fits logFinal n heights →
      FoldBounds 𝕂 c δ loss g (Rounds.plan a logFinal fuel n heights) →
      (Rounds.schedule a logFinal words fuel n heights).foldErrorAt d δ loss j ω ≤
        ENNReal.ofReal (planMax g (Rounds.plan a logFinal fuel n heights) / Fintype.card 𝕂)
  | 0, n, ω, heights, j, hn, hfuel, hfit, _ => by
    rw [Rounds.schedule, Rounds.foldErrorAt]
    exact bot_le
  | fuel + 1, n, ω, heights, j, hn, hfuel, hfit, hg => by
    by_cases hfin : n ≤ logFinal
    · rw [Rounds.schedule, ite_eq_left hfin, Rounds.foldErrorAt]
      exact bot_le
    have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
    have h1 := Rounds.one_le_logArity ha (by omega) hfit
    have h2 := Rounds.logArity_le a logFinal n heights
    -- fold `0` onto `2 ^ (n - la)` points, or a later one
    have hstep (la : ℕ) (hla1 : 1 ≤ la) (hla2 : la ≤ n - logFinal) (M : ℕ) (inj : Bool)
        (hM : M = Rounds.foldWords (la, n - la, inj)) (h : List ℕ)
        (hf : Rounds.Fits logFinal (n - la) h)
        (hg : FoldBounds 𝕂 c δ loss g
          ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h)) :
        lossyMcaError (univariatePowersGenerator 𝕂 M)
            (ReedSolomon.code ((ω.subdomain la : Domain.SmoothCosetFftDomain (n - la) 𝕂) :
              Fin (2 ^ (n - la)) ↪ 𝕂) ((Rounds.schedule a logFinal words fuel (n - la) h).degree d))
            δ loss ≤
          ENNReal.ofReal (planMax g
            ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h) / Fintype.card 𝕂) ∧
        ∀ j, (Rounds.schedule a logFinal words fuel (n - la) h).foldErrorAt d δ loss j
            (ω.subdomain la) ≤
          ENNReal.ofReal (planMax g
            ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h) / Fintype.card 𝕂) := by
      have hdeg : c * (Rounds.schedule a logFinal words fuel (n - la) h).degree d =
          2 ^ (n - la) := by
        rw [Rounds.degree_schedule ha words d fuel _ h (by omega) (by omega) hf, mul_left_comm,
          hd, ← pow_add]
        congr 1
        omega
      refine ⟨(hM ▸ (hg _ List.mem_cons_self).2 _ _ hdeg).trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (le_planMax g List.mem_cons_self) hK.le)),
        fun j ↦ (foldErrorAt_schedule_le c a ha d logFinal hd δ loss g words fuel (n - la)
          (ω.subdomain la) h j (by omega) (by omega) hf
          fun f hf ↦ hg f (List.mem_cons_of_mem _ hf)).trans
          (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_right _ _) hK.le))⟩
    rw [Rounds.schedule, ite_eq_right hfin]
    match heights, hfit, h1, h2, j, hg with
    | [], hfit, h1, h2, j, hg =>
      simp only [Rounds.plan, ite_eq_right hfin] at hg ⊢
      have h := hstep _ h1 h2 _ false (foldWords_false _ _).symm [] (Rounds.fits_nil _ _) hg
      cases j with
      | zero => exact h.1
      | succ j => exact h.2 j
    | m :: rest, hfit, h1, h2, j, hg =>
      have h3 := Rounds.logArity_le_cons a logFinal n m rest
      by_cases hm : m = n - Rounds.logArity a logFinal n (m :: rest)
      · simp only [ite_eq_left hm, Rounds.plan, ite_eq_right hfin] at hg ⊢
        have h := hstep _ h1 h2 _ true (foldWords_true _ _).symm rest
          (Rounds.fits_of_eq hfit hm) hg
        cases j with
        | zero => exact h.1
        | succ j => exact h.2 j
      · simp only [ite_eq_right hm, Rounds.plan, ite_eq_right hfin] at hg ⊢
        have h := hstep _ h1 h2 _ false (foldWords_false _ _).symm _
          (Rounds.fits_cons_of_ne hfit h3 hm) hg
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

/-- The largest error of FRI's folds on the batch at any arity and proximity loss: the largest of
bounds `g` on the folds of its plan, over `|𝕂|`. -/
theorem friFoldErrorB_le (δ loss : ℝ≥0) (g : ℕ × ℕ × Bool → ℝ)
    (hg : FoldBounds 𝕂 (2 ^ S.params.logBlowup) δ loss g (friPlan S)) :
    ⨆ j, Iop.Batch.friFoldError S δ loss j ≤
      ENNReal.ofReal (planMax g (friPlan S) / Fintype.card 𝕂) := by
  refine iSup_le fun j ↦ ?_
  have hf := (S.valid S.top).finalPolyFits
  have hn : S.params.logFinalPolyLen + S.params.logBlowup ≤ S.logTop := by
    change _ ≤ S.logN S.top + S.params.logBlowup
    omega
  rw [Iop.Batch.friFoldError, Iop.Batch.Setup.friRounds, Iop.Setup.friRounds]
  exact foldErrorAt_schedule_le (2 ^ S.params.logBlowup) _ (S.valid S.top).folds _ _
    (by rw [← pow_add, add_comm]) δ loss g _ _ _ _ _ j hn (Nat.sub_le _ _) (fits_friHeights S) hg

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
