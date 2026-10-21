/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.FriSchedule

/-! # FRI's rounds on fixed words, fold by fold

The random-oracle model reads FRI's committed words off the prover's hash queries, so they are
fixed before each folding challenge (`Rounds.run`): fold `j` folds word `words j`, read on its
domain, at `βs j`, injecting the rounds' input, and the final word is a polynomial on the final
domain. Each fold is one oracle answer, so its bad event is stated alone (`FoldFails`): the run is
lossily safe exactly when no fold fails (`safeLossy_run_iff`), fold `j`'s event reads only word
`j` (`foldFails_congr`), and over a uniform challenge it has probability at most fold `j`'s error
(`prob_foldFails_le`, `foldErrorAt`, the summand of `Rounds.foldError`).
-/

@[expose] public section

namespace CompStark.Sound.FriGame

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions Fri FriInject
open OracleComp
open scoped BigOperators ProbabilityTheory NNReal

variable {K : Type} [Field K]

namespace Rounds

/-- FRI's run on fixed words: fold `j` folds `words j`, read on its domain, at `βs j`, and the
final word is `fp` on the final domain. -/
def run (d : ℕ) (hd : 0 < d) : (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) → (fp : K[X]) →
    (βs : ℕ → K) → {n : ℕ} → (ω : SmoothCosetFftDomain n K) → (r : Rounds K n) →
      InjectTrace ω (r.degree d)
  | _, fp, _, _, ω, .final => .terminal fun x ↦ fp.eval (ω x)
  | words, fp, βs, n, ω, .fold k hk none rest =>
      .fold hk (degree_pos hd rest) (words 0 n) (βs 0)
        (run d hd (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest)
  | words, fp, βs, n, ω, .fold k hk (some g) rest =>
      .inject hk (degree_pos hd rest) (words 0 n) (βs 0) g
        (run d hd (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest)
termination_by structural _ _ _ _ _ r => r

variable [DecidableEq K]

/-- Fold `j` of the rounds fails on word `words j` at the challenge `β`: ArkLib's lossy folding
failure, or the injected fold's (`LossyInjectFailure`). -/
def FoldFails (d : ℕ) (θ loss : ℝ) (β : K) : (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) → ℕ →
    {n : ℕ} → SmoothCosetFftDomain n K → Rounds K n → Prop
  | _, _, _, _, .final => False
  | words, 0, n, ω, .fold k _ none rest =>
      LossyFoldingAgreementFailure ω (words 0 n) k (rest.degree d) θ loss β
  | words, 0, n, ω, .fold k _ (some g) rest =>
      LossyInjectFailure ω (words 0 n) k (rest.degree d) g θ loss β
  | words, j + 1, _, ω, .fold k _ _ rest =>
      FoldFails d θ loss β (fun i ↦ words (i + 1)) j (ω.subdomain k) rest
termination_by structural _ _ _ _ r => r

/-- The run is lossily safe exactly when no fold fails at its challenge. -/
theorem safeLossy_run_iff {d : ℕ} (hd : 0 < d) (θ loss : ℝ) (fp : K[X]) :
    ∀ (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (βs : ℕ → K) {n : ℕ}
      (ω : SmoothCosetFftDomain n K) (r : Rounds K n),
      (run d hd words fp βs ω r).SafeLossy θ loss ↔
        ∀ j, ¬ FoldFails d θ loss (βs j) words j ω r
  | _, _, _, _, .final => ⟨fun _ _ h ↦ h, fun _ ↦ trivial⟩
  | words, βs, _, ω, .fold k hk none rest => by
    simp only [run, InjectTrace.SafeLossy, safeLossy_run_iff hd θ loss fp _ _ _ rest]
    constructor
    · rintro ⟨h0, hrest⟩ (_ | j)
      · exact h0
      · exact hrest j
    · intro h
      exact ⟨h 0, fun j ↦ h (j + 1)⟩
  | words, βs, _, ω, .fold k hk (some g) rest => by
    simp only [run, InjectTrace.SafeLossy, safeLossy_run_iff hd θ loss fp _ _ _ rest]
    constructor
    · rintro ⟨h0, hrest⟩ (_ | j)
      · exact h0
      · exact hrest j
    · intro h
      exact ⟨h 0, fun j ↦ h (j + 1)⟩
termination_by structural _ _ _ _ r => r

/-- Fold `j`'s failure reads only word `j`. -/
theorem foldFails_congr (d : ℕ) (θ loss : ℝ) (β : K) :
    ∀ (words words' : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (j : ℕ), words j = words' j →
      ∀ {n : ℕ} (ω : SmoothCosetFftDomain n K) (r : Rounds K n),
        FoldFails d θ loss β words j ω r ↔ FoldFails d θ loss β words' j ω r
  | _, _, _, _, _, _, .final => Iff.rfl
  | _, _, 0, h, _, _, .fold _ _ none _ => by rw [FoldFails, FoldFails, h]
  | _, _, 0, h, _, _, .fold _ _ (some _) _ => by rw [FoldFails, FoldFails, h]
  | words, words', j + 1, h, _, ω, .fold k _ none rest =>
      foldFails_congr d θ loss β (fun i ↦ words (i + 1)) (fun i ↦ words' (i + 1)) j h
        (ω.subdomain k) rest
  | words, words', j + 1, h, _, ω, .fold k _ (some _) rest =>
      foldFails_congr d θ loss β (fun i ↦ words (i + 1)) (fun i ↦ words' (i + 1)) j h
        (ω.subdomain k) rest
termination_by structural _ _ _ _ _ _ r => r

/-- Fold `j`'s error: the lossy MCA error of the powers of the challenge over the fold's `2 ^ k`
coefficient words, and its injected input; `0` past the last fold. -/
noncomputable def foldErrorAt [Fintype K] [SampleableType K] (d : ℕ) (θ loss : ℝ) :
    ℕ → {n : ℕ} → SmoothCosetFftDomain n K → Rounds K n → ENNReal
  | _, _, _, .final => 0
  | 0, n, ω, .fold k _ none rest =>
      lossyMcaError (univariatePowersGenerator K (2 ^ k - 1))
        (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss
  | 0, n, ω, .fold k _ (some _) rest =>
      lossyMcaError (univariatePowersGenerator K (2 ^ k))
        (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss
  | j + 1, _, ω, .fold k _ _ rest => foldErrorAt d θ loss j (ω.subdomain k) rest
termination_by structural _ _ _ r => r

/-- **One fold.** Over a uniform challenge, fold `j` fails with probability at most its error,
whatever the words. -/
theorem prob_foldFails_le [Fintype K] [SampleableType K] {d : ℕ} (hd : 0 < d) (θ loss : ℝ) :
    ∀ (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (j : ℕ) {n : ℕ} (ω : SmoothCosetFftDomain n K)
      (r : Rounds K n),
      Pr{let β ←$ᵗ K}[FoldFails d θ loss β words j ω r] ≤ foldErrorAt d θ loss j ω r
  | _, _, _, _, .final => by
    simp only [FoldFails, prEvent_false, foldErrorAt, le_refl]
  | words, 0, n, ω, .fold k _ none rest =>
      lossyFoldingAgreementFailure_prob_le_powers ω (words 0 n) (degree_pos hd rest) θ loss
  | words, 0, n, ω, .fold k _ (some g) rest =>
      lossyInjectFailure_prob_le ω (words 0 n) g (degree_pos hd rest) θ loss
  | words, j + 1, _, ω, .fold k _ none rest =>
      prob_foldFails_le hd θ loss (fun i ↦ words (i + 1)) j (ω.subdomain k) rest
  | words, j + 1, _, ω, .fold k _ (some _) rest =>
      prob_foldFails_le hd θ loss (fun i ↦ words (i + 1)) j (ω.subdomain k) rest
termination_by structural _ _ _ _ r => r

/-- Each fold's error is a summand of the folds' errors. -/
theorem foldErrorAt_le_foldError [Fintype K] [SampleableType K] (d : ℕ) (θ loss : ℝ) :
    ∀ (j : ℕ) {n : ℕ} (ω : SmoothCosetFftDomain n K) (r : Rounds K n),
      foldErrorAt d θ loss j ω r ≤ r.foldError d θ loss ω
  | _, _, _, .final => le_rfl
  | 0, _, _, .fold _ _ none _ => le_self_add
  | 0, _, _, .fold _ _ (some _) _ => le_self_add
  | j + 1, _, ω, .fold k _ none rest =>
      (foldErrorAt_le_foldError d θ loss j (ω.subdomain k) rest).trans le_add_self
  | j + 1, _, ω, .fold k _ (some _) rest =>
      (foldErrorAt_le_foldError d θ loss j (ω.subdomain k) rest).trans le_add_self
termination_by structural _ _ _ r => r

/-- A fold's error depends on the heights only, not on the injected words. -/
theorem foldErrorAt_schedule_congr [Fintype K] [SampleableType K]
    (maxLogArity logFinal d : ℕ) (θ loss : ℝ) (words words' : (m : ℕ) → Fin (2 ^ m) → K) :
    ∀ (fuel n : ℕ) (ω : SmoothCosetFftDomain n K) (heights : List ℕ) (j : ℕ),
      (schedule maxLogArity logFinal words fuel n heights).foldErrorAt d θ loss j ω =
        (schedule maxLogArity logFinal words' fuel n heights).foldErrorAt d θ loss j ω
  | 0, _, _, _, _ => rfl
  | fuel + 1, n, ω, heights, j => by
    by_cases hfin : n ≤ logFinal
    · simp only [schedule, ite_eq_left hfin]
    simp only [schedule, ite_eq_right hfin]
    have ih := foldErrorAt_schedule_congr maxLogArity logFinal d θ loss words words' fuel
    have hdeg (l : List ℕ) :=
      (foldError_schedule_congr maxLogArity logFinal d θ loss words words' fuel
        (n - logArity maxLogArity logFinal n l)
        (ω.subdomain (logArity maxLogArity logFinal n l)) l).2.2
    match heights, j with
    | [], 0 => simp only [foldErrorAt, hdeg []]
    | [], j + 1 => simp only [foldErrorAt, ih]
    | m :: rest, 0 =>
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · have h := (foldError_schedule_congr maxLogArity logFinal d θ loss words words' fuel
          (n - logArity maxLogArity logFinal n (m :: rest))
          (ω.subdomain (logArity maxLogArity logFinal n (m :: rest))) rest).2.2
        simp only [ite_eq_left hm, foldErrorAt, h]
      · simp only [ite_eq_right hm, foldErrorAt, hdeg (m :: rest)]
    | m :: rest, j + 1 =>
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [ite_eq_left hm, foldErrorAt, ih]
      · simp only [ite_eq_right hm, foldErrorAt, ih]

end Rounds

namespace Rounds

variable (d : ℕ) (hd : 0 < d)

/-- The run has the rounds' number of folds. -/
theorem numFolds_run :
    ∀ (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (fp : K[X]) (βs : ℕ → K) {n : ℕ}
      (ω : SmoothCosetFftDomain n K) (r : Rounds K n),
      (run d hd words fp βs ω r).numFolds = r.numFolds
  | _, _, _, _, _, .final => rfl
  | words, fp, βs, _, ω, .fold k _ none rest => congrArg (· + 1)
      (numFolds_run (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest)
  | words, fp, βs, _, ω, .fold k _ (some _) rest => congrArg (· + 1)
      (numFolds_run (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest)
termination_by structural _ _ _ _ _ r => r

/-- The run's injected words are the rounds' inputs. -/
theorem inputsAgree_run (ρ : ℝ) :
    ∀ (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (fp : K[X]) (βs : ℕ → K) {n : ℕ}
      (ω : SmoothCosetFftDomain n K) (r : Rounds K n),
      (run d hd words fp βs ω r).InputsAgree ρ ↔ r.InputsAgree d ρ ω
  | _, _, _, _, _, .final => Iff.rfl
  | words, fp, βs, _, ω, .fold k _ none rest =>
      inputsAgree_run ρ (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest
  | words, fp, βs, _, ω, .fold k _ (some _) rest =>
      and_congr Iff.rfl
        (inputsAgree_run ρ (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest)
termination_by structural _ _ _ _ _ r => r

/-- The run's final word is a codeword when the final polynomial has degree below `d`. -/
theorem finalInCode_run (fp : K[X]) (hfinal : fp.natDegree < d) :
    ∀ (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (βs : ℕ → K) {n : ℕ}
      (ω : SmoothCosetFftDomain n K) (r : Rounds K n),
      (run d hd words fp βs ω r).FinalInCode
  | _, _, _, _, .final =>
      mem_code_of_polynomial_of_natDegree_lt_of_eval fp hfinal fun _ ↦ rfl
  | words, βs, _, ω, .fold k _ none rest =>
      finalInCode_run fp hfinal (fun j ↦ words (j + 1)) (fun j ↦ βs (j + 1)) (ω.subdomain k) rest
  | words, βs, _, ω, .fold k _ (some _) rest =>
      finalInCode_run fp hfinal (fun j ↦ words (j + 1)) (fun j ↦ βs (j + 1)) (ω.subdomain k) rest
termination_by structural _ _ _ _ r => r

/-- The run's first word is word `0` on the first domain, or the final word without folds. -/
theorem initial_run (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (fp : K[X]) (βs : ℕ → K)
    {n : ℕ} (ω : SmoothCosetFftDomain n K) (r : Rounds K n) (h : 0 < r.numFolds) :
    (run d hd words fp βs ω r).initial = words 0 n := by
  match r, h with
  | .fold _ _ none _, _ => rfl
  | .fold _ _ (some _) _, _ => rfl

end Rounds

end CompStark.Sound.FriGame
