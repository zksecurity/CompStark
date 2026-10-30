/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.FriInject

/-! # FRI's rounds with injected inputs

Plonky3's FRI over inputs of several heights, on a domain `ω` of `2 ^ n` points: each round folds
by `2 ^ k` and may inject an input word of the folded domain's size (`Rounds`). The rounds fix the
degree bound of each layer (`Rounds.degree`), which inputs agree with their codes
(`Rounds.InputsAgree`), and the soundness error at proximity `δ` (`error`): each fold's lossy MCA
error (`foldError`; the powers of `β` over `2 ^ k` coefficient words, and the injected input with
them) and `(1 - δ + m · loss) ^ t` for the queries, `m` folds, at the best proximity loss. It is
the error of ArkLib's FRI on the interaction layer along the same schedule
(`CompStark/Interaction/Fri.lean`), and the non-interactive proof runs its folds
(`Sound/FriRun.lean`).
-/

@[expose] public section

namespace CompStark.Sound.FriGame

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions Fri FriInject
open OracleComp
open scoped BigOperators ProbabilityTheory NNReal

variable {K : Type}

/-- FRI's rounds from a domain of `2 ^ n` points: each folds by `2 ^ k` and may inject an input
word of the folded domain's size. -/
inductive Rounds (K : Type) : ℕ → Type
  | final {n : ℕ} : Rounds K n
  | fold {n : ℕ} (k : ℕ) (hk : k ≤ n) (input : Option (Fin (2 ^ (n - k)) → K))
      (rest : Rounds K (n - k)) : Rounds K n

namespace Rounds

/-- The number of folds. -/
def numFolds : {n : ℕ} → Rounds K n → ℕ
  | _, .final => 0
  | _, .fold _ _ _ rest => rest.numFolds + 1

/-- The degree bound of the code before the rounds, for a final degree bound `d`. -/
def degree (d : ℕ) : {n : ℕ} → Rounds K n → ℕ
  | _, .final => d
  | _, .fold k _ _ rest => 2 ^ k * rest.degree d

theorem degree_pos {d : ℕ} (hd : 0 < d) : ∀ {n : ℕ} (r : Rounds K n), 0 < r.degree d
  | _, .final => hd
  | _, .fold _ _ _ rest => Nat.mul_pos (Nat.two_pow_pos _) (degree_pos hd rest)

variable [Field K]

/-- Every injected input agrees with a codeword of its code on a set of at least `ρ` of its
domain. -/
def InputsAgree (d : ℕ) (ρ : ℝ) : {n : ℕ} → SmoothCosetFftDomain n K → Rounds K n → Prop
  | _, _, .final => True
  | _, ω, .fold k _ none rest => rest.InputsAgree d ρ (ω.subdomain k)
  | _, ω, .fold k _ (some g) rest =>
      Agrees (ω.subdomain k) (rest.degree d) ρ g ∧ rest.InputsAgree d ρ (ω.subdomain k)

/-- The folds' errors at proximity `θ` and loss `loss`: the lossy MCA error of the powers of `β`
over the fold's `2 ^ k` coefficient words, and its injected input. -/
noncomputable def foldError [Fintype K] [DecidableEq K] [SampleableType K] (d : ℕ) (θ loss : ℝ) :
    {n : ℕ} → SmoothCosetFftDomain n K → Rounds K n → ENNReal
  | _, _, .final => 0
  | n, ω, .fold k _ none rest =>
      lossyMcaError (univariatePowersGenerator K (2 ^ k - 1))
        (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss +
      rest.foldError d θ loss (ω.subdomain k)
  | n, ω, .fold k _ (some _) rest =>
      lossyMcaError (univariatePowersGenerator K (2 ^ k))
        (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss +
      rest.foldError d θ loss (ω.subdomain k)

end Rounds

open Rounds

variable [Field K] [Fintype K] [DecidableEq K]

/-- FRI's soundness error at proximity `δ`, at the best proximity loss: the folds' errors and
`(1 - δ + m · loss) ^ t` for the queries. -/
noncomputable def error [SampleableType K] {n : ℕ} (ω : SmoothCosetFftDomain n K)
    (r : Rounds K n) (d t : ℕ)
    (δ : ℝ) : ENNReal :=
  ⨅ loss : ℝ≥0, r.foldError d δ loss ω + ENNReal.ofReal (1 - δ + r.numFolds * loss) ^ t

end CompStark.Sound.FriGame
