/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoichi Hirai, Pietro Monticone, Aristotle (Harmonic), Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.QuerySoundness

/-! # FRI's query traces with words injected mid-folding

ArkLib's FRI query traces (`Fri.FoldTrace`, `ArkLib/ProofSystem/Fri/QuerySoundness.lean`), with
the folding of Plonky3's FRI over inputs of several heights: a fold may add a word `g` of the
folded domain's size, scaled by `α ^ 2 ^ k`, to the folded word (`InjectTrace.inject`; Plonky3
rolls the reduced opening of the next height in with `β ^ arity`). `InjectTrace.accepting`: the
initial positions at which every local folding check accepts. `Agrees`: a word agrees with a
codeword on a set of at least a given fraction of the domain.
-/

@[expose] public section

namespace CompStark.Sound.FriInject

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions Fri
open CosetFftDomainClass (sqFoldMapGen)
open OracleComp
open scoped BigOperators ProbabilityTheory

variable {F : Type} [Field F]

/-- A word agrees with a codeword of `code domain d` on a set of at least `ρ` of the domain. -/
def Agrees {m : ℕ} (domain : Fin (2 ^ m) ↪ F) (d : ℕ) (ρ : ℝ) (w : Fin (2 ^ m) → F) : Prop :=
  ∃ T : Finset (Fin (2 ^ m)), ρ * 2 ^ m ≤ T.card ∧ ∃ v ∈ code domain d, ∀ x ∈ T, v x = w x

/-! ### Traces with injected words -/

/-- The algebraic data read by FRI's query phase (ArkLib's `FoldTrace`), with folds that may add
an injected word: at each step the degree bound and domain shrink by the folding factor; the last
word is checked for membership in its RS code. -/
inductive InjectTrace : {n : ℕ} → SmoothCosetFftDomain n F → ℕ → Type
  | terminal {n : ℕ} {domain : SmoothCosetFftDomain n F} {d : ℕ}
      (f : Fin (2 ^ n) → F) : InjectTrace domain d
  | fold {n k d : ℕ} {domain : SmoothCosetFftDomain n F}
      (hk : k ≤ n) (hd : 0 < d) (f : Fin (2 ^ n) → F) (α : F)
      (tail : InjectTrace (domain.subdomain k) d) : InjectTrace domain (2 ^ k * d)
  | inject {n k d : ℕ} {domain : SmoothCosetFftDomain n F}
      (hk : k ≤ n) (hd : 0 < d) (f : Fin (2 ^ n) → F) (α : F) (g : Fin (2 ^ (n - k)) → F)
      (tail : InjectTrace (domain.subdomain k) d) : InjectTrace domain (2 ^ k * d)

namespace InjectTrace

variable {n d : ℕ} {domain : SmoothCosetFftDomain n F}

/-- The word at the beginning of a trace. -/
def initial : InjectTrace domain d → (Fin (2 ^ n) → F)
  | .terminal f => f
  | .fold _ _ f _ _ => f
  | .inject _ _ f _ _ _ => f

/-- The final code-membership check. -/
def FinalInCode : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    InjectTrace domain d → Prop
  | _, d, domain, .terminal f => f ∈ code domain d
  | _, _, _, .fold _ _ _ _ tail => tail.FinalInCode
  | _, _, _, .inject _ _ _ _ _ tail => tail.FinalInCode

end InjectTrace

variable [DecidableEq F]

/-! ### Accepting positions -/

namespace InjectTrace

variable {n d : ℕ} {domain : SmoothCosetFftDomain n F}

/-- Initial positions at which every local folding check accepts. -/
noncomputable def accepting : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    InjectTrace domain d → Finset (Fin (2 ^ n))
  | _, _, _, .terminal _ => Finset.univ
  | _, _, domain, .fold (k := k) _ _ f α tail => by
      classical
      exact Finset.univ.filter fun i ↦
        let x := sqFoldMapGen (i := k) i
        foldWord domain f k α x = tail.initial x ∧ x ∈ tail.accepting
  | _, _, domain, .inject (k := k) _ _ f α g tail => by
      classical
      exact Finset.univ.filter fun i ↦
        let x := sqFoldMapGen (i := k) i
        foldWord domain f k α x + α ^ 2 ^ k * g x = tail.initial x ∧ x ∈ tail.accepting

end InjectTrace

end CompStark.Sound.FriInject
