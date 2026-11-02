/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.RandomOracle
public import CompStark.Ni.Natural

/-! # The verifier's primitives on answers

The primitives on oracle answers are natural in the monad the answers come from
(`withAnswers_map`), so simulating the verifier's oracles by `impl` runs the verifier on the
answers of `impl` (`simulateQ_verifyWith`, from `Stark.verifyWith_map`).
-/

@[expose] public section
namespace CompStark.RandomOracle
open CompStark.Stark OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}

/-- The primitives on answers `ask`, mapped by a monad morphism, are those on the mapped
answers. -/
theorem withAnswers_map {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m]
    [LawfulMonad n] (φ : m →ᵐ n) (ask : (q : Query F) → m (Answer K q)) :
    (withAnswers K ask).map φ = withAnswers K fun q ↦ φ (ask q) := by
  simp only [Primitives.map, withAnswers, Primitives.mk.injEq, heq_eq_eq, true_and, and_true]
  funext s
  rcases s with ⟨cap, input, _ | ⟨x, rest⟩⟩
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure]
  · simp only [MonadHom.mmap_pure]

/-- Simulating the oracles of the verifier by `impl` runs the verifier on the answers of
`impl`. -/
theorem simulateQ_verifyWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec F K) n) (P : Fri.Params) (A : Air F)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F) :
    simulateQ impl (verifyWith (ideal F K) P A vk proof pis) =
      verifyWith (withAnswers K impl) P A vk proof pis := by
  have h := verifyWith_map (simulateQ' impl) (ideal F K) P A vk proof pis
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

end CompStark.RandomOracle
