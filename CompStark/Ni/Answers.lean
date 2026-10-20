/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.RandomOracle
public import CompStark.Ni.Natural
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-! # The verifier on fixed answers

Against an answer table `answer`, the verifier's oracle computation `verifyWith (ideal K)` is the
verifier on the pure primitives `idealOf answer` (`evalWithAnswerFn_verifyWith`), and its query
log is the log of the verifier on `idealLogged answer`, the same primitives that also log every
query (`tableQueryLog_verifyWith`). Both follow from the naturality of the verifier
(`Stark.verifyWith_map`) for the simulation of the oracles, `simulateQ_verifyWith`.
-/

@[expose] public section
namespace CompStark.RandomOracle
open CompStark.Stark OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

variable {K : Nat}

/-- The primitives on answers `ask`, mapped by a monad morphism, are those on the mapped
answers. -/
theorem withAnswers_map {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m]
    [LawfulMonad n] (φ : m →ᵐ n) (ask : (q : Query) → m (Answer K q)) :
    (withAnswers K ask).map φ = withAnswers K fun q ↦ φ (ask q) := by
  simp only [Primitives.map, withAnswers, Primitives.mk.injEq, heq_eq_eq, true_and, and_true]
  funext s
  rcases s with ⟨cap, input, _ | ⟨x, rest⟩⟩
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure]
  · simp only [MonadHom.mmap_pure]

/-- Simulating the oracles of the verifier by `impl` runs the verifier on the answers of
`impl`. -/
theorem simulateQ_verifyWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec K) n) (P : Fri.Params) (A : Air) (proof : Proof EF) (pis : List F) :
    simulateQ impl (verifyWith (ideal K) P A proof pis) =
      verifyWith (withAnswers K impl) P A proof pis := by
  have h := verifyWith_map (simulateQ' impl) (ideal K) P A proof pis
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

/-- The verifier's primitives on fixed answers, logging every query. -/
abbrev idealLogged (answer : (q : Query) → Answer K q) :
    Primitives (WriterT (QueryLog (spec K)) Id) :=
  withAnswers K (QueryImpl.ofFn answer).withLogging

/-- **The verifier against an answer table** is the verifier on `idealOf`. -/
theorem evalWithAnswerFn_verifyWith (answer : (q : Query) → Answer K q) (P : Fri.Params)
    (A : Air) (proof : Proof EF) (pis : List F) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (verifyWith (ideal K) P A proof pis) =
      verifyWith (idealOf answer) P A proof pis :=
  simulateQ_verifyWith (QueryImpl.ofFn answer) P A proof pis

/-- **The verifier's queries against an answer table** are the log of the verifier on
`idealLogged`. -/
theorem tableQueryLog_verifyWith (answer : (q : Query) → Answer K q) (P : Fri.Params)
    (A : Air) (proof : Proof EF) (pis : List F) :
    tableQueryLog (verifyWith (ideal K) P A proof pis) answer =
      (verifyWith (idealLogged answer) P A proof pis).run.2 := by
  rw [tableQueryLog, simulateQ_verifyWith]

end CompStark.RandomOracle

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

variable (S : Setup KoalaBear.Fast.Ext4)

theorem evalWithAnswerFn_verifyRo (answer : (q : Query) → Answer S.streamLen q) (proof : Proof EF)
    (pis : List F) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (S.verifyRo proof pis) =
      if proof.degreeBits = S.logN then verifyWith (idealOf answer) S.params S.air proof pis
      else .error "degree bits" := by
  unfold verifyRo
  split
  · exact evalWithAnswerFn_verifyWith answer _ _ proof pis
  · rfl

theorem tableQueryLog_verifyRo (answer : (q : Query) → Answer S.streamLen q) (proof : Proof EF)
    (pis : List F) :
    tableQueryLog (S.verifyRo proof pis) answer =
      if proof.degreeBits = S.logN then
        (verifyWith (idealLogged answer) S.params S.air proof pis).run.2
      else [] := by
  unfold verifyRo
  split
  · exact tableQueryLog_verifyWith answer _ _ proof pis
  · exact tableQueryLog_pure _ _

end CompStark.Iop.Setup
