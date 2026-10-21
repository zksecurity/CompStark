/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Answers
public import CompStark.Batch.Setup

/-! # The batch verifier and setup on fixed answers

As for the STARK (`Ni/Natural.lean`, `Ni/Answers.lean`), the batch verifier `verifyBatchWith` and
the batch setup `commonWith` are natural in their primitives (`verifyBatchWith_map`,
`commonWith_map`). So against an answer table they are the verifier and the setup on `idealOf`
(`evalWithAnswerFn_verifyBatchWith`, `evalWithAnswerFn_commonWith`), and their query logs are the
logs of their runs on `idealLogged` (`tableQueryLog_verifyBatchWith`).
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark

variable {F : Type} {m n : Type → Type} [Monad m] [Monad n] (φ : m →ᵐ n)

theorem injNodeWith_map [Zero F] (H : Primitives F m) (ms : List (Merkle.Matrix F)) (k : Nat) :
    ∀ l i, φ (injNodeWith H ms k l i) = injNodeWith (H.map φ) ms k l i
  | 0, _ => rfl
  | l + 1, i => by
    simp only [injNodeWith, MonadHom.mmap_bind, MonadHom.mmap_ite, MonadHom.mmap_pure,
      injNodeWith_map H ms k l]
    rfl

variable [BaseField F]

/-- **The batch setup is natural in its primitives.** -/
theorem commonWith_map (H : Primitives F m) (P : Params) (instances : List (Instance F)) :
    φ (commonWith H P instances) = commonWith (H.map φ) P instances := by
  unfold commonWith
  split
  · simp only [MonadHom.mmap_pure]
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, injNodeWith_map]

variable [LawfulMonad m] [LawfulMonad n] {EF : Type} [Challenge F EF]

/-- **The batch verifier is natural in its primitives.** -/
theorem verifyBatchWith_map (H : Primitives F m) (P : Params) (instances : List (Instance F))
    (common : Common F) (proof : BatchProof F EF) (pis : List (List F)) :
    φ (verifyBatchWith H P instances common proof pis) =
      verifyBatchWith (H.map φ) P instances common proof pis := by
  change (ExceptT.mapHom φ _).run = _
  simp only [verifyBatchWith, MonadHom.mmap_bind, MonadHom.mmap_pure, MonadHom.mmap_ite,
    exceptT_mapHom_throw, exceptT_mapHom_run, mapM_observeList, mapM_observeExts, mapM_sampleExt,
    mapM_ensure, mapM_checkWitness, mapM_verifyPcs, Primitives.map_init]
  rfl

end CompStark.Batch

namespace CompStark.RandomOracle
open CompStark.Stark CompStark.Batch OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}

/-- Simulating the oracles of the batch verifier by `impl` runs it on the answers of `impl`. -/
theorem simulateQ_verifyBatchWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec F K) n) (P : Fri.Params) (instances : List (Instance F))
    (common : Common F) (proof : BatchProof F EF) (pis : List (List F)) :
    simulateQ impl (verifyBatchWith (ideal F K) P instances common proof pis) =
      verifyBatchWith (withAnswers K impl) P instances common proof pis := by
  have h := verifyBatchWith_map (simulateQ' impl) (ideal F K) P instances common proof pis
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

/-- **The batch verifier against an answer table** is the batch verifier on `idealOf`. -/
theorem evalWithAnswerFn_verifyBatchWith (answer : (q : Query F) → Answer K q) (P : Fri.Params)
    (instances : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (pis : List (List F)) :
    evalWithAnswerFn (QueryImpl.ofFn answer)
        (verifyBatchWith (ideal F K) P instances common proof pis) =
      verifyBatchWith (idealOf answer) P instances common proof pis :=
  simulateQ_verifyBatchWith (QueryImpl.ofFn answer) P instances common proof pis

/-- **The batch verifier's queries against an answer table** are the log of the batch verifier on
`idealLogged`. -/
theorem tableQueryLog_verifyBatchWith (answer : (q : Query F) → Answer K q) (P : Fri.Params)
    (instances : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (pis : List (List F)) :
    tableQueryLog (verifyBatchWith (ideal F K) P instances common proof pis) answer =
      (verifyBatchWith (idealLogged answer) P instances common proof pis).run.2 := by
  rw [tableQueryLog, simulateQ_verifyBatchWith]

/-- Simulating the oracles of the batch setup by `impl` runs it on the answers of `impl`. -/
theorem simulateQ_commonWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec F K) n) (P : Fri.Params) (instances : List (Instance F)) :
    simulateQ impl (commonWith (ideal F K) P instances) =
      commonWith (withAnswers K impl) P instances := by
  have h := commonWith_map (simulateQ' impl) (ideal F K) P instances
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

/-- **The batch setup against an answer table** is the batch setup on `idealOf`. -/
theorem evalWithAnswerFn_commonWith (answer : (q : Query F) → Answer K q) (P : Fri.Params)
    (instances : List (Instance F)) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (commonWith (ideal F K) P instances) =
      commonWith (idealOf answer) P instances :=
  simulateQ_commonWith (QueryImpl.ofFn answer) P instances

end CompStark.RandomOracle
