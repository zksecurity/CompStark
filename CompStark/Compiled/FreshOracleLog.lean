/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.FreshSnapshot

/-! The fresh chronological handler is the cached random oracle with its duplicate reads removed. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Compiled.ChallengeSnapshot
open OracleComp OracleSpec Interaction.Oracle.Security Keccak.Commit.RandomOracleTrace

variable {Input Key Digest α : Type} {Response : Key → Type}
    [DecidableEq Input] [DecidableEq Key] [SampleableType Digest] [∀ key, SampleableType (Response key)]

/-- Deterministic query logging returns exactly the evaluation and its chronological query trace. -/
theorem eval_withQueryLog {D : Type} {R : D → Type} (program : OracleComp (ofFn R) α)
    (table : ∀ key, R key) :
    evalWithAnswerFn (QueryImpl.ofFn table) program.withQueryLog =
      (evalWithAnswerFn (QueryImpl.ofFn table) program, tableQueryLog program table) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind key next ih =>
      simp only [withQueryLog_bind, withQueryLog_query, evalWithAnswerFn_bind,
        evalWithAnswerFn_map, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
        tableQueryLog_query_bind, evalWithAnswerFn_pure, ih, Prod.map_apply, id_eq, List.singleton_append]

/-- Logging does not change the actual queried coordinates of deterministic execution. -/
theorem tableLog_withQueryLog {D : Type} {R : D → Type} (program : OracleComp (ofFn R) α)
    (table : ∀ key, R key) : tableQueryLog program.withQueryLog table = tableQueryLog program table := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind key next ih =>
      simp only [withQueryLog_bind, withQueryLog_query, tableQueryLog_bind,
        evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      simp only [map_eq_bind_pure_comp, tableQueryLog_bind, tableQueryLog_pure,
        List.append_nil, tableQueryLog_query, ih, List.singleton_append, Function.comp_apply]

/-- Removing duplicate reads from the logged handler execution reconstructs its exact fresh state. -/
theorem handler_log (program : OracleComp (spec Input Digest Response) α)
    (retained : QueryLog (spec Input Digest Response)) :
    (fun result => (result.1.1, freshen result.1.2 retained)) <$>
      (simulateQ handler program.withQueryLog).run retained =
        (simulateQ handler program).run retained := by
  induction program using OracleComp.inductionOn generalizing retained with
  | pure result => simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure, map_pure, freshen.eq_1]
  | query_bind key next ih =>
      simp only [withQueryLog_bind, withQueryLog_query, simulateQ_bind, simulateQ_map,
        simulateQ_spec_query, simulateQ_pure, StateT.run_pure, StateT.run_bind, StateT.run_map, handler, StateT.run_mk]
      cases known : Bcs.cacheOf retained key with
      | some value =>
          simpa [simulateQ_pure, StateT.run_pure, Functor.map_map, freshen, known, Function.comp_def]
            using ih value retained
      | none =>
          simp only [bind_assoc, pure_bind, map_bind,
            Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq,
            List.singleton_append, freshen.eq_2, known, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          congr 1
          funext value
          exact ih value (⟨key, value⟩ :: retained)

/-- Forgetting the chronological handler state gives the same output distribution as the cached oracle. -/
theorem handler_output (program : OracleComp (spec Input Digest Response) α)
    (retained : QueryLog (spec Input Digest Response)) :
    Prod.fst <$> (simulateQ handler program).run retained =
      (simulateQ randomOracle program).run' (Bcs.cacheOf retained) := by
  have projected := congrArg (fun computation => Prod.fst <$> computation) (handler_projects program retained)
  simpa only [Functor.map_map, Function.comp_def, Prod.map_fst, id_eq, StateT.run', StateT.run] using projected

/-- The cached oracle's full log determines exactly the fresh state used by the hash-exception bound. -/
theorem randomOracle_fresh_log (program : OracleComp (spec Input Digest Response) α) :
    (fun result => (result.1, freshen result.2 [])) <$>
      (simulateQ randomOracle program.withQueryLog).run' ∅ =
        (simulateQ handler program).run [] := by
  rw [← Bcs.cacheOf_nil, ← handler_output]
  simpa only [Functor.map_map, Function.comp_def] using handler_log program []

/-- Pure output processing preserves every pathwise oracle-cost bound. -/
theorem costBound_map_iff {D β ω : Type} {R : D → Type} [AddCommMonoid ω] [Preorder ω]
    (program : OracleComp (ofFn R) α) (map : α → β) (cost : CostModel (ofFn R) ω) (bound : ω) :
    WorstCaseCostBound (map <$> program) cost bound ↔ WorstCaseCostBound program cost bound := by
  simp only [worstCaseCostBound_iff_support_bound, costDist, instrumentedRun, simulateQ_map,
    WriterT.run_map, support_map]
  aesop

/-- Query logging is transparent to key-dependent pathwise costs as well as total query counts. -/
theorem costBound_withQueryLog_iff {D ω : Type} {R : D → Type} [AddCommMonoid ω] [Preorder ω]
    (program : OracleComp (ofFn R) α) (cost : CostModel (ofFn R) ω) (bound : ω) :
    WorstCaseCostBound program.withQueryLog cost bound ↔ WorstCaseCostBound program cost bound := by
  have same := costBound_map_iff program.withQueryLog Prod.fst cost bound
  have projection : Prod.fst <$> program.withQueryLog = program :=
    loggingOracle.fst_map_run_simulateQ program
  rw [projection] at same
  exact same.symm

end CompStark.Compiled.ChallengeSnapshot
