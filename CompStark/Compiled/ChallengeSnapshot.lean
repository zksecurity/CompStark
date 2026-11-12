/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.MerkleTrace
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-! The oracle log before a first query is independent of that query's response. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Compiled.ChallengeSnapshot
open OracleComp OracleSpec
open Interaction.Oracle.Security

variable {D α : Type} {R : D → Type} [DecidableEq D]

/-- Retain precisely the chronological query prefix preceding the first selected query. -/
def before (program : OracleComp (ofFn R) α) (table : ∀ key, R key) (target : D) :
    QueryLog (ofFn R) :=
  (tableQueryLog program table).takeWhile fun entry => entry.1 != target

/-- Resampling the selected oracle cell cannot change the log preceding its first query. -/
theorem before_update (program : OracleComp (ofFn R) α) (table : ∀ key, R key)
    (target : D) (value : R target) :
    before program (Function.update table target value) target = before program table target := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind key next ih =>
      unfold before at *
      rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
      by_cases same : key = target
      · subst key
        simp only [bne_self_eq_false, List.takeWhile_cons_of_neg, Bool.false_eq_true, not_false_eq_true]
      · rw [Function.update_of_ne same]
        simp [same, ih]

/-- Process a chronological log into a newest-first log retaining each key's first answer. -/
def freshen (log : QueryLog (ofFn R)) (retained : QueryLog (ofFn R)) : QueryLog (ofFn R) :=
  match log with
  | [] => retained
  | entry :: rest => freshen rest
      (if (Bcs.cacheOf retained entry.1).isSome then retained else entry :: retained)
termination_by structural log

/-- The finite fresh snapshot just before a challenge is independent of its answer. -/
theorem freshen_before_update (program : OracleComp (ofFn R) α) (table : ∀ key, R key)
    (target : D) (value : R target) :
    freshen (before program (Function.update table target value) target) [] =
      freshen (before program table target) [] := by rw [before_update]

/-- Appending chronological traces resumes the same first-answer-only log construction. -/
theorem freshen_append (left right retained : QueryLog (ofFn R)) :
    freshen (left ++ right) retained = freshen right (freshen left retained) := by
  induction left generalizing retained with
  | nil => rfl
  | cons entry left ih => simp only [List.cons_append, freshen.eq_2, ih]

omit [DecidableEq D] in
/-- Every entry in a deterministic query log carries its table's answer. -/
theorem tableLog_agrees (program : OracleComp (ofFn R) α) (table : ∀ key, R key) :
    ∀ entry ∈ tableQueryLog program table, table entry.1 = entry.2 := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [tableQueryLog_pure, List.not_mem_nil, false_implies, implies_true]
  | query_bind key next ih =>
      intro entry member
      rw [tableQueryLog_query_bind] at member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact ih _ entry member

/-- Filtering repeated coordinates preserves coherence with a fixed answer table. -/
theorem freshen_agrees (table : ∀ key, R key) (log retained : QueryLog (ofFn R))
    (logged : ∀ entry ∈ log, table entry.1 = entry.2)
    (prior : ∀ entry ∈ retained, table entry.1 = entry.2) :
    ∀ entry ∈ freshen log retained, table entry.1 = entry.2 := by
  induction log generalizing retained with
  | nil => exact prior
  | cons entry rest ih =>
      rw [freshen.eq_2]
      apply ih _ (fun e member => logged e (List.mem_cons_of_mem _ member))
      split
      · exact prior
      · intro e member
        rcases List.mem_cons.mp member with rfl | member
        · exact logged _ List.mem_cons_self
        · exact prior e member

/-- Freshening only prepends new answers, leaving the earlier snapshot as a suffix. -/
theorem freshen_suffix (log retained : QueryLog (ofFn R)) :
    ∃ later, freshen log retained = later ++ retained := by
  induction log generalizing retained with
  | nil => exact ⟨[], rfl⟩
  | cons entry rest ih =>
      rw [freshen.eq_2]
      split
      · exact ih retained
      · obtain ⟨later, equal⟩ := ih (entry :: retained)
        exact ⟨later ++ [entry], by rw [equal, List.append_assoc]; rfl⟩

/-- A coherent finite cache answers each present key with its table's value. -/
theorem cache_agrees (table : ∀ key, R key) (log : QueryLog (ofFn R))
    (coherent : ∀ entry ∈ log, table entry.1 = entry.2)
    (key : D) (value : R key) (known : Bcs.cacheOf log key = some value) : table key = value := by
  induction log with
  | nil => cases known
  | cons entry log ih =>
      obtain ⟨other, answer⟩ := entry
      by_cases same : key = other
      · subst other
        have equal : answer = value := Option.some.inj (by
          simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self] using known)
        exact (coherent _ List.mem_cons_self).trans equal
      · apply ih (fun e member => coherent e (List.mem_cons_of_mem _ member))
        simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ same] using known

/-- Any answer retained before freshening remains cached afterwards. -/
theorem freshen_preserves_key (log retained : QueryLog (ofFn R)) (key : D)
    (known : Bcs.cacheOf retained key ≠ none) : Bcs.cacheOf (freshen log retained) key ≠ none := by
  induction log generalizing retained with
  | nil => exact known
  | cons entry rest ih =>
      rw [freshen.eq_2]
      apply ih
      split
      · exact known
      · intro absent
        exact known (Bcs.cacheOf_cons_eq_none.mp absent).2

/-- Every query in a chronological log is cached after removing repeated reads. -/
theorem freshen_records_key (log retained : QueryLog (ofFn R))
    (entry : (key : D) × R key) (member : entry ∈ log) :
    Bcs.cacheOf (freshen log retained) entry.1 ≠ none := by
  induction log generalizing retained with
  | nil => cases member
  | cons head rest ih =>
      rw [freshen.eq_2]
      rcases List.mem_cons.mp member with rfl | member
      · apply freshen_preserves_key
        split
        · exact Option.isSome_iff_ne_none.mp ‹_›
        · simp only [Bcs.cacheOf_cons, QueryCache.cacheQuery_self, ne_eq, reduceCtorEq, not_false_eq_true]
      · exact ih _ member

/-- Every actual query is available with its actual answer in the final fresh cache. -/
theorem freshen_tableLog_known (program : OracleComp (ofFn R) α) (table : ∀ key, R key)
    (entry : (key : D) × R key) (member : entry ∈ tableQueryLog program table) :
    Bcs.cacheOf (freshen (tableQueryLog program table) []) entry.1 = some entry.2 := by
  have coherent := freshen_agrees table (tableQueryLog program table) [] (tableLog_agrees program table)
    (fun _ h => nomatch h)
  have present := freshen_records_key (tableQueryLog program table) [] entry member
  cases known : Bcs.cacheOf (freshen (tableQueryLog program table) []) entry.1 with
  | none => exact (present known).elim
  | some value =>
      have equal := (cache_agrees table _ coherent _ value known).symm.trans (tableLog_agrees program table entry member)
      rw [equal]

end CompStark.Compiled.ChallengeSnapshot
