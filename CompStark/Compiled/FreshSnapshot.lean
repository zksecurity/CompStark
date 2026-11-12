/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.ChallengeSnapshot

/-! First-query snapshots are actual suffixes of the final fresh oracle trace. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Compiled.ChallengeSnapshot
open OracleComp OracleSpec Interaction.Oracle.Security

variable {D α : Type} {R : D → Type} [DecidableEq D]

/-- A coordinate absent from both input logs remains absent after freshening. -/
theorem freshen_absent (log retained : QueryLog (ofFn R)) (target : D)
    (absent : Bcs.cacheOf retained target = none)
    (unqueried : ∀ entry ∈ log, entry.1 ≠ target) :
    Bcs.cacheOf (freshen log retained) target = none := by
  induction log generalizing retained with
  | nil => exact absent
  | cons entry rest ih =>
      rw [freshen.eq_2]
      apply ih
      · split
        · exact absent
        · exact Bcs.cacheOf_cons_eq_none.mpr ⟨unqueried entry List.mem_cons_self, absent⟩
      · exact fun e member => unqueried e (List.mem_cons_of_mem _ member)

/-- The strict first-query snapshot contains no answer for its selected coordinate. -/
theorem before_absent (program : OracleComp (ofFn R) α) (table : ∀ key, R key) (target : D) :
    Bcs.cacheOf (freshen (before program table target) []) target = none := by
  apply freshen_absent _ _ _ rfl
  intro entry member
  have different : (entry.1 != target) = true := List.all_eq_true.mp List.all_takeWhile entry member
  simpa only [bne_iff_ne] using different

/-- A queried coordinate splits the chronological log immediately after its frozen prefix. -/
theorem tableLog_split (program : OracleComp (ofFn R) α) (table : ∀ key, R key) (target : D)
    (queried : ⟨target, table target⟩ ∈ tableQueryLog program table) :
    ∃ rest, tableQueryLog program table = before program table target ++ ⟨target, table target⟩ :: rest := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [tableQueryLog_pure, List.not_mem_nil] at queried
  | query_bind key next ih =>
      rw [tableQueryLog_query_bind] at queried ⊢
      by_cases same : key = target
      · subst key
        refine ⟨tableQueryLog (next (table target)) table, ?_⟩
        simp only [before, tableQueryLog_query_bind, bne_self_eq_false,
          List.takeWhile_cons_of_neg, Bool.false_eq_true, not_false_eq_true, List.nil_append]
      · have tail : ⟨target, table target⟩ ∈ tableQueryLog (next (table key)) table := by
          rcases List.mem_cons.mp queried with equal | member
          · exact (same (congrArg Sigma.fst equal).symm).elim
          · exact member
        obtain ⟨rest, split⟩ := ih _ tail
        refine ⟨rest, ?_⟩
        simpa [before, same] using congrArg (List.cons ⟨key, table key⟩) split

/-- A queried coordinate and its frozen prefix form a suffix of the final fresh log. -/
theorem freshen_tableLog_split (program : OracleComp (ofFn R) α) (table : ∀ key, R key) (target : D)
    (queried : ⟨target, table target⟩ ∈ tableQueryLog program table) :
    ∃ later, freshen (tableQueryLog program table) [] =
      later ++ (⟨target, table target⟩ :: freshen (before program table target) []) := by
  obtain ⟨rest, split⟩ := tableLog_split program table target queried
  rw [split, freshen_append, freshen.eq_2, before_absent]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact freshen_suffix rest _

end CompStark.Compiled.ChallengeSnapshot
