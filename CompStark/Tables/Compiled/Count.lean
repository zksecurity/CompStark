/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Transcript

/-! The compiled composed system's number of draws: the bus's fingerprint and descent, the table
sumcheck's batching and rounds, the external argument's draws and WHIR's. Every compiled path has
at most that many challenge moves (`challenge_bound`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- The number of draws of the compiled composed system. -/
def count (params : Parameters S L k M) : ℕ :=
  1 + busRankCount (GrandProduct.layers (Bus.μ S L)) 0 + (TableSumcheck.maxHeight S L + 1) +
    params.externalCount + whirRankCount params.schedule

variable (S L k) in
/-- The bus has one rank per fingerprint draw and per descent draw. -/
theorem busPresentation_counted :
    (busPresentation S L k).Counted (1 + busRankCount (GrandProduct.layers (Bus.μ S L)) 0) := by
  refine ⟨busRankCount (GrandProduct.layers (Bus.μ S L)) 0, by omega, fun _ => ?_⟩
  have h := grandProduct_counted (count := 0)
    (.sender (rest := fun _ : S.BoundaryValues L => Protocol.done) (fun values => fieldEvents values)
      (fun _ => .done)) (fun _ => rfl) (GrandProduct.layers (Bus.μ S L)) 0
  rw [Nat.zero_add] at h
  exact h

variable (S L) in
/-- The table sumcheck has its batching draw and one draw per round. -/
theorem tablePresentation_counted :
    (tablePresentation S L).Counted (TableSumcheck.maxHeight S L + 1) := by
  have table (rounds : ℕ) : (tableRounds S L rounds).Counted rounds := by
    induction rounds with
    | zero => exact fun _ => rfl
    | succ rounds ih => exact ⟨_, rfl, ih⟩
  exact ⟨_, rfl, table _⟩

/-- The compiled presentation has `count` ranks. -/
theorem presentation_counted (params : Parameters S L k M) :
    (presentation params).Counted (count params) := by
  change ((outerPresentation params).append (whirPresentation params.schedule)).Counted _
  exact Presentation.Counted.append _ _
    (Presentation.Counted.append _ _ (Presentation.Counted.append _ _
      (busPresentation_counted S L k) (tablePresentation_counted S L)) params.externalCounted)
    (whirPresentation_counted params.schedule)

/-- Every compiled path has at most `count` challenge moves. -/
theorem challenge_bound (params : Parameters S L k M) :
    StandardBcs.ChallengeBound (Com := Commit.Digest) (fun _ : PUnit => coin params) (count params) := by
  intro statement path
  exact (Presentation.Counted.keys (presentation params) (presentation_counted params) path).le

end CompStark.Tables.Compiled
