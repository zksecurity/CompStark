/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Honest

/-! The fast verifier of the composed system: the outer endpoint parsed directly, the claim pool
with factored equality weights, and the PCS's word-level acceptance of the base-field oracle. It
decides the specification verifier (`verify_iff`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

variable (M)

/-- A column claim with a factored equality weight, if the column is stacked. -/
def columnClaimEvaluated (t : Fin S.tables.length) (c : ℕ) (z : List E) (value : E) :
    Option (Pcs.EvaluatedClaim M) :=
  ((S.stackColumns L).finIdxOf? (t, c)).map fun b ↦ ⟨.eq (S.liftPoint L M b z), value⟩

/-- The pool's claims with factored weights. -/
def poolEvaluated (o : TableSumcheck.Output S L k) : List (Pcs.EvaluatedClaim M) :=
  ((List.finRange (S.boundaryColumns L).length).filterMap fun j ↦
    columnClaimEvaluated (L := L) M (S.boundaryColumns L)[j].1 (S.boundaryColumns L)[j].2
      (o.bus.point.take (L.logHeight (S.boundaryColumns L)[j].1)) (o.bus.boundary j)) ++
  (List.finRange S.tables.length).flatMap fun t ↦
    if h : S.Direct L t = false then
      (List.finRange (TableSumcheck.transmitted S t).length).filterMap fun i ↦
        if TableSumcheck.virtualAt S t (TableSumcheck.transmitted S t)[i] then none
        else columnClaimEvaluated (L := L) M t (TableSumcheck.transmitted S t)[i]
          (o.point.take (L.logHeight t)) (o.values ⟨t, h⟩ i)
    else []

/-- Forgetting the evaluators of a factored column claim gives the column claim. -/
theorem columnClaimEvaluated_claim (t : Fin S.tables.length) (c : ℕ) (z : List E) (value : E) :
    (columnClaimEvaluated (S := S) (L := L) M t c z value).map Pcs.EvaluatedClaim.claim =
      columnClaim S L M t c z value := by
  unfold columnClaimEvaluated columnClaim
  cases (S.stackColumns L).finIdxOf? (t, c) <;> rfl

/-- Forgetting the evaluators of the factored pool gives the pool. -/
theorem poolEvaluated_claims (o : TableSumcheck.Output S L k) :
    (poolEvaluated M o).map Pcs.EvaluatedClaim.claim = pool S L k M o := by
  unfold poolEvaluated pool boundaryClaims valueClaims
  rw [List.map_append, List.map_filterMap, List.map_flatMap]
  congr 1
  · apply List.filterMap_congr
    intro j _
    exact columnClaimEvaluated_claim M _ _ _ _
  · apply List.flatMap_congr
    intro t _
    split
    · rw [List.map_filterMap]
      apply List.filterMap_congr
      intro i _
      split
      · rfl
      · exact columnClaimEvaluated_claim M _ _ _ _
    · rfl

/-- The opening's claims with factored weights. -/
def openingClaimsEvaluated (setup : Setup S L k M) :
    (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M →
      setup.external.protocol.tree.ExecutionPath → List (Pcs.EvaluatedClaim M)
  | ((_, none), _), _ => []
  | ((_, some o), _), path => poolEvaluated M o ++ setup.external.evaluated o path

/-- The outer public checks, decided. -/
def publicAcceptedB :
    (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M → Bool
  | ((_, none), _) => false
  | ((_, some o), out) => o.active && decide (o.bus.point.length = Bus.μ S L) && out.active

/-- The decided checks are the public checks. -/
theorem publicAcceptedB_iff
    (out : (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M) :
    publicAcceptedB M out = true ↔ publicAccepted out := by
  rcases out with ⟨⟨bus, table⟩, eo⟩
  cases table with
  | none => exact ⟨fun h ↦ absurd h Bool.false_ne_true, False.elim⟩
  | some o =>
    simp only [publicAcceptedB, publicAccepted, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

variable {M}

/-- The fast verifier of the composed system of a setup and an evaluated opening schedule. -/
def verifyWith (setup : Setup S L k M) (evaluated : Pcs.EvaluatedSchedule M)
    (path : (composedProtocol setup evaluated.schedule).tree.ExecutionPath) : Bool :=
  let parts := splitPath (outerProtocol setup) (Whir.opening E evaluated.schedule) path.2
  let out := outerOutput setup parts.1
  let externalPath := (splitPath (appendProtocol (Bus.protocol S L k) (TableSumcheck.protocol S L))
    setup.external.protocol parts.1).2
  publicAcceptedB M out &&
    Pcs.acceptsBaseEvaluated evaluated path.1 (openingClaimsEvaluated M setup out externalPath) parts.2

variable (params : Parameters S L k M)

/-- The fast verifier of the composed system. -/
abbrev verify (path : (protocol params).tree.ExecutionPath) : Bool :=
  verifyWith params.toSetup params.evaluated path

/-- Forgetting the evaluators of the opening's factored claims gives the opening's claims. -/
theorem openingClaimsEvaluated_map (setup : Setup S L k M) (bus : Option (Bus.Output S L k))
    (table : Option (TableSumcheck.Output S L k)) (path : setup.external.protocol.tree.ExecutionPath) :
    (openingClaimsEvaluated M setup ((bus, table), externalOutput setup table path) path).map
      Pcs.EvaluatedClaim.claim = openingClaims ((bus, table), externalOutput setup table path) := by
  cases table with
  | none => rfl
  | some o =>
    simp only [openingClaimsEvaluated, openingClaims, externalOutput, List.map_append,
      poolEvaluated_claims, setup.external.evaluated_claims]

/-- The fast verifier decides the specification verifier. -/
theorem verify_iff (path : (protocol params).tree.ExecutionPath) :
    verify params path = true ↔ Accepts params path := by
  unfold verify verifyWith Accepts executionParts
  dsimp only
  rw [← outerOutput_eq, Bool.and_eq_true, publicAcceptedB_iff, Pcs.acceptsBaseEvaluated_eq,
    Pcs.acceptsEvaluated_eq]
  unfold outerOutput
  dsimp only
  rw [openingClaimsEvaluated_map]

end CompStark.Tables.Composed
