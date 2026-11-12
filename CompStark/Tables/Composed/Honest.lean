/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.HonestTable
public import CompStark.Pcs.Honest

/-! The honest prover of the composed system and its completeness: it commits the witness's stack,
runs the honest bus, table sumcheck and external argument, and opens the claim pool with the
honest PCS. For every satisfying witness whose padding rows are the padding row, against every coin
sequence, the specification verifier accepts (`completeness`). -/

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

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (params : Parameters S L k M)

/-- The verifier's coins of the composed system. -/
structure Coins where
  /-- The bus's coins. -/
  bus : BusCoins S L k
  /-- The table sumcheck's coins. -/
  table : TableCoins S L
  /-- The external argument's coins. -/
  external : params.external.Coins
  /-- The opening's coins. -/
  opening : Pcs.WhirCoins K E params.schedule

/-- A bus output for a rejected bus, which an honest prover never meets. -/
def rejectedBus : Bus.Output S L k := ⟨0, 0, [], 0, 0, false⟩

/-- The honest outer transcript. -/
noncomputable def honestOuterPath (w : Witness K S.tables.length) (coins : Coins params) :
    (outerProtocol params.toSetup).tree.ExecutionPath :=
  let busPath := honestBusPath S L k w coins.bus
  let bus := (Bus.outputClaim S L k busPath).getD rejectedBus
  let tablePath := honestTablePath S L k bus w coins.table
  let table := (TableSumcheck.outputClaim S L k bus tablePath).getD rejectedOutput
  joinPath _ _ (joinPath _ _ busPath tablePath)
    (params.external.honest table (S.stack L M w) coins.external)

/-- The honest transcript of the composed system. -/
noncomputable def honestPath (w : Witness K S.tables.length) (coins : Coins params) :
    (protocol params).tree.ExecutionPath :=
  let outer := honestOuterPath params w coins
  let opening := Pcs.Honest.prove params.schedule (S.stack L M w)
    (openingClaims ((outerReduction params.toSetup).output outer)) coins.opening
  ⟨opening.initial, joinPath _ _ outer opening.transcript⟩

/-- Completeness: for every satisfying witness whose padding rows are the padding row, the
specification verifier accepts the honest transcript against every coin sequence. -/
theorem completeness (w : Witness K S.tables.length) (hsat : S.Satisfied L w) (padded : S.Padded L w)
    (coins : Coins params) : Accepts params (honestPath params w coins) := by
  have shaped := hsat.1
  have hext := hsat.2.2.2.2
  have hinterp := params.external.interpret_stack w shaped hext
  obtain ⟨o, hbus, hterm⟩ := honestBus_terminal params.wellFormed params.busShape w hsat padded coins.bus
  obtain ⟨o', htable, hterm'⟩ := honestTable_terminal params.wellFormed o w hsat hterm coins.table
  set q := S.stack L M w
  set busPath := honestBusPath S L k w coins.bus
  set tablePath := honestTablePath S L k o w coins.table
  set extPath := params.external.honest o' q coins.external
  have houter : honestOuterPath params w coins =
      joinPath _ _ (joinPath _ _ busPath tablePath) extPath := by
    unfold honestOuterPath
    dsimp only
    rw [show Bus.outputClaim S L k (honestBusPath S L k w coins.bus) = some o from hbus, Option.getD_some]
    rw [show TableSumcheck.outputClaim S L k o (honestTablePath S L k o w coins.table) = some o' from htable,
      Option.getD_some]
  have hout : (outerReduction params.toSetup).output (honestOuterPath params w coins) =
      ((some o, some o'), params.external.output o' extPath) := by
    rw [houter]
    unfold outerReduction
    rw [Reduction.then_output, splitPath_joinPath, Reduction.then_output, splitPath_joinPath]
    change ((Bus.outputClaim S L k busPath,
      (tableReduction params.toSetup (Bus.outputClaim S L k busPath)).output tablePath),
      (externalReduction params.toSetup
        ((tableReduction params.toSetup (Bus.outputClaim S L k busPath)).output tablePath)).output extPath) = _
    rw [hbus]
    change ((some o, TableSumcheck.outputClaim S L k o tablePath),
      (externalReduction params.toSetup (TableSumcheck.outputClaim S L k o tablePath)).output extPath) = _
    rw [htable]
    rfl
  obtain ⟨hactive, ⟨_, hpoint, hboundary⟩, hvalues⟩ := hterm'
  have hstart : Retained.input (params.external.labels o') q := by
    apply params.external.start_complete o' q (params.external.rider_stack w _ shaped hext)
    rw [hinterp]
    exact fun t i _ ↦ hvalues t i
  obtain ⟨eactive, eclaims⟩ := params.external.honest_holds o' q coins.external hstart
  have hpool : ∀ c ∈ pool S L k M o', c.Holds (fun u ↦ ofK (q u)) := by
    apply (pool_holds_iff params.fits params.boundary w q _ o').mpr
    · exact ⟨hboundary, fun t i _ ↦ hvalues t i⟩
    · rw [← hinterp]
      exact agrees_interpret params.toSetup q
  have hclaims : ∀ c ∈ openingClaims ((outerReduction params.toSetup).output
      (honestOuterPath params w coins)), c.Holds (fun u ↦ ofK (q u)) := by
    rw [hout]
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hpool c h
    · exact eclaims c h
  unfold Accepts executionParts honestPath
  dsimp only
  rw [splitPath_joinPath]
  dsimp only
  refine ⟨?_, Pcs.Honest.prove_accepts params.schedule q _ coins.opening hclaims⟩
  rw [hout]
  exact ⟨hactive, hpoint, eactive⟩

end CompStark.Tables.Composed
