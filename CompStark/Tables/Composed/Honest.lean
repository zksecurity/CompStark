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

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- The verifier's coins of the composed system of a setup, its external argument's honest prover
and an opening schedule. -/
structure Coins (setup : Setup S L k M) (honest : setup.external.Honest) (schedule : Whir.Schedule K M) where
  /-- The bus's coins. -/
  bus : BusCoins S L k
  /-- The table sumcheck's coins. -/
  table : TableCoins S L
  /-- The external argument's coins. -/
  external : honest.Coins
  /-- The opening's coins. -/
  opening : Pcs.WhirCoins K E schedule

/-- A bus output for a rejected bus, which an honest prover never meets. -/
def rejectedBus : Bus.Output S L k := ⟨0, 0, [], 0, 0, false⟩

/-- The honest outer transcript. -/
def honestOuterPath (setup : Setup S L k M) (honest : setup.external.Honest) {schedule : Whir.Schedule K M}
    (w : Witness K S.tables.length) (coins : Coins setup honest schedule) :
    (outerProtocol setup).tree.ExecutionPath :=
  let busPath := honestBusPath S L k w coins.bus
  let bus := (Bus.outputClaim S L k busPath).getD rejectedBus
  let tablePath := honestTablePath S L k bus w coins.table
  let table := (TableSumcheck.outputClaim S L k bus tablePath).getD rejectedOutput
  joinPath _ _ (joinPath _ _ busPath tablePath)
    (honest.honest table (S.stack L M w) coins.external)

/-- The honest transcript of the composed system of a setup and an opening schedule. -/
def honestPath (setup : Setup S L k M) (honest : setup.external.Honest) (schedule : Whir.Schedule K M)
    (w : Witness K S.tables.length) (coins : Coins setup honest schedule) :
    (composedProtocol setup schedule).tree.ExecutionPath :=
  let outer := honestOuterPath setup honest w coins
  let opening := Pcs.Honest.prove schedule (S.stack L M w)
    (openingClaims setup (outerOutput setup outer)) coins.opening
  ⟨opening.initial, joinPath _ _ outer opening.transcript⟩

variable (params : Parameters S L k M)

/-- Completeness: for every satisfying witness whose padding rows are the padding row, the
specification verifier accepts the honest transcript against every coin sequence. -/
theorem completeness (honest : params.external.Honest) (w : Witness K S.tables.length)
    (hsat : S.Satisfied L w) (padded : S.Padded L w) (coins : Coins params.toSetup honest params.schedule) :
    Accepts params (honestPath params.toSetup honest params.schedule w coins) := by
  have shaped := hsat.1
  have hext := hsat.2.2.2.2
  have hinterp := params.external.interpret_stack w shaped hext
  obtain ⟨o, hbus, hterm⟩ := honestBus_terminal params.wellFormed params.busShape w hsat padded coins.bus
  obtain ⟨o', htable, hterm'⟩ := honestTable_terminal params.wellFormed params.degree_le o w hsat hterm coins.table
  set q := S.stack L M w
  set busPath := honestBusPath S L k w coins.bus
  set tablePath := honestTablePath S L k o w coins.table
  set extPath := honest.honest o' q coins.external
  have houter : honestOuterPath params.toSetup honest w coins =
      joinPath _ _ (joinPath _ _ busPath tablePath) extPath := by
    unfold honestOuterPath
    dsimp only
    rw [show Bus.outputClaim S L k (honestBusPath S L k w coins.bus) = some o from hbus, Option.getD_some]
    rw [show TableSumcheck.outputClaim S L k o (honestTablePath S L k o w coins.table) = some o' from htable,
      Option.getD_some]
  have hout : (outerReduction params.toSetup params.reductions).output (honestOuterPath params.toSetup honest w coins) =
      ((some o, some o'), params.external.output o' extPath) := by
    rw [houter]
    unfold outerReduction
    rw [Reduction.then_output, splitPath_joinPath, Reduction.then_output, splitPath_joinPath]
    change ((Bus.outputClaim S L k busPath,
      (tableReduction params.toSetup (Bus.outputClaim S L k busPath)).output tablePath),
      (externalReduction params.toSetup params.reductions
        ((tableReduction params.toSetup (Bus.outputClaim S L k busPath)).output tablePath)).output extPath) = _
    rw [hbus]
    change ((some o, TableSumcheck.outputClaim S L k o tablePath),
      (externalReduction params.toSetup params.reductions (TableSumcheck.outputClaim S L k o tablePath)).output extPath) = _
    rw [htable, externalReduction_output]
    rfl
  obtain ⟨hlength, hactive, ⟨_, hpoint, hboundary⟩, hvalues⟩ := hterm'
  have hstart : params.external.start o' q := by
    apply params.external.start_complete o' q hlength (params.external.rider_stack w _ shaped hext)
    rw [hinterp]
    exact fun t i _ ↦ hvalues t i
  obtain ⟨eactive, eclaims⟩ := honest.honest_holds o' q coins.external hstart (by rw [hinterp]; exact hext)
  have hpool : ∀ c ∈ pool S L k M o', c.Holds (fun u ↦ ofK (q u)) := by
    apply (pool_holds_iff params.fits params.boundary w q _ o').mpr
    · exact ⟨hboundary, fun t i _ ↦ hvalues t i⟩
    · rw [← hinterp]
      exact agrees_interpret params.toSetup q
  have hclaims : ∀ c ∈ openingClaims params.toSetup (outerOutput params.toSetup
      (honestOuterPath params.toSetup honest w coins)), c.Holds (fun u ↦ ofK (q u)) := by
    rw [outerOutput_eq params.toSetup params.reductions, hout]
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hpool c h
    · exact eclaims c h
  unfold Accepts executionParts honestPath
  dsimp only
  rw [splitPath_joinPath]
  dsimp only
  rw [← outerOutput_eq params.toSetup params.reductions]
  refine ⟨?_, Pcs.Honest.prove_accepts params.schedule q _ coins.opening hclaims⟩
  rw [outerOutput_eq params.toSetup params.reductions, hout]
  exact ⟨hactive, hpoint, eactive⟩

end CompStark.Tables.Composed
