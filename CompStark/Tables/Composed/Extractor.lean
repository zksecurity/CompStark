/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Certificate

/-! The composed system's extractor as a computable definition (`extractor`), separate from the
certificate's challenge schedule and its error, which are probability-valued. The outer reductions'
backward maps are their `ReductionMaps` (`outerMaps`), and the certificate's extractor is this one
(`certificate_extractor`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

section
variable (setup : Setup S L k M)

/-- The bus phase's endpoint law on the stack. -/
theorem busEndpoint : EndpointLaw (Bus.protocol S L k)
    (pullLabels setup.external.interpret (setup.external.rider []) (Bus.labels S L k))
    (Bus.outputClaim S L k) (busRelation setup) := by
  have endpoint := pull_endpoint (Bus.protocol S L k) setup.external.interpret
    (setup.external.rider []) (Bus.labels S L k) (Bus.outputClaim S L k)
    (fun out q ↦ match out with | none => False | some out => Bus.Terminal S L k out q)
    (fun fixed ↦ (Bus.terminalRelation S L k fixed).knowledge_iff)
  intro fixed path witness
  refine (endpoint fixed path witness).trans ?_
  apply and_congr_right
  intro _
  cases Bus.outputClaim S L k path with
  | none => exact and_iff_left_of_imp False.elim
  | some out => exact Iff.rfl

/-- The bus phase's backward maps. -/
def busMaps : ReductionMaps (Bus.protocol S L k) (Whir.Table K M) (Option (Bus.Output S L k)) :=
  retainedMaps (Bus.protocol S L k)
    (pullLabels setup.external.interpret (setup.external.rider []) (Bus.labels S L k))
    (Bus.outputClaim S L k) (busRelation setup) (busEndpoint setup)

/-- The bus reduction's maps. -/
theorem busReduction_maps : (busReduction setup).maps = busMaps setup := rfl

/-- The table phase's backward maps. -/
def tableMaps : Option (Bus.Output S L k) →
    ReductionMaps (TableSumcheck.protocol S L) (Whir.Table K M) (Option (TableSumcheck.Output S L k))
  | none => retainedMaps (TableSumcheck.protocol S L) (falseLabels _ _) (fun _ ↦ none) (tableEndpoint setup)
      (by
        intro fixed path witness
        change _ ↔ ListLift.boundTerminalEquiv fixed (falseLabels _ _) path witness = fixed ∧
          tableEndpoint setup none (ListLift.boundTerminalEquiv fixed (falseLabels _ _) path witness)
        rw [ListLift.bound_terminal_holds, terminalPredicate_falseLabels]
        simp only [tableEndpoint, and_false])
  | some bus => retainedMaps (TableSumcheck.protocol S L) (tableLabels setup bus)
      (TableSumcheck.outputClaim S L k bus) (tableEndpoint setup)
      (endpoint_of_terminalPredicate _ _ _ _ (by
        intro path q
        exact tableRounds_endpoint setup bus path.1 _ [] _ _ path.2 q))

/-- The table reductions' maps. -/
theorem tableReduction_maps : (bus : Option (Bus.Output S L k)) →
    (tableReduction setup bus).maps = tableMaps setup bus
  | none => rfl
  | some _ => rfl

variable (red : setup.external.Reductions)

/-- The external argument's backward maps. -/
def externalMaps : Option (TableSumcheck.Output S L k) →
    ReductionMaps setup.external.protocol (Whir.Table K M) setup.external.Output
  | none => retainedMaps setup.external.protocol (falseLabels _ _)
      (setup.external.output (rejectedOutput : TableSumcheck.Output S L k)) (fun _ _ ↦ False)
      (by
        intro fixed path witness
        change _ ↔ ListLift.boundTerminalEquiv fixed (falseLabels _ _) path witness = fixed ∧ False
        rw [ListLift.bound_terminal_holds, terminalPredicate_falseLabels])
  | some o => (red.reduction o (tableGate o)).maps

/-- The external reductions' maps. -/
theorem externalReduction_maps : (table : Option (TableSumcheck.Output S L k)) →
    (externalReduction setup red table).maps = externalMaps setup red table
  | none => rfl
  | some _ => rfl

/-- Composition of maps depends only on the composed maps. -/
theorem ReductionMaps.then_congr {P Q : Protocol} {W A B : Type} {first first' : ReductionMaps P W A}
    {second second' : A → ReductionMaps Q W B} (hfirst : first = first') (hsecond : second = second')
    (seam : ∀ claim witness, (second claim).input witness ↔ first.relation claim witness)
    (seam' : ∀ claim witness, (second' claim).input witness ↔ first'.relation claim witness) :
    first.then second seam = first'.then second' seam' := by
  subst hfirst hsecond
  rfl

/-- The outer reductions' backward maps in sequence. -/
def outerMaps : ReductionMaps (outerProtocol setup) (Whir.Table K M)
    ((Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × setup.external.Output) :=
  ((busMaps setup).then (tableMaps setup) (by
      intro bus q
      cases bus with
      | none =>
        change ListLift.input (falseLabels _ (TableSumcheck.protocol S L).tree) q ↔ busRelation setup none q
        simp only [busRelation, input_falseLabels]
      | some bus => exact Iff.rfl)).then
    (fun claim ↦ externalMaps setup red claim.2) (by
      intro claim q
      rcases claim with ⟨bus, table⟩
      cases bus <;> cases table <;>
      first
      | (change ListLift.input (falseLabels _ _) q ↔ False; rw [input_falseLabels])
      | (rename_i o
         change (red.reduction o (tableGate o)).input q ↔ tableEndpoint setup (some o) q
         rw [red.reduction_input]
         simp only [tableEndpoint, tableGate]
         exact ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h2, h3, h4, h1⟩, fun ⟨h2, h3, h4, h1⟩ ↦ ⟨h1, h2, h3, h4⟩⟩))

/-- The outer reduction's maps. -/
theorem outerReduction_maps : (outerReduction setup red).maps = outerMaps setup red :=
  (Reduction.maps_then _ _ _).trans (ReductionMaps.then_congr
    ((Reduction.maps_then _ _ _).trans (ReductionMaps.then_congr (busReduction_maps setup)
      (funext (tableReduction_maps setup)) _ _))
    (funext fun claim => externalReduction_maps setup red claim.2) _ _)

end

variable (params : Parameters S L k M)

/-- The extractor over the outer reductions' backward maps `R`, list-decoded at the committed word. -/
def chainOuter (R : ReductionMaps (outerProtocol params.toSetup) (Whir.Table K M)
      ((Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × params.external.Output))
    (word : Whir.oracleMessage K params.schedule) :
    RoundExtractor (outerProtocol params.toSetup).tree (committedState params word) :=
  ListLift.rebaseExtractor (outer_ne_done params.toSetup)
    (ListLift.extractor (candidates params.schedule params.decoder word) fun fixed => R.extractor fixed)
    (fun witness => witness.2)

/-- The outer endpoint's witness over the maps `R`: the candidate and the same stack. -/
def chainTerminalEquiv (R : ReductionMaps (outerProtocol params.toSetup) (Whir.Table K M)
      ((Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × params.external.Output))
    (word : Whir.oracleMessage K params.schedule) (path : (outerProtocol params.toSetup).tree.ExecutionPath) :
    ((chainOuter params R word).terminalState path).Witness ≃ (Whir.Table K M × Whir.Table K M) :=
  (ListLift.rebaseTerminalEquiv (target := committedState params word) (outer_ne_done params.toSetup)
    (ListLift.extractor (candidates params.schedule params.decoder word) fun fixed => R.extractor fixed)
    (fun witness => witness.2) path).trans
    ((ListLift.terminalEquiv (candidates params.schedule params.decoder word)
      (fun fixed => R.extractor fixed) path).trans
      (Equiv.sigmaEquivProdOfEquiv fun fixed => (R.terminal fixed).witnessEquiv path))

/-- WHIR's extractor at the outer endpoint over the maps `R`. -/
def chainOpening (R : ReductionMaps (outerProtocol params.toSetup) (Whir.Table K M)
      ((Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × params.external.Output))
    (word : Whir.oracleMessage K params.schedule) (path : (outerProtocol params.toSetup).tree.ExecutionPath) :
    RoundExtractor (Whir.opening E params.schedule).tree ((chainOuter params R word).terminalState path) :=
  ListLift.rebaseExtractor (opening_ne_done params.schedule)
    (ListLift.frameExtractor (publicAccepted params.toSetup (R.output path))
      (Whir.openingExtractor (algebraMap K E) params.schedule
        (Whir.proximityFamily (algebraMap K E) params.schedule params.security)
        (Whir.openingState (algebraMap K E) params.schedule params.security word
          (openingClaims params.toSetup (R.output path))).holds params.decoders word
        (openingClaims params.toSetup (R.output path)) params.decoder))
    (fun q => (chainTerminalEquiv params R word path).symm (q, q))

/-- The composed extractor over the outer reductions' backward maps `R`. -/
def chain (R : ReductionMaps (outerProtocol params.toSetup) (Whir.Table K M)
      ((Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × params.external.Output)) :
    RoundExtractor (protocol params).tree (inputState params) := fun word =>
  ⟨committedState params word, id, (chainOuter params R word).append
    (fun _ => (Whir.opening E params.schedule).tree) (fun path => chainOpening params R word path)⟩

/-- The certificate's extractor is the chain over the outer reduction's maps. -/
theorem certificate_chain :
    (certificate params).extractor = chain params (outerReduction params.toSetup params.reductions).maps := rfl

/-- The composed system's extractor. -/
def extractor : RoundExtractor (protocol params).tree (inputState params) :=
  chain params (outerMaps params.toSetup params.reductions)

/-- The composed certificate extracts with `extractor`. -/
theorem certificate_extractor : (certificate params).extractor = extractor params :=
  (certificate_chain params).trans (congrArg (chain params) (outerReduction_maps _ _))

end CompStark.Tables.Composed
