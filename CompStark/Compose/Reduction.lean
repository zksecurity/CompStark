/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compose.ListLift
public import CompStark.Multilinear.Retained

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

/-! Retained-carrier reductions with explicit terminal problems and ArkLib sequential composition. -/

@[expose] public section

namespace CompStark.Compose

open Interaction Interaction.Oracle Interaction.Oracle.Security PFunctor.FreeM


/-- Constant-shape dependent append retains both role and oracle-interface decorations. -/
def appendProtocol (first second : Protocol) : Protocol :=
  ⟨PFunctor.FreeM.append first.tree (fun _ => second.tree),
    Displayed.Decoration.append first.roles (fun _ => second.roles),
    Displayed.Decoration.append first.oracles (fun _ => second.oracles)⟩

/-- Split an actual appended execution, retaining concrete oracle payloads. -/
def splitPath (first second : Protocol)
    (path : (appendProtocol first second).tree.ExecutionPath) :
    first.tree.ExecutionPath × second.tree.ExecutionPath :=
  let parts := PathAlong.split TypeTree.runtimeLens first.tree (fun _ => second.tree) path
  (parts.1, parts.2)

/-- A closed endpoint problem over the actual retained object. -/
def endpointProblem (W A : Type) (fixed : W) (relation : A → W → Prop) :
    Problem (⟨fun _ : Unit => A⟩ : ClaimFamily Unit) where
  Witness _ _ := W
  admissible _ _ := True
  rel _ claim witness := witness = fixed ∧ relation claim witness
  rel_admissible := fun _ _ _ _ => trivial

/-- An authored reduction together with its fixed-object certificate and named endpoint identification. Its output is read from the actual path, never supplied by an accepting-witness oracle. -/
structure Reduction (protocol : Protocol) (W A : Type) where
  /-- Input predicate on the retained object. -/
  input : W → Prop
  /-- Concrete public endpoint parser. -/
  output : protocol.tree.ExecutionPath → A
  /-- Obligations transferred to the following reduction. -/
  relation : A → W → Prop
  /-- Fixed-object certificates for every candidate, including candidates outside the proximity list. -/
  certificate : (fixed : W) → KnowledgeCertificate protocol.tree protocol.roles
    (ListLift.bound fixed input)
  /-- The exact carrier and relation of every authored endpoint. -/
  terminal : (fixed : W) → TerminalRelation (certificate fixed).extractor
    (endpointProblem W A fixed relation) (fun _ => ()) output
  /-- Complete extraction retains exactly the object identified at the endpoint. -/
  extract_eq : ∀ fixed path witness, (certificate fixed).extractor.extractWitness path witness =
    (terminal fixed).witnessEquiv path witness
  /-- Common authored samplers and errors. -/
  challenges : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles
  /-- The common schedule is independent of the candidate. -/
  schedule_eq : ∀ fixed, (certificate fixed).challenges = challenges

/-- The authored terminal predicate agrees with the parsed endpoint on the same retained object. -/
def EndpointLaw {W A : Type} (protocol : Protocol) (labels : ListLift.Labels W protocol.tree)
    (output : protocol.tree.ExecutionPath → A) (relation : A → W → Prop) : Prop :=
  ∀ fixed path witness,
      ((ListLift.boundExtractor fixed labels).terminalState path).holds witness ↔
        (endpointProblem W A fixed relation).rel () (output path)
          ((ListLift.retainedTerminalEquiv
            (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness) labels)
            path) ((RoundExtractor.terminalWitnessEquiv
              (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
                labels)) (ListLift.bound fixed (ListLift.input labels)) (Equiv.refl W) path) witness))

/-- An endpoint predicate law on the common carrier supplies the equality-bound terminal law. -/
theorem endpoint_of_terminalPredicate {W A : Type} (protocol : Protocol)
    (labels : ListLift.Labels W protocol.tree) (output : protocol.tree.ExecutionPath → A)
    (relation : A → W → Prop)
    (endpoint : ∀ path witness, ListLift.terminalPredicate labels path witness ↔
      relation (output path) witness) : EndpointLaw protocol labels output relation := by
  intro fixed path witness
  exact (ListLift.bound_terminal_holds fixed labels path witness).trans
    (and_congr_right fun _ => endpoint path _)

/-- Author a reduction with concrete identity maps; its proof obligations are the prover laws, local bounds, and endpoint interpretation. -/
def reduction {W A : Type} (protocol : Protocol) (labels : ListLift.Labels W protocol.tree)
    (output : protocol.tree.ExecutionPath → A) (relation : A → W → Prop)
    (challenges : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles)
    (preserving : ∀ fixed, (ListLift.boundExtractor fixed labels).IsProverPreserving protocol.roles)
    (bounded : ∀ fixed, (ListLift.boundExtractor fixed labels).IsLocallyBounded
      protocol.roles challenges)
    (endpoint : EndpointLaw protocol labels output relation) :
    Reduction protocol W A where
  input := ListLift.input labels
  output := output
  relation := relation
  certificate fixed := {
    extractor := ListLift.boundExtractor fixed labels
    challenges := challenges
    prover_preserving := preserving fixed
    local_bound := bounded fixed }
  terminal fixed := {
    witnessEquiv := fun path =>
      (RoundExtractor.terminalWitnessEquiv
        (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
          labels)) (ListLift.bound fixed (ListLift.input labels)) (Equiv.refl W) path).trans
        (ListLift.retainedTerminalEquiv _ path)
    knowledge_iff := endpoint fixed }
  extract_eq fixed := ListLift.bound_extractWitness fixed labels
  challenges := challenges
  schedule_eq := fun _ => rfl

/-- Transfer the laws of an existing component certificate to its physical retained carrier, framing or restricting its prefixes as needed. The source certificate's actual proof fields discharge the transport premises. -/
def componentReduction {W A : Type} (protocol : Protocol)
    (labels : ListLift.Labels W protocol.tree)
    (output : protocol.tree.ExecutionPath → A) (relation : A → W → Prop)
    (challenges : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles)
    {sourceTree : Oracle.TypeTree} {sourceRoles : sourceTree.RoleDecoration}
    {sourceStates : W → KnowledgeState}
    (source : ∀ fixed, KnowledgeCertificate sourceTree sourceRoles (sourceStates fixed))
    (transport : ∀ fixed,
      (source fixed).extractor.IsProverPreserving sourceRoles →
      (source fixed).extractor.IsLocallyBounded sourceRoles (source fixed).challenges →
      (ListLift.boundExtractor fixed labels).IsProverPreserving protocol.roles ∧
      (ListLift.boundExtractor fixed labels).IsLocallyBounded protocol.roles challenges)
    (endpoint : EndpointLaw protocol labels output relation) : Reduction protocol W A :=
  reduction protocol labels output relation challenges
    (fun fixed => (transport fixed (source fixed).prover_preserving (source fixed).local_bound).1)
    (fun fixed => (transport fixed (source fixed).prover_preserving (source fixed).local_bound).2)
    endpoint

/-- Sequentially compose at the actual first-stage endpoint. The suffix input law is required on every endpoint, even one that is false or rejected. -/
def Reduction.then {P Q : Protocol} {W A B : Type} (first : Reduction P W A)
    (second : A → Reduction Q W B)
    (seam : ∀ claim witness, (second claim).input witness ↔ first.relation claim witness) :
    Reduction (appendProtocol P Q) W (A × B) := by
  let suffix := fun _ : P.tree.BranchPath => Q.tree
  let secondCert := fun (fixed : W) (path : P.tree.ExecutionPath) =>
    ((second (first.output path)).certificate fixed).changeInputState
      (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) () (first.output path))
      (Equiv.refl W) (by
        intro witness
        exact and_congr_right (fun _ => (seam (first.output path) witness).symm))
  let cert := fun fixed => KnowledgeCertificate.sequential (first.certificate fixed) suffix
    (fun _ => Q.roles) (endpointProblem W A fixed first.relation) (fun _ => ()) first.output
    (first.terminal fixed) (secondCert fixed)
  let finalRel := fun (claim : A × B) (witness : W) =>
    (second claim.1).relation claim.2 witness
  exact {
    input := first.input
    output := fun path => let parts := splitPath P Q path
                          (first.output parts.1, (second (first.output parts.1)).output parts.2)
    relation := finalRel
    certificate := cert
    terminal := by
      intro fixed
      exact KnowledgeCertificate.sequentialTerminalRelation (first.certificate fixed) suffix
        (fun _ => Q.roles) (endpointProblem W A fixed first.relation) (fun _ => ()) first.output
        (first.terminal fixed) (secondCert fixed) (endpointProblem W (A × B) fixed finalRel)
        (fun _ _ => ()) (fun path rest =>
          (first.output path, (second (first.output path)).output rest))
        (fun path => {
          witnessEquiv :=
            (((second (first.output path)).terminal fixed).changeInputState
              (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) ()
                (first.output path)) (Equiv.refl W) (by
                intro witness
                exact and_congr_right (fun _ => (seam (first.output path) witness).symm))).witnessEquiv
          knowledge_iff := fun rest witness =>
            (((second (first.output path)).terminal fixed).changeInputState
              (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) ()
                (first.output path)) (Equiv.refl W) (by
                  intro witness
                  exact and_congr_right (fun _ =>
                    (seam (first.output path) witness).symm))).knowledge_iff rest witness })
    extract_eq := by
      intro fixed full witness
      let parts := PathAlong.split Oracle.TypeTree.runtimeLens P.tree suffix full
      let after := KnowledgeCertificate.sequentialSuffix (first.certificate fixed) suffix
        (fun _ => Q.roles) (endpointProblem W A fixed first.relation) (fun _ => ()) first.output
        (first.terminal fixed) (secondCert fixed)
      have extraction := ListLift.append_extractWitness (first.certificate fixed).extractor suffix
        (fun path => (after path).extractor) full witness
      refine extraction.trans ?_
      rw [first.extract_eq]
      change (first.terminal fixed).witnessEquiv parts.1
        ((after parts.1).extractor.extractWitness parts.2 _) = _
      let terminal := ListLift.appendTerminalEquiv (first.certificate fixed).extractor suffix
        (fun path => (after path).extractor) full witness
      have firstRoot := RoundExtractor.extractWitness_changeInputState
        (secondCert fixed parts.1).extractor ((first.certificate fixed).extractor.terminalState parts.1)
        ((first.terminal fixed).witnessEquiv parts.1) parts.2 terminal
      refine firstRoot.trans ?_
      have changeRoot := RoundExtractor.extractWitness_changeInputState
        ((second (first.output parts.1)).certificate fixed).extractor
        (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) () (first.output parts.1))
        (Equiv.refl W) parts.2
        (RoundExtractor.terminalWitnessEquiv (secondCert fixed parts.1).extractor
          ((first.certificate fixed).extractor.terminalState parts.1)
          ((first.terminal fixed).witnessEquiv parts.1) parts.2 terminal)
      exact changeRoot.trans ((second (first.output parts.1)).extract_eq fixed parts.2 _)
    challenges := RoundExtractor.appendSchedule suffix P.roles (fun _ => Q.roles)
      first.challenges (fun path => (second (first.output path)).challenges)
    schedule_eq := by
      intro fixed
      change RoundExtractor.appendSchedule suffix P.roles (fun _ => Q.roles)
        (first.certificate fixed).challenges
        (fun path => ((second (first.output path)).certificate fixed).challenges) = _
      simp only [Reduction.schedule_eq] }
/-- Executable retained maps and endpoint identifications, independent of challenge distributions. -/
structure ReductionMaps (protocol : Protocol) (W A : Type) where
  /-- Predicate at the input. -/
  input : W → Prop
  /-- Endpoint read from the actual transcript. -/
  output : protocol.tree.ExecutionPath → A
  /-- Predicate at the endpoint. -/
  relation : A → W → Prop
  /-- Backward maps for each fixed retained object. -/
  extractor : (fixed : W) → RoundExtractor protocol.tree (ListLift.bound fixed input)
  /-- Explicit terminal carrier and predicate identification. -/
  terminal : (fixed : W) → TerminalRelation (extractor fixed)
    (endpointProblem W A fixed relation) (fun _ => ()) output
  /-- Complete extraction preserves the object identified by the terminal map. -/
  extract_eq : ∀ fixed path witness, (extractor fixed).extractWitness path witness =
    (terminal fixed).witnessEquiv path witness

/-- Forget the analytical samplers of a reduction. -/
def Reduction.maps {P : Protocol} {W A : Type} (r : Reduction P W A) : ReductionMaps P W A where
  input := r.input
  output := r.output
  relation := r.relation
  extractor fixed := (r.certificate fixed).extractor
  terminal := r.terminal
  extract_eq := r.extract_eq

/-- Retained backward maps specified by prefix predicates and the endpoint law. -/
def retainedMaps {W A : Type} (protocol : Protocol) (labels : ListLift.Labels W protocol.tree)
    (output : protocol.tree.ExecutionPath → A) (relation : A → W → Prop)
    (endpoint : EndpointLaw protocol labels output relation) : ReductionMaps protocol W A where
  input := ListLift.input labels
  output := output
  relation := relation
  extractor fixed := ListLift.boundExtractor fixed labels
  terminal fixed := {
    witnessEquiv := fun path =>
      (RoundExtractor.terminalWitnessEquiv
        (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
          labels)) (ListLift.bound fixed (ListLift.input labels)) (Equiv.refl W) path).trans
        (ListLift.retainedTerminalEquiv _ path)
    knowledge_iff := endpoint fixed }
  extract_eq := fun fixed => ListLift.bound_extractWitness fixed labels

/-- Compose executable reductions at the actual parsed endpoint. -/
def ReductionMaps.then {P Q : Protocol} {W A B : Type} (first : ReductionMaps P W A)
    (second : A → ReductionMaps Q W B)
    (seam : ∀ claim witness, (second claim).input witness ↔ first.relation claim witness) :
    ReductionMaps (appendProtocol P Q) W (A × B) := by
  let suffix := fun _ : P.tree.BranchPath => Q.tree
  let secondExt := fun (fixed : W) (path : P.tree.ExecutionPath) =>
    ((second (first.output path)).extractor fixed).changeInputState
      (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) () (first.output path))
      (Equiv.refl W)
  let after := fun (fixed : W) (path : P.tree.ExecutionPath) =>
    (secondExt fixed path).changeInputState ((first.extractor fixed).terminalState path)
      ((first.terminal fixed).witnessEquiv path)
  let finalRel := fun (claim : A × B) (witness : W) =>
    (second claim.1).relation claim.2 witness
  exact {
    input := first.input
    output := fun path => let parts := splitPath P Q path
                          (first.output parts.1, (second (first.output parts.1)).output parts.2)
    relation := finalRel
    extractor fixed := (first.extractor fixed).append suffix (after fixed)
    terminal fixed := TerminalRelation.append (first.extractor fixed) suffix (after fixed)
      (endpointProblem W (A × B) fixed finalRel) (fun _ _ => ())
      (fun path rest => (first.output path, (second (first.output path)).output rest))
      (fun path => {
        witnessEquiv :=
          ((((second (first.output path)).terminal fixed).changeInputState
            (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) () (first.output path))
            (Equiv.refl W) (by
              intro witness
              exact and_congr_right (fun _ => (seam (first.output path) witness).symm))).changeInputState
            ((first.extractor fixed).terminalState path) ((first.terminal fixed).witnessEquiv path)
            ((first.terminal fixed).knowledge_iff path)).witnessEquiv
        knowledge_iff := fun rest witness =>
          ((((second (first.output path)).terminal fixed).changeInputState
            (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) () (first.output path))
            (Equiv.refl W) (by
              intro witness
              exact and_congr_right (fun _ => (seam (first.output path) witness).symm))).changeInputState
            ((first.extractor fixed).terminalState path) ((first.terminal fixed).witnessEquiv path)
            ((first.terminal fixed).knowledge_iff path)).knowledge_iff rest witness })
    extract_eq := by
      intro fixed full witness
      let parts := PathAlong.split Oracle.TypeTree.runtimeLens P.tree suffix full
      have extraction := ListLift.append_extractWitness (first.extractor fixed) suffix
        (after fixed) full witness
      refine extraction.trans ?_
      rw [first.extract_eq]
      let terminal := ListLift.appendTerminalEquiv (first.extractor fixed) suffix
        (after fixed) full witness
      have firstRoot := RoundExtractor.extractWitness_changeInputState
        (secondExt fixed parts.1) ((first.extractor fixed).terminalState parts.1)
        ((first.terminal fixed).witnessEquiv parts.1) parts.2 terminal
      refine firstRoot.trans ?_
      have changeRoot := RoundExtractor.extractWitness_changeInputState
        ((second (first.output parts.1)).extractor fixed)
        (KnowledgeState.ofProblem (endpointProblem W A fixed first.relation) () (first.output parts.1))
        (Equiv.refl W) parts.2
        (RoundExtractor.terminalWitnessEquiv (secondExt fixed parts.1)
          ((first.extractor fixed).terminalState parts.1)
          ((first.terminal fixed).witnessEquiv parts.1) parts.2 terminal)
      exact changeRoot.trans ((second (first.output parts.1)).extract_eq fixed parts.2 _) }

/-- Forgetting analytical schedules commutes with sequential composition. -/
theorem Reduction.maps_then {P Q : Protocol} {W A B : Type} (first : Reduction P W A)
    (second : A → Reduction Q W B)
    (seam : ∀ claim witness, (second claim).input witness ↔ first.relation claim witness) :
    (first.then second seam).maps = first.maps.then (fun claim => (second claim).maps) seam := by
  rfl

end CompStark.Compose
