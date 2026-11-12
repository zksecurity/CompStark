/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compose.Reduction

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

/-! Transport identity extractors through a fixed view of the retained object. -/

@[expose] public section

namespace CompStark.Compose

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp
open CompStark.Multilinear


/-- Prefix predicates of an existing retained-object component, pulled back to the physical stack and framed by an unchanged obligation. -/
def pullLabels {V W : Type} (view : W → V) (frame : W → Prop) :
    {tree : Oracle.TypeTree} → Retained.Labels V tree → ListLift.Labels W tree
  | .done, labels => fun witness => labels (view witness) ∧ frame witness
  | .public _ _, labels =>
      ⟨fun witness => labels.1 (view witness) ∧ frame witness,
        fun move => pullLabels view frame (labels.2 move)⟩
  | .oracle _ _, labels =>
      ⟨fun witness => labels.1 (view witness) ∧ frame witness,
        fun message => pullLabels view frame (labels.2 message)⟩

/-- A rejecting prefix has no knowledge witness at any later authored node. -/
def falseLabels (W : Type) : (tree : Oracle.TypeTree) → ListLift.Labels W tree
  | .done => fun _ => False
  | .public _ next => ⟨fun _ => False, fun move => falseLabels W (next move)⟩
  | .oracle _ next => ⟨fun _ => False, fun _ => falseLabels W (next PUnit.unit)⟩

/-- Rejected labels expose the false predicate at every root. -/
theorem input_falseLabels (W : Type) (tree : Oracle.TypeTree) :
    ListLift.input (falseLabels W tree) = fun _ => False := by
  cases tree using Oracle.TypeTree.casesOn <;> rfl

/-- A permanently rejected prefix cannot acquire knowledge at a prover move. -/
theorem false_retained_preserving {W : Type} (fixed : W) :
    (tree : Oracle.TypeTree) → (roles : tree.RoleDecoration) →
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (falseLabels W tree))).IsProverPreserving roles
  | .done, _ => trivial
  | .public _ next, roles => by
      refine ⟨?_, fun move => false_retained_preserving fixed (next move) (roles.2 move)⟩
      intro move _ witness good
      change W at witness
      change ListLift.input (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
        (falseLabels W (next move))) witness at good
      rw [ListLift.input_map] at good
      rw [input_falseLabels] at good
      exact good.2.elim
  | .oracle _ next, roles => by
      refine ⟨?_, fun _ => false_retained_preserving fixed (next PUnit.unit) (roles.2 PUnit.unit)⟩
      intro message witness good
      change W at witness
      change ListLift.input (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
        (falseLabels W (next PUnit.unit))) witness at good
      rw [ListLift.input_map] at good
      rw [input_falseLabels] at good
      exact good.2.elim

/-- Every challenge at a permanently rejected prefix has an empty bad event. -/
theorem false_retained_bounded {W : Type} (fixed : W) :
    (tree : Oracle.TypeTree) → (roles : tree.RoleDecoration) →
    (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (falseLabels W tree))).IsLocallyBounded roles schedule
  | .done, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, schedule =>
      fun move => false_retained_bounded fixed (next move) (roles move) (schedule.2 move)
  | .public _ next, ⟨.receiver, roles⟩, schedule => by
      refine ⟨?_, fun move => false_retained_bounded fixed (next move) (roles move) (schedule.2 move)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      refine (prEvent_mono _ _ (fun _ => False) ?_).trans (by
        simp only [prEvent_false, zero_le])
      rintro move ⟨witness, _, good⟩
      change W at witness
      change ListLift.input (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
        (falseLabels W (next move))) witness at good
      rw [ListLift.input_map] at good
      rw [input_falseLabels] at good
      exact good.2
  | .oracle _ next, roles, schedule =>
      fun message => false_retained_bounded fixed (next PUnit.unit) (roles.2 PUnit.unit) (schedule message)

/-- Equality-bound rejection preserves knowledge at every prover move. -/
theorem false_preserving {W : Type} (fixed : W) (tree : Oracle.TypeTree)
    (roles : tree.RoleDecoration) :
    (ListLift.boundExtractor fixed (falseLabels W tree)).IsProverPreserving roles :=
  RoundExtractor.isProverPreserving_changeInputState
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (falseLabels W tree))) (ListLift.bound fixed (ListLift.input (falseLabels W tree))) (Equiv.refl W)
    (fun witness => by rw [ListLift.input_map]; exact Iff.rfl) roles
    (false_retained_preserving fixed tree roles)

/-- Equality-bound rejection has no local challenge failure. -/
theorem false_bounded {W : Type} (fixed : W) (tree : Oracle.TypeTree)
    (roles : tree.RoleDecoration) (schedule : RoundExtractor.ChallengeSchedule tree roles) :
    (ListLift.boundExtractor fixed (falseLabels W tree)).IsLocallyBounded roles schedule :=
  RoundExtractor.isLocallyBounded_changeInputState
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (falseLabels W tree))) (ListLift.bound fixed (ListLift.input (falseLabels W tree))) (Equiv.refl W)
    (fun witness => by rw [ListLift.input_map]; exact Iff.rfl) roles schedule
    (false_retained_bounded fixed tree roles schedule)

/-- Every complete rejected path retains the false predicate. -/
theorem terminalPredicate_falseLabels (W : Type) :
    (tree : Oracle.TypeTree) → (path : tree.ExecutionPath) →
    ListLift.terminalPredicate (falseLabels W tree) path = fun _ => False
  | .done, _ => rfl
  | .public _ next, path => terminalPredicate_falseLabels W (next path.1) path.2
  | .oracle _ next, path => terminalPredicate_falseLabels W (next PUnit.unit) path.2

/-- Pulling back labels pulls back the root predicate and retains its frame. -/
theorem input_pullLabels {V W : Type} (view : W → V) (frame : W → Prop)
    {tree : Oracle.TypeTree} (labels : Retained.Labels V tree) (witness : W) :
    ListLift.input (pullLabels view frame labels) witness ↔
      Retained.input labels (view witness) ∧ frame witness := by
  cases tree using Oracle.TypeTree.casesOn <;> exact Iff.rfl

/-- The component predicate selected by the actual complete path. -/
def viewedTerminalPredicate {V : Type} : {tree : Oracle.TypeTree} →
    Retained.Labels V tree → tree.ExecutionPath → V → Prop
  | .done, labels, _ => labels
  | .public _ _, labels, path => viewedTerminalPredicate (labels.2 path.1) path.2
  | .oracle _ _, labels, path => viewedTerminalPredicate (labels.2 path.1) path.2

/-- Component identity maps retain their equality binding and terminal predicate. -/
theorem viewed_terminal_holds {V : Type} (fixed : V) : {tree : Oracle.TypeTree} →
    (labels : Retained.Labels V tree) → (path : tree.ExecutionPath) →
    (witness : ((Retained.extractor fixed labels).terminalState path).Witness) →
    ((Retained.extractor fixed labels).terminalState path).holds witness ↔
      Retained.terminalEquiv fixed labels path witness = fixed ∧
        viewedTerminalPredicate labels path (Retained.terminalEquiv fixed labels path witness)
  | .done, _, _, _ => Iff.rfl
  | .public _ _, labels, path, witness => viewed_terminal_holds fixed (labels.2 path.1) path.2 witness
  | .oracle _ _, labels, path, witness => viewed_terminal_holds fixed (labels.2 path.1) path.2 witness

/-- A pulled-back terminal predicate is the viewed component predicate and the retained frame. -/
theorem terminalPredicate_pullLabels {V W : Type} (view : W → V) (frame : W → Prop) :
    {tree : Oracle.TypeTree} → (labels : Retained.Labels V tree) → (path : tree.ExecutionPath) →
    (witness : W) → ListLift.terminalPredicate (pullLabels view frame labels) path witness ↔
      viewedTerminalPredicate labels path (view witness) ∧ frame witness
  | .done, _, _, _ => Iff.rfl
  | .public _ _, labels, path, witness =>
      terminalPredicate_pullLabels view frame (labels.2 path.1) path.2 witness
  | .oracle _ _, labels, path, witness =>
      terminalPredicate_pullLabels view frame (labels.2 path.1) path.2 witness

/-- A component's named endpoint law pulls back to the same physical candidate. -/
theorem pull_endpoint {V W A : Type} (protocol : Protocol) (view : W → V) (frame : W → Prop)
    (labels : Retained.Labels V protocol.tree) (output : protocol.tree.ExecutionPath → A)
    (relation : A → V → Prop)
    (endpoint : ∀ fixed path witness,
      ((Retained.extractor fixed labels).terminalState path).holds witness ↔
        Retained.terminalEquiv fixed labels path witness = fixed ∧
          relation (output path) (Retained.terminalEquiv fixed labels path witness)) :
    EndpointLaw protocol (pullLabels view frame labels) output
      (fun claim witness => relation claim (view witness) ∧ frame witness) := by
  intro fixed path witness
  change _ ↔ ListLift.boundTerminalEquiv fixed (pullLabels view frame labels) path witness = fixed ∧ _
  rw [ListLift.bound_terminal_holds, terminalPredicate_pullLabels]
  apply and_congr_right
  intro _
  let value := view (ListLift.boundTerminalEquiv fixed (pullLabels view frame labels) path witness)
  have law := (viewed_terminal_holds value labels path
    ((Retained.terminalEquiv value labels path).symm value)).symm.trans
      (endpoint value path ((Retained.terminalEquiv value labels path).symm value))
  simp only [Equiv.apply_symm_apply, true_and] at law
  exact and_congr_left (fun _ => law)

/-- A physical equality binding transports prover preservation through any total view. -/
theorem pull_retained_preserving {V W : Type} (view : W → V) (frame : W → Prop) (fixed : W) :
    {tree : Oracle.TypeTree} → (labels : Retained.Labels V tree) →
    (roles : tree.RoleDecoration) →
    (Retained.extractor (view fixed) labels).IsProverPreserving roles →
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (pullLabels view frame labels))).IsProverPreserving roles
  | .done, _, _, _ => trivial
  | .public _ _, labels, roles, preserving => by
      refine ⟨?_, fun move => pull_retained_preserving view frame fixed (labels.2 move)
        (roles.2 move) (preserving.2 move)⟩
      intro move sender witness good
      change W at witness
      change witness = fixed ∧ ListLift.input (pullLabels view frame labels) witness
      change ListLift.input (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
        (pullLabels view frame (labels.2 move))) witness at good
      rw [ListLift.input_map, input_pullLabels] at good
      rw [input_pullLabels]
      exact ⟨good.1, (preserving.1 move sender (view witness)
        ⟨congrArg view good.1, good.2.1⟩).2, good.2.2⟩
  | .oracle _ _, labels, roles, preserving => by
      refine ⟨?_, fun message => pull_retained_preserving view frame fixed (labels.2 message)
        (roles.2 PUnit.unit) (preserving.2 message)⟩
      intro message witness good
      change W at witness
      change witness = fixed ∧ ListLift.input (pullLabels view frame labels) witness
      change ListLift.input (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
        (pullLabels view frame (labels.2 message))) witness at good
      rw [ListLift.input_map, input_pullLabels] at good
      rw [input_pullLabels]
      exact ⟨good.1, (preserving.1 message (view witness)
        ⟨congrArg view good.1, good.2.1⟩).2, good.2.2⟩

/-- Every bad pulled-back challenge is bad for the component at the fixed viewed object. -/
theorem pull_bad_subset {V W Moves : Type} (view : W → V) (frame : W → Prop)
    (fixed : W) {next : Moves → Oracle.TypeTree}
    (labels : Retained.Labels V (.public Moves next)) (move : Moves) :
    RoundExtractor.badChallenge (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (pullLabels view frame labels))) move →
      RoundExtractor.badChallenge (Retained.extractor (view fixed) labels) move := by
  rintro ⟨witness, bad, good⟩
  change W at witness
  change ListLift.input (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
    (pullLabels view frame (labels.2 move))) witness at good
  rw [ListLift.input_map] at good
  change ¬ (witness = fixed ∧ ListLift.input (pullLabels view frame labels) witness) at bad
  rw [input_pullLabels] at good bad
  refine ⟨view witness, ?_, congrArg view good.1, good.2.1⟩
  intro known
  exact bad ⟨good.1, known.2, good.2.2⟩

/-- Physical pullback and a fixed frame preserve the component's entire local schedule. -/
theorem pull_retained_bounded {V W : Type} (view : W → V) (frame : W → Prop) (fixed : W) :
    {tree : Oracle.TypeTree} → (labels : Retained.Labels V tree) →
    (roles : tree.RoleDecoration) → (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    (Retained.extractor (view fixed) labels).IsLocallyBounded roles schedule →
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (pullLabels view frame labels))).IsLocallyBounded roles schedule
  | .done, _, _, _, _ => trivial
  | .public _ _, labels, ⟨.sender, roles⟩, schedule, bounded =>
      fun move => pull_retained_bounded view frame fixed (labels.2 move) (roles move)
        (schedule.2 move) (bounded move)
  | .public _ _, labels, ⟨.receiver, roles⟩, schedule, bounded => by
      refine ⟨?_, fun move => pull_retained_bounded view frame fixed (labels.2 move)
        (roles move) (schedule.2 move) (bounded.2 move)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro round context
      exact (prEvent_mono schedule.1.1 _ _ (pull_bad_subset view frame fixed labels)).trans
        ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp bounded.1 round context)
  | .oracle _ _, labels, roles, schedule, bounded =>
      fun message => pull_retained_bounded view frame fixed (labels.2 message) (roles.2 PUnit.unit)
        (schedule message) (bounded message)

/-- The physical equality-bound extractor inherits the component's prover laws. -/
theorem pull_preserving {V W : Type} (view : W → V) (frame : W → Prop) (fixed : W)
    {tree : Oracle.TypeTree} (labels : Retained.Labels V tree) (roles : tree.RoleDecoration)
    (preserving : (Retained.extractor (view fixed) labels).IsProverPreserving roles) :
    (ListLift.boundExtractor fixed (pullLabels view frame labels)).IsProverPreserving roles :=
  RoundExtractor.isProverPreserving_changeInputState
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (pullLabels view frame labels))) (ListLift.bound fixed (ListLift.input (pullLabels view frame labels)))
    (Equiv.refl W)
    (fun witness => by rw [ListLift.input_map]; exact Iff.rfl) roles
    (pull_retained_preserving view frame fixed labels roles preserving)

/-- The physical equality-bound extractor inherits the component's local bounds. -/
theorem pull_bounded {V W : Type} (view : W → V) (frame : W → Prop) (fixed : W)
    {tree : Oracle.TypeTree} (labels : Retained.Labels V tree) (roles : tree.RoleDecoration)
    (schedule : RoundExtractor.ChallengeSchedule tree roles)
    (bounded : (Retained.extractor (view fixed) labels).IsLocallyBounded roles schedule) :
    (ListLift.boundExtractor fixed (pullLabels view frame labels)).IsLocallyBounded roles schedule :=
  RoundExtractor.isLocallyBounded_changeInputState
    (ListLift.retained (ListLift.map (fun predicate witness => witness = fixed ∧ predicate witness)
      (pullLabels view frame labels))) (ListLift.bound fixed (ListLift.input (pullLabels view frame labels)))
    (Equiv.refl W)
    (fun witness => by rw [ListLift.input_map]; exact Iff.rfl) roles schedule
    (pull_retained_bounded view frame fixed labels roles schedule bounded)

end CompStark.Compose
