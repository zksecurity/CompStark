/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition

set_option smartUnfolding false

/-! Finite unions of knowledge certificates. The candidate set is fixed before any challenge. A tagged backward map keeps the candidate's index, including when the candidate carriers differ. The common sampler is an explicit premise; its error is multiplied by the real list bound without integer rounding. -/

@[expose] public section

namespace Interaction.Oracle.Security.ListLift

open Interaction.Oracle PFunctor.FreeM OracleComp

universe w


/-- A finite union with a total carrier, even when the candidate set is empty. Only the predicate restricts the index to the prefix-fixed finite set. -/
def state {I : Type w} (candidates : Finset I) (states : I → KnowledgeState.{w}) :
    KnowledgeState.{w} where
  Witness := (i : I) × (states i).Witness
  holds witness := witness.1 ∈ candidates ∧ (states witness.1).holds witness.2

/-- Lift each backward map through its own candidate, never selecting an index after a challenge. -/
def extractor {I : Type w} (candidates : Finset I) :
    {tree : Oracle.TypeTree} → {states : I → KnowledgeState.{w}} →
    ((i : I) → RoundExtractor tree (states i)) → RoundExtractor tree (state candidates states)
  | .done, _, _ => PUnit.unit
  | .public _ _, _, family => fun move =>
      ⟨state candidates (fun i => (family i move).1),
        (fun witness => ⟨witness.1, (family witness.1 move).2.1 witness.2⟩),
        extractor candidates (fun i => (family i move).2.2)⟩
  | .oracle _ _, _, family => fun message =>
      ⟨state candidates (fun i => (family i message).1),
        (fun witness => ⟨witness.1, (family witness.1 message).2.1 witness.2⟩),
        extractor candidates (fun i => (family i message).2.2)⟩

/-- Keep every sampler and multiply every verifier-node error by the same nonnegative real factor. -/
noncomputable def scale : {tree : Oracle.TypeTree} → (roles : tree.RoleDecoration) →
    ℝ → RoundExtractor.ChallengeSchedule tree roles →
    RoundExtractor.ChallengeSchedule tree roles
  | .done, _, _, _ => PUnit.unit
  | .public _ _, ⟨.sender, roles⟩, L, schedule =>
      ⟨PUnit.unit, fun move => scale (roles move) L (schedule.2 move)⟩
  | .public _ _, ⟨.receiver, roles⟩, L, schedule =>
      ⟨⟨schedule.1.1, ENNReal.ofReal L * schedule.1.2⟩,
        fun move => scale (roles move) L (schedule.2 move)⟩
  | .oracle _ _, roles, L, schedule =>
      fun message => scale (roles.2 PUnit.unit) L (schedule message)

/-- At a fixed prefix a bad union witness belongs to one of the original candidate bad events. -/
theorem badChallenge_subset {I : Type w} (candidates : Finset I)
    {Moves : Type} {next : Moves → Oracle.TypeTree} {states : I → KnowledgeState.{w}}
    (family : (i : I) → RoundExtractor (.public Moves next) (states i)) (move : Moves) :
    RoundExtractor.badChallenge (extractor candidates family) move →
      ∃ i ∈ candidates, RoundExtractor.badChallenge (family i) move := by
  rintro ⟨⟨i, witness⟩, bad, member, good⟩
  exact ⟨i, member, witness, fun known => bad ⟨member, known⟩, good⟩

/-- Candidate-preserving backward maps inherit every prover-message law. -/
theorem extractor_preserving {I : Type w} (candidates : Finset I) :
    {tree : Oracle.TypeTree} → {states : I → KnowledgeState.{w}} →
    (family : (i : I) → RoundExtractor tree (states i)) →
    (roles : tree.RoleDecoration) →
    (∀ i, (family i).IsProverPreserving roles) →
    (extractor candidates family).IsProverPreserving roles
  | .done, _, _, _, _ => trivial
  | .public _ _, _, family, roles, preserving =>
      ⟨fun move sender witness good =>
        ⟨good.1, (preserving witness.1).1 move sender witness.2 good.2⟩,
        fun move => extractor_preserving candidates (fun i => (family i move).2.2)
          (roles.2 move) (fun i => (preserving i).2 move)⟩
  | .oracle _ _, _, family, roles, preserving =>
      ⟨fun message witness good =>
        ⟨good.1, (preserving witness.1).1 message witness.2 good.2⟩,
        fun message => extractor_preserving candidates (fun i => (family i message).2.2)
          (roles.2 PUnit.unit) (fun i => (preserving i).2 message)⟩

/-- The finite union bound uses a small finite index type even when candidate carriers inhabit a larger universe. -/
theorem local_union_bound {I : Type w} (candidates : Finset I) (L : ℝ)
    (card_le : (candidates.card : ℝ) ≤ L)
    {Moves : Type} {next : Moves → Oracle.TypeTree} {states : I → KnowledgeState.{w}}
    (family : (i : I) → RoundExtractor (.public Moves next) (states i))
    (sample : ProbComp Moves) (error : ENNReal)
    (bounded : ∀ i, Pr{let move ← sample}[RoundExtractor.badChallenge (family i) move] ≤ error) :
    Pr{let move ← sample}[RoundExtractor.badChallenge (extractor candidates family) move] ≤
      ENNReal.ofReal L * error := by
  classical
  let index : Fin candidates.card → {i // i ∈ candidates} := candidates.equivFin.symm
  have subset : ∀ move, RoundExtractor.badChallenge (extractor candidates family) move →
      ∃ j : Fin candidates.card, RoundExtractor.badChallenge (family (index j).val) move := by
    intro move bad
    obtain ⟨i, member, bad⟩ := badChallenge_subset candidates family move bad
    refine ⟨candidates.equivFin ⟨i, member⟩, ?_⟩
    change RoundExtractor.badChallenge
      (family ((candidates.equivFin.symm (candidates.equivFin ⟨i, member⟩)).val)) move
    rw [candidates.equivFin.symm_apply_apply]
    exact bad
  have union := prEvent_exists_le_card_mul sample
    (fun j : Fin candidates.card => RoundExtractor.badChallenge (family (index j).val))
    (fun j => bounded (index j).val)
  have count : (candidates.card : ENNReal) ≤ ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal card_le
  have union_bound :
      Pr{let move ← sample}[∃ j : Fin candidates.card,
        RoundExtractor.badChallenge (family (index j).val) move] ≤ candidates.card * error := by
    simpa only [Fintype.card_fin] using union
  exact (prEvent_mono sample _ _ subset).trans
    (union_bound.trans (mul_le_mul' count le_rfl))

/-- Every authored verifier prefix inherits the same sampler and the finite-union local error. -/
theorem extractor_bounded {I : Type w} (candidates : Finset I) (L : ℝ)
    (card_le : (candidates.card : ℝ) ≤ L) :
    {tree : Oracle.TypeTree} → {states : I → KnowledgeState.{w}} →
    (family : (i : I) → RoundExtractor tree (states i)) →
    (roles : tree.RoleDecoration) → (common : RoundExtractor.ChallengeSchedule tree roles) →
    (∀ i, (family i).IsLocallyBounded roles common) →
    (extractor candidates family).IsLocallyBounded roles (scale roles L common)
  | .done, _, _, _, _, _ => trivial
  | .public _ _, _, family, ⟨.sender, roles⟩, common, bounded =>
      fun move => extractor_bounded candidates L card_le (fun i => (family i move).2.2)
        (roles move) (common.2 move) (fun i => bounded i move)
  | .public _ _, _, family, ⟨.receiver, roles⟩, common, bounded => by
      refine ⟨?_, fun move => extractor_bounded candidates L card_le
        (fun i => (family i move).2.2) (roles move) (common.2 move)
        (fun i => (bounded i).2 move)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro round context
      exact local_union_bound candidates L card_le family common.1.1 common.1.2
        (fun i => (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp (bounded i).1 round context)
  | .oracle _ _, _, family, roles, common, bounded =>
      fun message => extractor_bounded candidates L card_le (fun i => (family i message).2.2)
        (roles.2 PUnit.unit) (common message) (fun i => bounded i message)

/-- Generic finite-list composition over arbitrary knowledge certificates with the same authored schedule. Bounds and samplers must agree at every prefix, including unreachable prefixes. -/
noncomputable def certificate {I : Type w} (candidates : Finset I) (L : ℝ)
    (card_le : (candidates.card : ℝ) ≤ L)
    {tree : Oracle.TypeTree} {roles : tree.RoleDecoration} {states : I → KnowledgeState.{w}}
    (family : (i : I) → KnowledgeCertificate tree roles (states i))
    (common : RoundExtractor.ChallengeSchedule tree roles)
    (same : ∀ i, (family i).challenges = common) :
    KnowledgeCertificate tree roles (state candidates states) where
  extractor := extractor candidates (fun i => (family i).extractor)
  challenges := scale roles L common
  prover_preserving := extractor_preserving candidates _ roles (fun i => (family i).prover_preserving)
  local_bound := extractor_bounded candidates L card_le _ roles common
    (fun i => same i ▸ (family i).local_bound)

/-- Change a nonterminal root by a total backward map. Child states and their extractors are retained exactly. -/
def rebaseExtractor {state target : KnowledgeState.{w}} :
    {tree : Oracle.TypeTree} → (tree ≠ .done) → RoundExtractor tree state →
    (state.Witness → target.Witness) → RoundExtractor tree target
  | .done, nonempty, _, _ => False.elim (nonempty rfl)
  | .public _ _, _, original, backward => fun move =>
      ⟨(original move).1, backward ∘ (original move).2.1, (original move).2.2⟩
  | .oracle _ _, _, original, backward => fun message =>
      ⟨(original message).1, backward ∘ (original message).2.1, (original message).2.2⟩

/-- Root rebasing needs only preservation of true knowledge, so it also handles an untagged PCS witness lifting to a candidate-tagged outer endpoint. -/
def rebase {tree : Oracle.TypeTree} {roles : tree.RoleDecoration}
    {state : KnowledgeState.{w}} (original : KnowledgeCertificate tree roles state)
    (nonempty : tree ≠ .done) (target : KnowledgeState.{w})
    (backward : state.Witness → target.Witness)
    (preserves : ∀ witness, state.holds witness → target.holds (backward witness)) :
    KnowledgeCertificate tree roles target where
  extractor := rebaseExtractor nonempty original.extractor backward
  challenges := original.challenges
  prover_preserving := by
    cases tree using Oracle.TypeTree.casesOn with
    | done => exact False.elim (nonempty rfl)
    | «public» Moves next =>
        exact ⟨fun move sender witness good => preserves _
          (original.prover_preserving.1 move sender witness good), original.prover_preserving.2⟩
    | «oracle» Messages next =>
        exact ⟨fun message witness good => preserves _
          (original.prover_preserving.1 message witness good), original.prover_preserving.2⟩
  local_bound := by
    cases tree using Oracle.TypeTree.casesOn with
    | done => exact False.elim (nonempty rfl)
    | «oracle» Messages next => exact original.local_bound
    | «public» Moves next =>
        rcases roles with ⟨role, roles⟩
        cases role with
        | sender => exact original.local_bound
        | receiver =>
            refine ⟨?_, original.local_bound.2⟩
            rw [_root_.RoundByRound.GameFamily.isBounded_iff]
            intro round context
            refine (prEvent_mono original.challenges.1.1 _
              (RoundExtractor.badChallenge original.extractor) ?_).trans
                ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp
                  original.local_bound.1 round context)
            rintro move ⟨witness, bad, good⟩
            exact ⟨witness, fun known => bad (preserves _ known), good⟩

/-- Rebasing a nonterminal root keeps the concrete terminal carrier. -/
def rebaseTerminalEquiv {state target : KnowledgeState.{w}} :
    {tree : Oracle.TypeTree} → (nonempty : tree ≠ .done) →
    (original : RoundExtractor tree state) → (backward : state.Witness → target.Witness) →
    (path : tree.ExecutionPath) →
      ((rebaseExtractor nonempty original backward).terminalState path).Witness ≃
        (original.terminalState path).Witness
  | .done, nonempty, _, _, _ => False.elim (nonempty rfl)
  | .public _ _, _, _, _, _ => Equiv.refl _
  | .oracle _ _, _, _, _, _ => Equiv.refl _

/-- Root rebasing preserves the terminal carrier as an equality of types. -/
theorem rebase_terminal_witness {state target : KnowledgeState.{w}} :
    {tree : Oracle.TypeTree} → (nonempty : tree ≠ .done) →
    (original : RoundExtractor tree state) → (backward : state.Witness → target.Witness) →
    (path : tree.ExecutionPath) →
      ((rebaseExtractor nonempty original backward).terminalState path).Witness =
        (original.terminalState path).Witness
  | .done, nonempty, _, _, _ => False.elim (nonempty rfl)
  | .public _ _, _, _, _, _ => rfl
  | .oracle _ _, _, _, _, _ => rfl

/-- Identify the tagged terminal carrier with the family of actual component terminal carriers. -/
def terminalEquiv {I : Type w} (candidates : Finset I) :
    {tree : Oracle.TypeTree} → {states : I → KnowledgeState.{w}} →
    (family : (i : I) → RoundExtractor tree (states i)) → (path : tree.ExecutionPath) →
    ((extractor candidates family).terminalState path).Witness ≃
      ((i : I) × ((family i).terminalState path).Witness)
  | .done, _, _, _ => Equiv.refl _
  | .public _ _, _, family, path => terminalEquiv candidates
      (fun i => (family i path.1).2.2) path.2
  | .oracle _ _, _, family, path => terminalEquiv candidates
      (fun i => (family i path.1).2.2) path.2

/-- Terminal union knowledge is membership of the retained index together with that component's terminal knowledge. -/
theorem terminal_holds {I : Type w} (candidates : Finset I) :
    {tree : Oracle.TypeTree} → {states : I → KnowledgeState.{w}} →
    (family : (i : I) → RoundExtractor tree (states i)) → (path : tree.ExecutionPath) →
    (witness : ((extractor candidates family).terminalState path).Witness) →
    ((extractor candidates family).terminalState path).holds witness ↔
      (terminalEquiv candidates family path witness).1 ∈ candidates ∧
        ((family (terminalEquiv candidates family path witness).1).terminalState path).holds
          (terminalEquiv candidates family path witness).2
  | .done, _, _, _, _ => Iff.rfl
  | .public _ _, _, family, path, witness =>
      terminal_holds candidates (fun i => (family i path.1).2.2) path.2 witness
  | .oracle _ _, _, family, path, witness =>
      terminal_holds candidates (fun i => (family i path.1).2.2) path.2 witness

/-- Complete-path extraction keeps the original index and applies exactly its component's backward maps. -/
theorem extractWitness_eq {I : Type w} (candidates : Finset I) :
    {tree : Oracle.TypeTree} → {states : I → KnowledgeState.{w}} →
    (family : (i : I) → RoundExtractor tree (states i)) → (path : tree.ExecutionPath) →
    (witness : ((extractor candidates family).terminalState path).Witness) →
    (extractor candidates family).extractWitness path witness =
      ⟨(terminalEquiv candidates family path witness).1,
        (family (terminalEquiv candidates family path witness).1).extractWitness path
          (terminalEquiv candidates family path witness).2⟩
  | .done, _, _, _, _ => rfl
  | .public _ _, states, family, path, witness => by
      change (fun (w : (i : I) × (family i path.1).1.Witness) =>
        (⟨w.1, (family w.1 path.1).2.1 w.2⟩ : (state candidates states).Witness))
        ((extractor candidates (fun i => (family i path.1).2.2)).extractWitness path.2 witness) = _
      rw [extractWitness_eq candidates (fun i => (family i path.1).2.2) path.2 witness]
      rfl
  | .oracle _ _, states, family, path, witness => by
      change (fun (w : (i : I) × (family i path.1).1.Witness) =>
        (⟨w.1, (family w.1 path.1).2.1 w.2⟩ : (state candidates states).Witness))
        ((extractor candidates (fun i => (family i path.1).2.2)).extractWitness path.2 witness) = _
      rw [extractWitness_eq candidates (fun i => (family i path.1).2.2) path.2 witness]
      rfl

/-- Rebasing changes no terminal knowledge predicate. -/
theorem rebase_terminal_holds {state target : KnowledgeState.{w}}
    {tree : Oracle.TypeTree} (nonempty : tree ≠ .done)
    (original : RoundExtractor tree state) (backward : state.Witness → target.Witness)
    (path : tree.ExecutionPath)
    (witness : ((rebaseExtractor nonempty original backward).terminalState path).Witness) :
    ((rebaseExtractor nonempty original backward).terminalState path).holds witness ↔
      (original.terminalState path).holds
        (rebaseTerminalEquiv nonempty original backward path witness) := by
  cases tree using Oracle.TypeTree.casesOn with
  | done => exact False.elim (nonempty rfl)
  | «public» => exact Iff.rfl
  | «oracle» => exact Iff.rfl

/-- Rebasing composes the complete backward extractor with its explicit root map. -/
theorem rebase_extractWitness {state target : KnowledgeState.{w}}
    {tree : Oracle.TypeTree} (nonempty : tree ≠ .done)
    (original : RoundExtractor tree state) (backward : state.Witness → target.Witness)
    (path : tree.ExecutionPath)
    (witness : ((rebaseExtractor nonempty original backward).terminalState path).Witness) :
    (rebaseExtractor nonempty original backward).extractWitness path witness =
      backward (original.extractWitness path
        (rebaseTerminalEquiv nonempty original backward path witness)) := by
  cases tree using Oracle.TypeTree.casesOn with
  | done => exact False.elim (nonempty rfl)
  | «public» => rfl
  | «oracle» => rfl

/-- Conjoin a public prefix-fixed gate to a knowledge state without changing its carrier. -/
def frameState (gate : Prop) (original : KnowledgeState.{w}) : KnowledgeState.{w} :=
  ⟨original.Witness, fun witness => gate ∧ original.holds witness⟩

/-- Frame a public rejection flag through every backward map. -/
def frameExtractor (gate : Prop) : {tree : Oracle.TypeTree} → {state : KnowledgeState.{w}} →
    RoundExtractor tree state → RoundExtractor tree (frameState gate state)
  | .done, _, _ => PUnit.unit
  | .public _ _, _, original => fun move =>
      ⟨frameState gate (original move).1, (original move).2.1,
        frameExtractor gate (original move).2.2⟩
  | .oracle _ _, _, original => fun message =>
      ⟨frameState gate (original message).1, (original message).2.1,
        frameExtractor gate (original message).2.2⟩

/-- A fixed public gate preserves all prover-message implications. -/
theorem frame_preserving (gate : Prop) :
    {tree : Oracle.TypeTree} → {state : KnowledgeState.{w}} →
    (original : RoundExtractor tree state) → (roles : tree.RoleDecoration) →
    original.IsProverPreserving roles → (frameExtractor gate original).IsProverPreserving roles
  | .done, _, _, _, _ => trivial
  | .public _ _, _, original, roles, preserving =>
      ⟨fun move sender witness good => ⟨good.1, preserving.1 move sender witness good.2⟩,
        fun move => frame_preserving gate (original move).2.2 (roles.2 move) (preserving.2 move)⟩
  | .oracle _ _, _, original, roles, preserving =>
      ⟨fun message witness good => ⟨good.1, preserving.1 message witness good.2⟩,
        fun message => frame_preserving gate (original message).2.2
          (roles.2 PUnit.unit) (preserving.2 message)⟩

/-- A framed bad challenge is already bad for the unframed certificate. -/
theorem frame_bad_subset (gate : Prop) {Moves : Type} {next : Moves → Oracle.TypeTree}
    {state : KnowledgeState.{w}} (original : RoundExtractor (.public Moves next) state)
    (move : Moves) : RoundExtractor.badChallenge (frameExtractor gate original) move →
      RoundExtractor.badChallenge original move := by
  rintro ⟨witness, bad, gate_holds, good⟩
  exact ⟨witness, fun known => bad ⟨gate_holds, known⟩, good⟩

/-- Framing changes neither samplers nor local errors at any authored prefix. -/
theorem frame_bounded (gate : Prop) :
    {tree : Oracle.TypeTree} → {state : KnowledgeState.{w}} →
    (original : RoundExtractor tree state) → (roles : tree.RoleDecoration) →
    (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    original.IsLocallyBounded roles schedule →
      (frameExtractor gate original).IsLocallyBounded roles schedule
  | .done, _, _, _, _, _ => trivial
  | .public _ _, _, original, ⟨.sender, roles⟩, schedule, bounded =>
      fun move => frame_bounded gate (original move).2.2 (roles move) (schedule.2 move) (bounded move)
  | .public _ _, _, original, ⟨.receiver, roles⟩, schedule, bounded => by
      refine ⟨?_, fun move => frame_bounded gate (original move).2.2
        (roles move) (schedule.2 move) (bounded.2 move)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro round context
      exact (prEvent_mono schedule.1.1 _ _ (frame_bad_subset gate original)).trans
        ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp bounded.1 round context)
  | .oracle _ _, _, original, roles, schedule, bounded =>
      fun message => frame_bounded gate (original message).2.2 (roles.2 PUnit.unit)
        (schedule message) (bounded message)

/-- A prefix-fixed public gate introduces no additional challenge error. -/
def frame {tree : Oracle.TypeTree} {roles : tree.RoleDecoration} {state : KnowledgeState.{w}}
    (original : KnowledgeCertificate tree roles state) (gate : Prop) :
    KnowledgeCertificate tree roles (frameState gate state) where
  extractor := frameExtractor gate original.extractor
  challenges := original.challenges
  prover_preserving := frame_preserving gate _ roles original.prover_preserving
  local_bound := frame_bounded gate _ roles original.challenges original.local_bound

/-- Framing identifies the actual terminal carrier with the original carrier by identity at every step. -/
def frameTerminalEquiv (gate : Prop) :
    {tree : Oracle.TypeTree} → {state : KnowledgeState.{w}} →
    (original : RoundExtractor tree state) → (path : tree.ExecutionPath) →
    ((frameExtractor gate original).terminalState path).Witness ≃
      (original.terminalState path).Witness
  | .done, _, _, _ => Equiv.refl _
  | .public _ _, _, original, path => frameTerminalEquiv gate (original path.1).2.2 path.2
  | .oracle _ _, _, original, path => frameTerminalEquiv gate (original path.1).2.2 path.2

/-- Framing preserves the terminal carrier as an equality of types. -/
theorem frame_terminal_witness (gate : Prop) :
    {tree : Oracle.TypeTree} → {state : KnowledgeState.{w}} →
    (original : RoundExtractor tree state) → (path : tree.ExecutionPath) →
    ((frameExtractor gate original).terminalState path).Witness =
      (original.terminalState path).Witness
  | .done, _, _, _ => rfl
  | .public _ _, _, original, path => frame_terminal_witness gate (original path.1).2.2 path.2
  | .oracle _ _, _, original, path => frame_terminal_witness gate (original path.1).2.2 path.2

/-- The public frame remains a conjunct of the terminal knowledge predicate. -/
theorem frame_terminal_holds (gate : Prop) :
    {tree : Oracle.TypeTree} → {state : KnowledgeState.{w}} →
    (original : RoundExtractor tree state) → (path : tree.ExecutionPath) →
    (witness : ((frameExtractor gate original).terminalState path).Witness) →
    ((frameExtractor gate original).terminalState path).holds witness ↔
      gate ∧ (original.terminalState path).holds (frameTerminalEquiv gate original path witness)
  | .done, _, _, _, _ => Iff.rfl
  | .public _ _, _, original, path, witness =>
      frame_terminal_holds gate (original path.1).2.2 path.2 witness
  | .oracle _ _, _, original, path, witness =>
      frame_terminal_holds gate (original path.1).2.2 path.2 witness

/-- Framing preserves the complete backward witness map. -/
theorem frame_extractWitness (gate : Prop) :
    {tree : Oracle.TypeTree} → {state : KnowledgeState.{w}} →
    (original : RoundExtractor tree state) → (path : tree.ExecutionPath) →
    (witness : ((frameExtractor gate original).terminalState path).Witness) →
    (frameExtractor gate original).extractWitness path witness =
      original.extractWitness path (frameTerminalEquiv gate original path witness)
  | .done, _, _, _, _ => rfl
  | .public _ _, _, original, path, witness =>
      congrArg (original path.1).2.1
        (frame_extractWitness gate (original path.1).2.2 path.2 witness)
  | .oracle _ _, _, original, path, witness =>
      congrArg (original path.1).2.1
        (frame_extractWitness gate (original path.1).2.2 path.2 witness)

/-- Predicates on a common retained carrier at all authored public and oracle prefixes. -/
def Labels (W : Type) : Oracle.TypeTree → Type
  | .done => W → Prop
  | .public M next => (W → Prop) × ((move : M) → Labels W (next move))
  | .oracle M next => (W → Prop) × (M → Labels W (next PUnit.unit))

/-- The predicate at the root of an authored retained-carrier tree. -/
def input {W : Type} : {tree : Oracle.TypeTree} → Labels W tree → W → Prop
  | .done, labels => labels
  | .public _ _, labels => labels.1
  | .oracle _ _, labels => labels.1

/-- Apply one predicate transformation at every prefix. -/
def map {W : Type} (f : (W → Prop) → W → Prop) :
    {tree : Oracle.TypeTree} → Labels W tree → Labels W tree
  | .done, labels => f labels
  | .public _ _, labels => ⟨f labels.1, fun move => map f (labels.2 move)⟩
  | .oracle _ _, labels => ⟨f labels.1, fun message => map f (labels.2 message)⟩

/-- Identity backward maps on a common carrier with independently specified prefix predicates. -/
def retained {W : Type} : {tree : Oracle.TypeTree} → (labels : Labels W tree) →
    RoundExtractor tree ⟨W, input labels⟩
  | .done, _ => PUnit.unit
  | .public _ _, labels => fun move =>
      ⟨⟨W, input (labels.2 move)⟩, id, retained (labels.2 move)⟩
  | .oracle _ _, labels => fun message =>
      ⟨⟨W, input (labels.2 message)⟩, id, retained (labels.2 message)⟩

/-- Delay predicate decoration so erased labels are never traversed by the identity maps. -/
def retainedDelayed {W : Type} : {tree : Oracle.TypeTree} →
    (labels : Unit → Labels W tree) → RoundExtractor tree ⟨W, input (labels ())⟩
  | .done, _ => PUnit.unit
  | .public _ _, labels => fun move =>
      ⟨⟨W, input ((labels ()).2 move)⟩, id,
        retainedDelayed (fun _ => (labels ()).2 move)⟩
  | .oracle _ _, labels => fun message =>
      ⟨⟨W, input ((labels ()).2 message)⟩, id,
        retainedDelayed (fun _ => (labels ()).2 message)⟩

/-- Delayed predicate decoration preserves every retained state and backward map. -/
theorem retainedDelayed_eq {W : Type} : {tree : Oracle.TypeTree} →
    (labels : Unit → Labels W tree) → retainedDelayed labels = retained (labels ())
  | .done, _ => rfl
  | .public _ next, labels => by
    funext move
    exact congrArg (fun rest : RoundExtractor (next move) ⟨W, input ((labels ()).2 move)⟩ =>
      (⟨⟨W, input ((labels ()).2 move)⟩, id, rest⟩ :
        (after : KnowledgeState) × ((after.Witness → W) × RoundExtractor (next move) after)))
      (retainedDelayed_eq (fun _ => (labels ()).2 move))
  | .oracle _ next, labels => by
    funext message
    exact congrArg (fun rest : RoundExtractor (next PUnit.unit) ⟨W, input ((labels ()).2 message)⟩ =>
      (⟨⟨W, input ((labels ()).2 message)⟩, id, rest⟩ :
        (after : KnowledgeState) × ((after.Witness → W) × RoundExtractor (next PUnit.unit) after)))
      (retainedDelayed_eq (fun _ => (labels ()).2 message))

/-- Runtime retained maps do not evaluate their proof-only predicate decoration. -/
def retainedCode {W : Type} {tree : Oracle.TypeTree} (labels : Labels W tree) :
    RoundExtractor tree ⟨W, input labels⟩ := retainedDelayed (fun _ => labels)

/-- The delayed implementation is the exact retained extractor. -/
@[csimp] theorem retained_code : @retained = @retainedCode := by
  funext W tree labels
  exact (retainedDelayed_eq (fun _ => labels)).symm

/-- An equality-bound retained state. -/
def bound {W : Type} (fixed : W) (predicate : W → Prop) : KnowledgeState :=
  ⟨W, fun witness => witness = fixed ∧ predicate witness⟩

/-- The identity extractor for an equality-bound candidate. -/
def boundExtractor {W : Type} (fixed : W) {tree : Oracle.TypeTree} (labels : Labels W tree) :
    RoundExtractor tree (bound fixed (input labels)) :=
  (retained (map (fun predicate witness => witness = fixed ∧ predicate witness) labels)).changeInputState
    (bound fixed (input labels)) (Equiv.refl W)

/-- The predicate reached by the actual public messages and oracle payloads. -/
def terminalPredicate {W : Type} : {tree : Oracle.TypeTree} →
    Labels W tree → tree.ExecutionPath → W → Prop
  | .done, labels, _ => labels
  | .public _ _, labels, path => terminalPredicate (labels.2 path.1) path.2
  | .oracle _ _, labels, path => terminalPredicate (labels.2 path.1) path.2

/-- Retained terminal carriers are identified by identity at every authored step. -/
def retainedTerminalEquiv {W : Type} : {tree : Oracle.TypeTree} → (labels : Labels W tree) →
    (path : tree.ExecutionPath) → ((retained labels).terminalState path).Witness ≃ W
  | .done, _, _ => Equiv.refl W
  | .public _ _, labels, path => retainedTerminalEquiv (labels.2 path.1) path.2
  | .oracle _ _, labels, path => retainedTerminalEquiv (labels.2 path.1) path.2

/-- Every terminal retained carrier is the original carrier, independently of its predicates. -/
theorem retained_terminal_witness {W : Type} : {tree : Oracle.TypeTree} →
    (labels : Labels W tree) → (path : tree.ExecutionPath) →
    ((retained labels).terminalState path).Witness = W
  | .done, _, _ => rfl
  | .public _ _, labels, path => retained_terminal_witness (labels.2 path.1) path.2
  | .oracle _ _, labels, path => retained_terminal_witness (labels.2 path.1) path.2

/-- Identify retained carriers by a proof-only cast without evaluating prefix predicates. -/
def retainedTerminalCast {W : Type} {tree : Oracle.TypeTree} (labels : Labels W tree)
    (path : tree.ExecutionPath) : ((retained labels).terminalState path).Witness ≃ W :=
  Equiv.cast (retained_terminal_witness labels path)

/-- The cast implements the exact retained terminal equivalence. -/
@[csimp] theorem retainedTerminalEquiv_code : @retainedTerminalEquiv = @retainedTerminalCast := by
  funext W tree
  induction tree with
  | done => rfl
  | «public» M next ih =>
    funext labels path
    exact congrFun (congrFun (ih path.1) (labels.2 path.1)) path.2
  | «oracle» M next ih =>
    funext labels path
    exact congrFun (congrFun ih (labels.2 path.1)) path.2

/-- The retained terminal predicate is the predicate selected by the actual path. -/
theorem retained_terminal_holds {W : Type} : {tree : Oracle.TypeTree} →
    (labels : Labels W tree) → (path : tree.ExecutionPath) →
    (witness : ((retained labels).terminalState path).Witness) →
    ((retained labels).terminalState path).holds witness ↔
      terminalPredicate labels path (retainedTerminalEquiv labels path witness)
  | .done, _, _, _ => Iff.rfl
  | .public _ _, labels, path, witness => retained_terminal_holds (labels.2 path.1) path.2 witness
  | .oracle _ _, labels, path, witness => retained_terminal_holds (labels.2 path.1) path.2 witness

/-- All retained backward maps preserve the exact terminal object. -/
theorem retained_extractWitness {W : Type} : {tree : Oracle.TypeTree} →
    (labels : Labels W tree) → (path : tree.ExecutionPath) →
    (witness : ((retained labels).terminalState path).Witness) →
    (retained labels).extractWitness path witness = retainedTerminalEquiv labels path witness
  | .done, _, _, _ => rfl
  | .public _ _, labels, path, witness => retained_extractWitness (labels.2 path.1) path.2 witness
  | .oracle _ _, labels, path, witness => retained_extractWitness (labels.2 path.1) path.2 witness

/-- Mapping predicates commutes with selecting the root predicate. -/
theorem input_map {W : Type} (f : (W → Prop) → W → Prop)
    {tree : Oracle.TypeTree} (labels : Labels W tree) : input (map f labels) = f (input labels) := by
  cases tree using Oracle.TypeTree.casesOn <;> rfl

/-- Mapping predicates commutes with selecting the terminal predicate. -/
theorem terminalPredicate_map {W : Type} (f : (W → Prop) → W → Prop) :
    {tree : Oracle.TypeTree} → (labels : Labels W tree) → (path : tree.ExecutionPath) →
    terminalPredicate (map f labels) path = f (terminalPredicate labels path)
  | .done, _, _ => rfl
  | .public _ _, labels, path => terminalPredicate_map f (labels.2 path.1) path.2
  | .oracle _ _, labels, path => terminalPredicate_map f (labels.2 path.1) path.2

/-- Canonical carrier identification for the equality-bound retained extractor. -/
def boundTerminalEquiv {W : Type} (fixed : W) {tree : Oracle.TypeTree}
    (labels : Labels W tree) (path : tree.ExecutionPath) :
    ((boundExtractor fixed labels).terminalState path).Witness ≃ W :=
  (RoundExtractor.terminalWitnessEquiv
    (retained (map (fun predicate witness => witness = fixed ∧ predicate witness) labels))
    (bound fixed (input labels)) (Equiv.refl W) path).trans (retainedTerminalEquiv _ path)

/-- Equality binding remains conjoined to the actual terminal predicate. -/
theorem bound_terminal_holds {W : Type} (fixed : W) {tree : Oracle.TypeTree}
    (labels : Labels W tree) (path : tree.ExecutionPath)
    (witness : ((boundExtractor fixed labels).terminalState path).Witness) :
    ((boundExtractor fixed labels).terminalState path).holds witness ↔
      boundTerminalEquiv fixed labels path witness = fixed ∧
        terminalPredicate labels path (boundTerminalEquiv fixed labels path witness) := by
  exact (RoundExtractor.terminalKnowledge_changeInputState
    (retained (map (fun predicate witness => witness = fixed ∧ predicate witness) labels))
    (bound fixed (input labels)) (Equiv.refl W)
    (fun witness => by rw [input_map]; exact Iff.rfl) path witness).trans
    ((retained_terminal_holds _ path _).trans (by rw [terminalPredicate_map]; exact Iff.rfl))

/-- Equality binding changes no complete backward map. -/
theorem bound_extractWitness {W : Type} (fixed : W) {tree : Oracle.TypeTree}
    (labels : Labels W tree) (path : tree.ExecutionPath)
    (witness : ((boundExtractor fixed labels).terminalState path).Witness) :
    (boundExtractor fixed labels).extractWitness path witness =
      boundTerminalEquiv fixed labels path witness :=
  (RoundExtractor.extractWitness_changeInputState
    (retained (map (fun predicate witness => witness = fixed ∧ predicate witness) labels))
    (bound fixed (input labels)) (Equiv.refl W) path witness).trans
    (retained_extractWitness _ path _)

/-- The actual appended path ends in the suffix selected by its concrete split. -/
theorem append_terminalState {tree : Oracle.TypeTree} {state : KnowledgeState.{w}}
    (first : RoundExtractor tree state) (suffix : tree.BranchPath → Oracle.TypeTree)
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (first.terminalState path))
    (full : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) :
    (first.append suffix second).terminalState full =
      ((second (PathAlong.split TypeTree.runtimeLens tree suffix full).1).terminalState
        (PathAlong.split TypeTree.runtimeLens tree suffix full).2) :=
  (congrArg (first.append suffix second).terminalState
    (PathAlong.append_split TypeTree.runtimeLens tree suffix full).symm).trans
      (RoundExtractor.terminalState_append first suffix second _ _)

/-- The appended terminal carrier is the concrete suffix terminal carrier, with its named transport. -/
def appendTerminalEquiv {tree : Oracle.TypeTree} {state : KnowledgeState.{w}}
    (first : RoundExtractor tree state) (suffix : tree.BranchPath → Oracle.TypeTree)
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (first.terminalState path))
    (full : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) :
    ((first.append suffix second).terminalState full).Witness ≃
      ((second (PathAlong.split TypeTree.runtimeLens tree suffix full).1).terminalState
        (PathAlong.split TypeTree.runtimeLens tree suffix full).2).Witness :=
  Equiv.cast (congrArg KnowledgeState.Witness (append_terminalState first suffix second full))

/-- Appending keeps exactly the terminal knowledge of the actual suffix. -/
theorem append_terminal_holds {tree : Oracle.TypeTree} {state : KnowledgeState.{w}}
    (first : RoundExtractor tree state) (suffix : tree.BranchPath → Oracle.TypeTree)
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (first.terminalState path))
    (full : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix))
    (witness : ((first.append suffix second).terminalState full).Witness) :
    ((first.append suffix second).terminalState full).holds witness ↔
      ((second (PathAlong.split TypeTree.runtimeLens tree suffix full).1).terminalState
        (PathAlong.split TypeTree.runtimeLens tree suffix full).2).holds
          (appendTerminalEquiv first suffix second full witness) := by
  have law (a b : KnowledgeState.{w}) (equal : a = b) (value : a.Witness) :
      a.holds value ↔ b.holds (cast (congrArg KnowledgeState.Witness equal) value) := by
    cases equal
    exact Iff.rfl
  exact law _ _ (append_terminalState first suffix second full) witness

/-- Reindexing an actual path transports its supplied witness without changing extraction. -/
theorem extractWitness_cast_path {tree : Oracle.TypeTree} {state : KnowledgeState.{w}}
    (extractor : RoundExtractor tree state) (path other : tree.ExecutionPath) (equal : path = other)
    (witness : (extractor.terminalState path).Witness) :
    extractor.extractWitness other
      (cast (congrArg (fun p => (extractor.terminalState p).Witness) equal) witness) =
        extractor.extractWitness path witness := by
  cases equal
  rfl

/-- The complete extractor on a split appended path applies exactly the suffix and then the prefix maps. -/
theorem append_extractWitness {tree : Oracle.TypeTree} {state : KnowledgeState.{w}}
    (first : RoundExtractor tree state) (suffix : tree.BranchPath → Oracle.TypeTree)
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (first.terminalState path))
    (full : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix))
    (witness : ((first.append suffix second).terminalState full).Witness) :
    (first.append suffix second).extractWitness full witness =
      first.extractWitness (PathAlong.split TypeTree.runtimeLens tree suffix full).1
        ((second (PathAlong.split TypeTree.runtimeLens tree suffix full).1).extractWitness
          (PathAlong.split TypeTree.runtimeLens tree suffix full).2
          (appendTerminalEquiv first suffix second full witness)) := by
  let parts := PathAlong.split TypeTree.runtimeLens tree suffix full
  have joined := PathAlong.append_split TypeTree.runtimeLens tree suffix full
  have law := RoundExtractor.extractWitness_append first suffix second parts.1 parts.2
    (appendTerminalEquiv first suffix second full witness)
  have cast_equal :
      (RoundExtractor.terminalState_append first suffix second parts.1 parts.2).symm ▸
        (appendTerminalEquiv first suffix second full witness) =
      cast (congrArg (fun p => ((first.append suffix second).terminalState p).Witness)
        joined.symm) witness := by
    simp only [appendTerminalEquiv, Equiv.cast_apply, eqRec_eq_cast, cast_cast]
  rw [cast_equal, extractWitness_cast_path _ _ _ joined.symm] at law
  exact law

/-- A framed terminal witness exists exactly when its public gate and original terminal knowledge hold. -/
theorem exists_frame_terminal_iff (gate : Prop) {tree : Oracle.TypeTree} {state : KnowledgeState.{w}}
    (original : RoundExtractor tree state) (path : tree.ExecutionPath) :
    (∃ witness, ((frameExtractor gate original).terminalState path).holds witness) ↔
      gate ∧ ∃ witness, (original.terminalState path).holds witness := by
  constructor
  · rintro ⟨witness, good⟩
    have known := (frame_terminal_holds gate original path witness).mp good
    exact ⟨known.1, frameTerminalEquiv gate original path witness, known.2⟩
  · rintro ⟨gate_holds, witness, good⟩
    refine ⟨(frameTerminalEquiv gate original path).symm witness, ?_⟩
    exact (frame_terminal_holds gate original path _).mpr
      ⟨gate_holds, by simpa only [Equiv.apply_symm_apply] using good⟩

/-- Rebasing a nonterminal root preserves existence of terminal knowledge. -/
theorem exists_rebase_terminal_iff {tree : Oracle.TypeTree} {state target : KnowledgeState.{w}}
    (nonempty : tree ≠ .done) (original : RoundExtractor tree state)
    (backward : state.Witness → target.Witness) (path : tree.ExecutionPath) :
    (∃ witness, ((rebaseExtractor nonempty original backward).terminalState path).holds witness) ↔
      ∃ witness, (original.terminalState path).holds witness := by
  constructor
  · rintro ⟨witness, good⟩
    exact ⟨rebaseTerminalEquiv nonempty original backward path witness,
      (rebase_terminal_holds nonempty original backward path witness).mp good⟩
  · rintro ⟨witness, good⟩
    refine ⟨(rebaseTerminalEquiv nonempty original backward path).symm witness, ?_⟩
    exact (rebase_terminal_holds nonempty original backward path _).mpr
      (by simpa only [Equiv.apply_symm_apply] using good)

/-- Appended terminal knowledge exists exactly at the actual suffix endpoint. -/
theorem exists_append_terminal_iff {tree : Oracle.TypeTree} {state : KnowledgeState.{w}}
    (first : RoundExtractor tree state) (suffix : tree.BranchPath → Oracle.TypeTree)
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (first.terminalState path))
    (full : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) :
    (∃ witness, ((first.append suffix second).terminalState full).holds witness) ↔
      ∃ witness, ((second (PathAlong.split TypeTree.runtimeLens tree suffix full).1).terminalState
        (PathAlong.split TypeTree.runtimeLens tree suffix full).2).holds witness := by
  rw [append_terminalState]

/-- A fresh evaluation separates every pair in a prefix-fixed list only outside the pair-collision event. An answer chosen after the point does not single out a reference candidate. -/
def PairCollision {W Point Value : Type} (candidates : Finset W)
    (evaluate : W → Point → Value) (point : Point) : Prop :=
  ∃ f ∈ candidates, ∃ g ∈ candidates, f ≠ g ∧ evaluate f point = evaluate g point

/-- Outside pair collision, any claimed value is consistent with at most one candidate. -/
theorem atMostOne_of_no_pairCollision {W Point Value : Type} (candidates : Finset W)
    (evaluate : W → Point → Value) (point : Point) (value : Value)
    (separated : ¬ PairCollision candidates evaluate point) :
    ∀ f ∈ candidates, ∀ g ∈ candidates,
      evaluate f point = value → evaluate g point = value → f = g := by
  intro f hf g hg hfv hgv
  by_contra different
  exact separated ⟨f, hf, g, hg, different, hfv.trans hgv.symm⟩

end Interaction.Oracle.Security.ListLift
