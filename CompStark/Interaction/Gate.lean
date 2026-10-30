/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Interaction.Oracle.Security.KnowledgeSoundness

/-! # Gating a knowledge certificate by a proposition

A verifier that checks a condition `c` decided before an interaction, and accepts only if `c`
holds and the interaction accepts, has the interaction's knowledge certificate with every state
conjoined with `c` (`KnowledgeCertificate.gate`): the same witness maps, the same challenge
programs and errors. A conjoined later state holding forces `c`, so a bad challenge of the gated
certificate is a bad challenge of the original, and no prover message can make `c` true.
-/

@[expose] public section
namespace CompStark.Interaction
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp
open OracleSpec

/-- A knowledge state conjoined with `c`: the same witnesses, holding when `c` holds and they
hold. -/
def gateState (c : Prop) (state : KnowledgeState) : KnowledgeState :=
  ⟨state.Witness, fun w ↦ c ∧ state.holds w⟩

/-- The witness maps of an extractor, between the states conjoined with `c`. -/
def gateExtractor (c : Prop) : {tree : Oracle.TypeTree} → {state : KnowledgeState} →
    RoundExtractor tree state → RoundExtractor tree (gateState c state)
  | .done, _, _ => PUnit.unit
  | .public _ _, _, extractor => fun move ↦
      ⟨gateState c (extractor move).1, (extractor move).2.1,
        gateExtractor c (extractor move).2.2⟩
  | .oracle _ _, _, extractor => fun message ↦
      ⟨gateState c (extractor message).1, (extractor message).2.1,
        gateExtractor c (extractor message).2.2⟩

/-- The terminal state of a gated extractor is the gated terminal state. -/
theorem terminalState_gateExtractor (c : Prop) : {tree : Oracle.TypeTree} →
    {state : KnowledgeState} → (extractor : RoundExtractor tree state) →
    (path : tree.ExecutionPath) →
    (gateExtractor c extractor).terminalState path = gateState c (extractor.terminalState path)
  | .done, _, _, _ => rfl
  | .public _ _, _, extractor, path =>
      terminalState_gateExtractor c (extractor path.1).2.2 path.2
  | .oracle _ _, _, extractor, path =>
      terminalState_gateExtractor c (extractor path.1).2.2 path.2

/-- Prover messages preserve the gated states. -/
theorem isProverPreserving_gateExtractor (c : Prop) : {tree : Oracle.TypeTree} →
    {state : KnowledgeState} → (extractor : RoundExtractor tree state) →
    (roles : tree.RoleDecoration) → extractor.IsProverPreserving roles →
    (gateExtractor c extractor).IsProverPreserving roles
  | .done, _, _, _, _ => trivial
  | .public _ _, _, extractor, roles, preserving =>
      ⟨fun move sender w h ↦ ⟨h.1, preserving.1 move sender w h.2⟩, fun move ↦
        isProverPreserving_gateExtractor c (extractor move).2.2 (roles.2 move) (preserving.2 move)⟩
  | .oracle _ _, _, extractor, roles, preserving =>
      ⟨fun message w h ↦ ⟨h.1, preserving.1 message w h.2⟩, fun message ↦
        isProverPreserving_gateExtractor c (extractor message).2.2 (roles.2 PUnit.unit)
          (preserving.2 message)⟩

/-- A bad challenge of the gated extractor is a bad challenge of the original. -/
theorem badChallenge_gateExtractor (c : Prop) {Moves : Type} {next : Moves → Oracle.TypeTree}
    {state : KnowledgeState} (extractor : RoundExtractor (.public Moves next) state)
    (challenge : Moves) (h : (gateExtractor c extractor).badChallenge challenge) :
    extractor.badChallenge challenge := by
  obtain ⟨w, hnot, hc, hw⟩ := h
  exact ⟨w, fun hs ↦ hnot ⟨hc, hs⟩, hw⟩

/-- The gated extractor keeps every local bound. -/
theorem isLocallyBounded_gateExtractor (c : Prop) : {tree : Oracle.TypeTree} →
    {state : KnowledgeState} → (extractor : RoundExtractor tree state) →
    (roles : tree.RoleDecoration) → (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    extractor.IsLocallyBounded roles schedule →
    (gateExtractor c extractor).IsLocallyBounded roles schedule
  | .done, _, _, _, _, _ => trivial
  | .public _ _, _, extractor, ⟨.sender, roles⟩, schedule, bounded => fun move ↦
      isLocallyBounded_gateExtractor c (extractor move).2.2 (roles move) (schedule.2 move)
        (bounded move)
  | .public _ _, _, extractor, ⟨.receiver, roles⟩, schedule, bounded => by
      refine ⟨?_, fun move ↦ isLocallyBounded_gateExtractor c (extractor move).2.2 (roles move)
        (schedule.2 move) (bounded.2 move)⟩
      have hb := (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp bounded.1
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro round context
      exact (prEvent_mono _ _ _ fun challenge h ↦ badChallenge_gateExtractor c extractor
        challenge h).trans (hb round context)
  | .oracle _ _, _, extractor, roles, schedule, bounded => fun message ↦
      isLocallyBounded_gateExtractor c (extractor message).2.2 (roles.2 PUnit.unit)
        (schedule message) (bounded message)

/-- **A gated knowledge certificate.** Every state conjoined with `c`, with the same witness maps,
challenge programs and errors. -/
def gateCertificate (c : Prop) {tree : Oracle.TypeTree} {roles : tree.RoleDecoration}
    {state : KnowledgeState} (certificate : KnowledgeCertificate tree roles state) :
    KnowledgeCertificate tree roles (gateState c state) where
  extractor := gateExtractor c certificate.extractor
  challenges := certificate.challenges
  prover_preserving := isProverPreserving_gateExtractor c _ roles certificate.prover_preserving
  local_bound := isLocallyBounded_gateExtractor c _ roles _ certificate.local_bound

end CompStark.Interaction
