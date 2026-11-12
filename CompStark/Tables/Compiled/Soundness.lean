/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Count
public import CompStark.Compiled.WhirTerminal
public import ArkLib.Interaction.Oracle.Security.Recursion

/-! Standard-model knowledge soundness of the composed system compiled with Keccak Merkle roots and
the Keccak duplex: against every adversary, the probability that a proof verifies while the
extracted stack fails the composed input relation is at most the Merkle extractor's node failures
plus, for each of the `count` draws, the correlation-intractability failure of the challenge table
at that draw (`knowledgeSoundness`). -/

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
open StandardBcs StateRestoration
open MixedMerkleTree.Knowledge (ExtractorMap NodeAdversary nodeFail)
open scoped ENNReal

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- The compiled certificate: the composed certificate pulled back along the presentation. -/
noncomputable def certificate (params : Parameters S L k M) :=
  (presentation params).certificate (Composed.certificate params.toParameters)

/-- The ideal execution selected by the same-coins Merkle word extractor. -/
def extractedPath (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest) (c : Coins) :=
  StandardBcs.extractedPath (coin params) (A c).2.1 (messages params A X c)

/-- The composed terminal carrier is WHIR's singleton closing carrier. -/
noncomputable def originalTerminalEquiv (params : Parameters S L k M)
    (path : (Composed.protocol params.toParameters).tree.ExecutionPath) :
    ((Composed.certificate params.toParameters).extractor.terminalState path).Witness ≃ PUnit.{1} :=
  let parts := executionParts params.toParameters path
  let out := (outerReduction params.toSetup params.reductions).output parts.1
  (ListLift.appendTerminalEquiv (outerCertificate params.toParameters path.1).extractor
    (fun _ => (Whir.opening E params.schedule).tree)
    (fun outer => (openingCertificate params.toParameters path.1 outer).extractor) path.2).trans
    ((ListLift.rebaseTerminalEquiv (opening_ne_done params.schedule)
      (framedWhir params.toParameters path.1 out).extractor
      (fun q => (outerTerminalEquiv params.toParameters path.1 parts.1).symm (q, q)) parts.2).trans
    ((ListLift.frameTerminalEquiv _
      (Whir.openingExtractor (algebraMap K E) params.schedule
        (Whir.proximityFamily (algebraMap K E) params.schedule params.security)
        (Whir.openingState (algebraMap K E) params.schedule params.security path.1
          (openingClaims params.toSetup out)).holds params.decoders path.1
        (openingClaims params.toSetup out) params.decoder) parts.2).trans
    ((Equiv.cast (congrArg KnowledgeState.Witness (Whir.openingExtractor_terminalState
      (algebraMap K E) params.schedule params.security params.decoders path.1
      (openingClaims params.toSetup out) params.decoder parts.2))).trans
    (Equiv.cast (level_witness params.schedule
      (Whir.proximityFamily (algebraMap K E) params.schedule params.security) params.decoders _ _ true
      parts.2)))))

/-- The composed terminal predicate holds at some witness exactly when the verifier accepts. -/
theorem original_terminal_iff (params : Parameters S L k M)
    (path : (Composed.protocol params.toParameters).tree.ExecutionPath) :
    (∃ witness, ((Composed.certificate params.toParameters).extractor.terminalState path).holds witness) ↔
      Accepts params.toParameters path := by
  refine ⟨fun ⟨witness, known⟩ ↦ ?_, accepts_terminal params.toParameters path⟩
  change ((committedCertificate params.toParameters path.1).extractor.terminalState path.2).holds witness at known
  have known' := (ListLift.exists_append_terminal_iff (outerCertificate params.toParameters path.1).extractor
    (fun _ => (Whir.opening E params.schedule).tree)
    (fun outer => (openingCertificate params.toParameters path.1 outer).extractor) path.2).mp ⟨witness, known⟩
  change ∃ witness, ((openingCertificate params.toParameters path.1
    (executionParts params.toParameters path).1).extractor.terminalState
    (executionParts params.toParameters path).2).holds witness at known'
  have known'' := (ListLift.exists_rebase_terminal_iff (opening_ne_done params.schedule)
    (framedWhir params.toParameters path.1 ((outerReduction params.toSetup params.reductions).output
      (executionParts params.toParameters path).1)).extractor
    (fun q => (outerTerminalEquiv params.toParameters path.1 (executionParts params.toParameters path).1).symm (q, q))
    (executionParts params.toParameters path).2).mp known'
  obtain ⟨gate, whir⟩ := (ListLift.exists_frame_terminal_iff _ _ (executionParts params.toParameters path).2).mp known''
  refine ⟨gate, ?_⟩
  obtain ⟨w, holds⟩ := whir
  change ((Whir.openingExtractor (algebraMap K E) params.schedule
    (Whir.proximityFamily (algebraMap K E) params.schedule params.security)
    (Whir.openingState (algebraMap K E) params.schedule params.security path.1 _).holds
    params.decoders path.1 _ params.decoder).terminalState (executionParts params.toParameters path).2).holds w at holds
  have := (Whir.level_terminal_iff (algebraMap K E) params.schedule params.security params.decoders _ _ true _).mp
    (by rw [← Whir.openingExtractor_terminalState]; exact ⟨w, holds⟩)
  exact this.2

/-- The compiled terminal predicate is the verifier's acceptance of the parsed execution. -/
theorem terminal_holds_iff (params : Parameters S L k M)
    (path : (presentation params).protocol.tree.ExecutionPath)
    (witness : ((certificate params).extractor.terminalState path).Witness) :
    ((certificate params).extractor.terminalState path).holds witness ↔
      Accepts params.toParameters ((presentation params).originalPath path) := by
  let equal := (presentation params).terminalState_eq (Composed.certificate params.toParameters).extractor path
  have law : ∀ (a b : KnowledgeState) (equal : a = b) (w : a.Witness),
      a.holds w ↔ b.holds (equal ▸ w) := by
    intro a b equal w
    subst b
    rfl
  refine (law _ _ equal witness).trans (Iff.trans ?_ (original_terminal_iff params _))
  constructor
  · exact fun known => ⟨_, known⟩
  · rintro ⟨other, known⟩
    have same := (originalTerminalEquiv params _).injective
      (Subsingleton.elim (originalTerminalEquiv params _ other)
        (originalTerminalEquiv params _ (equal ▸ witness)))
    exact same ▸ known

/-- The singleton terminal inhabitant on a compiled path. -/
noncomputable def terminalForPath (params : Parameters S L k M)
    (path : (presentation params).protocol.tree.ExecutionPath) :
    ((certificate params).extractor.terminalState path).Witness :=
  ((presentation params).terminalState_eq (Composed.certificate params.toParameters).extractor path).symm ▸
    (originalTerminalEquiv params _).symm PUnit.unit

/-- The terminal inhabitant on the extracted path. -/
noncomputable def terminalWitness (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest) (c : Coins) :
    ((certificate params).extractor.terminalState (extractedPath params A X c)).Witness :=
  terminalForPath params (extractedPath params A X c)

/-- The non-interactive verifier: the challenge table from the seeded duplex and compiled
acceptance. -/
def verify (params : Parameters S L k M) (proof : Proof params) : Prop :=
  StandardBcs.verify (fun _ => coin params) (challengeTable params) (accept Commit.hash params) proof

/-- A verified proof without Merkle disagreement has terminal knowledge on its extracted path. -/
theorem transfer (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest) (c : Coins)
    (accepted : verify params (A c)) (agreement : ¬ Disagree params A X c) :
    ((certificate params).extractor.terminalState (extractedPath params A X c)).holds
      (terminalWitness params A X c) :=
  (terminal_holds_iff params _ _).mpr (authenticated_acceptance params A X c accepted.2.1 agreement)

/-- Standard-model knowledge soundness: the probability that a proof verifies while the extracted
stack fails the composed input relation is at most the Merkle extractor's node failures plus the
challenge table's correlation-intractability failures at each of the `count` draws. -/
theorem knowledgeSoundness (params : Parameters S L k M) {Coins : Type} [SampleableType Coins]
    (A : Coins → Proof params) (X : ExtractorMap Coins (List K) Commit.Digest) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      verify params (A c) ∧ ¬ (inputState params.toParameters).holds
        (StandardBcs.compositeExtractor (fun _ => coin params) (fun _ => inputState params.toParameters)
          (fun _ => (certificate params).extractor) A (messages params A X)
          (terminalWitness params A X) c)] ≤
      merkleError params A X +
        ∑ rank ∈ Finset.range (count params),
          StandardBcs.ciRel (fun _ => coin params) (fun _ => inputState params.toParameters)
            (fun _ => certificate params) A (messages params A X) (challengeTable params) rank :=
  (StandardBcs.knowledgeSoundness (fun _ => coin params) (fun _ => inputState params.toParameters)
    (fun _ => certificate params) A (messages params A X) (challengeTable params)
    (accept Commit.hash params) (terminalWitness params A X) (Disagree params A X)
    (fun c accepted agreement => transfer params A X c accepted agreement)
    (count params) (fun _ path => challenge_bound params PUnit.unit path)).trans
      (add_le_add (disagreement_bound params A X) le_rfl)

/-- A verifying proof's extracted stack interprets to a satisfying witness of the system, except
with the probability of `knowledgeSoundness`. -/
theorem extracted_satisfied (params : Parameters S L k M) (q : Whir.Table K M)
    (known : (inputState params.toParameters).holds q) :
    S.Satisfied L (params.external.interpret q) :=
  inputState_satisfied params.toParameters q known

end CompStark.Tables.Compiled
