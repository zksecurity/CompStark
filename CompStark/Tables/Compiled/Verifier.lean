/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Soundness
public import CompStark.Tables.Composed.Verifier

/-! The executable verifier of a compiled proof: one duplex traversal checks every challenge and
grinding nonce, then the fast composed verifier runs on the words the Merkle openings give, and
the opening batches are checked against their roots and the WHIR query positions. It decides
`Tables.Compiled.verify` (`check_iff`). -/

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

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- Reveal-only blocks announce nothing. -/
theorem grandRounds_unannounced {tail : Protocol} (suffix : Presentation tail) (h : suffix.Unannounced)
    (degree count : ℕ) : (grandRounds degree suffix count).Unannounced := by
  induction count with
  | zero => exact h
  | succ count ih => exact ih

/-- Interpolation draws announce nothing. -/
theorem interpolation_unannounced {tail : Protocol} (suffix : Presentation tail) (h : suffix.Unannounced)
    (count : ℕ) : (interpolation suffix count).Unannounced := by
  induction count with
  | zero => exact h
  | succ count ih => exact ih

/-- A product descent announces nothing. -/
theorem grandProduct_unannounced {tail : Protocol} (suffix : Presentation tail) (h : suffix.Unannounced)
    (layers : List ℕ) (used : ℕ) : (grandProduct suffix layers used).Unannounced := by
  induction layers generalizing used with
  | nil => exact h
  | cons lanes rest ih =>
      refine grandRounds_unannounced _ ?_ _ _
      exact fun _ => interpolation_unannounced _ (ih _) lanes

/-- WHIR's scalar rounds announce nothing. -/
theorem whirRounds_unannounced {tail : Protocol} (suffix : Presentation tail) (h : suffix.Unannounced)
    (count : ℕ) : (whirRounds suffix count).Unannounced := by
  induction count with
  | zero => exact h
  | succ count ih => exact fun _ => ih

/-- WHIR announces nothing. -/
theorem whirPresentation_unannounced {n : ℕ} (schedule : Whir.Schedule K n) :
    (whirPresentation schedule).Unannounced := by
  change (whirWirePresentation schedule).Unannounced
  induction schedule with
  | last lanes tail encoding queries =>
      apply whirRounds_unannounced
      exact fun _ _ => whirRounds_unannounced .done trivial tail
  | more lanes encoding queries rest ih =>
      apply whirRounds_unannounced
      exact fun _ _ _ => ih

/-- The compiled presentation announces nothing. -/
theorem presentation_unannounced (params : Parameters S L k M) : (presentation params).Unannounced := by
  change ((outerPresentation params).append (whirPresentation params.schedule)).Unannounced
  refine Presentation.Unannounced.append _ _ (Presentation.Unannounced.append _ _
    (Presentation.Unannounced.append _ _ ?_ ?_) params.externalUnannounced) (whirPresentation_unannounced _)
  · intro _
    refine grandProduct_unannounced _ ?_ _ _
    exact fun _ => trivial
  · change (tableRounds S L (TableSumcheck.maxHeight S L)).Unannounced
    induction TableSumcheck.maxHeight S L with
    | zero => exact fun _ => trivial
    | succ count ih => exact ih

/-- The opened-word checks: the fast composed verifier on the opened words, the query positions,
the batch count and every batch against its root. -/
def openingCheck (params : Parameters S L k M) (proof : Proof params) : Bool :=
  let path := (presentation params).openedPath Commit.hash proof.2.1 proof.2.2
  let parts := executionParts params.toParameters path
  Composed.verify params.toParameters path &&
    decide (proof.2.2.map OpeningBatch.queries = whirQueries params.schedule parts.2) &&
    decide (proof.2.2.length = (trees params proof).length) &&
    (trees params proof).all fun tree => Commit.accepts Commit.hash tree.height tree.rowWords
      tree.leafWords tree.opening.queries tree.opening.batch tree.root

/-- The opened-word checks decide the opened verifier. -/
theorem openingCheck_iff (params : Parameters S L k M) (proof : Proof params) :
    openingCheck params proof = true ↔ openingAccept Commit.hash params proof := by
  unfold openingCheck openingAccept
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, verify_iff, TreeOpening.accepts]
  tauto

/-- The executable verifier of a compiled proof. -/
def check (params : Parameters S L k M) (proof : Proof params) : Bool :=
  WireObserver.check _ (presentation params).observer (initialState params) proof.2.1 &&
    (presentation params).grindingCheck proof.2.1 (initialState params) &&
    openingCheck params proof

/-- The executable verifier decides the compiled verifier. -/
theorem check_iff (params : Parameters S L k M) (proof : Proof params) :
    check params proof = true ↔ verify params proof := by
  unfold check verify StandardBcs.verify accept
  rw [Bool.and_eq_true, Bool.and_eq_true, WireObserver.check_iff,
    Presentation.grindingCheck_iff _ (presentation_unannounced params), openingCheck_iff]
  change ((CorrelationIntractable.Consistent _ _ proof.2.1 ∧ _) ∧ _) ↔
    CorrelationIntractable.Consistent _ _ proof.2.1 ∧ _ ∧ _
  tauto

/-- The data the verifier reads: the setup, the evaluated opening schedule, the external
argument's presentation and the transcript seed. -/
structure Data (S : System K) (L : Layout S.tables.length) (k M : ℕ) where
  /-- The setup. -/
  setup : Setup S L k M
  /-- The opening schedule with its query-weight evaluators. -/
  evaluated : Pcs.EvaluatedSchedule M
  /-- The external argument's presentation. -/
  externalPresentation : Presentation setup.external.protocol
  /-- The duplex's initialization vector. -/
  iv : Commit.Digest
  /-- The statement digest. -/
  statement : Commit.Digest

/-- The verifier's data of the parameters. -/
def Parameters.data (params : Parameters S L k M) : Data S L k M :=
  ⟨params.toSetup, params.evaluated, params.externalPresentation, params.iv, params.statement⟩

namespace Data

variable (d : Data S L k M)

/-- The compiled presentation of the data. -/
def presentation : Presentation (composedProtocol d.setup d.evaluated.schedule) :=
  .merkle (baseLayout d.evaluated.schedule (2 ^ d.evaluated.schedule.lanes))
    ((((busPresentation S L k).append (tablePresentation S L)).append d.externalPresentation).append
      (whirPresentation d.evaluated.schedule))

/-- A compiled proof of the data. -/
abbrev Proof := FSProof PUnit Commit.Digest Openings (fun _ => d.presentation.coin)

/-- The executable verifier on the data. -/
def check (proof : d.Proof) : Bool :=
  let state := Transcript.seedDigests d.iv d.statement
  let path := d.presentation.openedPath Commit.hash proof.2.1 proof.2.2
  let parts := splitPath (outerProtocol d.setup) (Whir.opening E d.evaluated.schedule) path.2
  let trees := d.presentation.trees proof.2.1 proof.2.2 0
  WireObserver.check _ d.presentation.observer state proof.2.1 &&
    d.presentation.grindingCheck proof.2.1 state &&
    (verifyWith d.setup d.evaluated path &&
      decide (proof.2.2.map OpeningBatch.queries = whirQueries d.evaluated.schedule parts.2) &&
      decide (proof.2.2.length = trees.length) &&
      trees.all fun tree => Commit.accepts Commit.hash tree.height tree.rowWords
        tree.leafWords tree.opening.queries tree.opening.batch tree.root)

end Data

/-- The verifier reads only the parameters' data. -/
theorem check_data (params : Parameters S L k M) (proof : Proof params) :
    check params proof = params.data.check proof := rfl

/-- The executable verifier on the parameters' data decides the compiled verifier. -/
theorem data_check_iff (params : Parameters S L k M) (proof : Proof params) :
    params.data.check proof = true ↔ verify params proof := by
  rw [← check_data]
  exact check_iff params proof

end CompStark.Tables.Compiled
