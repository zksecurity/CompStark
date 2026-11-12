/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Count
public import CompStark.Tables.Compiled.Presentation

/-! The composed system compiled with one Keccak root per encoded word: its parameters, its
presentation and proofs, the Merkle trees a proof opens, the verifier's view of the opened words,
and the bound on a verifying opening that disagrees with the Merkle extractor. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp
open StandardBcs StateRestoration
open MixedMerkleTree.Knowledge (ExtractorMap extractedLeaves nodeFail derivedAdversary)
open scoped ENNReal

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- The composed system's parameters with its external argument's presentation, which commits no
word. -/
structure Parameters (S : System K) (L : Layout S.tables.length) (k M : ℕ)
    extends Composed.Parameters S L k M where
  /-- The external argument's public-coin presentation. -/
  externalPresentation : Presentation toSetup.external.protocol
  /-- The external argument commits no word. -/
  externalShapes : externalPresentation.HasShapes []
  /-- The external argument's messages have prefix-free encodings and its draws squeeze. -/
  externalFramed : externalPresentation.Framed
  /-- The external argument's number of draws. -/
  externalCount : ℕ
  /-- The external argument has one rank per draw. -/
  externalCounted : externalPresentation.Counted externalCount
  /-- The duplex's initialization vector. -/
  iv : Commit.Digest
  /-- The digest of the statement the transcript is bound to. -/
  statement : Commit.Digest

/-- The rows of the stack's initial word, one per folding lane pattern. -/
def Parameters.semanticRowWords (params : Parameters S L k M) : ℕ := 2 ^ params.schedule.lanes

/-- Reveal-only blocks keep a presentation's commitments. -/
theorem grandRounds_shapes {tail : Protocol} (suffix : Presentation tail) (h : suffix.HasShapes [])
    (degree count : ℕ) : (grandRounds degree suffix count).HasShapes [] := by
  induction count with
  | zero => exact h
  | succ count ih => exact ih

/-- Interpolation draws keep a presentation's commitments. -/
theorem interpolation_shapes {tail : Protocol} (suffix : Presentation tail) (h : suffix.HasShapes [])
    (count : ℕ) : (interpolation suffix count).HasShapes [] := by
  induction count with
  | zero => exact h
  | succ count ih => exact ih

/-- A product descent keeps a presentation's commitments. -/
theorem grandProduct_shapes {tail : Protocol} (suffix : Presentation tail) (h : suffix.HasShapes [])
    (layers : List ℕ) (used : ℕ) : (grandProduct suffix layers used).HasShapes [] := by
  induction layers generalizing used with
  | nil => exact h
  | cons lanes rest ih =>
      refine grandRounds_shapes _ ?_ _ _
      exact fun _ => interpolation_shapes _ (ih _) lanes

/-- The bus commits no word. -/
theorem busPresentation_shapes : (busPresentation S L k).HasShapes [] := by
  intro _
  refine grandProduct_shapes _ ?_ _ _
  exact fun _ => rfl

/-- The table sumcheck commits no word. -/
theorem tablePresentation_shapes : (tablePresentation S L).HasShapes [] := by
  change (tableRounds S L (TableSumcheck.maxHeight S L)).HasShapes []
  induction TableSumcheck.maxHeight S L with
  | zero => exact fun _ => rfl
  | succ count ih => exact ih

/-- The bus, the table sumcheck and the external argument, all public. -/
def outerPresentation (params : Parameters S L k M) : Presentation (outerProtocol params.toSetup) :=
  ((busPresentation S L k).append (tablePresentation S L)).append params.externalPresentation

/-- The outer presentation commits no word. -/
theorem outerPresentation_shapes (params : Parameters S L k M) :
    (outerPresentation params).HasShapes [] :=
  (Presentation.HasShapes.append _ _ (busPresentation_shapes (S := S) (L := L) (k := k))
    tablePresentation_shapes).append _ _ params.externalShapes

/-- The composed presentation: the stack's initial word as a root, then the outer protocol and the
WHIR opening. -/
def presentation (params : Parameters S L k M) : Presentation (Composed.protocol params.toParameters) :=
  .merkle (baseLayout params.schedule params.semanticRowWords)
    ((outerPresentation params).append (whirPresentation params.schedule))

/-- Public-coin IOP compiled with one Keccak root per initial or folded RS word. -/
def coin (params : Parameters S L k M) := (presentation params).coin

/-- A proof carries its full compiled path and only the pruned opening batches beside it. -/
abbrev Proof (params : Parameters S L k M) :=
  FSProof PUnit Commit.Digest Openings (fun _ => coin params)

/-- The ordered Merkle objects produced by one proof. -/
def trees (params : Parameters S L k M) (proof : Proof params) : List TreeOpening :=
  (presentation params).trees proof.2.1 proof.2.2 0

/-- Run the composed verifier using only the authenticated rows, and check the exact query
positions and number of batches, so no prover-selected oracle queries are trusted. -/
def openingAccept (hash : ByteArray → Commit.Digest) (params : Parameters S L k M) (proof : Proof params) : Prop :=
  let path := (presentation params).openedPath hash proof.2.1 proof.2.2
  let parts := executionParts params.toParameters path
  Accepts params.toParameters path ∧
    proof.2.2.map OpeningBatch.queries = whirQueries params.schedule parts.2 ∧
    proof.2.2.length = (trees params proof).length ∧
    ∀ tree ∈ trees params proof, tree.accepts hash

/-- Commitment occurrences on every path have exactly the fixed schedule's tree shapes. -/
theorem trees_shapes (params : Parameters S L k M) (proof : Proof params) :
    (trees params proof).map (fun tree => (tree.height, tree.rowWords, tree.leafWords)) =
      treeShapes params.schedule params.semanticRowWords := by
  apply Presentation.HasShapes.trees
  exact ⟨_, rfl, (outerPresentation_shapes params).append _ _ (whirPresentation_shapes params.schedule)⟩

/-- One same-coins wire adversary for an explicitly indexed commitment occurrence. -/
def merkleAdversary (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (slot : Fin (treeShapes params.schedule params.semanticRowWords).length) : Commit.Adversary Coins := fun c =>
  let tree := (trees params (A c))[slot.val]?.getD
    ⟨Vector.replicate 32 0, 0, 0, 0, ⟨[], ⟨[], []⟩⟩⟩
  (tree.root, tree.opening.queries, tree.opening.batch)

/-- Merkle positions include both the commitment occurrence and its mixed-tree position. -/
noncomputable def merklePositions {n : ℕ} (schedule : Whir.Schedule K n) (liveRows : ℕ) :
    Finset (Fin (treeShapes schedule liveRows).length × MixedMerkleTree.Knowledge.Position) :=
  (Finset.univ : Finset (Fin (treeShapes schedule liveRows).length)).biUnion fun slot =>
    (MixedMerkleTree.Knowledge.positions ((treeShapes schedule liveRows)[slot]).1 0 (fun _ => false)).image
      (fun position => (slot, position))

/-- The derived Keccak node adversary at a concrete commitment and tree position. -/
def nodeAdversary (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest)
    (position : Fin (treeShapes params.schedule params.semanticRowWords).length × MixedMerkleTree.Knowledge.Position) :=
  let shape := (treeShapes params.schedule params.semanticRowWords)[position.1]
  derivedAdversary Commit.hashLeaf Commit.compress [] shape.1 0 (fun _ => false)
    (Commit.mixedAdversary Commit.hash shape.1 shape.2.1 shape.2.2
      (merkleAdversary params A position.1)) X position.2

/-- Extract and materialize VCVio's hash-consistent leaf mask for one commitment occurrence. -/
@[macro_inline] def merkleLeaves (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest)
    (slot : Fin (treeShapes params.schedule params.semanticRowWords).length) (c : Coins) :
    ℕ → Option (List K) :=
  let shape := (treeShapes params.schedule params.semanticRowWords)[slot]
  let extracted := MixedMerkleTree.Knowledge.extractedMask Commit.hashLeaf Commit.compress []
    shape.1 0 (fun _ => false)
    (Commit.mixedAdversary Commit.hash shape.1 shape.2.1 shape.2.2 (merkleAdversary params A slot)) X c
  let leaves := Array.ofFn extracted
  fun i => if h : i < 2 ^ shape.1 then leaves[i]'(by simpa only [leaves, Array.size_ofFn] using h) else none

/-- Materialization preserves VCVio's exact mask, including every hidden column. -/
theorem merkleLeaves_eq (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest)
    (slot : Fin (treeShapes params.schedule params.semanticRowWords).length) (c : Coins) :
    merkleLeaves params A X slot c =
      let shape := (treeShapes params.schedule params.semanticRowWords)[slot]
      fun i => if bound : i < 2 ^ shape.1 then
        MixedMerkleTree.Knowledge.extractedMask Commit.hashLeaf Commit.compress [] shape.1 0
          (fun _ => false) (Commit.mixedAdversary Commit.hash shape.1 shape.2.1 shape.2.2
            (merkleAdversary params A slot)) X c ⟨i, bound⟩
      else none := by
  funext i
  unfold merkleLeaves
  split_ifs <;> simp only [Array.getElem_ofFn]

/-- The `StandardBcs` message extractor is exactly VCVio extraction through the leaf layouts. -/
@[macro_inline] def messages (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest) (c : Coins) :
    ExtractedMessages (coin params) (A c).2.1 :=
  let images := Vector.ofFn fun slot : Fin (treeShapes params.schedule params.semanticRowWords).length =>
    merkleLeaves params A X slot c
  (presentation params).messages (A c).2.1 (fun index =>
    if bound : index < (treeShapes params.schedule params.semanticRowWords).length then
      images[index] else fun _ => none) 0

/-- Sharing complete occurrence images preserves the original message map. -/
theorem messages_eq (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest) (c : Coins) :
    messages params A X c =
      (presentation params).messages (A c).2.1 (fun index =>
        if bound : index < (treeShapes params.schedule params.semanticRowWords).length then
          merkleLeaves params A X ⟨index, bound⟩ c else fun _ => none) 0 := by
  simp only [messages, Vector.getElem_ofFn]

/-- A verifying supplied Merkle leaf differs from the extractor at some commitment occurrence. -/
def Disagree (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : ExtractorMap Coins (List K) Commit.Digest) (c : Coins) : Prop :=
  ∃ slot : Fin (treeShapes params.schedule params.semanticRowWords).length,
    let shape := (treeShapes params.schedule params.semanticRowWords)[slot]
    Commit.Disagree Commit.hash shape.1 shape.2.1 shape.2.2 (merkleAdversary params A slot) X c

/-- Compiled disagreement exposes a node failure in the fixed commitment schedule. -/
theorem disagreement_implies_nodeBad (params : Parameters S L k M) {Coins : Type}
    (A : Coins → Proof params) (X : ExtractorMap Coins (List K) Commit.Digest) (c : Coins)
    (disagree : Disagree params A X c) :
    ∃ position ∈ merklePositions params.schedule params.semanticRowWords,
      MixedMerkleTree.Knowledge.NodeBad Commit.answer (nodeAdversary params A X position)
        (X position.2 (nodeAdversary params A X position)) c := by
  obtain ⟨slot, disagree⟩ := disagree
  obtain ⟨position, member, bad⟩ := Commit.disagreement_implies_nodeBad Commit.hash
    ((treeShapes params.schedule params.semanticRowWords)[slot]).1
    ((treeShapes params.schedule params.semanticRowWords)[slot]).2.1
    ((treeShapes params.schedule params.semanticRowWords)[slot]).2.2
    (merkleAdversary params A slot) X c disagree
  exact ⟨(slot, position), Finset.mem_biUnion.mpr
    ⟨slot, Finset.mem_univ _, Finset.mem_image.mpr ⟨position, member, rfl⟩⟩, bad⟩

/-- The total binding error is the finite sum of Keccak node-failure probabilities. -/
noncomputable def merkleError (params : Parameters S L k M) {Coins : Type} [SampleableType Coins]
    (A : Coins → Proof params) (X : ExtractorMap Coins (List K) Commit.Digest) : ℝ≥0∞ :=
  ∑ position ∈ merklePositions params.schedule params.semanticRowWords,
    nodeFail Commit.answer (nodeAdversary params A X position) (X position.2 (nodeAdversary params A X position))

/-- The pruned-opening transfer lemmas and VCVio's mixed-tree knowledge bound bound disagreement
by the explicit sum over commitment occurrences and their node positions. -/
theorem disagreement_bound (params : Parameters S L k M) {Coins : Type} [SampleableType Coins]
    (A : Coins → Proof params) (X : ExtractorMap Coins (List K) Commit.Digest) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Disagree params A X c] ≤ merkleError params A X := by
  classical
  let slots := Finset.univ (α := Fin (treeShapes params.schedule params.semanticRowWords).length)
  calc
    _ ≤ ∑ slot ∈ slots, Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
        let shape := (treeShapes params.schedule params.semanticRowWords)[slot]
        Commit.Disagree Commit.hash shape.1 shape.2.1 shape.2.2 (merkleAdversary params A slot) X c] := by
      refine (prEvent_mono ($ᵗ Coins : ProbComp Coins) _ _ ?_).trans
        (prEvent_exists_finset_le slots ($ᵗ Coins : ProbComp Coins)
          (fun slot c => let shape := (treeShapes params.schedule params.semanticRowWords)[slot]
            Commit.Disagree Commit.hash shape.1 shape.2.1 shape.2.2 (merkleAdversary params A slot) X c))
      intro c disagree
      obtain ⟨slot, failure⟩ := disagree
      exact ⟨slot, Finset.mem_univ slot, failure⟩
    _ ≤ ∑ slot ∈ slots, ∑ v ∈ MixedMerkleTree.Knowledge.positions
        ((treeShapes params.schedule params.semanticRowWords)[slot]).1 0 (fun _ => false),
        nodeFail Commit.answer (nodeAdversary params A X (slot, v))
          (X v (nodeAdversary params A X (slot, v))) :=
      Finset.sum_le_sum fun slot _ => Commit.disagreement_bound Commit.hash
        ((treeShapes params.schedule params.semanticRowWords)[slot]).1 ((treeShapes params.schedule params.semanticRowWords)[slot]).2.1
        ((treeShapes params.schedule params.semanticRowWords)[slot]).2.2 (merkleAdversary params A slot) X
    _ = merkleError params A X := by
      unfold merkleError merklePositions
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro slot _
        rw [Finset.sum_image]
        intro a _ b _ equal
        exact (Prod.mk.inj equal).2
      · intro a _ b _ different
        apply Finset.disjoint_left.mpr
        intro position ha hb
        obtain ⟨va, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨vb, _, equal⟩ := Finset.mem_image.mp hb
        exact different (Prod.mk.inj equal).1.symm

end CompStark.Tables.Compiled
