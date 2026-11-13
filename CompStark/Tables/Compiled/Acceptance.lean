/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Transfer

/-! Accepted authenticated batches transfer the composed verifier to the extracted words. -/

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
open MixedMerkleTree.Knowledge (ExtractorMap extractedLeaves nodeFail derivedAdversary)
open scoped ENNReal

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

noncomputable section

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- Authentication transfers acceptance to any complete leaf images agreeing at the sampled columns. -/
theorem authenticated_acceptance_of_leafAgreement (hash : ByteArray → Commit.Digest) (params : Parameters S L k M) (proof : Proof params)
    (leafImage : ℕ → ℕ → Option (List K)) (accepted : openingAccept hash params proof)
    (agreement : LeafAgreement (fun _ tree => tree.openedLeaves hash)
      (fun index _ => leafImage index) 0 (trees params proof)) :
    Accepts params.toParameters ((presentation params).originalPath
      (StandardBcs.extractedPath (coin params) proof.2.1
        ((presentation params).messages proof.2.1 leafImage 0))) := by
  let openings := proof.2.2
  let first : ℕ → TreeOpening → ℕ → Option (List K) := fun _ tree => tree.openedLeaves hash
  let leaves := leafImage
  let second : ℕ → TreeOpening → ℕ → Option (List K) := fun index _ => leaves index
  let rootTree : TreeOpening := ⟨proof.2.1.1, (baseLayout params.schedule params.semanticRowWords).height,
    (baseLayout params.schedule params.semanticRowWords).rowWords, (baseLayout params.schedule params.semanticRowWords).leafWords, openingAt openings 0⟩
  obtain ⟨outer, whir, tree_eq, parsed⟩ :=
    (outerPresentation params).append_split (whirPresentation params.schedule)
      (outerPresentation_shapes params) proof.2.1.2 openings 1
  let out := (outerReduction params.toSetup params.reductions).output outer
  have fullAgreement := agreement
  change (∀ index ∈ rootTree.opening.queries, first 0 rootTree index = second 0 rootTree index) ∧
    LeafAgreement first second 1
      (((outerPresentation params).append (whirPresentation params.schedule)).trees
        proof.2.1.2 openings 1) at fullAgreement
  rw [tree_eq] at fullAgreement
  have queried := congrArg (List.map OpeningBatch.queries)
    (trees_openings params proof accepted.2.2.1)
  simp only [List.map_map] at queried
  have queryLists := queried.trans accepted.2.1
  change (trees params proof).map (fun tree => tree.opening.queries) =
    whirQueries params.schedule (executionParts params.toParameters
      ((presentation params).originalPath (StandardBcs.extractedPath (coin params) proof.2.1
        ((presentation params).openedMessages hash proof.2.1 openings 0)))).2 at queryLists
  erw [Presentation.reconstruct_opened] at queryLists
  change (rootTree :: ((outerPresentation params).append (whirPresentation params.schedule)).trees
      proof.2.1.2 openings 1).map (fun tree => tree.opening.queries) =
    whirQueries params.schedule (splitPath (outerProtocol params.toSetup)
      (Whir.opening E params.schedule)
      (((outerPresentation params).append (whirPresentation params.schedule)).reconstruct
        proof.2.1.2 openings first 1)).2 at queryLists
  rw [tree_eq, parsed] at queryLists
  have whir_eq := whir_accepts_congr params.schedule whir openings first second 1
    (Whir.mapMasked (algebraMap K E) ((baseLayout params.schedule params.semanticRowWords).decode (first 0 rootTree)))
    (Whir.mapMasked (algebraMap K E) ((baseLayout params.schedule params.semanticRowWords).decode (second 0 rootTree)))
    (openingClaims params.toSetup out) rootTree.opening.queries queryLists
    (fun column member => by
      unfold Whir.mapMasked
      rw [baseLayout_congr params.schedule params.semanticRowWords _ _ column
        (fullAgreement.1 column.val member)])
    fullAgreement.2
  have acceptedOriginal := accepted.1
  change Accepts params.toParameters ((presentation params).originalPath
    (StandardBcs.extractedPath (coin params) proof.2.1
      ((presentation params).openedMessages hash proof.2.1 openings 0))) at acceptedOriginal
  erw [Presentation.reconstruct_opened] at acceptedOriginal
  simp only [Accepts, executionParts] at acceptedOriginal
  erw [parsed first] at acceptedOriginal
  change publicAccepted params.toSetup out ∧
    Whir.accepts (algebraMap K E) params.schedule
      (Whir.mapMasked (algebraMap K E) ((baseLayout params.schedule params.semanticRowWords).decode (first 0 rootTree)))
      (openingClaims params.toSetup out)
      ((whirPresentation params.schedule).reconstruct whir openings first 1) = true at acceptedOriginal
  change Accepts params.toParameters ((presentation params).originalPath
    (StandardBcs.extractedPath (coin params) proof.2.1
      ((presentation params).messages proof.2.1 leaves 0)))
  erw [Presentation.reconstruct_messages (openings := openings)]
  simp only [Accepts, executionParts]
  erw [parsed second]
  exact ⟨acceptedOriginal.1, whir_eq ▸ acceptedOriginal.2⟩


/-- Acceptance of complete leaf images transfers to the opened rows agreeing with them at the sampled
columns, when the batches are the sampled query lists of the commitments. -/
theorem acceptance_of_leafAgreement_complete (hash : ByteArray → Commit.Digest) (params : Parameters S L k M)
    (proof : Proof params) (leafImage : ℕ → ℕ → Option (List K))
    (queries : proof.2.2.map OpeningBatch.queries = whirQueries params.schedule
      (executionParts params.toParameters ((presentation params).openedPath hash proof.2.1 proof.2.2)).2)
    (length : proof.2.2.length = (trees params proof).length)
    (accepted : Accepts params.toParameters ((presentation params).originalPath
      (StandardBcs.extractedPath (coin params) proof.2.1
        ((presentation params).messages proof.2.1 leafImage 0))))
    (agreement : LeafAgreement (fun _ tree => tree.openedLeaves hash)
      (fun index _ => leafImage index) 0 (trees params proof)) :
    Accepts params.toParameters ((presentation params).openedPath hash proof.2.1 proof.2.2) := by
  let openings := proof.2.2
  let first : ℕ → TreeOpening → ℕ → Option (List K) := fun _ tree => tree.openedLeaves hash
  let leaves := leafImage
  let second : ℕ → TreeOpening → ℕ → Option (List K) := fun index _ => leaves index
  let rootTree : TreeOpening := ⟨proof.2.1.1, (baseLayout params.schedule params.semanticRowWords).height,
    (baseLayout params.schedule params.semanticRowWords).rowWords, (baseLayout params.schedule params.semanticRowWords).leafWords, openingAt openings 0⟩
  obtain ⟨outer, whir, tree_eq, parsed⟩ :=
    (outerPresentation params).append_split (whirPresentation params.schedule)
      (outerPresentation_shapes params) proof.2.1.2 openings 1
  let out := (outerReduction params.toSetup params.reductions).output outer
  have fullAgreement := agreement
  change (∀ index ∈ rootTree.opening.queries, first 0 rootTree index = second 0 rootTree index) ∧
    LeafAgreement first second 1
      (((outerPresentation params).append (whirPresentation params.schedule)).trees
        proof.2.1.2 openings 1) at fullAgreement
  rw [tree_eq] at fullAgreement
  have queried := congrArg (List.map OpeningBatch.queries)
    (trees_openings params proof length)
  simp only [List.map_map] at queried
  have queryLists := queried.trans queries
  change (trees params proof).map (fun tree => tree.opening.queries) =
    whirQueries params.schedule (executionParts params.toParameters
      ((presentation params).originalPath (StandardBcs.extractedPath (coin params) proof.2.1
        ((presentation params).openedMessages hash proof.2.1 openings 0)))).2 at queryLists
  erw [Presentation.reconstruct_opened] at queryLists
  change (rootTree :: ((outerPresentation params).append (whirPresentation params.schedule)).trees
      proof.2.1.2 openings 1).map (fun tree => tree.opening.queries) =
    whirQueries params.schedule (splitPath (outerProtocol params.toSetup)
      (Whir.opening E params.schedule)
      (((outerPresentation params).append (whirPresentation params.schedule)).reconstruct
        proof.2.1.2 openings first 1)).2 at queryLists
  rw [tree_eq, parsed] at queryLists
  have whir_eq := whir_accepts_congr params.schedule whir openings first second 1
    (Whir.mapMasked (algebraMap K E) ((baseLayout params.schedule params.semanticRowWords).decode (first 0 rootTree)))
    (Whir.mapMasked (algebraMap K E) ((baseLayout params.schedule params.semanticRowWords).decode (second 0 rootTree)))
    (openingClaims params.toSetup out) rootTree.opening.queries queryLists
    (fun column member => by
      unfold Whir.mapMasked
      rw [baseLayout_congr params.schedule params.semanticRowWords _ _ column
        (fullAgreement.1 column.val member)])
    fullAgreement.2
  have acceptedFull := accepted
  erw [Presentation.reconstruct_messages (openings := openings)] at acceptedFull
  simp only [Accepts, executionParts] at acceptedFull
  erw [parsed second] at acceptedFull
  change publicAccepted params.toSetup out ∧
    Whir.accepts (algebraMap K E) params.schedule
      (Whir.mapMasked (algebraMap K E) ((baseLayout params.schedule params.semanticRowWords).decode (second 0 rootTree)))
      (openingClaims params.toSetup out)
      ((whirPresentation params.schedule).reconstruct whir openings second 1) = true at acceptedFull
  change Accepts params.toParameters ((presentation params).originalPath
    (StandardBcs.extractedPath (coin params) proof.2.1
      ((presentation params).openedMessages hash proof.2.1 openings 0)))
  erw [Presentation.reconstruct_opened]
  simp only [Accepts, executionParts]
  erw [parsed first]
  exact ⟨acceptedFull.1, whir_eq.trans acceptedFull.2⟩

/-- Authentication transfers composed acceptance to the identical same-coins extracted path. -/
theorem authenticated_acceptance (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : MixedMerkleTree.Knowledge.ExtractorMap Coins (List K) Commit.Digest) (c : Coins)
    (accepted : openingAccept Commit.hash params (A c)) (agreement : ¬ Disagree params A X c) :
    Accepts params.toParameters ((presentation params).originalPath
      (StandardBcs.extractedPath (coin params) (A c).2.1 (messages params A X c))) := by
  rw [messages_eq]
  exact authenticated_acceptance_of_leafAgreement Commit.hash params (A c) _ accepted
    (leafAgreement params A X c accepted agreement)

end

end CompStark.Tables.Compiled
