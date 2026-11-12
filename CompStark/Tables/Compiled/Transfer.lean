/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Transfer
public import CompStark.Tables.Compiled.Protocol

/-! A proof's supplied opening batches are its trees' batches, and accepted batches that agree with the Merkle extractor give its leaves. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp
open StandardBcs StateRestoration
open MixedMerkleTree.Knowledge (ExtractorMap extractedLeaves nodeFail derivedAdversary)
open scoped ENNReal

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- An exact batch count identifies the supplied batches with the commitment list's batches. -/
theorem trees_openings (params : Parameters S L k M) (proof : Proof params)
    (length : proof.2.2.length = (trees params proof).length) :
    (trees params proof).map TreeOpening.opening = proof.2.2 := by
  apply List.ext_getElem
  · exact (List.length_map _).trans length.symm
  · intro index left right
    rw [List.getElem_map]
    have indexBound : index < (trees params proof).length := by
      simpa only [List.length_map] using left
    have actual := (presentation params).trees_openingAt proof.2.1 proof.2.2 0 index indexBound
    change ((presentation params).trees proof.2.1 proof.2.2 0)[index].opening = _
    rw [actual]
    simp only [openingAt, Nat.zero_add, List.getElem?_eq_getElem right, Option.getD_some]

/-- Accepted non-disagreeing batches agree with the Merkle extractor at every supplied column. -/
theorem leafAgreement (params : Parameters S L k M) {Coins : Type} (A : Coins → Proof params)
    (X : MixedMerkleTree.Knowledge.ExtractorMap Coins (List K) Commit.Digest) (c : Coins)
    (accepted : openingAccept Commit.hash params (A c)) (agreement : ¬ Disagree params A X c) :
    LeafAgreement (fun _ tree => tree.openedLeaves Commit.hash)
      (fun index _ => if bound : index < (treeShapes params.schedule params.semanticRowWords).length then
        merkleLeaves params A X ⟨index, bound⟩ c else fun _ => none) 0 (trees params (A c)) := by
  apply LeafAgreement.of_forall
  intro index bound query queried
  have shapes := trees_shapes params (A c)
  have lengths := congrArg List.length shapes
  simp only [List.length_map] at lengths
  have shapeBound : index < (treeShapes params.schedule params.semanticRowWords).length := lengths ▸ bound
  let slot : Fin (treeShapes params.schedule params.semanticRowWords).length := ⟨index, shapeBound⟩
  let tree := (trees params (A c))[index]
  have shape : (tree.height, tree.rowWords, tree.leafWords) = (treeShapes params.schedule params.semanticRowWords)[slot] := by
    have eq := congrArg (fun xs : List (ℕ × ℕ × ℕ) => xs[index]?.getD (0, 0, 0)) shapes
    simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
      List.getElem?_eq_getElem shapeBound, Option.map_some, Option.getD_some] at eq
    exact eq
  have height := congrArg Prod.fst shape
  have row := congrArg (fun s => s.2.1) shape
  have leaf := congrArg (fun s => s.2.2) shape
  have output : merkleAdversary params A slot c = (tree.root, tree.opening.queries, tree.opening.batch) := by
    simp only [merkleAdversary, slot, List.getElem?_eq_getElem bound, Option.getD_some, tree]
  have per := tree.openedLeaves_eq_extracted (merkleAdversary params A slot) X c output
    (accepted.2.2.2 tree (List.getElem_mem bound)) (fun bad => agreement ⟨slot, by
      simpa only [← height, ← row, ← leaf] using bad⟩) query queried
  simp only [Nat.zero_add]
  change tree.openedLeaves Commit.hash query = (if h : index < (treeShapes params.schedule params.semanticRowWords).length then
    merkleLeaves params A X ⟨index, h⟩ c else fun _ => none) query
  rw [dite_eq_left shapeBound]
  change tree.openedLeaves Commit.hash query = merkleLeaves params A X slot c query
  rw [merkleLeaves_eq]
  dsimp only
  rw [← height, ← row, ← leaf]
  exact per

end CompStark.Tables.Compiled
