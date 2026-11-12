/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Whir

/-! Concrete commitment paths, Merkle extraction and the verifier's opened-word view. The
announced query lists are checked against the WHIR path, and authentication hints are not
absorbed into the challenge table. Public setup and the statement are fixed before a proof. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Multilinear CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp
open StandardBcs StateRestoration
open MixedMerkleTree.Knowledge (ExtractorMap extractedLeaves nodeFail derivedAdversary)
open scoped ENNReal


/-- One pruned opening batch with the column list the verifier must reproduce. -/
structure OpeningBatch where
  /-- Query positions, including duplicates, in the verifier's sampling order. -/
  queries : List ℕ
  /-- Wire rows and shared sibling hashes. -/
  batch : Commit.Pruned

/-- Authentication data ordered by the corresponding commitment occurrences. -/
abbrev Openings := List OpeningBatch

/-- Missing authentication data decode to an empty, rejecting Merkle batch. -/
def openingAt (openings : Openings) (index : ℕ) : OpeningBatch :=
  openings[index]?.getD ⟨[], ⟨[], []⟩⟩

/-- A single concrete root, tree shape and opening batch on a compiled path. -/
structure TreeOpening where
  /-- Root transmitted at this commitment occurrence. -/
  root : Commit.Digest
  /-- Binary tree height. -/
  height : ℕ
  /-- Transmitted row width. -/
  rowWords : ℕ
  /-- Reconstructed leaf width. -/
  leafWords : ℕ
  /-- Authentication data for this commitment. -/
  opening : OpeningBatch

/-- Acceptance of a single root's checked pruned batch under a raw-byte hash. -/
def TreeOpening.accepts (hash : ByteArray → Commit.Digest) (tree : TreeOpening) : Prop :=
  Commit.accepts hash tree.height tree.rowWords tree.leafWords tree.opening.queries
    tree.opening.batch tree.root = true

/-- Reconstructed leaves preserve the absence of missing or malformed paths. -/
@[macro_inline] def TreeOpening.openedLeaves (hash : ByteArray → Commit.Digest) (tree : TreeOpening) :
    ℕ → Option (List K) :=
  match Commit.expand hash tree.height tree.rowWords tree.leafWords tree.opening.queries tree.opening.batch with
  | none => fun _ => none
  | some (_, paths) => fun index =>
      (paths.find? fun path => path.index == index).map Commit.Path.leaf

/-- Read the root and shape at every PCS commitment occurrence. -/
def Presentation.trees : {original : Protocol} → (presentation : Presentation original) →
    (compile Commit.Digest presentation.coin).tree.ExecutionPath → Openings → ℕ → List TreeOpening
  | _, .refine wire _, path, openings, index => wire.trees path openings index
  | _, .done, _, _, _ => []
  | _, @Presentation.sender _ _ _ _ next, path, openings, index =>
      (next path.1).trees path.2 openings index
  | _, @Presentation.reveal _ _ _ _ _ next, path, openings, index => next.trees path.2 openings index
  | _, @Presentation.merkle _ _ _ _ layout next, path, openings, index =>
      ⟨path.1, layout.height, layout.rowWords, layout.leafWords, openingAt openings index⟩ ::
        next.trees path.2 openings (index + 1)
  | _, @Presentation.announce _ _ _ _ _ next, path, openings, index => (next path.1).trees path.2 openings index
  | _, .grind _ next, path, openings, index => next.trees path.2 openings index
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, path, openings, index => next.trees path.2 openings index

/-- Reconstruct the original oracle words solely from the supplied authentication rows. -/
def Presentation.openedMessages (hash : ByteArray → Commit.Digest) : {original : Protocol} → (presentation : Presentation original) →
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath) →
    Openings → ℕ → ExtractedMessages presentation.coin path
  | _, .refine wire _, path, openings, index => wire.openedMessages hash path openings index
  | _, .done, _, _, _ => fun index => nomatch index
  | _, @Presentation.sender _ _ _ _ next, path, openings, index =>
      (next path.1).openedMessages hash path.2 openings index
  | _, @Presentation.reveal _ _ _ _ _ next, path, openings, index => next.openedMessages hash path.2 openings index
  | _, @Presentation.merkle _ _ _ _ layout next, path, openings, index => fun occurrence =>
      match occurrence with
      | .inl _ => layout.decode
          (TreeOpening.openedLeaves hash
            ⟨path.1, layout.height, layout.rowWords, layout.leafWords, openingAt openings index⟩)
      | .inr occurrence => next.openedMessages hash path.2 openings (index + 1) occurrence
  | _, @Presentation.announce _ _ _ _ _ next, path, openings, index => (next path.1).openedMessages hash path.2 openings index
  | _, .grind _ next, path, openings, index => next.openedMessages hash path.2 openings index
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, path, openings, index => next.openedMessages hash path.2 openings index

/-- The verifier's ideal path, using its own decoded opening rows for oracle answers. -/
def Presentation.openedPath (hash : ByteArray → Commit.Digest) {original : Protocol}
    (presentation : Presentation original)
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath) (openings : Openings) :
    original.tree.ExecutionPath :=
  presentation.originalPath
    (extractedPath presentation.coin path (presentation.openedMessages hash path openings 0))

/-- The authored WHIR query list for each encoded word, in commitment order. -/
def whirQueries : {n : ℕ} → (schedule : Whir.Schedule K n) →
    (Whir.opening E schedule).tree.ExecutionPath → List (List ℕ)
  | _, .last lanes tail encoding queries, path =>
      let round := Whir.readRounds (Whir.transition E (.last lanes tail encoding queries))
        lanes 0 path.2
      [List.ofFn fun i : Fin queries => (round.2.2.2.2.1 i).val]
  | _, .more lanes encoding queries rest, path =>
      let round := Whir.readRounds (Whir.transition E (.more lanes encoding queries rest))
        lanes 0 path.2
      let after := round.2.2.2
      (List.ofFn fun i : Fin queries => (after.2.2.2.1 i).val) ::
        whirQueries rest after.2.2.2.2

/-- Fixed public height and widths at each commitment occurrence. -/
def treeShapes {n : ℕ} (schedule : Whir.Schedule K n) (liveRows : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((baseLayout schedule liveRows).height, (baseLayout schedule liveRows).rowWords, (baseLayout schedule liveRows).leafWords) ::
    later schedule
where
  /-- Later encoded levels have three limbs per extension-field row. -/
  later : {n : ℕ} → Whir.Schedule K n → List (ℕ × ℕ × ℕ)
    | _, .last .. => []
    | _, .more _ _ _ rest =>
      ((extensionLayout rest).height, (extensionLayout rest).rowWords,
        (extensionLayout rest).leafWords) :: later rest

/-- A presentation has a fixed list of Merkle shapes along every public branch. -/
def Presentation.HasShapes : {original : Protocol} → Presentation original →
    List (ℕ × ℕ × ℕ) → Prop
  | _, .refine wire _, shapes => wire.HasShapes shapes
  | _, .done, shapes => shapes = []
  | _, @Presentation.sender _ _ _ _ next, shapes => ∀ move, (next move).HasShapes shapes
  | _, @Presentation.reveal _ _ _ _ _ next, shapes => next.HasShapes shapes
  | _, @Presentation.merkle _ _ _ _ layout next, shapes =>
      ∃ tail, shapes = (layout.height, layout.rowWords, layout.leafWords) :: tail ∧ next.HasShapes tail
  | _, @Presentation.announce _ _ _ _ _ next, shapes => ∀ move, (next move).HasShapes shapes
  | _, .grind _ next, shapes => next.HasShapes shapes
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, shapes => next.HasShapes shapes

/-- A fixed shape profile is preserved when presentations are appended. -/
theorem Presentation.HasShapes.append {first second : Protocol}
    (presentation : Presentation first) (suffix : Presentation second)
    {before after : List (ℕ × ℕ × ℕ)} (head : presentation.HasShapes before)
    (tail : suffix.HasShapes after) : (presentation.append suffix).HasShapes (before ++ after) := by
  induction presentation generalizing before with
  | refine wire projection ih => exact ih head
  | done => exact head ▸ tail
  | sender encode next ih => exact fun move => ih move (head move)
  | reveal encode next ih => exact ih head
  | merkle layout next ih =>
      obtain ⟨rest, rfl, shapes⟩ := head
      exact ⟨rest ++ after, rfl, ih shapes⟩
  | announce encode valid next ih => exact fun move => ih move (head move)
  | grind bits next ih => exact ih head
  | challenge move shape draw next ih => exact ih head

/-- Reading commitments realizes a presentation's fixed shape profile. -/
theorem Presentation.HasShapes.trees {original : Protocol} (presentation : Presentation original)
    {shapes : List (ℕ × ℕ × ℕ)} (fixed : presentation.HasShapes shapes)
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath)
    (openings : Openings) (offset : ℕ) :
    ((presentation.trees path openings offset).map
      (fun tree => (tree.height, tree.rowWords, tree.leafWords))) = shapes := by
  induction presentation generalizing shapes offset with
  | refine wire projection ih => exact ih fixed path offset
  | done => exact fixed.symm
  | sender encode next ih => exact ih path.1 (fixed path.1) path.2 offset
  | reveal encode next ih => exact ih fixed path.2 offset
  | merkle layout next ih =>
      obtain ⟨rest, rfl, shapes⟩ := fixed
      exact congrArg (List.cons (layout.height, layout.rowWords, layout.leafWords))
        (ih shapes path.2 (offset + 1))
  | announce encode valid next ih => exact ih path.1 (fixed path.1) path.2 offset
  | grind bits next ih => exact ih fixed path.2 offset
  | challenge move shape draw next ih => exact ih fixed path.2 offset

/-- Public scalar-round blocks introduce no additional commitments. -/
theorem whirRounds_shapes {tail : Protocol} (suffix : Presentation tail)
    {shapes : List (ℕ × ℕ × ℕ)} (fixed : suffix.HasShapes shapes) (rounds : ℕ) :
    (whirRounds suffix rounds).HasShapes shapes := by
  induction rounds with
  | zero => exact fixed
  | succ rounds ih => exact fun _ => ih

/-- WHIR commits precisely its successor encoded words, in schedule order. -/
theorem whirPresentation_shapes {n : ℕ} (schedule : Whir.Schedule K n) :
    (whirPresentation schedule).HasShapes (treeShapes.later schedule) := by
  change (whirWirePresentation schedule).HasShapes _
  induction schedule with
  | last lanes tail encoding queries =>
      apply whirRounds_shapes
      exact fun _ _ => whirRounds_shapes .done rfl tail
  | more lanes encoding queries rest ih =>
      apply whirRounds_shapes
      exact fun _ => ⟨_, rfl, fun _ _ => ih⟩

/-- Decode each committed word from the top-down Merkle extractor, preserving its occurrence
index and its base-field or extension-field leaf layout. -/
def Presentation.messages : {original : Protocol} → (presentation : Presentation original) →
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath) →
    (ℕ → ℕ → Option (List K)) → ℕ → ExtractedMessages presentation.coin path
  | _, .refine wire _, path, leaves, slot => wire.messages path leaves slot
  | _, .done, _, _, _ => fun index => nomatch index
  | _, @Presentation.sender _ _ _ _ next, path, leaves, slot => (next path.1).messages path.2 leaves slot
  | _, @Presentation.reveal _ _ _ _ _ next, path, leaves, slot => next.messages path.2 leaves slot
  | _, @Presentation.merkle _ _ _ _ layout next, path, leaves, slot => fun occurrence =>
      match occurrence with
      | .inl _ => layout.decode (leaves slot)
      | .inr occurrence => next.messages path.2 leaves (slot + 1) occurrence
  | _, @Presentation.announce _ _ _ _ _ next, path, leaves, slot => (next path.1).messages path.2 leaves slot
  | _, .grind _ next, path, leaves, slot => next.messages path.2 leaves slot
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, path, leaves, slot => next.messages path.2 leaves slot

end CompStark.Compiled
