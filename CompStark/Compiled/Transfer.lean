/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Protocol

/-! Authentication preserves the exact sampled-column observations of the composed verifier. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Multilinear CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security
open StandardBcs

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

noncomputable section

/-- Parse the typed compiled path with a chosen complete leaf image at each commitment. -/
def Presentation.reconstruct : {original : Protocol} → (presentation : Presentation original) →
    (compile Commit.Digest presentation.coin).tree.ExecutionPath → Openings →
    (ℕ → TreeOpening → ℕ → Option (List K)) → ℕ → original.tree.ExecutionPath
  | _, .refine wire projection, path, openings, leaves, slot =>
      projection.path (wire.reconstruct path openings leaves slot)
  | _, .done, _, _, _, _ => PUnit.unit
  | _, @Presentation.sender _ _ _ _ next, path, openings, leaves, slot =>
      ⟨path.1, (next path.1).reconstruct path.2 openings leaves slot⟩
  | _, @Presentation.reveal _ _ _ _ _ next, path, openings, leaves, slot =>
      ⟨path.1, next.reconstruct path.2 openings leaves slot⟩
  | _, @Presentation.merkle _ _ _ _ layout next, path, openings, leaves, slot =>
      ⟨layout.decode (leaves slot
        ⟨path.1, layout.height, layout.rowWords, layout.leafWords, openingAt openings slot⟩),
        next.reconstruct path.2 openings leaves (slot + 1)⟩
  | _, @Presentation.announce _ _ _ _ _ next, path, openings, leaves, slot => (next path.1).reconstruct path.2 openings leaves slot
  | _, .grind _ next, path, openings, leaves, slot => next.reconstruct path.2 openings leaves slot
  | _, @Presentation.challenge _ _ _ _ _ move shape _ next, path, openings, leaves, slot =>
      ⟨move path.1, cast (congrArg (fun p : Protocol => p.tree.ExecutionPath)
        (shape path.1).symm) (next.reconstruct path.2 openings leaves slot)⟩

/-- The Merkle message extractor's parsed path is leaf-image reconstruction. -/
theorem Presentation.reconstruct_messages {original : Protocol} (presentation : Presentation original)
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath) (openings : Openings)
    (leaves : ℕ → ℕ → Option (List K)) (slot : ℕ) :
    presentation.originalPath (StandardBcs.extractedPath presentation.coin path
      (presentation.messages path leaves slot)) =
      presentation.reconstruct path openings (fun index _ => leaves index) slot := by
  induction presentation generalizing slot with
  | refine wire projection ih => exact congrArg projection.path (ih path slot)
  | done => rfl
  | sender encode next ih =>
      exact congrArg (Sigma.mk path.1) (ih path.1 path.2 slot)
  | reveal encode next ih =>
      exact congrArg (Sigma.mk path.1) (ih path.2 slot)
  | merkle layout next ih =>
      exact congrArg (Sigma.mk _) (ih path.2 (slot + 1))
  | announce encode valid next ih => exact ih path.1 path.2 slot
  | grind bits next ih => exact ih path.2 slot
  | challenge move shape draw next ih =>
      exact congrArg (Sigma.mk (move path.1)) (congrArg
        (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) (shape path.1).symm))
        (ih path.2 slot))

/-- The opening-based parsed path is reconstruction from the expanded authentication batches. -/
theorem Presentation.reconstruct_opened (hash : ByteArray → Commit.Digest) {original : Protocol}
    (presentation : Presentation original)
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath) (openings : Openings)
    (slot : ℕ) :
    presentation.originalPath (StandardBcs.extractedPath presentation.coin path
      (presentation.openedMessages hash path openings slot)) =
      presentation.reconstruct path openings (fun _ tree => tree.openedLeaves hash) slot := by
  induction presentation generalizing slot with
  | refine wire projection ih => exact congrArg projection.path (ih path slot)
  | done => rfl
  | sender encode next ih =>
      exact congrArg (Sigma.mk path.1) (ih path.1 path.2 slot)
  | reveal encode next ih =>
      exact congrArg (Sigma.mk path.1) (ih path.2 slot)
  | merkle layout next ih =>
      exact congrArg (Sigma.mk _) (ih path.2 (slot + 1))
  | announce encode valid next ih => exact ih path.1 path.2 slot
  | grind bits next ih => exact ih path.2 slot
  | challenge move shape draw next ih =>
      exact congrArg (Sigma.mk (move path.1)) (congrArg
        (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) (shape path.1).symm))
        (ih path.2 slot))

/-- Splitting an appended path commutes with protocol equality on its prefix. -/
theorem splitPath_transport {first next : Protocol} (equal : first = next) (second : Protocol)
    (path : (Compose.appendProtocol next second).tree.ExecutionPath) :
    Compose.splitPath first second (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath)
      (congrArg (fun p => Compose.appendProtocol p second) equal).symm) path) =
      (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) equal.symm)
        (Compose.splitPath next second path).1, (Compose.splitPath next second path).2) := by
  subst next
  rfl

/-- A prefix without Merkle words has the same public parse for every choice of leaf images. -/
theorem Presentation.append_split {first second : Protocol} (presentation : Presentation first)
    (suffix : Presentation second) (empty : presentation.HasShapes [])
    (path : (compile Commit.Digest (presentation.append suffix).coin).tree.ExecutionPath)
    (openings : Openings) (slot : ℕ) :
    ∃ head : first.tree.ExecutionPath,
      ∃ tail : (compile Commit.Digest suffix.coin).tree.ExecutionPath,
        (presentation.append suffix).trees path openings slot = suffix.trees tail openings slot ∧
        ∀ leaves, Compose.splitPath first second
          ((presentation.append suffix).reconstruct path openings leaves slot) =
            (head, suffix.reconstruct tail openings leaves slot) := by
  induction presentation generalizing slot with
  | refine wire projection ih =>
      obtain ⟨head, tail, trees, parsed⟩ := ih empty path slot
      refine ⟨projection.path head, tail, trees, fun leaves => ?_⟩
      exact (projection.splitPath_append second _).trans
        (congrArg (fun pair => (projection.path pair.1, pair.2)) (parsed leaves))
  | done => exact ⟨PUnit.unit, path, rfl, fun _ => rfl⟩
  | @sender Moves inst rest encode next ih =>
      obtain ⟨head, tail, trees, parsed⟩ := ih path.1 (empty path.1) path.2 slot
      refine ⟨⟨path.1, head⟩, tail, trees, fun leaves => ?_⟩
      exact congrArg (fun pair : (rest path.1).tree.ExecutionPath × second.tree.ExecutionPath =>
        ((Sigma.mk path.1 pair.1 : (Protocol.public .sender Moves rest).tree.ExecutionPath), pair.2)) (parsed leaves)
  | @reveal Messages inst interface rest encode next ih =>
      obtain ⟨head, tail, trees, parsed⟩ := ih empty path.2 slot
      refine ⟨⟨path.1, head⟩, tail, trees, fun leaves => ?_⟩
      exact congrArg (fun pair : rest.tree.ExecutionPath × second.tree.ExecutionPath =>
        ((Sigma.mk path.1 pair.1 : (Protocol.oracleWith Messages interface rest).tree.ExecutionPath), pair.2))
        (parsed leaves)
  | merkle layout next ih => obtain ⟨rest, impossible, _⟩ := empty; cases impossible
  | announce encode valid next ih => exact ih path.1 (empty path.1) path.2 slot
  | grind bits next ih => exact ih empty path.2 slot
  | @challenge Challenge Moves inst rest tailProtocol move shape draw next ih =>
      obtain ⟨head, tail, trees, parsed⟩ := ih empty path.2 slot
      refine ⟨⟨move path.1, cast (congrArg (fun p : Protocol => p.tree.ExecutionPath)
        (shape path.1).symm) head⟩, tail, trees, fun leaves => ?_⟩
      have transported := splitPath_transport (shape path.1) second
        ((next.append suffix).reconstruct path.2 openings leaves slot)
      have same := transported.trans (congrArg (fun pair =>
        (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) (shape path.1).symm)
          pair.1, pair.2)) (parsed leaves))
      exact congrArg (fun pair : (rest (move path.1)).tree.ExecutionPath × second.tree.ExecutionPath =>
        ((Sigma.mk (move path.1) pair.1 : (Protocol.public .receiver Moves rest).tree.ExecutionPath), pair.2)) same


/-- A presentation without Merkle words is independent of the reconstructed leaf images. -/
theorem Presentation.reconstruct_eq_of_no_merkle {original : Protocol}
    (presentation : Presentation original) (empty : presentation.HasShapes [])
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath) (openings : Openings)
    (first second : ℕ → TreeOpening → ℕ → Option (List K)) (slot : ℕ) :
    presentation.reconstruct path openings first slot =
      presentation.reconstruct path openings second slot := by
  induction presentation generalizing slot with
  | refine wire projection ih => exact congrArg projection.path (ih empty path slot)
  | done => rfl
  | sender encode next ih => exact congrArg (Sigma.mk path.1) (ih path.1 (empty path.1) path.2 slot)
  | reveal encode next ih => exact congrArg (Sigma.mk path.1) (ih empty path.2 slot)
  | merkle layout next ih => obtain ⟨rest, impossible, _⟩ := empty; cases impossible
  | announce encode valid next ih => exact ih path.1 (empty path.1) path.2 slot
  | grind bits next ih => exact ih empty path.2 slot
  | challenge move shape draw next ih =>
      exact congrArg (Sigma.mk (move path.1))
        (congrArg (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) (shape path.1).symm))
        (ih empty path.2 slot))

/-- Parsing scalar rounds exposes a leaf-independent prefix and the compiled suffix. -/
theorem whirRounds_split {rest : Protocol} (suffix : Presentation rest) (rounds : ℕ)
    (path : (compile Commit.Digest (whirRounds suffix rounds).coin).tree.ExecutionPath)
    (openings : Openings) (slot : ℕ) :
    ∃ tail : (compile Commit.Digest suffix.coin).tree.ExecutionPath,
      ∃ prepare : E → E × (Fin rounds → E) × Bool,
        (whirRounds suffix rounds).trees path openings slot = suffix.trees tail openings slot ∧
        ∀ leaves current, Whir.readRounds rest rounds current
          ((whirRounds suffix rounds).reconstruct path openings leaves slot) =
            ((prepare current).1, (prepare current).2.1, (prepare current).2.2,
              suffix.reconstruct tail openings leaves slot) := by
  induction rounds with
  | zero => exact ⟨path, fun current => (current, Fin.elim0, true), rfl, fun _ _ => rfl⟩
  | succ rounds ih =>
      obtain ⟨tail, prepare, trees, parsed⟩ := ih path.2.2
      refine ⟨tail, (fun current =>
        let result := prepare (Whir.evalQuadratic current path.1 path.2.1)
        (result.1, Fin.cons (α := fun _ => E) path.2.1 result.2.1,
          (Sumcheck.compressedOps 1).accept current path.1 && result.2.2)),
        trees, ?_⟩
      intro leaves current
      exact congrArg (fun result : E × (Fin rounds → E) × Bool × rest.tree.ExecutionPath =>
        (result.1, Fin.cons (α := fun _ => E) path.2.1 result.2.1,
          (Sumcheck.compressedOps 1).accept current path.1 && result.2.2.1,
          result.2.2.2)) (parsed leaves (Whir.evalQuadratic current path.1 path.2.1))


set_option maxHeartbeats 1600000

/-- Fold parsing projects the final lookahead away while retaining it for the boundary. -/
theorem foldProjection_split {source target : Protocol} (suffix : Presentation source)
    (first : Whir.Quadratic E → Whir.Quadratic E)
    (project : Whir.Quadratic E → Projection source target) (rounds : ℕ)
    (path : (compile Commit.Digest
      (whirRounds (.sender quadraticEvents fun _ => suffix) rounds).coin).tree.ExecutionPath)
    (openings : Openings) (slot : ℕ) :
    ∃ residual : Whir.Quadratic E,
      ∃ tail : (compile Commit.Digest suffix.coin).tree.ExecutionPath,
        ∃ prepare : E → E × (Fin rounds → E) × Bool,
          (whirRounds (.sender quadraticEvents fun _ => suffix) rounds).trees path openings slot =
            suffix.trees tail openings slot ∧
          ∀ leaves current, Whir.readRounds target rounds current
            ((foldProjection first project rounds).path
              ((whirRounds (.sender quadraticEvents fun _ => suffix) rounds).reconstruct
                path openings leaves slot)) =
              ((prepare current).1, (prepare current).2.1, (prepare current).2.2,
                (project residual).path (suffix.reconstruct tail openings leaves slot)) := by
  induction rounds generalizing first with
  | zero => exact ⟨path.1, path.2, fun current => (current, Fin.elim0, true), rfl, fun _ _ => rfl⟩
  | succ rounds ih =>
      obtain ⟨residual, tail, prepare, trees, parsed⟩ := ih id path.2.2
      refine ⟨residual, tail, (fun current =>
        let result := prepare (Whir.evalQuadratic current (first path.1) path.2.1)
        (result.1, Fin.cons (α := fun _ => E) path.2.1 result.2.1,
          (Sumcheck.compressedOps 1).accept current (first path.1) && result.2.2)), trees, ?_⟩
      intro leaves current
      exact congrArg (fun result : E × (Fin rounds → E) × Bool × target.tree.ExecutionPath =>
        (result.1, Fin.cons (α := fun _ => E) path.2.1 result.2.1,
          (Sumcheck.compressedOps 1).accept current (first path.1) && result.2.2.1,
          result.2.2.2)) (parsed leaves (Whir.evalQuadratic current (first path.1) path.2.1))

/-- The sumcheck parser's challenges and suffix do not depend on its initial running value. -/
theorem readRounds_public (rest : Protocol) (rounds : ℕ) (first second : E)
    (path : (Whir.scalarRounds E rounds rest).tree.ExecutionPath) :
    (Whir.readRounds rest rounds first path).2.1 = (Whir.readRounds rest rounds second path).2.1 ∧
      (Whir.readRounds rest rounds first path).2.2.2 =
        (Whir.readRounds rest rounds second path).2.2.2 := by
  induction rounds generalizing first second with
  | zero => exact ⟨rfl, rfl⟩
  | succ rounds ih =>
      have same := ih (Whir.evalQuadratic first path.1 path.2.1)
        (Whir.evalQuadratic second path.1 path.2.1) path.2.2
      exact ⟨congrArg (Fin.cons (α := fun _ => E) path.2.1) same.1, same.2⟩

/-- A folded masked oracle reads only the specified column, preserving its zero default. -/
theorem foldWord_congr {lanes columns : ℕ} (first second : Whir.MaskedWord E lanes columns)
    (point : Fin lanes → E) (column : Fin columns)
    (same : first column = second column) :
    (Whir.foldMaskedWord first point column).getD 0 =
      (Whir.foldMaskedWord second point column).getD 0 := by
  exact congrArg (fun value => (value.map (fun rows => Whir.mle rows point)).getD 0) same

/-- Query availability depends only on the masks of the sampled columns. -/
theorem queriesKnown_congr {lanes columns queries : ℕ}
    (first second : Whir.MaskedWord E lanes columns) (xs : Fin queries → Fin columns)
    (same : ∀ q, first (xs q) = second (xs q)) :
    Whir.queriesKnown first xs = Whir.queriesKnown second xs := by
  apply Bool.eq_iff_iff.mpr
  rw [Whir.queriesKnown_iff, Whir.queriesKnown_iff]
  constructor
  · intro h q
    rw [← same q]
    exact h q
  · intro h q
    rw [same q]
    exact h q

/-- The base-field leaf decoder preserves equality of an entire sampled masked column. -/
theorem baseLayout_congr {n : ℕ} (schedule : Whir.Schedule K n) (liveRows : ℕ)
    (first second : ℕ → Option (List K)) (column : Fin schedule.columns)
    (same : first column.val = second column.val) :
    (baseLayout schedule liveRows).decode first column =
      (baseLayout schedule liveRows).decode second column := by
  change (first column.val).map _ = (second column.val).map _
  rw [same]

/-- The extension-field decoder preserves the complete sampled masked column. -/
theorem extensionLayout_congr {n : ℕ} (schedule : Whir.Schedule K n)
    (first second : ℕ → Option (List K)) (column : Fin schedule.columns)
    (same : first column.val = second column.val) :
    (extensionLayout schedule).decode first column =
      (extensionLayout schedule).decode second column := by
  change (first column.val).map _ = (second column.val).map _
  rw [same]

/-- An accepted batch without disagreement returns the extractor's leaf at every named query. -/
theorem TreeOpening.openedLeaves_eq_extracted {Coins : Type} (A : Commit.Adversary Coins)
    (X : MixedMerkleTree.Knowledge.ExtractorMap Coins (List K) Commit.Digest)
    (tree : TreeOpening) (c : Coins)
    (output : A c = (tree.root, tree.opening.queries, tree.opening.batch))
    (accepted : tree.accepts Commit.hash)
    (agreement : ¬ Commit.Disagree Commit.hash tree.height tree.rowWords tree.leafWords A X c)
    (index : ℕ) (queried : index ∈ tree.opening.queries) :
    tree.openedLeaves Commit.hash index = Commit.maskedLeaves Commit.hash tree.height tree.rowWords tree.leafWords A X c index := by
  change Commit.accepts Commit.hash tree.height tree.rowWords tree.leafWords tree.opening.queries
    tree.opening.batch tree.root = true at accepted
  cases expanded : Commit.expand Commit.hash tree.height tree.rowWords tree.leafWords
      tree.opening.queries tree.opening.batch with
  | none =>
      simp only [Commit.accepts, expanded] at accepted
      cases accepted
  | some pair =>
      obtain ⟨digest, paths⟩ := pair
      have same : digest = tree.root := by
        simpa only [Commit.accepts, expanded, beq_iff_eq] using accepted
      subst digest
      have indices := (Commit.accepted_openings_verify Commit.hash _ _ _ _ _ _ paths expanded).1
      obtain ⟨path, member, position⟩ := List.mem_map.mp (indices.symm ▸ queried)
      have found : (paths.find? (fun p => p.index == index)).isSome :=
        List.find?_isSome.mpr ⟨path, member, beq_iff_eq.mpr position⟩
      obtain ⟨selected, selected_eq⟩ := Option.isSome_iff_exists.mp found
      have selected_mem := List.mem_of_find?_eq_some selected_eq
      have selected_pred : (selected.index == index) = true := List.find?_some (p := fun p : Commit.Path => p.index == index) (a := selected) selected_eq
      have selected_index : selected.index = index := beq_iff_eq.mp selected_pred
      have leaf : Commit.maskedLeaves Commit.hash tree.height tree.rowWords tree.leafWords A X c
          selected.index = some selected.leaf := by
        by_contra different
        apply agreement
        refine ⟨?_, selected.toMixed, ?_, different⟩
        · simpa only [output] using accepted
        · simpa only [Commit.mixedAdversary, output, expanded] using
            List.mem_map.mpr ⟨selected, selected_mem, rfl⟩
      simpa only [TreeOpening.openedLeaves, expanded, selected_eq, Option.map_some,
        selected_index] using leaf.symm

/-- Each commitment reads the authentication batch at its exact sequential offset. -/
theorem Presentation.trees_openingAt {original : Protocol} (presentation : Presentation original)
    (path : (compile Commit.Digest presentation.coin).tree.ExecutionPath) (openings : Openings)
    (offset index : ℕ) (bound : index < (presentation.trees path openings offset).length) :
    ((presentation.trees path openings offset)[index]).opening = openingAt openings (offset + index) := by
  induction presentation generalizing offset index with
  | refine wire projection ih => exact ih path offset index bound
  | done => cases bound
  | sender encode next ih => exact ih path.1 path.2 offset index bound
  | reveal encode next ih => exact ih path.2 offset index bound
  | merkle layout next ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have tailBound : index < (next.trees path.2 openings (offset + 1)).length :=
            Nat.lt_of_succ_lt_succ bound
          have tail := ih path.2 (offset + 1) index tailBound
          change ((next.trees path.2 openings (offset + 1))[index]'tailBound).opening =
            openingAt openings (offset + (index + 1))
          rw [show offset + (index + 1) = offset + 1 + index by omega]
          exact tail
  | announce encode valid next ih => exact ih path.1 path.2 offset index bound
  | grind bits next ih => exact ih path.2 offset index bound
  | challenge move shape draw next ih => exact ih path.2 offset index bound

/-- Each listed tree's sampled columns agree under two complete leaf-image assignments. -/
def LeafAgreement (first second : ℕ → TreeOpening → ℕ → Option (List K)) : ℕ → List TreeOpening → Prop
  | _, [] => True
  | slot, tree :: rest =>
      (∀ index ∈ tree.opening.queries, first slot tree index = second slot tree index) ∧
        LeafAgreement first second (slot + 1) rest

/-- Pointwise agreement at sequential tree indices gives the recursive agreement invariant. -/
theorem LeafAgreement.of_forall (first second : ℕ → TreeOpening → ℕ → Option (List K))
    (trees : List TreeOpening) (offset : ℕ)
    (agree : ∀ index (bound : index < trees.length), ∀ query ∈ trees[index].opening.queries,
      first (offset + index) trees[index] query = second (offset + index) trees[index] query) :
    LeafAgreement first second offset trees := by
  induction trees generalizing offset with
  | nil => trivial
  | cons tree rest ih =>
      refine ⟨agree 0 (Nat.zero_lt_succ _), ih (offset + 1) ?_⟩
      intro index bound query member
      have result := agree (index + 1) (Nat.succ_lt_succ bound) query member
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result

set_option maxHeartbeats 1600000

/-- Reconstruct the ideal WHIR path after retaining the production boundary state. -/
def whirReconstruct {n : ℕ} (schedule : Whir.Schedule K n)
    (combine : E → Whir.Quadratic E → Whir.Quadratic E)
    (path : (compile Commit.Digest (whirWirePresentation schedule).coin).tree.ExecutionPath)
    (openings : Openings) (leaves : ℕ → TreeOpening → ℕ → Option (List K)) (slot : ℕ) :
    (Whir.opening E schedule).tree.ExecutionPath :=
  (whirProjection schedule combine).path
    ((whirWirePresentation schedule).reconstruct path openings leaves slot)

/-- Authentication preserves WHIR acceptance for every retained boundary combination. -/
theorem whirLevel_accepts_congr {n : ℕ} (schedule : Whir.Schedule K n)
    (combine : E → Whir.Quadratic E → Whir.Quadratic E)
    (path : (compile Commit.Digest (whirWirePresentation schedule).coin).tree.ExecutionPath)
    (openings : Openings) (first second : ℕ → TreeOpening → ℕ → Option (List K)) (slot : ℕ)
    (word₁ word₂ : Whir.oracleMessage E schedule) (claims : List (Whir.Claim E n))
    (headQueries : List ℕ)
    (queryLists : headQueries :: ((whirWirePresentation schedule).trees path openings slot).map
      (fun tree => tree.opening.queries) = whirQueries schedule
        (whirReconstruct schedule combine path openings first slot))
    (headAgreement : ∀ column : Fin schedule.columns, column.val ∈ headQueries →
      word₁ column = word₂ column)
    (agreement : LeafAgreement first second slot
      ((whirWirePresentation schedule).trees path openings slot)) :
    Whir.accepts (algebraMap K E) schedule word₁ claims
      (whirReconstruct schedule combine path openings first slot) =
    Whir.accepts (algebraMap K E) schedule word₂ claims
      (whirReconstruct schedule combine path openings second slot) := by
  induction schedule generalizing slot headQueries combine with
  | last lanes tail encoding queries =>
      let suffix : Presentation (whirWireTransition (.last lanes tail encoding queries)) :=
        .sender (fun table => fieldEvents fun i : Fin (2 ^ tail) =>
          table (fun bit => i.val.testBit bit.val)) (fun _ =>
            .grind 17 (.challenge id (fun _ => rfl) (queryDraw queries (tail + encoding.rate))
              (.challenge id (fun _ => rfl) scalarDraw (whirRounds .done tail))))
      obtain ⟨residual, after, prepare, _, parsed⟩ := foldProjection_split suffix (combine path.1)
        (whirBoundaryProjection (.last lanes tail encoding queries)) lanes path.2 openings slot
      let current := (Whir.batch claims path.1).value
      let round := prepare current
      let xs : Fin queries → encoding.Columns := after.2.2.1
      have queries_eq : headQueries = List.ofFn (fun i : Fin queries => (xs i).val) := by
        change headQueries :: _ = [List.ofFn (fun i : Fin queries =>
          ((Whir.readRounds _ lanes 0 ((foldProjection (combine path.1)
            (whirBoundaryProjection (.last lanes tail encoding queries)) lanes).path
              ((whirRounds (.sender quadraticEvents fun _ => suffix) lanes).reconstruct
                path.2 openings first slot))).2.2.2.2.1 i).val)] at queryLists
        rw [parsed] at queryLists
        exact (List.cons.inj queryLists).1
      have known := queriesKnown_congr word₁ word₂ xs (fun i =>
        headAgreement (xs i) (queries_eq ▸ List.mem_ofFn.mpr ⟨i, rfl⟩))
      have samples : (List.ofFn (fun i : Fin queries =>
          (⟨fun u => (algebraMap K E) (encoding.weight (xs i) u),
            (Whir.foldMaskedWord word₁ round.2.1 (xs i)).getD 0⟩ : Whir.Claim E tail))) =
          List.ofFn (fun i : Fin queries =>
          (⟨fun u => (algebraMap K E) (encoding.weight (xs i) u),
            (Whir.foldMaskedWord word₂ round.2.1 (xs i)).getD 0⟩ : Whir.Claim E tail)) := by
        apply congrArg List.ofFn
        funext i
        apply congrArg (fun value => (⟨fun u => (algebraMap K E) (encoding.weight (xs i) u), value⟩ : Whir.Claim E tail))
        exact foldWord_congr _ _ _ _ (headAgreement (xs i)
          (queries_eq ▸ List.mem_ofFn.mpr ⟨i, rfl⟩))
      have suffix_eq := suffix.reconstruct_eq_of_no_merkle
        (fun _ => whirRounds_shapes .done rfl tail) after openings first second slot
      change Whir.accepts (algebraMap K E) (.last lanes tail encoding queries) word₁ claims ⟨path.1, _⟩ =
        Whir.accepts (algebraMap K E) (.last lanes tail encoding queries) word₂ claims ⟨path.1, _⟩
      simp only [Whir.accepts.eq_1]
      erw [parsed first current, parsed second current]
      rw [← suffix_eq]
      exact congrArg₂ (fun available (sampled : List (Whir.Claim E tail)) =>
        let boundary := (whirBoundaryProjection (.last lanes tail encoding queries) residual).path
          (suffix.reconstruct after openings first slot)
        let finalBatch := Whir.batch
          ((⟨Whir.restrict (Whir.batch claims path.1).weight round.2.1, round.1⟩ : Whir.Claim E tail) :: sampled)
          boundary.2.2.1
        let closing := Whir.readRounds .done tail finalBatch.value boundary.2.2.2
        round.2.2 && available && closing.2.2.1 &&
          decide (Whir.mle finalBatch.weight closing.2.1 * Whir.mle boundary.1 closing.2.1 = closing.1)) known samples
  | @more tail lanes encoding queries rest ih =>
      let suffix : Presentation (whirWireTransition (.more lanes encoding queries rest)) :=
        .merkle (extensionLayout rest)
          (.challenge id (fun _ => rfl) (vectorDraw tail)
            (.sender (fun value => fieldEvents ![value]) (fun _ =>
              .sender quadraticEvents fun _ =>
                .grind 17 (.challenge id (fun _ => rfl) (queryDraw queries (tail + encoding.rate))
                  (whirWirePresentation rest)))))
      obtain ⟨residualPair, after, prepare, tree_eq, parsed⟩ := foldProjection_split suffix (combine path.1)
        (whirBoundaryProjection (.more lanes encoding queries rest)) lanes path.2 openings slot
      let nextTree : TreeOpening := ⟨after.1, (extensionLayout rest).height,
        (extensionLayout rest).rowWords, (extensionLayout rest).leafWords, openingAt openings slot⟩
      let nextPath := after.2.2.2.2.2.2
      let nextCombine := fun lam query => combineQuadratic residualPair after.2.2.2.1 query lam
      let current := (Whir.batch claims path.1).value
      let round := prepare current
      let xs : Fin queries → encoding.Columns := after.2.2.2.2.2.1
      let residual : Whir.Claim E tail := ⟨Whir.restrict (Whir.batch claims path.1).weight round.2.1, round.1⟩
      let newClaims₁ := Whir.nextClaims encoding (algebraMap K E) residual after.2.1 after.2.2.1 xs
        (fun x => (Whir.foldMaskedWord word₁ round.2.1 x).getD 0)
      let newClaims₂ := Whir.nextClaims encoding (algebraMap K E) residual after.2.1 after.2.2.1 xs
        (fun x => (Whir.foldMaskedWord word₂ round.2.1 x).getD 0)
      change headQueries :: ((whirRounds (.sender quadraticEvents fun _ => suffix) lanes).trees
        path.2 openings slot).map _ = _ at queryLists
      rw [tree_eq] at queryLists
      change headQueries :: nextTree.opening.queries ::
        ((whirWirePresentation rest).trees nextPath openings (slot + 1)).map (fun tree => tree.opening.queries) =
        List.ofFn (fun i : Fin queries =>
          ((Whir.readRounds _ lanes 0 ((foldProjection (combine path.1)
            (whirBoundaryProjection (.more lanes encoding queries rest)) lanes).path
              ((whirRounds (.sender quadraticEvents fun _ => suffix) lanes).reconstruct
                path.2 openings first slot))).2.2.2.2.2.2.1 i).val) ::
          whirQueries rest
            (Whir.readRounds _ lanes 0 ((foldProjection (combine path.1)
              (whirBoundaryProjection (.more lanes encoding queries rest)) lanes).path
                ((whirRounds (.sender quadraticEvents fun _ => suffix) lanes).reconstruct
                  path.2 openings first slot))).2.2.2.2.2.2.2 at queryLists
      rw [parsed] at queryLists
      have queries_eq : headQueries = List.ofFn (fun i : Fin queries => (xs i).val) :=
        (List.cons.inj queryLists).1
      have tailQueries : nextTree.opening.queries ::
          ((whirWirePresentation rest).trees nextPath openings (slot + 1)).map (fun tree => tree.opening.queries) =
          whirQueries rest (whirReconstruct rest nextCombine nextPath openings first (slot + 1)) :=
        (List.cons.inj queryLists).2
      have known := queriesKnown_congr word₁ word₂ xs (fun i =>
        headAgreement (xs i) (queries_eq ▸ List.mem_ofFn.mpr ⟨i, rfl⟩))
      have columns (i : Fin queries) : (Whir.foldMaskedWord word₁ round.2.1 (xs i)).getD 0 =
          (Whir.foldMaskedWord word₂ round.2.1 (xs i)).getD 0 := foldWord_congr _ _ _ _
            (headAgreement (xs i) (queries_eq ▸ List.mem_ofFn.mpr ⟨i, rfl⟩))
      have sameClaims : newClaims₁ = newClaims₂ := by
        apply congrArg (fun sampled : List (Whir.Claim E tail) =>
          residual :: (⟨Whir.eqWeight after.2.1, after.2.2.1⟩ : Whir.Claim E tail) :: sampled)
        apply congrArg List.ofFn
        funext i
        exact congrArg (fun value => (⟨fun u => (algebraMap K E) (encoding.weight (xs i) u), value⟩ : Whir.Claim E tail))
          (columns i)
      change LeafAgreement first second slot
        ((whirRounds (.sender quadraticEvents fun _ => suffix) lanes).trees path.2 openings slot) at agreement
      have agreement := (congrArg (LeafAgreement first second slot) tree_eq).mp agreement
      change (∀ index ∈ nextTree.opening.queries, first slot nextTree index = second slot nextTree index) ∧
        LeafAgreement first second (slot + 1) ((whirWirePresentation rest).trees nextPath openings (slot + 1)) at agreement
      have rest_eq := ih nextCombine nextPath (slot + 1)
        ((extensionLayout rest).decode (first slot nextTree))
        ((extensionLayout rest).decode (second slot nextTree)) newClaims₂ nextTree.opening.queries
        tailQueries (fun column member => extensionLayout_congr rest _ _ column
          (agreement.1 column.val member)) agreement.2
      change Whir.accepts (algebraMap K E) (.more lanes encoding queries rest) word₁ claims ⟨path.1, _⟩ =
        Whir.accepts (algebraMap K E) (.more lanes encoding queries rest) word₂ claims ⟨path.1, _⟩
      simp only [Whir.accepts.eq_2]
      erw [parsed first current, parsed second current]
      change (round.2.2 && Whir.queriesKnown word₁ xs && Whir.accepts (algebraMap K E) rest
        ((extensionLayout rest).decode (first slot nextTree)) newClaims₁
        (whirReconstruct rest nextCombine nextPath openings first (slot + 1))) = _
      rw [sameClaims, known]
      exact congrArg (Bool.and (round.2.2 && Whir.queriesKnown word₂ xs)) rest_eq

/-- WHIR acceptance depends on complete rows only at the authenticated sampled columns. -/
theorem whir_accepts_congr {n : ℕ} (schedule : Whir.Schedule K n)
    (path : (compile Commit.Digest (whirPresentation schedule).coin).tree.ExecutionPath)
    (openings : Openings) (first second : ℕ → TreeOpening → ℕ → Option (List K)) (slot : ℕ)
    (word₁ word₂ : Whir.oracleMessage E schedule) (claims : List (Whir.Claim E n))
    (headQueries : List ℕ)
    (queryLists : headQueries :: ((whirPresentation schedule).trees path openings slot).map
      (fun tree => tree.opening.queries) = whirQueries schedule
        ((whirPresentation schedule).reconstruct path openings first slot))
    (headAgreement : ∀ column : Fin schedule.columns, column.val ∈ headQueries →
      word₁ column = word₂ column)
    (agreement : LeafAgreement first second slot
      ((whirPresentation schedule).trees path openings slot)) :
    Whir.accepts (algebraMap K E) schedule word₁ claims
      ((whirPresentation schedule).reconstruct path openings first slot) =
    Whir.accepts (algebraMap K E) schedule word₂ claims
      ((whirPresentation schedule).reconstruct path openings second slot) :=
  whirLevel_accepts_congr schedule (fun _ => id) path openings first second slot word₁ word₂ claims
    headQueries queryLists headAgreement agreement

end
end CompStark.Compiled
