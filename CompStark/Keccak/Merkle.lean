/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Refines
public import ToMathlib.Data.IndexedBinaryTree.Perfect
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Completeness
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Multi

/-! # Streaming, root-only Keccak Merkle commitments

Rows are packed little-endian 64-bit lanes. The caller supplies the complete leaf
image; lane permutations, zero prefixes and field encodings belong to the caller.
The binary-carry builder hashes each row as it arrives and retains its payload and
all internal nodes. A finished commitment owns this private data explicitly.
-/

@[expose] public section
namespace CompStark.Keccak.Merkle
open BinaryTree InductiveMerkleTree

/-- A complete leaf image, consisting of addressable, packed 64-bit lanes. -/
structure Row where
  bytes : ByteArray
  addressable : bytes.size < USize.size
  aligned : bytes.size % 8 = 0

/-- Pack words little-endian without assigning them a field interpretation. -/
def Row.ofWords (words : Array UInt64) (h : words.size * 8 < USize.size) : Row where
  bytes := ByteArray.mk (Array.ofFn (n := words.size * 8) fun i ↦
    (words[i.val / 8]! >>> ((i.val % 8) * 8).toUInt64).toUInt8)
  addressable := by simpa only [ByteArray.size, Array.size_ofFn] using h
  aligned := by simp only [ByteArray.size, Array.size_ofFn, Nat.mul_mod_left]

/-- A Keccak-256 digest, in its canonical byte order. -/
abbrev Digest := { bytes : ByteArray // bytes.size = 32 }

/-- Hash the complete leaf image. -/
def hashRow (row : Row) : Digest :=
  ⟨keccak256 row.bytes row.addressable, size_keccak256 ..⟩

/-- Hash left then right, with no protocol-specific framing. -/
def compress (left right : Digest) : Digest :=
  ⟨hashNode left.val right.val left.property right.property, by
    simp only [hashNode, size_keccak256]⟩

/-- The VCVio leaf hash. -/
def specHashRow (row : Row) : Digest :=
  ⟨VCVio.Algorithms.Keccak.keccak256 row.bytes,
    VCVio.Algorithms.Keccak.squeeze_size _ _⟩

/-- The VCVio internal-node hash. -/
def specCompress (left right : Digest) : Digest :=
  ⟨VCVio.Algorithms.Keccak.keccak256 (left.val ++ right.val),
    VCVio.Algorithms.Keccak.squeeze_size _ _⟩

@[simp] theorem hashRow_eq : hashRow = specHashRow := by
  funext row
  apply Subtype.ext
  exact keccak256_eq ..

@[simp] theorem compress_eq : compress = specCompress := by
  funext left right
  apply Subtype.ext
  exact hashNode_eq left.val right.val left.property right.property

/-- Cached perfect subtree and its retained payloads. The cache certificate is erased. -/
structure Tree (depth : Nat) where
  rows : LeafData Row (Skeleton.perfect depth)
  nodes : FullData Digest (Skeleton.perfect depth)
  correct : nodes = buildMerkleTreeWithHash (rows.map specHashRow) specCompress

/-- Public commitment; all other tree data is private prover output. -/
def Tree.root {depth : Nat} (tree : Tree depth) : Digest := tree.nodes.getRootValue

/-- Hash a row immediately. -/
def Tree.leaf (row : Row) : Tree 0 where
  rows := .leaf row
  nodes := .leaf (hashRow row)
  correct := by simp only [hashRow_eq]; rfl

/-- Join adjacent subtrees of the same height without rehashing their leaves. -/
def Tree.join {depth : Nat} (left right : Tree depth) : Tree (depth + 1) where
  rows := .internal left.rows right.rows
  nodes := .internal (compress left.root right.root) left.nodes right.nodes
  correct := by
    simp only [compress_eq, Tree.root, left.correct, right.correct]
    rfl

/-- Exact cache refinement, including every leaf and every internal digest. -/
theorem Tree.nodes_eq {depth : Nat} (tree : Tree depth) :
    tree.nodes = buildMerkleTreeWithHash (tree.rows.map specHashRow) specCompress :=
  tree.correct

/-- The public root is VCVio's root on the retained private payloads. -/
theorem Tree.root_eq {depth : Nat} (tree : Tree depth) :
    tree.root = (buildMerkleTreeWithHash (tree.rows.map specHashRow) specCompress).getRootValue :=
  congrArg FullData.getRootValue tree.correct

/-- An existentially sized completed subtree. -/
abbrev Subtree := (depth : Nat) × Tree depth

/-- Newest subtree first. Equal-height neighbors are merged by binary carry. -/
def carry (next : Subtree) : List Subtree → List Subtree
  | [] => [next]
  | prev :: rest =>
    if h : prev.1 = next.1 then
      carry ⟨next.1 + 1, Tree.join (h ▸ prev.2) next.2⟩ rest
    else next :: prev :: rest

/-- A stream of rows, with completed subtrees retained for openings. -/
structure Builder where
  forest : List Subtree := []

/-- Absorb one row and finish every newly completed subtree. -/
def Builder.absorbRow (builder : Builder) (row : Row) : Builder :=
  ⟨carry ⟨0, Tree.leaf row⟩ builder.forest⟩

/-- Absorb finished rows in order; successive calls can consume encoder tiles. -/
def Builder.absorb (builder : Builder) (rows : Array Row) : Builder :=
  rows.foldl Builder.absorbRow builder

/-- Finish only a nonempty power-of-two stream. -/
def Builder.finish (builder : Builder) : Except String Subtree :=
  match builder.forest with
  | [tree] => .ok tree
  | _ => .error "Merkle commitment requires a nonempty power-of-two row count"

/-- Commit a complete array, returning both root access and private tree data. -/
def commit (rows : Array Row) : Except String Subtree :=
  (Builder.absorb {} rows).finish

/-- Retained rows in left-to-right order. -/
def rowList : {s : Skeleton} → LeafData Row s → List Row
  | _, .leaf row => [row]
  | _, .internal left right => rowList left ++ rowList right

/-- The stream represented by a newest-first forest. -/
def forestRows (forest : List Subtree) : List Row :=
  forest.reverse.flatMap fun t ↦ rowList t.2.rows

/-- Carry preserves row order, including across tile boundaries. -/
theorem carry_rows (next : Subtree) (forest : List Subtree) :
    forestRows (carry next forest) = forestRows forest ++ rowList next.2.rows := by
  induction forest generalizing next with
  | nil => simp only [carry, forestRows, List.reverse_cons, List.reverse_nil,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil]
  | cons prev rest ih =>
    simp only [carry]
    split
    · rename_i h
      cases next with | mk n next =>
        cases prev with | mk k prev =>
          dsimp only at h
          subst k
          rw [ih]
          simp only [forestRows, List.reverse_cons, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, Tree.join, rowList,
            List.append_assoc]
    · simp only [forestRows, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Each absorbed row is appended exactly once to the private payload sequence. -/
theorem Builder.absorbRow_rows (builder : Builder) (row : Row) :
    forestRows (builder.absorbRow row).forest = forestRows builder.forest ++ [row] :=
  carry_rows _ _

/-- Encoder tiles append their rows in order, with no padding or omitted payloads. -/
theorem Builder.absorb_rows (builder : Builder) (rows : Array Row) :
    forestRows (builder.absorb rows).forest = forestRows builder.forest ++ rows.toList := by
  have aux (rs : List Row) (b : Builder) :
      forestRows (rs.foldl Builder.absorbRow b).forest = forestRows b.forest ++ rs := by
    induction rs generalizing b with
    | nil => simp only [List.foldl_nil, List.append_nil]
    | cons r rs ih =>
      rw [List.foldl_cons, ih, Builder.absorbRow_rows, List.append_assoc]
      rfl
  simpa only [Builder.absorb, Array.foldl_toList] using aux rows.toList builder

/-- Finishing exposes exactly the rows accumulated by the stream. -/
theorem Builder.finish_rows (builder : Builder) (tree : Subtree)
    (h : builder.finish = .ok tree) : rowList tree.2.rows = forestRows builder.forest := by
  cases builder with
  | mk forest =>
    cases forest with
    | nil => simp only [Builder.finish, reduceCtorEq] at h
    | cons t rest =>
      cases rest with
      | nil =>
        cases Except.ok.inj h
        simp only [forestRows, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      | cons u rest => simp only [Builder.finish, reduceCtorEq] at h

/-- Commitment preserves every input payload, in row order. -/
theorem commit_rows (rows : Array Row) (tree : Subtree) (h : commit rows = .ok tree) :
    rowList tree.2.rows = rows.toList := by
  rw [Builder.finish_rows _ _ h, Builder.absorb_rows]
  rfl

/-- Canonical query order: ascending and without duplicates. -/
def positions (queries : List Nat) : List Nat := queries.dedup.mergeSort (· ≤ ·)

/-- One root-only opening phase. Rows follow `positions`, siblings run bottom-up. -/
structure Opening where
  leafData : List Row
  siblingHashes : List Digest

/-- Cached authentication path, in bottom-up order. -/
def Tree.path {depth : Nat} (tree : Tree depth) (index : Nat) : List Digest :=
  (generateProof tree.nodes (SkeletonLeafIndex.ofNat depth index)).toList.reverse

/-- Canonical pruned opening; invalid and empty query sets are rejected. -/
def Tree.open {depth : Nat} (tree : Tree depth) (queries : List Nat) :
    Except String Opening :=
  if queries.isEmpty || !(queries.all (· < 2 ^ depth)) then
    .error "Merkle queries must be nonempty and within the committed domain"
  else
    let qs := positions queries
    .ok ⟨qs.map fun q ↦ tree.rows.get (SkeletonLeafIndex.ofNat depth q),
      MixedMerkleTree.prune ⟨ByteArray.mk (Array.replicate 32 0), by rfl⟩ depth qs
        (qs.map tree.path)⟩

/-- Every cached path equals VCVio's path on the retained payloads. -/
theorem Tree.path_eq {depth : Nat} (tree : Tree depth) (index : Nat) :
    tree.path index = (generateProof
      (buildMerkleTreeWithHash (tree.rows.map specHashRow) specCompress)
      (SkeletonLeafIndex.ofNat depth index)).toList.reverse := by
  rw [Tree.path, tree.correct]

/-- The complete sparse opening is VCVio's canonical pruning of its honest paths. -/
theorem Tree.open_eq {depth : Nat} (tree : Tree depth) (queries : List Nat)
    (hne : queries.isEmpty = false) (hin : queries.all (· < 2 ^ depth) = true) :
    tree.open queries = .ok ⟨(positions queries).map fun q ↦
        tree.rows.get (SkeletonLeafIndex.ofNat depth q),
      MixedMerkleTree.prune ⟨ByteArray.mk (Array.replicate 32 0), by rfl⟩ depth
        (positions queries) ((positions queries).map fun q ↦
          (generateProof (buildMerkleTreeWithHash (tree.rows.map specHashRow) specCompress)
            (SkeletonLeafIndex.ofNat depth q)).toList.reverse)⟩ := by
  simp only [Tree.open, hne, hin, Bool.not_true, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte]
  congr 3
  apply List.map_congr_left
  intro q _
  exact tree.path_eq q

/-- Check shape and consume the complete canonical bottom-up sibling stream. -/
def verify (depth : Nat) (root : Digest) (queries : List Nat) (opening : Opening) : Bool :=
  if queries.isEmpty || !(queries.all (· < 2 ^ depth)) then false else
  let qs := positions queries
  if opening.leafData.length != qs.length then false else
  let start := (qs.zip opening.leafData).zipIdx |>.map fun ((index, row), lead) ↦
    (index, lead, hashRow row)
  let result := MixedMerkleTree.walk hashRow compress
    ⟨ByteArray.mk (Array.replicate 32 0), by rfl⟩ (fun _ ↦ none) depth start
      opening.siblingHashes
  result.2.isEmpty && match result.1 with
    | [(index, _, digest)] => index == 0 && digest.val == root.val
    | _ => false

/-- Intrinsic batch opening for VCVio consumers, over the same retained cache. -/
def Tree.batchProof {depth : Nat} (tree : Tree depth)
    (selector : LeafData Bool (Skeleton.perfect depth)) (h : selector.anySelected = true) :
    BatchProof Digest selector := generateBatchProof tree.nodes selector h

/-- Every honest intrinsic multi-opening recomputes the commitment root. -/
theorem Tree.batch_complete {depth : Nat} (tree : Tree depth)
    (selector : LeafData Bool (Skeleton.perfect depth)) (h : selector.anySelected = true) :
    getPutativeBatchRootWithHash specCompress
      (selectedValues (tree.rows.map specHashRow) selector) (tree.batchProof selector h) =
        tree.root := by
  rw [Tree.batchProof, Tree.root, tree.correct]
  exact functional_batch_completeness _ _ _ _

end CompStark.Keccak.Merkle
