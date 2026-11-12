/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.Commit.Merkle
meta import Mathlib.Tactic.DSimpPercent
/-! Shared-sibling reconstruction with a certified scalar sponge throughout each hash. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Keccak.Commit.Scalar
open CompStark.BinaryFields
/-- Retain scalar lanes on addressable arrays; oversized mathematical arrays use total absorption. -/
def hashBytes (bytes : ByteArray) : ByteArray :=
  if h : bytes.size < USize.size then CompStark.Keccak.keccak256 bytes h
  else CompStark.Keccak.hashNative bytes
/-- Addressable hashing and the total mathematical hash have identical digest bytes. -/
theorem hashBytes_eq (bytes : ByteArray) : hashBytes bytes = VCVio.Algorithms.Keccak.keccak256 bytes := by
  unfold hashBytes
  split_ifs with sized
  · exact CompStark.Keccak.keccak256_eq bytes sized
  · rw [CompStark.Keccak.hash_native]
/-- Return the fixed-width scalar sponge digest without rebuilding a lane array per block. -/
def hash (bytes : ByteArray) : Digest :=
  ⟨(hashBytes bytes).data, by rw [hashBytes_eq]; exact VCVio.Algorithms.Keccak.squeeze_size _ _⟩
/-- Scalar hashing preserves the complete canonical digest. -/
theorem hash_eq (bytes : ByteArray) : hash bytes = Keccak.Commit.hash bytes := by
  apply Vector.ext
  intro i hi
  simp only [hash, Keccak.Commit.hash, hashBytes_eq]
/-- Hash the complete opened leaf image with scalar sponge lanes. -/
def hashLeaf (xs : List K) : Digest := hash (leafBytes xs)
/-- Leaf hashing preserves every byte of every supplied leaf. -/
@[csimp] theorem hashLeaf_code : Keccak.Commit.hashLeaf = hashLeaf := by
  funext xs
  exact (hash_eq _).symm
/-- Hash a binary node's canonical ordered concatenation with scalar sponge lanes. -/
def compress (left right : Digest) : Digest := hash ⟨left.toArray ++ right.toArray⟩
/-- Scalar node hashing preserves the ordered binary-tree digest. -/
@[csimp] theorem compress_code : Keccak.Commit.compress = compress := by
  funext left right
  exact (hash_eq _).symm
/-- Expand one shared-sibling level with scalar node hashing. -/
def expandLevelScalar : ℕ → List (ℕ × Digest) → List Digest →
    Option (List (ℕ × Digest) × List (ℕ × Digest) × List Digest)
  | _, [], hints => some ([], [], hints)
  | 0, _ :: _, _ => none
  | fuel + 1, (i, x) :: rest, hints => do
      match rest with
      | (j, y) :: tail =>
        if i % 2 = 0 ∧ j = i + 1 then
          let (parents, siblings, unused) ← expandLevelScalar fuel tail hints
          pure ((i / 2, compress x y) :: parents, (i, y) :: (j, x) :: siblings, unused)
        else
          let sibling ← hints.head?
          let (parents, siblings, unused) ← expandLevelScalar fuel rest hints.tail
          pure ((i / 2, MixedMerkleTree.pairUp compress i x sibling) :: parents,
            (i, sibling) :: siblings, unused)
      | [] =>
        let sibling ← hints.head?
        pure ([(i / 2, MixedMerkleTree.pairUp compress i x sibling)], [(i, sibling)], hints.tail)

/-- Scalar node hashing is the generic pair hash at Keccak-256. -/
theorem compress_eq : compress = pairWith Keccak.Commit.hash := by
  funext left right
  exact hash_eq _

/-- Scalar leaf hashing is the generic leaf hash at Keccak-256. -/
theorem hashLeaf_eq : hashLeaf = leafWith Keccak.Commit.hash := by
  funext xs
  exact hash_eq _

/-- Scalar expansion retains every parent, sibling and unused hint, including failures. -/
theorem expandLevelScalar_eq (fuel : Nat) (nodes : List (Nat × Digest)) (hints : List Digest) :
    expandLevelScalar fuel nodes hints = expandLevel Keccak.Commit.hash fuel nodes hints := by
  induction fuel generalizing nodes hints with
  | zero => cases nodes <;> rfl
  | succ fuel ih =>
    cases nodes with
    | nil => rfl
    | cons head rest =>
      rcases head with ⟨i, x⟩
      cases rest with
      | nil => simp only [expandLevelScalar.eq_4, expandLevel.eq_4, compress_eq]
      | cons next tail =>
        rcases next with ⟨j, y⟩
        simp only [expandLevelScalar.eq_3, expandLevel.eq_3, ih, compress_eq]

/-- Expand successive shared-sibling levels with scalar node hashing. -/
def expandLevelsScalar : ℕ → ℕ → List (ℕ × Digest) → List Path → List Digest →
    Option (List (ℕ × Digest) × List Path × List Digest)
  | 0, _, nodes, paths, hints => some (nodes, paths, hints)
  | remaining + 1, level, nodes, paths, hints => do
      let (parents, siblings, unused) ← expandLevelScalar nodes.length nodes hints
      let paths ← paths.mapM fun p ↦ do
        let sibling ← siblings.lookup (p.index >>> level)
        pure { p with siblings := p.siblings ++ [sibling] }
      expandLevelsScalar remaining (level + 1) parents paths unused

/-- Scalar multi-level expansion preserves all paths and failures. -/
theorem expandLevelsScalar_eq (remaining level : Nat) (nodes : List (Nat × Digest))
    (paths : List Path) (hints : List Digest) :
    expandLevelsScalar remaining level nodes paths hints =
      expandLevels Keccak.Commit.hash remaining level nodes paths hints := by
  induction remaining generalizing level nodes paths hints with
  | zero => rfl
  | succ remaining ih => simp only [expandLevelsScalar.eq_2, expandLevels.eq_2, ih, expandLevelScalar_eq]

/-- Check shape and expand a pruned opening with scalar leaf and node hashes. -/
def expandScalar (height rowWords leafWords : Nat) (queries : List Nat) (batch : Pruned) :
    Option (Digest × List Path) := do
  let ps := positions queries
  if ps.isEmpty || !(ps.all (· < 2 ^ height)) || ps.length != batch.leafData.length ||
      rowWords > leafWords || !(batch.leafData.all (fun row ↦ row.length == rowWords)) then none
  else do
    let paths := (ps.zip batch.leafData).map fun (i, row) ↦
      Path.mk i (restoreLeaf leafWords row) []
    let nodes := paths.map fun p ↦ (p.index, hashLeaf p.leaf)
    let (nodes, paths, unused) ← expandLevelsScalar height 0 nodes paths batch.siblingHashes
    if !unused.isEmpty then none else do
      let top ← nodes.head?
      let ordered ← queries.mapM fun i ↦ paths.find? (fun p ↦ p.index == i)
      pure (top.2, ordered)

/-- The scalar batch checker preserves every accepted and rejected opening. -/
theorem expandScalar_eq (height rowWords leafWords : Nat) (queries : List Nat) (batch : Pruned) :
    expandScalar height rowWords leafWords queries batch =
      Keccak.Commit.expand Keccak.Commit.hash height rowWords leafWords queries batch := by
  simp only [expandScalar, Keccak.Commit.expand, expandLevelsScalar_eq, hashLeaf_eq]
end CompStark.Keccak.Commit.Scalar
