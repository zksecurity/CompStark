/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Bytes
public import CompStark.Keccak.Merkle

/-! The streaming Keccak Merkle commitment on leaf images of field words: its leaf hash is the commitment's leaf digest, and its openings serialize in authentication order. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.MerkleLeaves
open CompStark.BinaryFields

/-- A complete protocol leaf image as a native authenticated Merkle row. -/
def merkleRow (words : List K) (h : 8 * words.length < USize.size) :
    CompStark.Keccak.Merkle.Row :=
  have size : (Commit.leafBytes words).size = 8 * words.length := by
    clear h
    change (words.flatMap Commit.wordBytes).length = _
    induction words with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, Commit.wordBytes_length,
        List.length_cons, ih]
      omega
  ⟨Commit.leafBytes words, by rw [size]; exact h, by rw [size]; omega⟩

/-- Hashing a framed row gives exactly the production leaf digest. -/
theorem merkleRow_hash (words : List K) (h : 8 * words.length < USize.size) :
    (CompStark.Keccak.Merkle.hashRow (merkleRow words h)).val.data =
      (Commit.hashLeaf words).toArray := by
  rw [CompStark.Keccak.Merkle.hashRow_eq]
  rfl

/-- Wire rows omit only the announced leading zero words; authentication retains the full image. -/
def openingRows (zeroPrefix : Nat) (opening : CompStark.Keccak.Merkle.Opening) : List ByteArray :=
  opening.leafData.map fun row => row.bytes.extract (8 * zeroPrefix) row.bytes.size

/-- Canonical Merkle hints serialize bottom-up, preserving the authenticated sibling order. -/
def openingHashes (opening : CompStark.Keccak.Merkle.Opening) : ByteArray :=
  opening.siblingHashes.foldl (fun bytes hash => bytes ++ hash.val) ByteArray.empty

open CompStark.Keccak.Merkle BinaryTree in
/-- Authenticate a query batch with one shared domain-size calculation. -/
def openPrepared {depth : Nat} (tree : Tree depth) (queries : List Nat) :
    Except String Opening :=
  let domain := 2 ^ depth
  if queries.isEmpty || !(queries.all (· < domain)) then
    .error "Merkle queries must be nonempty and within the committed domain"
  else
    let qs := positions queries
    .ok ⟨qs.map fun q => tree.rows.get (SkeletonLeafIndex.ofNat depth q),
      MixedMerkleTree.prune ⟨ByteArray.mk (Array.replicate 32 0), by rfl⟩ depth qs
        (qs.map tree.path)⟩

/-- Sharing the domain size preserves rejection, rows and every authentication byte. -/
@[csimp] theorem open_prepared_code :
    @CompStark.Keccak.Merkle.Tree.open = @openPrepared := by
  rfl

end CompStark.Keccak.MerkleLeaves
