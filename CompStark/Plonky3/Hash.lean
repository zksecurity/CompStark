/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Hash.Sponge
public import CompStark.Merkle.Mmcs
public import CompStark.Poseidon2.Impl

/-! # Plonky3's Poseidon2 Merkle tree

`Hash.Poseidon2.hash` and `Hash.Poseidon2.compress` are the hashes of Plonky3's Poseidon2 Merkle
tree over a field with Plonky3's Poseidon2 instances (`Poseidon2Field`): the sponge on the width-24
permutation with rate 16 and eight-element digests (`PaddingFreeSponge<_, 24, 16, 8>`), and
compression by the width-16 permutation (`TruncatedPermutation<_, 2, 8, 16>`). Both run on the
field's implementations and are the specification's (`hash_eq`, `compress_eq`).
`Merkle.Poseidon2` is the tree, its openings and their verification on them.
-/

@[expose] public section
namespace CompStark.Hash

namespace Poseidon2

variable (F : Type) [Field F] [Poseidon2Field F]

/-- Plonky3's Poseidon2 Merkle leaf hash: the sponge on the width-24 permutation, rate 16,
eight-element digests. -/
def hash (xs : List F) : Vector F 8 :=
  sponge (Poseidon2Field.perm24 (F := F)).perm 16 8 (by decide) (by decide) xs

/-- Plonky3's Poseidon2 Merkle compression: the width-16 permutation, truncated to eight
elements. -/
def compress (a b : Vector F 8) : Vector F 8 :=
  Hash.compress (Poseidon2Field.perm16 (F := F)).perm (by decide) a b

theorem hash_eq (xs : List F) :
    hash F xs = sponge (CompStark.Poseidon2.permute (Poseidon2Field.params24 (F := F))) 16 8
      (by decide) (by decide) xs := by
  rw [hash, funext (Poseidon2Field.perm24 (F := F)).perm_eq]

theorem compress_eq (a b : Vector F 8) :
    compress F a b =
      Hash.compress (CompStark.Poseidon2.permute (Poseidon2Field.params16 (F := F))) (by decide)
        a b := by
  rw [compress, funext (Poseidon2Field.perm16 (F := F)).perm_eq]

end Poseidon2
end CompStark.Hash

namespace CompStark.Merkle
namespace Poseidon2

variable (F : Type) [Field F] [Poseidon2Field F]

/-- Plonky3's Poseidon2 Merkle tree: `Hash.Poseidon2.hash` leaves, `Hash.Poseidon2.compress`
nodes. -/
def root (ms : List (Matrix F)) : Vector F 8 :=
  Merkle.root (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F) ms

/-- The Poseidon2 opening of base-field matrices. -/
def openBatch (ms : List (Matrix F)) (index : Nat) : List (List F) × List (Vector F 8) :=
  Merkle.openBatch (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F) ms index

/-- The Poseidon2 verification of a base-field opening. -/
def verifyBatch [DecidableEq F] (commit : Vector F 8) (heights : List Nat) (index : Nat)
    (values : List (List F)) (path : List (Vector F 8)) : Bool :=
  Merkle.verifyBatch (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F) commit heights index
    values path

end Poseidon2
end CompStark.Merkle
