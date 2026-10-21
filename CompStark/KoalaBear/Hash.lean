/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Hash.Sponge
public import CompStark.Merkle.Mmcs
public import CompStark.Poseidon2.KoalaBear

/-! # Plonky3's Poseidon2 Merkle tree over KoalaBear

`Hash.KoalaBear.hash` and `Hash.KoalaBear.compress` are the instances of Plonky3's Poseidon2
Merkle tree: the sponge on the width-24 permutation with rate 16 and eight-element digests, and
compression by the width-16 permutation. `Merkle.KoalaBear` is the tree, its openings and their
verification on them.
-/

@[expose] public section
namespace CompStark.Hash

namespace KoalaBear

variable (F : Type*) [Field F]

/-- Plonky3's Poseidon2 Merkle leaf hash: the sponge on the width-24 permutation, rate 16,
eight-element digests. -/
def hash (xs : List F) : Vector F 8 :=
  sponge (Poseidon2.permute (Poseidon2.KoalaBear.width24 F)) 16 8 (by decide) (by decide) xs

/-- Plonky3's Poseidon2 Merkle compression: the width-16 permutation, truncated to eight
elements. -/
def compress (a b : Vector F 8) : Vector F 8 :=
  Hash.compress (Poseidon2.permute (Poseidon2.KoalaBear.width16 F)) (by decide) a b

end KoalaBear
end CompStark.Hash

namespace CompStark.Merkle
namespace KoalaBear

variable (F : Type*) [Field F]

/-- Plonky3's Poseidon2 Merkle tree over KoalaBear: `Hash.KoalaBear.hash` leaves,
`Hash.KoalaBear.compress` nodes. -/
def root (ms : List (Matrix F)) : Vector F 8 :=
  Merkle.root (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) ms

/-- The KoalaBear Poseidon2 opening of base-field matrices. -/
def openBatch (ms : List (Matrix F)) (index : Nat) : List (List F) × List (Vector F 8) :=
  Merkle.openBatch (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) ms index

/-- The KoalaBear Poseidon2 verification of a base-field opening. -/
def verifyBatch [DecidableEq F] (commit : Vector F 8) (heights : List Nat) (index : Nat)
    (values : List (List F)) (path : List (Vector F 8)) : Bool :=
  Merkle.verifyBatch (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) commit heights index
    values path

end KoalaBear
end CompStark.Merkle
