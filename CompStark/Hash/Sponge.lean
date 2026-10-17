/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.KoalaBear

/-! # Sponge hashing and truncated-permutation compression

Plonky3's `PaddingFreeSponge` and `TruncatedPermutation`, over any permutation of `t` field
elements:

* `sponge perm rate out xs` starts from the zero state; every block of `rate` inputs overwrites
  the first `rate` coordinates and is followed by a permutation, a final partial block included,
  without padding. The digest is the first `out` coordinates. The empty input hashes to zeros.
* `compress perm a b` places `a` and `b` side by side in a zero state, permutes and keeps the
  first coordinates.

`KoalaBear.hash` and `KoalaBear.compress` are the instances of Plonky3's Poseidon2 Merkle tree:
the sponge on the width-24 permutation with rate 16 and eight-element digests, and compression
by the width-16 permutation.
-/

@[expose] public section
namespace CompStark.Hash

variable {F : Type*} [Zero F] {t : Nat}

/-- Overwrite the first coordinates of `s` with `xs`. -/
def overwrite (s : Vector F t) (xs : List F) : Vector F t :=
  Vector.ofFn fun i ↦ xs.getD i.val s[i]

/-- Absorb `xs` in blocks of `rate`, permuting after every block. -/
def absorb (perm : Vector F t → Vector F t) (rate : Nat) (hr : 0 < rate) (s : Vector F t) :
    List F → Vector F t
  | [] => s
  | x :: xs =>
    absorb perm rate hr (perm (overwrite s ((x :: xs).take rate))) ((x :: xs).drop rate)
termination_by xs => xs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The padding-free sponge: the first `out` coordinates after absorbing `xs`. -/
def sponge (perm : Vector F t → Vector F t) (rate out : Nat) (hr : 0 < rate) (ho : out ≤ t)
    (xs : List F) : Vector F out :=
  (absorb perm rate hr (Vector.replicate t 0) xs).take out |>.cast (by omega)

/-- Compression of two digests by a truncated permutation. -/
def compress {n : Nat} (perm : Vector F t → Vector F t) (h : 2 * n ≤ t) (a b : Vector F n) :
    Vector F n :=
  (perm (overwrite (Vector.replicate t 0) (a.toList ++ b.toList))).take n |>.cast (by omega)

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
