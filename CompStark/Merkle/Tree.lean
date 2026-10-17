/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Hash.Sponge

/-! # Merkle tree commitments to matrices

Plonky3's `MerkleTree::new` over a list of row-major matrices, with a leaf hash `hash` and a
two-to-one compression `compress` on digests of `d` field elements:

* The matrices are ordered by height, tallest first, keeping the given order among equal
  heights. The first digest layer hashes, for every row of the tallest matrices, the
  concatenation of that row of each of them.
* Every further layer compresses consecutive pairs of digests. Matrices whose height rounds up
  to the size of the next layer are injected there: a digest becomes
  `compress (compress left right) (hash rows)`, or `compress (compress left right) 0` past the
  injected matrices' height.
* Every layer but the root is padded with zero digests to even length, except a single first
  digest. The root is the last digest.
-/

@[expose] public section
namespace CompStark.Merkle

variable {F : Type*} [Zero F] {d : Nat}

/-- A row-major matrix of `height` rows of `width` field elements. -/
structure Matrix (F : Type*) where
  width : Nat
  height : Nat
  values : Array F

/-- Row `i` of a matrix. -/
def Matrix.row (m : Matrix F) (i : Nat) : List F :=
  (List.range m.width).map fun j ↦ m.values.getD (i * m.width + j) 0

/-- `n` rounded up to even, except for a single element. -/
def padEven (n : Nat) : Nat := if n = 1 then 1 else n + n % 2

/-- A list padded with `x` to length `n`. -/
def padTo {α : Type*} (x : α) (n : Nat) (l : List α) : List α :=
  l ++ List.replicate (n - l.length) x

/-- The first digest layer: the hashes of the rows of the tallest matrices `ms` of height `h`. -/
def firstLayer (hash : List F → Vector F d) (ms : List (Matrix F)) (h : Nat) : List (Vector F d) :=
  padTo 0 (padEven h) ((List.range h).map fun i ↦ hash (ms.flatMap (·.row i)))

/-- The next digest layer: compressed pairs, with the matrices `ms` injected. -/
def nextLayer (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (ms : List (Matrix F)) (prev : List (Vector F d)) : List (Vector F d) :=
  let n := prev.length / 2
  let pair (i : Nat) := compress (prev.getD (2 * i) 0) (prev.getD (2 * i + 1) 0)
  let injected (i : Nat) : Vector F d :=
    match ms with
    | [] => pair i
    | m :: _ =>
      if i < m.height then compress (pair i) (hash (ms.flatMap (·.row i)))
      else compress (pair i) 0
  padTo 0 (if prev.length = 2 then 1 else (n + 1) / 2 * 2) ((List.range n).map injected)

/-- The layers above `prev`, injecting the matrices of `rest` in order; `fuel` bounds the
number of layers. -/
def upperLayers (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d) :
    Nat → List (Matrix F) → List (Vector F d) → List (Vector F d)
  | 0, _, prev => prev
  | fuel + 1, rest, prev =>
    if prev.length ≤ 1 then prev
    else
      let n := (prev.length / 2).nextPowerOfTwo
      let ms := rest.takeWhile (·.height.nextPowerOfTwo == n)
      upperLayers hash compress fuel (rest.drop ms.length) (nextLayer hash compress ms prev)

/-- The root of the Merkle tree of the matrices `ms`. -/
def root (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (ms : List (Matrix F)) : Vector F d :=
  let sorted := ms.mergeSort fun a b ↦ b.height ≤ a.height
  let h := (sorted.headD ⟨0, 0, #[]⟩).height
  let tallest := sorted.takeWhile (·.height == h)
  let first := firstLayer hash tallest h
  (upperLayers hash compress first.length (sorted.drop tallest.length) first).headD 0

/-- Plonky3's Poseidon2 Merkle tree over KoalaBear: `KoalaBear.hash` leaves,
`KoalaBear.compress` nodes. -/
def KoalaBear.root (F : Type*) [Field F] (ms : List (Matrix F)) : Vector F 8 :=
  Merkle.root (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) ms

end CompStark.Merkle
