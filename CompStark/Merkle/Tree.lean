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
* The cap of height `h` (`capOf`, Plonky3's `MerkleTree::cap`) is the layer `h` levels below the
  root, `h` capped at the tree's levels, as `2 ^ h` digests padded with zero digests.
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

/-- Every layer from `prev` up, as `upperLayers` builds them. -/
def upperLayersAll (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) :
    Nat → List (Matrix F) → List (Vector F d) → List (List (Vector F d))
  | 0, _, prev => [prev]
  | fuel + 1, rest, prev =>
    if prev.length ≤ 1 then [prev]
    else
      let n := (prev.length / 2).nextPowerOfTwo
      let ms := rest.takeWhile (·.height.nextPowerOfTwo == n)
      prev :: upperLayersAll hash compress fuel (rest.drop ms.length)
        (nextLayer hash compress ms prev)

/-- The matrices sorted tallest first, keeping the given order among equal heights. -/
def sortTallest (ms : List (Matrix F)) : List (Matrix F) :=
  ms.mergeSort fun a b ↦ b.height ≤ a.height

/-- The digest layers of the Merkle tree of `ms`, leaves first: Plonky3's `digest_layers`. -/
def layers (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (ms : List (Matrix F)) : List (List (Vector F d)) :=
  let sorted := sortTallest ms
  let h := (sorted.headD ⟨0, 0, #[]⟩).height
  let tallest := sorted.takeWhile (·.height == h)
  let first := firstLayer hash tallest h
  upperLayersAll hash compress first.length (sorted.drop tallest.length) first

/-- The cap of height `h` of the tree with the digest layers `ls`, leaves first: the first
`2 ^ h` digests of the layer `h` levels below the root, padded with zero digests, `h` capped at
the tree's levels (Plonky3's `MerkleTree::cap`). -/
def capOf (ls : List (List (Vector F d))) (h : Nat) : List (Vector F d) :=
  let levels := ls.length - 1
  let h := min h levels
  padTo 0 (2 ^ h) ((ls.getD (levels - h) []).take (2 ^ h))

theorem length_capOf (ls : List (List (Vector F d))) (h : Nat) :
    (capOf ls h).length = 2 ^ min h (ls.length - 1) := by
  simp only [capOf, padTo, List.length_append, List.length_replicate, List.length_take]
  omega

theorem getLastD_upperLayersAll (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (fuel : Nat) (rest : List (Matrix F))
    (prev x y : List (Vector F d)) :
    (upperLayersAll hash compress fuel rest prev).getLastD x =
      (upperLayersAll hash compress fuel rest prev).getLastD y := by
  induction fuel generalizing rest prev with
  | zero => rfl
  | succ fuel ih =>
    simp only [upperLayersAll]
    split
    · rfl
    · simp only [List.getLastD_cons]

theorem upperLayers_eq_getLast (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (fuel : Nat) (rest : List (Matrix F))
    (prev : List (Vector F d)) :
    upperLayers hash compress fuel rest prev =
      (upperLayersAll hash compress fuel rest prev).getLastD [] := by
  induction fuel generalizing rest prev with
  | zero => rfl
  | succ fuel ih =>
    simp only [upperLayers, upperLayersAll]
    split
    · rfl
    · rw [ih, List.getLastD_cons]
      exact getLastD_upperLayersAll _ _ _ _ _ _ _

/-- The root is the single digest of the last layer. -/
theorem root_eq_layers (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (ms : List (Matrix F)) :
    root hash compress ms = ((layers hash compress ms).getLastD []).headD 0 := by
  simp only [root, layers, sortTallest, upperLayers_eq_getLast]

end CompStark.Merkle
