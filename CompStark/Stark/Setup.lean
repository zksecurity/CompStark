/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Merkle.VCVio

/-! # The preprocessed trace's verifying key

Plonky3's `setup_preprocessed`: the verifying key of an AIR's preprocessed trace is its width,
the log of its height, and the Merkle cap of its low-degree extension onto `L`, rows in
bit-reversed order: the nodes of the layer the cap height below the root. `preprocessedKeyWith`
computes it on any primitives `H` (`Primitives`), node by node from the leaves
(`merkleNodeWith`), so that one definition is Plonky3's setup on Poseidon2 (`setup`) and the
random-oracle model's on random oracles, where its oracle calls are counted.

On pure hashes the nodes are VCVio's (`merkleNodeWith_pure`), so the root is the Merkle tree's
(`Merkle.root_eq_nodeValue`), and so is the cap.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

variable {F : Type} {m : Type → Type} [Monad m]

/-- The digest of node `t` at height `j` of the Merkle tree with leaf digests `leaf`, by the
compression of `H`. -/
def merkleNodeWith (H : Primitives F m) (leaf : Nat → m (Digest F)) : Nat → Nat → m (Digest F)
  | 0, t => leaf t
  | j + 1, t => do
    let left ← merkleNodeWith H leaf j (2 * t)
    let right ← merkleNodeWith H leaf j (2 * t + 1)
    H.compress left right

/-- The preprocessed trace's extension onto the domain of `2 ^ (logN + logBlowup)` points. -/
def preprocessedLde [BaseField F] (P : Params) (A : Air F) (logN : Nat) : Mat F :=
  ldeRef logN P.logBlowup gen A.preprocessedWidth A.preprocessed

/-- The cap of height `h` (capped at `levels`) of the Merkle tree with `levels` levels above the
leaf digests `leaf`, by the compression of `H`: the `2 ^ h` nodes of its layer `h` levels below the
root. -/
def merkleCapWith (H : Primitives F m) (leaf : Nat → m (Digest F)) (levels h : Nat) :
    m (Cap F) := do
  let h := min h levels
  return (← (List.range (2 ^ h)).mapM (merkleNodeWith H leaf (levels - h))).toArray

/-- The verifying key of `A`'s preprocessed trace for `2 ^ logN` rows on the primitives `H`: the
Merkle cap by `H`'s hashes of the rows of its extension, if it has columns. -/
def preprocessedKeyWith [BaseField F] (H : Primitives F m) (P : Params) (A : Air F) (logN : Nat) :
    m (Option (PreprocessedKey F)) :=
  if A.preprocessedWidth = 0 then pure none else do
    let cap ← merkleCapWith H (fun r ↦ H.hash (rowOf (preprocessedLde P A logN) r).toList)
      (logN + P.logBlowup) P.capHeight
    pure (some ⟨A.preprocessedWidth, logN, cap⟩)

/-- On pure hashes, the nodes are VCVio's. -/
theorem merkleNodeWith_pure (H : Primitives F Id) (hash : List F → Digest F)
    (compress : Digest F → Digest F → Digest F) (hh : ∀ xs, H.hash xs = hash xs)
    (hc : ∀ a b, H.compress a b = compress a b) (leaf : Nat → List F) :
    ∀ j t, merkleNodeWith H (fun r ↦ H.hash (leaf r)) j t =
      Merkle.nodeValue compress (fun r ↦ hash (leaf r)) j t
  | 0, t => hh _
  | j + 1, t => by
    rw [merkleNodeWith, Merkle.nodeValue_succ, ← merkleNodeWith_pure H hash compress hh hc leaf,
      ← merkleNodeWith_pure H hash compress hh hc leaf]
    exact hc _ _

end CompStark.Stark

namespace CompStark.Merkle

variable {F : Type} [Zero F] {d : Nat}

/-- The Merkle root of one matrix of `2 ^ k` rows is its root node. -/
theorem root_eq_nodeValue (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (mat : Matrix F) (k : Nat)
    (hh : mat.height = 2 ^ k) :
    root hash compress [mat] = nodeValue compress (fun r ↦ hash (mat.row r)) k 0 := by
  rw [root_eq_layers, layers_eq_nodeValue hash compress [mat] k (List.cons_ne_nil _ _)
    (fun m hm ↦ by rw [List.mem_singleton.mp hm]; exact hh), List.range_succ, List.map_append,
    List.getLastD_eq_getLast?, List.getLast?_append, List.map_cons, List.map_nil,
    List.getLast?_singleton]
  simp only [Option.some_or, Option.getD_some, Nat.sub_self, Nat.pow_zero, List.range_one,
    List.map_cons, List.map_nil, List.headD_cons]
  congr 1
  funext r
  simp only [leafHashes, List.flatMap_cons, List.flatMap_nil, List.append_nil]

end CompStark.Merkle
