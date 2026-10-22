/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Batch.Verifier
public import CompStark.Fri.Prover
public import CompStark.Merkle.Mixed

/-! # The batch's common data on any primitives

Plonky3's `ProverData::from_airs_and_degrees`: the common data of a batch is the Merkle cap of
the extensions of its instances' preprocessed traces, in instance order, those of mixed heights
injected into the tree of the tallest (`setupBatch`). `commonWith` computes it on any primitives
`H` (`Primitives`), node by node from the leaves (`injNodeWith`, the nodes `Merkle.injNode` on
`H`'s hashes), so that the random-oracle model runs Plonky3's setup on random oracles and counts
its oracle calls.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark

variable {F : Type} {m : Type → Type} [Monad m]

/-- The node at level `l` and index `i` of the tree of matrices `ms` of heights at most `2 ^ k`,
by the hashes of `H`: a leaf hashes the rows of the tallest matrices; a node compresses its
children, then, if some matrices have its layer's height, the result with the hash of their
rows. -/
def injNodeWith [Zero F] (H : Primitives F m) (ms : List (Merkle.Matrix F)) (k : Nat) :
    Nat → Nat → m (Digest F)
  | 0, i => H.hash (Merkle.groupRows ms k i)
  | l + 1, i => do
    let left ← injNodeWith H ms k l (2 * i)
    let right ← injNodeWith H ms k l (2 * i + 1)
    let p ← H.compress left right
    if ms.any (·.height == 2 ^ (k - (l + 1))) then
      H.compress p (← H.hash (Merkle.groupRows ms (k - (l + 1)) i))
    else pure p

variable [BaseField F]

/-- The extensions of the instances' preprocessed traces, in instance order, of those that have
preprocessed columns. -/
def preprocessedMats (P : Params) (instances : List (Instance F)) : List (Mat F) :=
  instances.filterMap fun I ↦
    if I.air.preprocessedWidth = 0 then none
    else some (ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed)

/-- The log height of the tallest preprocessed trace's extension. -/
def preprocessedLogHeight (P : Params) (instances : List (Instance F)) : Nat :=
  ((instances.filter (0 < ·.air.preprocessedWidth)).map (·.logN + P.logBlowup)).foldl max 0

/-- The common data of the instances on the primitives `H`: the cap of height `P.capHeight`
(capped at the tree's levels) of the tree of their preprocessed traces' extensions, if any has
preprocessed columns. -/
def commonWith (H : Primitives F m) (P : Params) (instances : List (Instance F)) : m (Common F) :=
  if (preprocessedMats P instances).isEmpty then pure ⟨none⟩ else do
    let k := preprocessedLogHeight P instances
    let h := min P.capHeight k
    let cap ← (List.range (2 ^ h)).mapM
      (injNodeWith H ((preprocessedMats P instances).map Mat.toMatrix) k (k - h))
    return ⟨some cap.toArray⟩

end CompStark.Batch
