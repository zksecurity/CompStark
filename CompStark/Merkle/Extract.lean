/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.VCVio

/-! # Extracting committed rows from hash queries

A Merkle commitment binds its rows only through the hash queries made so far. This file reads a
single-height Plonky3 tree back from those queries, generically over the digest type:

* A `Cache` records the answered queries as relations: which rows the leaf hash sent to which
  digest, and which pairs `compress` sent to which digest. A random oracle's query cache and a
  query log are both caches.
* `extractRow cache k i root`: the row at index `i` of the depth-`k` tree under `root`, walking
  down from `root` through cached compressions and inverting the leaf hash at the bottom; under a
  Merkle cap, in the subtree under the index's cap entry (`extractCapRow`).
* `extractRow_eq_of_verifyBatch`: if no two cached queries share an answer, an accepted
  `verifyBatch` opening whose hashes are all cached opens the extracted row.
* `extractRow_eq_of_noPrediction`: extraction does not change when the cache grows by entries
  whose answers are digests the extraction could reach: the root and the children of cached
  compressions. So extraction at the time the root is bound equals extraction at the end.

Extraction picks preimages by choice, so it only depends on the cache's relations, not on the
order of a log. That is why it does not reuse VCVio's `MerkleTreeExtractor.treeAt`, which takes
the first match in a homogeneous log of node queries and does not invert the leaf hash.
-/

@[expose] public section
namespace CompStark.Merkle

/-- Answered hash queries: `leaf row y` if the leaf hash of `row` was answered `y`, and
`node left right y` if the compression of `left, right` was answered `y`. -/
structure Cache (F D : Type*) where
  /-- The answered leaf-hash queries. -/
  leaf : List F → D → Prop
  /-- The answered compression queries. -/
  node : D → D → D → Prop

namespace Cache

variable {F D : Type*}

/-- No two cached rows hash to one digest, and no two cached pairs compress to one digest. -/
structure Injective (cache : Cache F D) : Prop where
  leaf : ∀ row row' y, cache.leaf row y → cache.leaf row' y → row = row'
  node : ∀ left right left' right' y, cache.node left right y → cache.node left' right' y →
    left = left' ∧ right = right'

/-- The digests extraction under `root` can reach: `root` and the children of cached
compressions. -/
def Known (cache : Cache F D) (root y : D) : Prop :=
  y = root ∨ ∃ left right parent, cache.node left right parent ∧ (y = left ∨ y = right)

/-- `later` extends `now` and every entry it adds answers a digest not `Known` to `now`: no added
query predicts a digest that extraction from `now` under `root` can reach. -/
structure NoPrediction (now later : Cache F D) (root : D) : Prop where
  leaf_le : ∀ row y, now.leaf row y → later.leaf row y
  node_le : ∀ left right y, now.node left right y → later.node left right y
  leaf_new : ∀ row y, later.leaf row y → now.Known root y → now.leaf row y
  node_new : ∀ left right y, later.node left right y → now.Known root y → now.node left right y

end Cache

section Extract

variable {F D : Type*}

/-- Some `a` with `P a`, if there is one. -/
noncomputable def pick {α : Type*} (P : α → Prop) : Option α :=
  open Classical in if h : ∃ a, P a then some (Classical.choose h) else none

/-- The children of `parent`: a cached pair compressing to it. -/
noncomputable def children (cache : Cache F D) (parent : D) : Option (D × D) :=
  pick fun pair ↦ cache.node pair.1 pair.2 parent

/-- The digest of node `i` at depth `k` below `root`, walking down cached compressions. The
parent of node `i` is node `i / 2`, and node `i` is its left child for even `i`. -/
noncomputable def nodeAt (cache : Cache F D) : (k : Nat) → (i : Nat) → (root : D) → Option D
  | 0, _, root => some root
  | k + 1, i, root => (nodeAt cache k (i / 2) root).bind fun parent ↦
      (children cache parent).map fun (left, right) ↦ if i % 2 = 0 then left else right

/-- The row committed at index `i` of the depth-`k` tree under `root`: a cached leaf-hash
preimage of the leaf digest. -/
noncomputable def extractRow (cache : Cache F D) (k i : Nat) (root : D) : Option (List F) :=
  (nodeAt cache k i root).bind fun leaf ↦ pick fun row ↦ cache.leaf row leaf

/-- The row committed at index `i` of the depth-`k` tree under the cap `cap` of height `h`, capped
at `k`: the row at the index's low `l` bits of the depth-`l` subtree under the index's cap entry,
for the `l` levels below the cap. -/
noncomputable def extractCapRow [Zero D] (cache : Cache F D) (k h i : Nat) (cap : List D) :
    Option (List F) :=
  extractRow cache (k - min h k) (i % 2 ^ (k - min h k)) (cap.getD (i >>> (k - min h k)) 0)

/-- `parent` is reached from `leaf` at index `i` by compressing with the siblings `path`, each
compression cached. -/
def PathIn (cache : Cache F D) : D → Nat → List D → D → Prop
  | leaf, _, [], parent => leaf = parent
  | leaf, i, sib :: sibs, root => ∃ parent,
      (if i % 2 = 0 then cache.node leaf sib parent else cache.node sib leaf parent) ∧
        PathIn cache parent (i / 2) sibs root

/-- `pick` of a unique witness. -/
theorem pick_eq {α : Type*} (P : α → Prop) (a : α) (ha : P a) (huniq : ∀ b, P b → b = a) :
    pick P = some a := by
  have h : ∃ a, P a := ⟨a, ha⟩
  simp only [pick, h, ↓reduceDIte, huniq _ (Classical.choose_spec h)]

/-- `pick` returns a witness. -/
theorem pick_spec {α : Type*} (P : α → Prop) (a : α) (h : pick P = some a) : P a := by
  unfold pick at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact Classical.choose_spec hex
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- The children of a cached compression in an injective cache. -/
theorem children_eq (cache : Cache F D) (hinj : cache.Injective) (left right parent : D)
    (h : cache.node left right parent) : children cache parent = some (left, right) :=
  pick_eq _ (left, right) h fun pair hpair ↦ by
    obtain ⟨h1, h2⟩ := hinj.node _ _ _ _ _ hpair h
    rw [← h1, ← h2]

/-- **Opened paths are extracted.** In an injective cache, a cached path from `leaf` at `i` to
`root` makes `leaf` the extracted node `i` at depth `path.length`. -/
theorem nodeAt_of_pathIn (cache : Cache F D) (hinj : cache.Injective) (root : D) :
    (path : List D) → (leaf : D) → (i : Nat) → PathIn cache leaf i path root →
      nodeAt cache path.length i root = some leaf
  | [], leaf, _, h => by simp only [PathIn] at h; simp only [List.length_nil, nodeAt, h]
  | sib :: sibs, leaf, i, ⟨parent, hstep, hrest⟩ => by
    simp only [List.length_cons, nodeAt, nodeAt_of_pathIn cache hinj root sibs parent _ hrest,
      Option.bind_some]
    by_cases hi : i % 2 = 0
    · simp only [hi, ↓reduceIte] at hstep
      simp only [children_eq cache hinj _ _ _ hstep, Option.map_some, hi, ↓reduceIte]
    · simp only [hi, ↓reduceIte] at hstep
      simp only [children_eq cache hinj _ _ _ hstep, Option.map_some, hi, ↓reduceIte]

/-- In an injective cache, a cached path from the hash of `row` at `i` to `root` makes `row` the
extracted row `i`. -/
theorem extractRow_of_pathIn (cache : Cache F D) (hinj : cache.Injective) (root : D)
    (path : List D) (row : List F) (leaf : D) (i : Nat) (hleaf : cache.leaf row leaf)
    (hpath : PathIn cache leaf i path root) :
    extractRow cache path.length i root = some row := by
  simp only [extractRow, nodeAt_of_pathIn cache hinj root path leaf i hpath, Option.bind_some]
  exact pick_eq _ row hleaf fun row' h ↦ hinj.leaf _ _ _ h hleaf

/-- Every extracted node is `Known`. -/
theorem known_of_nodeAt (cache : Cache F D) (root : D) :
    (k i : Nat) → (y : D) → nodeAt cache k i root = some y → cache.Known root y
  | 0, _, y, h => by
    simp only [nodeAt, Option.some.injEq] at h
    exact Or.inl h.symm
  | k + 1, i, y, h => by
    simp only [nodeAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨parent, -, ⟨left, right⟩, hc, hy⟩ := h
    have hnode : cache.node left right parent :=
      pick_spec (fun pair : D × D ↦ cache.node pair.1 pair.2 parent) _ hc
    refine Or.inr ⟨left, right, parent, hnode, ?_⟩
    by_cases hi : i % 2 = 0
    · simp only [hi, ↓reduceIte] at hy; exact Or.inl hy.symm
    · simp only [hi, ↓reduceIte] at hy; exact Or.inr hy.symm

/-- Without prediction, a `Known` digest has the same children later. -/
theorem children_eq_of_noPrediction (now later : Cache F D) (root y : D)
    (h : now.NoPrediction later root) (hy : now.Known root y) :
    children later y = children now y := by
  have hP : (fun pair : D × D ↦ later.node pair.1 pair.2 y) =
      fun pair ↦ now.node pair.1 pair.2 y :=
    funext fun pair ↦ propext ⟨fun hl ↦ h.node_new _ _ _ hl hy, h.node_le _ _ _⟩
  simp only [children, hP]

/-- Without prediction, extracted nodes stay the same. -/
theorem nodeAt_eq_of_noPrediction (now later : Cache F D) (root : D)
    (h : now.NoPrediction later root) :
    (k i : Nat) → nodeAt later k i root = nodeAt now k i root
  | 0, _ => rfl
  | k + 1, i => by
    simp only [nodeAt, nodeAt_eq_of_noPrediction now later root h k (i / 2)]
    cases hp : nodeAt now k (i / 2) root with
    | none => rfl
    | some parent =>
      simp only [Option.bind_some,
        children_eq_of_noPrediction now later root parent h (known_of_nodeAt now root _ _ _ hp)]

/-- **Stability of extraction.** Extraction under `root` does not change when the cache grows by
entries that predict no digest it can reach. -/
theorem extractRow_eq_of_noPrediction (now later : Cache F D) (root : D)
    (h : now.NoPrediction later root) (k i : Nat) :
    extractRow later k i root = extractRow now k i root := by
  simp only [extractRow, nodeAt_eq_of_noPrediction now later root h]
  cases hl : nodeAt now k i root with
  | none => rfl
  | some leaf =>
    have hy := known_of_nodeAt now root _ _ _ hl
    have hP : (fun row ↦ later.leaf row leaf) = fun row ↦ now.leaf row leaf :=
      funext fun row ↦ propext ⟨fun hl ↦ h.leaf_new _ _ hl hy, h.leaf_le _ _⟩
    simp only [Option.bind_some, hP]

end Extract

section Verify

open BinaryTree InductiveMerkleTree

variable {F : Type*} {d : Nat}

/-- The pairs compressed when climbing from `leaf` at `i` with the siblings `path`, from the
leaves up. -/
def climbPairs (compress : Vector F d → Vector F d → Vector F d) :
    Vector F d → Nat → List (Vector F d) → List (Vector F d × Vector F d)
  | _, _, [] => []
  | leaf, i, sib :: sibs =>
    let pair := if i % 2 = 0 then (leaf, sib) else (sib, leaf)
    pair :: climbPairs compress (compress pair.1 pair.2) (i / 2) sibs

/-- A climb whose compressions are cached is a cached path. -/
theorem pathIn_climb (cache : Cache F (Vector F d)) (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (values : List (List F)) :
    (path : List (Vector F d)) → (leaf : Vector F d) → (i padded : Nat) →
      (∀ pair ∈ climbPairs compress leaf i path,
        cache.node pair.1 pair.2 (compress pair.1 pair.2)) →
      PathIn cache leaf i path (climb hash compress values path [] i padded leaf)
  | [], _, _, _, _ => rfl
  | sib :: sibs, leaf, i, padded, h => by
    simp only [climbPairs, List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hstep, hrest⟩ := h
    by_cases hi : i % 2 = 0
    · simp only [hi, ↓reduceIte] at hstep hrest
      exact ⟨_, by simp only [hi, ↓reduceIte]; exact hstep,
        by simpa only [climb, hi, ↓reduceIte] using
          pathIn_climb cache hash compress values sibs _ (i / 2) (padded / 2) hrest⟩
    · simp only [hi, ↓reduceIte] at hstep hrest
      exact ⟨_, by simp only [hi, ↓reduceIte]; exact hstep,
        by simpa only [climb, hi, ↓reduceIte] using
          pathIn_climb cache hash compress values sibs _ (i / 2) (padded / 2) hrest⟩

/-- **Accepted openings open the extracted rows.** If no two cached queries share an answer, an
accepted opening at `i` of `n > 0` matrices of height `2 ^ k` against `root`, whose leaf hash and
compressions are all cached, opens the extracted row `i`: the concatenated opened rows. -/
theorem extractRow_eq_of_verifyBatch [DecidableEq F] (cache : Cache F (Vector F d))
    (hinj : cache.Injective) (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (root : Vector F d) (n k i : Nat)
    (hn : 0 < n) (values : List (List F)) (path : List (Vector F d))
    (hv : verifyBatch hash compress root (List.replicate n (2 ^ k)) i values path = true)
    (hleaf : cache.leaf values.flatten (hash values.flatten))
    (hnodes : ∀ pair ∈ climbPairs compress (hash values.flatten) i path,
      cache.node pair.1 pair.2 (compress pair.1 pair.2)) :
    extractRow cache k i root = some values.flatten := by
  have hlog : Nat.log2 (2 ^ k).nextPowerOfTwo = k := log2Ceil_two_pow k
  have hlen : path.length = k := by
    simp only [verifyBatch, heightGroups_replicate n _ hn, Bool.and_eq_true, beq_iff_eq,
      hlog] at hv
    exact hv.1.1.2
  have hdepth : path.reverse.length = (SkeletonLeafIndex.ofNat k i).depth := by
    rw [List.length_reverse, hlen, SkeletonLeafIndex.depth_ofNat]
  have hroot := ((verifyBatch_iff hash compress root n k i hn values path ⟨_, hdepth⟩ rfl).mp
    hv).2.2
  rw [← climb_eq_getPutativeRootWithHash hash compress values i (2 ^ k) _ k path _
    ⟨path.reverse, hdepth⟩ rfl rfl] at hroot
  rw [← hlen]
  refine extractRow_of_pathIn cache hinj root path _ _ i hleaf ?_
  rw [← hroot]
  exact pathIn_climb cache hash compress values path _ i _ hnodes

end Verify

end CompStark.Merkle
