/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Mmcs
public import ToMathlib.Data.IndexedBinaryTree.Perfect
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Binding
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Completeness
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Inductive

/-! # Merkle commitments as VCVio Merkle trees

The Merkle tree of a batch of matrices of one height `2 ^ k` is VCVio's inductive Merkle tree
over the perfect skeleton of depth `k`, with `compress` as the node hash and leaf `i` the `hash`
of the concatenated rows `i`:

* `root_eq_buildMerkleTreeWithHash`: the commitment is the root of `buildMerkleTreeWithHash`.
* `openBatch_fst`, `openBatch_snd`: an opening at `i < 2 ^ k` is the rows `i` and VCVio's
  `generateProof` at the leaf `SkeletonLeafIndex.ofNat k i`, reversed: Plonky3 lists siblings
  from the leaves up, VCVio from the root down.
* `verifyBatch_iff`: verification accepts exactly when VCVio's putative root of the leaf
  `hash values.flatten` with the reversed path is the commitment.
* `verifyBatch_openBatch`: honest openings verify, by VCVio's `functional_completeness`.
* `verifyBatch_binding`: two accepted openings of one index under one commitment with different
  rows of the same widths give a collision of `hash` or of `compress`.

Plonky3's openings of matrices of mixed heights are VCVio's openings of trees with injected
payloads (`MixedMerkleTree`): the payload of a leaf is the concatenated rows of the tallest
matrices, and a group of shorter matrices injects its concatenated rows at the layer of its padded
height. `sched` reads off where a walk over the height groups injects which group:

* `climb_eq`: Plonky3's `climb` is VCVio's `MixedMerkleTree.climb` at the payloads `climbPays`.
* `walkM_eq`: the walk of a multi-opening, with pure hashes, is VCVio's `MixedMerkleTree.walk` at
  the payloads `walkPays`, with the zero digest past the end of the siblings.
* `sched_eq_find`: for heights that are distinct powers of two, tallest first, the group injected
  at a depth is the group of the height of that depth.
-/

@[expose] public section
namespace CompStark.Merkle

open BinaryTree InductiveMerkleTree
open MixedMerkleTree (nodeValue nodeValue_zero nodeValue_succ perfectLeaves perfectLeaves_get
  generateProof_perfectLeaves xor_one_eq)

section Perfect

variable {α : Type*}

/-- The next layer up of the layer `g`. -/
def pairUp (compress : α → α → α) (g : Nat → α) (t : Nat) : α :=
  compress (g (2 * t)) (g (2 * t + 1))

/-- A node is the node one height lower over the next layer up. -/
theorem nodeValue_succ_pairUp (compress : α → α → α) (g : Nat → α) (j t : Nat) :
    nodeValue compress g (j + 1) t = nodeValue compress (pairUp compress g) j t := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih => rw [nodeValue_succ, ih, ih, ← nodeValue_succ compress (pairUp compress g)]

end Perfect

variable {F : Type} {d : Nat}

/-- Reading a tabulated list. -/
private theorem getD_map_range {β : Type*} (g : Nat → β) (n i : Nat) (x : β) (hi : i < n) :
    ((List.range n).map g).getD i x = g i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

/-- Padding to the length a list already has does nothing. -/
theorem padTo_of_length {β : Type*} (x : β) (l : List β) (n : Nat) (h : l.length = n) :
    padTo x n l = l := by
  simp only [padTo, h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- One layer up from a full layer of `2 ^ (k + 1)` digests. -/
theorem nextLayer_range [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (g : Nat → Vector F d) (k : Nat) :
    nextLayer hash compress [] ((List.range (2 ^ (k + 1))).map g) =
      (List.range (2 ^ k)).map (pairUp compress g) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  simp only [nextLayer, List.length_map, List.length_range, hpow]
  rw [Nat.mul_div_cancel_left _ (by decide)]
  rw [padTo_of_length]
  · apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    simp only [pairUp]
    rw [getD_map_range _ _ _ _ (by omega), getD_map_range _ _ _ _ (by omega)]
  · simp only [List.length_map, List.length_range]
    rcases k with _ | k
    · rfl
    · have := Nat.one_le_two_pow (n := k)
      have h2 : ¬2 * (2 ^ k * 2) = 2 := by omega
      simp only [Nat.pow_succ, h2, ↓reduceIte]
      omega

/-- The layers above a full layer of `2 ^ k` digests. -/
theorem upperLayersAll_range [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (k fuel : Nat) (hk : k ≤ fuel)
    (g : Nat → Vector F d) :
    upperLayersAll hash compress fuel [] ((List.range (2 ^ k)).map g) =
      (List.range (k + 1)).map fun j ↦
        (List.range (2 ^ (k - j))).map (nodeValue compress g j) := by
  induction k generalizing fuel g with
  | zero =>
    cases fuel with
    | zero => rfl
    | succ fuel => simp only [upperLayersAll]; rfl
  | succ k ih =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlen : ¬ ((List.range (2 ^ (k + 1))).map g).length ≤ 1 := by
      simp only [List.length_map, List.length_range, Nat.pow_succ]
      have := Nat.one_le_two_pow (n := k); omega
    simp only [upperLayersAll, hlen, ite_false, List.takeWhile_nil, List.length_nil,
      List.drop_zero, nextLayer_range, ih fuel (by omega)]
    rw [List.range_succ_eq_map (n := k + 1), List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Nat.succ_sub_succ]
    apply List.map_congr_left
    intro t _
    rw [nodeValue_succ_pairUp]

/-- `takeWhile` keeps a list whose elements all pass. -/
private theorem takeWhile_of_forall {β : Type*} (p : β → Bool) (l : List β)
    (h : ∀ x ∈ l, p x) :
    l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.takeWhile_cons, h a List.mem_cons_self, ↓reduceIte,
      ih fun x hx ↦ h x (List.mem_cons_of_mem a hx)]

/-- Matrices of one height are already sorted tallest first. -/
theorem sortTallest_of_height (ms : List (Matrix F)) (h : Nat) (hh : ∀ m ∈ ms, m.height = h) :
    sortTallest ms = ms := by
  apply List.mergeSort_of_pairwise
  apply List.Pairwise.imp_of_mem (R := fun _ _ ↦ True) _ (List.pairwise_of_forall fun _ _ ↦ ⟨⟩)
  intro a b ha hb _
  simp only [hh a ha, hh b hb, Nat.le_refl, decide_true]

/-- `2 ^ k` is a power of two. -/
private theorem isPowerOfTwo_two_pow : (k : Nat) → (2 ^ k).isPowerOfTwo
  | 0 => Nat.isPowerOfTwo_one
  | k + 1 => by
    rw [Nat.pow_succ]; exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo (isPowerOfTwo_two_pow k)

/-- `⌈log₂ 2 ^ k⌉ = k`. -/
theorem log2Ceil_two_pow (k : Nat) : log2Ceil (2 ^ k) = k := by
  simp only [log2Ceil, Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k), Nat.log2_two_pow]

/-- `2 ^ k` pads to itself. -/
theorem nextPowerOfTwo_two_pow (k : Nat) : (2 ^ k).nextPowerOfTwo = 2 ^ k :=
  Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k)

/-- The levels below the cap of a tree of `2 ^ k` rows and cap height `capHeight`. -/
theorem capLevels_two_pow (k capHeight : Nat) :
    capLevels (2 ^ k) capHeight = (k - min capHeight k, min capHeight k) := by
  rw [capLevels, nextPowerOfTwo_two_pow, Nat.log2_two_pow]

/-! ### Openings of mixed heights as VCVio openings -/

section Schedule

/-- The groups a climb or a walk over `n` layers from the padded height `padded` injects, by depth
below its top: a group `(h, is)` is injected into the layer of its padded height, the groups taken
in order. -/
def sched : Nat → List (Nat × List Nat) → Nat → Nat → Option (List Nat)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | n + 1, (h, is) :: rest, padded, e =>
    if h.nextPowerOfTwo = padded / 2 then
      if e = n then some is else sched n rest (padded / 2) e
    else if e = n then none else sched n ((h, is) :: rest) (padded / 2) e

theorem sched_nil : ∀ n padded e, sched n [] padded e = none
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

/-- The payloads of a single opening of the rows `values`: the concatenated rows of the injected
groups. -/
def climbPays (values : List (List F)) (n : Nat) (groups : List (Nat × List Nat)) (padded : Nat)
    (e : Nat) : Option (List F) :=
  (sched n groups padded e).map fun is ↦ is.flatMap fun m ↦ values.getD m []

theorem climbPays_nil (values : List (List F)) (n padded : Nat) :
    climbPays values n [] padded = fun _ ↦ none := by
  funext e
  simp only [climbPays, sched_nil, Option.map_none]

/-- The payloads of a multi-opening of the queries' rows `rows`, by lead. -/
def walkPays (rows : List (List (List F))) (n : Nat) (groups : List (Nat × List Nat))
    (padded : Nat) (e : Nat) : Option (Nat → List F) :=
  (sched n groups padded e).map fun is q ↦ is.flatMap fun m ↦ (rows.getD q []).getD m []

/-- A query's payloads in a multi-opening are those of its single opening. -/
theorem paysOf_walkPays (rows : List (List (List F))) (n : Nat) (groups : List (Nat × List Nat))
    (padded r : Nat) :
    MixedMerkleTree.paysOf (walkPays rows n groups padded) r =
      climbPays (rows.getD r []) n groups padded := by
  funext e
  simp only [MixedMerkleTree.paysOf, walkPays, climbPays, Option.map_map]
  rfl

/-- Plonky3's `climb` is VCVio's climb at the payloads `climbPays`. -/
theorem climb_eq (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (values : List (List F)) :
    ∀ (path : List (Vector F d)) (groups : List (Nat × List Nat)) (i padded : Nat)
      (x : Vector F d), climb hash compress values path groups i padded x =
        MixedMerkleTree.climb hash compress (climbPays values path.length groups padded) i x path
  | [], _, _, _, _ => rfl
  | s :: path, groups, i, padded, x => by
    rw [MixedMerkleTree.climb_cons]
    have hpair : (if i % 2 = 0 then compress x s else compress s x) =
        MixedMerkleTree.pairUp compress i x s := rfl
    rcases groups with _ | ⟨⟨h, is⟩, rest⟩
    · simp only [climb, hpair, List.length_cons, climbPays_nil, MixedMerkleTree.inject]
      rw [climb_eq hash compress values path [] (i / 2) (padded / 2), climbPays_nil]
    · by_cases hc : h.nextPowerOfTwo = padded / 2
      · simp only [climb, hpair, hc, ↓reduceIte, hashRows]
        rw [climb_eq hash compress values path rest (i / 2) (padded / 2)]
        have hp : climbPays values (path.length + 1) ((h, is) :: rest) padded path.length =
            some (is.flatMap fun m ↦ values.getD m []) := by
          simp only [climbPays, sched, hc, ↓reduceIte, Option.map_some]
        rw [List.length_cons, hp, MixedMerkleTree.inject]
        refine MixedMerkleTree.climb_congr _ _ _ _ _ fun e he ↦ ?_
        simp only [climbPays, sched, hc, ↓reduceIte, Nat.ne_of_lt he]
      · simp only [climb, hpair, hc, ↓reduceIte]
        rw [climb_eq hash compress values path ((h, is) :: rest) (i / 2) (padded / 2)]
        have hp : climbPays values (path.length + 1) ((h, is) :: rest) padded path.length =
            none := by
          simp only [climbPays, sched, hc, ↓reduceIte, Option.map_none]
        rw [List.length_cons, hp, MixedMerkleTree.inject]
        refine MixedMerkleTree.climb_congr _ _ _ _ _ fun e he ↦ ?_
        simp only [climbPays, sched, hc, ↓reduceIte, Nat.ne_of_lt he]

/-- A walk step injecting the group `(h, is)` when its height is the next layer's. -/
theorem walkM_succ_cons [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (rows : List (List (List F)))
    (levels h : Nat) (is : List Nat) (rest : List (Nat × List Nat)) (padded : Nat)
    (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) :
    walkM (m := Id) hash compress rows (levels + 1) ((h, is) :: rest) padded nodes sibs =
      if h.nextPowerOfTwo = padded / 2 then
        walkM (m := Id) hash compress rows levels rest (padded / 2)
          ((MixedMerkleTree.level compress 0 nodes sibs).1.map fun x ↦
            (x.1, x.2.1, compress x.2.2 (hash (is.flatMap fun k ↦ (rows.getD x.2.1 []).getD k []))))
          (MixedMerkleTree.level compress 0 nodes sibs).2
      else walkM (m := Id) hash compress rows levels ((h, is) :: rest) (padded / 2)
        (MixedMerkleTree.level compress 0 nodes sibs).1
        (MixedMerkleTree.level compress 0 nodes sibs).2 := by
  simp only [walkM]
  split
  · exact congrArg (fun ps ↦ walkM (m := Id) hash compress rows levels rest (padded / 2) ps
      (MixedMerkleTree.level compress 0 nodes sibs).2) List.idRun_mapM
  · rfl

/-- A walk step without groups left. -/
theorem walkM_succ_nil [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (rows : List (List (List F)))
    (levels padded : Nat) (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) :
    walkM (m := Id) hash compress rows (levels + 1) [] padded nodes sibs =
      walkM (m := Id) hash compress rows levels [] (padded / 2)
        (MixedMerkleTree.level compress 0 nodes sibs).1
        (MixedMerkleTree.level compress 0 nodes sibs).2 := rfl

/-- The walk of a multi-opening, with pure hashes, is VCVio's walk at the payloads `walkPays`. -/
theorem walkM_eq [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (rows : List (List (List F))) :
    ∀ (levels : Nat) (groups : List (Nat × List Nat)) (padded : Nat)
      (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)),
      walkM (m := Id) hash compress rows levels groups padded nodes sibs =
        MixedMerkleTree.walk hash compress 0 (walkPays rows levels groups padded) levels nodes
          sibs
  | 0, _, _, _, _ => rfl
  | levels + 1, groups, padded, nodes, sibs => by
    rw [MixedMerkleTree.walk]
    rcases groups with _ | ⟨⟨h, is⟩, rest⟩
    · rw [walkM_succ_nil, walkM_eq hash compress rows levels [] (padded / 2)]
      have hnone : walkPays rows (levels + 1) [] padded levels = none := by
        simp only [walkPays, sched_nil, Option.map_none]
      rw [hnone]
      simp only [Option.map_none, MixedMerkleTree.inject, Prod.mk.eta, List.map_id']
      refine MixedMerkleTree.walk_congr _ _ _ _ _ _ fun e _ ↦ ?_
      simp only [walkPays, sched_nil, Option.map_none]
    · rw [walkM_succ_cons]
      by_cases hc : h.nextPowerOfTwo = padded / 2
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc),
          walkM_eq hash compress rows levels rest (padded / 2)]
        have hp : walkPays rows (levels + 1) ((h, is) :: rest) padded levels =
            some fun q ↦ is.flatMap fun m ↦ (rows.getD q []).getD m [] := by
          simp only [walkPays, sched, hc, ↓reduceIte, Option.map_some]
        rw [hp]
        simp only [Option.map_some, MixedMerkleTree.inject]
        refine MixedMerkleTree.walk_congr _ _ _ _ _ _ fun e he ↦ ?_
        simp only [walkPays, sched, hc, ↓reduceIte, Nat.ne_of_lt he]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc),
          walkM_eq hash compress rows levels ((h, is) :: rest) (padded / 2)]
        have hp : walkPays rows (levels + 1) ((h, is) :: rest) padded levels = none := by
          simp only [walkPays, sched, hc, ↓reduceIte, Option.map_none]
        rw [hp]
        simp only [Option.map_none, MixedMerkleTree.inject, Prod.mk.eta, List.map_id']
        refine MixedMerkleTree.walk_congr _ _ _ _ _ _ fun e he ↦ ?_
        simp only [walkPays, sched, hc, ↓reduceIte, Nat.ne_of_lt he]

/-- **The injection schedule.** For groups of distinct heights `2 ^ j < 2 ^ k`, tallest first, a
climb or walk over `L ≤ k` layers from the height `2 ^ k` injects at depth `e` the group of height
`2 ^ (e + k - L)`, if there is one. -/
theorem sched_eq_find : ∀ (L k : Nat) (G : List (Nat × List Nat)), L ≤ k →
    G.Pairwise (fun a b ↦ b.1 < a.1) → (∀ g ∈ G, ∃ j < k, g.1 = 2 ^ j) →
    ∀ e < L, sched L G (2 ^ k) e = (G.find? fun g ↦ g.1 == 2 ^ (e + (k - L))).map (·.2)
  | 0, _, _, _, _, _, e, he => absurd he (Nat.not_lt_zero e)
  | L + 1, k, G, hL, hs, hG, e, he => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hpad : 2 ^ (k' + 1) / 2 = 2 ^ k' := by
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    have hexp : e + (k' + 1 - (L + 1)) = e + (k' - L) := by omega
    rw [hexp]
    rcases G with _ | ⟨⟨h, is⟩, rest⟩
    · simp only [sched, List.find?_nil, Option.map_none]
    obtain ⟨j, hj, hjh⟩ := hG _ List.mem_cons_self
    dsimp only at hjh
    subst hjh
    have hrest : ∀ g ∈ rest, g.1 < 2 ^ j := fun g hg ↦ List.rel_of_pairwise_cons hs hg
    have hrestj : ∀ g ∈ rest, ∃ j' < j, g.1 = 2 ^ j' := fun g hg ↦ by
      obtain ⟨j', -, e'⟩ := hG g (List.mem_cons_of_mem _ hg)
      exact ⟨j', (Nat.pow_lt_pow_iff_right (by decide)).mp (e' ▸ hrest g hg), e'⟩
    rw [sched, nextPowerOfTwo_two_pow, hpad]
    by_cases hjk : j = k'
    · subst hjk
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      by_cases heL : e = L
      · subst heL
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl),
          List.find?_cons_of_pos (by simp only [beq_iff_eq]; congr 1; omega)]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false heL),
          sched_eq_find L j rest (by omega) hs.of_cons
          (fun g hg ↦ hrestj g hg) e (by omega),
          List.find?_cons_of_neg (by
            simp only [beq_iff_eq]
            intro h'
            have := Nat.pow_right_injective (le_refl 2) h'
            omega)]
    · have hjk' : j < k' := by omega
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h' ↦ hjk (Nat.pow_right_injective (le_refl 2) h'))]
      by_cases heL : e = L
      · subst heL
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        symm
        rw [Option.map_eq_none_iff, List.find?_eq_none]
        intro g hg
        simp only [beq_iff_eq, show e + (k' - e) = k' by omega]
        rcases List.mem_cons.mp hg with rfl | hg
        · exact fun h' ↦ hjk (Nat.pow_right_injective (le_refl 2) h')
        · have := hrest g hg
          have := Nat.pow_lt_pow_right (show 1 < 2 by decide) hjk'
          omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false heL),
          sched_eq_find L k' ((2 ^ j, is) :: rest) (by omega) hs
          (fun g hg ↦ by
            rcases List.mem_cons.mp hg with rfl | hg
            · exact ⟨j, hjk', rfl⟩
            · obtain ⟨j', hj', e'⟩ := hrestj g hg
              exact ⟨j', by omega, e'⟩) e (by omega)]

/-- In groups of strictly decreasing heights, the group of a height is found by its height. -/
theorem find?_height_eq {G : List (Nat × List Nat)} (hs : G.Pairwise (fun a b ↦ b.1 < a.1))
    {g : Nat × List Nat} (hg : g ∈ G) : G.find? (fun g' ↦ g'.1 == g.1) = some g := by
  induction G with
  | nil => exact absurd hg List.not_mem_nil
  | cons a G ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact List.find?_cons_of_pos (beq_self_eq_true _)
    · rw [List.find?_cons_of_neg (by
        have := List.rel_of_pairwise_cons hs hg
        simp only [beq_iff_eq]; omega)]
      exact ih hs.of_cons hg

end Schedule

/-- Leaf `i` of a batch: the hash of the concatenated rows `i`. -/
def leafHashes [Zero F] (hash : List F → Vector F d) (ms : List (Matrix F))
    (i : Nat) : Vector F d :=
  hash (ms.flatMap (·.row i))

/-- The leaves of the Merkle tree of a batch of matrices of height `2 ^ k`, on the perfect
skeleton of depth `k`. -/
def leafData [Zero F] (hash : List F → Vector F d) (ms : List (Matrix F)) (k : Nat) :
    LeafData (Vector F d) (Skeleton.perfect k) :=
  perfectLeaves (leafHashes hash ms) k 0

/-- The digest layers of a batch of matrices of height `2 ^ k`: layer `j` holds the nodes at
height `j`. -/
theorem layers_eq_nodeValue [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d)
    (ms : List (Matrix F)) (k : Nat) (hms : ms ≠ []) (hh : ∀ m ∈ ms, m.height = 2 ^ k) :
    layers hash compress ms = (List.range (k + 1)).map fun j ↦
      (List.range (2 ^ (k - j))).map (nodeValue compress (leafHashes hash ms) j) := by
  obtain ⟨m, ms', rfl⟩ := List.exists_cons_of_ne_nil hms
  have hsort := sortTallest_of_height _ _ hh
  have htake : (m :: ms').takeWhile (·.height == 2 ^ k) = m :: ms' :=
    takeWhile_of_forall _ _ fun x hx ↦ by simp only [hh x hx, beq_self_eq_true]
  have hpad : padEven (2 ^ k) = 2 ^ k := by
    rcases k with _ | k
    · rfl
    · simp only [padEven, Nat.pow_succ, Nat.mul_mod_left, Nat.add_zero]
      have := Nat.one_le_two_pow (n := k)
      simp only [show 2 ^ k * 2 ≠ 1 by omega, ↓reduceIte]
  simp only [layers, hsort, List.headD_cons, hh m List.mem_cons_self, htake, List.length_cons,
    firstLayer, hpad, List.drop_succ_cons, List.drop_length]
  rw [padTo_of_length _ _ _ (by simp only [List.length_map, List.length_range]),
    List.length_map, List.length_range]
  exact upperLayersAll_range hash compress k _ Nat.lt_two_pow_self.le (leafHashes hash _)

/-- The commitment to a batch of matrices of height `2 ^ k` is the root of VCVio's Merkle tree
on their leaf hashes. -/
theorem root_eq_buildMerkleTreeWithHash [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d)
    (ms : List (Matrix F)) (k : Nat) (hms : ms ≠ []) (hh : ∀ m ∈ ms, m.height = 2 ^ k) :
    root hash compress ms =
      (buildMerkleTreeWithHash (leafData hash ms k) compress).getRootValue := by
  rw [root_eq_layers, layers_eq_nodeValue hash compress ms k hms hh, List.range_succ,
    List.map_append, List.getLastD_eq_getLast?, List.getLast?_append, List.map_cons,
    List.map_nil, List.getLast?_singleton]
  simp only [Option.some_or, Option.getD_some, Nat.sub_self, Nat.pow_zero, List.range_one,
    List.map_cons, List.map_nil, List.headD_cons]
  rfl

/-- The opened rows at `i` are the rows `i`. -/
theorem openBatch_fst [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (ms : List (Matrix F)) (k i : Nat)
    (hh : ∀ m ∈ ms, m.height = 2 ^ k) :
    (openBatch hash compress ms i).1 = ms.map (·.row i) := by
  have hmax : (sortTallest ms |>.headD ⟨0, 0, #[]⟩).height = 2 ^ k ∨ ms = [] := by
    rcases ms with _ | ⟨m, ms⟩
    · exact Or.inr rfl
    · rw [sortTallest_of_height _ _ hh]; exact Or.inl (hh m List.mem_cons_self)
  rcases hmax with hmax | rfl
  · simp only [openBatch, openWith, hmax, log2Ceil_two_pow]
    apply List.map_congr_left
    intro m hm
    simp only [hh m hm, log2Ceil_two_pow, Nat.sub_self, Nat.shiftRight_zero]
  · rfl

/-- The sibling path at `i < 2 ^ k`: the sibling `(i >>> j) ^^^ 1` of every height `j < k`. -/
theorem openBatch_snd_eq_nodeValue [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (ms : List (Matrix F)) (k i : Nat)
    (hms : ms ≠ []) (hh : ∀ m ∈ ms, m.height = 2 ^ k) (hi : i < 2 ^ k) :
    (openBatch hash compress ms i).2 = (List.range k).map fun j ↦
      nodeValue compress (leafHashes hash ms) j ((i >>> j) ^^^ 1) := by
  obtain ⟨m, ms', rfl⟩ := List.exists_cons_of_ne_nil hms
  simp only [openBatch, openWith, sortTallest_of_height _ _ hh, List.headD_cons,
    hh m List.mem_cons_self, log2Ceil_two_pow, layers_eq_nodeValue hash compress _ k hms hh]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [getD_map_range _ _ _ _ (by omega), getD_map_range]
  rw [xor_one_eq, Nat.shiftRight_eq_div_pow]
  obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
  have h1 : i / 2 ^ j < 2 ^ (e + 1) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), ← Nat.pow_add]
    exact lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega))
  rw [he, Nat.pow_succ] at *
  have := Nat.mod_lt (i / 2 ^ j + 1) (show 2 > 0 by decide)
  omega

/-- The sibling path of an opening at `i < 2 ^ k` is VCVio's proof for the leaf `ofNat k i`,
reversed. -/
theorem openBatch_snd [Zero F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (ms : List (Matrix F)) (k i : Nat)
    (hms : ms ≠ []) (hh : ∀ m ∈ ms, m.height = 2 ^ k) (hi : i < 2 ^ k) :
    (openBatch hash compress ms i).2 =
      (generateProof (buildMerkleTreeWithHash (leafData hash ms k) compress)
        (SkeletonLeafIndex.ofNat k i)).toList.reverse := by
  have h0 : i / 2 ^ k = 0 := Nat.div_eq_of_lt hi
  have := generateProof_perfectLeaves compress (leafHashes hash ms) k i
  rw [h0] at this
  rw [leafData, this, List.reverse_reverse,
    openBatch_snd_eq_nodeValue hash compress ms k i hms hh hi]

/-- The grouping fold of `heightGroups` over indices of one height. -/
private theorem foldr_group (heights : List Nat) (h : Nat) (l : List Nat) (x : Nat)
    (hget : ∀ i ∈ l ++ [x], heights.getD i 0 = h) :
    (l ++ [x]).foldr (fun i gs ↦
      match gs with
      | (h, is) :: rest => if heights.getD i 0 = h then (h, i :: is) :: rest
          else (heights.getD i 0, [i]) :: gs
      | [] => [(heights.getD i 0, [i])]) [] = [(h, l ++ [x])] := by
  induction l with
  | nil =>
    simp only [List.nil_append, List.foldr_cons, List.foldr_nil,
      hget x (List.mem_append_right _ (List.mem_singleton_self x))]
  | cons a l ih =>
    simp only [List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih fun i hi ↦ hget i (List.mem_cons_of_mem a hi), hget a List.mem_cons_self]
    simp only [↓reduceIte]

/-- A batch of `n > 0` matrices of one height forms one height group. -/
theorem heightGroups_replicate (n h : Nat) (hn : 0 < n) :
    heightGroups (List.replicate n h) = [(h, List.range n)] := by
  have hget : ∀ i ∈ List.range n, (List.replicate n h).getD i 0 = h := by
    intro i hi
    rw [List.mem_range] at hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi, ↓reduceIte,
      Option.getD_some]
  have hsort : (List.range n).mergeSort (fun a b ↦
      decide ((List.replicate n h).getD b 0 ≤ (List.replicate n h).getD a 0)) = List.range n := by
    apply List.mergeSort_of_pairwise
    apply List.Pairwise.imp_of_mem (R := fun _ _ ↦ True) _
      (List.pairwise_of_forall fun _ _ ↦ ⟨⟩)
    intro a b ha hb _
    simp only [hget a ha, hget b hb, Nat.le_refl, decide_true]
  simp only [heightGroups, List.length_replicate, hsort]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ] at hget ⊢
  exact foldr_group _ _ _ _ hget

/-- Concatenating a list of lists by index. -/
theorem flatMap_range_getD {β : Type*} (l : List (List β)) :
    (List.range l.length).flatMap (l.getD · []) = l.flatten := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.getD_cons_zero,
      List.flatMap_map, Nat.succ_eq_add_one, List.getD_cons_succ, ih, List.flatten_cons]

/-- Verification of an opening at `i` of a batch of `n > 0` matrices of height `2 ^ k` accepts
exactly when there are `n` rows, `i < 2 ^ k`, and VCVio's putative root of the leaf
`hash values.flatten`, with any proof listing `path` from the root down, is the commitment. -/
theorem verifyBatch_iff [DecidableEq F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (commit : Vector F d) (n k i : Nat)
    (hn : 0 < n) (values : List (List F)) (path : List (Vector F d))
    (v : List.Vector (Vector F d) (SkeletonLeafIndex.ofNat k i).depth)
    (hv : v.toList = path.reverse) :
    verifyBatch hash compress commit (List.replicate n (2 ^ k)) i values path = true ↔
      values.length = n ∧ i < 2 ^ k ∧
        getPutativeRootWithHash (SkeletonLeafIndex.ofNat k i) (hash values.flatten) v compress =
          commit := by
  have hlen : path.length = k := by
    have := congrArg List.length hv
    simp only [List.Vector.toList_length, SkeletonLeafIndex.depth_ofNat,
      List.length_reverse] at this
    exact this.symm
  simp only [verifyBatch, heightGroups_replicate n _ hn, List.tail_cons, List.zip_nil_right,
    List.all_nil, Bool.true_and, List.length_replicate, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, hlen, Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k),
    Nat.log2_two_pow, true_and, and_assoc]
  rw [climb_eq, climbPays_nil,
    MixedMerkleTree.climb_eq_getPutativeRootWithHash hash compress i _ k path _ v rfl hv]
  constructor
  · rintro ⟨hl, hi, hr⟩
    subst hl
    rw [hashRows, flatMap_range_getD] at hr
    exact ⟨rfl, hi, hr⟩
  · rintro ⟨hl, hi, hr⟩
    subst hl
    rw [hashRows, flatMap_range_getD]
    exact ⟨rfl, hi, hr⟩

/-- `flatten` is injective on lists of lists of the same lengths. -/
private theorem flatten_injective_of_lengths {β : Type*} (l₁ l₂ : List (List β))
    (hw : l₁.map List.length = l₂.map List.length) (h : l₁.flatten = l₂.flatten) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => simp only [List.map_nil, List.map_cons, List.nil_eq, reduceCtorEq] at hw
  | cons a l₁ ih => cases l₂ with
    | nil => simp only [List.map_nil, List.map_cons, reduceCtorEq] at hw
    | cons b l₂ =>
      simp only [List.map_cons, List.cons.injEq] at hw
      simp only [List.flatten_cons] at h
      obtain ⟨hab, hl⟩ := List.append_inj h hw.1
      rw [hab, ih l₂ hw.2 hl]

/-- Binding of the commitment to a batch of `n > 0` matrices of height `2 ^ k`: two accepted
openings of the same index with different rows of the same widths give a collision of `hash` on
the leaves or of `compress`. -/
theorem verifyBatch_binding [DecidableEq F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (commit : Vector F d) (n k i : Nat)
    (hn : 0 < n) (values₁ values₂ : List (List F)) (path₁ path₂ : List (Vector F d))
    (h₁ : verifyBatch hash compress commit (List.replicate n (2 ^ k)) i values₁ path₁ = true)
    (h₂ : verifyBatch hash compress commit (List.replicate n (2 ^ k)) i values₂ path₂ = true)
    (hw : values₁.map List.length = values₂.map List.length) (hne : values₁ ≠ values₂) :
    (values₁.flatten ≠ values₂.flatten ∧ hash values₁.flatten = hash values₂.flatten) ∨
      ∃ l₁ r₁ l₂ r₂, Collision compress l₁ r₁ l₂ r₂ := by
  have hlen (values path) (h : verifyBatch hash compress commit (List.replicate n (2 ^ k)) i
      values path = true) : path.reverse.length = (SkeletonLeafIndex.ofNat k i).depth := by
    simp only [verifyBatch, heightGroups_replicate n _ hn, Bool.and_eq_true, beq_iff_eq,
      Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k), Nat.log2_two_pow] at h
    rw [List.length_reverse, h.1.1.2, SkeletonLeafIndex.depth_ofNat]
  have hf : values₁.flatten ≠ values₂.flatten := fun h ↦
    hne (flatten_injective_of_lengths _ _ hw h)
  rw [verifyBatch_iff hash compress commit n k i hn values₁ path₁ ⟨_, hlen _ _ h₁⟩ rfl] at h₁
  rw [verifyBatch_iff hash compress commit n k i hn values₂ path₂ ⟨_, hlen _ _ h₂⟩ rfl] at h₂
  by_cases hh : hash values₁.flatten = hash values₂.flatten
  · exact Or.inl ⟨hf, hh⟩
  · obtain ⟨l₁, r₁, l₂, r₂, -, hc⟩ := getPutativeRootWithHash_binding_collision compress _ _ _
      _ _ hh (h₁.2.2.trans h₂.2.2.symm)
    exact Or.inr ⟨l₁, r₁, l₂, r₂, hc⟩

/-- Completeness: an honest opening at `i < 2 ^ k` of a batch of matrices of height `2 ^ k`
verifies against its commitment, as an instance of VCVio's `functional_completeness`. -/
theorem verifyBatch_openBatch [Zero F] [DecidableEq F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (ms : List (Matrix F)) (k i : Nat)
    (hms : ms ≠ []) (hh : ∀ m ∈ ms, m.height = 2 ^ k) (hi : i < 2 ^ k) :
    verifyBatch hash compress (root hash compress ms) (ms.map (·.height)) i
      (openBatch hash compress ms i).1 (openBatch hash compress ms i).2 = true := by
  have hheights : ms.map (·.height) = List.replicate ms.length (2 ^ k) :=
    List.eq_replicate_iff.mpr ⟨List.length_map _, fun b hb ↦ by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb; exact hh m hm⟩
  have hpos : 0 < ms.length := List.length_pos_iff.mpr hms
  rw [hheights, verifyBatch_iff hash compress _ _ k i hpos _ _ _
      (by rw [openBatch_snd hash compress ms k i hms hh hi, List.reverse_reverse]),
    openBatch_fst hash compress ms k i hh,
    root_eq_buildMerkleTreeWithHash hash compress ms k hms hh]
  refine ⟨List.length_map _, hi, ?_⟩
  have hleaf : hash (ms.map (·.row i)).flatten = (leafData hash ms k).get
      (SkeletonLeafIndex.ofNat k i) := by
    rw [leafData, ← Nat.div_eq_of_lt hi, perfectLeaves_get, leafHashes, List.flatMap_def]
  rw [hleaf]
  exact functional_completeness _ _ _


end CompStark.Merkle
