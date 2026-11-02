/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Mixed
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Extract

/-! # Extracting committed rows

A Plonky3 tree of matrices of heights `2 ^ j ≤ 2 ^ K` is VCVio's tree with injected payloads
(`MixedMerkleTree`): the rows of the tallest matrices are its leaves' payloads, and the rows of
the matrices of height `2 ^ t < 2 ^ K` are injected at depth `t` (`injLevels`). VCVio's
`MixedMerkleTree.extract` reads such a tree back from a cache of answered hash queries; this file
connects it to Plonky3's openings:

* `extractGroup_of_verifyBatch`: in an injective cache, an accepted opening whose leaf hash and
  climb are cached opens the extracted rows of every group of matrices of one height.
* `extractRow_eq_of_verifyBatch`: the same for matrices of one height.
* `extractCapRow`: extraction under a Merkle cap of height `h`, capped at the tree's levels, as
  Plonky3 caps its trees.

`matColumn` reads column `j` of matrix `t` off its group's extracted rows, at the matrix's offset
among the matrices of its height (`matOffset`).
-/

@[expose] public section
namespace CompStark.Merkle

open MixedMerkleTree (Cache ClimbCached extract)

/-- The injected levels of matrices of heights `heights` below `2 ^ K`: the depths `log₂ h` of the
heights `h < 2 ^ K`. -/
def injLevels (K : Nat) (heights : List Nat) (t : Nat) : Bool :=
  heights.any fun h ↦ decide (h < 2 ^ K) && h.log2 == t

theorem injLevels_iff (K : Nat) (heights : List Nat) (t : Nat) :
    injLevels K heights t = true ↔ ∃ h ∈ heights, h < 2 ^ K ∧ h.log2 = t := by
  simp only [injLevels, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]

/-! ### Openings of mixed heights -/

section Climb
variable {F : Type} {d : Nat} (cache : Cache (List F) (Vector F d)) (hash : List F → Vector F d)
  (compress : Vector F d → Vector F d → Vector F d) (values : List (List F))

/-- **Accepted openings of mixed heights open the extracted rows.** In an injective cache, an
accepted opening at `i` of matrices of heights `2 ^ j ≤ 2 ^ K`, some of height `2 ^ K`, whose
leaf hash and climb are cached, opens every group's extracted rows: the opened rows of the
matrices of each height, concatenated, at the index shifted to that height. -/
theorem extractGroup_of_verifyBatch [Zero F] [DecidableEq F] (hinj : cache.Injective)
    (root : Vector F d) (K : Nat) (heights : List Nat) (hpow : ∀ h ∈ heights, ∃ j ≤ K, h = 2 ^ j)
    (htop : 2 ^ K ∈ heights) (i : Nat) (path : List (Vector F d))
    (hv : verifyBatch hash compress root heights i values path = true)
    (hleaf : ∀ g ∈ (heightGroups heights).head?, cache.leaf (g.2.flatMap fun m ↦ values.getD m [])
      (hash (g.2.flatMap fun m ↦ values.getD m [])))
    (hc : ∀ g ∈ (heightGroups heights).head?, ClimbCached cache hash compress
      (climbPays values path.length (heightGroups heights).tail (2 ^ K)) i
      (hash (g.2.flatMap fun m ↦ values.getD m [])) path) :
    ∀ g ∈ heightGroups heights, ∀ l, g.1 = 2 ^ l →
      extract cache (injLevels K heights) K l (i >>> (K - l)) root =
        some (g.2.flatMap fun m ↦ values.getD m []) := by
  obtain ⟨keys, hk, hmem, hG⟩ := heightGroups_eq heights
  obtain ⟨ks, hks⟩ : ∃ ks, keys = 2 ^ K :: ks := by
    rcases keys with _ | ⟨a, ks⟩
    · exact absurd ((hmem _).mpr htop) List.not_mem_nil
    · refine ⟨ks, ?_⟩
      obtain ⟨j, hj, rfl⟩ := hpow a ((hmem a).mp List.mem_cons_self)
      rcases List.mem_cons.mp ((hmem _).mpr htop) with h | h
      · rw [h]
      · have := List.rel_of_pairwise_cons hk h
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj
        omega
  set idx : Nat → List Nat := fun h ↦ (List.range heights.length).filter (heights.getD · 0 == h)
  have hksl : ∀ h ∈ ks, ∃ j < K, h = 2 ^ j := fun h hh ↦ by
    obtain ⟨j, hj, rfl⟩ := hpow h ((hmem h).mp (hks ▸ List.mem_cons_of_mem _ hh))
    have := List.rel_of_pairwise_cons (hks ▸ hk) hh
    exact ⟨j, (Nat.pow_lt_pow_iff_right (by decide)).mp this, rfl⟩
  set G := ks.map fun h ↦ (h, idx h) with hGdef
  have hGs : G.Pairwise fun a b ↦ b.1 < a.1 := List.pairwise_map.mpr ((hks ▸ hk).of_cons.imp id)
  have hGp : ∀ g ∈ G, ∃ j < K, g.1 = 2 ^ j := fun g hg ↦ by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact hksl h hh
  rw [hG, hks, List.map_cons] at hleaf hc ⊢
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq', List.tail_cons]
    at hleaf hc
  simp only [verifyBatch, hG, hks, List.map_cons, nextPowerOfTwo_two_pow, Nat.log2_two_pow,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨-, -⟩, hpl⟩, -⟩, hclimb⟩ := hv
  rw [climb_eq] at hclimb
  rw [hpl] at hc hclimb
  have hsched := sched_eq_find K K G le_rfl hGs hGp
  -- The injected depths are the depths of the shorter groups.
  have hinjl : ∀ l < K, injLevels K heights l = true ↔ ∃ g ∈ G, g.1 = 2 ^ l := by
    intro l hl
    rw [injLevels_iff]
    constructor
    · rintro ⟨h, hh, hlt, rfl⟩
      obtain ⟨j, -, rfl⟩ := hpow h hh
      rw [Nat.log2_two_pow]
      have hk' : 2 ^ j ∈ keys := (hmem _).mpr hh
      rw [hks] at hk'
      rcases List.mem_cons.mp hk' with e | hk'
      · omega
      · exact ⟨_, List.mem_map_of_mem hk', rfl⟩
    · rintro ⟨g, hg, hgl⟩
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      dsimp only at hgl
      subst hgl
      exact ⟨2 ^ l, (hmem _).mp (hks ▸ List.mem_cons_of_mem _ hh),
        Nat.pow_lt_pow_right (by decide) hl, Nat.log2_two_pow⟩
  have hpays : ∀ l < K, ∀ g ∈ G, g.1 = 2 ^ l →
      climbPays values K G (2 ^ K) l = some (g.2.flatMap fun m ↦ values.getD m []) := by
    intro l hl g hg hgl
    rw [climbPays, hsched l hl, Nat.sub_self, Nat.add_zero, ← hgl, find?_height_eq hGs hg]
    rfl
  have hinjd : ∀ l < path.length, injLevels K heights l =
      (climbPays values K G (2 ^ K) l).isSome := by
    intro l hl
    rw [hpl] at hl
    rw [Bool.eq_iff_iff, hinjl l hl]
    constructor
    · rintro ⟨g, hg, hgl⟩
      rw [hpays l hl g hg hgl, Option.isSome_some]
    · intro h
      rw [climbPays, hsched l hl, Option.map_map, Option.isSome_map, Option.isSome_iff_exists]
        at h
      obtain ⟨g, hg⟩ := h
      exact ⟨g, List.mem_of_find?_eq_some hg, by
        simpa only [beq_iff_eq, Nat.add_zero, Nat.sub_self] using List.find?_some hg⟩
  obtain ⟨hn, hext⟩ := MixedMerkleTree.extract_of_climb cache hash compress hinj
    (injLevels K heights) K root (climbPays values K G (2 ^ K)) path i _ hpl.le hinjd hc hclimb
  intro g hg l hgl
  rcases List.mem_cons.mp hg with rfl | hg
  · have hl : l = K := Nat.pow_right_injective (le_refl 2) hgl.symm
    subst hl
    rw [Nat.sub_self, Nat.shiftRight_zero]
    rw [hpl] at hn
    exact MixedMerkleTree.extract_leaf cache hinj _ _ _ root _ _ hn hleaf
  · obtain ⟨j, hj, hgj⟩ := hGp g hg
    have hl : l = j := Nat.pow_right_injective (le_refl 2) (hgl.symm.trans hgj)
    subst hl
    have := hext l (by omega) _ (hpays l hj g hg hgl)
    rwa [hpl] at this

/-- **Accepted openings open the extracted rows.** In an injective cache, an accepted opening at
`i` of `n > 0` matrices of height `2 ^ k` against `root`, whose leaf hash and compressions are all
cached, opens the extracted row `i`: the concatenated opened rows. -/
theorem extractRow_eq_of_verifyBatch [Zero F] [DecidableEq F] (hinj : cache.Injective)
    (root : Vector F d) (n k i : Nat) (hn : 0 < n) (path : List (Vector F d))
    (hv : verifyBatch hash compress root (List.replicate n (2 ^ k)) i values path = true)
    (hleaf : cache.leaf values.flatten (hash values.flatten))
    (hc : ClimbCached cache hash compress (fun _ ↦ none) i (hash values.flatten) path) :
    extract cache (fun _ ↦ false) k k i root = some values.flatten := by
  simp only [verifyBatch, heightGroups_replicate n _ hn, List.tail_cons, List.zip_nil_right,
    List.all_nil, Bool.true_and, List.length_replicate, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, nextPowerOfTwo_two_pow, Nat.log2_two_pow] at hv
  obtain ⟨⟨⟨hl, hpl⟩, -⟩, hclimb⟩ := hv
  rw [climb_eq, climbPays_nil, hashRows, ← hl, flatMap_range_getD] at hclimb
  obtain ⟨hnode, -⟩ := MixedMerkleTree.extract_of_climb cache hash compress hinj (fun _ ↦ false) k
    root (fun _ ↦ none) path i _ hpl.le (fun _ _ ↦ rfl) hc hclimb
  rw [hpl] at hnode
  exact MixedMerkleTree.extract_leaf cache hinj _ _ _ root _ _ hnode hleaf

end Climb

/-! ### Caps and columns -/

section Columns
variable {F D : Type*}

/-- The row committed at index `i` of the depth-`k` tree under the cap `cap` of height `h`, capped
at `k`: the row at the index's low `l` bits of the depth-`l` subtree under the index's cap entry,
for the `l` levels below the cap. -/
noncomputable def extractCapRow [Zero D] (cache : Cache (List F) D) (k h i : Nat)
    (cap : List D) : Option (List F) :=
  extract cache (fun _ ↦ false) (k - min h k) (k - min h k) (i % 2 ^ (k - min h k))
    (cap.getD (i >>> (k - min h k)) 0)

/-- The offset of matrix `t`'s columns among its group's: the widths `ws` of the earlier matrices
of its height. -/
def matOffset (hs ws : List ℕ) (t : ℕ) : ℕ :=
  (((List.range t).filter fun t' ↦ hs.getD t' 0 = hs.getD t 0).map (ws.getD · 0)).sum

/-- Column `j` of matrix `t`, of heights `hs` and widths `ws`, at row `r` of its height `2 ^ m`,
extracted under `root`: entry `j` past its offset of its group's extracted rows, zero where
nothing is extracted. -/
noncomputable def matColumn [Zero F] (cache : Cache (List F) D) (root : D) (K : ℕ)
    (hs ws : List ℕ) (t j m r : ℕ) : F :=
  ((extract cache (injLevels K hs) K m r root).getD []).getD (matOffset hs ws t + j) 0

/-- Column `j` of matrix `t` at row `r` of its height `2 ^ m`, extracted under the cap `cap` of
height `capHeight` (capped at `K`, `c` levels): `matColumn` in the subtree under the row's cap
entry, whose matrices have the heights divided by `2 ^ c`, at the row's low `m - c` bits. -/
noncomputable def matColumnCap [Zero F] [Zero D] (cache : Cache (List F) D) (cap : List D)
    (capHeight K : ℕ) (hs ws : List ℕ) (t j m r : ℕ) : F :=
  matColumn cache (cap.getD (r >>> (m - min capHeight K)) 0) (K - min capHeight K)
    (hs.map (· / 2 ^ min capHeight K)) ws t j (m - min capHeight K)
    (r % 2 ^ (m - min capHeight K))

end Columns

end CompStark.Merkle
