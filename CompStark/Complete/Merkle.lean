/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Plonky3.Prover
public import CompStark.Stark.Points
public import CompStark.Fri.Verifier
public import CompStark.Merkle.Mixed

/-! # Honest Merkle openings verify

Every commitment of the uni-stark prover holds matrices of one height `2 ^ k`: the trace's
extension, the quotient chunks' extensions, each commit-phase round. For such a batch the
specification's opening `Committed.openAt` at any row verifies against `Committed.root`.

`Merkle.verifyBatch_openBatch` proves this for `Merkle.openBatch` and `Merkle.root` over any
`hash` and `compress`. `(Committed F)` stores the same digest layers as arrays, so its root is
`Merkle.root`, its path is `Merkle.openBatch`'s, and, with one height, its rows are the rows at the
index unshifted, which are `Merkle.openBatch`'s rows.

The verifier checks openings at all queries at once (`checkMulti`): the specification's
multi-opening `openMulti` of such a batch at indices within its height verifies against its root
(`verifyMulti_openMulti`), by `Merkle.verifyMulti_prune` on the tree's nodes.
-/

@[expose] public section

namespace CompStark.Fri
open CompStark.Stark CompStark.Merkle

variable {F : Type}
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

/-- A running maximum from at most `h` over matrices of height `h` is `h`. -/
theorem foldl_max_height (ms : List (Mat F)) (h : Nat)
    (hms : ∀ m ∈ ms, m.height = h) : ∀ acc, acc ≤ h → ms ≠ [] → ms.foldl
        (fun m a ↦ max m a.height) acc = h := by
  induction ms with
  | nil => intro _ _ hne; exact absurd rfl hne
  | cons a t ih =>
    intro acc hacc _
    rw [List.foldl_cons, hms a List.mem_cons_self, Nat.max_eq_right hacc]
    cases t with
    | nil => rfl
    | cons b t =>
      exact ih (fun m hm ↦ hms m (List.mem_cons_of_mem a hm)) h (Nat.le_refl h)
        (List.cons_ne_nil b t)

/-! ### Mixed heights -/

/-- Matrices of heights `2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`. -/
def MixedHeights (k : Nat) (ms : List (Mat F)) : Prop :=
  (∀ m ∈ ms, ∃ j ≤ k, m.height = 2 ^ j) ∧ ∃ m ∈ ms, m.height = 2 ^ k

theorem MixedHeights.toMatrix {k : Nat} {ms : List (Mat F)} (h : MixedHeights k ms) :
    (∀ m ∈ ms.map Mat.toMatrix, ∃ j ≤ k, m.height = 2 ^ j) ∧
      ∃ m ∈ ms.map Mat.toMatrix, m.height = 2 ^ k := by
  refine ⟨fun m hm ↦ ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact h.1 a ha
  · obtain ⟨a, ha, hk⟩ := h.2; exact ⟨a.toMatrix, List.mem_map_of_mem ha, hk⟩

/-- A running maximum of heights at most `2 ^ k`, one of them `2 ^ k`, is `2 ^ k`. -/
theorem foldl_max_mixed (k : Nat) : ∀ (ms : List (Mat F)) (acc : Nat), acc ≤ 2 ^ k →
    (∀ m ∈ ms, m.height ≤ 2 ^ k) → (acc = 2 ^ k ∨ ∃ m ∈ ms, m.height = 2 ^ k) →
    ms.foldl (fun a m ↦ max a m.height) acc = 2 ^ k
  | [], acc, _, _, h => by
    rcases h with h | ⟨m, hm, -⟩
    · exact h
    · exact absurd hm List.not_mem_nil
  | m :: ms, acc, hacc, hle, h => by
    rw [List.foldl_cons]
    refine foldl_max_mixed k ms _ (Nat.max_le.mpr ⟨hacc, hle m List.mem_cons_self⟩)
      (fun x hx ↦ hle x (List.mem_cons_of_mem _ hx)) ?_
    rcases h with h | ⟨x, hx, hxk⟩
    · left; rw [h]; exact Nat.max_eq_left (hle m List.mem_cons_self)
    · rcases List.mem_cons.mp hx with rfl | hx
      · left; rw [hxk]; exact Nat.max_eq_right hacc
      · right; exact ⟨x, hx, hxk⟩

variable [BaseField F]

/-- The largest height of matrices of one height `h` is `h`. -/
theorem maxHeight_ofMats [Poseidon2Field F] (ms : List (Mat F)) (h : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = h) : (Committed.ofMats hashF compF ms).maxHeight = h :=
  foldl_max_height ms h hms 0 (Nat.zero_le h) hne

/-- `rowOf` is the Merkle tree's row. -/
theorem rowOf_toList (m : Mat F) (i : Nat) : (rowOf m i).toList = m.toMatrix.row i := by
  apply List.ext_getElem
  · simp only [rowOf, Array.toList_ofFn, List.length_ofFn, Merkle.Matrix.row, Mat.toMatrix,
      List.length_map, List.length_range]
  · intro j h1 h2
    simp only [rowOf, Array.toList_ofFn, List.getElem_ofFn, Merkle.Matrix.row, Mat.toMatrix,
      List.getElem_map, List.getElem_range]

/-- The committed root is the Merkle root. -/
theorem root_ofMats [Poseidon2Field F] (ms : List (Mat F)) :
    (Committed.ofMats hashF compF ms).root =
      Merkle.root (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F) (ms.map Mat.toMatrix) := by
  rw [Merkle.root_eq_layers]
  simp only [Committed.ofMats, Committed.root]
  generalize Merkle.layers (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F)
    (ms.map Mat.toMatrix) = ls
  simp only [List.back?_toArray, List.getLast?_map, List.getLastD_eq_getLast?]
  cases ls.getLast? with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Option.getD_some, List.headD_eq_getD, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- The opening's rows of matrices of one height `2 ^ k` are their rows at the index. -/
theorem openAt_values [Poseidon2Field F] (ms : List (Mat F)) (k : Nat)
    (hms : ∀ m ∈ ms, m.height = 2 ^ k) (i : Nat) :
    ((Committed.ofMats hashF compF ms).openAt i).values = (ms.map fun m ↦ rowOf m i).toArray := by
  simp only [Committed.openAt]
  congr 1
  apply List.map_congr_left
  intro m hm
  rw [maxHeight_ofMats ms (2 ^ k) (List.ne_nil_of_mem hm) hms, hms m hm, Nat.sub_self,
    Nat.shiftRight_zero]

theorem getD_toArrays {α : Type*} [Zero α] (ls : List (List α)) (j x : Nat) :
    (((ls.map List.toArray).toArray.getD j #[]).getD x 0) = (ls.getD j []).getD x 0 := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases ls[j]? <;> simp only [Option.map_some, Option.map_none, Option.getD_some,
    Option.getD_none, List.getElem?_toArray, List.getElem?_nil]

/-- The opening's path of matrices of one height `2 ^ k` is `Merkle.openBatch`'s. -/
theorem openAt_path [Poseidon2Field F] (ms : List (Mat F)) (k : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = 2 ^ k) (i : Nat) :
    ((Committed.ofMats hashF compF ms).openAt i).path.toList =
      (Merkle.openBatch (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F)
        (ms.map Mat.toMatrix) i).2 := by
  have hms' : ∀ m ∈ ms.map Mat.toMatrix, m.height = 2 ^ k := fun m hm ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact hms a ha
  have hne' : ms.map Mat.toMatrix ≠ [] := by
    rwa [Ne, List.map_eq_nil_iff]
  have hmax : ((sortTallest (ms.map Mat.toMatrix)).headD ⟨0, 0, #[]⟩).height = 2 ^ k := by
    rw [sortTallest_of_height _ _ hms']
    obtain ⟨m, ms', h⟩ := List.exists_cons_of_ne_nil hne'
    rw [h, List.headD_cons]; exact hms' m (h ▸ List.mem_cons_self)
  simp only [Committed.openAt, maxHeight_ofMats ms _ hne hms]
  simp only [Merkle.openBatch, openWith, hmax, Array.toList_ofFn, Committed.ofMats,
    Committed.maxHeight, foldl_max_height ms _ hms 0 (Nat.zero_le _) hne]
  apply List.ext_getElem (by simp only [List.length_ofFn, List.length_map, List.length_range])
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, getD_toArrays, Fin.val_cast]

/-- The specification's opening at row `i` of a batch of matrices of one height `2 ^ k`
verifies against its root. -/
theorem verifyBatch_openAt [Poseidon2Field F] (ms : List (Mat F)) (k : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = 2 ^ k ∧ m.values.size = m.width * m.height)
    (i : Nat) (hi : i < 2 ^ k) :
    Merkle.Poseidon2.verifyBatch F (Committed.ofMats hashF compF ms).root
      (ms.map (·.height)) i
          (((Committed.ofMats hashF compF ms).openAt i).values.toList.map (·.toList))
      ((Committed.ofMats hashF compF ms).openAt i).path.toList = true := by
  have hh : ∀ m ∈ ms, m.height = 2 ^ k := fun m hm ↦ (hms m hm).1
  have hh' : ∀ m ∈ ms.map Mat.toMatrix, m.height = 2 ^ k := fun m hm ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact hh a ha
  have hne' : ms.map Mat.toMatrix ≠ [] := by
    rwa [Ne, List.map_eq_nil_iff]
  have hv : ((Committed.ofMats hashF compF ms).openAt i).values.toList.map (·.toList) =
      (Merkle.openBatch (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F)
        (ms.map Mat.toMatrix) i).1 := by
    rw [openAt_values ms k hh, Merkle.openBatch_fst _ _ _ k i hh', List.toList_toArray,
      List.map_map, List.map_map]
    exact List.map_congr_left fun m _ ↦ rowOf_toList m i
  have hH : ms.map (·.height) = (ms.map Mat.toMatrix).map (·.height) := by
    rw [List.map_map]; rfl
  rw [root_ofMats, hv, openAt_path ms k hne hh, hH]
  exact Merkle.verifyBatch_openBatch _ _ _ k i hne' hh' hi

theorem maxHeight_mixed [Poseidon2Field F] {k : Nat} {ms : List (Mat F)}
    (h : MixedHeights k ms) : (Committed.ofMats hashF compF ms).maxHeight = 2 ^ k :=
  foldl_max_mixed k ms 0 (Nat.zero_le _) (fun m hm ↦ by
    obtain ⟨j, hj, hj'⟩ := h.1 m hm
    rw [hj']; exact Nat.pow_le_pow_right (by decide) hj) (Or.inr h.2)

/-- The opening's rows of matrices of mixed heights are their rows at the index shifted to their
heights. -/
theorem openAt_values_mixed [Poseidon2Field F] {k : Nat} {ms : List (Mat F)}
    (h : MixedHeights k ms) (i : Nat) :
    ((Committed.ofMats hashF compF ms).openAt i).values =
      (ms.map fun m ↦ rowOf m (i >>> (k - Nat.log2 m.height))).toArray := by
  simp only [Committed.openAt, maxHeight_mixed h, log2Ceil_two_pow]
  congr 1
  refine List.map_congr_left fun m hm ↦ ?_
  obtain ⟨j, -, hj⟩ := h.1 m hm
  rw [hj, log2Ceil_two_pow, Nat.log2_two_pow]

/-- The root of matrices of mixed heights is the tree's top node. -/
theorem root_eq_injNode [Poseidon2Field F] {k : Nat} {ms : List (Mat F)}
    (h : MixedHeights k ms) :
    (Committed.ofMats hashF compF ms).root =
      injNode hashF compF (ms.map Mat.toMatrix) k k 0 := by
  obtain ⟨h1, h2⟩ := h.toMatrix
  rw [root_ofMats, root_eq_layers, layers_eq_injNode _ _ _ k h1 h2, List.range_succ,
    List.map_append, List.getLastD_eq_getLast?, List.getLast?_append, List.map_cons,
    List.map_nil, List.getLast?_singleton]
  simp only [Option.some_or, Option.getD_some, Nat.sub_self, Nat.pow_zero, List.range_one,
    List.map_cons, List.map_nil, List.headD_cons]

/-- The opening's path at `i < 2 ^ k` of matrices of mixed heights: the sibling
`(i >>> j) ^^^ 1` of every level `j < k`. -/
theorem openAt_path_mixed [Poseidon2Field F] {k : Nat} {ms : List (Mat F)}
    (h : MixedHeights k ms) (i : Nat) (hi : i < 2 ^ k) :
    ((Committed.ofMats hashF compF ms).openAt i).path.toList =
      (List.range k).map fun j ↦
        injNode hashF compF (ms.map Mat.toMatrix) k j ((i >>> j) ^^^ 1) := by
  obtain ⟨h1, h2⟩ := h.toMatrix
  have hk : log2Ceil (Committed.ofMats hashF compF ms).maxHeight = k := by
    rw [maxHeight_mixed h, log2Ceil_two_pow]
  simp only [Committed.openAt, Array.toList_ofFn]
  apply List.ext_getElem (by simp only [List.length_ofFn, List.length_map, List.length_range, hk])
  intro j hj1 hj2
  rw [List.length_ofFn, hk] at hj1
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, Committed.ofMats,
    getD_toArrays]
  have hx : (i >>> j) ^^^ 1 < 2 ^ (k - j) := by
    rw [xor_one_eq, Nat.shiftRight_eq_div_pow]
    obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
    have h1 : i / 2 ^ j < 2 ^ (e + 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), ← Nat.pow_add]
      exact lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega))
    rw [he, Nat.pow_succ] at *
    have := Nat.mod_lt (i / 2 ^ j + 1) (show 2 > 0 by decide)
    omega
  rw [layers_eq_injNode _ _ _ k h1 h2, getD_map_range' _ _ _ _ (by omega), getD_map_range' _ _ _ _ hx]

/-- **Honest multi-openings verify.** The specification's multi-opening at indices below
`2 ^ k` of matrices of heights `2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`, verifies against its
root. -/
theorem verifyMulti_openMulti [Poseidon2Field F] {k : Nat} {ms : List (Mat F)}
    (h : MixedHeights k ms) (indices : List Nat) (hidx : ∀ i ∈ indices, i < 2 ^ k) :
    Merkle.verifyMultiM (m := Id) hashF compF (Committed.ofMats hashF compF ms).root
      (ms.map fun m ↦ (m.height, m.width)) indices
      (indices.map fun i ↦ ((Committed.ofMats hashF compF ms).openAt i).values.toList.map
        (·.toList))
      (Merkle.prune k indices
        (indices.map fun i ↦ ((Committed.ofMats hashF compF ms).openAt i).path.toList)) = true := by
  obtain ⟨h1, h2⟩ := h.toMatrix
  have hrows : ∀ i, ((Committed.ofMats hashF compF ms).openAt i).values.toList.map (·.toList) =
      (ms.map Mat.toMatrix).map fun m ↦ m.row (i >>> (k - Nat.log2 m.height)) := fun i ↦ by
    rw [openAt_values_mixed h, List.toList_toArray, List.map_map, List.map_map]
    exact List.map_congr_left fun m _ ↦ rowOf_toList m _
  have hdims : (ms.map fun m ↦ (m.height, m.width)) =
      (ms.map Mat.toMatrix).map fun m ↦ (m.height, m.width) := by
    rw [List.map_map]; rfl
  rw [root_eq_injNode h, hdims, List.map_congr_left fun i _ ↦ hrows i]
  refine Merkle.verifyMulti_prune_mixed hashF compF (ms.map Mat.toMatrix) k h1 h2 indices hidx _
    fun q hq j hj ↦ ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq,
    Option.map_some, Option.getD_some]
  rw [openAt_path_mixed h _ (hidx _ (List.getElem_mem hq))]
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]

/-- On Poseidon2, the verifier's multi-opening check is `Merkle.verifyMultiM` on Poseidon2's
hashes. -/
theorem checkMulti_eq [Poseidon2Field F] (commit : Digest F) (dims : List (Nat × Nat))
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Digest F))
    (t : Transcript F 24) :
    checkMulti (poseidon2 F) commit dims indices rows sibs t =
      .ok (Merkle.verifyMultiM (m := Id) hashF compF commit dims indices rows sibs, t) := rfl

end CompStark.Fri
