/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Plonky3.Prover
public import CompStark.Stark.Points
public import CompStark.Fri.Verifier
public import CompStark.Merkle.Multi

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

/-- Concatenating a list of `n` lists by index. -/
theorem flatMap_range_getD {β : Type*} (l : List (List β)) :
    (List.range l.length).flatMap (l.getD · []) = l.flatten := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.getD_cons_zero,
      List.flatMap_map, Nat.succ_eq_add_one, List.getD_cons_succ, ih, List.flatten_cons]

/-- The root of a batch of matrices of one height `2 ^ k` is the tree's top node. -/
theorem root_eq_nodeValue [Poseidon2Field F] (ms : List (Mat F)) (k : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = 2 ^ k) :
    (Committed.ofMats hashF compF ms).root =
      nodeValue compF (leafHashes hashF (ms.map Mat.toMatrix)) k 0 := by
  have hms' : ∀ m ∈ ms.map Mat.toMatrix, m.height = 2 ^ k := fun m hm ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact hms a ha
  have hne' : ms.map Mat.toMatrix ≠ [] := by rwa [Ne, List.map_eq_nil_iff]
  rw [root_ofMats, root_eq_layers, layers_eq_nodeValue _ _ _ k hne' hms', List.range_succ,
    List.map_append, List.getLastD_eq_getLast?, List.getLast?_append, List.map_cons,
    List.map_nil, List.getLast?_singleton]
  simp only [Option.some_or, Option.getD_some, Nat.sub_self, Nat.pow_zero, List.range_one,
    List.map_cons, List.map_nil, List.headD_cons]

/-- **Honest multi-openings verify.** The specification's multi-opening at indices below the
height of a batch of matrices of one height `2 ^ k` verifies against its root. -/
theorem verifyMulti_openMulti [Poseidon2Field F] (ms : List (Mat F)) (k : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = 2 ^ k ∧ m.values.size = m.width * m.height)
    (indices : List Nat) (hidx : ∀ i ∈ indices, i < 2 ^ k) :
    Merkle.verifyMultiM (m := Id) hashF compF (Committed.ofMats hashF compF ms).root
      (ms.map fun m ↦ (m.height, m.width)) indices
      (indices.map fun i ↦ ((Committed.ofMats hashF compF ms).openAt i).values.toList.map
        (·.toList))
      (Merkle.prune k indices
        (indices.map fun i ↦ ((Committed.ofMats hashF compF ms).openAt i).path.toList)) = true := by
  have hh : ∀ m ∈ ms, m.height = 2 ^ k := fun m hm ↦ (hms m hm).1
  have hms' : ∀ m ∈ ms.map Mat.toMatrix, m.height = 2 ^ k := fun m hm ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact hh a ha
  have hne' : ms.map Mat.toMatrix ≠ [] := by rwa [Ne, List.map_eq_nil_iff]
  have hrows : ∀ i, ((Committed.ofMats hashF compF ms).openAt i).values.toList.map (·.toList) =
      (ms.map Mat.toMatrix).map (·.row i) := fun i ↦ by
    rw [openAt_values ms k hh, List.toList_toArray, List.map_map, List.map_map]
    exact List.map_congr_left fun m _ ↦ rowOf_toList m i
  rw [root_eq_nodeValue ms k hne hh]
  have hrows' : (indices.map fun i ↦ ((Committed.ofMats hashF compF ms).openAt i).values.toList.map
      (·.toList)) = indices.map fun i ↦ (ms.map Mat.toMatrix).map (·.row i) :=
    List.map_congr_left fun i _ ↦ hrows i
  rw [hrows']
  refine Merkle.verifyMulti_prune hashF compF (leafHashes hashF (ms.map Mat.toMatrix)) ms.length k
    (List.length_pos_iff.mpr hne) (ms.map fun m ↦ (m.height, m.width)) ?_
    (fun i ↦ (ms.map Mat.toMatrix).map (·.row i)) ?_ ?_ indices hidx
    (indices.map fun i ↦ ((Committed.ofMats hashF compF ms).openAt i).path.toList) ?_
  · rw [List.map_map]
    exact List.eq_replicate_iff.mpr ⟨by rw [List.length_map], fun b hb ↦ by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb; exact hh m hm⟩
  · intro i
    simp only [List.map_map]
    refine List.map_congr_left fun m _ ↦ ?_
    simp only [Function.comp_apply, Merkle.Matrix.row, List.length_map, List.length_range,
      Mat.toMatrix]
  · intro i
    have e := flatMap_range_getD ((ms.map Mat.toMatrix).map (·.row i))
    rw [List.length_map, List.length_map] at e
    rw [leafHashes, e, List.flatMap_def]
  · intro q hq j hj
    have hp : (indices.map fun i ↦ ((Committed.ofMats hashF compF ms).openAt i).path.toList).getD
        q [] = ((Committed.ofMats hashF compF ms).openAt indices[q]).path.toList := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq]
      rfl
    rw [hp, openAt_path ms k hne hh,
      Merkle.openBatch_snd_eq_nodeValue _ _ _ k _ hne' hms' (hidx _ (List.getElem_mem hq)),
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl

/-- On Poseidon2, the verifier's multi-opening check is `Merkle.verifyMultiM` on Poseidon2's
hashes. -/
theorem checkMulti_eq [Poseidon2Field F] (commit : Digest F) (dims : List (Nat × Nat))
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Digest F))
    (t : Transcript F 24) :
    checkMulti (poseidon2 F) commit dims indices rows sibs t =
      .ok (Merkle.verifyMultiM (m := Id) hashF compF commit dims indices rows sibs, t) := rfl

end CompStark.Fri
