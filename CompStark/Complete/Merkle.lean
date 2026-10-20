/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Fri.Verifier
public import CompStark.Merkle.VCVio

/-! # Honest Merkle openings verify

Every commitment of the uni-stark prover holds matrices of one height `2 ^ k`: the trace's
extension, the quotient chunks' extensions, each commit-phase round. For such a batch the
specification's opening `Committed.openAt` at any row verifies against `Committed.root`.

`Merkle.verifyBatch_openBatch` proves this for `Merkle.openBatch` and `Merkle.root` over any
`hash` and `compress`. `Committed` stores the same digest layers as arrays, so its root is
`Merkle.root`, its path is `Merkle.openBatch`'s, and, with one height, its rows are the rows at the
index unshifted, which are `Merkle.openBatch`'s rows.

On Poseidon2 the verifier's `checkOpening` is `Merkle.KoalaBear.verifyBatch` (`checkOpening_eq`),
by `Merkle.verifyBatchM_pure`: with pure hashes the monadic opening check is the pure one.
-/

@[expose] public section

namespace CompStark.Merkle
variable {F : Type} {d : Nat} {m : Type → Type} [Monad m] [LawfulMonad m]


theorem climbM_pure (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (values : List (List F)) :
    ∀ path groups index padded root,
      climbM (m := m) (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values path groups
        index padded root = pure (climb hash compress values path groups index padded root)
  | [], _, _, _, _ => rfl
  | sib :: sibs, groups, index, padded, root => by
    simp only [climbM, climb]
    have step : ∀ root : Vector F d, (do
        let root ← (pure root : m (Vector F d))
        match groups with
        | (h, is) :: rest =>
          if h.nextPowerOfTwo = padded / 2 then do
            let leaf ← pure (hash (is.flatMap fun i ↦ values.getD i []))
            let root ← pure (compress root leaf)
            (climbM (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values sibs rest
              (index / 2) (padded / 2) root)
          else (climbM (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values sibs
            groups (index / 2) (padded / 2) root)
        | [] => (climbM (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values sibs []
            (index / 2) (padded / 2) root)) =
        pure (match groups with
          | (h, is) :: rest =>
            if h.nextPowerOfTwo = padded / 2 then
              climb hash compress values sibs rest (index / 2) (padded / 2)
                (compress root (hashRows hash values is))
            else climb hash compress values sibs groups (index / 2) (padded / 2) root
          | [] => climb hash compress values sibs [] (index / 2) (padded / 2) root) := by
      intro root
      rw [pure_bind]
      rcases groups with _ | ⟨⟨h, is⟩, rest⟩
      · exact climbM_pure hash compress values sibs _ _ _ _
      · dsimp only
        by_cases hh : h.nextPowerOfTwo = padded / 2
        · simp only [hh, ite_true]
          rw [ pure_bind, pure_bind, hashRows]
          exact climbM_pure hash compress values sibs _ _ _ _
        · simp only [hh, ite_false]
          exact climbM_pure hash compress values sibs _ _ _ _
    by_cases hi : index % 2 = 0
    · simp only [hi, ite_true]; exact step _
    · simp only [hi, ite_false]; exact step _

/-- With pure hashes, `verifyBatchM` is `verifyBatch`. -/
theorem verifyBatchM_pure [DecidableEq F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (commit : Vector F d) (heights : List Nat)
    (index : Nat) (values : List (List F)) (path : List (Vector F d)) :
    verifyBatchM (m := m) (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) commit
      heights index values path =
      pure (verifyBatch hash compress commit heights index values path) := by
  unfold verifyBatchM verifyBatch
  rcases heightGroups heights with _ | ⟨⟨maxH, tallest⟩, rest⟩
  · rfl
  · dsimp only
    split
    · rename_i h
      rw [h, Bool.true_and, pure_bind, climbM_pure, pure_bind, hashRows]
    · rename_i h
      rw [Bool.not_eq_true] at h
      rw [h, Bool.false_and]

end CompStark.Merkle

namespace CompStark.Fri
open CompStark.Stark CompStark.Merkle

local notation "F" => KoalaBear.Fast.Field

/-- A running maximum from at most `h` over matrices of height `h` is `h`. -/
theorem foldl_max_height (ms : List Mat) (h : Nat) (hms : ∀ m ∈ ms, m.height = h) :
    ∀ acc, acc ≤ h → ms ≠ [] → ms.foldl (fun m a ↦ max m a.height) acc = h := by
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

/-- The largest height of matrices of one height `h` is `h`. -/
theorem maxHeight_ofMats (ms : List Mat) (h : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = h) : (Committed.ofMats ms).maxHeight = h :=
  foldl_max_height ms h hms 0 (Nat.zero_le h) hne

/-- `rowOf` is the Merkle tree's row. -/
theorem rowOf_toList (m : Mat) (i : Nat) : (rowOf m i).toList = m.toMatrix.row i := by
  apply List.ext_getElem
  · simp only [rowOf, Array.toList_ofFn, List.length_ofFn, Merkle.Matrix.row, Mat.toMatrix,
      List.length_map, List.length_range]
  · intro j h1 h2
    simp only [rowOf, Array.toList_ofFn, List.getElem_ofFn, Merkle.Matrix.row, Mat.toMatrix,
      List.getElem_map, List.getElem_range]

/-- The committed root is the Merkle root. -/
theorem root_ofMats (ms : List Mat) :
    (Committed.ofMats ms).root =
      Merkle.root (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) (ms.map Mat.toMatrix) := by
  rw [Merkle.root_eq_layers]
  simp only [Committed.ofMats, Committed.root]
  generalize Merkle.layers (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F)
    (ms.map Mat.toMatrix) = ls
  simp only [List.back?_toArray, List.getLast?_map, List.getLastD_eq_getLast?]
  cases ls.getLast? with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Option.getD_some, List.headD_eq_getD, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- The opening's rows of matrices of one height `2 ^ k` are their rows at the index. -/
theorem openAt_values (ms : List Mat) (k : Nat) (hms : ∀ m ∈ ms, m.height = 2 ^ k) (i : Nat) :
    ((Committed.ofMats ms).openAt i).values = (ms.map fun m ↦ rowOf m i).toArray := by
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
theorem openAt_path (ms : List Mat) (k : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = 2 ^ k) (i : Nat) :
    ((Committed.ofMats ms).openAt i).path.toList =
      (Merkle.openBatch (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F)
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
theorem verifyBatch_openAt (ms : List Mat) (k : Nat) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, m.height = 2 ^ k ∧ m.values.size = m.width * m.height)
    (i : Nat) (hi : i < 2 ^ k) :
    Merkle.KoalaBear.verifyBatch KoalaBear.Fast.Field (Committed.ofMats ms).root
      (ms.map (·.height)) i (((Committed.ofMats ms).openAt i).values.toList.map (·.toList))
      ((Committed.ofMats ms).openAt i).path.toList = true := by
  have hh : ∀ m ∈ ms, m.height = 2 ^ k := fun m hm ↦ (hms m hm).1
  have hh' : ∀ m ∈ ms.map Mat.toMatrix, m.height = 2 ^ k := fun m hm ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact hh a ha
  have hne' : ms.map Mat.toMatrix ≠ [] := by
    rwa [Ne, List.map_eq_nil_iff]
  have hv : ((Committed.ofMats ms).openAt i).values.toList.map (·.toList) =
      (Merkle.openBatch (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F)
        (ms.map Mat.toMatrix) i).1 := by
    rw [openAt_values ms k hh, Merkle.openBatch_fst _ _ _ k i hh', List.toList_toArray,
      List.map_map, List.map_map]
    exact List.map_congr_left fun m _ ↦ rowOf_toList m i
  have hH : ms.map (·.height) = (ms.map Mat.toMatrix).map (·.height) := by
    rw [List.map_map]; rfl
  rw [root_ofMats, hv, openAt_path ms k hne hh, hH]
  exact Merkle.verifyBatch_openBatch _ _ _ k i hne' hh' hi

/-- On Poseidon2, the verifier's opening check is `Merkle.KoalaBear.verifyBatch`. -/
theorem checkOpening_eq (commit : Digest) (heights : List Nat) (index : Nat)
    (values : List (List F)) (path : List Digest) :
    checkOpening poseidon2 commit heights index values path =
      pure (Merkle.KoalaBear.verifyBatch F commit heights index values path) := by
  unfold checkOpening
  rw [show Merkle.verifyBatchM poseidon2.hash poseidon2.compress commit heights index values path
    = (pure (Merkle.KoalaBear.verifyBatch F commit heights index values path) : Id Bool) from
    Merkle.verifyBatchM_pure _ _ _ _ _ _ _]
  rfl

end CompStark.Fri
