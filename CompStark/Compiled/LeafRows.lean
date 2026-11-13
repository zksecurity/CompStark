/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.WhirProver

/-! The rows the honest prover commits decode back to its words: `baseRows` under `baseLayout` and
`extensionRows` under `extensionLayout`, for words revealing every column. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Pcs

/-- Horner decoding assembles the little-endian bits. -/
theorem cubeIndexHorner_bits : {n : ℕ} → (row : Whir.Cube n) →
    cubeIndexHorner row = Pcs.bitsIndex (List.ofFn row)
  | 0, _ => rfl
  | n + 1, row => by
      rw [cubeIndexHorner, List.ofFn_succ, Pcs.bitsIndex, ← cubeIndexHorner_bits (fun i : Fin n => row i.succ)]
      cases row 0 <;> simp only [Bool.toNat_true, Bool.toNat_false, ↓reduceIte, Bool.false_eq_true] <;> ring

/-- The leaf layouts' row index is the vertex's numeric index. -/
theorem cubeIndex_eq_val {n : ℕ} (row : Whir.Cube n) : cubeIndex row = (Pcs.cubeIndex n row).val := by
  rw [← cubeIndexHorner_eq, cubeIndexHorner_bits, Pcs.cubeIndex_code]
  rfl

/-- A base-field word revealing every column decodes from its committed rows. -/
theorem baseRows_decode {n : ℕ} (schedule : Whir.Schedule K n) (word : Whir.oracleMessage K schedule)
    (full : ∀ column, ∃ values, word column = some values) :
    (baseLayout schedule (2 ^ schedule.lanes)).decode (fun i => some (baseRows word i)) = word := by
  funext column
  obtain ⟨values, hvalues⟩ := full column
  change Option.map (fun payload row => payload.getD (2 ^ schedule.lanes - 1 - cubeIndex row) 0)
    (some (baseRows word column.val)) = word column
  rw [hvalues]
  unfold baseRows
  rw [dif_pos column.isLt]
  change Option.map (fun payload row => payload.getD (2 ^ schedule.lanes - 1 - cubeIndex row) 0)
    (some (match word column with
    | some values => List.ofFn fun j : Fin (2 ^ schedule.lanes) =>
        values (Pcs.mask schedule.lanes ⟨2 ^ schedule.lanes - 1 - j.val, by omega⟩)
    | none => [])) = some values
  rw [hvalues, Option.map_some]
  congr 1
  funext row
  have bound := (Pcs.cubeIndex schedule.lanes row).isLt
  rw [cubeIndex_eq_val, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega), Option.getD_some]
  conv_rhs => rw [← Pcs.mask_cubeIndex schedule.lanes row]
  congr 2
  apply Fin.ext
  simp only
  omega

/-- An extension-field word revealing every column decodes from its committed rows. -/
theorem extensionRows_decode {n : ℕ} (schedule : Whir.Schedule K n) (word : Whir.oracleMessage E schedule)
    (full : ∀ column, ∃ values, word column = some values) :
    (extensionLayout schedule).decode (fun i => some (extensionRows word i)) = word := by
  funext column
  obtain ⟨values, hvalues⟩ := full column
  change Option.map (fun payload row =>
      E.ofLimbs (payload.getD (3 * cubeIndex row) 0) (payload.getD (3 * cubeIndex row + 1) 0)
        (payload.getD (3 * cubeIndex row + 2) 0))
    (some (extensionRows word column.val)) = word column
  rw [hvalues]
  unfold extensionRows
  rw [dif_pos column.isLt]
  change Option.map (fun payload row =>
      E.ofLimbs (payload.getD (3 * cubeIndex row) 0) (payload.getD (3 * cubeIndex row + 1) 0)
        (payload.getD (3 * cubeIndex row + 2) 0))
    (some (match word column with
    | some values => List.ofFn fun j : Fin (3 * 2 ^ schedule.lanes) =>
        (values (Pcs.mask schedule.lanes ⟨j.val / 3, by omega⟩)).limb ⟨j.val % 3, by omega⟩
    | none => [])) = some values
  rw [hvalues, Option.map_some]
  congr 1
  funext row
  have bound := (Pcs.cubeIndex schedule.lanes row).isLt
  have limb : ∀ i : Fin 3, (List.ofFn fun j : Fin (3 * 2 ^ schedule.lanes) =>
      (values (Pcs.mask schedule.lanes ⟨j.val / 3, by omega⟩)).limb ⟨j.val % 3, by omega⟩).getD
        (3 * (Pcs.cubeIndex schedule.lanes row).val + i.val) 0 = (values row).limb i := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega), Option.getD_some]
    conv_rhs => rw [← Pcs.mask_cubeIndex schedule.lanes row]
    congr 2
    · congr 1
      apply Fin.ext
      simp only
      omega
    · simp only
      omega
  have l0 := limb 0
  have l1 := limb 1
  have l2 := limb 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero] at l0 l1 l2
  rw [cubeIndex_eq_val, l0, l1, l2]
  exact ofLimbs_limb (values row)

/-- A base layout's tree has one leaf per column. -/
theorem baseLayout_columns {n : ℕ} (schedule : Whir.Schedule K n) (liveRows : ℕ) :
    2 ^ (baseLayout schedule liveRows).height = schedule.columns := by
  cases schedule <;> rfl

/-- The committed base rows of a word revealing every column have the layout's width. -/
theorem baseRows_length {n : ℕ} (schedule : Whir.Schedule K n) (word : Whir.oracleMessage K schedule)
    (full : ∀ column, ∃ values, word column = some values) :
    ∀ i < 2 ^ (baseLayout schedule (2 ^ schedule.lanes)).height,
      (baseRows word i).length = (baseLayout schedule (2 ^ schedule.lanes)).rowWords := by
  intro i hi
  rw [baseLayout_columns] at hi
  obtain ⟨values, hvalues⟩ := full ⟨i, hi⟩
  unfold baseRows
  rw [dif_pos hi, hvalues]
  exact List.length_ofFn

/-- The committed extension rows of a word revealing every column have the layout's width. -/
theorem extensionRows_length {n : ℕ} (schedule : Whir.Schedule K n) (word : Whir.oracleMessage E schedule)
    (full : ∀ column, ∃ values, word column = some values) :
    ∀ i < 2 ^ (extensionLayout schedule).height,
      (extensionRows word i).length = (extensionLayout schedule).rowWords := by
  intro i hi
  change i < 2 ^ (baseLayout schedule (2 ^ schedule.lanes)).height at hi
  rw [baseLayout_columns] at hi
  obtain ⟨values, hvalues⟩ := full ⟨i, hi⟩
  unfold extensionRows
  rw [dif_pos hi, hvalues]
  exact List.length_ofFn

/-- A word read off encoded rows reveals every column. -/
theorem wordOfRows_full {lanes columns : ℕ} {F : Type} [Zero F] (rows : Vector (Array F) (2 ^ lanes)) :
    ∀ column, ∃ values, (wordOfRows rows : Whir.MaskedWord F lanes columns) column = some values :=
  fun _ => ⟨_, rfl⟩

end CompStark.Compiled
