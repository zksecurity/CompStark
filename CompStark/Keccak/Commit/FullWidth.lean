/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Merkle

/-! The deployed short-row transport embeds into full-width semantic openings. -/

set_option autoImplicit false
@[expose] public section
namespace CompStark.Keccak.Commit
open CompStark.BinaryFields

/-- Restore every omitted zero limb, preserving malformed-row rejection. -/
def Pruned.fullWidth (rowWords leafWords : Nat) (batch : Pruned) : Pruned :=
  if rowWords ≤ leafWords ∧ ∀ row ∈ batch.leafData, row.length = rowWords then
    ⟨batch.leafData.map (restoreLeaf leafWords), batch.siblingHashes⟩
  else ⟨[], batch.siblingHashes⟩

/-- Restoring a row of bounded width produces the complete leaf width. -/
theorem restoreLeaf_length {width : Nat} {row : List K} (bounded : row.length ≤ width) :
    (restoreLeaf width row).length = width := by
  simp only [restoreLeaf, List.length_append, List.length_replicate]
  omega

/-- A complete leaf is unchanged by restoration. -/
theorem restoreLeaf_full {width : Nat} {row : List K} (full : row.length = width) :
    restoreLeaf width row = row := by
  simp only [restoreLeaf, full, Nat.sub_self, List.replicate_zero, List.nil_append]

/-- Full-width embedding preserves both successful expansion and rejection. -/
theorem expand_fullWidth (hash : ByteArray → Digest) (height rowWords leafWords : Nat) (queries : List Nat) (batch : Pruned) :
    expand hash height leafWords leafWords queries (batch.fullWidth rowWords leafWords) =
      expand hash height rowWords leafWords queries batch := by
  classical
  by_cases valid : rowWords ≤ leafWords ∧ ∀ row ∈ batch.leafData, row.length = rowWords
  · have widths : ∀ row ∈ batch.leafData,
        (restoreLeaf leafWords row).length = leafWords := by
      intro row member
      exact restoreLeaf_length (by rw [valid.2 row member]; exact valid.1)
    have restored : ∀ row ∈ batch.leafData,
        restoreLeaf leafWords (restoreLeaf leafWords row) = restoreLeaf leafWords row := by
      intro row member
      exact restoreLeaf_full (widths row member)
    have rows : batch.leafData.all (fun row => row.length == rowWords) = true := by
      simpa only [List.all_eq_true, beq_iff_eq] using valid.2
    have fullRows : (batch.leafData.map (restoreLeaf leafWords)).all
        (fun row => row.length == leafWords) = true := by
      simpa only [List.all_map, List.all_eq_true, Function.comp_apply, beq_iff_eq] using widths
    simp only [Pruned.fullWidth, ite_eq_left valid, expand, List.length_map,
      fullRows, rows, Bool.not_true, Nat.lt_irrefl, decide_false, Bool.or_false,
      show ¬ rowWords > leafWords from by omega]
    have paths : ((positions queries).zip (batch.leafData.map (restoreLeaf leafWords))).map
        (fun pair => Path.mk pair.1 (restoreLeaf leafWords pair.2) []) =
        ((positions queries).zip batch.leafData).map
        (fun pair => Path.mk pair.1 (restoreLeaf leafWords pair.2) []) := by
      rw [List.zip_map_right, List.map_map]
      apply List.map_congr_left
      intro pair member
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      rw [restored pair.2 (List.of_mem_zip member).2]
    rw [paths]
  · have rejected : (decide (rowWords > leafWords) ||
        !(batch.leafData.all (fun row => row.length == rowWords))) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        Bool.eq_false_iff]
      by_cases bound : rowWords ≤ leafWords
      · exact Or.inr (fun rows => valid ⟨bound, (List.all_eq_true.mp rows) |> fun h row mem => beq_iff_eq.mp (h row mem)⟩)
      · exact Or.inl (by omega)
    have emptyReject : ((positions queries).isEmpty ||
        !(positions queries).all (fun x => decide (x < 2 ^ height)) ||
        ((positions queries).length != 0)) = true := by
      by_cases empty : positions queries = []
      · simp only [empty, List.isEmpty_nil, Bool.true_or]
      · have count : (positions queries).length ≠ 0 := (fun h => empty (List.length_eq_zero_iff.mp h))
        simp only [bne_iff_ne.mpr count, Bool.or_true]
    simp only [Pruned.fullWidth, ite_eq_right valid, expand, List.length_nil,
      List.all_nil, Bool.not_true, Nat.lt_irrefl, decide_false, Bool.or_false,
      Bool.or_assoc, rejected, Bool.or_true, ↓reduceIte]
    simpa only [Bool.or_assoc] using
      (show (if ((positions queries).isEmpty ||
          !(positions queries).all (fun x => decide (x < 2 ^ height)) ||
          ((positions queries).length != 0)) then none else _) = none by
        rw [ite_eq_left emptyReject])

/-- Full-width embedding preserves the exact root-authentication decision. -/
theorem accepts_fullWidth (hash : ByteArray → Digest) (height rowWords leafWords : Nat) (queries : List Nat)
    (batch : Pruned) (commitment : Digest) :
    accepts hash height leafWords leafWords queries (batch.fullWidth rowWords leafWords) commitment =
      accepts hash height rowWords leafWords queries batch commitment := by
  simp only [accepts, expand_fullWidth]

end CompStark.Keccak.Commit
