/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PackedProofs
import Mathlib.Data.List.Range

/-! Structural interval-write invariants for retained native extension-field buffers. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64

/-- Write a consecutive block of extension-field values into an existing packed buffer. -/
def writePackedBlock (out : PackedE) (offset count : Nat) (value : Nat → WordExt3) : PackedE :=
  (List.range count).foldl (fun state j => state.set (offset+j) (value j)) out

/-- Every complete in-bounds packed block write retains the original buffer length. -/
theorem writePackedBlock_size (out : PackedE) (offset count : Nat) (value : Nat → WordExt3)
    (hb : offset+count ≤ out.size) : (writePackedBlock out offset count value).size = out.size := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hs := ih (by omega)
    unfold writePackedBlock
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [PackedE.size_set _ _ _ (by change offset+count < (writePackedBlock out offset count value).size; rw [hs]; omega)]
    exact hs

/-- A complete packed block write changes exactly its selected interval. -/
theorem writePackedBlock_get (out : PackedE) (offset count : Nat) (value : Nat → WordExt3)
    (hb : offset+count ≤ out.size) (i : Nat) (hi : i < out.size) :
    (writePackedBlock out offset count value).get i =
      if offset ≤ i ∧ i < offset+count then value (i-offset) else out.get i := by
  induction count with
  | zero => simp only [writePackedBlock,List.range_zero,List.foldl_nil,show ¬(offset ≤ i ∧ i < offset+0) by omega,ite_false]
  | succ count ih =>
    have hs := writePackedBlock_size out offset count value (by omega)
    unfold writePackedBlock
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [PackedE.get_set _ _ _ (by change offset+count < (writePackedBlock out offset count value).size; rw [hs]; omega)
      (by change i < (writePackedBlock out offset count value).size; rw [hs]; exact hi)]
    by_cases he : offset+count = i
    · rw [ite_eq_left he,ite_eq_left (by omega)]
      exact congrArg value (by omega)
    · rw [ite_eq_right he]
      change (writePackedBlock out offset count value).get i = _
      rw [ih (by omega)]
      have heq : (offset ≤ i ∧ i < offset+count) ↔ (offset ≤ i ∧ i < offset+(count+1)) := by omega
      simp only [heq]

/-- Write a consecutive sequence of equally wide row blocks. -/
def writePackedRows (out : PackedE) (offset rows width : Nat) (value : Nat → Nat → WordExt3) : PackedE :=
  (List.range rows).foldl (fun state row => writePackedBlock state (offset+row*width) width (value row)) out

/-- Writing any in-bounds sequence of packed rows retains the complete buffer length. -/
theorem writePackedRows_size (out : PackedE) (offset rows width : Nat) (value : Nat → Nat → WordExt3)
    (hb : offset+rows*width ≤ out.size) :
    (writePackedRows out offset rows width value).size = out.size := by
  induction rows with
  | zero => rfl
  | succ rows ih =>
    have hs := ih (by nlinarith)
    unfold writePackedRows
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [writePackedBlock_size _ _ _ _ (by
      change offset+rows*width+width ≤ (writePackedRows out offset rows width value).size
      rw [hs]
      nlinarith)]
    exact hs

/-- Writing complete packed rows preserves every entry before the first row. -/
theorem writePackedRows_prefix (out : PackedE) (offset rows width : Nat) (value : Nat → Nat → WordExt3)
    (hb : offset+rows*width ≤ out.size) (i : Nat) (hi : i < offset) :
    (writePackedRows out offset rows width value).get i = out.get i := by
  induction rows with
  | zero => rfl
  | succ rows ih =>
    have hs := writePackedRows_size out offset rows width value (by nlinarith)
    unfold writePackedRows
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [writePackedBlock_get _ _ _ _ (by
      change offset+rows*width+width ≤ (writePackedRows out offset rows width value).size
      rw [hs]; nlinarith) i (by
        change i < (writePackedRows out offset rows width value).size
        rw [hs]; nlinarith),ite_eq_right (by omega)]
    exact ih (by nlinarith)

/-- Every retained row column contains its exact prescribed value after its row is processed. -/
theorem writePackedRows_get (out : PackedE) (offset rows width : Nat) (value : Nat → Nat → WordExt3)
    (hb : offset+rows*width ≤ out.size) (row column : Nat) (hc : column < width)
    (hi : offset+row*width+column < out.size) :
    (writePackedRows out offset rows width value).get (offset+row*width+column) =
      if row < rows then value row column else out.get (offset+row*width+column) := by
  induction rows with
  | zero => simp only [writePackedRows,List.range_zero,List.foldl_nil,Nat.not_lt_zero,ite_false]
  | succ rows ih =>
    have hs := writePackedRows_size out offset rows width value (by nlinarith)
    unfold writePackedRows
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [writePackedBlock_get _ _ _ _ (by
      change offset+rows*width+width ≤ (writePackedRows out offset rows width value).size
      rw [hs]; nlinarith) _ (by
        change offset+row*width+column < (writePackedRows out offset rows width value).size
        rw [hs]; exact hi)]
    by_cases he : row = rows
    · subst row
      rw [ite_eq_left (by omega),ite_eq_left (by omega)]
      exact congrArg (value rows) (by omega)
    · rw [ite_eq_right (by
        rintro ⟨hlo,hhi⟩
        by_cases hr : row < rows
        · nlinarith
        · have hr1 : rows+1 ≤ row := by omega
          nlinarith)]
      change (writePackedRows out offset rows width value).get _ = _
      rw [ih (by nlinarith)]
      have heq : row < rows ↔ row < rows+1 := by omega
      simp only [heq]

end CompStark.Keccak.GkrProver
