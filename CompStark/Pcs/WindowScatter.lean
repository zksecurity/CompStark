/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.TensorProjectionActive

/-! In-place reconstruction through the occupied coefficients of compact windows. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] WordExt3.toField

/-- Add the retained prefix of one local window to its physical coordinates. -/
def scatterWindowLoop {cols : Nat} (w : BasisWindow cols) (left : Nat) (bound : left ≤ w.count)
    (out : Vector WordExt3 cols) : Vector WordExt3 cols :=
  match left with
  | 0 => out
  | left+1 =>
    let i := w.start+left
    have valid : i < cols := by have := w.fits; dsimp only [i]; omega
    scatterWindowLoop w left (by omega)
      (out.set i (WordExt3.add out[i] w.values[left]))
termination_by structural left

/-- Each occupied coefficient contributes once to its physical coordinate. -/
theorem scatterWindowLoop_refines {cols : Nat} (w : BasisWindow cols) (left : Nat)
    (bound : left ≤ w.count) (out : Vector WordExt3 cols) (i : Fin cols) :
    (scatterWindowLoop w left bound out)[i].toField = out[i].toField +
      ∑ j : Fin left, if w.start+j.val = i.val then w.values[j.val].toField else 0 := by
  induction left generalizing out with
  | zero =>
    rw [scatterWindowLoop]
    simp only [Fin.sum_univ_zero, add_zero]
  | succ left ih =>
    rw [scatterWindowLoop, ih, Fin.sum_univ_castSucc]
    simp only [Fin.getElem_fin, Vector.getElem_set, Fin.val_castSucc, Fin.val_last]
    by_cases atLast : w.start+left = i.val
    · simp only [atLast, ite_true, WordExt3.toField_add]
      ac_rfl
    · simp only [atLast, ite_false, add_zero]

/-- Reconstruct one compact window without scanning its zero padding. -/
def scatterWindow {cols : Nat} (w : BasisWindow cols) (out : Vector WordExt3 cols) :
    Vector WordExt3 cols := scatterWindowLoop w w.count (Nat.le_refl _) out

/-- Sparse reconstruction equals addition of the complete zero-extended window. -/
theorem scatterWindow_refines {cols : Nat} (w : BasisWindow cols)
    (out : Vector WordExt3 cols) (i : Fin cols) :
    (scatterWindow w out)[i].toField = out[i].toField + w.expand[i].toField := by
  rw [scatterWindow, scatterWindowLoop_refines]
  congr 1
  simp only [BasisWindow.expand, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · rename_i inside
    calc
      _ = (if w.start+(i.val-w.start) = i.val then
          w.values[i.val-w.start].toField else 0) := by
        apply Finset.sum_eq_single (⟨i.val-w.start, by omega⟩ : Fin w.count)
        · intro j _ different
          have ne : w.start+j.val ≠ i.val := by intro eq; apply different; apply Fin.ext; change j.val = i.val-w.start; omega
          simp only [ne, ite_false]
        · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
      _ = _ := by simp only [show w.start+(i.val-w.start) = i.val by omega, ite_true]
  · rename_i outside
    have z : (⟨⟨0⟩,⟨0⟩,⟨0⟩⟩ : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
    rw [z]
    apply Finset.sum_eq_zero
    intro j _
    have ne : w.start+j.val ≠ i.val := by have := j.isLt; omega
    simp only [ne, ite_false]

/-- Accumulate all occupied local windows in one reusable output vector. -/
def scatterWindows {cols : Nat} (windows : List (BasisWindow cols)) (out : Vector WordExt3 cols) :
    Vector WordExt3 cols :=
  match windows with
  | [] => out
  | w::rest => scatterWindows rest (scatterWindow w out)

/-- Sparse accumulation preserves the complete sum of all windows. -/
theorem scatterWindows_refines {cols : Nat} (windows : List (BasisWindow cols))
    (out : Vector WordExt3 cols) (i : Fin cols) :
    (scatterWindows windows out)[i].toField = out[i].toField +
      (windows.map fun w => w.expand[i].toField).sum := by
  induction windows generalizing out with
  | nil => simp only [scatterWindows, List.map_nil, List.sum_nil, add_zero]
  | cons w rest ih =>
    rw [scatterWindows, ih, scatterWindow_refines, List.map_cons, List.sum_cons, add_assoc]

/-- Lift point windows once per high block using their occupied coefficients. -/
def liftTensorPointBinaryScatter (cols low high count : Nat) (shape : cols = high*low)
    (windows : Vector (BasisWindow low) count) (gamma : Vector (Vector WordExt3 high) count)
    (ring : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) : Vector WordExt3 cols :=
  let weighted := tensorWeightedWindowsShared low high count windows gamma a
  let points := weighted.map fun ws => scatterWindows ws.toList (Vector.replicate low 0)
  let binary := prepareCoordinates (Vector.ofFn fun bit : Fin 192 => a[count+bit.val])
  Vector.ofFn fun i => WordExt3.add
    points[(i.cast shape).divNat][(i.cast shape).modNat]
    (applyCoordinateBytes binary ring[i])

/-- Vector-backed windows retain their complete finite coordinate sum. -/
theorem windowList_sum {low count : Nat} (ws : Vector (BasisWindow low) count) (i : Fin low) :
    (ws.toList.map fun w => w.expand[i].toField).sum = ∑ p : Fin count, ws[p].expand[i].toField := by
  conv_lhs => rw [← Vector.ofFn_getElem (xs := ws)]
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_apply, List.sum_ofFn,
    Fin.getElem_fin]

/-- Occupied-window writes equal the complete point and binary tensor lift. -/
@[csimp] theorem liftTensorPointBinaryShared_code :
    @liftTensorPointBinaryShared = @liftTensorPointBinaryScatter := by
  funext cols low high count shape windows gamma ring a
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  simp only [liftTensorPointBinaryShared, liftTensorPointBinaryScatter,
    Vector.getElem_ofFn, WordExt3.toField_add, Vector.getElem_map, Fin.getElem_fin]
  congr 1
  have accumulated := scatterWindows_refines
    (tensorWeightedWindowsShared low high count windows gamma a)[(Fin.cast shape ⟨i,hi⟩).divNat].toList
    (Vector.replicate low 0) (Fin.cast shape ⟨i,hi⟩).modNat
  simp only [Fin.getElem_fin, Vector.getElem_replicate] at accumulated
  refine Eq.trans ?_ accumulated.symm
  have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  rw [z, zero_add, sumExt_toField]
  have listSum := windowList_sum
    (tensorWeightedWindowsShared low high count windows gamma a)[(Fin.cast shape ⟨i,hi⟩).divNat]
    (Fin.cast shape ⟨i,hi⟩).modNat
  simp only [Fin.getElem_fin] at listSum
  refine Eq.trans ?_ listSum.symm
  apply Finset.sum_congr rfl
  intro p _
  simp only [BasisColumn.valueAt_eq, BasisColumn.expand, Fin.getElem_fin]

end CompStark.Pcs
