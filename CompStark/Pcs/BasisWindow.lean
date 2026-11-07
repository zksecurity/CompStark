/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.NativeBasis
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Intervals

/-! Compact column windows for the production factored Basis. -/
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Summing a zero-extended interval visits only its occupied local coordinates. -/
theorem basis_window_sum {F : Type} [AddCommMonoid F] (cols start count : Nat)
    (fits : start+count ≤ cols) (f : Nat → F) :
    (∑ i ∈ Finset.range cols, if start ≤ i ∧ i < start+count then f (i-start) else 0) =
      ∑ i ∈ Finset.range count, f i := by
  calc
    _ = ∑ i ∈ Finset.Ico start (start+count), f (i-start) := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    _ = ∑ i ∈ Finset.range count, f i := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]

/-- A retained local column tensor and its physical start inside one lane. -/
structure BasisWindow (cols : Nat) where
  /-- First live column. -/
  start : Nat
  /-- Number of live columns. -/
  count : Nat
  /-- Local tensor values without zero padding. -/
  values : Vector WordExt3 count
  /-- Every retained column lies inside its lane. -/
  fits : start+count ≤ cols

/-- The complete Boolean factor represented by a compact window. -/
def BasisWindow.expand {cols : Nat} (w : BasisWindow cols) : Vector WordExt3 cols :=
  Vector.ofFn fun i => if h : w.start ≤ i.val ∧ i.val < w.start+w.count then
    w.values[i.val-w.start]'(by omega) else ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

/-- Project a witness row using only the window's retained coefficients. -/
def BasisWindow.project {cols : Nat} (w : BasisWindow cols) (f : Vector Word cols) : WordExt3 :=
  sumWords (List.ofFn fun i : Fin w.count => WordExt3.mulScalar w.values[i]
    (f[w.start+i.val]'(by have := i.isLt; have := w.fits; omega)))

/-- Compact-window projection is the exact full weighted row sum. -/
theorem BasisWindow.project_refines {cols : Nat} (w : BasisWindow cols) (f : Vector Word cols) :
    (w.project f).toField = ∑ x : Fin cols, w.expand[x].toField *
      (algebraMap BF64 BF64.Ext3) f[x].toField := by
  simp only [BasisWindow.project, sumWords_refines, List.map_ofFn, Function.comp_apply,
    WordExt3.toField_mulScalar, Algebra.smul_def, List.sum_ofFn]
  let term (i : Nat) : BF64.Ext3 :=
    w.values[i]!.toField * (algebraMap BF64 BF64.Ext3) f[w.start+i]!.toField
  have scalar (i : Fin cols) : w.expand[i].toField * (algebraMap BF64 BF64.Ext3) f[i].toField =
      if w.start ≤ i.val ∧ i.val < w.start+w.count then term (i.val-w.start) else 0 := by
    simp only [BasisWindow.expand, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · rename_i inside
      have pos : w.start+(i.val-w.start) = i.val := by omega
      simp only [term, pos]
      rw [getElem!_pos w.values (i.val-w.start) (by omega), getElem!_pos f i.val i.isLt]
    · change (0 : BF64.Ext3) * _ = 0
      exact zero_mul _
  simp_rw [scalar]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    if w.start ≤ i ∧ i < w.start+w.count then term (i-w.start) else 0),
    basis_window_sum cols w.start w.count w.fits, ← Fin.sum_univ_eq_sum_range term]
  apply Finset.sum_congr rfl
  intro i _
  simp only [term, Fin.getElem_fin]
  rw [getElem!_pos w.values i.val i.isLt,
    getElem!_pos f (w.start+i.val) (by have := i.isLt; have := w.fits; omega)]
  exact mul_comm _ _

end CompStark.Pcs
