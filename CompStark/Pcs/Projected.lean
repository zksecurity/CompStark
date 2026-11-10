/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.BitFold

/-! Shared byte-table projections of point windows and binary ring coordinates. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] Word.toField WordExt3.toField

/-- Retained occupied window and its precomputed byte images. -/
structure WindowProjection (cols : Nat) where
  /-- The exact occupied input interval. -/
  window : BasisWindow cols
  /-- Shared byte images of the local weights. -/
  plan : ByteFoldPlan window.count

/-- Prepare a point window once and retain its byte tables across all witness lanes. -/
def windowProjector {cols : Nat} (w : BasisWindow cols) : WindowProjection cols :=
  ⟨w, prepareByteFold w.values⟩

/-- Apply retained byte images to one occupied witness interval. -/
def WindowProjection.project {cols : Nat} (p : WindowProjection cols)
    (f : Fin cols → Word) : WordExt3 :=
  dotBytePlan p.plan (Vector.ofFn fun i : Fin p.window.count =>
    f ⟨p.window.start+i.val, by have := i.isLt; have := p.window.fits; omega⟩)

/-- Shared point byte tables preserve the complete occupied-window projection. -/
theorem windowProjector_eq {cols : Nat} (w : BasisWindow cols) (f : Fin cols → Word) :
    (windowProjector w).project f = w.projectAt f := by
  apply WordExt3.toField_injective
  unfold WindowProjection.project windowProjector BasisWindow.projectAt
  rw [dotBytePlan_refines, sumWords_refines]
  simp only [List.map_ofFn, Function.comp_apply, WordExt3.toField_mulScalar,
    Algebra.smul_def, List.sum_ofFn, Fin.getElem_fin, Vector.getElem_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Prepare one ring tensor and project all its 192 binary coordinates together. -/
def ringProjector {cols : Nat} (values : Vector WordExt3 cols) :
    (Fin cols → Word) → Vector Word 192 :=
  let plan := prepareByteFold values
  fun f => transposeExt (foldBytePlan plan (Vector.ofFn f))

/-- Shared ring projection agrees with every separate binary-coordinate column. -/
theorem ringProjector_eq {cols : Nat} (values : Vector WordExt3 cols)
    (f : Fin cols → Word) (bit : Fin 192) :
    (⟨(ringProjector values f)[bit], ⟨0⟩, ⟨0⟩⟩ : WordExt3) =
      (BasisColumn.binary values bit).project f := by
  unfold ringProjector
  rw [foldBytePlan_eq, transposeFoldBits]
  apply WordExt3.toField_injective
  rw [BasisColumn.project_refines]
  have embed (a : Word) : (⟨a, ⟨0⟩, ⟨0⟩⟩ : WordExt3).toField =
      (algebraMap BF64 BF64.Ext3) a.toField := by
    unfold WordExt3.toField Word.toField
    rfl
  rw [embed]
  change (algebraMap BF64 BF64.Ext3) (Word.ringEquiv (∑ x : Fin cols,
    if extBit values[x] bit then (Vector.ofFn f)[x] else 0)) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [BasisColumn.expand, Fin.getElem_fin, Vector.getElem_ofFn, extBit]
  split
  · have h1 : (1 : WordExt3).toField = 1 := map_one WordExt3.ringEquiv
    rw [h1, one_mul]
    rfl
  · have h0 : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
    rw [h0, zero_mul, map_zero, map_zero]

/-- Retain point plans once before projecting all witness lanes. -/
def windowMatrix (lanes cols count : Nat) (f : Vector Word (lanes*cols))
    (windows : Vector (BasisWindow cols) count) : Vector (Vector WordExt3 count) lanes :=
  let plans := windows.map windowProjector
  Vector.ofFn fun lane => Vector.ofFn fun term =>
    plans[term].project fun x => f[basisAddress lane x]

/-- Share identical occupied windows and cache their projections for every lane. -/
def windowMatrixShared (lanes cols count : Nat) (f : Vector Word (lanes*cols))
    (windows : Vector (BasisWindow cols) count) : Vector (Vector WordExt3 count) lanes :=
  let unique := windows.toList.eraseDups
  let plans := unique.toArray.map windowProjector
  let addresses : Vector (Fin unique.length) count := Vector.ofFn fun term =>
    ⟨unique.idxOf windows[term], List.idxOf_lt_length_iff.mpr
      (List.mem_eraseDups.mpr (Vector.mem_toList_iff.mpr (Vector.getElem_mem term.isLt)))⟩
  let cache : Vector (Vector WordExt3 unique.length) lanes := Vector.ofFn fun lane =>
    Vector.ofFn fun term => (plans[term.val]'(by simpa only [plans, Array.size_map, List.size_toArray] using term.isLt)).project
      (fun x => f[basisAddress lane x])
  Vector.ofFn fun lane => Vector.ofFn fun term => cache[lane][addresses[term]]

/-- Sharing duplicate occupied windows retains every projected point term. -/
@[csimp] theorem windowMatrix_code : @windowMatrix = @windowMatrixShared := by
  funext lanes cols count f windows
  apply Vector.ext
  intro lane hl
  apply Vector.ext
  intro term ht
  have mem : windows[term] ∈ windows.toList.eraseDups :=
    List.mem_eraseDups.mpr (Vector.mem_toList_iff.mpr (Vector.getElem_mem ht))
  simp only [windowMatrix, windowMatrixShared, Vector.getElem_ofFn, Fin.getElem_fin,
    Vector.getElem_map, Array.getElem_map, List.getElem_toArray,
    List.getElem_idxOf (List.idxOf_lt_length_iff.mpr mem)]

/-- Project point windows and a shared ring tensor with one retained plan per factor. -/
def projectPointBinary (lanes cols count : Nat) (f : Vector Word (lanes*cols))
    (windows : Vector (BasisWindow cols) count) (ring : Vector WordExt3 cols) :
    Vector WordExt3 (lanes*(count+192)) :=
  let points := windowMatrix lanes cols count f windows
  let ringPlan := prepareByteFold ring
  let rings : Vector (Vector Word 192) lanes := Vector.ofFn fun lane =>
    transposeExt (foldBytePlan ringPlan (Vector.ofFn fun x => f[basisAddress lane x]))
  Vector.ofFn fun i => Fin.addCases
    (fun term : Fin count => points[i.divNat][term])
    (fun bit : Fin 192 => ⟨rings[i.divNat][bit], ⟨0⟩, ⟨0⟩⟩) i.modNat

/-- Joint projection preserves the complete compact-column projection matrix. -/
theorem projectPointBinary_eq (lanes cols count : Nat) (f : Vector Word (lanes*cols))
    (windows : Vector (BasisWindow cols) count) (ring : Vector WordExt3 cols) :
    projectPointBinary lanes cols count f windows ring =
      projectColumns lanes cols (count+192) f (windows.map BasisColumn.point ++
        Vector.ofFn (fun bit : Fin 192 => BasisColumn.binary ring bit)) := by
  have cell (lane : Fin lanes) (term : Fin (count+192)) :
      Fin.addCases
        (fun t : Fin count => (windowProjector windows[t]).project (fun x => f[basisAddress lane x]))
        (fun bit : Fin 192 => (⟨(ringProjector ring (fun x => f[basisAddress lane x]))[bit], ⟨0⟩, ⟨0⟩⟩ : WordExt3)) term =
      (windows.map BasisColumn.point ++ Vector.ofFn (fun bit : Fin 192 =>
        BasisColumn.binary ring bit))[term].project (fun x => f[basisAddress lane x]) := by
    refine Fin.addCases (fun t => ?_) (fun bit => ?_) term
    · simp only [Fin.addCases_left, Fin.getElem_fin, Fin.val_castAdd,
        Vector.getElem_append_left t.isLt, Vector.getElem_map, BasisColumn.project]
      exact windowProjector_eq _ _
    · simp only [Fin.addCases_right, Fin.getElem_fin, Fin.val_natAdd,
        Vector.getElem_append_right (by omega : count+bit.val < count+192) (by omega : count ≤ count+bit.val), Nat.add_sub_cancel_left, Vector.getElem_ofFn]
      exact ringProjector_eq _ _ _
  apply Vector.ext
  intro i hi
  simp only [projectPointBinary, windowMatrix, projectColumns, Vector.getElem_ofFn, Fin.getElem_fin,
    Vector.getElem_map]
  exact cell _ _

/-- Retain each point multiplier across its occupied interval in the final shared lift. -/
def liftPointBinaryPrepared (cols count : Nat) (points : Vector (BasisWindow cols) count)
    (values : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) : Vector WordExt3 cols :=
  let binary := prepareCoordinates (Vector.ofFn fun bit : Fin 192 => a[count+bit.val])
  let maps := Vector.ofFn fun t : Fin count => Sumcheck.prepare a[t.val]
  Vector.ofFn fun i => WordExt3.add
    (sumExt count fun t =>
      let w := points[t]
      if h : w.start ≤ i.val ∧ i.val < w.start+w.count then
        maps[t].mul w.values[i.val-w.start] else 0)
    (applyCoordinateBytes binary values[i])

/-- Shared point multipliers retain every final coordinate of the compact Basis lift. -/
@[csimp] theorem liftPointBinaryBytes_code : @liftPointBinaryBytes = @liftPointBinaryPrepared := by
  funext cols count points values a
  unfold liftPointBinaryBytes liftPointBinaryPrepared
  dsimp only
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  apply congrArg₂ WordExt3.add
  · apply congrArg (sumExt count)
    funext t
    simp only [BasisColumn.scaleAt, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · exact (Sumcheck.prepared_mul_eq _ _).symm
    · rfl
  · rfl

end CompStark.Pcs
