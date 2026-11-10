/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.TensorProjection

/-! Occupied high-block masks shared by equal low point patterns. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] WordExt3.toField Word.toField

/-- The retained representative of each complete low window. -/
def tensorPatternKeys {low count : Nat} (windows : Vector (BasisWindow low) count) :
    Vector (Fin windows.toList.dedup.length) count :=
  let unique := windows.toList.dedup
  Vector.ofFn fun t =>
    ⟨unique.idxOf windows[t.val], List.idxOf_lt_length_iff.mpr
      (List.mem_dedup.mpr (Vector.mem_toList_iff.mpr (Vector.getElem_mem t.isLt)))⟩

attribute [local irreducible] tensorPatternKeys

/-- A retained low-window representative is the exact original low window. -/
theorem tensorPatternKeys_get {low count : Nat} (windows : Vector (BasisWindow low) count) (t : Fin count) :
    windows.toList.dedup[(tensorPatternKeys windows)[t.val].val] = windows[t.val] := by
  simp only [tensorPatternKeys, Vector.getElem_ofFn, Fin.val_mk]
  exact List.getElem_idxOf _

/-- Equal low windows have exactly the same retained pattern index. -/
theorem tensorPatternKeys_eq {low count : Nat} (windows : Vector (BasisWindow low) count)
    (t : Fin count) (p : Fin windows.toList.dedup.length) :
    windows[t.val] = windows.toList.dedup[p.val] ↔ (tensorPatternKeys windows)[t.val] = p := by
  have atKey := tensorPatternKeys_get windows t
  constructor
  · intro e
    apply Fin.ext
    exact (List.nodup_dedup windows.toList).getElem_inj_iff.mp (atKey.trans e)
  · intro e
    exact atKey.symm.trans (congrArg (fun i : Fin windows.toList.dedup.length =>
      windows.toList.dedup[i.val]) e)

/-- A low pattern is active where one of its point coefficients is nonzero. -/
def tensorPatternActive {patterns high count : Nat} (keys : Vector (Fin patterns) count)
    (gamma : Vector (Vector WordExt3 high) count) (p : Fin patterns) (h : Fin high) : Bool :=
  (List.finRange count).any fun t => decide (keys[t.val] = p) && decide (gamma[t.val][h.val] ≠ 0)

/-- Every nonzero point coefficient activates its shared low pattern. -/
theorem tensorPatternActive_of_nonzero {patterns high count : Nat}
    (keys : Vector (Fin patterns) count) (gamma : Vector (Vector WordExt3 high) count)
    (t : Fin count) (h : Fin high) (nonzero : gamma[t.val][h.val] ≠ 0) :
    tensorPatternActive keys gamma keys[t.val] h = true := by
  simp only [tensorPatternActive, List.any_eq_true]
  refine ⟨t, List.mem_finRange t, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨True.intro, nonzero⟩

/-- Project each distinct occupied low pattern only on its active high blocks. -/
def tensorWindowMatrixActive (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) : Vector (Vector WordExt3 count) lanes :=
  let unique := windows.toList.dedup
  let patterns := unique.length
  let plans := unique.toArray.map windowProjector
  let keys := tensorPatternKeys windows
  let active : Vector (Vector Bool high) patterns := Vector.ofFn fun p =>
    Vector.ofFn fun h => tensorPatternActive keys gamma p h
  let cache : Vector (Vector (Vector WordExt3 high) patterns) lanes := Vector.ofFn fun lane =>
    Vector.ofFn fun p => Vector.ofFn fun h =>
      if active[p.val][h.val] then
        (plans[p.val]'(by simpa only [plans, Array.size_map, List.size_toArray] using p.isLt)).project
          (fun x => f[basisAddress lane ((basisAddress h x).cast shape.symm)])
      else 0
  Vector.ofFn fun lane => Vector.ofFn fun t => sumExt high fun h =>
    roundProduct gamma[t.val][h.val] cache[lane.val][keys[t.val].val][h.val]

attribute [local irreducible] tensorPatternActive windowProjector tensorWindowMatrixActive

/-- Occupied high-block masks preserve the complete low/high point projection. -/
@[csimp] theorem tensorWindowMatrix_code : @tensorWindowMatrix = @tensorWindowMatrixActive := by
  funext lanes cols low high count shape f windows gamma
  apply Vector.ext
  intro lane hl
  apply Vector.ext
  intro term ht
  apply WordExt3.toField_injective
  have original := tensorWindowMatrix_refines lanes cols low high count shape f windows gamma
    (⟨lane,hl⟩ : Fin lanes) (⟨term,ht⟩ : Fin count)
  simp only [Fin.getElem_fin] at original
  refine original.trans ?_
  simp only [tensorWindowMatrixActive, Vector.getElem_ofFn, sumExt_toField]
  apply Finset.sum_congr rfl
  intro h _
  have key := tensorPatternKeys_get windows (⟨term,ht⟩ : Fin count)
  simp only [Array.getElem_map, List.getElem_toArray, key]
  simp only [roundProduct_eq, WordExt3.toField_mul]
  by_cases zero : gamma[term][h.val] = 0
  · have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
    simp only [zero, z, zero_mul, Finset.sum_const_zero]
  · have active := tensorPatternActive_of_nonzero (tensorPatternKeys windows) gamma (⟨term,ht⟩ : Fin count) h zero
    simp only [active, ite_true, windowProjector_eq]
    simp only [BasisWindow.projectAt_refines, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_assoc _ _ _

/-- Contract high coefficients through numeric pattern keys shared across all blocks. -/
def tensorWeightedWindowsShared (low high count : Nat) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (a : Vector WordExt3 (count+192)) :
    Vector (Vector (BasisWindow low) windows.toList.dedup.length) high :=
  let unique := windows.toList.dedup
  let keys := tensorPatternKeys windows
  Vector.ofFn fun h => Vector.ofFn fun p => scaleTensorWindow unique[p.val]
    (sumExt count fun t => if keys[t.val] = p then roundProduct a[t.val] gamma[t.val][h.val] else 0)

/-- Numeric pattern keys preserve every grouped high-block coefficient. -/
@[csimp] theorem tensorWeightedWindows_code : @tensorWeightedWindows = @tensorWeightedWindowsShared := by
  funext low high count windows gamma a
  simp only [tensorWeightedWindows, tensorWeightedWindowsShared]
  congr 1
  funext h
  congr 1
  funext p
  congr 1
  apply congrArg (sumExt count)
  funext t
  simp only [tensorPatternKeys_eq windows t p, Fin.getElem_fin]

/-- Reconstruct the shared point and ring tensor using numeric pattern keys. -/
def liftTensorPointBinaryShared (cols low high count : Nat) (shape : cols = high*low)
    (windows : Vector (BasisWindow low) count) (gamma : Vector (Vector WordExt3 high) count)
    (ring : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) : Vector WordExt3 cols :=
  let weighted := tensorWeightedWindowsShared low high count windows gamma a
  let binary := prepareCoordinates (Vector.ofFn fun bit : Fin 192 => a[count+bit.val])
  let patterns := windows.toList.dedup.length
  Vector.ofFn fun i => WordExt3.add
    (sumExt patterns fun p => (BasisColumn.point weighted[(i.cast shape).divNat][p]).valueAt ((i.cast shape).modNat))
    (applyCoordinateBytes binary ring[i])

/-- Numeric pattern sharing preserves every reconstructed coordinate. -/
@[csimp] theorem liftTensorPointBinary_code : @liftTensorPointBinary = @liftTensorPointBinaryShared := by
  funext cols low high count shape windows gamma ring a
  simp only [liftTensorPointBinary, liftTensorPointBinaryShared, ← tensorWeightedWindows_code,
    BasisColumn.valueAt_eq, BasisColumn.expand]

/-- Project point patterns on active blocks and share the complete binary ring fold. -/
def projectTensorPointBinaryActive (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (ring : Vector WordExt3 cols) :
    Vector WordExt3 (lanes*(count+192)) :=
  let points := tensorWindowMatrixActive lanes cols low high count shape f windows gamma
  let ringPlan := prepareByteFold ring
  let rings : Vector (Vector Word 192) lanes := Vector.ofFn fun lane =>
    transposeExt (foldBytePlan ringPlan (Vector.ofFn fun x => f[basisAddress lane x]))
  Vector.ofFn fun i => Fin.addCases
    (fun term : Fin count => points[i.divNat][term])
    (fun bit : Fin 192 => ⟨rings[i.divNat][bit], ⟨0⟩, ⟨0⟩⟩) i.modNat

/-- Occupied block projection retains every point and binary coordinate term. -/
@[csimp] theorem projectTensorPointBinary_code : @projectTensorPointBinary = @projectTensorPointBinaryActive := by
  funext lanes cols low high count shape f windows gamma ring
  simp only [projectTensorPointBinary, projectTensorPointBinaryActive, ← tensorWindowMatrix_code]

end CompStark.Pcs
