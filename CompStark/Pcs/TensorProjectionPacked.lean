/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.MixedDot
public import CompStark.Pcs.ByteFoldRows
public import CompStark.Pcs.TensorProjectionActive

/-! Retained packed point weights and shared binary-coordinate projection tables. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
attribute [local irreducible] Word.toField WordExt3.toField

/-- A compact point interval with its retained eight-wide mixed weights. -/
structure PackedWindowProjection (cols : Nat) where
  /-- Exact occupied interval. -/
  window : BasisWindow cols
  /-- Three packed polynomial coordinates of every local weight. -/
  weights : MixedDotPlan window.count

/-- Pack a point's mixed weights once for all physical witness lanes. -/
def packedWindowProjector {cols : Nat} (w : BasisWindow cols) : PackedWindowProjection cols :=
  ⟨w, prepareMixedDot w.values⟩

/-- Project one occupied interval with deferred polynomial reduction. -/
def PackedWindowProjection.project {cols : Nat} (p : PackedWindowProjection cols)
    (f : Fin cols → Word) : WordExt3 :=
  dotMixedPlan p.weights fun i =>
    f ⟨p.window.start+i.val, by have := p.window.fits; have := i.isLt; omega⟩

/-- Retained packed point weights give the complete occupied mixed dot. -/
theorem packedWindowProjector_eq {cols : Nat} (w : BasisWindow cols) (f : Fin cols → Word) :
    (packedWindowProjector w).project f = w.projectAt f := by
  apply WordExt3.toField_injective
  unfold PackedWindowProjection.project packedWindowProjector BasisWindow.projectAt
  rw [dotMixedPlan_refines, sumWords_refines]
  simp only [List.map_ofFn, Function.comp_apply, WordExt3.toField_mulScalar,
    Algebra.smul_def, List.sum_ofFn, Fin.getElem_fin]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

attribute [local irreducible] tensorPatternKeys tensorPatternActive windowProjector packedWindowProjector

/-- Cache packed point projections only on each retained low pattern's occupied high blocks. -/
def tensorWindowMatrixPacked (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) : Vector (Vector WordExt3 count) lanes :=
  let unique := windows.toList.dedup
  let patterns := unique.length
  let plans := unique.toArray.map packedWindowProjector
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

/-- Packed low-pattern dots preserve the complete active-block matrix. -/
@[csimp] theorem tensorWindowMatrixActive_code : @tensorWindowMatrixActive = @tensorWindowMatrixPacked := by
  funext lanes cols low high count shape f windows gamma
  apply Vector.ext
  intro lane hl
  apply Vector.ext
  intro term ht
  simp only [tensorWindowMatrixActive, tensorWindowMatrixPacked, Vector.getElem_ofFn,
    Fin.getElem_fin]
  apply congrArg (sumExt high)
  funext h
  simp only [Array.getElem_map, List.getElem_toArray]
  congr 1
  split <;> simp only [windowProjector_eq, packedWindowProjector_eq]

/-- Project packed point patterns and all shared binary ring coordinates. -/
def projectTensorPointBinaryPacked (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (ring : Vector WordExt3 cols) :
    Vector WordExt3 (lanes*(count+192)) :=
  let points := tensorWindowMatrixPacked lanes cols low high count shape f windows gamma
  let ringPlan := prepareByteFold ring
  let rings : Vector (Vector Word 192) lanes := Vector.ofFn fun lane =>
    transposeExt (foldBytePlan ringPlan (Vector.ofFn fun x => f[basisAddress lane x]))
  Vector.ofFn fun i => Fin.addCases
    (fun term : Fin count => points[i.divNat][term])
    (fun bit : Fin 192 => ⟨rings[i.divNat][bit], ⟨0⟩, ⟨0⟩⟩) i.modNat

/-- The joint packed-point and binary projection preserves every retained term. -/
@[csimp] theorem projectTensorPointBinaryActive_code :
    @projectTensorPointBinaryActive = @projectTensorPointBinaryPacked := by
  funext lanes cols low high count shape f windows gamma ring
  simp only [projectTensorPointBinaryActive, projectTensorPointBinaryPacked, ← tensorWindowMatrixActive_code]

end CompStark.Pcs
