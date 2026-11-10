/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.TensorProjectionPacked

/-! Binary ring projections through their compact occupied interval. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxHeartbeats 400000
attribute [local irreducible] WordExt3.toField

/-- Restrict physical witness reads to a compact window. -/
def windowWords {cols : Nat} (w : BasisWindow cols) (f : Vector Word cols) : Vector Word w.count :=
  Vector.ofFn fun j => f[w.start+j.val]'(by have := j.isLt; have := w.fits; omega)

/-- Compact bit folds equal the complete zero-extended ring fold. -/
theorem windowBits_eq {cols : Nat} (w : BasisWindow cols) (f : Vector Word cols) :
    foldBits (windowWords w f) w.values = foldBits f w.expand := by
  apply Vector.ext
  intro bit hbit
  apply WordExt3.toField_injective
  have a := foldBits_refines (windowWords w f) w.values (⟨bit,hbit⟩ : Fin 64)
  have b := foldBits_refines f w.expand (⟨bit,hbit⟩ : Fin 64)
  change (foldBits (windowWords w f) w.values)[bit].toField = _ at a
  change (foldBits f w.expand)[bit].toField = _ at b
  refine a.trans ?_
  refine Eq.trans ?_ b.symm
  let term (j : Nat) : BF64.Ext3 :=
    if f[w.start+j]!.val.toBitVec.getLsbD bit then w.values[j]!.toField else 0
  have scalar (i : Fin cols) :
      (if f[i].val.toBitVec.getLsbD bit then w.expand[i].toField else 0) =
        if w.start ≤ i.val ∧ i.val < w.start+w.count then term (i.val-w.start) else 0 := by
    simp only [BasisWindow.expand, Fin.getElem_fin, Vector.getElem_ofFn]
    by_cases inside : w.start ≤ i.val ∧ i.val < w.start+w.count
    · simp only [inside, and_self, dite_true, ite_true, term, show w.start+(i.val-w.start) = i.val by omega]
      rw [getElem!_pos f i.val i.isLt, getElem!_pos w.values (i.val-w.start) (by omega)]
    · simp only [inside, dite_false, ite_false]
      have z : (⟨⟨0⟩,⟨0⟩,⟨0⟩⟩ : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
      simp only [z, ite_self]
  simp_rw [scalar]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    if w.start ≤ i ∧ i < w.start+w.count then term (i-w.start) else 0),
    basis_window_sum cols w.start w.count w.fits, ← Fin.sum_univ_eq_sum_range term]
  apply Finset.sum_congr rfl
  intro i _
  simp only [windowWords, Fin.getElem_fin, Vector.getElem_ofFn, term]
  rw [getElem!_pos f (w.start+i.val) (by have := w.fits; have := i.isLt; omega),
    getElem!_pos w.values i.val i.isLt]

/-- Project all points and ring coordinates while visiting only the occupied ring interval. -/
def projectTensorPointWindow (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (ring : BasisWindow cols) :
    Vector WordExt3 (lanes*(count+192)) :=
  let points := tensorWindowMatrixPacked lanes cols low high count shape f windows gamma
  let ringPlan := prepareByteFold ring.values
  let rings : Vector (Vector Word 192) lanes := Vector.ofFn fun lane =>
    transposeExt (foldBytePlan ringPlan (Vector.ofFn fun j =>
      f[lane.val*cols+ring.start+j.val]'(by
        have := lane.isLt; have := j.isLt; have := ring.fits; nlinarith)))
  Vector.ofFn fun i => Fin.addCases
    (fun term : Fin count => points[i.divNat][term])
    (fun bit : Fin 192 => ⟨rings[i.divNat][bit], ⟨0⟩, ⟨0⟩⟩) i.modNat

/-- Compact occupied ring projection preserves every point and binary term. -/
theorem projectTensorPointWindow_eq (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (ring : BasisWindow cols) :
    projectTensorPointWindow lanes cols low high count shape f windows gamma ring =
      projectTensorPointBinary lanes cols low high count shape f windows gamma ring.expand := by
  have foldEq (lane : Fin lanes) :
      foldBits (Vector.ofFn fun j : Fin ring.count =>
        f[lane.val*cols+ring.start+j.val]'(by
          have := lane.isLt; have := j.isLt; have := ring.fits; nlinarith)) ring.values =
      foldBits (Vector.ofFn fun x : Fin cols => f[basisAddress lane x]) ring.expand := by
    simpa only [windowWords, Fin.getElem_fin, Vector.getElem_ofFn, basisAddress, Nat.add_assoc]
      using windowBits_eq ring (Vector.ofFn fun x => f[basisAddress lane x])
  rw [projectTensorPointBinary_code, projectTensorPointBinaryActive_code]
  simp only [projectTensorPointWindow, projectTensorPointBinaryPacked, foldBytePlan_eq, foldEq]

end CompStark.Pcs
