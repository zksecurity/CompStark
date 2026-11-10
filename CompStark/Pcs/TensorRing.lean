/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Copyright (c) 2026 leanEthereum.
Adapted from leanEthereum/leanMultisig, crates/pcs/src/stack_open/basis.rs.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.WindowBitFold
public import CompStark.Pcs.WindowFold

/-! Low/high ring projection with shared low subset-sum tables. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
attribute [local irreducible] WordExt3.toField Word.toField foldBits foldBytePlan prepareByteFold

/-- Read one occupied low interval from a physical witness lane and high block. -/
def tensorRingWords (lanes cols low high : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (window : BasisWindow low)
    (lane : Fin lanes) (h : Fin high) : Vector Word window.count :=
  Vector.ofFn fun j => source[lane.val*cols+h.val*low+window.start+j.val]'(by
    have hb := Nat.mul_le_mul_right low (Nat.succ_le_of_lt h.isLt)
    have hl := Nat.mul_le_mul_right cols (Nat.succ_le_of_lt lane.isLt)
    rw [Nat.succ_mul, ← shape] at hb
    rw [Nat.succ_mul] at hl
    have := window.fits
    have := j.isLt
    omega)

/-- Fold an occupied physical low block through retained subset-sum tables. -/
def tensorRingFold (lanes cols low high : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (window : BasisWindow low)
    (plan : ByteFoldPlan window.count) (lane : Fin lanes) (h : Fin high) : Vector WordExt3 64 :=
  foldByteWindow plan source (lane.val*cols+h.val*low+window.start) (by
    have hb := Nat.mul_le_mul_right low (Nat.succ_le_of_lt h.isLt)
    have hl := Nat.mul_le_mul_right cols (Nat.succ_le_of_lt lane.isLt)
    rw [Nat.succ_mul, ← shape] at hb
    rw [Nat.succ_mul] at hl
    have := window.fits
    omega)

/-- Physical interval folding preserves the complete compact-window byte fold. -/
theorem tensorRingFold_eq (lanes cols low high : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (window : BasisWindow low)
    (plan : ByteFoldPlan window.count) (lane : Fin lanes) (h : Fin high) :
    tensorRingFold lanes cols low high shape source window plan lane h =
      foldBytePlan plan (tensorRingWords lanes cols low high shape source window lane h) := by
  unfold tensorRingFold
  rw [foldByteWindow_eq]
  rfl

/-- Transpose occupied low blocks against one shared table, then apply high coefficients. -/
def tensorRingRows (lanes cols low high : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (window : BasisWindow low)
    (gamma : Vector WordExt3 high) : Vector (Vector WordExt3 64) lanes :=
  let plan := prepareByteFold window.values
  Vector.ofFn fun lane =>
    let blocks : Vector (Vector WordExt3 64) high := Vector.ofFn fun h =>
      if gamma[h.val] = 0 then Vector.replicate 64 0 else
        tensorRingFold lanes cols low high shape source window plan lane h
    Vector.ofFn fun bit => dotExtWide high (fun h => gamma[h.val]) (fun h => blocks[h.val][bit.val])

/-- Low/high ring projection retains every complete weighted witness bit row. -/
theorem tensorRingRows_eq (lanes cols low high : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (window : BasisWindow low)
    (gamma : Vector WordExt3 high) (weights : Vector WordExt3 cols)
    (factor : ∀ (h : Fin high) (x : Fin low),
      weights[(basisAddress h x).cast shape.symm].toField =
        gamma[h.val].toField * window.expand[x.val].toField) (lane : Fin lanes) :
    (tensorRingRows lanes cols low high shape source window gamma)[lane.val] =
      foldBits (Vector.ofFn fun x => source[basisAddress lane x]) weights := by
  simp only [Fin.getElem_fin] at factor
  unfold tensorRingRows
  rw [Vector.getElem_ofFn]
  apply Vector.ext
  intro bit hb
  apply WordExt3.toField_injective
  rw [Vector.getElem_ofFn, dotExtWide_refines]
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, tensorRingFold_eq]

  have spec := foldBits_refines (Vector.ofFn fun x => source[basisAddress lane x]) weights (⟨bit,hb⟩ : Fin 64)
  simp only [Fin.getElem_fin] at spec
  rw [spec]

  let equiv : Fin high × Fin low ≃ Fin cols := finProdFinEquiv.trans (finCongr shape.symm)
  conv_rhs => rw [← equiv.sum_comp, Fintype.sum_prod_type]

  apply Finset.sum_congr rfl
  intro h _
  have address (x : Fin low) : equiv (h,x) = (basisAddress h x).cast shape.symm := by
    apply Fin.ext
    simp only [equiv, Equiv.trans_apply, finProdFinEquiv, Equiv.coe_fn_mk,
      finCongr, Fin.val_cast, basisAddress, Nat.mul_comm, Nat.add_comm]
  simp only [address, factor, Vector.getElem_ofFn]

  by_cases zero : gamma[h.val] = 0
  · have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
    simp only [zero, z, zero_mul, ite_self, Finset.sum_const_zero]
  · simp only [zero, ite_false]
    have input : tensorRingWords lanes cols low high shape source window lane h =
        windowWords window (Vector.ofFn fun x : Fin low =>
          source[basisAddress lane ((basisAddress h x).cast shape.symm)]) := by
      apply Vector.ext
      intro j hj
      simp only [tensorRingWords, windowWords, Vector.getElem_ofFn, basisAddress, Fin.val_cast, Nat.add_assoc, Fin.getElem_fin]
    simp only [input, foldBytePlan_eq, windowBits_eq, Fin.getElem_fin]
    have lowSpec := foldBits_refines (Vector.ofFn fun x : Fin low =>
      source[basisAddress lane ((basisAddress h x).cast shape.symm)]) window.expand (⟨bit,hb⟩ : Fin 64)
    simp only [Fin.getElem_fin] at lowSpec
    rw [lowSpec, Finset.mul_sum]

    apply Finset.sum_congr rfl
    intro x _
    simp only [Vector.getElem_ofFn]
    split <;> simp only [mul_zero]

/-- Project point patterns and a low/high-factored ring with shared subset-sum tables. -/
def projectTensorFactoredRing (lanes cols low high count : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (pointGamma : Vector (Vector WordExt3 high) count) (ringLow : BasisWindow low)
    (ringHigh : Vector WordExt3 high) : Vector WordExt3 (lanes*(count+192)) :=
  let points := tensorWindowMatrixPacked lanes cols low high count shape source windows pointGamma
  let rings := (tensorRingRows lanes cols low high shape source ringLow ringHigh).map transposeExt
  Vector.ofFn fun i => Fin.addCases
    (fun term : Fin count => points[i.divNat][term])
    (fun bit : Fin 192 => ⟨rings[i.divNat][bit],⟨0⟩,⟨0⟩⟩) i.modNat

/-- Factored ring projection preserves the complete point/binary projection matrix. -/
theorem projectTensorFactoredRing_eq (lanes cols low high count : Nat) (shape : cols = high*low)
    (source : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (pointGamma : Vector (Vector WordExt3 high) count) (ringLow : BasisWindow low)
    (ringHigh : Vector WordExt3 high) (ring : Vector WordExt3 cols)
    (factor : ∀ (h : Fin high) (x : Fin low), ring[(basisAddress h x).cast shape.symm].toField =
      ringHigh[h.val].toField * ringLow.expand[x.val].toField) :
    projectTensorFactoredRing lanes cols low high count shape source windows pointGamma ringLow ringHigh =
      projectTensorPointBinary lanes cols low high count shape source windows pointGamma ring := by
  have rowsEq : (tensorRingRows lanes cols low high shape source ringLow ringHigh).map transposeExt =
      Vector.ofFn (fun lane : Fin lanes =>
        transposeExt (foldBits (Vector.ofFn fun x => source[basisAddress lane x]) ring)) := by
    apply Vector.ext
    intro lane hl
    simp only [Vector.getElem_map, Vector.getElem_ofFn,
      tensorRingRows_eq _ _ _ _ _ _ _ _ ring factor (⟨lane,hl⟩ : Fin lanes)]
  rw [projectTensorPointBinary_code, projectTensorPointBinaryActive_code]
  unfold projectTensorFactoredRing projectTensorPointBinaryPacked
  rw [rowsEq]
  simp only [foldBytePlan_eq]

end CompStark.Pcs
