/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.Projected

/-! Shared low-block patterns and high coefficients of projected opening terms. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 1024
set_option maxHeartbeats 400000
attribute [local irreducible] WordExt3.toField Word.toField

/-- Shared low-window projections followed by each claim's small high-block contraction. -/
def tensorWindowMatrix (lanes cols low high count : Nat) (shape : cols = high*low) (f : Vector Word (lanes*cols))
    (windows : Vector (BasisWindow low) count) (gamma : Vector (Vector WordExt3 high) count) :
    Vector (Vector WordExt3 count) lanes :=
  let blocks := windowMatrix (lanes*high) low count (f.cast (by simp only [shape, Nat.mul_assoc])) windows
  Vector.ofFn fun lane => Vector.ofFn fun term => sumExt high fun h =>
    roundProduct gamma[term][h] blocks[basisAddress lane h][term]

/-- A tensor projection equals the complete low/high kernel's mixed inner product. -/
theorem tensorWindowMatrix_refines (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (lane : Fin lanes) (term : Fin count) :
    (tensorWindowMatrix lanes cols low high count shape f windows gamma)[lane][term].toField =
      ∑ h : Fin high, ∑ x : Fin low,
        (gamma[term][h].toField * windows[term].expand[x].toField) *
          (algebraMap BF64 BF64.Ext3)
            f[basisAddress lane ((basisAddress h x).cast shape.symm)].toField := by
  simp only [tensorWindowMatrix, Fin.getElem_fin, Vector.getElem_ofFn, sumExt_toField]
  apply Finset.sum_congr rfl
  intro h _
  rw [roundProduct_eq, WordExt3.toField_mul]
  simp only [windowMatrix, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_map]
  rw [windowProjector_eq, BasisWindow.projectAt_refines, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Vector.getElem_cast, basisAddress, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, shape, Fin.val_cast]
  exact (mul_assoc _ _ _).symm

/-- Project low/high point tensors and all binary coordinates of the shared ring tensor. -/
def projectTensorPointBinary (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (ring : Vector WordExt3 cols) :
    Vector WordExt3 (lanes*(count+192)) :=
  let points := tensorWindowMatrix lanes cols low high count shape f windows gamma
  let ringPlan := prepareByteFold ring
  let rings : Vector (Vector Word 192) lanes := Vector.ofFn fun lane =>
    transposeExt (foldBytePlan ringPlan (Vector.ofFn fun x => f[basisAddress lane x]))
  Vector.ofFn fun i => Fin.addCases
    (fun term : Fin count => points[i.divNat][term])
    (fun bit : Fin 192 => ⟨rings[i.divNat][bit], ⟨0⟩, ⟨0⟩⟩) i.modNat

/-- Tensor projection preserves point windows whose complete columns factor low/high. -/
theorem projectTensorPointBinary_eq (lanes cols low high count : Nat) (shape : cols = high*low)
    (f : Vector Word (lanes*cols)) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (ring : Vector WordExt3 cols)
    (full : Vector (BasisWindow cols) count)
    (factor : ∀ (t : Fin count) (h : Fin high) (x : Fin low),
      full[t].expand[(basisAddress h x).cast shape.symm].toField = gamma[t][h].toField * windows[t].expand[x].toField) :
    projectTensorPointBinary lanes cols low high count shape f windows gamma ring =
      projectColumns lanes cols (count+192) f (full.map BasisColumn.point ++
        Vector.ofFn (fun bit : Fin 192 => BasisColumn.binary ring bit)) := by
  have point (lane : Fin lanes) (term : Fin count) :
      (tensorWindowMatrix lanes cols low high count shape f windows gamma)[lane][term] =
        full[term].projectAt (fun x => f[basisAddress lane x]) := by
    apply WordExt3.toField_injective
    rw [tensorWindowMatrix_refines, BasisWindow.projectAt_refines]
    rw [← ((finProdFinEquiv : Fin high × Fin low ≃ Fin (high*low)).trans (finCongr shape.symm)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro x _
    have address : ((finProdFinEquiv : Fin high × Fin low ≃ Fin (high*low)).trans (finCongr shape.symm)) (h,x) =
        (basisAddress h x).cast shape.symm := Fin.ext (by
      simp only [Equiv.trans_apply, finProdFinEquiv, finCongr, Equiv.coe_fn_mk, basisAddress, Fin.val_cast, Nat.mul_comm, Nat.add_comm])
    rw [address, factor]
  have cell (lane : Fin lanes) (term : Fin (count+192)) :
      Fin.addCases
        (fun t : Fin count => (tensorWindowMatrix lanes cols low high count shape f windows gamma)[lane][t])
        (fun bit : Fin 192 => (⟨(ringProjector ring (fun x => f[basisAddress lane x]))[bit], ⟨0⟩, ⟨0⟩⟩ : WordExt3)) term =
      (full.map BasisColumn.point ++ Vector.ofFn (fun bit : Fin 192 =>
        BasisColumn.binary ring bit))[term].project (fun x => f[basisAddress lane x]) := by
    refine Fin.addCases (fun t => ?_) (fun bit => ?_) term
    · simp only [Fin.addCases_left, Fin.getElem_fin, Fin.val_castAdd,
        Vector.getElem_append_left t.isLt, Vector.getElem_map, BasisColumn.project]
      exact point _ _
    · simp only [Fin.addCases_right, Fin.getElem_fin, Fin.val_natAdd,
        Vector.getElem_append_right (by omega : count+bit.val < count+192)
          (by omega : count ≤ count+bit.val), Nat.add_sub_cancel_left, Vector.getElem_ofFn]
      exact ringProjector_eq _ _ _
  apply Vector.ext
  intro i hi
  simp only [projectTensorPointBinary, projectColumns, Vector.getElem_ofFn, Fin.getElem_fin]
  exact cell _ _

/-- Scale an occupied low window once, dropping a zero weighted pattern. -/
def scaleTensorWindow {cols : Nat} (w : BasisWindow cols) (a : WordExt3) : BasisWindow cols :=
  if a = 0 then ⟨0, 0, #v[], by omega⟩ else
    ⟨w.start, w.count, w.values.map (Sumcheck.prepare a).mul, w.fits⟩

/-- Prepared occupied-window scaling retains its complete scalar multiple. -/
theorem scaleTensorWindow_refines {cols : Nat} (w : BasisWindow cols) (a : WordExt3) (x : Fin cols) :
    (scaleTensorWindow w a).expand[x.val].toField = a.toField * w.expand[x.val].toField := by
  by_cases hz : a = 0
  · rw [scaleTensorWindow, ite_eq_left hz]
    have zeroField : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
    simp only [BasisWindow.expand, Vector.getElem_ofFn,
      Nat.zero_add, Nat.not_lt_zero, and_false, dite_false, hz, zeroField, zero_mul]
    exact zeroField
  · rw [scaleTensorWindow, ite_eq_right hz]
    simp only [BasisWindow.expand, Vector.getElem_ofFn]
    split
    · simp only [Vector.getElem_map, Sumcheck.prepared_mul_eq, WordExt3.toField_mul]
    · change (0 : WordExt3).toField = a.toField * (0 : WordExt3).toField
      have z : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
      rw [z, mul_zero]

/-- Aggregate each shared low pattern's coefficient on every high block before lifting. -/
def tensorWeightedWindows (low high count : Nat) (windows : Vector (BasisWindow low) count)
    (gamma : Vector (Vector WordExt3 high) count) (a : Vector WordExt3 (count+192)) :
    Vector (Vector (BasisWindow low) windows.toList.dedup.length) high :=
  let unique := windows.toList.dedup
  Vector.ofFn fun h => Vector.ofFn fun p => scaleTensorWindow unique[p.val]
    (sumExt count fun t => if windows[t] = unique[p.val] then roundProduct a[t.val] gamma[t][h] else 0)

/-- Shared pattern aggregation retains every point contribution on one low/high coordinate. -/
theorem tensorWeightedWindows_refines (low high count : Nat)
    (windows : Vector (BasisWindow low) count) (gamma : Vector (Vector WordExt3 high) count)
    (a : Vector WordExt3 (count+192)) (h : Fin high) (x : Fin low) :
    (sumExt windows.toList.dedup.length fun p =>
      (tensorWeightedWindows low high count windows gamma a)[h][p].expand[x]).toField =
      ∑ t : Fin count, a[t.val].toField * gamma[t][h].toField * windows[t].expand[x].toField := by
  unfold tensorWeightedWindows
  dsimp only
  rw [sumExt_toField]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, scaleTensorWindow_refines]
  simp_rw [sumExt_toField, apply_ite, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  let unique := windows.toList.dedup
  have mem : windows[t] ∈ unique :=
    List.mem_dedup.mpr (Vector.mem_toList_iff.mpr (Vector.getElem_mem t.isLt))
  let key : Fin unique.length := ⟨unique.idxOf windows[t], List.idxOf_lt_length_iff.mpr mem⟩
  have atKey : unique[key.val] = windows[t] := List.getElem_idxOf key.isLt
  simp only [Fin.getElem_fin] at atKey
  have injective : ∀ p : Fin unique.length, windows[t.val] = unique[p.val] ↔ p = key := by
    intro p
    rw [← atKey, (List.nodup_dedup windows.toList).getElem_inj_iff]
    exact ⟨fun e => Fin.ext e.symm, fun e => congrArg Fin.val e.symm⟩
  change (∑ p : Fin unique.length,
    (if windows[t] = unique[p.val] then (roundProduct a[t.val] gamma[t][h]).toField else (0 : WordExt3).toField) *
      unique[p.val].expand[x].toField) = _
  have zeroField : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  simp only [Fin.getElem_fin, roundProduct_eq, WordExt3.toField_mul]
  simp only [injective, zeroField, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, atKey]

/-- Reconstruct grouped point patterns and a shared binary-coordinate tensor. -/
def liftTensorPointBinary (cols low high count : Nat) (shape : cols = high*low)
    (windows : Vector (BasisWindow low) count) (gamma : Vector (Vector WordExt3 high) count)
    (ring : Vector WordExt3 cols) (a : Vector WordExt3 (count+192)) : Vector WordExt3 cols :=
  let weighted := tensorWeightedWindows low high count windows gamma a
  let binary := prepareCoordinates (Vector.ofFn fun bit : Fin 192 => a[count+bit.val])
  let patterns := windows.toList.dedup.length
  Vector.ofFn fun i => WordExt3.add
    (sumExt patterns fun p => weighted[(i.cast shape).divNat][p].expand[(i.cast shape).modNat])
    (applyCoordinateBytes binary ring[i])

/-- Shared low/high lifting equals every complete compact point/binary column lift. -/
theorem liftTensorPointBinary_eq (cols low high count : Nat) (shape : cols = high*low)
    (windows : Vector (BasisWindow low) count) (gamma : Vector (Vector WordExt3 high) count)
    (ring : Vector WordExt3 cols) (full : Vector (BasisWindow cols) count)
    (factor : ∀ (t : Fin count) (h : Fin high) (x : Fin low),
      full[t].expand[(basisAddress h x).cast shape.symm].toField = gamma[t][h].toField * windows[t].expand[x].toField)
    (a : Vector WordExt3 (count+192)) :
    liftTensorPointBinary cols low high count shape windows gamma ring a = liftPointBinary cols count full ring a := by
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  simp only [liftTensorPointBinary, liftPointBinary, Vector.getElem_ofFn,
    WordExt3.toField_add, applyCoordinateBytes_eq]
  apply congrArg₂ HAdd.hAdd
  · rw [tensorWeightedWindows_refines, sumExt_toField]
    apply Finset.sum_congr rfl
    intro t _
    rw [BasisColumn.scaleAt_refines]
    simp only [BasisColumn.expand]
    have address : (basisAddress ((⟨i,hi⟩ : Fin cols).cast shape).divNat
        ((⟨i,hi⟩ : Fin cols).cast shape).modNat).cast shape.symm = ⟨i,hi⟩ := by
      apply Fin.ext
      simp only [basisAddress, Fin.val_cast, Fin.divNat, Fin.modNat]
      simpa only [Nat.mul_comm] using Nat.div_add_mod i low
    have cell := factor t ((⟨i,hi⟩ : Fin cols).cast shape).divNat
      ((⟨i,hi⟩ : Fin cols).cast shape).modNat
    have fullEq : full[t].expand[i].toField =
        gamma[t][((⟨i,hi⟩ : Fin cols).cast shape).divNat].toField *
          windows[t].expand[((⟨i,hi⟩ : Fin cols).cast shape).modNat].toField := by
      simpa only [address, Fin.getElem_fin] using cell
    exact (mul_assoc _ _ _).trans (congrArg (HMul.hMul a[t.val].toField) fullEq.symm)
  · rfl

end CompStark.Pcs
