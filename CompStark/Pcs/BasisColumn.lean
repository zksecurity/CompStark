/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.BasisWindow

/-! Shared point windows and binary coordinate columns of the production Basis. -/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Project a compact window without constructing a separate witness row. -/
def BasisWindow.projectAt {cols : Nat} (w : BasisWindow cols) (f : Fin cols → Word) : WordExt3 :=
  sumWords (List.ofFn fun i : Fin w.count => WordExt3.mulScalar w.values[i]
    (f ⟨w.start+i.val, by have := i.isLt; have := w.fits; omega⟩))

/-- Indexed witness access gives the same certified compact-window projection. -/
theorem BasisWindow.projectAt_refines {cols : Nat} (w : BasisWindow cols) (f : Fin cols → Word) :
    (w.projectAt f).toField = ∑ x : Fin cols, w.expand[x].toField *
      (algebraMap BF64 BF64.Ext3) (f x).toField := by
  have spec := w.project_refines (Vector.ofFn f)
  simpa only [BasisWindow.projectAt, BasisWindow.project, Fin.getElem_fin,
    Vector.getElem_ofFn] using spec

/-- Fold one binary coordinate using a single base-field XOR accumulator. -/
def basisBitLoop {cols : Nat} (values : Vector WordExt3 cols) (coordinate : Fin 192)
    (f : Fin cols → Word) : (n : Nat) → n ≤ cols → UInt64 → Word
  | 0, _, acc => ⟨acc⟩
  | n+1, bound, acc =>
      let i : Fin cols := ⟨n, by omega⟩
      if packedBit (mapLimb values[i] ⟨coordinate.val/64, by omega⟩).val
          ⟨coordinate.val%64, by omega⟩ then
        basisBitLoop values coordinate f n (by omega) (acc ^^^ (f i).val)
      else basisBitLoop values coordinate f n (by omega) acc

/-- Each visited selected base word contributes exactly once to its binary projection. -/
theorem basisBitLoop_refines {cols : Nat} (values : Vector WordExt3 cols) (coordinate : Fin 192)
    (f : Fin cols → Word) (n : Nat) (bound : n ≤ cols) (acc : UInt64) :
    (basisBitLoop values coordinate f n bound acc).toField = (Word.mk acc).toField +
      ∑ i : Fin n, if packedBit (mapLimb values[i.castLE bound]
        ⟨coordinate.val/64, by omega⟩).val ⟨coordinate.val%64, by omega⟩
        then (f (i.castLE bound)).toField else 0 := by
  induction n generalizing acc with
  | zero => simp only [basisBitLoop, Fin.sum_univ_zero, add_zero]
  | succ n ih =>
    have last : Fin.castLE bound (Fin.last n) = (⟨n, by omega⟩ : Fin cols) := rfl
    rw [basisBitLoop]
    split
    · rename_i yes
      change packedBit (mapLimb values[n] ⟨coordinate.val/64, by omega⟩).val
        ⟨coordinate.val%64, by omega⟩ = true at yes
      rw [ih]
      change (Word.add ⟨acc⟩ (f ⟨n, by omega⟩)).toField + _ = _
      rw [Word.toField_add, Fin.sum_univ_castSucc]
      simp only [Fin.getElem_fin, Fin.val_castLE, Fin.castLE_castSucc, last, yes, ↓reduceIte]
      rw [add_assoc, add_comm (f ⟨n, by omega⟩).toField]
    · rename_i no
      change ¬ packedBit (mapLimb values[n] ⟨coordinate.val/64, by omega⟩).val
        ⟨coordinate.val%64, by omega⟩ = true at no
      rw [ih, Fin.sum_univ_castSucc]
      simp only [Fin.getElem_fin, Fin.val_castLE, Fin.castLE_castSucc, last, no,
        Bool.false_eq_true, ↓reduceIte, add_zero]

/-- Point claims retain occupied windows; ring claims share one tensor's binary coordinates. -/
inductive BasisColumn (cols : Nat) where
  /-- A local equality tensor, including its fixed low-bit selector. -/
  | point (window : BasisWindow cols)
  /-- One coordinate of a shared extension equality tensor. -/
  | binary (values : Vector WordExt3 cols) (coordinate : Fin 192)

/-- Erase a compact factor to its complete numeric column table. -/
def BasisColumn.expand {cols : Nat} : BasisColumn cols → Vector WordExt3 cols
  | .point window => window.expand
  | .binary values coordinate => Vector.ofFn fun i =>
      if packedBit (mapLimb values[i] ⟨coordinate.val/64, by omega⟩).val
          ⟨coordinate.val%64, by omega⟩ then 1 else 0

/-- Project each factor in its native representation, sharing indexed witness access. -/
def BasisColumn.project {cols : Nat} (factor : BasisColumn cols) (f : Fin cols → Word) : WordExt3 :=
  match factor with
  | .point window => window.projectAt f
  | .binary values coordinate =>
      let result := basisBitLoop values coordinate f cols (Nat.le_refl cols) 0
      ⟨result, ⟨0⟩, ⟨0⟩⟩

/-- Point and binary projections agree with their complete factor tables. -/
theorem BasisColumn.project_refines {cols : Nat} (factor : BasisColumn cols) (f : Fin cols → Word) :
    (factor.project f).toField = ∑ x : Fin cols, factor.expand[x].toField *
      (algebraMap BF64 BF64.Ext3) (f x).toField := by
  cases factor with
  | point window => exact window.projectAt_refines f
  | binary values coordinate =>
    change (algebraMap BF64 BF64.Ext3)
      (basisBitLoop values coordinate f cols (Nat.le_refl cols) 0).toField = _
    rw [basisBitLoop_refines]
    change (algebraMap BF64 BF64.Ext3) (0 + _) = _
    rw [zero_add, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [BasisColumn.expand, Fin.getElem_fin, Vector.getElem_ofFn, Fin.val_castLE]
    split
    · change (algebraMap BF64 BF64.Ext3) (f i).toField =
        (WordExt3.ringEquiv (1 : WordExt3)) * _
      rw [map_one, one_mul]
    · change (algebraMap BF64 BF64.Ext3) 0 =
        (WordExt3.ringEquiv (0 : WordExt3)) * _
      rw [map_zero, map_zero, zero_mul]

/-- Produce the small row-major projection matrix without expanding compact factors. -/
def projectColumns (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (columns : Vector (BasisColumn cols) terms) : Vector WordExt3 (lanes*terms) :=
  Vector.ofFn fun i => columns[i.modNat].project fun x => f[basisAddress i.divNat x]

/-- Compact projections equal the certified complete-kernel projection matrix. -/
theorem projectColumns_eq (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (columns : Vector (BasisColumn cols) terms) :
    projectColumns lanes cols terms f columns =
      projectBasis lanes cols terms f (columns.map BasisColumn.expand) := by
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  simp only [projectColumns, Vector.getElem_ofFn]
  change (columns[(⟨i, hi⟩ : Fin (lanes*terms)).modNat].project
    (fun x => f[basisAddress (⟨i, hi⟩ : Fin (lanes*terms)).divNat x])).toField = _
  rw [BasisColumn.project_refines]
  simp only [projectBasis, Vector.getElem_ofFn, sumWords_refines, List.map_ofFn,
    Function.comp_apply, WordExt3.toField_mulScalar, Algebra.smul_def, List.sum_ofFn,
    Fin.getElem_fin, Vector.getElem_map]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

/-- Read one shared column factor without materializing its complete table. -/
def BasisColumn.valueAt {cols : Nat} (factor : BasisColumn cols) (i : Fin cols) : WordExt3 :=
  match factor with
  | .point w => if h : w.start ≤ i.val ∧ i.val < w.start+w.count then
      w.values[i.val-w.start]'(by omega) else 0
  | .binary values coordinate =>
      if packedBit (mapLimb values[i] ⟨coordinate.val/64, by omega⟩).val
          ⟨coordinate.val%64, by omega⟩ then 1 else 0

/-- Indexed compact lookup recovers the complete factor at the same column. -/
theorem BasisColumn.valueAt_eq {cols : Nat} (factor : BasisColumn cols) (i : Fin cols) :
    factor.valueAt i = factor.expand[i] := by
  cases factor <;> simp only [BasisColumn.valueAt, BasisColumn.expand, BasisWindow.expand,
    Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

/-- Reconstruct one final weight contribution, using XOR selection for binary factors. -/
def BasisColumn.scaleAt {cols : Nat} (factor : BasisColumn cols) (a : WordExt3) (i : Fin cols) :
    WordExt3 :=
  match factor with
  | .point w => if h : w.start ≤ i.val ∧ i.val < w.start+w.count then
      WordExt3.mul a (w.values[i.val-w.start]'(by omega)) else 0
  | .binary values coordinate =>
      if packedBit (mapLimb values[i] ⟨coordinate.val/64, by omega⟩).val
          ⟨coordinate.val%64, by omega⟩ then a else 0

/-- Compact point and binary scaling preserve the full coefficient product. -/
theorem BasisColumn.scaleAt_refines {cols : Nat} (factor : BasisColumn cols) (a : WordExt3)
    (i : Fin cols) :
    (factor.scaleAt a i).toField = a.toField * factor.expand[i].toField := by
  rw [← factor.valueAt_eq]
  cases factor <;> simp only [BasisColumn.scaleAt, BasisColumn.valueAt]
  all_goals split
  · exact WordExt3.toField_mul _ _
  · change WordExt3.ringEquiv 0 = _ * WordExt3.ringEquiv 0
    rw [map_zero, mul_zero]
  · change _ = _ * WordExt3.ringEquiv 1
    rw [map_one, mul_one]
  · change WordExt3.ringEquiv 0 = _ * WordExt3.ringEquiv 0
    rw [map_zero, mul_zero]

/-- Lift the final lane row directly from compact point windows and shared binary columns. -/
def liftColumns (cols terms : Nat) (a : Vector WordExt3 terms)
    (columns : Vector (BasisColumn cols) terms) : Vector WordExt3 cols :=
  Vector.ofFn fun i => sumWords (List.ofFn fun t : Fin terms => columns[t].scaleAt a[t] i)

/-- Compact final reconstruction equals the complete shared-kernel lift. -/
theorem liftColumns_eq (cols terms : Nat) (a : Vector WordExt3 terms)
    (columns : Vector (BasisColumn cols) terms) :
    liftColumns cols terms a columns = liftBasis cols terms a (columns.map BasisColumn.expand) := by
  apply Vector.ext
  intro i hi
  apply WordExt3.toField_injective
  simp only [liftColumns, liftBasis, Vector.getElem_ofFn, sumWords_refines,
    List.map_ofFn, Function.comp_apply, BasisColumn.scaleAt_refines, Fin.getElem_fin,
    Vector.getElem_map, WordExt3.toField_mul, List.sum_ofFn]

end CompStark.Pcs
