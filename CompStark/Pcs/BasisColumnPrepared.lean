/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.DirectSums

/-! Shared binary-column selections for projected lane matrices. -/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Point windows and the occupied indices of a binary column, prepared once for every lane. -/
inductive BasisProjection (cols : Nat) where
  /-- Retained local numeric weights. -/
  | point (window : BasisWindow cols)
  /-- The exact selected indices of the shared binary factor. -/
  | binary (indices : List (Fin cols))

/-- Record binary selections once before projecting the complete witness. -/
def BasisColumn.prepareProjection {cols : Nat} : BasisColumn cols → BasisProjection cols
  | .point w => .point w
  | .binary values coordinate => .binary ((List.finRange cols).filter fun i =>
      packedBit (mapLimb values[i] ⟨coordinate.val/64, by omega⟩).val
        ⟨coordinate.val%64, by omega⟩)

/-- XOR selected base words using one unboxed accumulator. -/
@[specialize] def projectionXor {cols : Nat} (f : Fin cols → Word) : List (Fin cols) → UInt64 → Word
  | [], acc => ⟨acc⟩
  | i::rest, acc => projectionXor f rest (acc ^^^ (f i).val)

/-- Project one prepared factor with indexed witness access. -/
@[specialize] def BasisProjection.project {cols : Nat} (plan : BasisProjection cols)
    (f : Fin cols → Word) : WordExt3 :=
  match plan with
  | .point w => w.projectAt f
  | .binary indices => ⟨projectionXor f indices 0, ⟨0⟩, ⟨0⟩⟩

/-- Fix a witness row's offset before entering a prepared projection loop. -/
@[noinline] def BasisProjection.projectFrom {total cols : Nat} (plan : BasisProjection cols)
    (f : Vector Word total) (offset : Nat) (fits : offset+cols ≤ total) : WordExt3 :=
  plan.project fun x => f[offset+x.val]'(by have := x.isLt; omega)

/-- XOR a prepared binary selection with a fixed packed witness offset. -/
def projectionXorFrom {total cols : Nat} (f : Vector Word total) (offset : Nat)
    (fits : offset+cols ≤ total) : List (Fin cols) → UInt64 → Word
  | [], acc => ⟨acc⟩
  | i::rest, acc => projectionXorFrom f offset fits rest
      (acc ^^^ (f[offset+i.val]'(by have := i.isLt; omega)).val)

/-- Direct indexed XOR agrees with the generic prepared binary projection. -/
theorem projectionXorFrom_eq {total cols : Nat} (f : Vector Word total) (offset : Nat)
    (fits : offset+cols ≤ total) (indices : List (Fin cols)) (acc : UInt64) :
    projectionXorFrom f offset fits indices acc =
      projectionXor (fun i => f[offset+i.val]'(by have := i.isLt; omega)) indices acc := by
  induction indices generalizing acc with
  | nil => rfl
  | cons i rest ih => exact ih _

/-- Project a prepared factor using direct witness reads inside the accumulator. -/
@[noinline] def BasisProjection.projectFromNative {total cols : Nat} (plan : BasisProjection cols)
    (f : Vector Word total) (offset : Nat) (fits : offset+cols ≤ total) : WordExt3 :=
  match plan with
  | .point w => sumExt w.count fun i => WordExt3.mulScalar w.values[i]
      (f[offset+w.start+i.val]'(by have := i.isLt; have := w.fits; omega))
  | .binary indices => ⟨projectionXorFrom f offset fits indices 0, ⟨0⟩, ⟨0⟩⟩

/-- Direct indexed projection preserves every compact point and binary factor. -/
@[csimp] theorem BasisProjection.projectFrom_code :
    @BasisProjection.projectFrom = @BasisProjection.projectFromNative := by
  funext total cols plan f offset fits
  cases plan with
  | point w =>
    unfold BasisProjection.projectFrom BasisProjection.project BasisWindow.projectAt
      BasisProjection.projectFromNative
    dsimp only
    rw [sumExt_eq]
    simp only [Nat.add_assoc]
  | binary indices =>
    unfold BasisProjection.projectFrom BasisProjection.project BasisProjection.projectFromNative
    dsimp only
    rw [projectionXorFrom_eq]

/-- Project all lanes after sharing every binary column's selected coordinates. -/
def projectColumnsPrepared (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (columns : Vector (BasisColumn cols) terms) : Vector WordExt3 (lanes*terms) :=
  let plans := columns.map BasisColumn.prepareProjection
  Vector.ofFn fun i => plans[i.modNat].projectFrom f (i.divNat.val*cols) (by
    have := i.divNat.isLt; nlinarith)

deriving instance DecidableEq for BasisWindow

/-- The distinct local equality windows shared by the physical point claims. -/
def projectionWindows {cols terms : Nat} (columns : Vector (BasisColumn cols) terms) :
    List (BasisWindow cols) :=
  (columns.toList.filterMap fun column => match column with
    | .point w => some w
    | .binary _ _ => none).eraseDups

/-- Every physical point column retains its representative in the shared window list. -/
theorem projectionWindows_mem {cols terms : Nat} (columns : Vector (BasisColumn cols) terms)
    (i : Fin terms) (w : BasisWindow cols) (entry : columns[i] = .point w) :
    w ∈ projectionWindows columns := by
  rw [projectionWindows, List.mem_eraseDups, List.mem_filterMap]
  refine ⟨.point w, ?_, rfl⟩
  rw [← entry]
  exact (Vector.mem_toList_iff).mpr (Vector.getElem_mem i.isLt)

/-- Share point-window projections as well as binary coordinate selections across the full matrix. -/
def projectColumnsShared (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (columns : Vector (BasisColumn cols) terms) : Vector WordExt3 (lanes*terms) :=
  let windows := projectionWindows columns
  let points : Vector WordExt3 (lanes*windows.length) := Vector.ofFn fun i =>
    (BasisProjection.point windows[i.modNat.val]).projectFrom f (i.divNat.val*cols)
      (by have := i.divNat.isLt; nlinarith)
  let plans := columns.map BasisColumn.prepareProjection
  Vector.ofFn fun i =>
    match entry : columns[i.modNat] with
    | .point w =>
      points[basisAddress i.divNat
        ⟨windows.idxOf w, List.idxOf_lt_length_iff.mpr (projectionWindows_mem columns i.modNat w entry)⟩]
    | .binary _ _ => plans[i.modNat].projectFrom f (i.divNat.val*cols)
        (by have := i.divNat.isLt; nlinarith)

/-- Selected-coordinate XOR is the corresponding base-field sum plus its initial accumulator. -/
theorem projectionXor_refines {cols : Nat} (f : Fin cols → Word)
    (indices : List (Fin cols)) (acc : UInt64) :
    (projectionXor f indices acc).toField = (Word.mk acc).toField +
      (indices.map fun i => (f i).toField).sum := by
  induction indices generalizing acc with
  | nil => simp only [projectionXor, List.map_nil, List.sum_nil, add_zero]
  | cons i rest ih =>
    rw [projectionXor, ih]
    change (Word.add ⟨acc⟩ (f i)).toField + _ = _
    rw [Word.toField_add, List.map_cons, List.sum_cons, add_assoc]

/-- Filtering selected coordinates is the same sum as retaining zeros at unselected coordinates. -/
private theorem projection_filter_sum {α F : Type} [AddMonoid F]
    (indices : List α) (select : α → Bool) (f : α → F) :
    ((indices.filter select).map f).sum =
      (indices.map fun i => if select i then f i else 0).sum := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    cases selected : select i <;>
      simp only [List.filter_cons, selected, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons, zero_add, ih]

/-- Preparing a column preserves its complete projection on every witness row. -/
theorem BasisColumn.prepareProjection_refines {cols : Nat} (column : BasisColumn cols)
    (f : Fin cols → Word) : column.prepareProjection.project f = column.project f := by
  cases column with
  | point w => rfl
  | binary values coordinate =>
    apply WordExt3.toField_injective
    change (algebraMap BF64 Ext3) (projectionXor f _ 0).toField =
      (algebraMap BF64 Ext3) (basisBitLoop values coordinate f cols (Nat.le_refl cols) 0).toField
    rw [projectionXor_refines, basisBitLoop_refines]
    change (algebraMap BF64 Ext3) (0 + _) = (algebraMap BF64 Ext3) (0 + _)
    congr 2
    rw [projection_filter_sum]
    simp only [List.finRange, List.map_ofFn, Function.comp_apply, List.sum_ofFn,
      Fin.castLE_refl]

/-- Sharing prepared selections preserves the complete row-major projection matrix. -/
theorem projectColumnsPrepared_eq : @projectColumns = @projectColumnsPrepared := by
  funext lanes cols terms f columns
  apply Vector.ext
  intro i hi
  simp only [projectColumns, projectColumnsPrepared, Vector.getElem_ofFn,
    Fin.getElem_fin, Vector.getElem_map, BasisProjection.projectFrom,
    BasisColumn.prepareProjection_refines]
  rfl

/-- Sharing equal point windows preserves every retained numeric projection. -/
theorem projectColumnsShared_eq (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (columns : Vector (BasisColumn cols) terms) :
    projectColumnsShared lanes cols terms f columns = projectColumnsPrepared lanes cols terms f columns := by
  apply Vector.ext
  intro i hi
  simp only [projectColumnsShared, projectColumnsPrepared, Vector.getElem_ofFn]
  split
  · rename_i w entry
    let windows := projectionWindows columns
    have mem := projectionWindows_mem columns (⟨i, hi⟩ : Fin (lanes*terms)).modNat w entry
    have bound : windows.idxOf w < windows.length := List.idxOf_lt_length_iff.mpr mem
    have positive : 0 < windows.length := by omega
    have quotient : ((i/terms)*windows.length+windows.idxOf w)/windows.length = i/terms := by
      rw [Nat.mul_comm, Nat.mul_add_div positive, Nat.div_eq_of_lt bound, Nat.add_zero]
    have remainder : ((i/terms)*windows.length+windows.idxOf w)%windows.length = windows.idxOf w :=
      Nat.mul_add_mod_of_lt bound
    simp only [basisAddress, Fin.divNat, Fin.modNat, Fin.getElem_fin, Vector.getElem_ofFn]
    change (BasisProjection.point windows[((i/terms)*windows.length+windows.idxOf w)%windows.length]).projectFrom
      f ((((i/terms)*windows.length+windows.idxOf w)/windows.length)*cols) _ = _
    simp only [quotient, remainder, List.getElem_idxOf bound]
    simp only [Fin.getElem_fin, Fin.modNat] at entry
    simp only [Vector.getElem_map, entry, BasisColumn.prepareProjection]
  · rfl

/-- Resolve each compact point window once, sharing its address across all witness lanes. -/
def projectionAddresses {cols terms : Nat} (columns : Vector (BasisColumn cols) terms) :
    Vector Nat terms :=
  let windows := projectionWindows columns
  columns.map fun column => match column with
    | .point w => windows.idxOf w
    | .binary _ _ => 0

/-- Project shared columns using cached point-window addresses for every witness lane. -/
def projectColumnsIndexed (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (columns : Vector (BasisColumn cols) terms) : Vector WordExt3 (lanes*terms) :=
  let windows := projectionWindows columns
  let points : Vector WordExt3 (lanes*windows.length) := Vector.ofFn fun i =>
    (BasisProjection.point windows[i.modNat.val]).projectFrom f (i.divNat.val*cols)
      (by have := i.divNat.isLt; nlinarith)
  let plans := columns.map BasisColumn.prepareProjection
  let addresses := projectionAddresses columns
  Vector.ofFn fun i => match entry : columns[i.modNat] with
    | .point w =>
      points[basisAddress i.divNat (⟨addresses[i.modNat], by
        simp only [addresses, projectionAddresses, Fin.getElem_fin, Vector.getElem_map]
        simp only [Fin.getElem_fin] at entry
        simp only [entry]
        exact List.idxOf_lt_length_iff.mpr (projectionWindows_mem columns i.modNat w entry)⟩ : Fin windows.length)]
    | .binary _ _ => plans[i.modNat].projectFrom f (i.divNat.val*cols)
        (by have := i.divNat.isLt; nlinarith)

/-- Cached point addresses select exactly the shared projection at every row and term. -/
theorem projectColumnsIndexed_eq (lanes cols terms : Nat) (f : Vector Word (lanes*cols))
    (columns : Vector (BasisColumn cols) terms) :
    projectColumnsIndexed lanes cols terms f columns = projectColumnsShared lanes cols terms f columns := by
  apply Vector.ext
  intro i hi
  simp only [projectColumnsIndexed, projectColumnsShared, Vector.getElem_ofFn]
  split
  · rename_i w entry
    simp only [Fin.getElem_fin, Fin.modNat] at entry
    simp only [projectionAddresses, Fin.getElem_fin, Vector.getElem_map, Fin.modNat, entry]
    split
    · rename_i w' entry'
      have same : w' = w := BasisColumn.point.inj (entry'.symm.trans entry)
      subst w'
      rfl
    · rename_i values coordinate entry'
      cases entry.symm.trans entry'
  · rename_i values coordinate entry
    split
    · rename_i w entry'
      cases entry.symm.trans entry'
    · rfl

/-- The compiled projection matrix shares point windows and binary selections across all lanes. -/
@[csimp] theorem projectColumns_code : @projectColumns = @projectColumnsIndexed := by
  funext lanes cols terms f columns
  rw [projectColumnsIndexed_eq, projectColumnsShared_eq]
  exact congrFun (congrFun (congrFun (congrFun (congrFun projectColumnsPrepared_eq lanes) cols) terms) f) columns

end CompStark.Pcs
