/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.ByteFoldRows

/-! Direct transposition and subset-sum projection from occupied physical witness intervals. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxHeartbeats 200000

/-- Read an occupied interval with one unchecked machine-indexed source load. -/
@[inline] def windowRead {size count : Nat} (source : Vector Word size) (offset : Nat)
    (fits : offset+count ≤ size) (native : size < USize.size) (j : Fin count) : Word :=
  let k := offset.toUSize+j.val.toUSize
  have kt : k.toNat = offset+j.val := by
    rw [USize.toNat_add]
    change (offset.toUSize.toNat+j.val.toUSize.toNat)%USize.size = _
    rw [USize.toNat_ofNat_of_lt' (by omega : offset < USize.size),
      USize.toNat_ofNat_of_lt' (by have := j.isLt; omega : j.val < USize.size),
      Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  source.uget k (by rw [kt]; have := j.isLt; omega)

/-- Direct physical reads retain the exact occupied witness value. -/
theorem windowRead_eq {size count : Nat} (source : Vector Word size) (offset : Nat)
    (fits : offset+count ≤ size) (native : size < USize.size) (j : Fin count) :
    windowRead source offset fits native j =
      source[offset+j.val]'(by have := j.isLt; omega) := by
  have kt : (offset.toUSize+j.val.toUSize).toNat = offset+j.val := by
    rw [USize.toNat_add]
    change (offset.toUSize.toNat+j.val.toUSize.toNat)%USize.size = _
    rw [USize.toNat_ofNat_of_lt' (by omega : offset < USize.size),
      USize.toNat_ofNat_of_lt' (by have := j.isLt; omega : j.val < USize.size),
      Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  simp only [windowRead, Vector.uget, Array.uget, kt, Vector.getElem_toArray]

/-- Transpose directly from a retained witness interval, padding only its incomplete final block. -/
def transposeWindow {size count : Nat} (source : Vector Word size) (offset : Nat)
    (fits : offset+count ≤ size) (native : size < USize.size) :
    Vector AdditiveNTT.Bitsliced.Block (bitFoldBlocks count) :=
  Vector.ofFn fun block => AdditiveNTT.Bitsliced.transpose
    (AdditiveNTT.Bitsliced.Block.ofFn fun row =>
      if inside : block.val*64+row.val < count then
        (windowRead source offset fits native ⟨block.val*64+row.val,inside⟩).val else 0)

/-- Direct source transposition equals transposition of the complete padded interval. -/
theorem transposeWindow_eq {size count : Nat} (source : Vector Word size) (offset : Nat)
    (fits : offset+count ≤ size) (native : size < USize.size) :
    transposeWindow source offset fits native =
      transposeWords (bitFoldBlocks count) (bitFoldPad (Vector.ofFn fun j : Fin count =>
        source[offset+j.val]'(by have := j.isLt; omega))) := by
  unfold transposeWindow transposeWords
  apply congrArg Vector.ofFn
  funext block
  apply congrArg AdditiveNTT.Bitsliced.transpose
  apply congrArg AdditiveNTT.Bitsliced.Block.ofFn
  funext row
  simp only [bitFoldPad, Vector.getElem_ofFn]
  by_cases inside : block.val*64+row.val < count
  all_goals simp only [inside, dite_true, dite_false, windowRead_eq]
  all_goals rfl


/-- Fold retained byte tables against an occupied physical interval without copying its words. -/
def foldByteWindow {size count : Nat} (plan : ByteFoldPlan count) (source : Vector Word size)
    (offset : Nat) (fits : offset+count ≤ size) : Vector WordExt3 64 :=
  if native : size < USize.size then
    let rows := (transposeWindow source offset fits native).map blockWords
    Vector.ofFn fun row => sumExt (bitFoldBlocks count) fun block =>
      byteFoldPlane (bitFoldBlocks count) plan block rows[block][row]
  else foldBytePlan plan (Vector.ofFn fun j : Fin count =>
    source[offset+j.val]'(by have := j.isLt; omega))

/-- Direct interval folding preserves every complete byte-plan projection coordinate. -/
theorem foldByteWindow_eq {size count : Nat} (plan : ByteFoldPlan count) (source : Vector Word size)
    (offset : Nat) (fits : offset+count ≤ size) :
    foldByteWindow plan source offset fits =
      foldBytePlan plan (Vector.ofFn fun j : Fin count =>
        source[offset+j.val]'(by have := j.isLt; omega)) := by
  unfold foldByteWindow
  split
  · rw [foldBytePlan_code]
    simp only [foldBytePlanGrouped, foldBitTablesGrouped, transposeWindow_eq]
  · rfl

end CompStark.Pcs
