/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.BitFold

/-! Eight-byte grouped lookup loops for transposed opening projections. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] WordExt3.toField

/-- XOR eight extension values using three scalar coordinate expressions. -/
@[inline] def xorEight (a b c d e f g h : WordExt3) : WordExt3 :=
  ⟨⟨a.c0.val ^^^ b.c0.val ^^^ c.c0.val ^^^ d.c0.val ^^^ e.c0.val ^^^ f.c0.val ^^^ g.c0.val ^^^ h.c0.val⟩,
   ⟨a.c1.val ^^^ b.c1.val ^^^ c.c1.val ^^^ d.c1.val ^^^ e.c1.val ^^^ f.c1.val ^^^ g.c1.val ^^^ h.c1.val⟩,
   ⟨a.c2.val ^^^ b.c2.val ^^^ c.c2.val ^^^ d.c2.val ^^^ e.c2.val ^^^ f.c2.val ^^^ g.c2.val ^^^ h.c2.val⟩⟩

/-- Eight scalar XOR expressions give the complete extension sum. -/
theorem xorEight_refines (a b c d e f g h : WordExt3) :
    (xorEight a b c d e f g h).toField =
      a.toField+b.toField+c.toField+d.toField+e.toField+f.toField+g.toField+h.toField := by
  change (WordExt3.add (WordExt3.add (WordExt3.add (WordExt3.add (WordExt3.add
    (WordExt3.add (WordExt3.add a b) c) d) e) f) g) h).toField = _
  simp only [WordExt3.toField_add]

/-- Load all eight lookup entries from one transposed plane. -/
@[inline] def byteFoldPlane (blocks : Nat) (tables : Vector (Vector WordExt3 256) (blocks*8))
    (block : Fin blocks) (plane : UInt64) : WordExt3 :=
  let t0 := (tables[block.val*8+0]'(by have := block.isLt; omega))[((plane >>> 0).toUInt8).toNat]'(UInt8.toNat_lt _)
  let t1 := (tables[block.val*8+1]'(by have := block.isLt; omega))[((plane >>> 8).toUInt8).toNat]'(UInt8.toNat_lt _)
  let t2 := (tables[block.val*8+2]'(by have := block.isLt; omega))[((plane >>> 16).toUInt8).toNat]'(UInt8.toNat_lt _)
  let t3 := (tables[block.val*8+3]'(by have := block.isLt; omega))[((plane >>> 24).toUInt8).toNat]'(UInt8.toNat_lt _)
  let t4 := (tables[block.val*8+4]'(by have := block.isLt; omega))[((plane >>> 32).toUInt8).toNat]'(UInt8.toNat_lt _)
  let t5 := (tables[block.val*8+5]'(by have := block.isLt; omega))[((plane >>> 40).toUInt8).toNat]'(UInt8.toNat_lt _)
  let t6 := (tables[block.val*8+6]'(by have := block.isLt; omega))[((plane >>> 48).toUInt8).toNat]'(UInt8.toNat_lt _)
  let t7 := (tables[block.val*8+7]'(by have := block.isLt; omega))[((plane >>> 56).toUInt8).toNat]'(UInt8.toNat_lt _)
  xorEight t0 t1 t2 t3 t4 t5 t6 t7

/-- Grouped plane loads retain every byte's contribution. -/
theorem byteFoldPlane_refines (blocks : Nat) (tables : Vector (Vector WordExt3 256) (blocks*8))
    (block : Fin blocks) (plane : UInt64) :
    (byteFoldPlane blocks tables block plane).toField = ∑ byte : Fin 8,
      ((tables[block.val*8+byte.val]'(by have := block.isLt; have := byte.isLt; omega))[(wordByte plane byte).toNat]'(UInt8.toNat_lt _)).toField := by
  simp only [byteFoldPlane, xorEight_refines, wordByte]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Nat.zero_add, Nat.reduceAdd, add_zero]
  ac_rfl

/-- Visit each transposed plane once and fold its eight bytes together. -/
def foldBitTablesGrouped (blocks : Nat) (tables : Vector (Vector WordExt3 256) (blocks*8))
    (f : Vector Word (blocks*64)) : Vector WordExt3 64 :=
  let rows := (transposeWords blocks f).map blockWords
  Vector.ofFn fun row => sumExt blocks fun block =>
    byteFoldPlane blocks tables block rows[block][row]

/-- Eight-byte grouping preserves the complete transposed fold. -/
@[csimp] theorem foldBitTablesArray_code : @foldBitTablesArray = @foldBitTablesGrouped := by
  funext blocks tables f
  apply Vector.ext
  intro row hr
  apply WordExt3.toField_injective
  simp only [foldBitTablesArray, foldBitTablesGrouped, Vector.getElem_ofFn,
    sumExt_toField, byteFoldPlane_refines]
  let equiv : Fin blocks × Fin 8 ≃ Fin (blocks*8) := finProdFinEquiv
  rw [← equiv.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro block _
  apply Finset.sum_congr rfl
  intro byte _
  simp only [equiv, finProdFinEquiv, Equiv.coe_fn_mk, Fin.getElem_fin]
  have div : (byte.val+8*block.val)/8 = block.val := by omega
  have mod : (byte.val+8*block.val)%8 = byte.val := by omega
  simp only [div, mod]
  simp only [Nat.add_comm, Nat.mul_comm]

/-- Fold arbitrary lengths with the grouped direct-plane loop. -/
def foldBytePlanGrouped {count : Nat} (plan : ByteFoldPlan count) (f : Vector Word count) :
    Vector WordExt3 64 :=
  foldBitTablesGrouped (bitFoldBlocks count) plan (bitFoldPad f)

/-- The grouped arbitrary-length wrapper preserves every weighted bit row. -/
@[csimp] theorem foldBytePlan_code : @foldBytePlan = @foldBytePlanGrouped := by
  funext count plan f
  simp only [foldBytePlan, foldBytePlanGrouped, ← foldBitTablesArray_code, ← foldBitTables_code]

/-- Reconstruct a mixed dot through grouped bit rows and polynomial shifts. -/
def dotBytePlanGrouped {count : Nat} (plan : ByteFoldPlan count) (f : Vector Word count) : WordExt3 :=
  reconstructBits (foldBytePlanGrouped plan f)

/-- Grouped reconstruction preserves the complete arbitrary-length mixed dot. -/
@[csimp] theorem dotBytePlan_code : @dotBytePlan = @dotBytePlanGrouped := by
  funext count plan f
  simp only [dotBytePlan, dotBitTables, dotBytePlanGrouped, foldBytePlanGrouped,
    ← reconstructBits_code, ← foldBitTablesArray_code, ← foldBitTables_code]

end CompStark.Pcs
