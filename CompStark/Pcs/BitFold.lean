/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.BasisColumnPrepared
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Transpose

/-! Shared Four-Russians tables and transposed witness blocks for opening projections. -/
@[expose] public section
namespace CompStark.Pcs
open BF64
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local irreducible] Word.toField WordExt3.toField
set_option smartUnfolding false
/-- One physical binary coordinate of an extension word. -/
def extBit (a : WordExt3) (i : Fin 192) : Bool :=
  packedBit (mapLimb a ⟨i.val/64, by omega⟩).val ⟨i.val%64, by omega⟩
/-- Physical binary coordinates add by exclusive or. -/
theorem extBit_add (a b : WordExt3) (i : Fin 192) :
    extBit (a+b) i = (extBit a i ^^ extBit b i) := by
  have limb : mapLimb (a+b) ⟨i.val/64, by omega⟩ =
      Word.add (mapLimb a ⟨i.val/64, by omega⟩) (mapLimb b ⟨i.val/64, by omega⟩) := by
    unfold mapLimb
    split <;> first | rfl | (split <;> rfl)
  simp only [extBit, limb, packedBit_eq, Word.add, UInt64.toBitVec_xor,
    BitVec.getLsbD_xor]
/-- Binary coordinate as an additive homomorphism. -/
def extBitHom (i : Fin 192) : WordExt3 →+ ZMod 2 where
  toFun a := if extBit a i then 1 else 0
  map_zero' := by
    have limb : mapLimb (0 : WordExt3) ⟨i.val/64, by omega⟩ = ⟨0⟩ := by
      unfold mapLimb
      split <;> first | rfl | (split <;> rfl)
    simp only [extBit, limb, packedBit_eq]
    change (if (0#64).getLsbD (i.val%64) then (1 : ZMod 2) else 0) = 0
    simp only [BitVec.getLsbD_zero, Bool.false_eq_true, ite_false]
  map_add' a b := by
    simp only [extBit_add]
    cases extBit a i <;> cases extBit b i <;> decide
/-- A binary coordinate of a base-field word. -/
def baseBitHom (i : Fin 64) : Word →+ ZMod 2 where
  toFun a := if packedBit a.val i then 1 else 0
  map_zero' := by
    simp only [packedBit_eq]
    change (if (0#64).getLsbD i.val then (1 : ZMod 2) else 0) = 0
    simp only [BitVec.getLsbD_zero, Bool.false_eq_true, ite_false]
  map_add' a b := by
    change (if packedBit (a.val ^^^ b.val) i then (1 : ZMod 2) else 0) = _
    simp only [packedBit_eq, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    cases a.val.toBitVec.getLsbD i.val <;> cases b.val.toBitVec.getLsbD i.val <;> decide
/-- Rectangular transpose from sixty-four extension words to 192 base words. -/
def transposeExt (a : Vector WordExt3 64) : Vector Word 192 :=
  let blocks := Vector.ofFn fun limb : Fin 3 => AdditiveNTT.Bitsliced.transpose
    (AdditiveNTT.Bitsliced.Block.ofFn fun row => (mapLimb a[row] limb).val)
  Vector.ofFn fun i : Fin 192 => ⟨(blocks[(⟨i.val/64, by omega⟩ : Fin 3)]).get ⟨i.val%64, by omega⟩⟩
/-- Rectangular transposition exchanges physical binary coordinates. -/
theorem transposeExt_bit (a : Vector WordExt3 64) (i : Fin 192) (bit : Fin 64) :
    packedBit (transposeExt a)[i].val bit = extBit a[bit] i := by
  simp only [transposeExt, Fin.getElem_fin, Vector.getElem_ofFn, packedBit_eq, extBit]
  change AdditiveNTT.Bitsliced.bit (AdditiveNTT.Bitsliced.transpose _) _ bit = _
  rw [AdditiveNTT.Bitsliced.bit_transpose]
  simp only [AdditiveNTT.Bitsliced.bit, AdditiveNTT.Bitsliced.Block.get_ofFn]
  rfl
/-- Binary sums of base words and extension words agree after transposition. -/
theorem transposeFoldBits (weights : Vector WordExt3 count) (f : Vector Word count)
    (i : Fin 192) :
    (transposeExt (foldBits f weights))[i] = ∑ x : Fin count, if extBit weights[x] i then f[x] else 0 := by
  change (Word.mk (transposeExt (foldBits f weights))[i].val) =
    Word.mk (∑ x : Fin count, if extBit weights[x] i then f[x] else 0).val
  apply congrArg Word.mk
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  by_cases bound : bit < 64
  · have bitEq := transposeExt_bit (foldBits f weights) i ⟨bit,bound⟩
    have foldEq : (foldBits f weights)[(⟨bit,bound⟩ : Fin 64)] =
        ∑ x : Fin count, if packedBit f[x].val ⟨bit,bound⟩ then weights[x] else 0 := by
      apply WordExt3.toField_injective
      rw [foldBits_refines]
      change _ = WordExt3.ringEquiv (∑ x : Fin count, if packedBit f[x].val ⟨bit,bound⟩ then weights[x] else 0)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [packedBit_eq]
      split <;> first | rfl | exact (map_zero _).symm
    rw [foldEq] at bitEq
    have mapped := congrArg (fun b => if b then (1 : ZMod 2) else 0) bitEq
    change baseBitHom ⟨bit,bound⟩ _ = extBitHom i _ at mapped
    rw [map_sum] at mapped
    have summed : baseBitHom ⟨bit,bound⟩ (∑ x : Fin count, if extBit weights[x] i then f[x] else 0) =
        ∑ x : Fin count, extBitHom i (if packedBit f[x].val ⟨bit,bound⟩ then weights[x] else 0) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x _
      cases h : extBit weights[x] i <;> cases h' : packedBit f[x].val ⟨bit,bound⟩ <;>
        simp_all only [Bool.false_eq_true, ↓reduceIte, map_zero] <;>
        simp_all only [baseBitHom, extBitHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Bool.false_eq_true, ↓reduceIte]
    rw [← summed] at mapped
    simp only [baseBitHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, packedBit_eq] at mapped
    change _ = _ at mapped
    have result : (transposeExt (foldBits f weights))[i].val.toBitVec.getLsbD bit =
        (∑ x : Fin count, if extBit weights[x] i then f[x] else 0).val.toBitVec.getLsbD bit := by
      cases hl : (transposeExt (foldBits f weights))[i].val.toBitVec.getLsbD bit <;>
        cases hr : (∑ x : Fin count, if extBit weights[x] i then f[x] else 0).val.toBitVec.getLsbD bit <;>
        simp only [hl, hr, Bool.false_eq_true, ite_false, ite_true] at mapped ⊢
      all_goals contradiction
    exact result
  · omega
/-- A field interpretation of the native three-register accumulator. -/
theorem sumExt_toField (n : Nat) (f : Fin n → WordExt3) :
    (sumExt n f).toField = ∑ i, (f i).toField := by
  rw [sumExt, sumExtLoop_refines]
  have hz : (⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩ : WordExt3).toField = 0 := by
    exact map_zero WordExt3.ringEquiv
  rw [hz, zero_add]
/-- Eight-bit portions of a transposed base word. -/
def wordByte (a : UInt64) (byte : Fin 8) : UInt8 :=
  (a >>> (8*byte.val).toUInt64).toUInt8
/-- Byte selection preserves the corresponding physical bit. -/
theorem wordByte_bit (a : UInt64) (byte bit : Fin 8) :
    (wordByte a byte).toNat.testBit bit.val =
      packedBit a ⟨8*byte.val+bit.val, by omega⟩ := by
  rw [packedBit_eq]
  change _ = a.toBitVec.getLsbD (8*byte.val+bit.val)
  simp only [wordByte, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.toUInt64, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, bit.isLt, decide_true, Bool.true_and]
  rw [Nat.mod_eq_of_lt (by have := byte.isLt; omega : 8*byte.val < 2^64),
    Nat.mod_eq_of_lt (by have := byte.isLt; omega : 8*byte.val < 64), Nat.testBit_shiftRight]
  rfl
set_option smartUnfolding true

/-- Build binary subset sums by sharing the lower half of each successive table. -/
def byteSubsetSums {R : Type} [AddCommMonoid R] (values : Array R) (n : Nat) : Array R :=
  match n with
  | 0 => #[0]
  | n+1 =>
    let low := byteSubsetSums values n
    low ++ low.map (fun x => x + values.getD n 0)
termination_by structural n

/-- A subset table has one entry for every binary mask. -/
@[simp] theorem byteSubsetSums_size {R : Type} [AddCommMonoid R] (values : Array R) (n : Nat) :
    (byteSubsetSums values n).size = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [byteSubsetSums, Array.size_append, Array.size_map, ih, pow_succ]; omega

/-- Each shared table entry is the sum selected by its binary mask. -/
theorem byteSubsetSums_get {R : Type} [AddCommMonoid R] (values : Array R) (n u : Nat)
    (hu : u < 2^n) :
    (byteSubsetSums values n)[u]'(by rw [byteSubsetSums_size]; exact hu) =
      ∑ k : Fin n, if u.testBit k.val then values.getD k.val 0 else 0 := by
  induction n generalizing u with
  | zero =>
    have : u = 0 := by simp only [pow_zero] at hu; omega
    subst u
    simp only [byteSubsetSums, Array.getElem_singleton, Fin.sum_univ_zero]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    by_cases low : u < 2^n
    · have bit : u.testBit n = false := Nat.testBit_lt_two_pow low
      simp only [byteSubsetSums]
      rw [Array.getElem_append_left (by rw [byteSubsetSums_size]; exact low)]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, add_zero, Fin.val_castSucc, Fin.val_last]
      exact ih u low
    · have bound : u - 2^n < 2^n := by rw [pow_succ] at hu; omega
      have split : u = 2^n + (u-2^n) := by omega
      have bit : u.testBit n = true := by
        rw [split, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow bound]; rfl
      have bits (k : Fin n) : u.testBit k.val = (u-2^n).testBit k.val := by
        conv_lhs => rw [split]
        exact Nat.testBit_two_pow_add_gt k.isLt _
      simp only [byteSubsetSums]
      rw [Array.getElem_append_right (by rw [byteSubsetSums_size]; omega)]
      simp only [Array.getElem_map, byteSubsetSums_size, ih (u-2^n) bound, Fin.val_castSucc,
        Fin.val_last, bit, ↓reduceIte, bits]

set_option smartUnfolding false

/-- The Four-Russians images of each group of eight extension weights. -/
def prepareBitFold (blocks : Nat) (weights : Vector WordExt3 (blocks*64)) :
    Vector (Vector WordExt3 256) (blocks*8) :=
  Vector.ofFn fun byte =>
    let values : Vector WordExt3 8 := Vector.ofFn fun bit =>
      weights[8*byte.val+bit.val]'(by have := byte.isLt; have := bit.isLt; omega)
    ⟨byteSubsetSums values.toArray 8, byteSubsetSums_size _ _⟩
/-- Each byte-table entry is its selected eight-weight sum. -/
theorem prepareBitFold_get (blocks : Nat) (weights : Vector WordExt3 (blocks*64))
    (byte : Fin (blocks*8)) (digit : Fin 256) :
    (prepareBitFold blocks weights)[byte][digit] =
      ∑ bit : Fin 8, if digit.val.testBit bit.val then
        weights[8*byte.val+bit.val]'(by have := byte.isLt; have := bit.isLt; omega) else 0 := by
  simp only [prepareBitFold, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_mk]
  rw [byteSubsetSums_get _ _ _ (by exact digit.isLt)]
  simp only [Array.getD_eq_getD_getElem?, Vector.size_toArray, Fin.isLt,
    Array.getElem?_eq_getElem, Option.getD_some, Vector.getElem_toArray, Vector.getElem_ofFn]
/-- Bit-transposed 64-word blocks of one witness lane. -/
def transposeWords (blocks : Nat) (f : Vector Word (blocks*64)) :
    Vector AdditiveNTT.Bitsliced.Block blocks :=
  Vector.ofFn fun block => AdditiveNTT.Bitsliced.transpose
    (AdditiveNTT.Bitsliced.Block.ofFn fun row =>
      (f[block.val*64+row.val]'(by have := block.isLt; have := row.isLt; omega)).val)
/-- Transposed witness bytes contain the original sixty-four word bits. -/
theorem transposeWords_byte (blocks : Nat) (f : Vector Word (blocks*64))
    (byte : Fin (blocks*8)) (row : Fin 64) (bit : Fin 8) :
    (wordByte ((transposeWords blocks f)[(⟨byte.val/8, by omega⟩ : Fin blocks)].get row)
      ⟨byte.val%8, by omega⟩).toNat.testBit bit.val =
      packedBit (f[8*byte.val+bit.val]'(by have := byte.isLt; have := bit.isLt; omega)).val row := by
  rw [wordByte_bit]
  simp only [transposeWords, Fin.getElem_fin, Vector.getElem_ofFn, packedBit_eq]
  have h := AdditiveNTT.Bitsliced.bit_transpose
    (AdditiveNTT.Bitsliced.Block.ofFn fun row : Fin 64 =>
      (f[byte.val/8*64+row.val]'(by have := byte.isLt; have := row.isLt; omega)).val)
    row ⟨8*(byte.val%8)+bit.val, by omega⟩
  simp only [AdditiveNTT.Bitsliced.bit, AdditiveNTT.Bitsliced.Block.get_ofFn] at h
  have index : byte.val/8*64+(8*(byte.val%8)+bit.val) = 8*byte.val+bit.val := by omega
  simp only [index] at h
  exact h
/-- Apply the shared eight-weight tables to all sixty-four witness bit rows. -/
def foldBitTables (blocks : Nat) (tables : Vector (Vector WordExt3 256) (blocks*8))
    (f : Vector Word (blocks*64)) : Vector WordExt3 64 :=
  let rows := transposeWords blocks f
  Vector.ofFn fun row => sumExt (blocks*8) fun byte =>
    let digit := wordByte ((rows[(⟨byte.val/8, by omega⟩ : Fin blocks)]).get row) ⟨byte.val%8, by omega⟩
    tables[byte][digit.toNat]'digit.toNat_lt
/-- Materialize scalar-register planes in direct indexed storage. -/
def blockWords (a : AdditiveNTT.Bitsliced.Block) : Vector UInt64 64 :=
  #v[a.w0, a.w1, a.w2, a.w3, a.w4, a.w5, a.w6, a.w7, a.w8, a.w9, a.w10, a.w11, a.w12, a.w13, a.w14, a.w15, a.w16, a.w17, a.w18, a.w19, a.w20, a.w21, a.w22, a.w23, a.w24, a.w25, a.w26, a.w27, a.w28, a.w29, a.w30, a.w31, a.w32, a.w33, a.w34, a.w35, a.w36, a.w37, a.w38, a.w39, a.w40, a.w41, a.w42, a.w43, a.w44, a.w45, a.w46, a.w47, a.w48, a.w49, a.w50, a.w51, a.w52, a.w53, a.w54, a.w55, a.w56, a.w57, a.w58, a.w59, a.w60, a.w61, a.w62, a.w63]
/-- Indexed storage retains every scalar-register bit plane. -/
theorem blockWords_get (a : AdditiveNTT.Bitsliced.Block) (i : Fin 64) :
    (blockWords a)[i] = a.get i := by
  fin_cases i <;> rfl

/-- Natural indexed plane loads retain the selected scalar-register plane. -/
theorem blockWords_getNat (a : AdditiveNTT.Bitsliced.Block) (i : Nat) (h : i < 64) :
    (blockWords a)[i] = a.get ⟨i, h⟩ := blockWords_get a ⟨i, h⟩

/-- Fold byte tables with direct plane loads inside the innermost loop. -/
def foldBitTablesArray (blocks : Nat) (tables : Vector (Vector WordExt3 256) (blocks*8))
    (f : Vector Word (blocks*64)) : Vector WordExt3 64 :=
  let rows := (transposeWords blocks f).map blockWords
  Vector.ofFn fun row => sumExt (blocks*8) fun byte =>
    let digit := wordByte rows[(⟨byte.val/8, by omega⟩ : Fin blocks)][row] ⟨byte.val%8, by omega⟩
    tables[byte][digit.toNat]'digit.toNat_lt

/-- Direct plane loads preserve every lookup and accumulated bit row. -/
@[csimp] theorem foldBitTables_code : @foldBitTables = @foldBitTablesArray := by
  funext blocks tables f
  unfold foldBitTables foldBitTablesArray
  simp only [Fin.getElem_fin, Vector.getElem_map, blockWords_getNat]

/-- Shared byte tables implement the complete weighted bit fold. -/
theorem foldBitTables_eq (blocks : Nat) (weights : Vector WordExt3 (blocks*64))
    (f : Vector Word (blocks*64)) :
    foldBitTables blocks (prepareBitFold blocks weights) f = foldBits f weights := by
  apply Vector.ext
  intro row hr
  apply WordExt3.toField_injective
  unfold foldBitTables
  rw [Vector.getElem_ofFn, sumExt_toField]
  have rhs := foldBits_refines f weights (⟨row,hr⟩ : Fin 64)
  change (foldBits f weights)[row].toField = _ at rhs
  rw [rhs]
  let equiv : Fin (blocks*8) × Fin 8 ≃ Fin (blocks*64) :=
    finProdFinEquiv.trans (finCongr (by omega))
  conv_rhs => rw [← equiv.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro byte _
  dsimp only
  have entry := prepareBitFold_get blocks weights byte
    ⟨(wordByte ((transposeWords blocks f)[(⟨byte.val/8, by omega⟩ : Fin blocks)].get ⟨row,hr⟩)
      ⟨byte.val%8, by omega⟩).toNat, UInt8.toNat_lt _⟩
  simp only [Fin.getElem_fin] at entry ⊢
  rw [entry]
  change WordExt3.ringEquiv (∑ bit : Fin 8, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro bit _
  have hb := transposeWords_byte blocks f byte (⟨row,hr⟩ : Fin 64) bit
  simp only [Fin.getElem_fin] at hb
  simp only [hb]
  simp only [equiv, Equiv.trans_apply, finProdFinEquiv, Equiv.coe_fn_mk, Fin.cast, finCongr, Nat.add_comm]
  rw [packedBit_eq]
  split <;> first | rfl | exact map_zero _
/-- The polynomial-basis vector is the corresponding power of the base generator. -/
theorem bitBasis_pow (i : Fin 64) :
    binaryBasisVector i = (Word.mk 2).toField ^ i.val := by
  have basis (j : Fin 64) : toQuot (binaryBasisVector j) =
      AdjoinRoot.mk basePoly (Polynomial.X ^ j.val) := by
    rw [toQuot, toPolyBF64, binaryBasisVector, toBitVec_ofBitVec,
      BinaryField.toPoly_one_shiftLeft j.val j.isLt]
  have hx : toQuot (Word.mk 2).toField = AdjoinRoot.mk basePoly Polynomial.X := by
    have h : (Word.mk 2).toField = binaryBasisVector 1 := by
      unfold Word.toField binaryBasisVector
      rfl
    rw [h, basis]
    change (AdjoinRoot.mk basePoly) (Polynomial.X ^ 1) = _
    rw [pow_one]
  apply toQuot_injective
  rw [basis, toQuot_npow, hx, ← map_pow]
/-- Multiply all three extension coefficients by the base polynomial generator. -/
@[inline] def shiftBitRow (a : WordExt3) : WordExt3 :=
  ⟨Sumcheck.timesX a.c0, Sumcheck.timesX a.c1, Sumcheck.timesX a.c2⟩
/-- The coefficientwise shift is multiplication by the embedded base generator. -/
theorem shiftBitRow_refines (a : WordExt3) :
    (shiftBitRow a).toField = (algebraMap BF64 BF64.Ext3) (Word.mk 2).toField * a.toField := by
  rw [← Algebra.smul_def]
  apply CompPoly.Extension.Ext.ext
  intro i
  rw [CompPoly.Extension.Ext.coeff_smul]
  fin_cases i <;>
    simp only [shiftBitRow, WordExt3.toField, CompPoly.Extension.Ext.coeff_ofFn,
      Nat.reduceEqDiff, ↓reduceIte, Sumcheck.timesX_toField]
/-- Horner reconstruction of weighted witness bits with three shift/XOR accumulators. -/
def reconstructBitLoop (sigma : Vector WordExt3 64) (n : Nat) (bound : n ≤ 64)
    (acc : WordExt3) : WordExt3 :=
  match n with
  | 0 => acc
  | n+1 => reconstructBitLoop sigma n (by omega)
      (WordExt3.add (shiftBitRow acc) sigma[n])
termination_by structural n
/-- Horner reconstruction retains the accumulated high coefficients and all lower bit rows. -/
theorem reconstructBitLoop_refines (sigma : Vector WordExt3 64)
    (n : Nat) (bound : n ≤ 64) (acc : WordExt3) :
    (reconstructBitLoop sigma n bound acc).toField =
      acc.toField * ((algebraMap BF64 BF64.Ext3) (Word.mk 2).toField)^n +
        ∑ i : Fin n, sigma[i.val].toField *
          ((algebraMap BF64 BF64.Ext3) (Word.mk 2).toField)^i.val := by
  induction n generalizing acc with
  | zero =>
    rw [reconstructBitLoop]
    simp only [pow_zero, mul_one, Fin.sum_univ_zero, add_zero]
  | succ n ih =>
    rw [reconstructBitLoop, ih, WordExt3.toField_add, shiftBitRow_refines,
      Fin.sum_univ_castSucc, pow_succ]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring
/-- Complete bit-row reconstruction using only polynomial shifts and XORs. -/
def reconstructBits (sigma : Vector WordExt3 64) : WordExt3 :=
  reconstructBitLoop sigma 64 (Nat.le_refl _) 0
/-- Shift/XOR reconstruction equals the mixed weighted sum of all sixty-four bit rows. -/
theorem reconstructBits_refines (sigma : Vector WordExt3 64) :
    (reconstructBits sigma).toField = ∑ i : Fin 64,
      sigma[i].toField * (algebraMap BF64 BF64.Ext3) (binaryBasisVector i) := by
  rw [reconstructBits, reconstructBitLoop_refines]
  have hz : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
  rw [hz, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin]
  rw [bitBasis_pow, map_pow]
/-- Reference reconstruction from sixty-four weighted physical bits. -/
def reconstructBitsSpec (sigma : Vector WordExt3 64) : WordExt3 :=
  sumExt 64 fun bit => WordExt3.mulScalar sigma[bit] (AdditiveNTT.Packed.flatBasis bit)
/-- Native bit reconstruction shares polynomial shifts instead of independent mixed products. -/
@[csimp] theorem reconstructBits_code : reconstructBitsSpec = reconstructBits := by
  funext sigma
  apply WordExt3.toField_injective
  rw [reconstructBitsSpec, sumExt_toField, reconstructBits_refines]
  apply Finset.sum_congr rfl
  intro i _
  rw [WordExt3.toField_mulScalar, AdditiveNTT.Packed.flatBasis_toField, Algebra.smul_def, mul_comm]
/-- Mixed base/extension dot product from one shared bit-fold plan. -/
def dotBitTables (blocks : Nat) (tables : Vector (Vector WordExt3 256) (blocks*8))
    (f : Vector Word (blocks*64)) : WordExt3 :=
  let sigma := foldBitTables blocks tables f
  reconstructBitsSpec sigma
/-- Reconstructing the sixty-four bit rows gives the complete mixed dot product. -/
theorem dotBitTables_refines (blocks : Nat) (weights : Vector WordExt3 (blocks*64))
    (f : Vector Word (blocks*64)) :
    (dotBitTables blocks (prepareBitFold blocks weights) f).toField =
      ∑ x : Fin (blocks*64), weights[x].toField * (algebraMap BF64 BF64.Ext3) f[x].toField := by
  unfold dotBitTables reconstructBitsSpec
  rw [sumExt_toField, foldBitTables_eq]
  simp only [WordExt3.toField_mulScalar, Algebra.smul_def,
    AdditiveNTT.Packed.flatBasis_toField, foldBits_refines, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [BF64.eq_sum_binaryBasisVector f[x].toField, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  have bitEq : f[x].toField.toBitVec.getLsb bit = f[x].val.toBitVec.getLsbD bit.val := by
    unfold Word.toField
    rfl
  rw [bitEq]
  split
  · exact mul_comm _ _
  · simp only [map_zero, mul_zero]
/-- A finite sum is unchanged by extending its table with zeros. -/
theorem sum_zero_padding {F : Type} [AddCommMonoid F] (count total : Nat)
    (fits : count ≤ total) (f : Fin count → F) :
    (∑ i : Fin total, if h : i.val < count then f ⟨i.val,h⟩ else 0) = ∑ i : Fin count, f i := by
  let g (i : Nat) : F := if h : i < count then f ⟨i,h⟩ else 0
  change (∑ i : Fin total, g i.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i ∈ Finset.range count, g i := by
      symm
      apply Finset.sum_subset (Finset.range_mono fits)
      intro i _ outside
      have h : ¬i < count := by simpa only [Finset.mem_range] using outside
      simp only [g, h, dite_false]
    _ = ∑ i : Fin count, f i := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp only [g, i.isLt, dite_true, Fin.eta]
/-- Zero padding to complete sixty-four-word transposition blocks. -/
def bitFoldBlocks (count : Nat) : Nat := (count+63)/64
/-- Every retained value fits in its complete transposition blocks. -/
theorem bitFoldBlocks_fits (count : Nat) : count ≤ bitFoldBlocks count*64 := by
  unfold bitFoldBlocks
  omega
/-- Retain the input values and pad the final transposition block with zero. -/
def bitFoldPad {F : Type} [Zero F] {count : Nat} (values : Vector F count) :
    Vector F (bitFoldBlocks count*64) :=
  Vector.ofFn fun i => if h : i.val < count then values[i.val]'h else 0
/-- Shared byte images of an arbitrary-length extension-weight table. -/
abbrev ByteFoldPlan (count : Nat) := Vector (Vector WordExt3 256) (bitFoldBlocks count*8)
/-- Prepare each eight-weight byte table once for every witness lane. -/
def prepareByteFold {count : Nat} (weights : Vector WordExt3 count) : ByteFoldPlan count :=
  prepareBitFold (bitFoldBlocks count) (bitFoldPad weights)
/-- Fold arbitrary-length witness bit rows through a retained byte plan. -/
def foldBytePlan {count : Nat} (plan : ByteFoldPlan count) (f : Vector Word count) :
    Vector WordExt3 64 :=
  foldBitTables (bitFoldBlocks count) plan (bitFoldPad f)
/-- Byte plans preserve every weighted bit row including a partial final block. -/
theorem foldBytePlan_eq {count : Nat} (weights : Vector WordExt3 count) (f : Vector Word count) :
    foldBytePlan (prepareByteFold weights) f = foldBits f weights := by
  apply Vector.ext
  intro bit hbit
  apply WordExt3.toField_injective
  unfold foldBytePlan prepareByteFold
  rw [foldBitTables_eq]
  have a := foldBits_refines (bitFoldPad f) (bitFoldPad weights) (⟨bit,hbit⟩ : Fin 64)
  have b := foldBits_refines f weights (⟨bit,hbit⟩ : Fin 64)
  change (foldBits (bitFoldPad f) (bitFoldPad weights))[bit].toField = _ at a
  change (foldBits f weights)[bit].toField = _ at b
  rw [a, b]
  calc
    _ = ∑ i : Fin (bitFoldBlocks count*64), if h : i.val < count then
        (if f[i.val].val.toBitVec.getLsbD bit then weights[i.val].toField else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [bitFoldPad, Fin.getElem_fin, Vector.getElem_ofFn]
      split
      · rfl
      · rename_i outside
        have hz : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
        simp only [hz, ite_self]
    _ = _ := by
      simpa only [Fin.getElem_fin] using sum_zero_padding count _ (bitFoldBlocks_fits count)
        (fun i : Fin count => if f[i].val.toBitVec.getLsbD bit then weights[i].toField else 0)
/-- Mixed dot product using a retained arbitrary-length byte plan. -/
def dotBytePlan {count : Nat} (plan : ByteFoldPlan count) (f : Vector Word count) : WordExt3 :=
  dotBitTables (bitFoldBlocks count) plan (bitFoldPad f)
/-- Padding and shared byte tables preserve the complete mixed inner product. -/
theorem dotBytePlan_refines {count : Nat} (weights : Vector WordExt3 count) (f : Vector Word count) :
    (dotBytePlan (prepareByteFold weights) f).toField =
      ∑ i : Fin count, weights[i].toField * (algebraMap BF64 BF64.Ext3) f[i].toField := by
  unfold dotBytePlan prepareByteFold
  rw [dotBitTables_refines]
  calc
    _ = ∑ i : Fin (bitFoldBlocks count*64), if h : i.val < count then
        weights[i.val].toField * (algebraMap BF64 BF64.Ext3) f[i.val].toField else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [bitFoldPad, Fin.getElem_fin, Vector.getElem_ofFn]
      split
      · rfl
      · have hz : (0 : WordExt3).toField = 0 := map_zero WordExt3.ringEquiv
        simp only [hz, zero_mul]
    _ = _ := by
      simpa only [Fin.getElem_fin] using sum_zero_padding count _ (bitFoldBlocks_fits count)
        (fun i : Fin count => weights[i].toField * (algebraMap BF64 BF64.Ext3) f[i].toField)
end CompStark.Pcs
