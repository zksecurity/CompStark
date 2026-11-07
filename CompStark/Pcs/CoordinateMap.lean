/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.Tensor
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.FlatBasis

/-! Application of a shared binary-linear map through its coordinate images. -/
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs
open BF64 CompPoly.Extension

/-- Select a physical coefficient without converting to the specification field. -/
@[inline] def mapLimb (a : WordExt3) (j : Fin 3) : Word :=
  if j.val = 0 then a.c0 else if j.val = 1 then a.c1 else a.c2

/-- Accumulate selected coordinate images with three machine-word registers. -/
def coordinateLoop (weights : Vector WordExt3 192) (a : WordExt3) :
    (n : Nat) → n ≤ 192 → UInt64 → UInt64 → UInt64 → WordExt3
  | 0, _, x, y, z => ⟨⟨x⟩, ⟨y⟩, ⟨z⟩⟩
  | n + 1, h, x, y, z =>
    if packedBit (mapLimb a ⟨n / 64, by omega⟩).val ⟨n % 64, by omega⟩ then
      let w := weights[n]
      coordinateLoop weights a n (by omega) (x ^^^ w.c0.val) (y ^^^ w.c1.val) (z ^^^ w.c2.val)
    else coordinateLoop weights a n (by omega) x y z

/-- Apply shared coordinate images with native bit tests and XOR accumulation. -/
def applyCoordinates (weights : Vector WordExt3 192) (a : WordExt3) : WordExt3 :=
  coordinateLoop weights a 192 (by decide) 0 0 0

/-- Physical coefficient selection agrees with the extension representation. -/
theorem mapLimb_toField (a : WordExt3) (j : Fin 3) :
    (mapLimb a j).toField = Ext.coeff a.toField j := by
  fin_cases j <;> rfl

/-- Coordinate images use the tensor product of the two polynomial bases. -/
theorem coordinateBasis_toField (j : Fin 3) (i : Fin 64) :
    (coordinateBasis ⟨i.val + 64 * j.val, by omega⟩).toField =
      Ext.ofBase (BF64.binaryBasisVector i) * ext3Gen ^ j.val := by
  have hm : (i.val + 64 * j.val) % 64 = i.val := by omega
  change _ = (algebraMap BF64 Ext3) (BF64.binaryBasisVector i) * (Ext.gen : Ext3) ^ j.val
  rw [← Algebra.smul_def, Ext.gen_pow_of_lt j.isLt]
  apply Ext.ext
  intro c
  rw [Ext.coeff_smul, Ext.coeff_ofFn]
  have bit : (Word.mk ((1 : UInt64) <<< i.val.toUInt64)).toField = BF64.binaryBasisVector i :=
    AdditiveNTT.Packed.flatBasis_toField i
  fin_cases j <;> fin_cases c <;>
    simp only [coordinateBasis, hm, WordExt3.toField, Ext.coeff_ofFn] <;>
    split_ifs <;> first | contradiction | omega |
      (simp only [mul_zero, mul_one]; first | exact bit | rfl)

/-- Every extension word is the sum of its selected physical binary coordinates. -/
theorem coordinateExpansion (a : WordExt3) :
    a.toField = ∑ i : Fin 192,
      if packedBit (mapLimb a ⟨i.val / 64, by omega⟩).val ⟨i.val % 64, by omega⟩
      then (coordinateBasis i).toField else 0 := by
  rw [← (finProdFinEquiv : Fin 3 × Fin 64 ≃ Fin 192).sum_comp,
    Fintype.sum_prod_type, ext3_eq_sum_coeff a.toField]
  apply Finset.sum_congr rfl
  intro j _
  rw [BF64.eq_sum_binaryBasisVector (Ext.coeff a.toField j)]
  change (Ext.ofBaseRingHom ext3Params) _ * _ = _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hm : (i.val + 64 * j.val) % 64 = i.val := by omega
  have hd : (i.val + 64 * j.val) / 64 = j.val := by omega
  simp only [finProdFinEquiv, Equiv.coe_fn_mk, hm, hd, coordinateBasis_toField,
    packedBit_eq, ← mapLimb_toField, Ext.ofBaseRingHom_apply]
  have bit : (mapLimb a j).toField.toBitVec.getLsb i =
      (mapLimb a j).val.toBitVec.getLsbD i.val := by rfl
  rw [bit]
  split <;> simp only [Ext.ofBase_zero, zero_mul]

/-- Frobenius compositions are additive in characteristic two. -/
def frobeniusAddHom {F : Type} [CommRing F] [CharP F 2]
    (stages : List (Nat × F)) : F →+ F where
  toFun := frobeniusMap stages
  map_zero' := by
    induction stages with
    | nil => rfl
    | cons stage stages ih => simp only [frobeniusMap, zero_pow (Nat.two_pow_pos stage.1).ne', mul_zero, add_zero, ih]
  map_add' a b := by
    induction stages generalizing a b with
    | nil => rfl
    | cons stage stages ih =>
      simp only [frobeniusMap, add_pow_char_pow, mul_add]
      rw [show a + b + (stage.2 * a ^ 2 ^ stage.1 + stage.2 * b ^ 2 ^ stage.1) =
        (a + stage.2 * a ^ 2 ^ stage.1) + (b + stage.2 * b ^ 2 ^ stage.1) by ring, ih]

/-- The native loop equals the initial accumulator plus all visited coordinate images. -/
theorem coordinateLoop_refines (weights : Vector WordExt3 192) (a : WordExt3)
    (n : Nat) (h : n ≤ 192) (x y z : UInt64) :
    (coordinateLoop weights a n h x y z).toField = (WordExt3.mk ⟨x⟩ ⟨y⟩ ⟨z⟩).toField +
      ∑ i : Fin n, if packedBit (mapLimb a ⟨i.val / 64, by omega⟩).val ⟨i.val % 64, by omega⟩
        then weights[i.val].toField else 0 := by
  induction n generalizing x y z with
  | zero => simp only [coordinateLoop, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ n ih =>
    rw [coordinateLoop]
    split
    · rename_i hb
      rw [ih]
      change (WordExt3.add ⟨⟨x⟩, ⟨y⟩, ⟨z⟩⟩ weights[n]).toField + _ = _
      rw [WordExt3.toField_add, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hb, ↓reduceIte]
      rw [add_assoc, add_comm weights[n].toField]
    · rename_i hb
      rw [ih, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hb, Bool.false_eq_true, ↓reduceIte, add_zero]

/-- Shared coordinate application equals the six-map composition on every input word. -/
theorem applyCoordinates_refines (challenges : Vector WordExt3 6) (a : WordExt3) :
    applyCoordinates (coordinateWeights challenges) a = binary64Map challenges a := by
  apply WordExt3.toField_injective
  rw [applyCoordinates, coordinateLoop_refines]
  change 0 + _ = _
  rw [zero_add, binary64Map, wordMap_refines, coordinateExpansion a]
  let f := frobeniusAddHom ((binary64Stages challenges).map fun stage => (stage.1, stage.2.toField))
  change _ = f _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split
  · exact coordinateWeights_refines challenges i
  · exact (map_zero f).symm

end CompStark.Pcs
