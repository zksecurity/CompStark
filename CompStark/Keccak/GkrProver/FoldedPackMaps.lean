/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.SubsetTables
public import CompStark.Keccak.GkrProver.WeightMapEval
public import CompStark.Keccak.GkrProver.ProductVertices

/-! Certified RMFE semantics of the byte maps used to materialize the retained pack table. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- A masked little-endian word byte retains exactly its corresponding eight source bits. -/
theorem maskedByte_testBit (raw : UInt64) (byte : Fin 2) (bit : Fin 8) :
    ((raw >>> (8*byte.val).toUInt64) &&& 255).toNat.testBit bit.val =
      raw.toNat.testBit (8*byte.val+bit.val) := by
  have hs : ((8*byte.val).toUInt64).toNat%64 = 8*byte.val := by
    have hb := byte.isLt
    rw [Nat.toUInt64,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  simp only [UInt64.toNat_and,UInt64.toNat_shiftRight,hs,Nat.testBit_and,Nat.testBit_shiftRight,
    UInt64.reduceToNat]
  have hm : (255 : Nat).testBit bit.val = true := by
    simpa only [show (2^8-1 : Nat) = 255 from rfl,bit.isLt,decide_true] using
      Nat.testBit_two_pow_sub_one 8 bit.val
  rw [hm,Bool.and_true]

/-- A byte-subset lookup is the exact selection of its eight coefficients in a sixteen-entry basis. -/
theorem subsets_extract_byte (values : Array W) (hv : values.size = 16) (byte : Fin 2) (raw : UInt64) :
    (subsets (values.extract (8*byte.val) (8*byte.val+8)))[((raw >>> (8*byte.val).toUInt64) &&& 255).toNat]! =
      ∑ bit : Fin 8, if raw.toNat.testBit (8*byte.val+bit.val) then values[8*byte.val+bit.val]! else 0 := by
  have hb := byte.isLt
  have hs : (values.extract (8*byte.val) (8*byte.val+8)).size = 8 := by
    rw [Array.size_extract,hv,Nat.min_eq_left (by omega)]
    omega
  rw [subsets_get _ _ (by rw [hs,UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)),byteSubset,hs]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro bit _
  rw [maskedByte_testBit]
  have hget : (values.extract (8*byte.val) (8*byte.val+8))[bit.val]! =
      values[8*byte.val+bit.val]! := by
    rw [getElem!_pos _ _ (by rw [hs]; exact bit.isLt),Array.getElem_extract,
      getElem!_pos values _ (by rw [hv]; have := bit.isLt; omega)]
  rw [hget]

attribute [local irreducible] eqTable instanceWeights rmfeValue subsets

/-- The two byte lookups for a retained pack are its exact equality-weighted RMFE evaluation. -/
theorem foldedPackMaps_lookup (s : W) (point : Array W) (q : Fin 16) (raw : UInt64) :
    let maps := (foldedPackMaps (instanceWeights s) point)[q.val]!
    maps.1[(raw &&& 255).toNat]!+maps.2[((raw >>> 8) &&& 255).toNat]! =
      (eqTable point)[q.val]!*rmfeValue s (lane raw) := by
  have hs : (instanceWeights s).size = 16 := by unfold instanceWeights; exact Array.size_ofFn ..
  simp only [foldedPackMaps,getElem!_pos,Array.size_ofFn,Fin.isLt,Array.getElem_ofFn]
  let values := (instanceWeights s).map (fun x => WordExt3.mul (eqTable point)[q.val]! x)
  have hv : values.size = 16 := by rw [Array.size_map,hs]
  change (subsets (values.extract 0 8))[(raw &&& 255).toNat]!+
    (subsets (values.extract 8 16))[((raw >>> 8) &&& 255).toNat]! = _
  have hl := subsets_extract_byte values hv (0 : Fin 2) raw
  have hh := subsets_extract_byte values hv (1 : Fin 2) raw
  simp only [Fin.val_zero,Nat.mul_zero,Nat.zero_add,show (0 : Nat).toUInt64 = (0 : UInt64) from rfl,
    UInt64.shiftRight_zero] at hl
  simp only [Fin.val_one,Nat.mul_one,show 8+8 = (16 : Nat) from rfl,show (8 : Nat).toUInt64 = (8 : UInt64) from rfl] at hh
  rw [hl,hh,rmfeValue_bits,Fin.sum_univ_add (a := 8) (b := 8),mul_add]
  apply congrArg₂ (fun x y : W => x+y)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro bit _
    rw [getElem!_pos _ _ (by rw [hv]; have := bit.isLt; omega),Array.getElem_map]
    rw [← getElem!_pos (instanceWeights s) _ (by rw [hs]; have := bit.isLt; omega),
      instanceWeights_eq s ⟨bit.val,by have := bit.isLt; omega⟩]
    simp only [Fin.val_castAdd,mul_ite,mul_one,mul_zero]
    rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro bit _
    rw [getElem!_pos _ _ (by rw [hv]; have := bit.isLt; omega),Array.getElem_map]
    rw [← getElem!_pos (instanceWeights s) _ (by rw [hs]; have := bit.isLt; omega),
      instanceWeights_eq s ⟨8+bit.val,by have := bit.isLt; omega⟩]
    simp only [Fin.val_natAdd,mul_ite,mul_one,mul_zero]
    rfl

end CompStark.Keccak.GkrProver
