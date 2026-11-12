/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.SubsetTables

/-! Exact bit-selection semantics of the committed-input byte transpose and lookup maps. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Gathering and transposing eight lane bytes retains each source bit in its selected column. -/
theorem bitColumns_bit (a b c d e f g h shift : UInt64) (bit row : Fin 8) :
    (bitColumns a b c d e f g h shift).toBitVec.getLsbD (8*bit.val+row.val) =
      (#[a,b,c,d,e,f,g,h][row.val]!).toBitVec.getLsbD (shift.toNat%64+bit.val) := by
  unfold bitColumns
  rw [transposeByte_bit]
  fin_cases row <;> fin_cases bit <;>
    simp [UInt64.toBitVec_or,UInt64.toBitVec_and,UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight,UInt64.toBitVec_ofNat,BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq']

/-- Selecting a transposed byte enumerates exactly the eight committed source words at that bit. -/
theorem bitColumns_byte_testBit (a b c d e f g h : UInt64) (byte bit row : Fin 8) :
    ((bitColumns a b c d e f g h (8*byte.val).toUInt64 >>> (8*bit.val).toUInt64) &&& 255).toNat.testBit row.val =
      (#[a,b,c,d,e,f,g,h][row.val]!).toNat.testBit (8*byte.val+bit.val) := by
  have hs (i : Fin 8) : ((8*i.val).toUInt64).toNat%64 = 8*i.val := by
    have := i.isLt
    rw [Nat.toUInt64,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  simp only [UInt64.toNat_and,Nat.testBit_and,UInt64.toNat_shiftRight,hs,
    Nat.testBit_shiftRight,UInt64.reduceToNat]
  have hm : (255 : Nat).testBit row.val = true := by
    simpa only [show (2^8-1 : Nat) = 255 from rfl,row.isLt,decide_true] using
      Nat.testBit_two_pow_sub_one 8 row.val
  rw [hm,Bool.and_true]
  have hb := bitColumns_bit a b c d e f g h (8*byte.val).toUInt64 bit row
  simpa only [hs,BitVec.getLsbD,UInt64.toNat_toBitVec] using hb

/-- One input-opening byte lookup is its exact weighted selection of eight committed bits. -/
theorem inputByte_lookup (weights : Array W) (start : Nat) (hs : start+8 ≤ weights.size)
    (a b c d e f g h : UInt64) (byte bit : Fin 8) :
    (subsets (weights.extract start (start+8)))[((bitColumns a b c d e f g h (8*byte.val).toUInt64 >>> (8*bit.val).toUInt64) &&& 255).toNat]! =
      ∑ row : Fin 8, if (#[a,b,c,d,e,f,g,h][row.val]!).toNat.testBit (8*byte.val+bit.val)
        then weights[start+row.val]! else 0 := by
  have hsize : (weights.extract start (start+8)).size = 8 := by
    rw [Array.size_extract,Nat.min_eq_left hs]
    omega
  rw [subsets_get _ _ (by rw [hsize,UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)),
    byteSubset,hsize,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro row _
  rw [bitColumns_byte_testBit]
  have hget : (weights.extract start (start+8))[row.val]! = weights[start+row.val]! := by
    rw [getElem!_pos _ _ (by rw [hsize]; exact row.isLt),Array.getElem_extract,
      getElem!_pos weights _ (by have := row.isLt; omega)]
  rw [hget]

end CompStark.Keccak.GkrProver
