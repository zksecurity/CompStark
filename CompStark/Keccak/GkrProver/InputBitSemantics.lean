/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.InputTableValues
public import CompStark.Keccak.GkrProver.BinaryEvaluation

/-! Multilinear semantics of every committed-input bit retained by the native opening prover. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- A native input group contributes the equality-weighted bits of its eight committed source words. -/
theorem inputGroupValue_sum (committed : Array UInt64) (n : Nat) (weights : Array W)
    (slot inst group : Nat) (hs : 8*group+8 ≤ weights.size) (z : Fin 64) :
    inputGroupValue committed n weights slot inst group z.val =
      ∑ row : Fin 8, if committed[slot*n+128*group+inst+16*row.val]!.toNat.testBit z.val
        then weights[8*group+row.val]! else 0 := by
  let offset := slot*n+128*group+inst
  let byte : Fin 8 := ⟨z.val/8,by have := z.isLt; omega⟩
  let bit : Fin 8 := ⟨z.val%8,Nat.mod_lt _ (by decide)⟩
  have h := inputByte_lookup weights (8*group) hs committed[offset]! committed[offset+16]!
    committed[offset+32]! committed[offset+48]! committed[offset+64]! committed[offset+80]!
    committed[offset+96]! committed[offset+112]! byte bit
  change inputGroupValue committed n weights slot inst group z.val = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro row _
  have hword : (#[committed[offset]!,committed[offset+16]!,committed[offset+32]!,committed[offset+48]!,
      committed[offset+64]!,committed[offset+80]!,committed[offset+96]!,committed[offset+112]!][row.val]!) =
        committed[offset+16*row.val]! := by
    fin_cases row <;> rfl
  rw [hword,show 8*byte.val+bit.val = z.val by dsimp only [byte,bit]; omega]

/-- Consecutive equal-width finite sums enumerate the identical contiguous source interval. -/
theorem sum_range_blocks (f : Nat → W) (width blocks : Nat) :
    (∑ block ∈ Finset.range blocks,∑ i ∈ Finset.range width,f (width*block+i)) =
      ∑ i ∈ Finset.range (width*blocks),f i := by
  induction blocks with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,Nat.mul_zero]
  | succ blocks ih =>
    rw [Finset.sum_range_succ,ih,Nat.mul_succ,Finset.sum_range_add]

attribute [local irreducible] eqTable inputGroupValue

/-- Every retained native input bit is the complete equality-weighted committed-bit column. -/
theorem inputBits_weighted (committed : Array UInt64) (n : Nat) (point : Array W)
    (hshape : 2^point.size = 8*(n/128)) (slot : Fin 64) (inst : Fin 16) (z : Fin 64) :
    (inputBits committed n point)[(inst.val+16*slot.val)*64+z.val]! =
      ∑ q ∈ Finset.range (2^point.size),
        (eqTable point)[q]! * if committed[slot.val*n+16*q+inst.val]!.toNat.testBit z.val then 1 else 0 := by
  rw [(inputBits_values committed n point slot inst z).2]
  have hgroup (group : Nat) (hg : group < n/128) :
      inputGroupValue committed n (eqTable point) slot.val inst.val group z.val =
        ∑ row ∈ Finset.range 8, (eqTable point)[8*group+row]! *
          if committed[slot.val*n+16*(8*group+row)+inst.val]!.toNat.testBit z.val then 1 else 0 := by
    rw [inputGroupValue_sum committed n (eqTable point) slot.val inst.val group
      (by rw [eqTable_size,hshape]; omega) z,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro row _
    rw [show slot.val*n+128*group+inst.val+16*row.val =
      slot.val*n+16*(8*group+row.val)+inst.val by ring]
    simp only [mul_ite,mul_one,mul_zero]
  calc
    _ = ∑ group ∈ Finset.range (n/128),∑ row ∈ Finset.range 8,
        (eqTable point)[8*group+row]! *
          if committed[slot.val*n+16*(8*group+row)+inst.val]!.toNat.testBit z.val then 1 else 0 :=
      Finset.sum_congr rfl (fun group hg => hgroup group (Finset.mem_range.mp hg))
    _ = _ := by
      rw [sum_range_blocks (fun q => (eqTable point)[q]! *
        if committed[slot.val*n+16*q+inst.val]!.toNat.testBit z.val then 1 else 0) 8 (n/128),← hshape]

/-- The production retained bit table is the exact multilinear contraction of the high instance coordinates. -/
theorem inputBits_binaryInterpolate (committed : Array UInt64) (n : Nat) (point : Array W)
    (hshape : 2^point.size = 8*(n/128)) (slot : Fin 64) (inst : Fin 16) (z : Fin 64) :
    (inputBits committed n point)[(inst.val+16*slot.val)*64+z.val]! =
      binaryInterpolate point.toList (fun q =>
        if committed[slot.val*n+16*q+inst.val]!.toNat.testBit z.val then 1 else 0) 0 := by
  simp only [binaryInterpolate_eqTable,Nat.mul_zero,Nat.zero_add]
  exact inputBits_weighted committed n point hshape slot inst z

end CompStark.Keccak.GkrProver
