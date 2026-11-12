/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.InputColumns
public import CompStark.Keccak.GkrProver.PackedAccumulation

/-! Structural block traversal and coordinate semantics of the native committed-input opening table. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The byte lookup contributed by one group of eight committed words to a retained input bit. -/
def inputGroupValue (committed : Array UInt64) (n : Nat) (weights : Array W)
    (slot inst group z : Nat) : W :=
  let offset := slot*n+128*group+inst
  let columns := bitColumns committed[offset]! committed[offset+16]! committed[offset+32]!
    committed[offset+48]! committed[offset+64]! committed[offset+80]! committed[offset+96]!
    committed[offset+112]! (8*(z/8)).toUInt64
  (subsets (weights.extract (8*group) (8*group+8)))[((columns >>> (8*(z%8)).toUInt64) &&& 255).toNat]!

/-- The complete group traversal adds one 64-bit block for a fixed slot and low inst coordinate. -/
def inputGroups (committed : Array UInt64) (n : Nat) (weights : Array W)
    (slot inst : Nat) (out : PackedE) : PackedE :=
  (List.range (n/128)).foldl (fun state group =>
    addPackedBlock state ((inst+16*slot)*64) 64 (inputGroupValue committed n weights slot inst group)) out

/-- Byte-major bit traversal enumerates the sixty-four consecutive bit coordinates exactly once. -/
theorem byteBitRange_eq :
    (List.range 8).flatMap (fun byte => (List.range 8).map (fun bit => 8*byte+bit)) = List.range 64 := by
  decide

/-- The two production byte-and-bit loops equal one contiguous additive block update. -/
theorem inputGroup_loops (committed : Array UInt64) (n : Nat) (weights : Array W)
    (slot inst group : Nat) (out : PackedE) :
    addPackedBlock out ((inst+16*slot)*64) 64 (inputGroupValue committed n weights slot inst group) =
      (List.range 8).foldl (fun state byte => (List.range 8).foldl (fun state bit =>
        let offset := slot*n+128*group+inst
        let columns := bitColumns committed[offset]! committed[offset+16]! committed[offset+32]!
          committed[offset+48]! committed[offset+64]! committed[offset+80]! committed[offset+96]!
          committed[offset+112]! (8*byte).toUInt64
        let value := (subsets (weights.extract (8*group) (8*group+8)))[((columns >>> (8*bit).toUInt64) &&& 255).toNat]!
        let j := (inst+16*slot)*64+8*byte+bit
        state.set j (WordExt3.add (state.get j) value)) state) out := by
  unfold addPackedBlock
  rw [← byteBitRange_eq,List.foldl_flatMap]
  apply foldl_congr_mem
  intro state byte _
  rw [List.foldl_map]
  apply foldl_congr_mem
  intro state bit hb
  have hb := List.mem_range.mp hb
  simp only [inputGroupValue,show (8*byte+bit)/8 = byte by omega,
    show (8*byte+bit)%8 = bit by omega,Nat.add_assoc]
  rfl

/-- The actual native bit-opening table is its structural slot, inst and group block traversal. -/
theorem inputBits_eq_blocks (committed : Array UInt64) (n : Nat) (point : Array W) :
    inputBits committed n point =
      ((List.range 64).foldl (fun state slot =>
        (List.range 16).foldl (fun state inst =>
          inputGroups committed n (eqTable point) slot inst state) state) (PackedE.zeros 65536)).toArray := by
  simp only [inputBits,Std.Legacy.Range.forIn_eq_forIn_range',List.forIn_pure_yield_eq_foldl,
    pure_bind,Id.run_pure,Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    ← List.range_eq_range']
  apply congrArg PackedE.toArray
  apply foldl_congr_mem
  intro state slot _
  apply foldl_congr_mem
  intro state inst _
  unfold inputGroups
  apply foldl_congr_mem
  intro state group hg
  rw [inputGroup_loops]
  have hg := List.mem_range.mp hg
  rw [getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hg),Array.getElem_ofFn]

end CompStark.Keccak.GkrProver
