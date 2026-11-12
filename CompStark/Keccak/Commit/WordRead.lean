/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.Commit.Bytes
public import CompPoly.Data.ByteArray.Pack

/-! Complete little-endian words through the approved packed byte loads. -/
@[expose] public section
namespace CompStark.Keccak.Commit
set_option maxHeartbeats 1000000

/-- Decode complete words with two bounded native loads, retaining partial-word semantics. -/
@[inline] def readWordPacked (bytes : ByteArray) (offset : Nat) : UInt64 :=
  if bound : offset+8 ≤ bytes.size then
    (bytes.getUInt32LE offset (by omega)).toUInt64 |||
      ((bytes.getUInt32LE (offset+4) (by omega)).toUInt64 <<< 32)
  else readWord bytes offset

/-- Packed decoding retains every byte of complete and partial input words. -/
@[csimp] theorem readWord_code : readWord = readWordPacked := by
  funext bytes offset
  unfold readWordPacked
  split
  · rename_i bound
    have lo : offset+4 ≤ bytes.size := by omega
    have hi : offset+4+4 ≤ bytes.size := by omega
    apply UInt64.toBitVec_inj.mp
    simp only [readWord, show List.range 8 = [0,1,2,3,4,5,6,7] from rfl,
      List.foldl_cons,List.foldl_nil,ByteArray.getUInt32LE,ByteArray.getUInt32LE!,
      lo,hi,ite_true,UInt64.toBitVec_or,UInt64.toBitVec_shiftLeft,UInt64.toBitVec_ofNat,
      UInt32.toBitVec_toUInt64,UInt32.toBitVec_or,UInt32.toBitVec_shiftLeft,
      UInt32.toBitVec_ofNat,UInt8.toBitVec_toUInt32,UInt8.toBitVec_toUInt64,
      ByteArray.get!_eq_getElem!,Nat.reduceMul,Nat.add_zero,Nat.add_assoc]
    apply BitVec.eq_of_getLsbD_eq
    intro i bit
    interval_cases i <;> simp
  · rfl
end CompStark.Keccak.Commit
