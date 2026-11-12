/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PackedTableValues
public import CompStark.Keccak.GkrProver.BinaryEvaluation

/-! Agreement between the retained native pack factors and the complete early tensor contractions. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- RMFE evaluation depends only on the sixteen simultaneous instance bits of a source word. -/
theorem rmfeValue_mask16 (s : W) (raw : UInt64) :
    rmfeValue s (lane (raw &&& 65535)) = rmfeValue s (lane raw) := by
  rw [rmfeValue_bits,rmfeValue_bits]
  apply Finset.sum_congr rfl
  intro i _
  rw [UInt64.toNat_and,Nat.testBit_and]
  have hm : (65535 : UInt64).toNat.testBit i.val = true := by
    simpa only [UInt64.reduceToNat,show (2^16-1 : Nat) = 65535 from rfl,i.isLt,decide_true] using
      Nat.testBit_two_pow_sub_one 16 i.val
  rw [hm,Bool.and_true]

/-- Machine-indexed tensor vertices are the exact natural-indexed sliced word under their address bound. -/
theorem tensorFactor_nat (s : W) (state : Array UInt64) (groups block : Nat) (j : Fin 1600)
    (q : Fin 16) (haddr : j.val*groups+4*block+q.val/4 < USize.size) :
    tensorFactor s state groups (16*block) j q.val =
      rmfeValue s (lane (state[j.val*groups+4*block+q.val/4]! >>> (16*(q.val%4)).toUInt64)) := by
  simp only [tensorFactor,tensorVertices,Nat.mod_eq_of_lt q.isLt]
  have hd : (16*block+q.val)/4 = 4*block+q.val/4 := by omega
  have hm : (16*block+q.val)%4 = q.val%4 := by omega
  rw [hd,hm]
  have hi : (j.val.toUSize*groups.toUSize+(4*block+q.val/4).toUSize).toNat =
      j.val*groups+4*block+q.val/4 := by
    simp only [Nat.toUSize,← USize.ofNat_mul,← USize.ofNat_add,USize.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by simpa only [Nat.add_assoc] using haddr)]
    omega
  rw [hi,rmfeValue_mask16]

/-- The retained table and early tensor use the identical four-coordinate multilinear factor contraction. -/
theorem packedTable_get_binaryInterpolate (w : SlicedWitness) (d : Nat) (s : W) (point : Array W)
    (hp : point.size = 4) (m : Fin 2) (b : Nat) (hb : b < 2^(w.nLog-4)/16) (j : Fin 1600)
    (haddr : ∀ q : Fin 16,j.val*(2^w.nLog/64)+4*b+q.val/4 < USize.size) :
    (packedTable w d (instanceWeights s) point).get ((m.val*(2^(w.nLog-4)/16)+b)*1600+j.val) =
      binaryInterpolate point.toList
        (tensorFactor s w.layers[12*(m.val+1)-d]! (2^w.nLog/64) (16*b) j) 0 := by
  rw [packedTable_get_rmfe w d s point m b hb j,binaryInterpolate_eqTable]
  simp only [hp,Nat.reducePow,Nat.mul_zero,Nat.zero_add]
  rw [← Fin.sum_univ_eq_sum_range (fun q => (eqTable point)[q]! *
    tensorFactor s w.layers[12*(m.val+1)-d]! (2^w.nLog/64) (16*b) j q) 16]
  apply Finset.sum_congr rfl
  intro q _
  rw [tensorFactor_nat s _ _ b j q (haddr q)]

end CompStark.Keccak.GkrProver
