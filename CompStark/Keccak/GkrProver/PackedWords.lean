/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompPoly.Fields.Binary.BF64.Packed
public import Lean.Elab.Tactic.Omega

/-! Complete packed-word reads determine the underlying byte buffer. -/
set_option maxRecDepth 32768
@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
/-- The two 32-bit halves of a little-endian 64-bit load are unique. -/
theorem halves_inj (a b c d : UInt32)
    (h : a.toUInt64 ||| (b.toUInt64 <<< 32) = c.toUInt64 ||| (d.toUInt64 <<< 32)) :
    a = c ∧ b = d := by
  have bits := congrArg UInt64.toBitVec h
  constructor
  · apply UInt32.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hb := congrArg (fun v : BitVec 64 => v.getLsbD i) bits
    simpa [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64,
      BitVec.shiftLeft_eq', BitVec.toNat_umod, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      show i < 64 by omega, show ¬32 ≤ i by omega, hi,
      decide_true,decide_false,Bool.true_and,Bool.false_and,Bool.or_false,ite_true] using hb
  · apply UInt32.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hb := congrArg (fun v : BitVec 64 => v.getLsbD (i+32)) bits
    simpa [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64,
      BitVec.shiftLeft_eq', BitVec.toNat_umod, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      show i+32 < 64 by omega, show ¬i+32 < 32 by omega, show 32 ≤ i+32 by omega,
      Nat.add_sub_cancel, hi,decide_true,decide_false,Bool.true_and,Bool.false_or,ite_true,ite_false] using hb
/-- Every byte of a packed field buffer is determined by its complete word reads. -/
theorem packed_ext (a b : Packed) (size : a.size = b.size)
    (same : ∀ i : Fin a.size, a.get i = b.get ⟨i.val,by omega⟩) : a = b := by
  rcases a with ⟨n,a,ha⟩
  rcases b with ⟨m,b,hb⟩
  change n = m at size
  subst m
  suffices a = b by subst b; rfl
  apply ByteArray.ext
  apply Array.ext
  · change a.size = b.size
    omega
  · intro i hi hj
    have hword : i/8 < n := by change i < a.size at hi; omega
    have hw := congrArg Word.val (same ⟨i/8,hword⟩)
    change (a.getUInt32LE (8*(i/8)) _).toUInt64 |||
      ((a.getUInt32LE (8*(i/8)+4) _).toUInt64 <<< 32) =
      (b.getUInt32LE (8*(i/8)) _).toUInt64 |||
      ((b.getUInt32LE (8*(i/8)+4) _).toUInt64 <<< 32) at hw
    have halves := halves_inj _ _ _ _ hw
    have hload : a.getUInt32LE! (4*(i/4)) = b.getUInt32LE! (4*(i/4)) := by
      by_cases h : i%8 < 4
      · have offset : 4*(i/4) = 8*(i/8) := by omega
        rw [offset]
        exact halves.1
      · have offset : 4*(i/4) = 8*(i/8)+4 := by omega
        rw [offset]
        exact halves.2
    rw [CompPoly.PackedRepr.getUInt32LE!_eq_ofWordBytes _ _ (by omega),
      CompPoly.PackedRepr.getUInt32LE!_eq_ofWordBytes _ _ (by omega)] at hload
    have hs := congrArg CompPoly.PackedRepr.wordBytes hload
    simp only [CompPoly.PackedRepr.wordBytes_ofWordBytes] at hs
    have hget := congrArg (fun v : Vector UInt8 4 => v[i%4]'(by omega)) hs
    simp only [ByteArray.bytesAt, Vector.getElem_ofFn] at hget
    change a.data[4*(i/4)+i%4]! = b.data[4*(i/4)+i%4]! at hget
    rw [show 4*(i/4)+i%4 = i by omega] at hget
    simpa only [getElem!_pos a.data i hi,getElem!_pos b.data i hj] using hget
end CompStark.Keccak.GkrProver
