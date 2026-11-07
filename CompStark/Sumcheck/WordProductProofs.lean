/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Sumcheck.WordProduct
/-! Kernel-checked interpolation and reduction identities for five-product multiplication. -/
public section
namespace CompStark.Sumcheck
open BF64
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The top shifted coordinate is exactly the word's highest bit. -/
private theorem topBit (a : BitVec 64) : a >>> 63 = if a.getLsbD 63 then 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i = 0
  · subst i
    cases hb : a.getLsbD 63 <;> have hb' : a[63] = _ := hb <;> simp [hb']
  · have hge : 64 ≤ 63 + i := by omega
    cases hb : a.getLsbD 63 <;> simp [BitVec.getLsbD_of_ge _ _ hge, BitVec.getLsbD_ofNat,
      Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))]

set_option linter.unusedSimpArgs false in
/-- Dividing by X and multiplying back preserves all sixty-four coordinates. -/
private theorem divideX_bits (a : BitVec 64) :
    let b := (a >>> 1) ^^^ (((0#64) - (a &&& (1#64))) &&& (0x800000000000000d#64))
    (b <<< 1) ^^^ (((0#64) - (b >>> 63)) &&& (0x1b#64)) = a := by
  dsimp only
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : a.getLsbD 0 <;> have h' : a[0] = _ := h <;>
    simp only [h, BitVec.ofBool_false, BitVec.ofBool_true, BitVec.setWidth_zero, BitVec.setWidth_one,
      BitVec.sub_zero, BitVec.neg_zero, BitVec.zero_and, BitVec.xor_zero]
  all_goals
    rw [topBit]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;>
      simp [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_of_ge, h, h']

/-- X multiplication agrees with multiplication by the polynomial-basis word two. -/
theorem timesX_toField (a : Word) : (timesX a).toField = (Word.mk 2).toField * a.toField :=
  Word.toField_xtime a.val

/-- The shift-and-correction division is a left inverse of X multiplication. -/
theorem timesX_divideX (a : Word) : timesX (divideX a) = a := by
  cases a with | mk value =>
  apply congrArg Word.mk
  apply UInt64.eq_of_toBitVec_eq
  change (Word.xtime ((value >>> 1) ^^^ (((0 : UInt64) - (value &&& 1)) &&& 0x800000000000000d))).toBitVec = value.toBitVec
  simpa only [Word.xtime, UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_sub,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.ofNat_eq_ofNat, BitVec.toNat_umod, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] using divideX_bits value.toBitVec

/-- Prefix XOR stages in the proof's fixed-width bitvector carrier. -/
private def prefixBits : Nat → BitVec 64 → BitVec 64
  | 0, a => a
  | n + 1, a => let p := prefixBits n a; p ^^^ (p <<< (2 ^ n))

/-- Adjacent-coordinate XOR commutes with one prefix-doubling stage. -/
private theorem adjacent_prefix (p : BitVec 64) (n : Nat) :
    ((p ^^^ (p <<< n)) <<< 1) ^^^ (p ^^^ (p <<< n)) =
      ((p <<< 1) ^^^ p) ^^^ (((p <<< 1) ^^^ p) <<< n) := by
  simp only [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]
  rw [Nat.add_comm n 1]
  ac_rfl

/-- A doubling stage cancels its two interior shifted copies. -/
private theorem prefix_double (a : BitVec 64) (n : Nat) :
    (a ^^^ (a <<< n)) ^^^ ((a ^^^ (a <<< n)) <<< n) = a ^^^ (a <<< (n + n)) := by
  simp only [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc (a <<< n) (a <<< n), BitVec.xor_self, BitVec.zero_xor]

/-- Each prefix stage inverts the adjacent-coordinate map up to its remaining high shift. -/
private theorem prefixBits_adjacent (n : Nat) (a : BitVec 64) :
    ((prefixBits n a) <<< 1) ^^^ prefixBits n a = a ^^^ (a <<< (2 ^ n)) := by
  induction n with
  | zero => simp only [prefixBits, pow_zero, BitVec.xor_comm]
  | succ n ih =>
    rw [prefixBits, adjacent_prefix, ih, prefix_double, pow_succ, Nat.mul_two]

/-- A prefix XOR reverses the adjacent-coordinate XOR map. -/
private theorem prefixXor_bits (a : BitVec 64) :
    let p := a ^^^ (a <<< 1)
    let p := p ^^^ (p <<< 2)
    let p := p ^^^ (p <<< 4)
    let p := p ^^^ (p <<< 8)
    let p := p ^^^ (p <<< 16)
    let p := p ^^^ (p <<< 32)
    (p <<< 1) ^^^ p = a := by
  change ((prefixBits 6 a) <<< 1) ^^^ prefixBits 6 a = a
  rw [prefixBits_adjacent, BitVec.shiftLeft_eq_zero (by decide), BitVec.xor_zero]

set_option linter.unusedSimpArgs false in
/-- The low-coordinate correction accounts for reduction at the highest bit. -/
private theorem divideXOne_correction (p : BitVec 64) :
    let q := p ^^^ (((0#64) - (p >>> 63)) &&& (9#64))
    (q <<< 1) ^^^ (((0#64) - (q >>> 63)) &&& (0x1b#64)) ^^^ q = (p <<< 1) ^^^ p := by
  dsimp only
  rw [topBit p]
  cases h : p.getLsbD 63 <;> have h' : p[63] = _ := h <;>
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.sub_zero,
      BitVec.zero_and, BitVec.xor_zero]
  all_goals
    rw [topBit]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;>
      simp [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_of_ge, h, h', Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

/-- The prefix and correction implement exact division by X+1. -/
theorem timesXOne_divideXOne (a : Word) :
    Word.add (timesX (divideXOne a)) (divideXOne a) = a := by
  cases a with | mk value =>
  apply congrArg Word.mk
  apply UInt64.eq_of_toBitVec_eq
  have correction := divideXOne_correction (prefixXor value).toBitVec
  have prefixLaw := prefixXor_bits value.toBitVec
  simp only [prefixXor, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat,
    BitVec.shiftLeft_eq', BitVec.ofNat_eq_ofNat, BitVec.toNat_umod, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] at correction
  change (Word.xtime _ ^^^ _).toBitVec = value.toBitVec
  simp only [Word.xtime, divideXOne, prefixXor, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    UInt64.toBitVec_sub, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.ofNat_eq_ofNat, BitVec.toNat_umod,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact correction.trans prefixLaw

/-- The interpolation denominator is nonzero in the base field. -/
theorem interpolationDenominator_ne_zero :
    (Word.mk 2).toField * ((Word.mk 2).toField + 1) ≠ 0 := by
  apply mul_ne_zero
  · intro zero
    have same : (Word.mk 2) = Word.mk 0 := Word.toField_injective zero
    have impossible := congrArg (fun a : Word => a.val.toNat) same
    contradiction
  · intro zero
    have three : (Word.mk 3).toField = (Word.mk 2).toField + 1 := rfl
    have same : (Word.mk 3) = Word.mk 0 := Word.toField_injective (three.trans zero)
    have impossible := congrArg (fun a : Word => a.val.toNat) same
    contradiction

/-- The two bit-linear inverses divide by the exact nonzero interpolation denominator. -/
theorem divideDenominator_toField (a : Word) :
    (divideDenominator a).toField =
      ((Word.mk 2).toField * ((Word.mk 2).toField + 1))⁻¹ * a.toField := by
  have x := congrArg Word.toField (timesX_divideX a)
  have adjacent := congrArg Word.toField (timesXOne_divideXOne (divideX a))
  rw [timesX_toField] at x
  rw [Word.toField_add, timesX_toField] at adjacent
  apply (mul_left_cancel₀ interpolationDenominator_ne_zero)
  rw [← mul_assoc, mul_inv_cancel₀ interpolationDenominator_ne_zero, one_mul]
  change (Word.mk 2).toField * ((Word.mk 2).toField + 1) *
    (divideXOne (divideX a)).toField = _
  calc
    _ = (Word.mk 2).toField *
        ((Word.mk 2).toField * (divideXOne (divideX a)).toField +
          (divideXOne (divideX a)).toField) := by ring
    _ = a.toField := by rw [adjacent, x]

set_option linter.unusedSimpArgs false in
/-- Five-point interpolation gives exactly the retained six-product extension multiplication. -/
theorem extMulFive_eq (a b : WordExt3) : extMulFive a b = WordExt3.mul a b := by
  apply WordExt3.toField_injective
  apply CompPoly.Extension.Ext.ext
  intro i
  have denominator := interpolationDenominator_ne_zero
  have hx := left_ne_zero_of_mul denominator
  have hu := right_ne_zero_of_mul denominator
  generalize ht : (Word.mk 2).toField = t at *
  fin_cases i <;>
    simp only [extMulFive, WordExt3.mul, WordExt3.toField, CompPoly.Extension.Ext.coeff_ofFn,
      Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceEqDiff, ↓reduceIte,
      Word.toField_add, Word.toField_mulMasked, timesX_toField, divideDenominator_toField, ht] <;>
    field_simp [hx, hu] <;>
    ring_nf <;>
    simp only [CharTwo.ofNat_eq_mod (R := BF64)] <;> norm_num

end CompStark.Sumcheck
