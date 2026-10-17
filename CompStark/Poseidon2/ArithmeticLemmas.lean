/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Arithmetic
public import CompPoly.Fields.KoalaBear.Fast
import CompPoly.Fields.Montgomery.Basic

/-! # Field semantics of the packed word arithmetic -/

@[expose] public section
namespace CompStark.Poseidon2
open Montgomery.Native32 Montgomery.Native32.FastField

local notation "F" => KoalaBear.Fast.Field

/-- `1 / 2` in the Montgomery field, named so that statements share one term. -/
def half : F := 2⁻¹

/-- Halving a canonical Montgomery word halves the field element. -/
theorem halve_val (x : F) : halve x.val = (x * half).val := by
  unfold half
  have hx : x.val.toNat < 2130706433 := x.property
  have hp : KoalaBear.fieldSize = 2130706433 := rfl
  -- The word of the half, as a natural number.
  have hh : (halve x.val).toNat = x.val.toNat / 2 + x.val.toNat % 2 * 1065353217 := by
    simp only [halve, UInt32.toNat_add, UInt32.toNat_shiftRight, UInt32.toNat_mul,
      UInt32.toNat_and, Nat.and_one_is_mod, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow,
      Nat.reduceMod, Nat.reducePow]
    omega
  have hlt : (halve x.val).toNat < 2130706433 := by rw [hh]; omega
  apply UInt32.toNat_inj.mp
  apply Montgomery.natCast_inj_of_lt (p := KoalaBear.fieldSize) _ (by exact hlt)
    (x * 2⁻¹).property
  -- Both words cast to `x · 2⁻¹ · 2 ^ 32`.
  have hc : ((halve x.val).toNat : ZMod KoalaBear.fieldSize) * 2 = (x.val.toNat : ZMod _) := by
    rw [hh]
    have : (x.val.toNat / 2 + x.val.toNat % 2 * 1065353217) * 2 =
        x.val.toNat + x.val.toNat % 2 * 2130706433 := by omega
    have e : (((x.val.toNat / 2 + x.val.toNat % 2 * 1065353217 : Nat) : ZMod KoalaBear.fieldSize))
        * 2 = (((x.val.toNat / 2 + x.val.toNat % 2 * 1065353217) * 2 : Nat) : ZMod _) := by
      push_cast; ring
    rw [e, this, Nat.cast_add, Nat.cast_mul,
      show ((2130706433 : Nat) : ZMod KoalaBear.fieldSize) = 0 from ZMod.natCast_self _,
      mul_zero, add_zero]
  have h2 : (2 : ZMod KoalaBear.fieldSize) ≠ 0 := Mont32Field.two_ne_zero
  have h2' : toField (2 : F) = 2 := by
    simpa using toField_natCast (modulus := KoalaBear.fieldSize) 2
  have hhalf : ((halve x.val).toNat : ZMod KoalaBear.fieldSize) = (x.val.toNat : ZMod _) * 2⁻¹ := by
    rw [← hc, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  rw [val_toNat_cast (x * 2⁻¹), toField_mul, toField_inv, h2', hhalf, val_toNat_cast x]
  ring

/-- The word of `x · 2 ^ (-n)`: canonical, and `2 ^ n` times it is `x` modulo `p`. -/
theorem mulInvPow2_toNat (n : Nat) (hn : n ≤ 24) (w : UInt32) (hw : w.toNat < 2130706433) :
    (mulInvPow2 n.toUInt32 w).toNat < 2130706433 ∧
      ((mulInvPow2 n.toUInt32 w).toNat * 2 ^ n) % 2130706433 = w.toNat % 2130706433 := by
  have h32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  have hnu : n.toUInt32.toNat = n := UInt32.toNat_ofNat_of_lt' (by unfold UInt32.size; omega)
  have hq : 2 ^ n ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hn
  have hqQ : 2 ^ n * 2 ^ (24 - n) = 2 ^ 24 := by rw [← Nat.pow_add]; congr 1; omega
  have hq0 : 0 < 2 ^ n := Nat.two_pow_pos n
  generalize ha : w.toNat = a at hw
  -- The parts of the word.
  have hpow : (1 <<< n.toUInt32 : UInt32).toNat = 2 ^ n := by
    have : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [UInt32.toNat_shiftLeft, hnu, UInt32.reduceToNat, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (show n < 32 by omega)]
    omega
  have hK : (127 <<< (24 - n.toUInt32) : UInt32).toNat = 127 * 2 ^ (24 - n) := by
    have h24 : (24 - n.toUInt32 : UInt32).toNat = 24 - n := by
      simp only [UInt32.toNat_sub, hnu, UInt32.reduceToNat]
      omega
    have : 127 * 2 ^ (24 - n) < 2 ^ 31 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 24 - n ≤ 24 by omega)
      omega
    simp only [UInt32.toNat_shiftLeft, h24, UInt32.reduceToNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show 24 - n < 32 by omega)]
    omega
  set q := 2 ^ n
  set Q := 2 ^ (24 - n)
  have hlo : a % q < q := Nat.mod_lt _ hq0
  have hdm : q * (a / q) + a % q = a := Nat.div_add_mod a q
  -- `T = 127 · Q · lo` is below `127 · 2 ^ 24 = p - 1`, and `T · q = (p - 1) · lo`.
  have hQ0 : 0 < Q := Nat.two_pow_pos _
  have hqQ' : q * (127 * Q) = 2130706432 := by
    rw [show q * (127 * Q) = 127 * (q * Q) by ring, hqQ]
    rfl
  have hT : a % q * (127 * Q) < 2130706432 := by
    have := Nat.mul_le_mul_right (127 * Q) (show a % q + 1 ≤ q by omega)
    rw [Nat.add_mul, Nat.one_mul, hqQ'] at this
    omega
  have hTq : a % q * (127 * Q) * q = 2130706432 * (a % q) := by
    rw [show a % q * (127 * Q) * q = q * (127 * Q) * (a % q) by ring, hqQ']
  have hD : (w / (1 <<< n.toUInt32)).toNat = a / q := by rw [UInt32.toNat_div, hpow, ha]
  have hM : (w % (1 <<< n.toUInt32) * (127 <<< (24 - n.toUInt32))).toNat = a % q * (127 * Q) := by
    rw [UInt32.toNat_mul, UInt32.toNat_mod, hpow, hK, ha, Nat.mod_eq_of_lt (by omega)]
  have hhi : a / q < 2130706433 := lt_of_le_of_lt (Nat.div_le_self a q) hw
  unfold mulInvPow2
  dsimp only
  generalize hd : w / (1 <<< n.toUInt32) - w % (1 <<< n.toUInt32) * (127 <<< (24 - n.toUInt32)) = d
  have hdv : d.toNat = (4294967296 - a % q * (127 * Q) + a / q) % 4294967296 := by
    rw [← hd, UInt32.toNat_sub, hD, hM]
  have he : (d + 2130706433).toNat = (d.toNat + 2130706433) % 4294967296 := by
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
  by_cases hle : a % q * (127 * Q) ≤ a / q
  · -- No wrap: the result is `hi - T`.
    have hd' : d.toNat = a / q - a % q * (127 * Q) := by rw [hdv]; omega
    have hne : ¬ d + 2130706433 < d := by
      rw [UInt32.lt_iff_toNat_lt, he, hd']; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne), hd']
    refine ⟨by omega, ?_⟩
    have hle' := Nat.mul_le_mul_right q hle
    rw [hTq, Nat.mul_comm (a / q) q] at hle'
    have : (a / q - a % q * (127 * Q)) * q + 2130706433 * (a % q) = a := by
      rw [Nat.sub_mul, hTq, Nat.mul_comm (a / q) q]; omega
    omega
  · -- Wrap: the result is `hi + p - T`.
    have hd' : d.toNat = 4294967296 - a % q * (127 * Q) + a / q := by rw [hdv]; omega
    have hlt : d + 2130706433 < d := by
      rw [UInt32.lt_iff_toNat_lt, he, hd']; omega
    have he' : (d + 2130706433).toNat = a / q + 2130706433 - a % q * (127 * Q) := by
      rw [he, hd']; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), he']
    refine ⟨by omega, ?_⟩
    have h1 := Nat.mul_le_mul_left 2130706432 (Nat.le_of_lt hlo)
    have : (a / q + 2130706433 - a % q * (127 * Q)) * q + 2130706433 * (a % q) =
        a + 2130706433 * q := by
      rw [Nat.sub_mul, Nat.add_mul, hTq, Nat.mul_comm (a / q) q]
      omega
    omega

/-- `2 ^ (-n)` in the Montgomery field. -/
def invPow2 (n : Nat) : F := (2 ^ n)⁻¹

/-- Multiplying a canonical Montgomery word by `2 ^ (-n)` with `mulInvPow2` multiplies the field
element. -/
theorem mulInvPow2_val (k : UInt32) (hk : k.toNat ≤ 24) (x : F) :
    mulInvPow2 k x.val = (x * invPow2 k.toNat).val := by
  have hx : x.val.toNat < 2130706433 := x.property
  have hkk : k.toNat.toUInt32 = k := UInt32.ofNat_toNat
  obtain ⟨hlt, hmod⟩ := mulInvPow2_toNat k.toNat hk x.val hx
  rw [hkk] at hlt hmod
  apply UInt32.toNat_inj.mp
  apply Montgomery.natCast_inj_of_lt (p := KoalaBear.fieldSize) _ (by exact hlt)
    (x * invPow2 k.toNat).property
  have h2 : ((2 : ZMod KoalaBear.fieldSize) ^ k.toNat) ≠ 0 := pow_ne_zero _ Mont32Field.two_ne_zero
  have hc : ((mulInvPow2 k x.val).toNat : ZMod KoalaBear.fieldSize) * 2 ^ k.toNat =
      (x.val.toNat : ZMod _) := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ KoalaBear.fieldSize).mpr hmod
    push_cast at this
    exact this
  have h2' : toField ((2 : F) ^ k.toNat) = 2 ^ k.toNat := by
    rw [toField_npow]
    congr 1
  have hw : ((mulInvPow2 k x.val).toNat : ZMod KoalaBear.fieldSize) =
      (x.val.toNat : ZMod _) * (2 ^ k.toNat)⁻¹ := by
    rw [← hc, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  rw [invPow2, val_toNat_cast (x * ((2 : F) ^ k.toNat)⁻¹), toField_mul, toField_inv, h2', hw,
    val_toNat_cast x]
  ring

end CompStark.Poseidon2
