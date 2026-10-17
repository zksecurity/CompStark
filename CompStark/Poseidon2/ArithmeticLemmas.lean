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

end CompStark.Poseidon2
