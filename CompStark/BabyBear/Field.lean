/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Mont32.BaseField
public import CompPoly.Fields.BabyBear.Fast

/-! # BabyBear as the base field

The fast BabyBear field `BabyBear.Fast.Field`, `p = 15 · 2^27 + 1`, is a `BaseField`
(`Mont32BaseField`) with Plonky3's choices: the multiplicative generator `31` as the coset shift,
and Plonky3's `TWO_ADIC_GENERATORS`, two-adicity `27`.
-/

@[expose] public section
namespace CompStark.BabyBear
open Montgomery.Native32

local notation "F" => _root_.BabyBear.Fast.Field

/-- Plonky3's `TWO_ADIC_GENERATORS` of BabyBear, canonical values. -/
def twoAdicTable : Array Nat := #[0x1, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da,
  0x669d6090, 0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715, 0x11c33e2a,
  0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f, 0x3e9430e8, 0xba067a3, 0x18adc27d,
  0x21fd55bc, 0x4b859b3d, 0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41]

/-- Plonky3's generator of the subgroup of order `2 ^ bits`, `bits ≤ 27`. -/
def twoAdicGen (bits : Nat) : F := ((twoAdicTable.getD bits 0 : Nat) : F)

set_option maxRecDepth 10000 in
/-- The canonical table holds CompPoly's Montgomery generators. -/
theorem twoAdicGen_eq_table : ∀ n : Fin 28,
    twoAdicGen n.val = _root_.BabyBear.Fast.twoAdicGenerators[n.val]'(by
      simp only [_root_.BabyBear.Fast.twoAdicGenerators, List.length_cons, List.length_nil]
      omega) := by
  decide

set_option maxRecDepth 10000 in
/-- Each generator is the square of the next. -/
theorem twoAdicGen_sq_table : ∀ n : Fin 27, twoAdicGen (n.val + 1) ^ 2 = twoAdicGen n.val := by
  decide

/-- Plonky3's generator of order `2 ^ n` is a primitive root of unity. -/
theorem isPrimitiveRoot_twoAdicGen (n : Nat) (hn : n ≤ 27) :
    IsPrimitiveRoot (twoAdicGen n) (2 ^ n) := by
  have h := _root_.BabyBear.isPrimitiveRoot_twoAdicGenerator ⟨n, by
    show n < 27 + 1; omega⟩
  rw [twoAdicGen_eq_table ⟨n, by omega⟩]
  refine IsPrimitiveRoot.of_map_of_injective (f := ringEquiv _root_.BabyBear.fieldSize) ?_
    (RingEquiv.injective _)
  have e : (ringEquiv _root_.BabyBear.fieldSize) (_root_.BabyBear.Fast.twoAdicGenerators[n]'(by
      simp only [_root_.BabyBear.Fast.twoAdicGenerators, List.length_cons, List.length_nil]
      omega)) =
      _root_.BabyBear.twoAdicGenerators[n]'(by
        simp only [_root_.BabyBear.twoAdicGenerators, List.length_cons, List.length_nil]
        omega) := by
    simp only [ringEquiv_apply, _root_.BabyBear.Fast.twoAdicGenerators_eq_map, List.getElem_map,
      _root_.BabyBear.Fast.ofField, toField_ofField]
  rw [e]
  exact h

/-- `31` is not in the two-adic subgroup. -/
theorem thirtyOne_pow_ne_one : (31 : F) ^ 2 ^ 27 ≠ 1 := by
  intro h
  have h' := congrArg FastField.toField h
  rw [toField_npow, toField_one, show FastField.toField (31 : F) = 31 by decide, ← sqIter_eq] at h'
  revert h'
  decide

/-- BabyBear with Plonky3's coset shift `31` and two-adic generators. -/
instance instMont32BaseField : Mont32BaseField _root_.BabyBear.fieldSize where
  twoAdicity := 27
  twoAdicGen := twoAdicGen
  isPrimitiveRoot_twoAdicGen := isPrimitiveRoot_twoAdicGen
  twoAdicGen_succ_sq k hk := twoAdicGen_sq_table ⟨k, hk⟩
  gen := 31
  gen_ne_zero := by decide
  gen_pow_ne_one := thirtyOne_pow_ne_one

@[simp] theorem twoAdicity_eq : twoAdicity F = 27 := rfl

/-- `p = 2013265921 = 15 · 2^27 + 1`. -/
@[simp high] theorem card_eq : Nat.card F = 2013265921 := by
  rw [Nat.card_eq_fintype_card, card_fastField]; rfl

end CompStark.BabyBear
