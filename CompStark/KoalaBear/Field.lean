/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BaseField
public import CompPoly.Fields.KoalaBear.Fast
public import CompPoly.Fields.Montgomery.Native32Bytes

/-! # KoalaBear as the base field

The fast KoalaBear field `KoalaBear.Fast.Field`, `p = 127 · 2^24 + 1`, is a `BaseField` with
Plonky3's choices: the multiplicative generator `3` as the coset shift, and Plonky3's
`TWO_ADIC_GENERATORS`, two-adicity `24`.
-/

@[expose] public section
namespace CompStark.KoalaBear
open Montgomery.Native32

local notation "F" => _root_.KoalaBear.Fast.Field

/-- Plonky3's `TWO_ADIC_GENERATORS` of KoalaBear, canonical values. -/
def twoAdicTable : Array Nat := #[0x1, 0x7f000000, 0x7e010002, 0x6832fe4a, 0x8dbd69c, 0xa28f031,
  0x5c4a5b99, 0x29b75a80, 0x17668b8a, 0x27ad539b, 0x334d48c7, 0x7744959c, 0x768fc6fa, 0x303964b2,
  0x3e687d4d, 0x45a60e61, 0x6e2f4d7a, 0x163bd499, 0x6c4a8a45, 0x143ef899, 0x514ddcad, 0x484ef19b,
  0x205d63c3, 0x68e7dd49, 0x6ac49f88]

/-- Plonky3's generator of the subgroup of order `2 ^ bits`, `bits ≤ 24`. -/
def twoAdicGen (bits : Nat) : F := ((twoAdicTable.getD bits 0 : Nat) : F)

set_option maxRecDepth 10000 in
/-- The canonical table holds CompPoly's Montgomery generators. -/
theorem twoAdicGen_eq_table : ∀ n : Fin 25,
    twoAdicGen n.val = _root_.KoalaBear.Fast.twoAdicGenerators[n.val]'(by
      simp only [_root_.KoalaBear.Fast.twoAdicGenerators, List.length_cons, List.length_nil]
      omega) := by
  decide

set_option maxRecDepth 10000 in
/-- Each generator is the square of the next. -/
theorem twoAdicGen_sq_table : ∀ n : Fin 24, twoAdicGen (n.val + 1) ^ 2 = twoAdicGen n.val := by
  decide

/-- Plonky3's generator of order `2 ^ n` is a primitive root of unity. -/
theorem isPrimitiveRoot_twoAdicGen (n : Nat) (hn : n ≤ 24) :
    IsPrimitiveRoot (twoAdicGen n) (2 ^ n) := by
  have h := _root_.KoalaBear.isPrimitiveRoot_twoAdicGenerator ⟨n, by
    show n < 24 + 1; omega⟩
  rw [twoAdicGen_eq_table ⟨n, by omega⟩]
  refine IsPrimitiveRoot.of_map_of_injective (f := ringEquiv _root_.KoalaBear.fieldSize) ?_
    (RingEquiv.injective _)
  have e : (ringEquiv _root_.KoalaBear.fieldSize) (_root_.KoalaBear.Fast.twoAdicGenerators[n]'(by
      simp only [_root_.KoalaBear.Fast.twoAdicGenerators, List.length_cons, List.length_nil]
      omega)) =
      _root_.KoalaBear.twoAdicGenerators[n]'(by
        simp only [_root_.KoalaBear.twoAdicGenerators, List.length_cons, List.length_nil]
        omega) := by
    simp only [ringEquiv_apply, _root_.KoalaBear.Fast.twoAdicGenerators_eq_map, List.getElem_map,
      _root_.KoalaBear.Fast.ofField, toField_ofField]
  rw [e]
  exact h

/-- `x ^ 2 ^ k` by squaring. -/
def sqIter {K : Type} [Mul K] (x : K) : Nat → K
  | 0 => x
  | k + 1 => sqIter (x * x) k

theorem sqIter_eq {K : Type} [Monoid K] (x : K) : ∀ k, sqIter x k = x ^ 2 ^ k
  | 0 => (pow_one x).symm
  | k + 1 => by rw [sqIter, sqIter_eq _ k, ← sq, ← pow_mul, pow_succ']

/-- `3` is not in the two-adic subgroup. -/
theorem three_pow_ne_one : (3 : F) ^ 2 ^ 24 ≠ 1 := by
  intro h
  have h' := congrArg FastField.toField h
  rw [toField_npow, toField_one, show FastField.toField (3 : F) = 3 by decide, ← sqIter_eq] at h'
  revert h'
  decide

/-- KoalaBear with Plonky3's coset shift `3` and two-adic generators. -/
instance instBaseField : BaseField F where
  toField := inferInstance
  toFintype := inferInstance
  two_ne_zero := NonBinaryField.char_neq_2
  twoAdicity := 24
  twoAdicGen := twoAdicGen
  isPrimitiveRoot_twoAdicGen := isPrimitiveRoot_twoAdicGen
  twoAdicGen_succ_sq k hk := twoAdicGen_sq_table ⟨k, hk⟩
  gen := 3
  gen_ne_zero := by decide
  gen_pow_ne_one := three_pow_ne_one

@[simp] theorem twoAdicity_eq : twoAdicity F = 24 := rfl

/-- `p = 2130706433 = 127 · 2^24 + 1`, for the base field's `Fintype`. -/
theorem card_eq : @Fintype.card F BaseField.toFintype = 2130706433 := card_fastField

/-- `omega` with KoalaBear's two-adicity unfolded to `24`. -/
macro "omega24" : tactic =>
  `(tactic| ((try simp only [CompStark.KoalaBear.twoAdicity_eq] at *); omega))

end CompStark.KoalaBear
