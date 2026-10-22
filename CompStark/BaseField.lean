/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Data.Classes.CanonicalNat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.ZMod.ValMinAbs

/-! # The base field

The STARK runs over a prime field `F` of odd characteristic, the base field. `BaseField F` is what
the verifier and its analysis use of it, on the executable type itself:

* the field operations, decidable equality, and finiteness as a proposition: no executable code
  enumerates the elements, and the analysis counts them by `Nat.card F`;
* a prime number `p = |F|` of elements, so `F` is `ℤ/p` and its characteristic is `p`
  (`ringChar_eq_card`);
* the canonical value `CanonicalNat.toNat : F → ℕ`, a bijection onto `[0, p)` for `p = |F|`, of
  which `sampleBits` keeps the low bits;
* the shift `gen` of the evaluation domains, a nonzero element outside the two-adic subgroup;
* the two-adic generators `twoAdicGen k` of order `2 ^ k` for `k ≤ twoAdicity`, each the square of
  the next.

Domains of size `2 ^ k` exist for `k ≤ twoAdicity`, so `2 ^ twoAdicity` divides `p - 1`
(`two_pow_dvd_card_sub_one`). An element stands for an integer of magnitude below `p / 2`
(`intValue`).
-/

@[expose] public section
namespace CompStark

/-- A prime field of odd characteristic with a canonical value per element, a coset shift and
two-adic generators: the base field of the STARK. -/
class BaseField (F : Type) extends Field F where
  [finite : Finite F]
  [decEq : DecidableEq F]
  [canonicalNat : CompPoly.CanonicalNat F]
  /-- The number of elements is prime: `F` is a prime field. -/
  card_prime : (Nat.card F).Prime
  /-- The characteristic is odd. -/
  two_ne_zero : (2 : F) ≠ 0
  /-- The two-adicity: subgroups of order `2 ^ k` for `k ≤ twoAdicity`. -/
  twoAdicity : ℕ
  /-- A generator of the subgroup of order `2 ^ k`, for `k ≤ twoAdicity`. -/
  twoAdicGen : ℕ → F
  isPrimitiveRoot_twoAdicGen (k : ℕ) : k ≤ twoAdicity → IsPrimitiveRoot (twoAdicGen k) (2 ^ k)
  /-- Each generator is the square of the next. -/
  twoAdicGen_succ_sq (k : ℕ) : k < twoAdicity → twoAdicGen (k + 1) ^ 2 = twoAdicGen k
  /-- The shift of the evaluation domains. -/
  gen : F
  gen_ne_zero : gen ≠ 0
  /-- The shifted domains are disjoint from the two-adic subgroups. -/
  gen_pow_ne_one : gen ^ 2 ^ twoAdicity ≠ 1

namespace BaseField

attribute [instance] finite
attribute [instance_reducible, instance] decEq canonicalNat

/-- The elements, for the analysis; noncomputable, so no executable code enumerates them. -/
noncomputable instance (priority := low) toFintype {F : Type} [BaseField F] : Fintype F :=
  Fintype.ofFinite F

variable {F : Type} [BaseField F]

/-- The characteristic is the number of elements `p`. -/
theorem ringChar_eq_card : ringChar F = Nat.card F := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card] at hcard
  have h := card_prime (F := F)
  rw [hcard] at h
  rw [hcard, ((Nat.Prime.pow_eq_iff h).mp rfl).2, pow_one]

/-- The integer of magnitude below `p / 2` that `x` stands for, `p = |F|`. -/
noncomputable def intValue (x : F) : ℤ :=
  ((ZMod.ringEquiv F (n := ringChar F)
    (by rw [← Nat.card_eq_fintype_card, ringChar_eq_card])).symm x).valMinAbs

/-- `ω_(n + b) ^ 2 ^ b = ω_n`. -/
theorem twoAdicGen_pow (n b : ℕ) (h : n + b ≤ twoAdicity F) :
    twoAdicGen (F := F) (n + b) ^ 2 ^ b = twoAdicGen n := by
  induction b with
  | zero => rw [Nat.add_zero, pow_zero, pow_one]
  | succ b ih =>
    rw [pow_succ', pow_mul, ← Nat.add_assoc, twoAdicGen_succ_sq _ (by omega), ih (by omega)]

theorem twoAdicGen_ne_zero (k : ℕ) (hk : k ≤ twoAdicity F) : twoAdicGen (F := F) k ≠ 0 :=
  (isPrimitiveRoot_twoAdicGen k hk).ne_zero (Nat.two_pow_pos k).ne'

/-- `2 ^ twoAdicity` divides `p - 1`: the two-adic subgroup is a subgroup of the units. -/
theorem two_pow_dvd_card_sub_one : 2 ^ twoAdicity F ∣ Nat.card F - 1 := by
  have h := isPrimitiveRoot_twoAdicGen (F := F) (twoAdicity F) le_rfl
  have hu := h.isUnit (Nat.two_pow_pos _).ne'
  rw [Nat.card_eq_fintype_card, ← Fintype.card_units, h.eq_orderOf, ← hu.unit_spec, orderOf_units]
  exact orderOf_dvd_card

/-- `2 ^ k` divides `p - 1` for `k ≤ twoAdicity`. -/
theorem two_pow_dvd_card_sub_one_of_le {k : ℕ} (hk : k ≤ twoAdicity F) :
    2 ^ k ∣ Nat.card F - 1 :=
  (Nat.pow_dvd_pow 2 hk).trans two_pow_dvd_card_sub_one

end BaseField

export BaseField (twoAdicity twoAdicGen gen intValue)

end CompStark
