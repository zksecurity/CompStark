/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BaseField
public import CompPoly.Fields.Montgomery.Native32Field
public import CompPoly.Fields.Montgomery.Native32Bytes
public import Mathlib.Data.Nat.Prime.Basic

/-! # Fast Montgomery fields as base fields

CompPoly's fast field `FastField p`, a 32-bit Montgomery field for any prime `p` with a
`Mont32Field p` instance, is a `BaseField` once the choices of the STARK's domains are made:
`Mont32BaseField p` holds the two-adicity, the two-adic generators and the coset shift, with their
proofs. The field structure is CompPoly's own (`instField`), so CompPoly's fast extensions over
`FastField p` are extensions of this base field. The two-adicity is at most 29
(`Mont32BaseField.twoAdicity_le_29`), so the domains fit 32-bit word indices.
-/

@[expose] public section
namespace CompStark
open Montgomery.Native32

/-- The domain data of a fast Montgomery field: the two-adicity, a generator of order `2 ^ k` for
every `k ≤ twoAdicity`, each the square of the next, and the coset shift of the evaluation
domains, outside the two-adic subgroup. -/
class Mont32BaseField (p : ℕ) [Mont32Field p] where
  /-- The two-adicity: subgroups of order `2 ^ k` for `k ≤ twoAdicity`. -/
  twoAdicity : ℕ
  /-- A generator of the subgroup of order `2 ^ k`, for `k ≤ twoAdicity`. -/
  twoAdicGen : ℕ → FastField p
  isPrimitiveRoot_twoAdicGen (k : ℕ) : k ≤ twoAdicity → IsPrimitiveRoot (twoAdicGen k) (2 ^ k)
  twoAdicGen_succ_sq (k : ℕ) : k < twoAdicity → twoAdicGen (k + 1) ^ 2 = twoAdicGen k
  /-- The shift of the evaluation domains. -/
  gen : FastField p
  gen_ne_zero : gen ≠ 0
  gen_pow_ne_one : gen ^ 2 ^ twoAdicity ≠ 1

/-- A fast Montgomery field with its domain data is a base field. -/
instance Mont32BaseField.instBaseField (p : ℕ) [Mont32Field p] [D : Mont32BaseField p] :
    BaseField (FastField p) where
  toField := instField
  card_prime := by rw [natCard_fastField]; exact Mont32Field.prime
  two_ne_zero := NonBinaryField.char_neq_2
  twoAdicity := D.twoAdicity
  twoAdicGen := D.twoAdicGen
  isPrimitiveRoot_twoAdicGen := D.isPrimitiveRoot_twoAdicGen
  twoAdicGen_succ_sq := D.twoAdicGen_succ_sq
  gen := D.gen
  gen_ne_zero := D.gen_ne_zero
  gen_pow_ne_one := D.gen_pow_ne_one

/-- The two-adicity of a Montgomery field is at most 29: `2 ^ 30` divides no `p - 1` with
`p < 2 ^ 31` prime, as `2 ^ 30 + 1 = 5 · 214748365`. -/
theorem Mont32BaseField.twoAdicity_le_29 (p : ℕ) [Mont32Field p]
    [Mont32BaseField p] : BaseField.twoAdicity (FastField p) ≤ 29 := by
  by_contra h
  have hdvd := BaseField.two_pow_dvd_card_sub_one_of_le (F := FastField p)
    (k := 30) (by omega)
  have hc : Nat.card (FastField p) = p := by
    rw [Nat.card_eq_fintype_card, card_fastField]
  rw [hc] at hdvd
  have hlt := Mont32Field.modulus_lt_two_pow_31 (modulus := p)
  have h2 := Mont32Field.two_lt_modulus (modulus := p)
  obtain ⟨m, hm⟩ := hdvd
  have hp : p = 5 * 214748365 := by
    have : m = 1 := by omega
    subst this
    omega
  have hprime := Mont32Field.prime (modulus := p)
  rw [hp] at hprime
  exact Nat.not_prime_mul (by decide) (by decide) hprime

/-- `x ^ 2 ^ k` by squaring, for checking the shift's order by `decide`. -/
def sqIter {K : Type} [Mul K] (x : K) : ℕ → K
  | 0 => x
  | k + 1 => sqIter (x * x) k

theorem sqIter_eq {K : Type} [Monoid K] (x : K) : ∀ k, sqIter x k = x ^ 2 ^ k
  | 0 => (pow_one x).symm
  | k + 1 => by rw [sqIter, sqIter_eq _ k, ← sq, ← pow_mul, pow_succ']

end CompStark
