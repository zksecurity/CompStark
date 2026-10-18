/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ExtWords

/-! # Inverses by the norm

`invDenoms` inverts `z - x` for base points `x` through the norm: with `σₖ` the automorphisms
`X ↦ ζᵏ X`, `ζ` of order 4, `(z - x) · ∏_{k ≠ 0} (σₖ z - x)` is the norm `N(x)`, a quartic in `x`
with base coefficients, and `∏_{k ≠ 0} (σₖ z - x)` is a cubic `Q(x)` with extension coefficients
(`mul_cubic`). For `z` outside the base field no factor vanishes, so `N(x) ≠ 0`
(`norm_ne_zero`).
-/

@[expose] public section
namespace CompStark.Stark.Norm
open KoalaBear.Fast

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

theorem mulAdd4_eq (a b c d e f g k : F) :
    Montgomery.Native32.mulAdd4 a b c d e f g k = a * b + c * d + e * f + g * k := by
  apply Montgomery.Native32.toField_injective
  rw [Montgomery.Native32.toField_mulAdd4, Montgomery.Native32.toField_add,
    Montgomery.Native32.toField_add, Montgomery.Native32.toField_add,
    Montgomery.Native32.toField_mul, Montgomery.Native32.toField_mul,
    Montgomery.Native32.toField_mul, Montgomery.Native32.toField_mul]

theorem ext {a b : EF} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3) : a = b := by
  cases a; cases b; simp only at h0 h1 h2 h3; rw [h0, h1, h2, h3]

theorem mul_c0 (a b : EF) :
    (a * b).c0 = a.c0 * b.c0 + 3 * (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1) := by
  show (Ext4.mul a b).c0 = _
  simp only [Ext4.mul, mulAdd4_eq, Ext4.triple]; ring

theorem mul_c1 (a b : EF) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + 3 * (a.c2 * b.c3 + a.c3 * b.c2) := by
  show (Ext4.mul a b).c1 = _
  simp only [Ext4.mul, mulAdd4_eq, Ext4.triple]; ring

theorem mul_c2 (a b : EF) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + 3 * (a.c3 * b.c3) := by
  show (Ext4.mul a b).c2 = _
  simp only [Ext4.mul, mulAdd4_eq, Ext4.triple]; ring

theorem mul_c3 (a b : EF) :
    (a * b).c3 = a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0 := by
  show (Ext4.mul a b).c3 = _
  simp only [Ext4.mul, mulAdd4_eq]

@[simp] theorem add_c0 (a b : EF) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : EF) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : EF) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem add_c3 (a b : EF) : (a + b).c3 = a.c3 + b.c3 := rfl
@[simp] theorem sub_c0 (a b : EF) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : EF) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : EF) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem sub_c3 (a b : EF) : (a - b).c3 = a.c3 - b.c3 := rfl

/-- `ζ`, of order 4. -/
abbrev zeta : F := twoAdicGen 2

theorem zeta_sq : zeta * zeta = -1 := by decide

/-- `powF` is exponentiation. -/
theorem powF_eq (x : F) (n : Nat) : powF x n = x ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases n with
    | zero => rw [powF, pow_zero]
    | succ n =>
      rw [powF, ih _ (by omega)]
      have hn := Nat.div_add_mod (n + 1) 2
      split
      · rename_i h
        rw [← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · rw [← pow_two, ← pow_mul]
        congr 1
        omega

theorem zeta_pow_two : zeta ^ 2 = -1 := by rw [pow_two, zeta_sq]

theorem powF_zeta_1 : powF zeta 1 = zeta := by rw [powF_eq, pow_one]
theorem powF_zeta_2 : powF zeta 2 = -1 := by rw [powF_eq, zeta_pow_two]
theorem powF_zeta_3 : powF zeta 3 = -zeta := by
  rw [powF_eq, show zeta ^ 3 = zeta ^ 2 * zeta by ring, zeta_pow_two, neg_one_mul]
theorem powF_zeta_4 : powF zeta 4 = 1 := by
  rw [powF_eq, show zeta ^ 4 = (zeta ^ 2) ^ 2 by ring, zeta_pow_two]; norm_num
theorem powF_zeta_6 : powF zeta 6 = -1 := by
  rw [powF_eq, show zeta ^ 6 = (zeta ^ 2) ^ 3 by ring, zeta_pow_two]; norm_num
theorem powF_zeta_9 : powF zeta 9 = zeta := by
  rw [powF_eq, show zeta ^ 9 = (zeta ^ 2) ^ 4 * zeta by ring, zeta_pow_two]; norm_num

/-- `σₖ z`, `X ↦ ζᵏ X`. -/
def conj (z : EF) (k : Nat) : EF :=
  ⟨z.c0, powF zeta k * z.c1, powF zeta (2 * k) * z.c2, powF zeta (3 * k) * z.c3⟩

/-- The elementary symmetric functions of `σ₁ z, σ₂ z, σ₃ z`. -/
def e1 (z : EF) : EF := conj z 1 + conj z 2 + conj z 3
def e2 (z : EF) : EF := conj z 1 * conj z 2 + conj z 1 * conj z 3 + conj z 2 * conj z 3
def e3 (z : EF) : EF := conj z 1 * conj z 2 * conj z 3

/-- The norm of `z - x`, `∏ₖ (σₖ z - x)`. -/
def norm (z : EF) (x : F) : F :=
  x ^ 4 - (z + e1 z).c0 * x ^ 3 + (e2 z + z * e1 z).c0 * x ^ 2 - (e3 z + z * e2 z).c0 * x +
    (z * e3 z).c0

/-- `∏_{k ≠ 0} (σₖ z - x) = -x³ + e₁x² - e₂x + e₃`. -/
def cubic (z : EF) (x : F) : EF :=
  ⟨-x ^ 3 + (e1 z).c0 * x ^ 2 - (e2 z).c0 * x + (e3 z).c0,
    (e1 z).c1 * x ^ 2 - (e2 z).c1 * x + (e3 z).c1,
    (e1 z).c2 * x ^ 2 - (e2 z).c2 * x + (e3 z).c2,
    (e1 z).c3 * x ^ 2 - (e2 z).c3 * x + (e3 z).c3⟩

theorem mul_cubic (z : EF) (x : F) : (z - Ext4.ofBase x) * cubic z x = Ext4.ofBase (norm z x) := by
  obtain ⟨z0, z1, z2, z3⟩ := z
  apply ext <;>
    simp only [mul_c0, mul_c1, mul_c2, mul_c3, add_c0, add_c1, add_c2, add_c3, sub_c0, sub_c1,
      sub_c2, sub_c3, cubic, norm, e1, e2, e3, conj, Ext4.ofBase, Nat.reduceMul, powF_zeta_1,
      powF_zeta_2, powF_zeta_3, powF_zeta_4, powF_zeta_6, powF_zeta_9]
  · ring
  · ring
  · linear_combination (-x ^ 2 * z1 ^ 2 - 3 * x ^ 2 * z3 ^ 2 + 2 * x * z0 * z1 ^ 2 +
      6 * x * z0 * z3 ^ 2 - 12 * x * z1 * z2 * z3 - z0 ^ 2 * z1 ^ 2 - 3 * z0 ^ 2 * z3 ^ 2 +
      12 * z0 * z1 * z2 * z3 - 3 * z1 ^ 2 * z2 ^ 2 - 9 * z2 ^ 2 * z3 ^ 2) * zeta_sq
  · ring

theorem cubic_eq_prod (z : EF) (x : F) : cubic z x =
    (conj z 1 - Ext4.ofBase x) * (conj z 2 - Ext4.ofBase x) * (conj z 3 - Ext4.ofBase x) := by
  obtain ⟨z0, z1, z2, z3⟩ := z
  apply ext <;>
    simp only [mul_c0, mul_c1, mul_c2, mul_c3, add_c0, add_c1, add_c2, add_c3, sub_c0, sub_c1,
      sub_c2, sub_c3, cubic, e1, e2, e3, conj, Ext4.ofBase, Nat.reduceMul, powF_zeta_1,
      powF_zeta_2, powF_zeta_3, powF_zeta_4, powF_zeta_6, powF_zeta_9] <;> ring

theorem zeta_ne_zero : zeta ≠ 0 := fun h ↦ by
  have := zeta_sq
  rw [h, mul_zero] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem toSpec_ne_zero {a : EF} (h : a ≠ 0) : Ext4.toSpec a ≠ 0 := fun h' ↦
  h (Ext4.toSpec_injective (h'.trans Ext4.toSpec_zero.symm))

/-- For `z` outside the base field, the norm of `z - x` is not zero. -/
theorem norm_ne_zero {z : EF} (hz : z.c1 ≠ 0 ∨ z.c2 ≠ 0 ∨ z.c3 ≠ 0) (x : F) : norm z x ≠ 0 := by
  have hconj (k : Nat) (hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) : conj z k - Ext4.ofBase x ≠ 0 := by
    intro h0
    have h1 := congrArg Ext4.c1 h0
    have h2 := congrArg Ext4.c2 h0
    have h3 := congrArg Ext4.c3 h0
    simp only [sub_c1, sub_c2, sub_c3, conj, Ext4.ofBase, sub_zero] at h1 h2 h3
    have hp (n : Nat) (hn : n ∈ [0, 1, 2, 3, 4, 6, 9]) : powF zeta n ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [powF_eq, pow_zero]; exact one_ne_zero
      · rw [powF_zeta_1]; exact zeta_ne_zero
      · rw [powF_zeta_2]; exact neg_ne_zero.mpr one_ne_zero
      · rw [powF_zeta_3]; exact neg_ne_zero.mpr zeta_ne_zero
      · rw [powF_zeta_4]; exact one_ne_zero
      · rw [powF_zeta_6]; exact neg_ne_zero.mpr one_ne_zero
      · rw [powF_zeta_9]; exact zeta_ne_zero
    have := hp k (by rcases hk with rfl | rfl | rfl | rfl <;> decide)
    have := hp (2 * k) (by rcases hk with rfl | rfl | rfl | rfl <;> decide)
    have := hp (3 * k) (by rcases hk with rfl | rfl | rfl | rfl <;> decide)
    rcases hz with h | h | h
    · exact h ((mul_eq_zero.mp h1).resolve_left ‹powF zeta k ≠ 0›)
    · exact h ((mul_eq_zero.mp h2).resolve_left ‹powF zeta (2 * k) ≠ 0›)
    · exact h ((mul_eq_zero.mp h3).resolve_left ‹powF zeta (3 * k) ≠ 0›)
  have h0 : z - Ext4.ofBase x ≠ 0 := by
    have := hconj 0 (Or.inl rfl)
    simp only [conj, Nat.mul_zero, powF_eq, pow_zero, one_mul] at this
    exact this
  intro hN
  have e := congrArg Ext4.toSpec (mul_cubic z x)
  rw [hN, cubic_eq_prod, Ext4.toSpec_mul, Ext4.toSpec_mul, Ext4.toSpec_mul] at e
  have hzero : Ext4.toSpec (Ext4.ofBase 0) = 0 := by
    rw [show Ext4.ofBase 0 = 0 from rfl, Ext4.toSpec_zero]
  rw [hzero] at e
  rcases mul_eq_zero.mp e with e | e
  · exact toSpec_ne_zero h0 e
  · rcases mul_eq_zero.mp e with e | e
    · rcases mul_eq_zero.mp e with e | e
      · exact toSpec_ne_zero (hconj 1 (by decide)) e
      · exact toSpec_ne_zero (hconj 2 (by decide)) e
    · exact toSpec_ne_zero (hconj 3 (by decide)) e

theorem smul_eq_ofBase_mul (x : F) (a : EF) : Ext4.smul x a = Ext4.ofBase x * a := by
  apply ext <;> simp only [Ext4.smul, Ext4.ofBase, mul_c0, mul_c1, mul_c2, mul_c3] <;> ring

/-- **The norm trick.** For `z` outside the base field, `1 / (z - x)` is the cubic over the
norm. -/
theorem inv_eq {z : EF} (hz : z.c1 ≠ 0 ∨ z.c2 ≠ 0 ∨ z.c3 ≠ 0) (x : F) :
    (z - Ext4.ofBase x)⁻¹ = Ext4.smul (norm z x)⁻¹ (cubic z x) := by
  have hN := norm_ne_zero hz x
  have hinv : Ext4.ofBase (norm z x) * Ext4.ofBase (norm z x)⁻¹ = 1 := by
    have h1 : (1 : EF).c1 = 0 := rfl
    have h2 : (1 : EF).c2 = 0 := rfl
    have h3 : (1 : EF).c3 = 0 := rfl
    apply ext <;> simp only [Ext4.ofBase, mul_c0, mul_c1, mul_c2, mul_c3, h1, h2, h3] <;> ring_nf
    · rw [mul_inv_cancel₀ hN]; rfl
  have e := congrArg Ext4.toSpec (mul_cubic z x)
  have e' := congrArg Ext4.toSpec hinv
  rw [Ext4.toSpec_mul] at e e'
  rw [Ext4.toSpec_one] at e'
  apply Ext4.toSpec_injective
  rw [Ext4.toSpec_inv, smul_eq_ofBase_mul, Ext4.toSpec_mul]
  have h1 : Ext4.toSpec (z - Ext4.ofBase x) *
      (Ext4.toSpec (Ext4.ofBase (norm z x)⁻¹) * Ext4.toSpec (cubic z x)) = 1 := by
    rw [← e', ← e]; ring
  exact (eq_inv_of_mul_eq_one_right h1).symm

end CompStark.Stark.Norm
