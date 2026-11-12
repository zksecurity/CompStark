/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Parameters
public import CompStark.Multilinear.Basic

/-! Rational upper bounds on the WHIR level errors at an integer Johnson multiplicity. Every
bound is conditional on natural-number inequalities only, so concrete levels are certified by
kernel evaluation. -/

@[expose] public section

namespace CompStark.Pcs

open CompStark.BinaryFields CompStark.Multilinear
open CompStark.Pcs (johnsonSlack johnsonLevelSecurity)
open scoped ENNReal

section Real

variable {n : ℕ} (enc : Whir.Encoding K n) (m : ℕ)

/-- The reduced rate is the base field's reduced-rate expression. -/
theorem reducedRate_eq :
    Whir.reducedRate enc = ((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + enc.rate) := rfl

/-- One minus the analysis radius is the reduced-rate Johnson factor `√ρ (1 + 1/m)`. -/
theorem one_sub_radius :
    1 - Whir.radius enc (johnsonLevelSecurity n enc.rate m) =
      Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + enc.rate)) * (1 + 1 / (m : ℝ)) := by
  simp only [Whir.radius, Whir.reducedRate, johnsonLevelSecurity, johnsonSlack]
  ring

/-- The square of the query base is a ratio of natural numbers. -/
theorem queryBase_sq (hm : 0 < m) :
    (Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + enc.rate)) * (1 + 1 / (m : ℝ))) ^ 2 =
      (((2 ^ n - 1) * (m + 1) ^ 2 : ℕ) : ℝ) / ((2 ^ (n + enc.rate) * m ^ 2 : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  push_cast
  field_simp

/-- Natural-number admissibility keeps the Johnson slack below the reduced-rate Johnson radius. -/
theorem johnsonSlack_lt (rate : ℕ) (hm : 0 < m)
    (h : (m + 1) ^ 2 * (2 ^ n - 1) < m ^ 2 * 2 ^ (n + rate)) :
    johnsonSlack n rate m < 1 - Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (0 : ℝ) < 2 ^ (n + rate) := by positivity
  have hρ : (0 : ℝ) ≤ ((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate) := by positivity
  have hfac : (0 : ℝ) ≤ 1 + 1 / (m : ℝ) := by positivity
  have hsq : Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate)) * (1 + 1 / (m : ℝ)) =
      Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate) * (1 + 1 / (m : ℝ)) ^ 2) := by
    rw [Real.sqrt_mul hρ, Real.sqrt_sq hfac]
  have lt_one : Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate) * (1 + 1 / (m : ℝ)) ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow]
    have hcast : (((m + 1) ^ 2 * (2 ^ n - 1) : ℕ) : ℝ) < ((m ^ 2 * 2 ^ (n + rate) : ℕ) : ℝ) := by
      exact_mod_cast h
    have : ((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate) * (1 + 1 / (m : ℝ)) ^ 2 =
        ((2 ^ n - 1 : ℕ) : ℝ) * (m + 1) ^ 2 / (m ^ 2 * 2 ^ (n + rate)) := by
      field_simp
    rw [this, div_lt_one (by positivity)]
    push_cast at hcast
    linarith
  have expand : Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate)) * (1 + 1 / (m : ℝ)) =
      Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + rate)) + johnsonSlack n rate m := by
    unfold johnsonSlack
    ring
  rw [hsq] at expand
  linarith

/-- The column-query error is at most `2^-κ` when the squared base, raised to `t`, is at most `4^-κ`. -/
theorem queryError_le (t κ : ℕ) (hm : 0 < m)
    (check : ((2 ^ n - 1) * (m + 1) ^ 2) ^ t * 4 ^ κ ≤ (2 ^ (n + enc.rate) * m ^ 2) ^ t) :
    Whir.queryError enc (johnsonLevelSecurity n enc.rate m) t ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  set x := Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + enc.rate)) * (1 + 1 / (m : ℝ)) with hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have x_nonneg : 0 ≤ x := by positivity
  have base : 1 - Whir.radius enc (johnsonLevelSecurity n enc.rate m) = x := one_sub_radius enc m
  have hd : (0 : ℝ) < ((2 ^ (n + enc.rate) * m ^ 2 : ℕ) : ℝ) := by positivity
  have squared : (x ^ t) ^ 2 ≤ (((2 : ℝ) ^ κ)⁻¹) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, queryBase_sq enc m hm, div_pow, inv_pow, ← pow_mul,
      mul_comm κ 2, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
    rw [div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    exact_mod_cast check
  have bound : x ^ t ≤ ((2 : ℝ) ^ κ)⁻¹ :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp squared
  unfold Whir.queryError
  rw [base]
  calc ENNReal.ofReal (x ^ t) ≤ ENNReal.ofReal (((2 : ℝ) ^ κ)⁻¹) := ENNReal.ofReal_le_ofReal bound
    _ = ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]

/-- At slack `√ρ / m` the real Johnson list bound is the rational `m 2^(n + rate) / (2 (2^n - 1))`. -/
theorem listBound_eq (hn : 0 < n) (hm : 0 < m) :
    Whir.listBound enc (johnsonLevelSecurity n enc.rate m) =
      ((m * 2 ^ (n + enc.rate) : ℕ) : ℝ) / ((2 * (2 ^ n - 1) : ℕ) : ℝ) := by
  have hD : (0 : ℝ) < ((2 ^ n - 1 : ℕ) : ℝ) := by
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (Nat.ne_of_gt hn)
    exact_mod_cast (by omega : 0 < 2 ^ n - 1)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ : (0 : ℝ) < ((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + enc.rate) := by positivity
  set x := Real.sqrt (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + enc.rate)) with hx
  have hs : x * x = ((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ (n + enc.rate) := Real.mul_self_sqrt hρ.le
  simp only [Whir.listBound, Whir.reducedRate, johnsonLevelSecurity, johnsonSlack, ← hx]
  rw [show 2 * (x / m) * x = 2 * (x * x) / m by ring, hs]
  push_cast
  field_simp

/-- At a positive slack and `m ≥ 3`, the MCA parameter `θ` is the multiplicity itself, and a rational
lower bound `X / Y ≤ √ρ` bounds Annex B's MCA numerator. -/
theorem mcaNumerator_le (X Y : ℕ) (hm : 3 ≤ m) (hX : 0 < X)
    (hxy : X ^ 2 * 2 ^ (n + enc.rate) ≤ (2 ^ n - 1) * Y ^ 2) :
    Whir.mcaNumerator enc (johnsonLevelSecurity n enc.rate m) ≤
      ((((2 * m + 1) ^ 5 + 24 * (2 * m + 1)) * Y ^ 3 * 2 ^ (n + enc.rate) : ℕ) : ℝ) /
          ((48 * X ^ 3 : ℕ) : ℝ) +
        (((2 * m + 1) * Y : ℕ) : ℝ) / ((2 * X : ℕ) : ℝ) := by
  set N : ℝ := 2 ^ (n + enc.rate) with hN
  have hNpos : 0 < N := by positivity
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  set ρ : ℝ := Whir.reducedRate enc with hρdef
  have hρeq : ρ = ((2 ^ n - 1 : ℕ) : ℝ) / N := rfl
  have hY : 0 < Y := by
    rcases Nat.eq_zero_or_pos Y with h | h
    · subst h
      have : 0 < X ^ 2 * 2 ^ (n + enc.rate) := by positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hxy
      omega
    · exact h
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have xlo : (X : ℝ) / Y ≤ Real.sqrt ρ := by
    apply Real.le_sqrt_of_sq_le
    rw [hρeq, div_pow, div_le_div_iff₀ (by positivity) hNpos]
    have : ((X ^ 2 * 2 ^ (n + enc.rate) : ℕ) : ℝ) ≤ (((2 ^ n - 1) * Y ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hxy
    push_cast at this
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this ⊢
    simp only [N]
    linarith
  have sρpos : 0 < Real.sqrt ρ := lt_of_lt_of_le (by positivity) xlo
  have hρle : ρ ≤ 1 := by
    rw [hρeq, div_le_one hNpos]
    have : ((2 ^ n - 1 : ℕ) : ℝ) ≤ 2 ^ n := by
      exact_mod_cast Nat.sub_le _ _
    calc ((2 ^ n - 1 : ℕ) : ℝ) ≤ 2 ^ n := this
      _ ≤ N := pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
  have hρnonneg : 0 ≤ ρ := by rw [hρeq]; positivity
  have radiusEq : Whir.radius enc (johnsonLevelSecurity n enc.rate m) =
      1 - Real.sqrt ρ * (1 + 1 / (m : ℝ)) := by
    have := one_sub_radius enc m
    rw [← hρeq] at this
    linarith
  have θEq : (max (⌈Real.sqrt ρ / (johnsonLevelSecurity n enc.rate m).slack⌉₊ : ℝ) 3) = m := by
    change (max (⌈Real.sqrt ρ / (Real.sqrt ρ / m)⌉₊ : ℝ) 3) = m
    rw [div_div_cancel₀ sρpos.ne', Nat.ceil_natCast, max_eq_left hmR]
  have radius_le : Whir.radius enc (johnsonLevelSecurity n enc.rate m) ≤ 1 := by
    rw [radiusEq]
    have : 0 ≤ Real.sqrt ρ * (1 + 1 / (m : ℝ)) := by positivity
    linarith
  unfold Whir.mcaNumerator
  simp only []
  rw [← hρdef, θEq]
  set γ := Whir.radius enc (johnsonLevelSecurity n enc.rate m)
  set x := Real.sqrt ρ
  have hx : 0 < x := sρpos
  have γρ : γ * ρ ≤ 1 := by
    rcases le_or_gt 0 γ with hγ | hγ
    · calc γ * ρ ≤ 1 * 1 := mul_le_mul radius_le hρle hρnonneg zero_le_one
        _ = 1 := one_mul 1
    · nlinarith
  have hxX : (X : ℝ) / Y ≤ x := xlo
  have hq : (0 : ℝ) < (X : ℝ) / Y := by positivity
  -- Replace the radius term by its bound, then the square root by its lower bound.
  have first : (2 * ((m : ℝ) + 1 / 2) ^ 5 + 3 * ((m : ℝ) + 1 / 2) * γ * ρ) / (3 * x ^ 3) * N ≤
      (2 * ((m : ℝ) + 1 / 2) ^ 5 + 3 * ((m : ℝ) + 1 / 2)) / (3 * ((X : ℝ) / Y) ^ 3) * N := by
    apply mul_le_mul_of_nonneg_right _ hNpos.le
    apply div_le_div₀ (by positivity) _ (by positivity)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.le hxX 3) (by norm_num)
    · have : 3 * ((m : ℝ) + 1 / 2) * γ * ρ = 3 * ((m : ℝ) + 1 / 2) * (γ * ρ) := by ring
      rw [this]
      nlinarith [show (0 : ℝ) ≤ 3 * ((m : ℝ) + 1 / 2) by positivity]
  have second : ((m : ℝ) + 1 / 2) / x ≤ ((m : ℝ) + 1 / 2) / ((X : ℝ) / Y) :=
    div_le_div_of_nonneg_left (by positivity) hq hxX
  refine (add_le_add first second).trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

end Real

/-- The field `E` has `2^192` elements. -/
theorem card_E : (Fintype.card E : ℝ) = 2 ^ 192 := by
  rw [show Fintype.card E = 2 ^ 192 from BF64.card_ext3]
  norm_num

/-- An `ENNReal.ofReal` of a nonnegative ratio below `2^-κ` is at most `2^-κ`. -/
theorem ofReal_le_inv_two_pow {x : ℝ} {κ : ℕ} (h : x ≤ ((2 : ℝ) ^ κ)⁻¹) :
    ENNReal.ofReal x ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  calc ENNReal.ofReal x ≤ ENNReal.ofReal (((2 : ℝ) ^ κ)⁻¹) := ENNReal.ofReal_le_ofReal h
    _ = ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]

/-- A real bound `x ≤ A / B` over `|E|` lies below `2^-κ` when `A 2^κ ≤ B 2^192`. -/
theorem div_card_le {x : ℝ} {A B κ : ℕ} (hB : 0 < B) (hx : x ≤ (A : ℝ) / B)
    (check : A * 2 ^ κ ≤ B * 2 ^ 192) : x / Fintype.card E ≤ ((2 : ℝ) ^ κ)⁻¹ := by
  rw [card_E, div_le_iff₀ (by positivity)]
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have checkR : (A : ℝ) * 2 ^ κ ≤ B * 2 ^ 192 := by exact_mod_cast check
  calc x ≤ (A : ℝ) / B := hx
    _ ≤ ((2 : ℝ) ^ κ)⁻¹ * 2 ^ 192 := by
      rw [div_le_iff₀ hBR, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith

section Errors

variable {n : ℕ} (enc : Whir.Encoding K n) (m : ℕ)

/-- Numerator of the rational list size of `listBound_eq`. -/
def listNumerator (n rate m : ℕ) : ℕ := m * 2 ^ (n + rate)

/-- Denominator of the rational list size of `listBound_eq`. -/
def listDenominator (n : ℕ) : ℕ := 2 * (2 ^ n - 1)

/-- The rational list size has a positive denominator. -/
theorem listDenominator_pos {n : ℕ} (hn : 0 < n) : 0 < listDenominator n := by
  have : 1 < 2 ^ n := Nat.one_lt_two_pow (Nat.ne_of_gt hn)
  unfold listDenominator
  omega

/-- The list bound is nonnegative and at most its rational value. -/
theorem listBound_le (hn : 0 < n) (hm : 0 < m) :
    0 ≤ Whir.listBound enc (johnsonLevelSecurity n enc.rate m) ∧
      Whir.listBound enc (johnsonLevelSecurity n enc.rate m) ≤
        ((listNumerator n enc.rate m : ℕ) : ℝ) / ((listDenominator n : ℕ) : ℝ) := by
  rw [listBound_eq enc m hn hm]
  exact ⟨by positivity, le_rfl⟩

/-- The batching error is at most `2^-κ` under the rational list bound. -/
theorem batchError_le (claims κ : ℕ) (hm : 0 < m) (hn : 0 < n)
    (check : (claims - 1) * listNumerator n enc.rate m * 2 ^ κ ≤
      listDenominator n * 2 ^ 192) :
    Whir.batchError (E := E) enc (johnsonLevelSecurity n enc.rate m) claims ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨nonneg, bound⟩ := listBound_le enc m hn hm
  apply ofReal_le_inv_two_pow
  apply div_card_le (listDenominator_pos hn) _ check
  rw [Nat.cast_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left bound (by positivity)

/-- The fold error is at most `2^-κ` under the rational list and MCA bounds. -/
theorem foldError_le (X Y κ : ℕ) (hm : 3 ≤ m) (hn : 0 < n)
    (hX : 0 < X) (hxy : X ^ 2 * 2 ^ (n + enc.rate) ≤ (2 ^ n - 1) * Y ^ 2)
    (check : (2 * listNumerator n enc.rate m * (48 * X ^ 3) * (2 * X) +
        ((2 * m + 1) ^ 5 + 24 * (2 * m + 1)) * Y ^ 3 * 2 ^ (n + enc.rate) *
          listDenominator n * (2 * X) +
        (2 * m + 1) * Y * listDenominator n * (48 * X ^ 3)) * 2 ^ κ ≤
      listDenominator n * (48 * X ^ 3) * (2 * X) * 2 ^ 192) :
    Whir.foldError (E := E) enc (johnsonLevelSecurity n enc.rate m) ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨nonneg, bound⟩ := listBound_le enc m hn (by omega)
  have mca := mcaNumerator_le enc m X Y hm hX hxy
  have hB := listDenominator_pos hn
  have hBR : (0 : ℝ) < listDenominator n := by exact_mod_cast hB
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  set mcaHi : ℝ := (((((2 * m + 1) ^ 5 + 24 * (2 * m + 1)) * Y ^ 3 * 2 ^ (n + enc.rate) : ℕ) : ℝ) /
      ((48 * X ^ 3 : ℕ) : ℝ) + (((2 * m + 1) * Y : ℕ) : ℝ) / ((2 * X : ℕ) : ℝ))
  have mcaHi_nonneg : 0 ≤ mcaHi := by positivity
  have total : 2 * Whir.listBound enc (johnsonLevelSecurity n enc.rate m) / Fintype.card E +
      mcaHi / Fintype.card E ≤ ((2 : ℝ) ^ κ)⁻¹ := by
    rw [← add_div]
    apply div_card_le (by positivity) _ check
    have combined : 2 * Whir.listBound enc (johnsonLevelSecurity n enc.rate m) + mcaHi ≤
        2 * ((listNumerator n enc.rate m : ℕ) : ℝ) / (listDenominator n : ℕ) + mcaHi := by
      rw [mul_div_assoc]
      linarith
    refine combined.trans (le_of_eq ?_)
    simp only [mcaHi]
    push_cast
    field_simp
    ring
  unfold Whir.foldError Whir.mcaError
  have hE : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  calc ENNReal.ofReal (2 * Whir.listBound enc (johnsonLevelSecurity n enc.rate m) / Fintype.card E) +
        ENNReal.ofReal (Whir.mcaNumerator enc (johnsonLevelSecurity n enc.rate m) / Fintype.card E) ≤
        ENNReal.ofReal (2 * Whir.listBound enc (johnsonLevelSecurity n enc.rate m) / Fintype.card E) +
          ENNReal.ofReal (mcaHi / Fintype.card E) := by
        gcongr
    _ = ENNReal.ofReal (2 * Whir.listBound enc (johnsonLevelSecurity n enc.rate m) / Fintype.card E +
          mcaHi / Fintype.card E) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := ofReal_le_inv_two_pow total

/-- The out-of-domain error at an entering level is at most `2^-κ` under the rational list bound. -/
theorem oodError_le (nvars κ : ℕ) (hm : 0 < m) (hn : 0 < n)
    (check : listNumerator n enc.rate m ^ 2 * nvars * 2 ^ κ ≤
      2 * listDenominator n ^ 2 * 2 ^ 192) :
    Whir.oodError (E := E) enc (johnsonLevelSecurity n enc.rate m) nvars ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨nonneg, bound⟩ := listBound_le enc m hn hm
  have hB := listDenominator_pos hn
  have hBR : (0 : ℝ) < listDenominator n := by exact_mod_cast hB
  apply ofReal_le_inv_two_pow
  apply div_card_le (by positivity) _ check
  set L := Whir.listBound enc (johnsonLevelSecurity n enc.rate m)
  have bound' : L ≤ (listNumerator n enc.rate m : ℝ) / listDenominator n := by
    exact bound
  have sq : L * L ≤ ((listNumerator n enc.rate m : ℝ) / listDenominator n) ^ 2 := by
    rw [sq]; exact mul_le_mul bound' bound' nonneg (le_trans nonneg bound')
  calc L * (L - 1) / 2 * nvars ≤ L * L / 2 * nvars := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by norm_num)
        nlinarith
    _ ≤ ((listNumerator n enc.rate m : ℝ) / listDenominator n) ^ 2 / 2 * nvars := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right sq (by norm_num)
    _ = _ := by
        push_cast
        field_simp

/-- A numerator charge `d / |E|` is at most `2^-κ` when `d 2^κ ≤ 2^192`. -/
theorem overE_le (d κ : ℕ) (check : d * 2 ^ κ ≤ 2 ^ 192) : overE d ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  unfold overE
  rw [show Fintype.card E = 2 ^ 192 from BF64.card_ext3]
  rw [ENNReal.div_le_iff (by positivity) (by simp), ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  exact_mod_cast check

/-- An outer charge `L₀ d / |E|` at the initial list bound is at most `2^-κ`. -/
theorem outerError_le (d κ : ℕ) (hm : 0 < m) (hn : 0 < n)
    (check : d * listNumerator n enc.rate m * 2 ^ κ ≤ listDenominator n * 2 ^ 192) :
    ENNReal.ofReal (Whir.listBound enc (johnsonLevelSecurity n enc.rate m)) * overE d ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  obtain ⟨nonneg, bound⟩ := listBound_le enc m hn hm
  have hE : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have eq : ENNReal.ofReal (Whir.listBound enc (johnsonLevelSecurity n enc.rate m)) * overE d =
      ENNReal.ofReal (d * Whir.listBound enc (johnsonLevelSecurity n enc.rate m) / Fintype.card E) := by
    unfold overE
    rw [mul_comm (d : ℝ), mul_div_assoc, ENNReal.ofReal_mul nonneg,
      ENNReal.ofReal_div_of_pos hE, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [eq]
  apply ofReal_le_inv_two_pow
  apply div_card_le (A := d * listNumerator n enc.rate m) (listDenominator_pos hn) _ check
  rw [Nat.cast_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left bound (by positivity)

end Errors

end CompStark.Pcs
