/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Mont32.BaseField
public import CompStark.Stark.Challenge
public import CompPoly.Fields.Montgomery.Native32Ext4

/-! # Quartic challenge fields of fast Montgomery fields

CompPoly's fast quartic extension `Ext4 p`, `FastField p [X] / (X^4 - W)` for a `Binomial4 p`
instance, is a challenge field (`Challenge`) of the base field `FastField p`: Plonky3's
`BinomialExtensionField<F, 4>`. Its spec field is CompPoly's `Ext` over `FastField p` with
CompPoly's field structure, the same as the base field's (`Mont32BaseField.instBaseField`).
-/

@[expose] public section
namespace CompStark
open CompPoly.Extension Montgomery.Native32

namespace Mont32

variable {p : ℕ} [Mont32Field p] [Mont32BaseField p] [Binomial4 p]

/-- The quartic extension `FastField p [X] / (X^4 - W)`. -/
instance instChallengeExt4 : Challenge (FastField p) (Ext4 p) where
  params := Ext4.P p
  coeffs x := [x.c0, x.c1, x.c2, x.c3]
  ofCoeffs l := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0⟩
  ofBase := Ext4.ofBase
  smul := Ext4.smul
  toSpec := Ext4.specEquiv p
  length_coeffs _ := rfl
  coeffNat_toSpec x i := by
    rw [Ext4.specEquiv_apply]
    by_cases hi : i < 4
    · rw [Ext4.coeffNat_toSpec _ hi]
      interval_cases i <;> rfl
    · rw [Ext.coeffNat_of_ge _ (by rw [Ext4.d_eq]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
  toSpec_ofCoeffs l := by
    rw [Ext4.specEquiv_apply, Ext4.toSpec]
    congr 1
    funext i
    fin_cases i <;> rfl
  toSpec_ofBase := Ext4.toSpec_ofBase
  toSpec_smul := Ext4.toSpec_smul
  toSpec_zero := Ext4.toSpec_zero
  toSpec_one := Ext4.toSpec_one
  toSpec_neg := Ext4.toSpec_neg
  toSpec_sub := Ext4.toSpec_sub
  toSpec_inv := Ext4.toSpec_inv

theorem coeffs_ext4 (x : Ext4 p) : Challenge.coeffs x = [x.c0, x.c1, x.c2, x.c3] := rfl

theorem ofCoeffs_ext4 (l : List (FastField p)) :
    (Challenge.ofCoeffs l : Ext4 p) = ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0⟩ := rfl

theorem ofBase_ext4 (x : FastField p) : (Challenge.ofBase x : Ext4 p) = Ext4.ofBase x := rfl

theorem smul_ext4 (x : FastField p) (a : Ext4 p) : Challenge.smul x a = Ext4.smul x a := rfl

theorem toSpec_ext4 (a : Ext4 p) : Challenge.toSpec a = Ext4.toSpec a := rfl

@[simp] theorem d_ext4 : Challenge.d (Ext4 p) = 4 := rfl

/-- `Ext4.toSpec_ofBase` for the generic `Ext.ofBase`. -/
theorem toSpec_ofBase_ext4 (x : FastField p) :
    Ext4.toSpec (Stark.Ext.ofBase x : Ext4 p) = Ext.ofBase x :=
  Ext4.toSpec_ofBase x

theorem outsideBase_ext4 (z : Ext4 p) :
    Stark.Ext.OutsideBase z ↔ z.c1 ≠ 0 ∨ z.c2 ≠ 0 ∨ z.c3 ≠ 0 := by
  constructor
  · rintro ⟨i, hi, h⟩
    match i, hi, h with
    | 1, _, h => exact Or.inl h
    | 2, _, h => exact Or.inr (Or.inl h)
    | 3, _, h => exact Or.inr (Or.inr h)
    | i + 4, _, h => exact absurd rfl h
  · rintro (h | h | h)
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩
    · exact ⟨3, by omega, h⟩

end Mont32
end CompStark
