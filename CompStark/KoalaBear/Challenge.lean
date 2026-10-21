/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.KoalaBear.Field
public import CompStark.Stark.Challenge
public import CompPoly.Fields.KoalaBear.FastExt4
public import CompPoly.Fields.KoalaBear.FastExt5

/-! # The challenge fields of the KoalaBear STARK

CompPoly's fast extensions as challenge fields (`Challenge`):

* the quartic `KoalaBear.Fast.Ext4`, `KoalaBear[X] / (X^4 - 3)`, Plonky3's
  `BinomialExtensionField<KoalaBear, 4>`;
* the quintic `KoalaBear.Fast.Ext5`, `KoalaBear[X] / (X^5 + X^2 - 1)`, Plonky3's
  `QuinticTrinomialExtensionField<KoalaBear>`.
-/

@[expose] public section
namespace CompStark
open CompPoly.Extension Montgomery.Native32

namespace KoalaBear
open _root_.KoalaBear.Fast

/-- Multiplication by `W = 3`. -/
theorem mulW_eq (x : Field) : Binomial4.mulW (p := _root_.KoalaBear.fieldSize) x = 3 * x := by
  rw [Binomial4.mulW_eq]; rfl

/-- The quartic extension `KoalaBear[X] / (X^4 - 3)` of Plonky3's KoalaBear configuration. -/
instance instChallengeExt4 : Challenge Field Ext4 where
  params := Montgomery.Native32.Ext4.P _root_.KoalaBear.fieldSize
  coeffs x := [x.c0, x.c1, x.c2, x.c3]
  ofCoeffs l := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0⟩
  ofBase := Montgomery.Native32.Ext4.ofBase
  smul := Montgomery.Native32.Ext4.smul
  toSpec := Montgomery.Native32.Ext4.specEquiv _root_.KoalaBear.fieldSize
  length_coeffs _ := rfl
  coeffNat_toSpec x i := by
    rw [Montgomery.Native32.Ext4.specEquiv_apply]
    by_cases hi : i < 4
    · rw [Montgomery.Native32.Ext4.coeffNat_toSpec _ hi]
      interval_cases i <;> rfl
    · rw [Ext.coeffNat_of_ge _ (by rw [Montgomery.Native32.Ext4.d_eq]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
  toSpec_ofCoeffs l := by
    rw [Montgomery.Native32.Ext4.specEquiv_apply, Montgomery.Native32.Ext4.toSpec]
    congr 1
    funext i
    fin_cases i <;> rfl
  toSpec_ofBase := Montgomery.Native32.Ext4.toSpec_ofBase
  toSpec_smul := Montgomery.Native32.Ext4.toSpec_smul
  toSpec_zero := Montgomery.Native32.Ext4.toSpec_zero
  toSpec_one := Montgomery.Native32.Ext4.toSpec_one
  toSpec_neg := Montgomery.Native32.Ext4.toSpec_neg
  toSpec_sub := Montgomery.Native32.Ext4.toSpec_sub
  toSpec_inv := Montgomery.Native32.Ext4.toSpec_inv

theorem coeffs_ext4 (x : Ext4) :
    Challenge.coeffs x = [x.c0, x.c1, x.c2, x.c3] := rfl

theorem ofCoeffs_ext4 (l : List Field) :
    (Challenge.ofCoeffs l : Ext4) =
      ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0⟩ := rfl

theorem ofBase_ext4 (x : Field) : (Challenge.ofBase x : Ext4) = Montgomery.Native32.Ext4.ofBase x :=
  rfl

theorem smul_ext4 (x : Field) (a : Ext4) :
    Challenge.smul x a = Montgomery.Native32.Ext4.smul x a := rfl

theorem toSpec_ext4 (a : Ext4) :
    Challenge.toSpec a = Montgomery.Native32.Ext4.toSpec a := rfl

@[simp] theorem d_ext4 : Challenge.d Ext4 = 4 := rfl

/-- `Ext4.toSpec_ofBase` for the generic `Ext.ofBase`. -/
theorem toSpec_ofBase_ext4 (x : Field) :
    Montgomery.Native32.Ext4.toSpec (Stark.Ext.ofBase x : Ext4) = Ext.ofBase x :=
  Montgomery.Native32.Ext4.toSpec_ofBase x

theorem outsideBase_ext4 (z : Ext4) :
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

/-- The quintic extension `KoalaBear[X] / (X^5 + X^2 - 1)`, Plonky3's
`QuinticTrinomialExtensionField<KoalaBear>`. -/
instance instChallengeExt5 : Challenge Field Ext5 where
  params := Ext5.P
  coeffs x := [x.c0, x.c1, x.c2, x.c3, x.c4]
  ofCoeffs l := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0⟩
  ofBase := Ext5.ofBase
  smul := Ext5.smul
  toSpec := Ext5.specEquiv
  length_coeffs _ := rfl
  coeffNat_toSpec x i := by
    rw [Ext5.specEquiv_apply]
    by_cases hi : i < 5
    · rw [Ext5.coeffNat_toSpec _ hi]
      interval_cases i <;> rfl
    · rw [Ext.coeffNat_of_ge _ (by rw [Ext5.d_eq]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
  toSpec_ofCoeffs l := by
    rw [Ext5.specEquiv_apply, Ext5.toSpec]
    congr 1
    funext i
    fin_cases i <;> rfl
  toSpec_ofBase := Ext5.toSpec_ofBase
  toSpec_smul := Ext5.toSpec_smul
  toSpec_zero := Ext5.toSpec_zero
  toSpec_one := Ext5.toSpec_one
  toSpec_neg := Ext5.toSpec_neg
  toSpec_sub := Ext5.toSpec_sub
  toSpec_inv := Ext5.toSpec_inv

theorem toSpec_ext5 (a : Ext5) : Challenge.toSpec a = Ext5.toSpec a := rfl

@[simp] theorem d_ext5 : Challenge.d Ext5 = 5 := rfl

end KoalaBear
end CompStark
