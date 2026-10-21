/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.KoalaBear.Field
public import CompStark.Mont32.Challenge
public import CompPoly.Fields.KoalaBear.FastExt4
public import CompPoly.Fields.KoalaBear.FastExt5

/-! # The challenge fields of the KoalaBear STARK

CompPoly's fast extensions as challenge fields (`Challenge`):

* the quartic `KoalaBear.Fast.Ext4`, `KoalaBear[X] / (X^4 - 3)`, Plonky3's
  `BinomialExtensionField<KoalaBear, 4>`, an instance of the quartic extensions of fast Montgomery
  fields (`Mont32.instChallengeExt4`);
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

/-- The quintic extension `KoalaBear[X] / (X^5 + X^2 - 1)`, Plonky3's
`QuinticTrinomialExtensionField<KoalaBear>`. -/
instance instChallengeExt5 : Challenge (FastField _root_.KoalaBear.fieldSize) Ext5 where
  params := Ext5.P
  coeffs x := [x.c0, x.c1, x.c2, x.c3, x.c4]
  ofCoeffs l := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0⟩
  ofBase := Ext5.ofBase
  smul := Ext5.smul
  toSpec := Ext5.specEquiv
  algebraId := "p3-power-basis-v1:X^5+X^2-1"
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
