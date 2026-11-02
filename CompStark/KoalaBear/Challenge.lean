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
  `BinomialExtensionField<KoalaBear, 4>`, as every quartic extension of a fast Montgomery field;
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
instance : Mont32.AlgebraId Ext5 := ⟨"p3-power-basis-v1:X^5+X^2-1"⟩

theorem toSpec_ext5 (a : Ext5) : Challenge.toSpec a = Ext5.toSpec a := rfl

@[simp] theorem d_ext5 : Challenge.d Ext5 = 5 := rfl

end KoalaBear
end CompStark
