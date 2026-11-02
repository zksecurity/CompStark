/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Mont32.BaseField
public import CompStark.Stark.Challenge
public import CompPoly.Fields.Montgomery.FastExt

/-! # Challenge fields of fast Montgomery fields

A fast extension `EF` of `FastField p` (CompPoly's `FastExt p EF`: coordinates in the power basis
of a monic modulus, with the spec field's operations) is a challenge field (`Challenge`) of the
base field `FastField p`, given Plonky3's identity of its algebra (`AlgebraId`). Its spec field is
CompPoly's `Ext` over `FastField p` with CompPoly's field structure, the same as the base field's
(`Mont32BaseField.instBaseField`). Instances: the quartic binomial extensions `Ext4 p`, Plonky3's
`BinomialExtensionField<F, 4>`, here, and KoalaBear's quintic `KoalaBear.Fast.Ext5` in
`CompStark/KoalaBear/Challenge.lean`.
-/

@[expose] public section
namespace CompStark
open CompPoly.Extension Montgomery.Native32

namespace Mont32

/-- Plonky3's identity of an extension's algebra and basis (`AlgebraIdentity::algebra_id`). -/
class AlgebraId (EF : Type) where
  algebraId : String

variable {p : ℕ} [Mont32Field p] [Mont32BaseField p]

/-- A fast extension as a challenge field. Inlined, so that code specialized to an extension runs
its arithmetic directly instead of through the instance's closures. -/
@[inline] instance instChallenge {EF : Type} [FastExt p EF] [AlgebraId EF] :
    Challenge (FastField p) EF where
  toBEq := instBEqOfDecidableEq
  toInhabited := ⟨0⟩
  params := FastExt.params EF
  coeffs x := List.ofFn (FastExt.coord x)
  ofCoeffs l := FastExt.ofCoords fun i ↦ l.getD i 0
  ofBase := FastExt.ofBase
  smul x a := FastExt.ofCoords fun i ↦ x * FastExt.coord a i
  toSpec := FastExt.specEquiv p EF
  algebraId := AlgebraId.algebraId EF
  length_coeffs _ := List.length_ofFn
  coeffNat_toSpec x i := by
    rw [FastExt.specEquiv_apply]
    by_cases hi : i < (FastExt.params EF).d
    · rw [Ext.coeffNat_of_lt _ hi, FastExt.coeff_toSpec, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn]
      simp only [hi, dite_true, Option.getD_some]
    · rw [Ext.coeffNat_of_ge _ (by omega),
        List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
  toSpec_ofCoeffs l := by rw [FastExt.specEquiv_apply, FastExt.toSpec_ofCoords]
  toSpec_ofBase := FastExt.toSpec_ofBase
  toSpec_smul x a := by
    rw [FastExt.specEquiv_apply, FastExt.specEquiv_apply, FastExt.toSpec_ofCoords]
    ext i
    rw [Ext.coeff_ofFn, Ext.coeff_smul, FastExt.coeff_toSpec]
  toSpec_zero := FastExt.toSpec_zero
  toSpec_one := FastExt.toSpec_one
  toSpec_neg := FastExt.toSpec_neg
  toSpec_sub := FastExt.toSpec_sub
  toSpec_inv := FastExt.toSpec_inv

variable {EF : Type} [FastExt p EF] [AlgebraId EF]

theorem coeffs_eq (x : EF) : Challenge.coeffs x = List.ofFn (FastExt.coord x) := rfl

theorem ofCoeffs_eq (l : List (FastField p)) :
    (Challenge.ofCoeffs l : EF) = FastExt.ofCoords fun i ↦ l.getD i 0 := rfl

theorem ofBase_eq (x : FastField p) : (Challenge.ofBase x : EF) = FastExt.ofBase x := rfl

theorem toSpec_eq (a : EF) : Challenge.toSpec a = FastExt.toSpec a := rfl

theorem d_eq : Challenge.d EF = FastExt.d p EF := rfl

theorem smul_eq (x : FastField p) (a : EF) :
    Challenge.smul x a = FastExt.ofBase x * a :=
  FastExt.toSpec_injective (by
    rw [← toSpec_eq, Challenge.toSpec_smul, FastExt.toSpec_mul, FastExt.toSpec_ofBase,
      ← Ext.algebraMap_eq_ofBase, Algebra.smul_def, toSpec_eq]
    rfl)

/-- An element outside the base field is no base element. -/
theorem ne_ofBase {z : EF} (hz : Stark.Ext.OutsideBase z) (x : FastField p) :
    z ≠ FastExt.ofBase x := fun h ↦
  Stark.Ext.toSpec_ne_algebraMap hz x (by
    rw [toSpec_eq, h, FastExt.toSpec_ofBase, Ext.algebraMap_eq_ofBase])

/-- The quartic binomial extension `FastField p [X] / (X^4 - W)`, Plonky3's
`BinomialExtensionField<F, 4>`. -/
instance [Binomial4 p] : AlgebraId (Ext4 p) :=
  ⟨s!"p3-power-basis-v1:X^4-{CompPoly.CanonicalNat.toNat (Binomial4.W (p := p))}"⟩

@[simp] theorem d_ext4 [Binomial4 p] : Challenge.d (Ext4 p) = 4 := rfl

end Mont32
end CompStark
