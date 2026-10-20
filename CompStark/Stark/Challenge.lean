/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.KoalaBear.FastExt4
public import CompPoly.Fields.KoalaBear.FastExt5
public import CompPoly.Fields.Extension.Field
public import Mathlib.Data.List.GetD

/-! # The challenge field

The STARK draws its challenges from an extension of KoalaBear. `Challenge EF` makes an executable
type `EF` such an extension: its operations, its coordinates over the fast base field, and a ring
isomorphism `toSpec` to the spec field `Ext params`, `KoalaBear[X] / params.poly`, under which
every operation agrees with the spec field's. The verifier and the prover run on `EF`; the
analysis lives in `Challenge.Spec EF`, a finite field of `fieldSize ^ d` elements.

`Fast.Ext4` and `Fast.Ext5` are instances. Generic helpers: base elements, powers, the basis
`X ^ e`, and `OutsideBase`, each with its value in the spec field.
-/

@[expose] public section
namespace CompStark

open CompPoly.Extension Montgomery.Native32

local notation "F" => KoalaBear.Fast.Field

/-- An executable extension field of KoalaBear: operations, coordinates over the fast base
field, and the ring isomorphism `toSpec` with the spec field `Ext params` that every operation
agrees with. -/
class Challenge (EF : Type) extends Add EF, Sub EF, Neg EF, Mul EF, Inv EF, Zero EF, One EF,
    BEq EF, Inhabited EF where
  /-- The modulus of the spec field. -/
  params : ExtensionParams KoalaBear.Field
  [card : Fact (Nat.card KoalaBear.Field = params.q)]
  [irred : Fact (Irreducible params.poly)]
  [lawfulBEq : LawfulBEq EF]
  /-- The `d` coordinates, lowest first. -/
  coeffs : EF → List F
  /-- The element with the given coordinates, missing ones zero. -/
  ofCoeffs : List F → EF
  /-- A base element. -/
  ofBase : F → EF
  /-- Multiplication by a base element. -/
  smul : F → EF → EF
  /-- The isomorphism with the spec field. -/
  toSpec : EF ≃+* Ext params
  length_coeffs (x : EF) : (coeffs x).length = params.d
  toField_coeffs (x : EF) (i : Nat) :
    FastField.toField ((coeffs x).getD i 0) = Ext.coeffNat (toSpec x) i
  toSpec_ofCoeffs (l : List F) :
    toSpec (ofCoeffs l) = Ext.ofFn fun i ↦ FastField.toField (l.getD i 0)
  toSpec_ofBase (x : F) : toSpec (ofBase x) = Ext.ofBase (FastField.toField x)
  toSpec_smul (x : F) (a : EF) : toSpec (smul x a) = FastField.toField x • toSpec a
  toSpec_zero : toSpec 0 = 0
  toSpec_one : toSpec 1 = 1
  toSpec_neg (a : EF) : toSpec (-a) = -toSpec a
  toSpec_sub (a b : EF) : toSpec (a - b) = toSpec a - toSpec b
  toSpec_inv (a : EF) : toSpec a⁻¹ = (toSpec a)⁻¹

namespace Challenge

attribute [instance] card irred lawfulBEq

variable (EF : Type) [Challenge EF]

/-- The spec field of `EF`, the `𝕂` of the analysis. -/
abbrev Spec : Type := Ext (params EF)

/-- The degree of the extension. -/
abbrev d : Nat := (params EF).d

variable {EF}

theorem q_eq : (params EF).q = KoalaBear.fieldSize := by
  rw [← (card (EF := EF)).out, Nat.card_eq_fintype_card, ZMod.card]

/-- The spec field has `fieldSize ^ d` elements. -/
theorem card_spec : Fintype.card (Spec EF) = KoalaBear.fieldSize ^ d EF := by
  rw [Ext.card_ext, q_eq]

@[simp] theorem toSpec_add (a b : EF) : toSpec (a + b) = toSpec a + toSpec b :=
  (toSpec (EF := EF)).map_add' a b

@[simp] theorem toSpec_mul (a b : EF) : toSpec (a * b) = toSpec a * toSpec b :=
  (toSpec (EF := EF)).map_mul' a b

attribute [simp] toSpec_ofBase toSpec_smul toSpec_zero toSpec_one toSpec_neg toSpec_sub toSpec_inv

theorem toSpec_injective : Function.Injective (toSpec (EF := EF)) := (toSpec (EF := EF)).injective

theorem coeffNat_toSpec (x : EF) (i : Nat) :
    Ext.coeffNat (toSpec x) i = FastField.toField ((coeffs x).getD i 0) :=
  (toField_coeffs x i).symm

/-- `ofCoeffs` inverts `coeffs`. -/
@[simp] theorem ofCoeffs_coeffs (x : EF) : ofCoeffs (coeffs x) = x := by
  refine toSpec_injective ?_
  rw [toSpec_ofCoeffs]
  ext i
  rw [Ext.coeff_ofFn, toField_coeffs, Ext.coeffNat_coe]

/-- `toSpec` maps base elements to `algebraMap`. -/
theorem toSpec_ofBase' (x : F) :
    toSpec (ofBase (EF := EF) x) = algebraMap KoalaBear.Field (Spec EF) (FastField.toField x) :=
  toSpec_ofBase x

/-- An element is the sum of its coordinates times the powers of the spec field's generator. -/
theorem toSpec_eq_sum (x : EF) : toSpec x = ∑ e ∈ Finset.range (d EF),
    Ext.gen ^ e *
      algebraMap KoalaBear.Field (Spec EF) (FastField.toField ((coeffs x).getD e 0)) := by
  refine Ext.toQuot_injective ?_
  rw [Ext.toQuot_sum, Ext.toQuot, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Ext.toQuot_mul, Ext.toQuot_pow, Ext.toQuot_gen, Ext.algebraMap_eq_ofBase, Ext.toQuot_ofBase,
    ← Ext.coeffNat_coe, coeffNat_toSpec, mul_comm]

end Challenge

namespace Stark.Ext
open Challenge

variable {EF : Type} [Challenge EF]

/-- An extension element of a base element. -/
abbrev ofBase (x : F) : EF := Challenge.ofBase x

/-- The base coefficients, lowest first. -/
abbrev coeffs (x : EF) : List F := Challenge.coeffs x

/-- `x ^ n` by squaring. -/
def pow (x : EF) : Nat → EF
  | 0 => 1
  | n + 1 =>
    let y := pow (x * x) ((n + 1) / 2)
    if (n + 1) % 2 = 1 then x * y else y
termination_by n => n
decreasing_by omega

/-- `x ^ (2 ^ k)`. -/
def powTwo (x : EF) : Nat → EF
  | 0 => x
  | k + 1 => powTwo (x * x) k

/-- `X ^ e`, the basis element `e` for `e < d`. -/
def basis (e : Nat) : EF :=
  Challenge.ofCoeffs ((List.range (e + 1)).map fun i ↦ if i = e then 1 else 0)

/-- `z` is outside the base field: no `z - x` for a base `x` vanishes. -/
def OutsideBase (z : EF) : Prop := ∃ i, 0 < i ∧ (coeffs z).getD i 0 ≠ 0

/-- `pow` is the power in the spec field. -/
@[simp] theorem toSpec_pow (x : EF) (n : Nat) : toSpec (pow x n) = toSpec x ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases n with
    | zero => rw [pow, toSpec_one, _root_.pow_zero]
    | succ k =>
      rw [pow]
      split_ifs with hp
      · rw [toSpec_mul, ih _ (by omega), toSpec_mul, ← sq, ← pow_mul, ← pow_succ']
        exact congrArg (toSpec x ^ ·) (by omega)
      · rw [ih _ (by omega), toSpec_mul, ← sq, ← pow_mul]
        exact congrArg (toSpec x ^ ·) (by omega)

/-- `powTwo` is `x ^ 2 ^ k` in the spec field. -/
@[simp] theorem toSpec_powTwo (x : EF) : ∀ k, toSpec (powTwo x k) = toSpec x ^ 2 ^ k
  | 0 => by rw [powTwo, _root_.pow_zero, pow_one]
  | k + 1 => by
    rw [powTwo, toSpec_powTwo _ k, toSpec_mul, ← sq, ← pow_mul, ← Nat.pow_succ']

/-- The basis element `e` is the spec generator's power `e`. -/
theorem toSpec_basis {e : Nat} (he : e < d EF) :
    toSpec (basis (EF := EF) e) = CompPoly.Extension.Ext.gen ^ e := by
  rw [basis, toSpec_ofCoeffs, CompPoly.Extension.Ext.gen_pow_of_lt he]
  congr 1
  funext i
  by_cases hi : (i : Nat) ≤ e
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega),
      List.getElem_map, List.getElem_range]
    split_ifs <;> simp only [Montgomery.Native32.toField_one, Montgomery.Native32.toField_zero]
  · rw [List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
      ite_eq_right (by omega), Montgomery.Native32.toField_zero]

/-- An element outside the base field differs from every base element. -/
theorem toSpec_ne_algebraMap {z : EF} (hz : OutsideBase z) (y : KoalaBear.Field) :
    toSpec z ≠ algebraMap KoalaBear.Field (Spec EF) y := by
  obtain ⟨i, hi, hne⟩ := hz
  intro h
  have hc := congrArg (CompPoly.Extension.Ext.coeffNat · i) h
  simp only [coeffNat_toSpec, CompPoly.Extension.Ext.algebraMap_eq_ofBase] at hc
  apply hne
  refine Montgomery.Native32.toField_injective ?_
  rw [hc, Montgomery.Native32.toField_zero]
  by_cases hd : i < (params EF).d
  · rw [CompPoly.Extension.Ext.coeffNat_of_lt _ hd, CompPoly.Extension.Ext.ofBase,
      CompPoly.Extension.Ext.coeff_ofFn]
    split_ifs with h0
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp hi)
    · rfl
  · exact CompPoly.Extension.Ext.coeffNat_of_ge _ (by omega)

end Stark.Ext

namespace KoalaBear

open _root_.KoalaBear.Fast

/-- The quartic extension `KoalaBear[X] / (X^4 - 3)` of Plonky3's KoalaBear configuration. -/
instance : Challenge Ext4 where
  params := Ext4.P
  coeffs x := [x.c0, x.c1, x.c2, x.c3]
  ofCoeffs l := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0⟩
  ofBase := Ext4.ofBase
  smul := Ext4.smul
  toSpec := Ext4.specEquiv
  length_coeffs _ := rfl
  toField_coeffs x i := by
    rw [Ext4.specEquiv_apply]
    by_cases hi : i < 4
    · rw [Ext4.coeffNat_toSpec _ hi]
      interval_cases i <;> rfl
    · rw [Ext.coeffNat_of_ge _ (by rw [Ext4.d_eq]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega),
        Montgomery.Native32.toField_zero]
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

theorem coeffs_ext4 (x : Ext4) : Challenge.coeffs x = [x.c0, x.c1, x.c2, x.c3] := rfl

theorem ofCoeffs_ext4 (l : List F) :
    (Challenge.ofCoeffs l : Ext4) = ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0⟩ := rfl

theorem ofBase_ext4 (x : F) : (Challenge.ofBase x : Ext4) = Ext4.ofBase x := rfl

theorem smul_ext4 (x : F) (a : Ext4) : Challenge.smul x a = Ext4.smul x a := rfl

theorem toSpec_ext4 (a : Ext4) : Challenge.toSpec a = Ext4.toSpec a := rfl

@[simp] theorem d_ext4 : Challenge.d Ext4 = 4 := rfl

/-- `Ext4.toSpec_ofBase` for the generic `Ext.ofBase`. -/
theorem toSpec_ofBase_ext4 (x : F) :
    Ext4.toSpec (Stark.Ext.ofBase x) = Ext.ofBase (FastField.toField x) :=
  Ext4.toSpec_ofBase x

theorem outsideBase_ext4 (z : Ext4) : Stark.Ext.OutsideBase z ↔ z.c1 ≠ 0 ∨ z.c2 ≠ 0 ∨ z.c3 ≠ 0 := by
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
instance : Challenge Ext5 where
  params := Ext5.P
  coeffs x := [x.c0, x.c1, x.c2, x.c3, x.c4]
  ofCoeffs l := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0⟩
  ofBase := Ext5.ofBase
  smul := Ext5.smul
  toSpec := Ext5.specEquiv
  length_coeffs _ := rfl
  toField_coeffs x i := by
    rw [Ext5.specEquiv_apply]
    by_cases hi : i < 5
    · rw [Ext5.coeffNat_toSpec _ hi]
      interval_cases i <;> rfl
    · rw [Ext.coeffNat_of_ge _ (by rw [Ext5.d_eq]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega),
        Montgomery.Native32.toField_zero]
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
