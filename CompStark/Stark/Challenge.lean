/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BaseField
public import CompPoly.Fields.Extension.Field
public import CompPoly.Fields.Extension.Bridge
public import Mathlib.Data.List.GetD

/-! # The challenge field

The STARK draws its challenges from an extension of its base field `F` (`BaseField`).
`Challenge F EF` makes an executable type `EF` such an extension: its operations, its coordinates
over `F`, and a ring isomorphism `toSpec` to the spec field `Ext params`, `F[X] / params.poly`,
under which every operation agrees with the spec field's. The verifier and the prover run on
`EF`; the analysis lives in `Challenge.Spec EF`, a finite field of `p ^ d` elements for `p = |F|`.

Generic helpers: base elements, powers, the basis `X ^ e`, and `OutsideBase`, each with its value
in the spec field.
-/

@[expose] public section
namespace CompStark

open CompPoly.Extension

/-- An executable extension field of the base field `F`: operations, coordinates over `F`, and the
ring isomorphism `toSpec` with the spec field `Ext params` that every operation agrees with. -/
class Challenge (F : outParam Type) [BaseField F] (EF : Type) extends Add EF, Sub EF, Neg EF,
    Mul EF, Inv EF, Zero EF, One EF, BEq EF, Inhabited EF where
  /-- The modulus of the spec field. -/
  params : ExtensionParams F
  [card : Fact (Nat.card F = params.q)]
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
  /-- Plonky3's identity of the algebra and its basis (`AlgebraIdentity::algebra_id`), which the
  transcript's domain separators bind. -/
  algebraId : String
  length_coeffs (x : EF) : (coeffs x).length = params.d
  coeffNat_toSpec (x : EF) (i : Nat) : Ext.coeffNat (toSpec x) i = (coeffs x).getD i 0
  toSpec_ofCoeffs (l : List F) : toSpec (ofCoeffs l) = Ext.ofFn fun i ↦ l.getD i 0
  toSpec_ofBase (x : F) : toSpec (ofBase x) = Ext.ofBase x
  toSpec_smul (x : F) (a : EF) : toSpec (smul x a) = x • toSpec a
  toSpec_zero : toSpec 0 = 0
  toSpec_one : toSpec 1 = 1
  toSpec_neg (a : EF) : toSpec (-a) = -toSpec a
  toSpec_sub (a b : EF) : toSpec (a - b) = toSpec a - toSpec b
  toSpec_inv (a : EF) : toSpec a⁻¹ = (toSpec a)⁻¹

namespace Challenge

attribute [instance] card irred lawfulBEq

variable {F : Type} [BaseField F] (EF : Type) [Challenge F EF]

/-- The spec field of `EF`, the `𝕂` of the analysis. -/
abbrev Spec : Type := Ext (params EF)

/-- The degree of the extension. -/
abbrev d : Nat := (params EF).d

variable {EF}

theorem q_eq : (params EF).q = Nat.card F := (card (EF := EF)).out.symm

/-- The spec field has `p ^ d` elements. -/
theorem card_spec : Fintype.card (Spec EF) = Nat.card F ^ d EF := by
  rw [Ext.card_ext, q_eq]

@[simp] theorem toSpec_add (a b : EF) : toSpec (a + b) = toSpec a + toSpec b :=
  (toSpec (EF := EF)).map_add' a b

@[simp] theorem toSpec_mul (a b : EF) : toSpec (a * b) = toSpec a * toSpec b :=
  (toSpec (EF := EF)).map_mul' a b

attribute [simp] toSpec_ofBase toSpec_smul toSpec_zero toSpec_one toSpec_neg toSpec_sub toSpec_inv

theorem toSpec_injective : Function.Injective (toSpec (EF := EF)) := (toSpec (EF := EF)).injective

/-- `ofCoeffs` inverts `coeffs`. -/
@[simp] theorem ofCoeffs_coeffs (x : EF) : ofCoeffs (coeffs x) = x := by
  refine toSpec_injective ?_
  rw [toSpec_ofCoeffs]
  ext i
  rw [Ext.coeff_ofFn, ← coeffNat_toSpec, Ext.coeffNat_coe]

/-- `toSpec` maps base elements to `algebraMap`. -/
theorem toSpec_ofBase' (x : F) : toSpec (ofBase (EF := EF) x) = algebraMap F (Spec EF) x :=
  toSpec_ofBase x

/-- An element is the sum of its coordinates times the powers of the spec field's generator. -/
theorem toSpec_eq_sum (x : EF) : toSpec x = ∑ e ∈ Finset.range (d EF),
    Ext.gen ^ e * algebraMap F (Spec EF) ((coeffs x).getD e 0) := by
  refine Ext.toQuot_injective ?_
  rw [Ext.toQuot_sum, Ext.toQuot, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Ext.toQuot_mul, Ext.toQuot_pow, Ext.toQuot_gen, Ext.algebraMap_eq_ofBase, Ext.toQuot_ofBase,
    ← Ext.coeffNat_coe, coeffNat_toSpec, mul_comm]

end Challenge

namespace Stark.Ext
open Challenge

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

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
  · rw [List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
      ite_eq_right (by omega)]

/-- An element outside the base field differs from every base element. -/
theorem toSpec_ne_algebraMap {z : EF} (hz : OutsideBase z) (y : F) :
    toSpec z ≠ algebraMap F (Spec EF) y := by
  obtain ⟨i, hi, hne⟩ := hz
  intro h
  have hc := congrArg (CompPoly.Extension.Ext.coeffNat · i) h
  simp only [coeffNat_toSpec, CompPoly.Extension.Ext.algebraMap_eq_ofBase] at hc
  apply hne
  rw [hc]
  by_cases hd : i < (params EF).d
  · rw [CompPoly.Extension.Ext.coeffNat_of_lt _ hd, CompPoly.Extension.Ext.ofBase,
      CompPoly.Extension.Ext.coeff_ofFn]
    split_ifs with h0
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp hi)
    · rfl
  · exact CompPoly.Extension.Ext.coeffNat_of_ge _ (by omega)

/-- An element is outside the base field exactly when it is no base element. -/
theorem outsideBase_iff {z : EF} : OutsideBase z ↔ ∀ y, toSpec z ≠ algebraMap F (Spec EF) y := by
  refine ⟨toSpec_ne_algebraMap, fun h ↦ ?_⟩
  by_contra hn
  apply h ((coeffs z).getD 0 0)
  have hs := Finset.sum_eq_single (s := Finset.range (d EF)) (a := 0)
    (f := fun e ↦ CompPoly.Extension.Ext.gen ^ e * algebraMap F (Spec EF)
      ((Challenge.coeffs z).getD e 0))
    (fun e _ he ↦ by
      have h0 : (coeffs z).getD e 0 = 0 := by
        by_contra hne
        exact hn ⟨e, Nat.pos_of_ne_zero he, hne⟩
      rw [show (Challenge.coeffs z).getD e 0 = 0 from h0, map_zero, mul_zero])
    (fun h0 ↦ absurd (Finset.mem_range.mpr (Challenge.params EF).d_pos) h0)
  rw [Challenge.toSpec_eq_sum, hs, pow_zero, one_mul]

/-- Multiplying by a nonzero base element keeps an element outside the base field. -/
theorem outsideBase_mul_ofBase {z : EF} (hz : OutsideBase z) {x : F} (hx : x ≠ 0) :
    OutsideBase (z * ofBase x) := by
  rw [outsideBase_iff] at *
  intro y hy
  have hx' : algebraMap F (Spec EF) x ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F (Spec EF)).injective]
    exact hx
  apply hz (y / x)
  rw [toSpec_mul, ofBase, toSpec_ofBase'] at hy
  rw [map_div₀, ← hy, mul_div_cancel_right₀ _ hx']

end Stark.Ext

end CompStark
