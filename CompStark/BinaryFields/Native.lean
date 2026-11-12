/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BinaryFields.Basic
public import CompPoly.Fields.Binary.BF64.WordField
public import Mathlib.Algebra.Ring.Ext

/-! Certified machine-word arithmetic for native verifier computation. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 8192

@[expose] public section
namespace CompStark.BinaryFields

/-- Multiply specification base-field values through the masked word kernel. -/
def mulNative (a b : K) : K :=
  BF64.Word.toField (BF64.Word.mulMasked (BF64.Word.ofField a) (BF64.Word.ofField b))

/-- The native base-field product has the exact specification coordinates. -/
theorem mulNative_eq (a b : K) : mulNative a b = a * b := by
  rw [mulNative, BF64.Word.toField_mulMasked, BF64.Word.toField_ofField,
    BF64.Word.toField_ofField]

/-- Replace the compiled natural-number product by the certified machine-word kernel. -/
@[csimp] theorem mulNat_native : BF64.mulNat = mulNative := by
  funext a b
  rw [mulNative_eq, ← BF64.mul_eq_mulNat]
  rfl

/-- A field dictionary retaining the certified machine-word product in generic algorithms. -/
@[instance_reducible] def nativeField : Field K := by
  letI : Mul K := ⟨mulNative⟩
  let ring : CommRing K := Function.Injective.commRing id Function.injective_id
    rfl rfl (fun _ _ => rfl) mulNative_eq (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have ring_eq : ring = BF64.instCommRing :=
    CommRing.ext rfl (funext fun a => funext fun b => mulNative_eq a b)
  letI : CommRing K := ring
  exact { BF64.instField with
    toCommRing := ring
    div := fun a b => mulNative a (BF64.invItohTsujii b)
    div_eq_mul_inv := fun _ _ => rfl
    mul_inv_cancel := by rw [ring_eq]; exact BF64.instField.mul_inv_cancel
    zpow_succ' := by rw [ring_eq]; exact BF64.instField.zpow_succ'
    nnratCast_def := by
      intro q
      change _ = mulNative _ _
      rw [mulNative_eq]
      exact BF64.instField.nnratCast_def q
    nnqsmul_def := by rw [ring_eq]; exact BF64.instField.nnqsmul_def
    ratCast_def := by
      intro q
      change _ = mulNative _ _
      rw [mulNative_eq]
      exact BF64.instField.ratCast_def q
    qsmul_def := by rw [ring_eq]; exact BF64.instField.qsmul_def }

/-- Generic field consumers receive the exact same operations through the word dictionary. -/
@[csimp] theorem field_native : BF64.instField = nativeField := by
  symm
  unfold nativeField
  simp only [show (fun a b => mulNative a (BF64.invItohTsujii b)) =
    (fun a b => a * BF64.invItohTsujii b) from funext fun a => funext fun b => mulNative_eq _ _]
  congr 1
  exact CommRing.ext rfl (funext fun a => funext fun b => mulNative_eq a b)

section
variable {F : Type} [spec : Field F]
/-- Retain a certified product and binary power in a generic field dictionary. -/
@[instance_reducible] def fieldWithProduct (product : F → F → F) (power : F → Nat → F)
    (hm : ∀ a b, product a b = a*b) (hp : ∀ a n, power a n = a^n) : Field F := by
  letI : Mul F := ⟨product⟩
  letI : Pow F Nat := ⟨power⟩
  let ring : CommRing F := Function.Injective.commRing id Function.injective_id
    rfl rfl (fun _ _ => rfl) hm (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) hp (fun _ => rfl) (fun _ => rfl)
  have ring_eq : ring = spec.toCommRing := CommRing.ext rfl (funext fun a => funext fun b => hm a b)
  letI : CommRing F := ring
  exact { spec with
    toCommRing := ring
    mul_inv_cancel := by rw [ring_eq]; exact spec.mul_inv_cancel
    zpow_succ' := by rw [ring_eq]; exact spec.zpow_succ'
    div_eq_mul_inv := by rw [ring_eq]; exact spec.div_eq_mul_inv
    nnqsmul_def := by rw [ring_eq]; exact spec.nnqsmul_def
    qsmul_def := by rw [ring_eq]; exact spec.qsmul_def }
/-- Certified operations preserve the complete field dictionary. -/
theorem fieldWithProduct_eq (product : F → F → F) (power : F → Nat → F)
    (hm : ∀ a b, product a b = a*b) (hp : ∀ a n, power a n = a^n) :
    fieldWithProduct product power hm hp = spec := by
  cases spec
  unfold fieldWithProduct
  dsimp only
  congr 1
  exact CommRing.ext rfl (funext fun a => funext fun b => hm a b)
end

/-- A monomorphic specification dictionary allows certified compiler substitution for E. -/
instance extensionFieldSpec : Field E := inferInstance

/-- Six-product extension multiplication through the three-word carrier. -/
def mulExtensionNative (a b : E) : E :=
  BF64.WordExt3.toField (BF64.WordExt3.mul (BF64.WordExt3.ofField a) (BF64.WordExt3.ofField b))

/-- The three-word product agrees with every specification extension product. -/
theorem mulExtensionNative_eq (a b : E) : mulExtensionNative a b = a * b := by
  rw [mulExtensionNative, BF64.WordExt3.toField_mul, BF64.WordExt3.toField_ofField,
    BF64.WordExt3.toField_ofField]

/-- Binary extension powers retain their three-word carrier throughout the loop. -/
def powerExtensionNative (a : E) (n : Nat) : E :=
  BF64.WordExt3.toField (BF64.WordExt3.powWord (BF64.WordExt3.ofField a) n)

/-- Binary word powers equal the exact extension-field powers. -/
theorem powerExtensionNative_eq (a : E) (n : Nat) : powerExtensionNative a n = a ^ n := by
  rw [powerExtensionNative, BF64.WordExt3.toField_powWord, BF64.WordExt3.toField_ofField]

/-- The extension dictionary retains word products and powers in generic round checks. -/
@[instance_reducible] def nativeExtensionField : Field E :=
  fieldWithProduct mulExtensionNative powerExtensionNative
    mulExtensionNative_eq powerExtensionNative_eq

/-- Every generic extension-field operation receives the exactly equal native dictionary. -/
@[csimp] theorem extension_field_native : extensionFieldSpec = nativeExtensionField :=
  (fieldWithProduct_eq _ _ _ _).symm

/-- Certified word dictionary for extension-field products. -/
@[instance_reducible] def nativeExtensionRing : CommRing E := nativeExtensionField.toCommRing
/-- Monomorphic specification dictionary for certified native compilation. -/
instance extensionRingSpec : CommRing E := extensionFieldSpec.toCommRing
/-- The compiler substitution preserves every specification operation. -/
@[csimp] theorem extension_ring_native : extensionRingSpec = nativeExtensionRing := by
  change extensionFieldSpec.toCommRing = nativeExtensionField.toCommRing
  rw [extension_field_native]
/-- Certified word dictionary for extension-field products. -/
@[instance_reducible] def nativeExtensionMonoid : CommMonoid E := nativeExtensionField.toCommMonoid
/-- Monomorphic specification dictionary for certified native compilation. -/
instance extensionMonoidSpec : CommMonoid E := extensionFieldSpec.toCommMonoid
/-- The compiler substitution preserves every specification operation. -/
@[csimp] theorem extension_monoid_native : extensionMonoidSpec = nativeExtensionMonoid := by
  change extensionFieldSpec.toCommMonoid = nativeExtensionField.toCommMonoid
  rw [extension_field_native]
/-- Certified word dictionary for extension-field products. -/
@[instance_reducible] def nativeExtensionMul : Mul E := ⟨mulExtensionNative⟩
/-- Monomorphic specification dictionary for certified native compilation. -/
instance extensionMulSpec : Mul E := inferInstance
/-- The compiler substitution preserves every specification operation. -/
@[csimp] theorem extension_mul_native : extensionMulSpec = nativeExtensionMul := by
  unfold extensionMulSpec nativeExtensionMul
  exact congrArg Mul.mk (funext fun a => funext fun b => (mulExtensionNative_eq a b).symm)
/-- Certified word dictionary for extension-field powers. -/
@[instance_reducible] def nativeExtensionPow : Pow E Nat := ⟨powerExtensionNative⟩
/-- Monomorphic specification dictionary for certified native compilation. -/
instance extensionPowSpec : Pow E Nat := inferInstance
/-- The compiler substitution preserves every specification operation. -/
@[csimp] theorem extension_pow_native : extensionPowSpec = nativeExtensionPow := by
  unfold extensionPowSpec nativeExtensionPow
  exact congrArg Pow.mk (funext fun a => funext fun n => (powerExtensionNative_eq a n).symm)
/-- Certified word dictionary for base-field products. -/
@[instance_reducible] def nativeBaseRing : CommRing K := nativeField.toCommRing
/-- Monomorphic specification dictionary for certified native compilation. -/
instance baseRingSpec : CommRing K := BF64.instCommRing
/-- The compiler substitution preserves every specification operation. -/
@[csimp] theorem base_ring_native : baseRingSpec = nativeBaseRing := by
  change BF64.instField.toCommRing = nativeField.toCommRing
  rw [field_native]
/-- Certified word dictionary for base-field products. -/
@[instance_reducible] def nativeBaseMonoid : CommMonoid K := nativeField.toCommMonoid
/-- Monomorphic specification dictionary for certified native compilation. -/
instance baseMonoidSpec : CommMonoid K := BF64.instCommRing.toCommMonoid
/-- The compiler substitution preserves every specification operation. -/
@[csimp] theorem base_monoid_native : baseMonoidSpec = nativeBaseMonoid := by
  change BF64.instField.toCommMonoid = nativeField.toCommMonoid
  rw [field_native]
/-- Certified word dictionary for base-field products. -/
@[instance_reducible] def nativeBaseMul : Mul K := ⟨mulNative⟩
/-- Monomorphic specification dictionary for certified native compilation. -/
instance baseMulSpec : Mul K := inferInstance
/-- The compiler substitution preserves every specification operation. -/
@[csimp] theorem base_mul_native : baseMulSpec = nativeBaseMul := by
  unfold baseMulSpec nativeBaseMul
  exact congrArg Mul.mk (funext fun a => funext fun b => (mulNative_eq a b).symm)

end CompStark.BinaryFields
