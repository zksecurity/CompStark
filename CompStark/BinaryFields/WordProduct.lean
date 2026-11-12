/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BinaryFields.Native
public import CompStark.Sumcheck.WordProductProofs
public import CompPoly.Fields.Binary.BF64.WordField

/-! Certified five-product arithmetic for native word-field consumers. -/

@[expose] public section
namespace CompStark.BinaryFields

/-- The five-product kernel agrees with the word field operation. -/
theorem fiveProduct_eq (a b : BF64.WordExt3) :
    CompStark.Sumcheck.extMulFive a b = a*b := CompStark.Sumcheck.extMulFive_eq a b

/-- A word field dictionary retaining the five-product kernel through generic consumers. -/
@[instance_reducible] def fiveProductField : Field BF64.WordExt3 :=
  fieldWithProduct CompStark.Sumcheck.extMulFive BF64.WordExt3.powWord fiveProduct_eq
    (fun _ _ => rfl)

/-- The certified dictionary preserves every word field operation. -/
@[csimp] theorem wordField_five : BF64.WordExt3.instField = fiveProductField :=
  (fieldWithProduct_eq _ _ _ _).symm

/-- The native cubic product agrees with five-point interpolation. -/
theorem wordProduct_five : BF64.WordExt3.mul = CompStark.Sumcheck.extMulFive := by
  funext a b
  exact (CompStark.Sumcheck.extMulFive_eq a b).symm

end CompStark.BinaryFields
