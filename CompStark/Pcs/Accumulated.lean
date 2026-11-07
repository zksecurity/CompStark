/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Sumcheck.Fold

/-! Shared-scalar updates of accumulated WHIR weights. -/
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Add a new weight table using one multiplier prepared for the entire table. -/
def addScaled {n : Nat} (scalar : CompStark.Sumcheck.Prepared)
    (acc values : Vector WordExt3 n) : Vector WordExt3 n :=
  Vector.ofFn fun i => WordExt3.add acc[i] (scalar.mul values[i])

/-- A shared-scalar update is the exact pointwise extension-field linear combination. -/
theorem addScaled_refines {n : Nat} (scalar : CompStark.Sumcheck.Prepared)
    (acc values : Vector WordExt3 n) (i : Fin n) :
    (addScaled scalar acc values)[i].toField =
      acc[i].toField + scalar.scalar.toField * values[i].toField := by
  simp only [addScaled, Fin.getElem_fin, Vector.getElem_ofFn, WordExt3.toField_add,
    scalar.mul_correct, WordExt3.toField_mul]

end CompStark.Pcs
