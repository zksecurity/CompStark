/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.Tensor
public import CompStark.Sumcheck.Fold

/-! Word-carrier compressed quadratic messages over blocked or adjacent pairs. -/
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Low input coordinate of an interleaved blocked pair. -/
def roundLow (rows width : Nat) (i : Fin (rows * width)) : Fin (2 * rows * width) :=
  ⟨2 * (i.val / width) * width + i.val % width, (CompStark.Sumcheck.pairIndex_lt rows width i).1⟩

/-- High input coordinate of an interleaved blocked pair. -/
def roundHigh (rows width : Nat) (i : Fin (rows * width)) : Fin (2 * rows * width) :=
  ⟨(2 * (i.val / width) + 1) * width + i.val % width, (CompStark.Sumcheck.pairIndex_lt rows width i).2⟩

/-- Constant and quadratic coefficients of the honest weighted pair interpolation. -/
def roundCoefficients (rows width : Nat) (table weights : Vector WordExt3 (2 * rows * width)) :
    Vector WordExt3 2 :=
  let low := roundLow rows width
  let high := roundHigh rows width
  #v[sumWords (List.ofFn fun i => WordExt3.mul table[low i] weights[low i]),
    sumWords (List.ofFn fun i => WordExt3.mul (WordExt3.add table[low i] table[high i])
      (WordExt3.add weights[low i] weights[high i]))]

/-- The constant message coefficient is the exact sum of low endpoint products. -/
theorem roundCoefficients_constant (rows width : Nat)
    (table weights : Vector WordExt3 (2 * rows * width)) :
    (roundCoefficients rows width table weights)[0].toField =
      ∑ i : Fin (rows * width), table[roundLow rows width i].toField *
        weights[roundLow rows width i].toField := by
  change (sumWords (List.ofFn fun i => WordExt3.mul table[roundLow rows width i]
    weights[roundLow rows width i])).toField = _
  simp only [sumWords_refines, List.map_ofFn, Function.comp_apply, WordExt3.toField_mul, List.sum_ofFn]

/-- The quadratic coefficient is the exact sum of endpoint differences' products. -/
theorem roundCoefficients_quadratic (rows width : Nat)
    (table weights : Vector WordExt3 (2 * rows * width)) :
    (roundCoefficients rows width table weights)[1].toField =
      ∑ i : Fin (rows * width),
        (table[roundLow rows width i].toField + table[roundHigh rows width i].toField) *
        (weights[roundLow rows width i].toField + weights[roundHigh rows width i].toField) := by
  change (sumWords (List.ofFn fun i => WordExt3.mul
    (WordExt3.add table[roundLow rows width i] table[roundHigh rows width i])
    (WordExt3.add weights[roundLow rows width i] weights[roundHigh rows width i]))).toField = _
  simp only [sumWords_refines, List.map_ofFn, Function.comp_apply,
    WordExt3.toField_mul, WordExt3.toField_add, List.sum_ofFn]

end CompStark.Pcs
