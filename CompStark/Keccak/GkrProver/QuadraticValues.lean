/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.QuadraticRounds

/-! Exact factor-sum invariants for the native quadratic opening loop. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The scaled dot product represented by the complete current pair of factor tables. -/
def quadraticTableValue (a b : Array W) (scale : W) : W :=
  scale*∑ j ∈ Finset.range a.size,a[j]!*b[j]!

/-- Folding either factor table retains exactly one row for each old pair. -/
theorem fold_rows_size (a : Array W) (width : Nat) (r : W) :
    (fold a width r).size = a.size/(2*width)*width := Array.size_ofFn ..

/-- Each folded row coordinate is the affine interpolation of the old paired rows. -/
theorem fold_row_get (a : Array W) (width : Nat) (r : W) (i j : Nat)
    (hi : i < a.size/(2*width)) (hj : j < width) :
    (fold a width r)[width*i+j]! =
      line a[2*i*width+j]! a[2*i*width+j+width]! r := by
  have hb : width*i+j < a.size/(2*width)*width := by nlinarith
  rw [getElem!_pos _ _ (by rw [fold_rows_size]; exact hb)]
  simp only [fold,Array.getElem_ofFn]
  have hd : (width*i+j)/width = i := by
    simpa only [Nat.mul_comm] using row_div hj i
  have hm : (width*i+j)%width = j := by
    simpa only [Nat.mul_comm] using row_mod hj i
  rw [hd,hm]
  have hindex : (2*i+1)*width+j = 2*i*width+j+width := by ring
  rw [hindex]

/-- The dot product of the folded factors is the exact bound quadratic polynomial. -/
theorem quadraticTableValue_fold (a b : Array W) (width : Nat) (scale r : W)
    (hab : a.size = b.size) :
    quadraticTableValue (fold a width r) (fold b width r) scale =
      quadraticRoundSum a b width scale r := by
  unfold quadraticTableValue
  rw [fold_rows_size,range_sum_blocks]
  apply congrArg (fun value : W => scale*value)
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [fold_row_get _ _ _ _ _ (Finset.mem_range.mp hi) (Finset.mem_range.mp hj),
    fold_row_get _ _ _ _ _ (by rw [← hab]; exact Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]

/-- Paired rows partition the complete entering dot product when the table has no incomplete row. -/
theorem quadraticBooleanSum_eq_value (a b : Array W) (width rows : Nat) (scale : W)
    (hw : 0 < width) (ha : a.size = rows*(2*width)) :
    quadraticBooleanSum a b width scale = quadraticTableValue a b scale := by
  unfold quadraticBooleanSum quadraticTableValue
  rw [ha,Nat.mul_div_cancel _ (by omega),range_sum_blocks]
  apply congrArg (fun value : W => scale*value)
  apply Finset.sum_congr rfl
  intro i _
  rw [show 2*width = width+width by omega,Finset.sum_range_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h0 : (width+width)*i+j = 2*i*width+j := by ring
  have h1 : (width+width)*i+(width+j) = 2*i*width+j+width := by ring
  rw [h0,h1]

/-- One production quadratic transition preserves the exact factor-sum running claim. -/
theorem quadraticStep_value (state : QuadraticResult) (width rows : Nat) (scale : W)
    (hw : 0 < width) (ha : state.a.size = rows*(2*width))
    (hab : state.a.size = state.b.size)
    (hv : state.value = quadraticTableValue state.a state.b scale) :
    (quadraticStep width scale state).value =
      quadraticTableValue (quadraticStep width scale state).a
        (quadraticStep width scale state).b scale := by
  dsimp only [quadraticStep]
  rw [hv,← quadraticBooleanSum_eq_value _ _ width rows scale hw ha,
    quadraticCoefficients_decode,quadraticTableValue_fold _ _ _ _ _ hab]

/-- All opening transitions preserve the exact running claim and the suffix-cube table shape. -/
theorem quadraticRun_invariant (initial : QuadraticResult) (width : Nat) (scale : W)
    (hw : 0 < width) (hab : initial.a.size = initial.b.size)
    (hv : initial.value = quadraticTableValue initial.a initial.b scale)
    (n remaining : Nat) (ha : initial.a.size = 2^(n+remaining)*width) :
    let final := quadraticRun width scale initial n
    final.a.size = 2^remaining*width ∧ final.a.size = final.b.size ∧
      final.value = quadraticTableValue final.a final.b scale := by
  induction n generalizing remaining with
  | zero => exact ⟨by simpa only [Nat.zero_add,quadraticRun] using ha,hab,hv⟩
  | succ n ih =>
    have hh := ih (remaining+1) (by simpa only [Nat.add_assoc,Nat.add_comm 1] using ha)
    let state := quadraticRun width scale initial n
    have hs : state.a.size = 2^remaining*(2*width) := by
      rw [hh.1,pow_succ,Nat.mul_assoc]
    have hv' := quadraticStep_value state width (2^remaining) scale hw hs hh.2.1 hh.2.2
    change (quadraticStep width scale state).a.size = _ ∧ _
    refine ⟨?_,?_,hv'⟩
    · dsimp only [quadraticStep]
      rw [fold_rows_size,hs,Nat.mul_div_cancel _ (by omega)]
    · change (quadraticStep width scale state).a.size = (quadraticStep width scale state).b.size
      simp only [quadraticStep,fold_rows_size]
      exact congrArg (fun size : Nat => size/(2*width)*width) hh.2.1

/-- The complete production opening run reaches an exact scaled terminal column dot product. -/
theorem proveQuadratics_value (writer : Writer) (a b : Array W) (width : Nat) (scale : W)
    (rounds : Nat) (hw : 0 < width) (ha : a.size = 2^rounds*width)
    (hab : a.size = b.size) :
    let final := proveQuadratics writer a b width scale (quadraticTableValue a b scale) rounds
    final.a.size = width ∧ final.b.size = width ∧
      final.value = scale*∑ j ∈ Finset.range width,final.a[j]!*final.b[j]! := by
  rw [proveQuadratics_eq_run]
  have hh := quadraticRun_invariant ⟨a,b,#[],#[],quadraticTableValue a b scale,writer⟩
    width scale hw hab rfl rounds 0 (by simpa only [Nat.add_zero] using ha)
  simp only [pow_zero,one_mul] at hh
  refine ⟨hh.1,hh.2.1.symm.trans hh.1,?_⟩
  rw [hh.2.2,quadraticTableValue,hh.1]

end CompStark.Keccak.GkrProver
