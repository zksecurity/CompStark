/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorValues

/-! Retained polynomial evaluation at the finite early-pack tensor endpoints. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- Retained-polynomial batching at a finite early-pack endpoint is its exact weighted sum. -/
theorem binaryValues_get (polynomials : Array PackedE) (point : Array W) (s : W) (i : Fin 16) :
    (binaryValues polynomials point (CompStark.Sumcheck.prepare s)).size = 16 ∧
    (binaryValues polynomials point (CompStark.Sumcheck.prepare s))[i.val]! =
      ∑ b ∈ Finset.range polynomials.size, if b%16 = i.val then
        (eqTable (point.extract 4 point.size))[b/16]! *
          evaluatePackedLoop polynomials[b]! (CompStark.Sumcheck.prepare s) polynomials[b]!.size 0
        else 0 := by
  let term (b : Nat) := (eqTable (point.extract 4 point.size))[b/16]! *
    evaluatePackedLoop polynomials[b]! (CompStark.Sumcheck.prepare s) polynomials[b]!.size 0
  let step (values : Array W) (b : Nat) := values.set! (b%16) (values[b%16]!+term b)
  have hg (values : Array W) (b : Nat) (hv : values.size = 16) :
      (step values b)[i.val]! = values[i.val]!+if b%16 = i.val then term b else 0 := by
    by_cases he : b%16 = i.val
    · simp only [step,he,ite_true]
      exact Array.getElem!_set!_self _ _ _ (by rw [hv]; exact i.isLt)
    · rw [ite_eq_right he]
      simp only [step,Array.getElem!_set!_ne _ _ _ _ he,add_zero]
  have hf := foldl_array_value_sum id step
    (fun b => if b%16 = i.val then term b else 0) i
    (by intro values b hv; exact (Array.size_set! ..).trans hv) hg
    (List.range polynomials.size) (Array.replicate 16 (lane 0)) (Array.size_replicate ..)
  simp only [binaryValues,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  change (((List.range polynomials.size).foldl step (Array.replicate 16 (lane 0))).size = 16) ∧ _
  have hz : (Array.replicate 16 (lane 0))[i.val]! = 0 := by
    rw [getElem!_pos _ _ (by simp only [Array.size_replicate]; exact i.isLt),Array.getElem_replicate]
    rfl
  simp only [id_eq] at hf
  rw [list_range_sum,hz,zero_add] at hf
  exact hf

/-- A contiguous natural-index sum is its row-major rectangular double sum. -/
theorem range_sum_blocks (f : Nat → W) (rows width : Nat) :
    (∑ i ∈ Finset.range (rows*width),f i) =
      ∑ row ∈ Finset.range rows, ∑ j ∈ Finset.range width,f (width*row+j) := by
  rw [← Fin.sum_univ_eq_sum_range]
  have h := (finProdFinEquiv (m := rows) (n := width)).sum_comp (fun i : Fin (rows*width) => f i.val)
  rw [Fintype.sum_prod_type] at h
  rw [← h]
  change (∑ row : Fin rows, ∑ j : Fin width,f (j.val+width*row.val)) = _
  trans ∑ row : Fin rows, ∑ j ∈ Finset.range width,f (j+width*row.val)
  · apply Finset.sum_congr rfl
    intro row _
    exact Fin.sum_univ_eq_sum_range (fun j => f (j+width*row.val)) width
  · rw [Fin.sum_univ_eq_sum_range (fun row => ∑ j ∈ Finset.range width,f (j+width*row)) rows]
    simp only [Nat.add_comm]

/-- Every finite tensor value batches exactly one residue from each sixteen-polynomial block. -/
theorem binaryValues_rows (polynomials : Array PackedE) (point : Array W) (s : W)
    (rows : Nat) (hs : polynomials.size = rows*16) (i : Fin 16) :
    (binaryValues polynomials point (CompStark.Sumcheck.prepare s))[i.val]! =
      ∑ row ∈ Finset.range rows, (eqTable (point.extract 4 point.size))[row]! *
        evaluatePackedLoop polynomials[16*row+i.val]! (CompStark.Sumcheck.prepare s)
          polynomials[16*row+i.val]!.size 0 := by
  rw [(binaryValues_get polynomials point s i).2,hs,range_sum_blocks]
  apply Finset.sum_congr rfl
  intro row _
  have hmod (j : Nat) (hj : j < 16) : (16*row+j)%16 = j := by omega
  have hdiv (j : Nat) (hj : j < 16) : (16*row+j)/16 = row := by omega
  trans ∑ j ∈ Finset.range 16, if j = i.val then
    (eqTable (point.extract 4 point.size))[row]! *
      evaluatePackedLoop polynomials[16*row+j]! (CompStark.Sumcheck.prepare s)
        polynomials[16*row+j]!.size 0 else 0
  · apply Finset.sum_congr rfl
    intro j hj
    rw [hmod j (Finset.mem_range.mp hj),hdiv j (Finset.mem_range.mp hj)]
  · rw [Finset.sum_ite_eq',ite_eq_left (Finset.mem_range.mpr i.isLt)]

end CompStark.Keccak.GkrProver
