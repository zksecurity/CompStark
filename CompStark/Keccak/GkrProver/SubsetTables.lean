/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.WeightMapProofs
public import CompStark.Keccak.GkrProver.QuadraticRounds

/-! Boolean subset-sum semantics of the native pack and input-opening lookup tables. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Appending a subset basis coefficient duplicates the old table with that coefficient added. -/
theorem subsets_push (values : Array W) (value : W) :
    subsets (values.push value) = subsets values ++ (subsets values).map (·+value) := by
  simp only [subsets,Array.forIn_pure_yield_eq_foldl,pure_bind,Array.foldl_push,Id.run_pure]

/-- A subset lookup table has one entry for every Boolean selection of its basis coefficients. -/
theorem subsets_size (values : Array W) : (subsets values).size = 2^values.size := by
  rcases values with ⟨xs⟩
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs value ih =>
    have he : ({toList := xs++[value]} : Array W) = xs.toArray.push value := by
      apply Array.toList_inj.mp
      simp only [Array.toList_push]
    rw [he,subsets_push]
    simp only [Array.size_append,Array.size_map,Array.size_push,pow_succ]
    change (subsets xs.toArray).size+(subsets xs.toArray).size = 2^xs.toArray.size*2
    rw [ih]
    change 2^xs.length+2^xs.length = 2^xs.length*2
    omega

/-- Appending a basis value preserves every subset sum that uses only the old bit positions. -/
theorem byteSubset_push_prefix (values : Array W) (value : W) (index : Nat) :
    byteSubset (fun k => (values.push value)[k]!) values.size index =
      byteSubset (fun k => values[k]!) values.size index := by
  unfold byteSubset
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [array_push_get_old _ _ _ (Finset.mem_range.mp hk)]

/-- Every production subset lookup is the exact sum of the basis values selected by its index bits. -/
theorem subsets_get (values : Array W) (index : Nat) (hi : index < 2^values.size) :
    (subsets values)[index]! = byteSubset (fun k => values[k]!) values.size index := by
  rcases values with ⟨xs⟩
  induction xs using List.reverseRecOn generalizing index with
  | nil =>
    have hz : index = 0 := by
      simp only [Array.size,List.length_nil,pow_zero] at hi
      omega
    subst index
    rfl
  | append_singleton xs value ih =>
    have he : ({toList := xs++[value]} : Array W) = xs.toArray.push value := by
      apply Array.toList_inj.mp
      simp only [Array.toList_push]
    rw [he] at hi ⊢
    rw [subsets_push]
    have hs := subsets_size xs.toArray
    by_cases hl : index < 2^xs.toArray.size
    · rw [getElem!_pos _ _ (by simp only [Array.size_append,Array.size_map,hs]; omega),
        Array.getElem_append_left (by rw [hs]; exact hl)]
      rw [← getElem!_pos _ _ (by rw [hs]; exact hl),ih index hl,Array.size_push,
        byteSubset_low _ _ _ hl,byteSubset_push_prefix]
    · have hh : index-2^xs.toArray.size < 2^xs.toArray.size := by
        simp only [Array.size_push,pow_succ] at hi
        omega
      rw [getElem!_pos _ _ (by simp only [Array.size_append,Array.size_map,hs]; omega),
        Array.getElem_append_right (by rw [hs]; omega)]
      simp only [Array.getElem_map,hs]
      rw [← getElem!_pos _ _ (by rw [hs]; exact hh),ih _ hh]
      have hindex : index = 2^xs.toArray.size+(index-2^xs.toArray.size) := by omega
      conv_rhs => rw [Array.size_push,hindex,byteSubset_high _ _ _ hh,byteSubset_push_prefix,
        array_push_get_last]

end CompStark.Keccak.GkrProver
