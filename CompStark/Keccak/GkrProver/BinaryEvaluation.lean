/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeEarlyRounds

/-! Agreement between recursive Boolean factor interpolation and the native equality-weight table. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Boolean factor interpolation commutes with a common scalar. -/
theorem binaryInterpolate_scale (point : List W) (values : Nat → W) (weight : W) (row : Nat) :
    binaryInterpolate point (fun i => weight*values i) row = weight*binaryInterpolate point values row := by
  induction point generalizing values with
  | nil => rfl
  | cons r point ih => simp only [binaryInterpolate,ih]; ring

/-- Consecutive Boolean coordinate blocks compose their multilinear contractions. -/
theorem binaryInterpolate_append (low high : List W) (values : Nat → W) (row : Nat) :
    binaryInterpolate (low++high) values row =
      binaryInterpolate high (fun i => binaryInterpolate low values i) row := by
  induction low generalizing values with
  | nil => rfl
  | cons r low ih =>
    simp only [List.cons_append,binaryInterpolate,ih,binaryInterpolate_add,binaryInterpolate_scale]

/-- Recursive Boolean interpolation is the exact equality-weighted sum of its contiguous source block. -/
theorem binaryInterpolate_eqTable (point : Array W) (values : Nat → W) (row : Nat) :
    binaryInterpolate point.toList values row =
      ∑ i ∈ Finset.range (2^point.size),(eqTable point)[i]!*values (2^point.size*row+i) := by
  rcases point with ⟨xs⟩
  induction xs using List.reverseRecOn generalizing values row with
  | nil =>
    simp only [binaryInterpolate,Array.size,List.length_nil,pow_zero,
      Finset.sum_range_one,Nat.one_mul,Nat.add_zero]
    change values row = (1 : W)*values row
    rw [one_mul]
  | append_singleton xs r ih =>
    have he : ({toList := xs++[r]} : Array W) = xs.toArray.push r := by
      apply Array.toList_inj.mp
      simp only [Array.toList_push]
    rw [he]
    rw [Array.toList_push,binaryInterpolate_append]
    simp only [binaryInterpolate]
    rw [ih values (2*row),ih values (2*row+1)]
    rw [Array.size_push,pow_succ,show 2^xs.toArray.size*2 = 2^xs.toArray.size+2^xs.toArray.size by omega,
      Finset.sum_range_add]
    apply congrArg₂ (fun x y : W => x+y)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hw := eqTable_push_get xs.toArray r ⟨i,Finset.mem_range.mp hi⟩ (0 : Fin 2)
      simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero,ite_true] at hw
      rw [hw]
      have hindex : 2^xs.toArray.size*(2*row)+i =
          (2^xs.toArray.size+2^xs.toArray.size)*row+i := by ring
      rw [hindex]
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hw := eqTable_push_get xs.toArray r ⟨i,Finset.mem_range.mp hi⟩ (1 : Fin 2)
      simp only [Fin.val_one,Nat.mul_one,one_ne_zero,ite_false] at hw
      rw [show 2^xs.toArray.size+i = i+2^xs.toArray.size by omega,hw]
      have hindex : 2^xs.toArray.size*(2*row+1)+i =
          (2^xs.toArray.size+2^xs.toArray.size)*row+(i+2^xs.toArray.size) := by ring
      rw [hindex]
      ring

end CompStark.Keccak.GkrProver
