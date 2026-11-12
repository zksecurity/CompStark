/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.EarlyRounds

/-! Boolean suffix selection in the production tensor's little-endian ternary coordinates. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Interpolation of consecutive coordinate blocks composes their tensor contractions. -/
theorem tensorInterpolate_append (low high : List W) (values : Nat → W) (row : Nat) :
    tensorInterpolate (low++high) values row =
      tensorInterpolate high (fun i => tensorInterpolate low values i) row := by
  induction low generalizing values with
  | nil => rfl
  | cons r low ih =>
    simp only [List.cons_append,tensorInterpolate,ih,interpolateQuadratic,
      tensorInterpolate_add,tensorInterpolate_scale]

/-- A Boolean row's coordinates, in little-endian order, as extension-field endpoints. -/
def booleanSuffix (row : Nat) : Nat → List W
  | 0 => []
  | n+1 => (if row%2 = 0 then 0 else 1)::booleanSuffix (row/2) n

/-- A Boolean suffix contains exactly its prescribed number of coordinates. -/
theorem booleanSuffix_length (row bits : Nat) : (booleanSuffix row bits).length = bits := by
  induction bits generalizing row with
  | zero => rfl
  | succ bits ih => simp only [booleanSuffix,List.length_cons,ih]

/-- Boolean-to-ternary digit conversion separates the lowest bit from the shifted suffix. -/
theorem ternarySuffixIndex_succ (row bits : Nat) :
    ternarySuffixIndex row (bits+1) = row%2+3*ternarySuffixIndex (row/2) bits := by
  unfold ternarySuffixIndex
  rw [Finset.sum_range_succ']
  simp only [pow_zero,Nat.div_one,Nat.mul_one]
  rw [Finset.mul_sum]
  conv_lhs => rw [Nat.add_comm]
  apply congrArg (fun value : Nat => row%2+value)
  apply Finset.sum_congr rfl
  intro bit _
  rw [pow_succ',Nat.div_div_eq_div_mul]
  ring

/-- Interpolation at a Boolean suffix selects exactly its corresponding finite ternary row. -/
theorem tensorInterpolate_booleanSuffix (row bits : Nat) (values : Nat → W) (high : Nat) :
    tensorInterpolate (booleanSuffix row bits) values high =
      values (3^bits*high+ternarySuffixIndex row bits) := by
  induction bits generalizing row values with
  | zero => simp only [booleanSuffix,tensorInterpolate,pow_zero,Nat.one_mul,
      ternarySuffixIndex,Finset.range_zero,Finset.sum_empty,Nat.add_zero]
  | succ bits ih =>
    rw [booleanSuffix,tensorInterpolate,ih,ih,ih,ternarySuffixIndex_succ]
    by_cases hb : row%2 = 0
    · rw [ite_eq_left hb]
      simp only [interpolateQuadratic,add_zero,mul_zero,one_mul,zero_mul]
      apply congrArg values
      rw [hb,pow_succ]
      ring
    · have hb1 : row%2 = 1 := by have := Nat.mod_lt row (by decide : 0 < 2); omega
      rw [ite_eq_right hb]
      simp only [interpolateQuadratic,one_mul,CharTwo.add_self_eq_zero,zero_mul,zero_add,add_zero]
      apply congrArg values
      rw [hb1,pow_succ]
      ring

/-- Appending Boolean endpoints evaluates the prefix interpolation at its exact finite ternary row. -/
theorem tensorInterpolate_append_booleanSuffix (point : List W) (row bits : Nat) (values : Nat → W) :
    tensorInterpolate (point++booleanSuffix row bits) values 0 =
      tensorInterpolate point values (ternarySuffixIndex row bits) := by
  rw [tensorInterpolate_append,tensorInterpolate_booleanSuffix,Nat.mul_zero,Nat.zero_add]

/-- Early cofactor evaluation is the full tensor evaluated at the bound prefix and every Boolean suffix. -/
theorem earlyRound_evaluate_suffix (values entering bound : Array W) (hs : values.size = 81)
    (hb : bound.size ≤ 3) (r : W) :
    (earlyRound values entering bound)[0]!+
      r*((earlyRound values entering bound)[1]!+r*(earlyRound values entering bound)[2]!) =
        ∑ row ∈ Finset.range (eqTable (entering.extract (bound.size+1) 4)).size,
          (eqTable (entering.extract (bound.size+1) 4))[row]! *
            tensorInterpolate (bound.toList++[r]++booleanSuffix row (3-bound.size))
              (fun i => values[i]!) 0 := by
  rw [earlyRound_evaluate_tensor values entering bound hs hb]
  apply Finset.sum_congr rfl
  intro row _
  rw [tensorInterpolate_append_booleanSuffix]

end CompStark.Keccak.GkrProver
