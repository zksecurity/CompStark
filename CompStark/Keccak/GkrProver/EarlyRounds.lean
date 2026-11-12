/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeTensorContraction

/-! Cofactor coefficient semantics for all four early native pack rounds. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The ternary index of a Boolean suffix, leaving its lowest coordinate free. -/
def earlySuffixIndex (row bits : Nat) : Nat :=
  ∑ bit ∈ Finset.range bits, ((row/2^bit)%2)*3^(bit+1)

/-- The native suffix-index loop is the exact little-endian Boolean-to-ternary digit conversion. -/
theorem earlySuffixIndex_fold (row bits : Nat) :
    (List.range bits).foldl (fun state bit =>
      (state.1+((row/2^bit)%2)*state.2,state.2*3)) (0,3) =
      (earlySuffixIndex row bits,3^(bits+1)) := by
  induction bits with
  | zero => simp only [List.range_zero,List.foldl_nil,earlySuffixIndex,Finset.range_zero,
      Finset.sum_empty,Nat.zero_add,pow_one]
  | succ bits ih =>
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    simp only [earlySuffixIndex,Finset.sum_range_succ,pow_succ]

/-- The three exact endpoint sums selected from the contracted production tensor. -/
def earlyRoundSums (values entering bound : Array W) (c : Fin 3) : W :=
  ∑ row ∈ Finset.range (eqTable (entering.extract (bound.size+1) 4)).size,
    (eqTable (entering.extract (bound.size+1) 4))[row]! *
      (bindEarly values bound)[earlySuffixIndex row (3-bound.size)+c.val]!

/-- The actual early pack loop transmits precisely its three quadratic cofactor coefficients. -/
theorem earlyRound_eq (values entering bound : Array W) :
    earlyRound values entering bound =
      #[earlyRoundSums values entering bound 0,
        earlyRoundSums values entering bound 0+earlyRoundSums values entering bound 1+
          earlyRoundSums values entering bound 2,
        earlyRoundSums values entering bound 2] := by
  let term (row c : Nat) := (eqTable (entering.extract (bound.size+1) 4))[row]! *
    (bindEarly values bound)[earlySuffixIndex row (3-bound.size)+c]!
  let step (state : W × W × W) (row : Nat) :=
    (state.1+term row 0,state.2.1+term row 1,state.2.2+term row 2)
  have h0 := foldl_value_sum (fun state : W × W × W => state.1) step (fun row => term row 0)
    (fun _ _ => rfl) (List.range (eqTable (entering.extract (bound.size+1) 4)).size) (0,0,0)
  have h1 := foldl_value_sum (fun state : W × W × W => state.2.1) step (fun row => term row 1)
    (fun _ _ => rfl) (List.range (eqTable (entering.extract (bound.size+1) 4)).size) (0,0,0)
  have h2 := foldl_value_sum (fun state : W × W × W => state.2.2) step (fun row => term row 2)
    (fun _ _ => rfl) (List.range (eqTable (entering.extract (bound.size+1) 4)).size) (0,0,0)
  simp only [list_range_sum,zero_add] at h0 h1 h2
  simp only [earlyRound,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range',earlySuffixIndex_fold]
  change #[((List.range _).foldl step (0,0,0)).1,
    ((List.range _).foldl step (0,0,0)).1+((List.range _).foldl step (0,0,0)).2.1+
      ((List.range _).foldl step (0,0,0)).2.2,
    ((List.range _).foldl step (0,0,0)).2.2] = _
  rw [h0,h1,h2]
  rfl

/-- Early cofactor evaluation is quadratic endpoint interpolation of its complete suffix sums. -/
theorem earlyRound_evaluate (values entering bound : Array W) (r : W) :
    (earlyRound values entering bound)[0]!+
      r*((earlyRound values entering bound)[1]!+r*(earlyRound values entering bound)[2]!) =
        interpolateQuadratic (earlyRoundSums values entering bound 0)
          (earlyRoundSums values entering bound 1) (earlyRoundSums values entering bound 2) r := by
  rw [earlyRound_eq]
  exact interpolateQuadratic_eq _ _ _ _

/-- A free ternary digit and any converted Boolean suffix stay within their complete tensor row block. -/
theorem earlySuffixIndex_bound (row bits : Nat) (c : Fin 3) :
    earlySuffixIndex row bits+c.val < 3^(bits+1) := by
  induction bits with
  | zero => simpa only [earlySuffixIndex,Finset.range_zero,Finset.sum_empty,Nat.zero_add,pow_one] using c.isLt
  | succ bits ih =>
    have hb : (row/2^bits)%2 < 2 := Nat.mod_lt _ (by decide)
    have hp : 0 < 3^(bits+1) := by positivity
    simp only [earlySuffixIndex,Finset.sum_range_succ] at *
    rw [pow_succ (n := bits+1)]
    nlinarith

/-- Every early coefficient is a complete equality-weighted suffix sum of the original production tensor. -/
theorem earlyRoundSums_tensor (values entering bound : Array W) (hs : values.size = 81)
    (hb : bound.size ≤ 3) (c : Fin 3) :
    earlyRoundSums values entering bound c =
      ∑ row ∈ Finset.range (eqTable (entering.extract (bound.size+1) 4)).size,
        (eqTable (entering.extract (bound.size+1) 4))[row]! *
          tensorInterpolate bound.toList (fun i => values[i]!)
            (earlySuffixIndex row (3-bound.size)+c.val) := by
  unfold earlyRoundSums
  apply Finset.sum_congr rfl
  intro row _
  apply congrArg (fun value : W => (eqTable (entering.extract (bound.size+1) 4))[row]!*value)
  apply bindEarly_get values bound (3^(4-bound.size))
  · rw [hs,← pow_add,show bound.size+(4-bound.size) = 4 by omega]
    decide
  · have h := earlySuffixIndex_bound row (3-bound.size) c
    simpa only [show 3-bound.size+1 = 4-bound.size by omega] using h

/-- Interpolating an appended high coordinate contracts the three already-interpolated prefix blocks. -/
theorem tensorInterpolate_append_singleton (point : List W) (values : Nat → W) (r : W) (row : Nat) :
    tensorInterpolate (point++[r]) values row =
      interpolateQuadratic (tensorInterpolate point values (3*row))
        (tensorInterpolate point values (3*row+1)) (tensorInterpolate point values (3*row+2)) r := by
  induction point generalizing values with
  | nil => rfl
  | cons s point ih =>
    simp only [List.cons_append,tensorInterpolate,ih,interpolateQuadratic]
    ring

/-- The ternary digits of the remaining Boolean coordinates, without the free low digit. -/
def ternarySuffixIndex (row bits : Nat) : Nat :=
  ∑ bit ∈ Finset.range bits, ((row/2^bit)%2)*3^bit

/-- The production suffix index leaves precisely one free ternary coordinate below its Boolean digits. -/
theorem earlySuffixIndex_eq (row bits : Nat) :
    earlySuffixIndex row bits = 3*ternarySuffixIndex row bits := by
  unfold earlySuffixIndex ternarySuffixIndex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  rw [pow_succ]
  ring

/-- Quadratic endpoint interpolation commutes with every finite sum of endpoint triples. -/
theorem interpolateQuadratic_finset_sum {A : Type} (indices : Finset A) (f : A → Nat → W) (r : W) :
    interpolateQuadratic (∑ a ∈ indices,f a 0) (∑ a ∈ indices,f a 1) (∑ a ∈ indices,f a 2) r =
      ∑ a ∈ indices,interpolateQuadratic (f a 0) (f a 1) (f a 2) r :=
  tensorInterpolate_finset_sum indices f [r] 0

/-- Quadratic endpoint interpolation commutes with a common scalar on its three endpoints. -/
theorem interpolateQuadratic_scale (a b c r weight : W) :
    interpolateQuadratic (weight*a) (weight*b) (weight*c) r =
      weight*interpolateQuadratic a b c r := by
  unfold interpolateQuadratic
  ring

/-- Evaluating an early native cofactor binds the next coordinate in every equality-weighted suffix row. -/
theorem earlyRound_evaluate_tensor (values entering bound : Array W) (hs : values.size = 81)
    (hb : bound.size ≤ 3) (r : W) :
    (earlyRound values entering bound)[0]!+
      r*((earlyRound values entering bound)[1]!+r*(earlyRound values entering bound)[2]!) =
        ∑ row ∈ Finset.range (eqTable (entering.extract (bound.size+1) 4)).size,
          (eqTable (entering.extract (bound.size+1) 4))[row]! *
            tensorInterpolate (bound.toList++[r]) (fun i => values[i]!)
              (ternarySuffixIndex row (3-bound.size)) := by
  rw [earlyRound_evaluate,earlyRoundSums_tensor values entering bound hs hb,
    earlyRoundSums_tensor values entering bound hs hb,earlyRoundSums_tensor values entering bound hs hb]
  simp only [earlySuffixIndex_eq,Fin.val_zero,Fin.val_one,show (2 : Fin 3).val = 2 from rfl]
  rw [interpolateQuadratic_finset_sum
    (Finset.range (eqTable (entering.extract (bound.size+1) 4)).size)
    (fun row i => (eqTable (entering.extract (bound.size+1) 4))[row]! *
      tensorInterpolate bound.toList (fun k => values[k]!) (3*ternarySuffixIndex row (3-bound.size)+i)) r]
  apply Finset.sum_congr rfl
  intro row _
  rw [tensorInterpolate_append_singleton]
  exact interpolateQuadratic_scale _ _ _ _ _

end CompStark.Keccak.GkrProver
