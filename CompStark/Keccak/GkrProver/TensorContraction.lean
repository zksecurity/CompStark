/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorProofs
public import CompStark.Keccak.GkrProver.Cofactor

/-! Quadratic interpolation semantics of the native ternary tensor contractions. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64 Polynomial
open scoped BigOperators

/-- Interpolate a quadratic from its zero, one and leading-coefficient endpoints. -/
def interpolateQuadratic (a b c r : W) : W := (1+r)*a+r*b+(r+r*r)*c

/-- The scalar expression in the production tensor loop is endpoint interpolation. -/
theorem interpolateQuadratic_eq (a b c r : W) :
    a+r*(a+b+c+r*c) = interpolateQuadratic a b c r := by
  unfold interpolateQuadratic
  ring

/-- Endpoint interpolation recovers every polynomial of degree at most two. -/
theorem interpolateQuadratic_polynomial (P : W⦃≤ 2⦄[X]) (r : W) :
    interpolateQuadratic (P.val.eval 0) (P.val.eval 1) (P.val.coeff 2) r = P.val.eval r := by
  rw [quadratic_polynomial_eval P 0,quadratic_polynomial_eval P 1,
    quadratic_polynomial_eval P r]
  simp only [zero_pow (by decide : 2 ≠ 0),one_pow,mul_zero,mul_one,add_zero]
  unfold interpolateQuadratic
  have hz := CharTwo.add_self_eq_zero (r*P.val.coeff 0+r*P.val.coeff 2)
  linear_combination hz

/-- A tensor product of quadratic endpoint bases, in little-endian ternary order. -/
def tensorInterpolate : List W → (Nat → W) → Nat → W
  | [], values, row => values row
  | r::point, values, row =>
      interpolateQuadratic
        (tensorInterpolate point (fun i => values (3*i)) row)
        (tensorInterpolate point (fun i => values (3*i+1)) row)
        (tensorInterpolate point (fun i => values (3*i+2)) row) r

/-- Tensor interpolation is additive in the complete endpoint table. -/
theorem tensorInterpolate_add (point : List W) (a b : Nat → W) (row : Nat) :
    tensorInterpolate point (fun i => a i+b i) row =
      tensorInterpolate point a row+tensorInterpolate point b row := by
  induction point generalizing a b with
  | nil => rfl
  | cons r point ih =>
    simp only [tensorInterpolate,ih,interpolateQuadratic]
    ring

/-- Tensor interpolation commutes with a shared extension-field scalar. -/
theorem tensorInterpolate_scale (point : List W) (a : Nat → W) (scale : W) (row : Nat) :
    tensorInterpolate point (fun i => scale*a i) row = scale*tensorInterpolate point a row := by
  induction point generalizing a with
  | nil => rfl
  | cons r point ih =>
    simp only [tensorInterpolate,ih,interpolateQuadratic]
    ring

/-- Contracting the low coordinate commutes with interpolation of all remaining coordinates. -/
theorem tensorInterpolate_contract (point : List W) (values : Nat → W) (r : W) (row : Nat) :
    tensorInterpolate point (fun i => interpolateQuadratic (values (3*i))
      (values (3*i+1)) (values (3*i+2)) r) row =
      tensorInterpolate (r::point) values row := by
  simp only [interpolateQuadratic,tensorInterpolate_add,tensorInterpolate_scale]
  rfl

/-- One complete contraction of an array's lowest ternary coordinate. -/
def contractEarly (values : Array W) (r : W) : Array W :=
  Array.ofFn fun i : Fin (values.size/3) =>
    interpolateQuadratic values[3*i.val]! values[3*i.val+1]! values[3*i.val+2]! r

/-- One native tensor contraction removes exactly one ternary coordinate. -/
theorem contractEarly_size (values : Array W) (r : W) :
    (contractEarly values r).size = values.size/3 := Array.size_ofFn

/-- Every in-bounds native contraction evaluates its three endpoint cells. -/
theorem contractEarly_get (values : Array W) (r : W) (i : Nat) (hi : i < values.size/3) :
    (contractEarly values r)[i]! =
      interpolateQuadratic values[3*i]! values[3*i+1]! values[3*i+2]! r := by
  rw [getElem!_pos _ i (by rw [contractEarly_size]; exact hi)]
  simp only [contractEarly,Array.getElem_ofFn]

/-- The production binding loop is the structural fold over endpoint contractions. -/
theorem bindEarly_eq_fold (values point : Array W) :
    bindEarly values point = point.toList.foldl contractEarly values := by
  simp only [bindEarly,Array.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure]
  simp only [← Array.foldl_toList]
  congr 1
  funext values r
  apply Array.ext
  · simp only [Array.size_ofFn,contractEarly_size]
  · intro i hi hj
    simp only [Array.getElem_ofFn,contractEarly]
    exact interpolateQuadratic_eq _ _ _ _

/-- Tensor interpolation only reads the contiguous ternary block belonging to its retained row. -/
theorem tensorInterpolate_congr (point : List W) (a b : Nat → W) (row : Nat)
    (h : ∀ i, 3^point.length*row ≤ i → i < 3^point.length*(row+1) → a i = b i) :
    tensorInterpolate point a row = tensorInterpolate point b row := by
  induction point generalizing a b with
  | nil =>
    apply h row
    · simp only [List.length_nil,pow_zero,one_mul,le_refl]
    · simp only [List.length_nil,pow_zero,one_mul]; omega
  | cons r point ih =>
    simp only [tensorInterpolate]
    congr 1
    all_goals apply ih; intro i hlo hhi; apply h
    all_goals simp only [List.length_cons,pow_succ]; nlinarith

/-- A structural sequence of native contractions is exact quadratic tensor interpolation. -/
theorem contractEarly_fold_get (point : List W) (values : Array W) (rows : Nat)
    (hsize : values.size = 3^point.length*rows) (row : Nat) (hrow : row < rows) :
    (point.foldl contractEarly values)[row]! =
      tensorInterpolate point (fun i => values[i]!) row := by
  induction point generalizing values with
  | nil => rfl
  | cons r point ih =>
    rw [List.foldl_cons,ih]
    · rw [← tensorInterpolate_contract]
      apply tensorInterpolate_congr
      intro i _ hhi
      apply contractEarly_get
      rw [hsize,List.length_cons,pow_succ,
        show 3^point.length*3*rows = (3^point.length*rows)*3 by ring,
        Nat.mul_div_left _ (by decide : 0 < 3)]
      have hp : 0 < 3^point.length := by positivity
      nlinarith
    · rw [contractEarly_size,hsize,List.length_cons,pow_succ,
        show 3^point.length*3*rows = (3^point.length*rows)*3 by ring,
        Nat.mul_div_left _ (by decide : 0 < 3)]

/-- The native binding loop evaluates the tensor's exact quadratic endpoint basis. -/
theorem bindEarly_get (values point : Array W) (rows : Nat)
    (hsize : values.size = 3^point.size*rows) (row : Nat) (hrow : row < rows) :
    (bindEarly values point)[row]! = tensorInterpolate point.toList (fun i => values[i]!) row := by
  rw [bindEarly_eq_fold]
  exact contractEarly_fold_get point.toList values rows (by simpa only [Array.length_toList] using hsize) row hrow

end CompStark.Keccak.GkrProver
