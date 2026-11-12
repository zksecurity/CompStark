/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorContraction

/-! Tensor interpolation of multilinear factors and their quadratic products. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Multilinear interpolation of a Boolean table in little-endian coordinate order. -/
def binaryInterpolate : List W → (Nat → W) → Nat → W
  | [], values, row => values row
  | r::point, values, row =>
      (1+r)*binaryInterpolate point (fun i => values (2*i)) row+
        r*binaryInterpolate point (fun i => values (2*i+1)) row

/-- A multilinear factor at zero, one or its infinity derivative in every ternary coordinate. -/
def ternaryLift {F : Type*} [Add F] : Nat → (Nat → F) → Nat → F
  | 0, values, row => values row
  | n+1, values, row =>
      if row%3 = 0 then ternaryLift n (fun i => values (2*i)) (row/3)
      else if row%3 = 1 then ternaryLift n (fun i => values (2*i+1)) (row/3)
      else ternaryLift n (fun i => values (2*i)+values (2*i+1)) (row/3)

/-- The zero endpoint of a lifted multilinear factor selects its even Boolean rows. -/
theorem ternaryLift_zero {F : Type*} [Add F] (n : Nat) (values : Nat → F) (row : Nat) :
    ternaryLift (n+1) values (3*row) = ternaryLift n (fun i => values (2*i)) row := by
  rw [ternaryLift]
  simp only [Nat.mul_mod_right,Nat.reduceEqDiff,ite_true,Nat.mul_div_right _ (by decide : 0 < 3)]

/-- The one endpoint of a lifted multilinear factor selects its odd Boolean rows. -/
theorem ternaryLift_one {F : Type*} [Add F] (n : Nat) (values : Nat → F) (row : Nat) :
    ternaryLift (n+1) values (3*row+1) = ternaryLift n (fun i => values (2*i+1)) row := by
  rw [ternaryLift]
  have hm : (3*row+1)%3 = 1 := by omega
  have hd : (3*row+1)/3 = row := by omega
  simp only [hm,hd,Nat.reduceEqDiff,ite_false,ite_true]

/-- The infinity endpoint is the sum of the zero and one Boolean faces. -/
theorem ternaryLift_infinity {F : Type*} [Add F] (n : Nat) (values : Nat → F) (row : Nat) :
    ternaryLift (n+1) values (3*row+2) =
      ternaryLift n (fun i => values (2*i)+values (2*i+1)) row := by
  rw [ternaryLift]
  have hm : (3*row+2)%3 = 2 := by omega
  have hd : (3*row+2)/3 = row := by omega
  simp only [hm,hd,Nat.reduceEqDiff,ite_false]

/-- Lifting a multilinear factor preserves addition of its Boolean tables. -/
theorem ternaryLift_add {F : Type*} [AddCommMonoid F] (n : Nat) (a b : Nat → F) (row : Nat) :
    ternaryLift n (fun i => a i+b i) row = ternaryLift n a row+ternaryLift n b row := by
  induction n generalizing a b row with
  | zero => rfl
  | succ n ih =>
    rw [ternaryLift,ternaryLift,ternaryLift]
    split
    · exact ih _ _ _
    · split
      · exact ih _ _ _
      · have hfun : (fun i => (a (2*i)+b (2*i))+(a (2*i+1)+b (2*i+1))) =
            (fun i => (a (2*i)+a (2*i+1))+(b (2*i)+b (2*i+1))) := by
          funext i
          ac_rfl
        rw [hfun,ih]

/-- Multilinear interpolation preserves addition of the Boolean tables. -/
theorem binaryInterpolate_add (point : List W) (a b : Nat → W) (row : Nat) :
    binaryInterpolate point (fun i => a i+b i) row =
      binaryInterpolate point a row+binaryInterpolate point b row := by
  induction point generalizing a b with
  | nil => rfl
  | cons r point ih =>
    simp only [binaryInterpolate,ih]
    ring

/-- A product of two affine factors has exactly its zero, one and infinity endpoints. -/
theorem interpolateQuadratic_product (a b c d r : W) :
    interpolateQuadratic (a*c) (b*d) ((a+b)*(c+d)) r =
      ((1+r)*a+r*b)*((1+r)*c+r*d) := by
  unfold interpolateQuadratic
  have hz := CharTwo.add_self_eq_zero (r*b*d)
  linear_combination hz

/-- The quadratic endpoint tensor of two multilinear factors interpolates their exact product. -/
theorem tensorInterpolate_product (point : List W) (a b : Nat → W) (row : Nat) :
    tensorInterpolate point
      (fun i => ternaryLift point.length a i*ternaryLift point.length b i) row =
      binaryInterpolate point a row*binaryInterpolate point b row := by
  induction point generalizing a b with
  | nil => rfl
  | cons r point ih =>
    simp only [List.length_cons,tensorInterpolate,ternaryLift_zero,ternaryLift_one,
      ternaryLift_infinity,ih,binaryInterpolate,binaryInterpolate_add]
    exact interpolateQuadratic_product _ _ _ _ _

/-- A degree-one tensor stores zero in every infinity coefficient slot. -/
def ternaryLinearLift : Nat → (Nat → W) → Nat → W
  | 0, values, row => values row
  | n+1, values, row =>
      if row%3 = 0 then ternaryLinearLift n (fun i => values (2*i)) (row/3)
      else if row%3 = 1 then ternaryLinearLift n (fun i => values (2*i+1)) (row/3)
      else 0

/-- Zero multilinear endpoint data gives a zero interpolated tensor. -/
theorem tensorInterpolate_zero (point : List W) (row : Nat) :
    tensorInterpolate point (fun _ => 0) row = 0 := by
  induction point with
  | nil => rfl
  | cons r point ih => simp only [tensorInterpolate,ih,interpolateQuadratic,mul_zero,add_zero]

/-- Tensor interpolation of a degree-one table is the same Boolean multilinear interpolation. -/
theorem tensorInterpolate_linear (point : List W) (values : Nat → W) (row : Nat) :
    tensorInterpolate point (ternaryLinearLift point.length values) row =
      binaryInterpolate point values row := by
  induction point generalizing values with
  | nil => rfl
  | cons r point ih =>
    have hzero (i : Nat) : ternaryLinearLift (point.length+1) values (3*i) =
        ternaryLinearLift point.length (fun j => values (2*j)) i := by
      rw [ternaryLinearLift]
      simp only [Nat.mul_mod_right,ite_true,Nat.mul_div_right _ (by decide : 0 < 3)]
    have hone (i : Nat) : ternaryLinearLift (point.length+1) values (3*i+1) =
        ternaryLinearLift point.length (fun j => values (2*j+1)) i := by
      rw [ternaryLinearLift]
      have hm : (3*i+1)%3 = 1 := by omega
      have hd : (3*i+1)/3 = i := by omega
      simp only [hm,hd,Nat.reduceEqDiff,ite_true,ite_false]
    have hinfinity (i : Nat) : ternaryLinearLift (point.length+1) values (3*i+2) = 0 := by
      rw [ternaryLinearLift]
      have hm : (3*i+2)%3 = 2 := by omega
      simp only [hm,Nat.reduceEqDiff,ite_false]
    simp only [List.length_cons,tensorInterpolate,hzero,hone,hinfinity,
      tensorInterpolate_zero,ih,interpolateQuadratic,mul_zero,add_zero,binaryInterpolate]

/-- Native contractions recover the full affine chi expression on the interpolated factors. -/
theorem tensorInterpolate_chi (point : List W) (a b c : Nat → W) (kappa : W) (row : Nat) :
    tensorInterpolate point
      (fun i => kappa*ternaryLinearLift point.length a i+
        kappa*ternaryLinearLift point.length c i+
        ternaryLift point.length b i*ternaryLift point.length c i) row =
      kappa*binaryInterpolate point a row+
        (kappa+binaryInterpolate point b row)*binaryInterpolate point c row := by
  rw [tensorInterpolate_add,tensorInterpolate_add,tensorInterpolate_scale,
    tensorInterpolate_scale,tensorInterpolate_linear,tensorInterpolate_linear,
    tensorInterpolate_product]
  ring

end CompStark.Keccak.GkrProver
