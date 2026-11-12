/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.Gkr.Protocol
/-! Shared equality weights and sparse linear Keccak evaluation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace CompStark.Keccak.Gkr

/-- Theta, rho and pi with array rotation lookup. -/
def linearFast {R : Type*} [CommRing R] (a : Fin 1600 → R) (j : Fin 1600) : R :=
  let l := inversePi (j.val / 64)
  let z := (j.val % 64 + 64 - rhoFast l) % 64
  a ⟨64*l.val+z, by omega⟩ +
    (∑ y : Fin 5, a ⟨64*((l.val%5+4)%5+5*y.val)+z, by omega⟩) +
    (∑ y : Fin 5, a ⟨64*((l.val%5+1)%5+5*y.val)+(z+63)%64, by omega⟩)
/-- Array lookup preserves the linear Keccak map. -/
@[csimp] theorem linear_code : @linear = @linearFast := by
  funext R inst a j
  simp only [linear, linearFast, rho_code]
/-- The integer coefficient of one input bit in one linear output. -/
def linearCoefficient (i j : Fin 1600) : Int :=
  linearFast (fun k => if k = i then 1 else 0) j
/-- Integer linear coefficients specialize to every coefficient ring. -/
theorem linearCoefficient_cast {R : Type*} [CommRing R] (i j : Fin 1600) :
    (linearCoefficient i j : R) = linear (fun k => if k = i then 1 else 0) j := by
  unfold linearCoefficient
  rw [← linear_code]
  change (Int.castRingHom R) (linear (fun k => if k = i then 1 else 0) j) = _
  simp only [linear, map_add, map_sum, apply_ite, map_one, map_zero]
/-- The shared sparse support of every transpose row. -/
def transposeSupport : Vector (List (Fin 1600)) 1600 :=
  Vector.ofFn fun i => (List.finRange 1600).filter fun j => decide (linearCoefficient i j ≠ 0)
/-- Omitting zero integer coefficients preserves the weighted sum. -/
theorem support_sum {R : Type*} [CommRing R] (w : Fin 1600 → R) (i : Fin 1600)
    (xs : List (Fin 1600)) :
    (((xs.filter fun j => decide (linearCoefficient i j ≠ 0)).map
      fun j => w j * (linearCoefficient i j : R)).sum) =
    ((xs.map fun j => w j * (linearCoefficient i j : R)).sum) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
      by_cases zero : linearCoefficient i j = 0
      · simp only [List.filter_cons, zero, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, Int.cast_zero,
          mul_zero, zero_add, ih]
      · simp only [List.filter_cons, zero, ne_eq, not_false_eq_true, decide_true,
          ↓reduceIte, List.map_cons, List.sum_cons, ih]
/-- Apply an integer coefficient, reading unit coefficients directly. -/
def scaleCoefficient {R : Type*} [CommRing R] (c : Int) (x : R) : R :=
  if c = 1 then x else x * (c : R)
/-- The unit coefficient branch is exactly scalar multiplication. -/
theorem scaleCoefficient_eq {R : Type*} [CommRing R] (c : Int) (x : R) :
    scaleCoefficient c x = x * (c : R) := by
  unfold scaleCoefficient
  split_ifs with unit
  · simp only [unit, Int.cast_one, mul_one]
  · rfl
/-- Immutable sparse rows retain each integer coefficient alongside its input index. -/
def transposeRows : Vector (List (Fin 1600 × Int)) 1600 :=
  Vector.ofFn fun i => transposeSupport[i].map fun j => (j, linearCoefficient i j)
/-- Apply the sparse transpose to one shared image of its weights. -/
@[macro_inline] def linearTransposeFast {R : Type*} [CommRing R] (w : Fin 1600 → R) : Fin 1600 → R :=
  let image := Vector.ofFn w
  fun i => ((transposeRows[i]).map fun term => scaleCoefficient term.2 image[term.1]).sum
/-- The sparse evaluator is exactly the dense transpose. -/
@[csimp] theorem linearTranspose_code : @linearTranspose = @linearTransposeFast := by
  funext R inst w i
  simp only [linearTransposeFast, transposeRows, transposeSupport, Fin.getElem_fin, Vector.getElem_ofFn,
    List.map_map, Function.comp_def, scaleCoefficient_eq]
  rw [support_sum]
  simp only [linearCoefficient_cast]
  simpa only [linearTranspose, List.ofFn_eq_map] using
    (Fin.sum_ofFn (fun j => w j * linear (fun k => if k = i then 1 else 0) j)).symm
/-- Tensor expansion of all equality-kernel weights. -/
def cubeWeights {R : Type*} [CommRing R] : {n : Nat} → (Fin n → R) → Vector R (2 ^ n)
  | 0, _ => #v[1]
  | n + 1, r =>
    let previous := cubeWeights (fun i : Fin n => r i.castSucc)
    let last := r (Fin.last n)
    let complement := 1 - last
    Vector.ofFn fun i : Fin (2 ^ (n + 1)) =>
      if h : i.val < 2 ^ n then previous[i.val] * complement
      else previous[i.val - 2 ^ n]'(by
        have bound : i.val < 2 ^ n * 2 := by simpa only [pow_succ] using i.isLt
        omega) * last
/-- Tensor expansion agrees with each individual equality weight. -/
theorem cubeWeights_get {R : Type*} [CommRing R] {n : Nat}
    (r : Fin n → R) (i : Fin (2 ^ n)) : (cubeWeights r)[i] = eqWeight r i.val := by
  induction n with
  | zero =>
    have hi : i.val = 0 := by have := i.isLt; norm_num at this; omega
    simp only [cubeWeights.eq_1, eqWeight, Fin.prod_univ_zero, Fin.getElem_fin, hi]
    rfl
  | succ n ih =>
    simp only [cubeWeights.eq_2, Fin.getElem_fin, Vector.getElem_ofFn]
    split_ifs with low
    · have old := ih (fun j => r j.castSucc) ⟨i.val, low⟩
      simp only [Fin.getElem_fin] at old
      rw [old]
      simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, ite_true] using
        (eqWeight_last r ⟨i.val, low⟩ 0).symm
    · have small : i.val - 2 ^ n < 2 ^ n := by
        have bound : i.val < 2 ^ n * 2 := by simpa only [pow_succ] using i.isLt
        omega
      have old := ih (fun j => r j.castSucc) ⟨i.val - 2 ^ n, small⟩
      simp only [Fin.getElem_fin] at old
      rw [old]
      have index : i.val - 2 ^ n + 2 ^ n * 1 = i.val := by omega
      have split := eqWeight_last r ⟨i.val - 2 ^ n, small⟩ 1
      simpa only [Fin.val_one, one_ne_zero, ite_false, index] using split.symm
/-- Build the next claim from one tensor expansion and the sparse transpose. -/
def nextClaimFast {R : Type} [CommRing R] [CharP R 2] {p : Nat}
    (t : LayerTranscript R p) : Claim R p :=
  let weights := cubeWeights t.positionPoint
  let betaSquared := t.beta ^ 2
  { value := t.evaluations 0 + t.beta * t.evaluations 1 + betaSquared * t.evaluations 2
    mu := muAt t.point
    point := t.packPoint
    weights := linearTransposeFast fun j =>
      weights[(⟨j.val, by have := j.isLt; omega⟩ : Fin (2 ^ 11))] +
      t.beta * weights[(⟨(along j 4).val, by have := (along j 4).isLt; omega⟩ : Fin (2 ^ 11))] +
      betaSquared * weights[(⟨(along j 3).val, by have := (along j 3).isLt; omega⟩ : Fin (2 ^ 11))] }
/-- Shared tensor weights preserve the next GKR claim exactly. -/
@[csimp] theorem nextClaim_code : @nextClaim = @nextClaimFast := by
  funext R inst char p t
  simp only [nextClaim, nextClaimFast, cubeWeights_get, ← linearTranspose_code]
/-- Horner evaluation shares multiplication by the polynomial challenge. -/
def polyEvalHorner {R : Type*} [CommRing R] : {n : Nat} → (Fin n → R) → R → R
| 0, _, _ => 0
| n+1, coeffs, s => coeffs 0 + s * polyEvalHorner (fun i : Fin n => coeffs i.succ) s
/-- Horner evaluation preserves the coefficient-sum specification. -/
theorem polyEvalHorner_eq {R : Type*} [CommRing R] {n : Nat} (coeffs : Fin n → R) (s : R) :
    polyEvalHorner coeffs s = polyEval coeffs s := by
  induction n with
  | zero => simp only [polyEvalHorner.eq_1, polyEval, Fin.sum_univ_zero]
  | succ n ih =>
    simp only [polyEvalHorner.eq_2, ih, polyEval, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
      mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Native GKR polynomial checks use the certified Horner evaluator. -/
@[csimp] theorem polyEval_code : @polyEval = @polyEvalHorner := by
  funext R inst n coefficients point
  exact (polyEvalHorner_eq coefficients point).symm

end CompStark.Keccak.Gkr
