/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.Executable
public import CompStark.Keccak.Gkr.ResidualAlgebra

/-! Equality tensor expansion with one multiplication per adjacent pair. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 8192

@[expose] public section
namespace CompStark.Keccak.Gkr

/-- Share the high half's products when computing the complementary equality weights. -/
def cubeWeightsShared {R : Type*} [CommRing R] :
    {n : Nat} → (Fin n → R) → Vector R (2^n)
  | 0, _ => #v[1]
  | n+1, point =>
    let previous := cubeWeightsShared (fun i : Fin n => point i.castSucc)
    let last := point (Fin.last n)
    let high := previous.map (fun a => a * last)
    Vector.ofFn fun i : Fin (2^(n+1)) =>
      if small : i.val < 2^n then previous[i.val] - high[i.val]
      else high[i.val-2^n]'(by
        have bound : i.val < 2^n*2 := by simpa only [pow_succ] using i.isLt
        omega)

/-- Complementary tensor weights equal the exact original equality tensor. -/
@[csimp] theorem cubeWeights_shared : @cubeWeights = @cubeWeightsShared := by
  funext R inst n point
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeWeights.eq_2, cubeWeightsShared.eq_2, ← ih]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    split_ifs
    · rw [Vector.getElem_map]
      ring
    · rw [Vector.getElem_map]

/-- Shared tensor construction retains each individual equality weight. -/
theorem cubeWeightsShared_get {R : Type*} [CommRing R] {n : Nat}
    (point : Fin n → R) (i : Fin (2^n)) : (cubeWeightsShared point)[i] = eqWeight point i.val := by
  rw [← cubeWeights_shared]
  exact cubeWeights_get point i

/-- Shared tensor construction materializes the exact family of equality weights. -/
theorem cubeWeightsShared_eq {R : Type*} [CommRing R] {n : Nat} (point : Fin n → R) :
    cubeWeightsShared point = Vector.ofFn (fun i : Fin (2^n) => eqWeight point i.val) := by
  apply Vector.ext
  intro i hi
  simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using cubeWeightsShared_get point ⟨i,hi⟩

/-- Batch each lane with its two cyclic row neighbors. -/
def batchLanes {R : Type*} [CommRing R] (lanes : Vector R (2^5)) (beta : R) : Vector R 25 :=
  let betaSquared := beta ^ 2
  Vector.ofFn fun lane : Fin 25 =>
    lanes[lane.val] +
      beta * lanes[(lane.val % 5 + 4) % 5 + 5 * (lane.val / 5)]'(by omega) +
      betaSquared * lanes[(lane.val % 5 + 3) % 5 + 5 * (lane.val / 5)]'(by omega)

/-- Each shared lane retains the exact quadratic batching expression. -/
theorem batchLanes_get {R : Type*} [CommRing R] (lanes : Vector R (2^5)) (beta : R)
    (i : Nat) (h : i < 25) :
    (batchLanes lanes beta)[i] = lanes[i]'(by omega) +
      beta * lanes[(i % 5 + 4) % 5 + 5 * (i / 5)]'(by omega) +
      beta^2 * lanes[(i % 5 + 3) % 5 + 5 * (i / 5)]'(by omega) := by
  simp only [batchLanes, Vector.getElem_ofFn]

/-- Separate slice weights from the three batched lane weights before transposition. -/
def positionWeights {R : Type*} [CommRing R] (point : Fin 11 → R) (beta : R) : Vector R 1600 :=
  let slices := cubeWeightsShared (fun i : Fin 6 => point (Fin.castAdd 5 i))
  let lanes := cubeWeightsShared (fun i : Fin 5 => point (Fin.natAdd 6 i))
  let batched := batchLanes lanes beta
  Vector.ofFn fun j : Fin 1600 => slices[j.val % 64] * batched[j.val / 64]'(by omega)

/-- Factored position weights preserve all three shifted equality weights. -/
theorem positionWeights_get {R : Type*} [CommRing R] (point : Fin 11 → R) (beta : R)
    (j : Fin 1600) :
    (positionWeights point beta)[j] = eqWeight point j.val +
      beta * eqWeight point (along j 4).val + beta ^ 2 * eqWeight point (along j 3).val := by
  have split (i : Fin 1600) : eqWeight point i.val =
      eqWeight (fun b : Fin 6 => point (Fin.castAdd 5 b)) (i.val % 64) *
      eqWeight (fun b : Fin 5 => point (Fin.natAdd 6 b)) (i.val / 64) := by
    have h := eqWeight_split (a := 6) (b := 5) point
      ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩ ⟨i.val / 64, by omega⟩
    simpa only [show (2:Nat)^6 = 64 from rfl, Nat.mod_add_div] using h
  rw [Fin.getElem_fin]
  unfold positionWeights
  rw [cubeWeightsShared_eq (fun i : Fin 6 => point (Fin.castAdd 5 i)),
    cubeWeightsShared_eq (fun i : Fin 5 => point (Fin.natAdd 6 i))]
  rw [Vector.getElem_ofFn]
  simp only [batchLanes, Vector.getElem_ofFn]
  rw [split j, split (along j 4), split (along j 3)]
  simp only [along, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (Nat.mod_lt j.val (by decide : 0 < 64)),
    Nat.mul_add_div (by decide : 0 < 64), Nat.div_eq_of_lt (Nat.mod_lt j.val (by decide : 0 < 64)),
    Nat.add_zero]
  ring

/-- Construct the next GKR claim with shared slice and batched lane weights. -/
def nextClaimShared {R : Type} [CommRing R] [CharP R 2] {p : Nat}
    (transcript : LayerTranscript R p) : Claim R p :=
  let weights := positionWeights transcript.positionPoint transcript.beta
  let betaSquared := transcript.beta ^ 2
  { value := transcript.evaluations 0 + transcript.beta * transcript.evaluations 1 +
      betaSquared * transcript.evaluations 2
    mu := muAt transcript.point
    point := transcript.packPoint
    weights := linearTransposeFast fun j => weights[j] }

/-- Factored position tensors preserve every next-claim field. -/
@[csimp] theorem nextClaim_shared : @nextClaimFast = @nextClaimShared := by
  funext R inst characteristic p transcript
  simp only [nextClaimFast, nextClaimShared, cubeWeights_get, positionWeights_get]

end CompStark.Keccak.Gkr
