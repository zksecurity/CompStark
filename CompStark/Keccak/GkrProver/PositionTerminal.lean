/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PositionTrace

/-! Exact terminal multilinear evaluations of the native position loop. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64

/-- A multilinear table with no remaining coordinates evaluates to its only entry. -/
theorem mle_no_coordinates (table : Fin 1 → W) (point : Fin 0 → W) : mle table point = table 0 := by
  simp only [mle,eqWeight,Fin.prod_univ_zero,one_mul]
  exact Fin.sum_univ_one table

/-- The complete native position run reaches the exact weight and three shifted-factor MLEs. -/
theorem positionRun_terminal (initial : PositionResult) (scale kappa : W) (n : Nat)
    (hw : initial.weights.size = 2^n) (hs : initial.factors.size = 3)
    (ht : ∀ k : Fin 3,(initial.factors[k.val]!).size = 2^n) :
    let final := positionRun scale kappa initial n
    final.weights.size = 1 ∧ final.factors.size = 3 ∧
      (∀ k : Fin 3,(final.factors[k.val]!).size = 1) ∧
      final.weights[0]! = mle (fun row : Fin (2^n) => initial.weights[row.val]!)
        (fun j => final.point[initial.point.size+j.val]!) ∧
      ∀ k : Fin 3,(final.factors[k.val]!)[0]! =
        mle (fun row : Fin (2^n) => (initial.factors[k.val]!)[row.val]!)
          (fun j => final.point[initial.point.size+j.val]!) := by
  induction n generalizing initial with
  | zero =>
    refine ⟨hw,hs,ht,?_,?_⟩
    · simp only [positionRun,mle,eqWeight,Fin.prod_univ_zero,one_mul]
      exact (Fin.sum_univ_one (fun row : Fin 1 => initial.weights[row.val]!)).symm
    · intro k
      simp only [positionRun,mle,eqWeight,Fin.prod_univ_zero,one_mul]
      exact (Fin.sum_univ_one (fun row : Fin 1 => (initial.factors[k.val]!)[row.val]!)).symm
  | succ n ih =>
    let next := positionStep scale kappa initial
    let r := ((initial.writer.writeAll
      ((positionRound initial.weights initial.factors kappa).map (scale*·))).sample).1
    have hnw : next.weights.size = 2^n := fold_size _ hw r
    have hns : next.factors.size = 3 := by dsimp only [next,positionStep]; rw [Array.size_map,hs]
    have hget (k : Nat) (hk : k < 3) : next.factors[k]! = fold initial.factors[k]! 1 r := by
      dsimp only [next,positionStep]
      rw [getElem!_pos _ _ (by rw [Array.size_map,hs]; exact hk),Array.getElem_map,
        ← getElem!_pos initial.factors _ (by rw [hs]; exact hk)]
    have hnt (k : Fin 3) : (next.factors[k.val]!).size = 2^n := by
      rw [hget k.val k.isLt]
      exact fold_size _ (ht k) r
    have hpoint : (positionRun scale kappa next n).point[initial.point.size]! = r := by
      rw [(positionRun_prefix scale kappa next n).1 _ (by
        dsimp only [next,positionStep]; rw [Array.size_push]; omega)]
      dsimp only [next,positionStep]
      exact array_push_get_last _ _
    have hvector : (fun j : Fin (n+1) => (positionRun scale kappa next n).point[initial.point.size+j.val]!) =
        Fin.cons r (fun j : Fin n => (positionRun scale kappa next n).point[next.point.size+j.val]!) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.val_zero,Nat.add_zero,Fin.cons_zero,hpoint]
      · dsimp only [next,positionStep]
        simp only [Fin.val_succ,Fin.cons_succ,Array.size_push,Nat.add_assoc,Nat.add_comm 1]
    have hh := ih next hnw hns hnt
    rw [positionRun_succ_first]
    refine ⟨hh.1,hh.2.1,hh.2.2.1,?_,?_⟩
    · rw [hh.2.2.2.1,hvector]
      exact fold_mle initial.weights hw r _
    · intro k
      rw [hh.2.2.2.2 k,hvector]
      simp only [hget k.val k.isLt]
      exact fold_mle initial.factors[k.val]! (ht k) r _

/-- The actual native position-loop body returns the three full shifted-factor MLEs at its sampled point. -/
theorem positionLoop_terminal (writer : Writer) (weights : Array W) (factors : Array (Array W))
    (scale kappa : W) (n : Nat) (hw : weights.size = 2^n) (hs : factors.size = 3)
    (ht : ∀ k : Fin 3,(factors[k.val]!).size = 2^n) :
    let final := positionLoop writer weights factors scale kappa n
    final.weights.size = 1 ∧ final.factors.size = 3 ∧
      (∀ k : Fin 3,(final.factors[k.val]!).size = 1) ∧
      final.weights[0]! = mle (fun row : Fin (2^n) => weights[row.val]!) (fun j => final.point[j.val]!) ∧
      ∀ k : Fin 3,(final.factors[k.val]!)[0]! =
        mle (fun row : Fin (2^n) => (factors[k.val]!)[row.val]!) (fun j => final.point[j.val]!) := by
  rw [positionLoop_eq_run]
  simpa only [Array.size_empty,Nat.zero_add] using
    positionRun_terminal ⟨weights,factors,#[],#[],writer⟩ scale kappa n hw hs ht

end CompStark.Keccak.GkrProver
