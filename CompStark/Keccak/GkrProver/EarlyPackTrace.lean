/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.TensorHonest

/-! Honest coefficient strategies for the four production early pack transitions. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64 Polynomial

/-- Execute a structural prefix of the native early transitions at their current sampled-coordinate index. -/
def earlyPackRun (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W) :
    Nat → PackResult → PackResult
  | 0,state => state
  | n+1,state => earlyPackRun w d claim s values n (nativePackStep w d claim s values state state.point.size)

/-- Early structural iteration preserves all entering sampled coordinates and messages. -/
theorem earlyPackRun_prefix (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W)
    (n : Nat) (state : PackResult) :
    (∀ i,i<state.point.size → (earlyPackRun w d claim s values n state).point[i]! = state.point[i]!) ∧
      (∀ i,i<state.messages.size → (earlyPackRun w d claim s values n state).messages[i]! = state.messages[i]!) := by
  induction n generalizing state with
  | zero => exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  | succ n ih =>
    rw [earlyPackRun]
    have hh := ih (nativePackStep w d claim s values state state.point.size)
    constructor
    · intro i hi
      rw [hh.1 i (by rw [(nativePackStep_lengths w d claim s values state state.point.size).1]; omega)]
      exact array_push_get_old _ _ _ hi
    · intro i hi
      rw [hh.2 i (by rw [(nativePackStep_lengths w d claim s values state state.point.size).2]; omega)]
      exact array_push_get_old _ _ _ hi

/-- The early transition emits the two transmitted coefficients of its complete scaled quadratic. -/
theorem nativePackStep_early_message (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W)
    (state : PackResult) (hi : state.point.size<4) :
    cofactorMessageOfArray (nativePackStep w d claim s values state state.point.size).messages[state.messages.size]! =
      ((earlyPolynomial values claim.point state.point state.scale).val.coeff 1,
        fun _ : Fin 1 => (earlyPolynomial values claim.point state.point state.scale).val.coeff 2) := by
  simp only [nativePackStep,ite_eq_left hi,array_push_get_last]
  change (((earlyRound values claim.point state.point).map (state.scale*·))[1]!,
    fun _ : Fin 1 => ((earlyRound values claim.point state.point).map (state.scale*·))[2]!) = _
  rw [earlyRound_map_get values claim.point state.point state.scale 1 (by decide),
    earlyRound_map_get values claim.point state.point state.scale 2 (by decide)]
  exact congrArg₂ Prod.mk
    (earlyPolynomial_coeff values claim.point state.point state.scale (1 : Fin 3)).symm
    (funext (fun _ => (earlyPolynomial_coeff values claim.point state.point state.scale (2 : Fin 3)).symm))

/-- Every early native message follows the honest quadratic-cofactor strategy on the complete production tensor. -/
theorem earlyPackRun_honest (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W)
    (hv : values.size=81) (hc : 4≤claim.point.size) (n : Nat) (state : PackResult)
    (hs : state.point.size+n=4) (i : Fin n) :
    let final := earlyPackRun w d claim s values n state
    cofactorMessageOfArray final.messages[state.messages.size+i.val]! =
      honestCofactorRounds
        (fun point : Fin n → W => state.scale*tensorInterpolate (state.point.toList++List.ofFn point) (fun i => values[i]!) 0)
        (tensorInterpolate_prefix_degree state.point n (fun i => values[i]!) state.scale)
        (fun j : Fin n => claim.point[state.point.size+j.val]!)
        (fun j : Fin n => final.point[state.point.size+j.val]!) i := by
  induction n generalizing state with
  | zero => exact i.elim0
  | succ n ih =>
    let next := nativePackStep w d claim s values state state.point.size
    have hns : next.point.size+n=4 := by rw [(nativePackStep_lengths w d claim s values state state.point.size).1]; omega
    have hpoint : (earlyPackRun w d claim s values n next).point[state.point.size]! = next.point[state.point.size]! :=
      (earlyPackRun_prefix w d claim s values n next).1 _ (by
        rw [(nativePackStep_lengths w d claim s values state state.point.size).1]; omega)
    rw [earlyPackRun]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,Nat.add_zero]
      rw [(earlyPackRun_prefix w d claim s values n next).2 _ (by
        rw [(nativePackStep_lengths w d claim s values state state.point.size).2]; omega)]
      rw [nativePackStep_early_message w d claim s values state (by omega)]
      simp only [honestCofactorRounds,Fin.cons_zero]
      have hh := earlyPolynomial_honest values claim.point state.point state.scale n hv hc (by omega)
      simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using
        (congrArg (fun P : W⦃≤2⦄[X] => (P.val.coeff 1,fun _ : Fin 1 => P.val.coeff 2)) hh).symm
    · simp only [Fin.val_succ,honestCofactorRounds,Fin.cons_succ,Fin.val_zero,Nat.add_zero]
      have heq :
          (fun rest : Fin n → W =>
            (1+claim.point[state.point.size]!+(earlyPackRun w d claim s values n next).point[state.point.size]!)*
              (state.scale*tensorInterpolate
                (state.point.toList++List.ofFn (Fin.cons
                  ((earlyPackRun w d claim s values n next).point[state.point.size]!) rest)) (fun i => values[i]!) 0)) =
          (fun rest : Fin n → W => next.scale*tensorInterpolate (next.point.toList++List.ofFn rest) (fun i => values[i]!) 0) := by
        funext rest
        rw [hpoint]
        dsimp only [next,nativePackStep]
        rw [array_push_get_last]
        simp only [List.ofFn_cons,Array.toList_push,List.append_assoc,List.singleton_append]
        ring
      have hcongr := honestCofactorRounds_congr
        (coordinateDegree_scale_tail
          (fun point : Fin (n+1) → W => state.scale*tensorInterpolate (state.point.toList++List.ofFn point) (fun i => values[i]!) 0)
          (tensorInterpolate_prefix_degree state.point (n+1) (fun i => values[i]!) state.scale)
          (1+claim.point[state.point.size]!+(earlyPackRun w d claim s values n next).point[state.point.size]!)
          ((earlyPackRun w d claim s values n next).point[state.point.size]!))
        (tensorInterpolate_prefix_degree next.point n (fun i => values[i]!) next.scale) heq
        (fun k : Fin n => claim.point[state.point.size+k.succ.val]!)
        (fun k : Fin n => claim.point[next.point.size+k.val]!)
        (fun k : Fin n => (earlyPackRun w d claim s values n next).point[state.point.size+k.succ.val]!)
        (fun k : Fin n => (earlyPackRun w d claim s values n next).point[next.point.size+k.val]!)
        (by funext k; dsimp only [next,nativePackStep]; simp only [Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1])
        (by funext k; dsimp only [next,nativePackStep]; simp only [Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1])
      have hm : next.messages.size=state.messages.size+1 :=
        (nativePackStep_lengths w d claim s values state state.point.size).2
      simpa only [hm,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using
        (ih next hns j).trans (congrFun hcongr j).symm

/-- Structural early iteration is the production fold over the same consecutive coordinate indices. -/
theorem earlyPackRun_eq_fold (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W)
    (n : Nat) (state : PackResult) :
    earlyPackRun w d claim s values n state =
      (List.range n).foldl (fun next i => nativePackStep w d claim s values next (state.point.size+i)) state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    rw [earlyPackRun,List.range_succ_eq_map,List.foldl_cons,List.foldl_map]
    simp only [Nat.add_zero]
    rw [ih]
    have hs := (nativePackStep_lengths w d claim s values state state.point.size).1
    simp only [hs,Nat.add_assoc,Nat.add_comm 1]

/-- At an empty entering point, structural iteration uses the unshifted production indices. -/
theorem earlyPackRun_empty_eq_fold (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W)
    (n : Nat) (state : PackResult) (hs : state.point.size=0) :
    earlyPackRun w d claim s values n state =
      (List.range n).foldl (nativePackStep w d claim s values) state := by
  rw [earlyPackRun_eq_fold]
  simp only [hs,Nat.zero_add]

/-- The first four production transitions are their structural early run. -/
theorem nativePackBoundary_eq_early (w : SlicedWitness) (d : Nat) (claim : Claim) (s : W) (values : Array W)
    (writer : Writer) (value : W) :
    (List.range 4).foldl (nativePackStep w d claim s values)
      ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩ =
      earlyPackRun w d claim s values 4 ⟨PackedE.zeros 0,lane 1,value,#[],#[],writer⟩ := by
  exact (earlyPackRun_empty_eq_fold w d claim s values 4 _ rfl).symm

end CompStark.Keccak.GkrProver
