/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.QuadraticTrace
public import CompStark.Keccak.GkrProver.PositionTerminal

/-! Exact terminal column evaluations of the native quadratic opening prover. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64

/-- The production quadratic prover samples exactly one coordinate per round. -/
theorem proveQuadratics_point_size (writer : Writer) (a b : Array W) (width : Nat)
    (scale value : W) (n : Nat) :
    (proveQuadratics writer a b width scale value n).point.size = n := by
  rw [proveQuadratics_eq_run]
  simpa only [Array.size_empty,Nat.zero_add] using
    (quadraticRun_lengths width scale ⟨a,b,#[],#[],value,writer⟩ n).1

/-- The production quadratic prover transmits exactly one compressed message per round. -/
theorem proveQuadratics_messages_size (writer : Writer) (a b : Array W) (width : Nat)
    (scale value : W) (n : Nat) :
    (proveQuadratics writer a b width scale value n).messages.size = n := by
  rw [proveQuadratics_eq_run]
  simpa only [Array.size_empty,Nat.zero_add] using
    (quadraticRun_lengths width scale ⟨a,b,#[],#[],value,writer⟩ n).2

/-- Every terminal opening column is its complete entering multilinear interpolation. -/
theorem quadraticRun_terminal (initial : QuadraticResult) (width : Nat) (scale : W) (n : Nat)
    (hw : 0 < width) (ha : initial.a.size = 2^n*width) (hab : initial.a.size = initial.b.size) :
    let final := quadraticRun width scale initial n
    final.a.size = width ∧ final.b.size = width ∧
      (∀ c : Fin width,final.a[c.val]! =
        mle (fun row : Fin (2^n) => initial.a[row.val*width+c.val]!)
          (fun j => final.point[initial.point.size+j.val]!)) ∧
      ∀ c : Fin width,final.b[c.val]! =
        mle (fun row : Fin (2^n) => initial.b[row.val*width+c.val]!)
          (fun j => final.point[initial.point.size+j.val]!) := by
  induction n generalizing initial with
  | zero =>
    refine ⟨by simpa only [quadraticRun,pow_zero,one_mul] using ha,
      by simpa only [quadraticRun,pow_zero,one_mul] using hab.symm.trans ha,?_,?_⟩
    · intro c
      rw [mle_no_coordinates]
      simp only [quadraticRun,Fin.val_zero,Nat.zero_mul,Nat.zero_add]
    · intro c
      rw [mle_no_coordinates]
      simp only [quadraticRun,Fin.val_zero,Nat.zero_mul,Nat.zero_add]
  | succ n ih =>
    let next := quadraticStep width scale initial
    let r := ((initial.writer.writeAll
      #[(quadraticCoefficients initial.a initial.b width scale).1,
        (quadraticCoefficients initial.a initial.b width scale).2]).sample).1
    have hna : next.a.size = 2^n*width := by
      dsimp only [next,quadraticStep]
      rw [fold_rows_size,ha,pow_succ,Nat.mul_assoc,Nat.mul_div_cancel _ (by omega)]
    have hnab : next.a.size = next.b.size := by
      dsimp only [next,quadraticStep]
      rw [fold_rows_size,fold_rows_size,hab]
    have hpoint : (quadraticRun width scale next n).point[initial.point.size]! = r := by
      rw [(quadraticRun_prefix width scale next n).1 _ (by
        dsimp only [next,quadraticStep]; rw [Array.size_push]; omega)]
      dsimp only [next,quadraticStep]
      exact array_push_get_last _ _
    have hvector : (fun j : Fin (n+1) => (quadraticRun width scale next n).point[initial.point.size+j.val]!) =
        Fin.cons r (fun j : Fin n => (quadraticRun width scale next n).point[next.point.size+j.val]!) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.val_zero,Nat.add_zero,Fin.cons_zero,hpoint]
      · dsimp only [next,quadraticStep]
        simp only [Fin.val_succ,Fin.cons_succ,Array.size_push,Nat.add_assoc,Nat.add_comm 1]
    have hh := ih next hna hnab
    rw [quadraticRun_succ_first]
    refine ⟨hh.1,hh.2.1,?_,?_⟩
    · intro c
      rw [hh.2.2.1 c,hvector]
      exact fold_column_mle initial.a ha r _ c
    · intro c
      rw [hh.2.2.2 c,hvector]
      exact fold_column_mle initial.b (hab.symm.trans ha) r _ c

/-- The production opening prover returns all exact terminal factor evaluations at its sampled point. -/
theorem proveQuadratics_terminal (writer : Writer) (a b : Array W) (width : Nat)
    (scale value : W) (n : Nat) (hw : 0 < width) (ha : a.size = 2^n*width) (hab : a.size = b.size) :
    let final := proveQuadratics writer a b width scale value n
    final.a.size = width ∧ final.b.size = width ∧
      (∀ c : Fin width,final.a[c.val]! =
        mle (fun row : Fin (2^n) => a[row.val*width+c.val]!) (fun j => final.point[j.val]!)) ∧
      ∀ c : Fin width,final.b[c.val]! =
        mle (fun row : Fin (2^n) => b[row.val*width+c.val]!) (fun j => final.point[j.val]!) := by
  rw [proveQuadratics_eq_run]
  simpa only [Array.size_empty,Nat.zero_add] using
    quadraticRun_terminal ⟨a,b,#[],#[],value,writer⟩ width scale n hw ha hab

end CompStark.Keccak.GkrProver
