/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.QuadraticHonest

/-! Complete honest-message semantics of the native quadratic opening trace. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64

/-- Interpret the two scalars of a native quadratic message in the specification wire format. -/
def quadraticMessageOfArray (message : Array W) : Sumcheck.CompressedMessage W 1 :=
  (message[0]!,fun _ => message[1]!)

/-- Honest coefficient strategies are unchanged by equal summands and equal challenge vectors. -/
theorem honestCompressedRounds_congr {n degree : Nat} {f g : (Fin n → W) → W}
    (hf : CoordinateDegree f (degree+1)) (hg : CoordinateDegree g (degree+1))
    (hfg : f = g) (point other : Fin n → W) (hp : point = other) :
    honestCompressedRounds f hf point = honestCompressedRounds g hg other := by
  subst g
  subst other
  rfl

/-- All messages authored by the actual opening loop are its honest quadratic strategy at the sampled points. -/
theorem quadraticRun_honest (initial : QuadraticResult) (width : Nat) (scale : W) (n : Nat)
    (hw : 0 < width) (ha : initial.a.size = 2^n*width) (hab : initial.a.size = initial.b.size)
    (i : Fin n) :
    quadraticMessageOfArray
      (quadraticRun width scale initial n).messages[initial.messages.size+i.val]! =
        honestCompressedRounds (quadraticSummand initial.a initial.b width n scale)
          (quadraticSummand_degree initial.a initial.b width n scale)
          (fun j => (quadraticRun width scale initial n).point[initial.point.size+j.val]!) i := by
  induction n generalizing initial with
  | zero => exact i.elim0
  | succ n ih =>
    let next := quadraticStep width scale initial
    have hna : next.a.size = 2^n*width := by
      dsimp only [next,quadraticStep]
      rw [fold_rows_size,ha,pow_succ,Nat.mul_assoc,Nat.mul_div_cancel _ (by omega)]
    have hnab : next.a.size = next.b.size := by
      dsimp only [next,quadraticStep]
      rw [fold_rows_size,fold_rows_size,hab]
    have hpoint : (quadraticRun width scale next n).point[initial.point.size]! =
        ((initial.writer.writeAll
          #[(quadraticCoefficients initial.a initial.b width scale).1,
            (quadraticCoefficients initial.a initial.b width scale).2]).sample).1 := by
      rw [(quadraticRun_prefix width scale next n).1 _ (by
        dsimp only [next,quadraticStep]; rw [Array.size_push]; omega)]
      dsimp only [next,quadraticStep]
      exact array_push_get_last _ _
    rw [quadraticRun_succ_first]
    change quadraticMessageOfArray (quadraticRun width scale next n).messages[initial.messages.size+i.val]! =
      honestCompressedRounds (quadraticSummand initial.a initial.b width (n+1) scale)
        (quadraticSummand_degree initial.a initial.b width (n+1) scale)
        (fun j => (quadraticRun width scale next n).point[initial.point.size+j.val]!) i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,Nat.add_zero]
      rw [(quadraticRun_prefix width scale next n).2 _ (by
        dsimp only [next,quadraticStep]; rw [Array.size_push]; omega)]
      dsimp only [next,quadraticStep]
      rw [array_push_get_last]
      change quadraticMessage (quadraticCoefficients initial.a initial.b width scale).1
        (quadraticCoefficients initial.a initial.b width scale).2 = _
      rw [honestCompressedRounds,Fin.cons_zero]
      exact quadraticCoefficients_honest initial.a initial.b width n scale ha hab _
    · rw [honestCompressedRounds,Fin.cons_succ]
      have heq :
          (fun rest => quadraticSummand initial.a initial.b width (n+1) scale
            (Fin.cons ((quadraticRun width scale next n).point[initial.point.size+0]!) rest)) =
          quadraticSummand next.a next.b width n scale := by
        funext rest
        simp only [Nat.add_zero]
        rw [hpoint]
        exact (quadraticSummand_fold initial.a initial.b width n scale _ ha hab rest).symm
      have hh := ih next hna hnab j
      have hcongr := honestCompressedRounds_congr
        ((quadraticSummand_degree initial.a initial.b width (n+1) scale).tail
          (quadraticRun width scale next n).point[initial.point.size+0]!)
        (quadraticSummand_degree next.a next.b width n scale) heq
        (fun k : Fin n => (quadraticRun width scale next n).point[initial.point.size+k.succ.val]!)
        (fun k : Fin n => (quadraticRun width scale next n).point[next.point.size+k.val]!) (by
          funext k
          dsimp only [next,quadraticStep]
          simp only [Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1])
      trans honestCompressedRounds (quadraticSummand next.a next.b width n scale)
        (quadraticSummand_degree next.a next.b width n scale)
        (fun k => (quadraticRun width scale next n).point[next.point.size+k.val]!) j
      · simpa only [next,quadraticStep,Array.size_push,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using hh
      · exact (congrFun hcongr j).symm

/-- The production quadratic prover emits the exact specification messages for its factor buffers. -/
theorem proveQuadratics_honest (writer : Writer) (a b : Array W) (width : Nat)
    (scale value : W) (n : Nat) (hw : 0 < width) (ha : a.size = 2^n*width)
    (hab : a.size = b.size) :
    let final := proveQuadratics writer a b width scale value n
    (fun i : Fin n => quadraticMessageOfArray final.messages[i.val]!) =
      honestCompressedRounds (quadraticSummand a b width n scale)
        (quadraticSummand_degree a b width n scale) (fun i => final.point[i.val]!) := by
  rw [proveQuadratics_eq_run]
  funext i
  simpa only [Array.size_empty,Nat.zero_add] using
    quadraticRun_honest ⟨a,b,#[],#[],value,writer⟩ width scale n hw ha hab i

end CompStark.Keccak.GkrProver
