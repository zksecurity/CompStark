/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.PhaseBoundaries
public import CompStark.Keccak.Gkr.RoundProjection
public import CompStark.Keccak.Gkr.OpeningAlgebra

/-! # Fixed-prefix bad challenge sets for the concrete GKR phases -/

@[expose] public section
open Polynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- A false layer claim becomes a true pack residual only at one of at most 46 product roots. -/
theorem product_phase_bad_set {E : Type} [Field E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (sent : Fin 47 → E)
    (wrong : ¬ ClaimHolds q d.castSucc c)
    (check : (∑ i, c.mu i * projectMessage sent i) + constantContribution d c = c.value) :
    ∃ bad : Finset E, bad.card ≤ 46 ∧ ∀ s (r : Fin (p+1) → E),
      polyEval sent s = residualSum (packSummand q d c s) r 0 → s ∈ bad := by
  have hne : honestProduct q d c ≠ messagePolynomial sent := by
    intro h
    apply wrong
    apply (layer_projection_identity q d c).mpr
    simpa only [h, project_messagePolynomial] using check
  refine ⟨collisionSet (honestProduct q d c) (messagePolynomial sent),
    collisionSet_card _ _ (honestProduct_degree q d c) (messagePolynomial_degree sent), ?_⟩
  intro s r good
  apply (mem_collisionSet _ _ hne s).mpr
  simpa only [messagePolynomial_eval, pack_start_identity] using good.symm

/-- A false pack/segment residual becomes true only on a fixed set of at most three challenges. -/
theorem packSegment_phase_bad_set {E : Type*} [Field E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s : E)
    (i : Fin (p+1)) (point : Fin (p+1) → E) (sent : Fin 4 → E) (target : E)
    (wrong : target ≠ residualSum (packSummand q d c s) point i.val)
    (check : polyEval sent 0 + polyEval sent 1 = target) :
    ∃ bad : Finset E, bad.card ≤ 3 ∧ ∀ r,
      polyEval sent r = residualSum (packSummand q d c s) (Function.update point i r) (i.val+1) → r ∈ bad := by
  have hf : (fun r => MvPolynomial.eval r (packPolynomial q d c s)) = packSummand q d c s :=
    funext (packPolynomial_eval q d c s)
  simpa only [hf] using residual_round_bad_set (packPolynomial q d c s) i point sent target
    (packPolynomial_degree q d c s i) (by simpa only [hf] using wrong) check

/-- A false position residual becomes true only on a fixed set of at most three challenges. -/
theorem position_phase_bad_set {E : Type} [Field E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p)
    (i : Fin 11) (point : Fin 11 → E) (sent : Fin 4 → E) (target : E)
    (wrong : target ≠ residualSum (positionSummand q d c t) point i.val)
    (check : polyEval sent 0 + polyEval sent 1 = target) :
    ∃ bad : Finset E, bad.card ≤ 3 ∧ ∀ r,
      polyEval sent r = residualSum (positionSummand q d c t) (Function.update point i r) (i.val+1) → r ∈ bad := by
  have hf : (fun r => MvPolynomial.eval r (positionPolynomial q d c t)) = positionSummand q d c t :=
    funext (positionPolynomial_eval q d c t)
  simpa only [hf] using residual_round_bad_set (positionPolynomial q d c t) i point sent target
    (positionPolynomial_degree q d c t i) (by simpa only [hf] using wrong) check

/-- A false committed-middle opening residual becomes true only on at most two challenges. -/
theorem word_opening_phase_bad_set {E : Type} [Field E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (i : Fin 6) (point : Fin 6 → E)
    (sent : Fin 3 → E) (target : E)
    (wrong : target ≠ residualSum (wordSummand x q t) point i.val)
    (check : polyEval sent 0 + polyEval sent 1 = target) :
    ∃ bad : Finset E, bad.card ≤ 2 ∧ ∀ r,
      polyEval sent r = residualSum (wordSummand x q t) (Function.update point i r) (i.val+1) → r ∈ bad := by
  have hf : (fun r => MvPolynomial.eval r (wordPolynomial x q t)) = wordSummand x q t :=
    funext (wordPolynomial_eval x q t)
  simpa only [hf] using residual_round_bad_set (wordPolynomial x q t) i point sent target
    (wordPolynomial_degree x q t i) (by simpa only [hf] using wrong) check

/-- A false committed-input opening residual becomes true only on at most two challenges. -/
theorem slice_opening_phase_bad_set {E : Type} [Field E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) (i : Fin 10) (point : Fin 10 → E)
    (sent : Fin 3 → E) (target : E)
    (wrong : target ≠ residualSum (inputSummand q t) point i.val)
    (check : polyEval sent 0 + polyEval sent 1 = target) :
    ∃ bad : Finset E, bad.card ≤ 2 ∧ ∀ r,
      polyEval sent r = residualSum (inputSummand q t) (Function.update point i r) (i.val+1) → r ∈ bad := by
  have hf : (fun r => MvPolynomial.eval r (inputPolynomial q t)) = inputSummand q t :=
    funext (inputPolynomial_eval q t)
  simpa only [hf] using residual_round_bad_set (inputPolynomial q t) i point sent target
    (inputPolynomial_degree q t i) (by simpa only [hf] using wrong) check

end CompStark.Keccak.Gkr
