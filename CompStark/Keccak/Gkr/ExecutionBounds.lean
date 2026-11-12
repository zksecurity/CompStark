/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.WireExecution
public import CompStark.Keccak.Gkr.PhaseBounds
public import CompStark.Keccak.Gkr.OpeningAlgebra
public import CompStark.Keccak.Gkr.BetaBoundary

/-! # Adaptive phase bounds with the committed table fixed -/

@[expose] public section
open Polynomial OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- Boolean function indices and integer cube indices give the same initial sum. -/
theorem booleanSum_eq_residualSum {E : Type*} [CommRing E] {n : Nat}
    (f : (Fin n → E) → E) (r : Fin n → E) : booleanSum f = residualSum f r 0 := by
  rw [residualSum_zero]
  unfold booleanSum
  rw [← finFunctionFinEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext i
  simpa only [cubePoint, Equiv.symm_apply_apply] using (cube_bit_cast (E := E) (finFunctionFinEquiv b) i).symm

/-- Independent coordinate sampling tests a nonzero coordinate-degree-bounded function.
Nonzero means nonzero as a function, so the statement also applies over small fields. -/
theorem runCoordinates_zero_bound {E : Type} [Field E] [Fintype E] (n d : Nat)
    (f : (Fin n → E) → E) (degree : CoordinateDegree f d) (wrong : ∃ r, f r ≠ 0) :
    Pr{let r ← runCoordinates E n}[f r = 0] ≤ (n*d : ENNReal) / Fintype.card E := by
  classical
  induction n with
  | zero =>
    obtain ⟨r,hr⟩ := wrong
    have he : r = Fin.elim0 := funext fun i => i.elim0
    simp only [he] at hr
    simp only [runCoordinates, prEvent_pure, hr, ite_false, Nat.cast_zero, zero_mul,
      ENNReal.zero_div, le_refl]
  | succ n ih =>
    obtain ⟨point,hpoint⟩ := wrong
    obtain ⟨P,hP,heval⟩ := degree 0 point
    have hne : P ≠ 0 := by
      intro hz
      have h := heval (point 0)
      simp only [hz, eval_zero, Function.update_eq_self] at h
      exact hpoint h.symm
    have hfirst : Pr{let r ← uniformField E}[∀ tail, f (Fin.cons r tail) = 0] ≤
        (d : ENNReal) / Fintype.card E := by
      refine (prEvent_mono _ _ _ (fun r h => ?_)).trans
        (polynomial_collision_bound P 0 hne hP (by simp))
      rw [heval, eval_zero]
      have hp : Function.update point 0 r = Fin.cons r (fun i => point i.succ) := by
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [hp]
      exact h _
    have hb := prEvent_bind_le_prEvent_add_of_support (uniformField E)
      (fun r => Fin.cons r <$> runCoordinates E n)
      (fun r => ∀ tail, f (Fin.cons r tail) = 0) (fun point => f point = 0)
      (ε := (n*d : ENNReal) / Fintype.card E) (by
        intro r _ bad
        rw [prEvent_map]
        apply ih _ (degree.tail r)
        simpa only [not_forall] using bad)
    have hrun : runCoordinates E (n+1) =
        (uniformField E >>= fun r => Fin.cons r <$> runCoordinates E n) := by
      simp only [runCoordinates, map_eq_bind_pure_comp, Function.comp_def]
    rw [hrun]
    refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
    rw [← ENNReal.add_div]
    have hn : (d : ENNReal) + n*d = (n+1)*d := by ring
    simpa only [Nat.cast_add, Nat.cast_one] using le_of_eq (congrArg (fun z : ENNReal => z / Fintype.card E) hn)

/-- A complete adaptive pack/segment phase has numerator three per coordinate. -/
theorem packSegment_phase_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s target : E)
    (prover : Prover E) (history : List (List E))
    (wrong : target ≠ (honestProduct q d c).eval s) :
    Pr{let trace ← runSumcheck E prover 1 (p+1) history}[
      roundsValid (packOps c.point) trace.1 trace.2 target ∧
        roundsEnd (packOps c.point) trace.1 trace.2 target = packSummand q d c s trace.2] ≤
      ((p+1)*3 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (packPolynomial q d c s)) = packSummand q d c s :=
    funext (packPolynomial_eval q d c s)
  have hd : CoordinateDegree (packSummand q d c s) 3 := by
    simpa only [he] using coordinateDegree_eval (packPolynomial q d c s) (packPolynomial_degree q d c s)
  have hw : target ≠ booleanSum (packSummand q d c s) := by
    rw [booleanSum_eq_residualSum _ (fun _ => 0), pack_start_identity]
    exact wrong
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, show (11*3 : ENNReal) = 33 by norm_num, show (6*2 : ENNReal) = 12 by norm_num] using
    runSumcheck_soundness prover 1 (p+1) 3 history (packOps c.point)
      (fun i => cofactorModel (c.point i)) (packSummand q d c s) target hd hw

/-- A complete adaptive position phase has numerator thirty-three. -/
theorem position_phase_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p) (target : E)
    (prover : Prover E) (history : List (List E))
    (wrong : target ≠ packSummand q d c t.point t.packPoint) :
    Pr{let trace ← runSumcheck E prover 2 11 history}[
      roundsValid (fun _ => Sumcheck.compressedOps 2) trace.1 trace.2 target ∧
        roundsEnd (fun _ => Sumcheck.compressedOps 2) trace.1 trace.2 target = positionSummand q d c t trace.2] ≤
      (33 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (positionPolynomial q d c t)) = positionSummand q d c t :=
    funext (positionPolynomial_eval q d c t)
  have hd : CoordinateDegree (positionSummand q d c t) 3 := by
    simpa only [he] using coordinateDegree_eval (positionPolynomial q d c t) (positionPolynomial_degree q d c t)
  have hw : target ≠ booleanSum (positionSummand q d c t) := by
    rw [booleanSum_eq_residualSum _ (fun _ => 0), position_start_identity]
    exact wrong
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, show (11*3 : ENNReal) = 33 by norm_num, show (6*2 : ENNReal) = 12 by norm_num] using
    runSumcheck_soundness prover 2 11 3 history (fun _ => Sumcheck.compressedOps 2)
      (fun _ => Sumcheck.compressedModel 2) (positionSummand q d c t) target hd hw

/-- A false position claim can yield a true batched layer claim only at two fixed roots. -/
theorem beta_phase_bad_set {E : Type} [Field E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p) (target : E)
    (wrong : target ≠ positionSummand q d c t t.positionPoint)
    (check : target = eqEval c.point t.packPoint *
      mle (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val,h⟩ else 0) t.positionPoint *
      ((∑ i, muAt t.point i)*t.evaluations 0 +
        ((∑ i, muAt t.point i)+t.evaluations 1)*t.evaluations 2)) :
    ∃ bad : Finset E, bad.card ≤ 2 ∧ ∀ beta,
      ClaimHolds q d.succ (nextClaim {t with beta := beta}) → beta ∈ bad := by
  let honest : Fin 3 → E := fun k => shiftedEvaluation q d t.point t.packPoint t.positionPoint k.val
  have hne : messagePolynomial honest ≠ messagePolynomial t.evaluations := by
    intro h
    have hh := messagePolynomial_injective h
    apply wrong
    rw [check, ← hh]
    rfl
  refine ⟨collisionSet (messagePolynomial honest) (messagePolynomial t.evaluations),
    collisionSet_card _ _ (messagePolynomial_degree _) (messagePolynomial_degree _), ?_⟩
  intro beta good
  apply (mem_collisionSet _ _ hne beta).mpr
  have hg := (beta_boundary_identity q d {t with beta := beta}).mp good
  simpa only [messagePolynomial_eval, honest] using hg.symm

/-- Beta batching has numerator two after any fixed position-phase prefix. -/
theorem beta_phase_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p) (target : E)
    (wrong : target ≠ positionSummand q d c t t.positionPoint)
    (check : target = eqEval c.point t.packPoint *
      mle (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val,h⟩ else 0) t.positionPoint *
      ((∑ i, muAt t.point i)*t.evaluations 0 +
        ((∑ i, muAt t.point i)+t.evaluations 1)*t.evaluations 2)) :
    Pr{let beta ← uniformField E}[ClaimHolds q d.succ (nextClaim {t with beta := beta})] ≤
      (2 : ENNReal) / Fintype.card E := by
  have hne : (fun k : Fin 3 => shiftedEvaluation q d t.point t.packPoint t.positionPoint k.val) ≠ t.evaluations := by
    intro h
    apply wrong
    rw [check, ← h]
    rfl
  simpa only [beta_boundary_identity, eq_comm] using beta_batching_bound _ _ hne

/-- The adaptive committed-middle opening has numerator twelve. -/
theorem word_opening_phase_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (prover : Prover E) (history : List (List E))
    (wrong : ¬ MiddleHolds x q t) :
    Pr{let trace ← runSumcheck E prover 1 6 history}[
      roundsValid (fun _ => Sumcheck.compressedOps 1) trace.1 trace.2 t.middleValue ∧
        roundsEnd (fun _ => Sumcheck.compressedOps 1) trace.1 trace.2 t.middleValue = wordSummand x q t trace.2] ≤
      (12 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (wordPolynomial x q t)) = wordSummand x q t :=
    funext (wordPolynomial_eval x q t)
  have hd : CoordinateDegree (wordSummand x q t) 2 := by
    simpa only [he] using coordinateDegree_eval (wordPolynomial x q t) (wordPolynomial_degree x q t)
  have hw : t.middleValue ≠ booleanSum (wordSummand x q t) := by
    rw [booleanSum_eq_residualSum _ (fun _ => 0), word_start_identity]
    exact wrong
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, show (11*3 : ENNReal) = 33 by norm_num, show (6*2 : ENNReal) = 12 by norm_num] using
    runSumcheck_soundness prover 1 6 2 history (fun _ => Sumcheck.compressedOps 1)
      (fun _ => Sumcheck.compressedModel 1) (wordSummand x q t) t.middleValue hd hw

end CompStark.Keccak.Gkr
