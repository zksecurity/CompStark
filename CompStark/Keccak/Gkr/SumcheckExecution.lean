/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.RoundProjection

/-! # Adaptive execution bounds for concrete GKR sumcheck blocks -/

@[expose] public section
open Polynomial OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- A scalar function has the given cap on every coordinate line through every point. -/
def CoordinateDegree {E : Type*} [CommRing E] {n : Nat}
    (f : (Fin n → E) → E) (d : Nat) : Prop :=
  ∀ (i : Fin n) (point : Fin n → E), ∃ h : E[X], h.degree ≤ d ∧
    ∀ r, h.eval r = f (Function.update point i r)

/-- A bounded multivariate polynomial supplies every coordinate-line degree certificate. -/
theorem coordinateDegree_eval {E : Type*} [CommRing E] {n d : Nat}
    (H : MvPolynomial (Fin n) E) (degree : ∀ i, H.degreeOf i ≤ d) :
    CoordinateDegree (fun point => H.eval point) d := by
  classical
  intro i point
  cases n with
  | zero => exact i.elim0
  | succ n =>
    refine ⟨H.evalExcept i (Fin.removeNth i point),
      Polynomial.degree_le_of_natDegree_le ((MvPolynomial.natDegree_evalExcept_le _ _ _).trans (degree i)), ?_⟩
    intro r
    rw [MvPolynomial.eval_evalExcept, Fin.insertNth_removeNth]

/-- Coordinate degree bounds survive fixing the first coordinate. -/
theorem CoordinateDegree.tail {E : Type*} [CommRing E] {n d : Nat}
    {f : (Fin (n+1) → E) → E} (h : CoordinateDegree f d) (r : E) :
    CoordinateDegree (fun point => f (Fin.cons r point)) d := by
  intro i point
  obtain ⟨P, hP, heval⟩ := h i.succ (Fin.cons r point)
  refine ⟨P,hP,?_⟩
  intro z
  rw [heval, ← Fin.cons_update]

/-- The Boolean sum of a scalar function, with coordinates ordered from low to high. -/
def booleanSum {E : Type*} [CommRing E] {n : Nat} (f : (Fin n → E) → E) : E :=
  ∑ b : Fin n → Fin 2, f (fun i => (b i : Nat))

/-- A Boolean sum splits into the two first-coordinate faces. -/
theorem booleanSum_succ {E : Type*} [CommRing E] {n : Nat}
    (f : (Fin (n+1) → E) → E) :
    booleanSum f = booleanSum (fun point => f (Fin.cons 0 point)) +
      booleanSum (fun point => f (Fin.cons 1 point)) := by
  unfold booleanSum
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)).sum_comp]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1
  · apply Finset.sum_congr rfl
    intro b _
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · apply Finset.sum_congr rfl
    intro b _
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The first honest sumcheck polynomial is fixed before its fresh challenge. -/
theorem first_projection_exists {E : Type*} [CommRing E] {n d : Nat}
    (f : (Fin (n+1) → E) → E) (degree : CoordinateDegree f d) :
    ∃ P : E[X], P.degree ≤ d ∧ ∀ r,
      P.eval r = booleanSum (fun point => f (Fin.cons r point)) := by
  classical
  choose P hdeg heval using fun b : Fin n → Fin 2 => degree 0 (Fin.cons 0 (fun i => (b i : Nat)))
  refine ⟨∑ b, P b, (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun b _ => hdeg b), ?_⟩
  intro r
  simp only [Polynomial.eval_finsetSum, heval, Fin.update_cons_zero, booleanSum]

/-- Transmitted messages and challenges returned by a sumcheck block. -/
abbrev SumcheckTrace (E : Type) (n d : Nat) := (Fin n → Sumcheck.CompressedMessage E d) × (Fin n → E)

/-- Execute a sumcheck block with each prover message chosen from its strict wire prefix. -/
noncomputable def runSumcheck (E : Type) [Fintype E] [Nonempty E]
    (prover : Prover E) (d : Nat) : (n : Nat) → List (List E) → ProbComp (SumcheckTrace E n d)
  | 0, _ => pure (Fin.elim0,Fin.elim0)
  | n+1, history => do
      let sent := vectorMessage (prover history (d+1))
      let r ← uniformField E
      let tail ← runSumcheck E prover d n (history ++ [List.ofFn (messageVector sent),[r]])
      pure (Fin.cons sent tail.1, Fin.cons r tail.2)

/-- A complete adaptive block loses its degree cap per round under its claim-aware models. -/
theorem runSumcheck_soundness {E : Type} [Field E] [Fintype E] [DecidableEq E]
    (prover : Prover E) (d n degree : Nat) (history : List (List E))
    (ops : Fin n → Sumcheck.MessageOps E (Sumcheck.CompressedMessage E d))
    (model : ∀ i, Sumcheck.MessageModel ({0,1} : Finset E) (ops i) degree)
    (f : (Fin n → E) → E) (target : E)
    (cap : CoordinateDegree f degree) (wrong : target ≠ booleanSum f) :
    Pr{let trace ← runSumcheck E prover d n history}[
      roundsValid ops trace.1 trace.2 target ∧ roundsEnd ops trace.1 trace.2 target = f trace.2] ≤
      (n*degree : ENNReal) / Fintype.card E := by
  classical
  induction n generalizing history target with
  | zero =>
    have hf : booleanSum f = f Fin.elim0 := by
      unfold booleanSum
      have he (b : Fin 0 → Fin 2) : (fun i => ((b i : Nat) : E)) = Fin.elim0 := by
        funext i; exact i.elim0
      simp only [he, Fintype.sum_unique]
    have hne : target ≠ f Fin.elim0 := by simpa only [hf] using wrong
    simp only [runSumcheck, prEvent_pure, roundsValid, roundsEnd, true_and, hne, ite_false,
      Nat.cast_zero, zero_mul, ENNReal.zero_div]
    exact le_rfl
  | succ n ih =>
    let sent := vectorMessage (prover history (d+1))
    let ev := (ops 0).evaluate target sent
    obtain ⟨P,hP,heval⟩ := first_projection_exists f cap
    have hrun : runSumcheck E prover d (n+1) history =
        (uniformField E >>= fun r => (fun tail : SumcheckTrace E n d =>
          (Fin.cons sent tail.1,Fin.cons r tail.2)) <$>
            runSumcheck E prover d n (history ++ [List.ofFn (messageVector sent),[r]])) := by
      simp only [runSumcheck, map_eq_bind_pure_comp, Function.comp_def, sent]
    rw [hrun]
    by_cases check : (ops 0).accept target sent = true
    · have hsum : ((model 0).interpret target sent).val.eval 0 +
          ((model 0).interpret target sent).val.eval 1 = target := by
        simpa only [Finset.sum_pair (zero_ne_one : (0 : E) ≠ 1)] using
          ((model 0).accept_iff target sent).mp check
      have hne : P ≠ ((model 0).interpret target sent).val := by
        intro equal
        have hwrong := wrong
        rw [booleanSum_succ, ← heval 0, ← heval 1, equal, hsum] at hwrong
        exact hwrong rfl
      have hfirst : Pr{let r ← uniformField E}[
          ev r = booleanSum (fun point => f (Fin.cons r point))] ≤
          (degree : ENNReal) / Fintype.card E := by
        simpa only [ev, (model 0).evaluate_eq, heval, eq_comm] using
          polynomial_collision_bound P ((model 0).interpret target sent).val hne hP
            (Polynomial.mem_degreeLE.mp ((model 0).interpret target sent).property)
      have hb := prEvent_bind_le_prEvent_add_of_support (uniformField E)
        (fun r => (fun tail : SumcheckTrace E n d =>
          (Fin.cons sent tail.1,Fin.cons r tail.2)) <$>
            runSumcheck E prover d n (history ++ [List.ofFn (messageVector sent),[r]]))
        (fun r => ev r = booleanSum (fun point => f (Fin.cons r point)))
        (fun trace => roundsValid ops trace.1 trace.2 target ∧ roundsEnd ops trace.1 trace.2 target = f trace.2)
        (ε := (n*degree : ENNReal) / Fintype.card E) (by
          intro r _ bad
          rw [prEvent_map]
          simpa only [roundsValid, roundsEnd, Fin.cons_zero, Fin.cons_succ, check, true_and, ev] using
            ih (history ++ [List.ofFn (messageVector sent),[r]]) (fun i => ops i.succ)
              (fun i => model i.succ) (fun point => f (Fin.cons r point))
              (ev r) (cap.tail r) bad)
      refine (hb.trans (add_le_add hfirst le_rfl)).trans ?_
      rw [← ENNReal.add_div]
      push_cast
      ring_nf
      exact le_rfl
    · apply prEvent_bind_le_of_forall_le
      intro r
      rw [prEvent_map]
      simp only [roundsValid, Fin.cons_zero, check, Bool.false_eq_true, false_and, prEvent_false, zero_le]

end CompStark.Keccak.Gkr
