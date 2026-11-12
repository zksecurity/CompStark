/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.Claims
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness

/-!
# Fixed-table local soundness bounds for Keccak GKR

Polynomial collision tests and sumcheck successors keep the PCS-supplied table fixed.
The adaptive wire execution admits a union bound by the sum of its per-challenge losses.
-/

@[expose] public section

open Polynomial OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- A full coefficient vector interpreted as a polynomial. -/
noncomputable def messagePolynomial {E : Type*} [CommRing E] {n : Nat}
    (a : Fin (n+1) → E) : E[X] := ∑ i, monomial i.val (a i)

/-- Evaluating the coefficient polynomial is the wire evaluator. -/
theorem messagePolynomial_eval {E : Type*} [CommRing E] {n : Nat}
    (a : Fin (n+1) → E) (r : E) : (messagePolynomial a).eval r = polyEval a r := by
  simp only [messagePolynomial, eval_finsetSum, eval_monomial, polyEval]

/-- The coefficient-vector interpretation respects its degree cap. -/
theorem messagePolynomial_degree {E : Type*} [CommRing E] {n : Nat}
    (a : Fin (n+1) → E) : (messagePolynomial a).degree ≤ n := by
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro i _
  exact (degree_monomial_le _ _).trans (by exact_mod_cast Nat.le_of_lt_succ i.isLt)

/-- The input coefficients are recovered without any reduction modulo the field size. -/
theorem messagePolynomial_coeff {E : Type*} [CommRing E] {n : Nat}
    (a : Fin (n+1) → E) (i : Fin (n+1)) : (messagePolynomial a).coeff i.val = a i := by
  simp only [messagePolynomial, finsetSum_coeff, coeff_monomial, Fin.val_inj]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Distinct coefficient vectors remain distinct polynomials, including over the binary field. -/
theorem messagePolynomial_injective {E : Type*} [CommRing E] {n : Nat} :
    Function.Injective (messagePolynomial (E := E) (n := n)) := by
  intro a b h
  funext i
  simpa only [messagePolynomial_coeff] using congrArg (fun f : E[X] => f.coeff i.val) h

/-- Schwartz–Zippel for a polynomial fixed before the fresh GKR challenge. -/
theorem polynomial_collision_bound {E : Type} [Field E] [Fintype E] {n : Nat}
    (honest sent : E[X]) (hne : honest ≠ sent) (hh : honest.degree ≤ n)
    (hs : sent.degree ≤ n) :
    Pr{let r ← uniformField E}[honest.eval r = sent.eval r] ≤
      (n : ENNReal) / Fintype.card E := by
  let _ := SampleableType.ofFintype E
  exact Probability.prob_polynomial_eval_eq_le hne
    (natDegree_le_of_degree_le hh) (natDegree_le_of_degree_le hs)

/-- One initial identity-testing coordinate, with the table fixed before sampling.
The remaining-coordinate family is fixed at the authored prefix. -/
theorem start_sampling_bound {E : Type} [Field E] [Fintype E] {p : Nat} {ι : Type*}
    (q₀ : Witness p) (residual : Witness p → ι → E[X])
    (degree : ∀ i, (residual q₀ i).degree ≤ 1)
    (wrong : ∃ i, residual q₀ i ≠ 0) :
    Pr{let r ← uniformField E}[∀ i, (residual q₀ i).eval r = 0] ≤
      (1 : ENNReal) / Fintype.card E := by
  obtain ⟨i, hi⟩ := wrong
  refine (prEvent_mono _ _ _ (fun _ h => h i)).trans ?_
  simpa only [eval_zero, Nat.cast_one] using
    polynomial_collision_bound (n := 1) (residual q₀ i) 0 hi (degree i) (by simp)

/-- A fixed false round sum can become a true successor only at a collision root. -/
theorem sumcheck_round_bound {E : Type} [Field E] [Fintype E] {n : Nat}
    (honest : E[X]) (sent : Fin (n+1) → E) (target : E)
    (degree : honest.degree ≤ n)
    (wrong : honest.eval 0 + honest.eval 1 ≠ target)
    (check : polyEval sent 0 + polyEval sent 1 = target) :
    Pr{let r ← uniformField E}[honest.eval r = polyEval sent r] ≤
      (n : ENNReal) / Fintype.card E := by
  have hne : honest ≠ messagePolynomial sent := by
    intro h
    apply wrong
    simpa only [h, messagePolynomial_eval] using check
  simpa only [messagePolynomial_eval] using
    polynomial_collision_bound honest (messagePolynomial sent) hne degree (messagePolynomial_degree sent)

/-- Quadratic batching of three fixed shifted evaluations has error at most two roots. -/
theorem beta_batching_bound {E : Type} [Field E] [Fintype E]
    (honest sent : Fin 3 → E) (wrong : honest ≠ sent) :
    Pr{let r ← uniformField E}[polyEval honest r = polyEval sent r] ≤
      (2 : ENNReal) / Fintype.card E := by
  simpa only [messagePolynomial_eval, Nat.cast_ofNat] using
    polynomial_collision_bound (messagePolynomial honest) (messagePolynomial sent)
      (fun h => wrong (messagePolynomial_injective h))
      (messagePolynomial_degree honest) (messagePolynomial_degree sent)

/-- The honest product polynomial has degree at most 46 for every fixed table and prefix. -/
theorem honestProduct_degree {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) : (honestProduct q d c).degree ≤ 46 := by
  unfold honestProduct
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro m _
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro b _
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j _
  apply (degree_smul_le _ _).trans
  dsimp only [packedLinear]
  apply (degree_add_le _ _).trans
  apply max_le
  · exact Embedding.kemb_mul_degree _ _
  · rw [← Embedding.kemb_add]
    exact Embedding.kemb_mul_degree _ _

/-- The wire projection of a product message agrees with the polynomial projection. -/
theorem project_messagePolynomial {E : Type*} [CommRing E]
    (a : Fin 47 → E) (i : Fin 16) : Embedding.kproj (messagePolynomial a) i = projectMessage a i := by
  simp only [Embedding.kproj, LinearMap.coe_mk, AddHom.coe_mk,
    messagePolynomial_coeff, projectMessage]

/-- For the fixed committed table, a false layer claim passes the product test at at most 46 roots. -/
theorem product_evaluation_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (d : Fin 12) (c : Claim E p) (sent : Fin 47 → E)
    (wrong : ¬ ClaimHolds q₀ d.castSucc c)
    (check : (∑ i, c.mu i * projectMessage sent i) + constantContribution d c = c.value) :
    Pr{let r ← uniformField E}[(honestProduct q₀ d c).eval r = polyEval sent r] ≤
      (46 : ENNReal) / Fintype.card E := by
  have hne : honestProduct q₀ d c ≠ messagePolynomial sent := by
    intro h
    apply wrong
    apply (layer_projection_identity q₀ d c).mpr
    simpa only [h, project_messagePolynomial] using check
  simpa only [messagePolynomial_eval, Nat.cast_ofNat] using
    polynomial_collision_bound (honestProduct q₀ d c) (messagePolynomial sent) hne
      (honestProduct_degree q₀ d c) (messagePolynomial_degree sent)

section SumcheckBounds
open Sumcheck.Interaction Sumcheck.Interaction.SingleRound Sumcheck.Interaction.MultivariateRound

/-- A pack or segment cubic round keeps the PCS table fixed in its successor relation. -/
theorem packSegment_challenge_bound {E : Type} [Field E] [Fintype E] {p n : Nat}
    (q₀ : Witness p) (summand : Witness p → Sumcheck.Spec.OracleStatement E n 3 ())
    (D : Fin 2 ↪ E) (i : Fin n) (stmt : Sumcheck.Spec.StatementRound E n i.castSucc)
    (sent : Message E 3)
    (wrong : ¬ closedRelation E n 3 D i.castSucc
      ⟨stmt, (polynomialFamily E n 3).behaviorOfRealizations (fun _ => summand q₀)⟩)
    (check : ((Finset.univ.map D).toList.map (fun x => sent.val.eval x)).sum = stmt.target) :
    Pr{let r ← uniformField E}[closedRelation E n 3 D i.succ
      ⟨⟨sent.val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily E n 3).behaviorOfRealizations (fun _ => summand q₀)⟩] ≤
      (3 : ENNReal) / Fintype.card E := by
  let _ := SampleableType.ofFintype E
  simpa only [uniformField, Nat.cast_ofNat] using
    uniform_successor_soundness n 3 E D i stmt (summand q₀) sent wrong check

/-- A position cubic has the same fixed-table three-root successor bound. -/
theorem position_challenge_bound {E : Type} [Field E] [Fintype E] {p n : Nat}
    (q₀ : Witness p) (summand : Witness p → Sumcheck.Spec.OracleStatement E n 3 ())
    (D : Fin 2 ↪ E) (i : Fin n) (stmt : Sumcheck.Spec.StatementRound E n i.castSucc)
    (sent : Message E 3)
    (wrong : ¬ closedRelation E n 3 D i.castSucc
      ⟨stmt, (polynomialFamily E n 3).behaviorOfRealizations (fun _ => summand q₀)⟩)
    (check : ((Finset.univ.map D).toList.map (fun x => sent.val.eval x)).sum = stmt.target) :
    Pr{let r ← uniformField E}[closedRelation E n 3 D i.succ
      ⟨⟨sent.val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily E n 3).behaviorOfRealizations (fun _ => summand q₀)⟩] ≤
      (3 : ENNReal) / Fintype.card E :=
  packSegment_challenge_bound q₀ summand D i stmt sent wrong check

/-- A committed-word opening round has a fixed-table quadratic successor bound. -/
theorem word_opening_challenge_bound {E : Type} [Field E] [Fintype E] {p n : Nat}
    (q₀ : Witness p) (summand : Witness p → Sumcheck.Spec.OracleStatement E n 2 ())
    (D : Fin 2 ↪ E) (i : Fin n) (stmt : Sumcheck.Spec.StatementRound E n i.castSucc)
    (sent : Message E 2)
    (wrong : ¬ closedRelation E n 2 D i.castSucc
      ⟨stmt, (polynomialFamily E n 2).behaviorOfRealizations (fun _ => summand q₀)⟩)
    (check : ((Finset.univ.map D).toList.map (fun x => sent.val.eval x)).sum = stmt.target) :
    Pr{let r ← uniformField E}[closedRelation E n 2 D i.succ
      ⟨⟨sent.val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily E n 2).behaviorOfRealizations (fun _ => summand q₀)⟩] ≤
      (2 : ENNReal) / Fintype.card E := by
  let _ := SampleableType.ofFintype E
  simpa only [uniformField, Nat.cast_ofNat] using
    uniform_successor_soundness n 2 E D i stmt (summand q₀) sent wrong check

/-- A bit-slice opening round has a fixed-table quadratic successor bound. -/
theorem slice_opening_challenge_bound {E : Type} [Field E] [Fintype E] {p n : Nat}
    (q₀ : Witness p) (summand : Witness p → Sumcheck.Spec.OracleStatement E n 2 ())
    (D : Fin 2 ↪ E) (i : Fin n) (stmt : Sumcheck.Spec.StatementRound E n i.castSucc)
    (sent : Message E 2)
    (wrong : ¬ closedRelation E n 2 D i.castSucc
      ⟨stmt, (polynomialFamily E n 2).behaviorOfRealizations (fun _ => summand q₀)⟩)
    (check : ((Finset.univ.map D).toList.map (fun x => sent.val.eval x)).sum = stmt.target) :
    Pr{let r ← uniformField E}[closedRelation E n 2 D i.succ
      ⟨⟨sent.val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily E n 2).behaviorOfRealizations (fun _ => summand q₀)⟩] ≤
      (2 : ENNReal) / Fintype.card E :=
  word_opening_challenge_bound q₀ summand D i stmt sent wrong check

end SumcheckBounds
/-- Scalar prefix claims preserve truth backwards across prover messages and have local challenge bounds. -/
noncomputable def WireLocallyBounded {E : Type} [Fintype E] [Nonempty E]
    (state : List WireStep → List (List E) → Prop) (prover : Prover E) :
    (s : List WireStep) → List (List E) → Prop
  | [], _ => True
  | .message n :: rest, history =>
      let next := history ++ [List.ofFn (prover history n)]
      (state rest next → state (.message n :: rest) history) ∧ WireLocallyBounded state prover rest next
  | .challenge k :: rest, history =>
      (Pr{let r ← uniformField E}[¬ state (.challenge k :: rest) history ∧ state rest (history ++ [[r]])] ≤
        (k.numerator : ENNReal) / Fintype.card E) ∧
      ∀ r, WireLocallyBounded state prover rest (history ++ [[r]])

/-- A union bound along the actual public schedule, including adaptive prover messages. -/
theorem runWire_union_bound {E : Type} [Fintype E] [Nonempty E]
    (state : List WireStep → List (List E) → Prop) (prover : Prover E)
    (s : List WireStep) (history : List (List E))
    (bounded : WireLocallyBounded state prover s history) :
    Pr{let messages ← runWire E prover s history}[
      ¬ state s history ∧ state [] (history ++ messages)] ≤
        (numeratorSum s : ENNReal) / Fintype.card E := by
  classical
  induction s generalizing history with
  | nil =>
    simp only [runWire, prEvent_pure, List.append_nil, not_and_self, ite_false,
      numeratorSum, List.map_nil, List.sum_nil, Nat.cast_zero, ENNReal.zero_div]
    exact le_rfl
  | cons step rest ih =>
    cases step with
    | message n =>
      let msg := List.ofFn (prover history n)
      have htail := ih (history ++ [msg]) bounded.2
      have hrun : runWire E prover (.message n :: rest) history =
          List.cons msg <$> runWire E prover rest (history ++ [msg]) := by
        simp only [runWire, map_eq_bind_pure_comp, Function.comp_def, msg]
      rw [hrun, prEvent_map]
      have hinclusion : Pr{let suffix ← runWire E prover rest (history ++ [msg])}[
          ¬ state (.message n :: rest) history ∧ state [] (history ++ msg :: suffix)] ≤
          Pr{let suffix ← runWire E prover rest (history ++ [msg])}[
            ¬ state rest (history ++ [msg]) ∧ state [] ((history ++ [msg]) ++ suffix)] := by
        apply prEvent_mono
        intro suffix h
        refine ⟨fun good => h.1 (bounded.1 good), ?_⟩
        simpa only [List.append_assoc, List.singleton_append] using h.2
      exact (hinclusion.trans htail).trans (by
        simp only [numeratorSum, List.map_cons, List.sum_cons, Nat.zero_add]
        exact le_rfl)
    | challenge k =>
      by_cases hfalse : ¬ state (.challenge k :: rest) history
      · have hstep : Pr{let r ← uniformField E}[state rest (history ++ [[r]])] ≤
            (k.numerator : ENNReal) / Fintype.card E := by
          simpa only [hfalse, not_false_eq_true, true_and] using bounded.1
        have htail := prEvent_bind_le_prEvent_add_of_support (uniformField E)
          (fun r => List.cons [r] <$> runWire E prover rest (history ++ [[r]]))
          (fun r => state rest (history ++ [[r]]))
          (fun messages => state [] (history ++ messages))
          (ε := (numeratorSum rest : ENNReal) / Fintype.card E) (by
            intro r _ bad
            rw [prEvent_map]
            have bound := ih (history ++ [[r]]) (bounded.2 r)
            simpa only [bad, not_false_eq_true, true_and, List.append_assoc, List.singleton_append] using bound)
        have hrun : runWire E prover (.challenge k :: rest) history =
            (uniformField E >>= fun r => List.cons [r] <$> runWire E prover rest (history ++ [[r]])) := by
          simp only [runWire, map_eq_bind_pure_comp, Function.comp_def]
        rw [hrun]
        simp only [hfalse, not_false_eq_true, true_and]
        refine (htail.trans (add_le_add hstep le_rfl)).trans ?_
        simp only [numeratorSum, List.map_cons, List.sum_cons, Nat.cast_add, ENNReal.add_div]
        exact le_rfl
      · have empty : ∀ messages : List (List E),
            ¬ (¬ state (.challenge k :: rest) history ∧ state [] (history ++ messages)) :=
          fun _ h => hfalse h.1
        refine (prEvent_mono _ _ (fun _ => False) (fun messages h => empty messages h)).trans ?_
        simp only [prEvent_false, zero_le]

end CompStark.Keccak.Gkr
