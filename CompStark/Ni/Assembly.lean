/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BadQuery

/-! # Knowledge soundness in the random-oracle model, assembled

The game of `run` (`game`) makes at most `Q + verifierQueries` oracle calls. B's
`prEvent_exists_fresh_bad_le` bounds the probability of an event that forces a fresh bad query by
the number of calls times the probability that one fresh answer is bad. Here a fresh answer is bad
if its digest clashes (`prob_clash_le`: `3 q / |F|^8`) or it makes its round bad
(`prob_roundBad_le`: the largest round error at the proximity loss), and the event, an accepted
proof the extractor cannot open, forces such a query (`exists_badAt`). The bound holds at every
loss, so at the infimum: `q · roundError + hashError F q`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Sound CompStark.Iop CompStark.RandomOracle
open OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### Logged computations on an answer table -/

section Logged
variable {K : Nat} (answer : (q : Query F) → Answer K q)

omit [BaseField F] in
theorem tableQueryLog_map {α β : Type} (f : α → β) (oa : OracleComp (spec F K) α) :
    tableQueryLog (f <$> oa) answer = tableQueryLog oa answer := by
  rw [map_eq_bind_pure_comp, tableQueryLog_bind, Function.comp_apply, tableQueryLog_pure,
    List.append_nil]

omit [BaseField F] in
theorem evalWithAnswerFn_logged {α : Type} (oa : OracleComp (spec F K) α) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (simulateQ loggingOracle oa).run =
      (evalWithAnswerFn (QueryImpl.ofFn answer) oa, tableQueryLog oa answer) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [run_simulateQ_loggingOracle_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map, ih,
      tableQueryLog_query_bind]
    simp only [evalWithAnswerFn_bind]
    rfl

omit [BaseField F] in
theorem tableQueryLog_logged {α : Type} (oa : OracleComp (spec F K) α) :
    tableQueryLog (simulateQ loggingOracle oa).run answer = tableQueryLog oa answer := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [run_simulateQ_loggingOracle_query_bind, tableQueryLog_query_bind, tableQueryLog_map,
      ih, tableQueryLog_query_bind]

omit [BaseField F] in
theorem length_tableQueryLog_le {α : Type} (oa : OracleComp (spec F K) α) (n : Nat)
    (hn : IsTotalQueryBound oa n) : (tableQueryLog oa answer).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp only [tableQueryLog_pure, List.length_nil, Nat.zero_le]
  | query_bind t k ih =>
    obtain ⟨hpos, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rw [tableQueryLog_query_bind, List.length_cons]
    have := ih (answer t) (n - 1) (hk _)
    omega

end Logged

/-! ### The game -/

section Game
variable (S : Iop.Setup EF) (publicValues : List F)

/-- The game of `run`: the prover, logged, then the verifier on its proof. -/
def game (prover : NIProver S) :
    OracleComp (spec F S.streamLen)
        (Proof F EF × QueryLog (spec F S.streamLen) × Except String Unit) :=
        do
  let (proof, log) ← (simulateQ loggingOracle prover).run
  return (proof, log, ← S.verifyRo proof publicValues)

theorem run_eq (prover : NIProver S) :
    run S publicValues prover = (simulateQ randomOracle (game S publicValues prover)).run' ∅ :=
  rfl

theorem isTotalQueryBound_game (prover : NIProver S) (Q : Nat)
    (hQ : prover.IsTotalQueryBound Q) :
    (game S publicValues prover).IsTotalQueryBound (Q + S.verifierQueries) := by
  refine isTotalQueryBound_bind
    ((isTotalQueryBound_run_simulateQ_loggingOracle_iff prover Q).mpr hQ) fun x ↦ ?_
  obtain ⟨proof, log⟩ := x
  exact (isTotalQueryBound_bind (n₂ := 0) (S.isTotalQueryBound_verifyRo proof publicValues)
    fun v ↦ (show IsTotalQueryBound (pure (proof, log, v) :
      OracleComp (spec F S.streamLen) _) 0 from trivial)).mono (by omega)

variable (answer : (q : Query F) → Answer S.streamLen q) (prover : NIProver S)

theorem evalWithAnswerFn_game :
    evalWithAnswerFn (QueryImpl.ofFn answer) (game S publicValues prover) =
      (evalWithAnswerFn (QueryImpl.ofFn answer) prover, tableQueryLog prover answer,
        evalWithAnswerFn (QueryImpl.ofFn answer)
          (S.verifyRo (evalWithAnswerFn (QueryImpl.ofFn answer) prover) publicValues)) := by
  simp only [game, evalWithAnswerFn_bind, evalWithAnswerFn_logged, evalWithAnswerFn_pure]

theorem tableQueryLog_game :
    tableQueryLog (game S publicValues prover) answer = tableQueryLog prover answer ++
      tableQueryLog (S.verifyRo (evalWithAnswerFn (QueryImpl.ofFn answer) prover) publicValues)
        answer := by
  simp only [game]
  rw [tableQueryLog_bind, evalWithAnswerFn_logged, tableQueryLog_logged, tableQueryLog_bind,
    tableQueryLog_pure, List.append_nil]

end Game

/-! ### The bound -/

section Bound
variable (S : Iop.Setup EF) (publicValues : List F) (δ δ' : NNReal)

/-- The event of knowledge soundness: an accepted proof for `2 ^ logN` rows, no trace close to
the committed one satisfying the AIR. -/
def Unopened (result : Proof F EF × QueryLog (spec F S.streamLen) × Except String Unit) : Prop :=
  result.2.2 = .ok () ∧ result.1.degreeBits = S.logN ∧
    ∀ trace ∈ closeTraces S δ' (committedTrace S result.2.1 result.1),
      ¬ S.air.Satisfied S.logN trace publicValues

theorem hashError_eq (q : Nat) :
    hashError F q = q * (((3 * q : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹) := by
  rw [hashError, card_digest, Nat.cast_pow, div_eq_mul_inv]
  push_cast
  ring

/-- **Knowledge soundness in the random-oracle model**, with the event spelled out. -/
theorem prob_unopened_le (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat) (prover : NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let result ← run S publicValues prover}[Unopened S publicValues δ' result] ≤
      (Q + S.verifierQueries) * roundError S δ δ' + hashError F (Q + S.verifierQueries) := by
  set n := Q + S.verifierQueries
  have hn0 : 0 < n := by unfold n Setup.verifierQueries; omega
  by_cases hbig : Fintype.card (Digest F) ≤ 3 * n
  · refine (prEvent_le_one _).trans (le_add_left ?_)
    rw [hashError_eq]
    have hcard : (Fintype.card (Digest F) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
    calc (1 : ℝ≥0∞) ≤ ((3 * n : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ := by
          rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hcard)
            (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
          exact_mod_cast hbig
      _ ≤ _ := le_mul_of_one_le_left (by positivity)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0.ne')
  have hsmall : 3 * n < Fintype.card (Digest F) := by omega
  have hloss : ∀ loss, Pr{let result ← run S publicValues prover}[
      Unopened S publicValues δ' result] ≤ n * roundBound S δ δ' loss + hashError F n := by
    intro loss
    rw [run_eq]
    refine (prEvent_exists_fresh_bad_le (game S publicValues prover) n
      (isTotalQueryBound_game S publicValues prover Q hQ) (Unopened S publicValues δ')
      (fun pre t u ↦ Clash pre t u ∨ RoundBad S publicValues δ δ' loss pre t u)
      (((3 * n : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ + roundBound S δ δ' loss)
      (fun pre t hlen _ ↦ (prEvent_or_le _ _ _).trans
        (add_le_add (prob_clash_le _ n pre hlen t)
          (prob_roundBad_le S publicValues δ δ' loss pre t)))
      fun answer hev ↦ ?_).trans ?_
    · rw [evalWithAnswerFn_game] at hev
      obtain ⟨hok, hdb, hfail⟩ := hev
      dsimp only at hok hdb hfail
      rw [Setup.evalWithAnswerFn_verifyRo, ite_eq_left hdb] at hok
      have hlog := tableQueryLog_game S publicValues answer prover
      rw [Setup.tableQueryLog_verifyRo, ite_eq_left hdb, ← tableQueryLog_verifyWith] at hlog
      have hlen := length_tableQueryLog_le answer _ n
        (isTotalQueryBound_game S publicValues prover Q hQ)
      rw [hlog] at hlen
      set proof := evalWithAnswerFn (QueryImpl.ofFn answer) prover
      obtain ⟨p, hp, hfresh, hbad⟩ := exists_badAt S publicValues δ δ' loss hδ' answer proof
        (tableQueryLog prover answer) (consistent_tableQueryLog _) hdb hok (by omega) hfail
      rw [hlog]
      exact ⟨_, _, _, (List.take_append_drop p _).symm.trans
        (by rw [List.drop_eq_getElem_cons hp]), hfresh, hbad⟩
    · rw [mul_add, add_comm, hashError_eq]
  calc _ ≤ ⨅ loss, (n * roundBound S δ δ' loss + hashError F n) := le_iInf hloss
    _ = n * roundError S δ δ' + hashError F n := by
      rw [roundError_eq, ENNReal.mul_iInf_of_ne (by exact_mod_cast hn0.ne')
        (ENNReal.natCast_ne_top _), ENNReal.iInf_add]
    _ = _ := by simp only [n, Nat.cast_add]

end Bound

end CompStark.Ni
