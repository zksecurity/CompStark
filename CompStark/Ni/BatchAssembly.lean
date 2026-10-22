/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchBadQuery
public import CompStark.Ni.Assembly
public import CompStark.Sound.Inclusion

/-! # Knowledge soundness of the batch STARK in the random-oracle model, assembled

As for the STARK (`Ni/Assembly.lean`): the game of `Iop.Batch.run` (`gameB`) makes at most
`Q + verifierQueries` oracle calls, the setup's, the prover's and the verifier's. A fresh answer
is bad if its digest clashes (`prob_clash_le`: `(2 ^ h + 2) q / |F|^8` for caps of height `h`) or
it makes its batch round bad (`prob_roundBadB_le`: the largest batch round error at the proximity
loss), and an accepted proof the extractor cannot open forces such a query (`exists_badAtB`). The
bound holds at every loss, so at the infimum: `q · roundError + hashError F h q`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Sound CompStark.Iop CompStark.RandomOracle
open OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### The game -/

section Game
variable (S : Iop.Batch.Setup EF) (publicValues : Fin S.k → List F)

/-- The batch setup, then the prover. -/
def setupAndProveB (prover : Iop.Batch.NIProver S) :
    OracleComp (spec F S.streamLen) (CompStark.Batch.Common F × CompStark.Batch.BatchProof F EF) :=
  do
  let common ← S.setupRo
  return (common, ← prover)

/-- The game of `Iop.Batch.run`: the setup and the prover, logged, then the verifier on the proof
against the setup's common data. -/
def gameB (prover : Iop.Batch.NIProver S) :
    OracleComp (spec F S.streamLen)
      (CompStark.Batch.BatchProof F EF × QueryLog (spec F S.streamLen) × Except String Unit) := do
  let ((common, proof), log) ← (simulateQ loggingOracle (setupAndProveB S prover)).run
  return (proof, log, ← S.verifyRo common proof publicValues)

theorem run_eqB (prover : Iop.Batch.NIProver S) :
    Iop.Batch.run S publicValues prover =
      (simulateQ randomOracle (gameB S publicValues prover)).run' ∅ :=
  rfl

theorem isTotalQueryBound_gameB (prover : Iop.Batch.NIProver S) (Q : Nat)
    (hQ : prover.IsTotalQueryBound Q) :
    (gameB S publicValues prover).IsTotalQueryBound (Q + S.verifierQueries) := by
  have hsp : (setupAndProveB S prover).IsTotalQueryBound (S.setupQueries + Q) :=
    isTotalQueryBound_bind S.isTotalQueryBound_setupRo fun common ↦
      (isTotalQueryBound_bind (n₂ := 0) hQ fun proof ↦
        (show IsTotalQueryBound (pure (common, proof) : OracleComp (spec F S.streamLen) _) 0
          from trivial)).mono (by omega)
  refine (isTotalQueryBound_bind (n₂ := S.verifierCalls)
    ((isTotalQueryBound_run_simulateQ_loggingOracle_iff _ _).mpr hsp) fun x ↦ ?_).mono
    (by unfold Iop.Batch.Setup.verifierQueries; omega)
  obtain ⟨⟨common, proof⟩, log⟩ := x
  exact (isTotalQueryBound_bind (n₂ := 0)
    (S.isTotalQueryBound_verifyBatchWith common proof (List.ofFn publicValues))
    fun v ↦ (show IsTotalQueryBound (pure (proof, log, v) :
      OracleComp (spec F S.streamLen) _) 0 from trivial)).mono (by omega)

variable (answer : (q : Query F) → Answer S.streamLen q) (prover : Iop.Batch.NIProver S)

theorem evalWithAnswerFn_setupAndProveB :
    evalWithAnswerFn (QueryImpl.ofFn answer) (setupAndProveB S prover) =
      (CompStark.Batch.commonWith (idealOf answer) S.params S.instances,
        evalWithAnswerFn (QueryImpl.ofFn answer) prover) := by
  simp only [setupAndProveB, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    evalWithAnswerFn_setupRoB]

theorem tableQueryLog_setupAndProveB :
    tableQueryLog (setupAndProveB S prover) answer =
      tableQueryLog S.setupRo answer ++ tableQueryLog prover answer := by
  simp only [setupAndProveB]
  rw [tableQueryLog_bind, tableQueryLog_bind]
  simp only [tableQueryLog_pure, List.append_nil]

theorem evalWithAnswerFn_gameB :
    evalWithAnswerFn (QueryImpl.ofFn answer) (gameB S publicValues prover) =
      (evalWithAnswerFn (QueryImpl.ofFn answer) prover,
        tableQueryLog (setupAndProveB S prover) answer,
        CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances
          (CompStark.Batch.commonWith (idealOf answer) S.params S.instances)
          (evalWithAnswerFn (QueryImpl.ofFn answer) prover) (List.ofFn publicValues)) := by
  simp only [gameB, evalWithAnswerFn_bind, evalWithAnswerFn_logged, evalWithAnswerFn_pure,
    evalWithAnswerFn_setupAndProveB, Iop.Batch.Setup.verifyRo, evalWithAnswerFn_verifyBatchWith]

theorem tableQueryLog_gameB :
    tableQueryLog (gameB S publicValues prover) answer =
      tableQueryLog (setupAndProveB S prover) answer ++
      tableQueryLog (CompStark.Batch.verifyBatchWith (ideal F S.streamLen) S.params S.instances
        (CompStark.Batch.commonWith (idealOf answer) S.params S.instances)
        (evalWithAnswerFn (QueryImpl.ofFn answer) prover) (List.ofFn publicValues)) answer := by
  simp only [gameB]
  rw [tableQueryLog_bind, evalWithAnswerFn_logged, tableQueryLog_logged, tableQueryLog_bind,
    tableQueryLog_pure, List.append_nil, evalWithAnswerFn_setupAndProveB]
  rfl

end Game

/-! ### The bound -/

section Bound
variable (S : Iop.Batch.Setup EF) (publicValues : Fin S.k → List F) (δ δ' : NNReal)

/-- The event of knowledge soundness: an accepted proof for the instances' trace lengths, no
tuple of traces close to the committed ones satisfying the batch. -/
def UnopenedB
    (result : CompStark.Batch.BatchProof F EF × QueryLog (spec F S.streamLen) ×
      Except String Unit) : Prop :=
  result.2.2 = .ok () ∧ result.1.degreeBits.toList = List.ofFn S.logN ∧
    ∀ traces ∈ Iop.Batch.closeTraces S δ' (Iop.Batch.committedTraces S result.2.1 result.1),
      ¬ S.Satisfied traces publicValues

/-- **Knowledge soundness of the batch STARK in the random-oracle model**, for any event that,
on every answer table, implies `UnopenedB`. -/
theorem prob_le_of_unopenedB (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat)
    (prover : Iop.Batch.NIProver S) (hQ : prover.IsTotalQueryBound Q)
    (E : CompStark.Batch.BatchProof F EF × QueryLog (spec F S.streamLen) × Except String Unit →
      Prop)
    (hE : ∀ answer, E (evalWithAnswerFn (QueryImpl.ofFn answer) (gameB S publicValues prover)) →
      UnopenedB S publicValues δ' (evalWithAnswerFn (QueryImpl.ofFn answer)
        (gameB S publicValues prover))) :
    Pr{let result ← Iop.Batch.run S publicValues prover}[E result] ≤
      (Q + S.verifierQueries) * Iop.Batch.roundError S δ δ' +
        hashError F S.params.capHeight (Q + S.verifierQueries) := by
  set n := Q + S.verifierQueries
  set c := 2 ^ S.params.capHeight + 2
  have hn0 : 0 < n := by
    unfold n Iop.Batch.Setup.verifierQueries Iop.Batch.Setup.verifierCalls; omega
  by_cases hbig : Fintype.card (Digest F) ≤ c * n
  · refine (prEvent_le_one _).trans (le_add_left ?_)
    rw [hashError_eq]
    have hcard : (Fintype.card (Digest F) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
    calc (1 : ℝ≥0∞) ≤ ((c * n : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ := by
          rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hcard)
            (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
          exact_mod_cast hbig
      _ ≤ _ := le_mul_of_one_le_left (by positivity)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0.ne')
  have hsmall : c * n < Fintype.card (Digest F) := by omega
  have hloss : ∀ loss, Pr{let result ← Iop.Batch.run S publicValues prover}[E result] ≤
      n * roundBoundB S δ δ' loss + hashError F S.params.capHeight n := by
    intro loss
    rw [run_eqB]
    refine (prEvent_exists_fresh_bad_le (gameB S publicValues prover) n
      (isTotalQueryBound_gameB S publicValues prover Q hQ) E
      (fun pre t u ↦ Clash (boundDigestsB S (initAnswers pre)) pre t u ∨
        RoundBadB S publicValues δ δ' loss pre t u)
      (((c * n : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ + roundBoundB S δ δ' loss)
      (fun pre t hlen _ ↦ (prEvent_or_le _ _ _).trans
        (add_le_add (prob_clash_le (boundDigestsB S (initAnswers pre)) _ Nat.one_le_two_pow
          (fun c i ↦ (length_boundDigestsB S _ c i).le) _ n pre hlen t)
          (prob_roundBadB_le S publicValues δ δ' loss pre t)))
      fun answer hev ↦ ?_).trans ?_
    · replace hev := hE answer hev
      rw [evalWithAnswerFn_gameB] at hev
      obtain ⟨hok, -, hfail⟩ := hev
      dsimp only at hok hfail
      have hlog := tableQueryLog_gameB S publicValues answer prover
      have hlen := length_tableQueryLog_le answer _ n
        (isTotalQueryBound_gameB S publicValues prover Q hQ)
      rw [hlog] at hlen
      set proof := evalWithAnswerFn (QueryImpl.ofFn answer) prover
      obtain ⟨p, hp, hfresh, hbad⟩ := exists_badAtB S publicValues δ δ' loss hδ' answer _
        proof (tableQueryLog (setupAndProveB S prover) answer) (consistent_tableQueryLog _) rfl
        (fun e he ↦ by
          rw [tableQueryLog_setupAndProveB]; exact List.mem_append_left _ he)
        hok (lt_of_le_of_lt (Nat.mul_le_mul_left _ hlen) hsmall) hfail
      rw [hlog]
      exact ⟨_, _, _, (List.take_append_drop p _).symm.trans
        (by rw [List.drop_eq_getElem_cons hp]), hfresh, hbad⟩
    · rw [mul_add, add_comm, hashError_eq]
  calc _ ≤ ⨅ loss, (n * roundBoundB S δ δ' loss + hashError F S.params.capHeight n) :=
        le_iInf hloss
    _ = n * Iop.Batch.roundError S δ δ' + hashError F S.params.capHeight n := by
      rw [roundError_eqB, ENNReal.mul_iInf_of_ne (by exact_mod_cast hn0.ne')
        (ENNReal.natCast_ne_top _), ENNReal.iInf_add]
    _ = _ := by simp only [n, Nat.cast_add]

/-- **Knowledge soundness of the batch STARK in the random-oracle model**, with the event spelled
out. -/
theorem prob_unopenedB_le (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat)
    (prover : Iop.Batch.NIProver S) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let result ← Iop.Batch.run S publicValues prover}[UnopenedB S publicValues δ' result] ≤
      (Q + S.verifierQueries) * Iop.Batch.roundError S δ δ' +
        hashError F S.params.capHeight (Q + S.verifierQueries) :=
  prob_le_of_unopenedB S publicValues δ δ' hδ' Q prover hQ _ fun _ h ↦ h

/-- An accepting batch verifier checked the multiplicity bound. -/
theorem heightBounded_of_ok (answer : (q : Query F) → Answer S.streamLen q)
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (hok : CompStark.Batch.verifyBatchWith (idealOf answer) S.params S.instances common proof
      (List.ofFn publicValues) = .ok ()) : S.HeightBounded := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlk, -⟩ :=
    verifyBatchWith_ok (idealOf answer) S.params S.instances common proof _ hok
  simp only [CompStark.Batch.lookupShapeOk, Bool.and_eq_true] at hlk
  have h := hlk.1.1.1.1.2
  rwa [Iop.Batch.Setup.instances, List.map_ofFn] at h

/-- The event of knowledge soundness with lookup inclusion: an accepted proof for the instances'
trace lengths, no tuple of traces close to the committed ones satisfying the batch with lookup
inclusion. -/
def UnopenedInclusionB
    (result : CompStark.Batch.BatchProof F EF × QueryLog (spec F S.streamLen) ×
      Except String Unit) : Prop :=
  result.2.2 = .ok () ∧ result.1.degreeBits.toList = List.ofFn S.logN ∧
    ∀ traces ∈ Iop.Batch.closeTraces S δ' (Iop.Batch.committedTraces S result.2.1 result.1),
      ¬ S.SatisfiedWithInclusion traces publicValues

/-- **Knowledge soundness of the batch STARK in the random-oracle model, with lookup inclusion**,
with the event spelled out: an accepting verifier checked the multiplicity bound, so with AIRs
bounding their queries' multiplicities, traces satisfying the batch satisfy it with lookup
inclusion. -/
theorem prob_unopenedInclusionB_le (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat)
    (prover : Iop.Batch.NIProver S) (hQ : prover.IsTotalQueryBound Q)
    (hcounts : ∀ i, (S.air i).CountsBounded (S.logN i)) :
    Pr{let result ← Iop.Batch.run S publicValues prover}[
      UnopenedInclusionB S publicValues δ' result] ≤
      (Q + S.verifierQueries) * Iop.Batch.roundError S δ δ' +
        hashError F S.params.capHeight (Q + S.verifierQueries) := by
  refine prob_le_of_unopenedB S publicValues δ δ' hδ' Q prover hQ _ fun answer h ↦ ?_
  obtain ⟨hok, hdb, hfail⟩ := h
  refine ⟨hok, hdb, fun traces ht hsat ↦ hfail traces ht ?_⟩
  rw [evalWithAnswerFn_gameB] at hok
  exact Sound.Batch.satisfiedWithInclusion_of_satisfied S traces publicValues
    (heightBounded_of_ok S publicValues answer _ _ hok) hcounts hsat

end Bound

end CompStark.Ni
