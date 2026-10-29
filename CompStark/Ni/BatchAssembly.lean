/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchBadQuery
public import CompStark.Ni.BatchLengths
public import CompStark.Ni.Assembly
public import CompStark.Sound.Inclusion

/-! # Knowledge soundness of the batch STARK in the random-oracle model, assembled

As for the STARK (`Ni/Assembly.lean`): the game of `Statement.run` (`gameB`) makes at most
`Q + verifierQueries` oracle calls, the setup's, the prover's and the verifier's. A fresh answer
is bad if its digest clashes (`prob_clash_le`: `(2 ^ (h + 1) + 2) q / |F|^8` for caps of height
`h`, a duplex call's input binding two windows of `2 ^ h` digests, at every vector of lengths
`Statement.boundDigests`) or it makes its batch round bad at some admitted vector of lengths
(`prob_roundBadCB_le`: the largest round bound over the admitted vectors, as the call's first
round fixes the vector, `eq_of_seedB_prefix`), and an accepted proof the extractor cannot open
forces such a query (`exists_badAtB` at the proof's lengths, which are admitted,
`Statement.admits_of_ok`). The bound holds at every choice of proximity losses, so at the
infimum: `q · roundError + hashError F (h + 1) q`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Sound CompStark.Iop CompStark.RandomOracle
open OracleSpec OracleComp
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-! ### The game -/

section Game
variable (C : Iop.Batch.Statement F) (publicValues : Fin C.k → List F)

/-- The batch setup, then the prover. -/
def setupAndProveB (prover : C.NIProver EF) :
    OracleComp (spec F (C.streamLen EF))
      (CompStark.Batch.Common F × CompStark.Batch.BatchProof F EF) := do
  let common ← C.setupRo EF
  return (common, ← prover)

/-- The game of `Statement.run`: the setup and the prover, logged, then the verifier on the proof
against the setup's common data. -/
def gameB (prover : C.NIProver EF) :
    OracleComp (spec F (C.streamLen EF))
      (CompStark.Batch.BatchProof F EF × QueryLog (spec F (C.streamLen EF)) ×
        Except String Unit) := do
  let ((common, proof), log) ← (simulateQ loggingOracle (setupAndProveB C prover)).run
  return (proof, log, ← CompStark.Batch.verifyBatchWith (ideal F (C.streamLen EF)) C.params
    C.airs common proof (List.ofFn publicValues))

theorem run_eqB (prover : C.NIProver EF) :
    C.run publicValues prover = (simulateQ randomOracle (gameB C publicValues prover)).run' ∅ :=
  rfl

/-- The common data the setup computes has the statement's lookups. -/
theorem lookups_of_mem_support_setupRo (common : CompStark.Batch.Common F)
    (h : common ∈ support (C.setupRo EF)) : common.lookups = List.ofFn C.lookups := by
  unfold Iop.Batch.Statement.setupRo CompStark.Batch.commonWith at h
  rw [mem_support_bind_iff] at h
  obtain ⟨c, -, hc⟩ := h
  rw [support_pure, Set.mem_singleton_iff] at hc
  rw [hc]
  show C.keyInstances.map (·.lookups) = _
  rw [Iop.Batch.Statement.keyInstances, Iop.Batch.Statement.instancesAt, List.map_ofFn]
  rfl

theorem isTotalQueryBound_gameB (prover : C.NIProver EF) (Q : Nat)
    (hQ : prover.IsTotalQueryBound Q) :
    (gameB C publicValues prover).IsTotalQueryBound (Q + C.verifierQueries EF) := by
  have hsp : (setupAndProveB C prover).IsTotalQueryBound (C.setupQueries + Q) :=
    isTotalQueryBound_bind (C.isTotalQueryBound_setupRo (EF := EF)) fun common ↦
      (isTotalQueryBound_bind (n₂ := 0) hQ fun proof ↦
        (show IsTotalQueryBound (pure (common, proof) : OracleComp (spec F (C.streamLen EF)) _) 0
          from trivial)).mono (by omega)
  refine (isTotalQueryBound_bind_of_mem_support (suffixBound := C.verifierCalls EF)
    ((isTotalQueryBound_run_simulateQ_loggingOracle_iff _ _).mpr hsp) fun x hx ↦ ?_).mono
    (by unfold Iop.Batch.Statement.verifierQueries; omega)
  obtain ⟨⟨common, proof⟩, log⟩ := x
  have hmem : (common, proof) ∈ support (setupAndProveB C prover) := by
    rw [← loggingOracle.support_fst_map_run_simulateQ, support_map]
    exact ⟨_, hx, rfl⟩
  have hl : common.lookups = List.ofFn C.lookups := by
    unfold setupAndProveB at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨c, hc, hmem⟩ := hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨p, -, hmem⟩ := hmem
    rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rw [hmem.1]
    exact lookups_of_mem_support_setupRo C c hc
  exact (isTotalQueryBound_bind (n₂ := 0)
    (C.isTotalQueryBound_verifyBatchWith common hl proof (List.ofFn publicValues))
    fun v ↦ (show IsTotalQueryBound (pure (proof, log, v) :
      OracleComp (spec F (C.streamLen EF)) _) 0 from trivial)).mono (by omega)

variable (answer : (q : Query F) → Answer (C.streamLen EF) q) (prover : C.NIProver EF)

theorem evalWithAnswerFn_setupAndProveB :
    evalWithAnswerFn (QueryImpl.ofFn answer) (setupAndProveB C prover) =
      (CompStark.Batch.commonWith (idealOf answer) C.params C.keyInstances,
        evalWithAnswerFn (QueryImpl.ofFn answer) prover) := by
  simp only [setupAndProveB, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    Iop.Batch.Statement.setupRo, evalWithAnswerFn_commonWith]

theorem tableQueryLog_setupAndProveB :
    tableQueryLog (setupAndProveB C prover) answer =
      tableQueryLog (C.setupRo EF) answer ++ tableQueryLog prover answer := by
  simp only [setupAndProveB]
  rw [tableQueryLog_bind, tableQueryLog_bind]
  simp only [tableQueryLog_pure, List.append_nil]

theorem evalWithAnswerFn_gameB :
    evalWithAnswerFn (QueryImpl.ofFn answer) (gameB C publicValues prover) =
      (evalWithAnswerFn (QueryImpl.ofFn answer) prover,
        tableQueryLog (setupAndProveB C prover) answer,
        CompStark.Batch.verifyBatchWith (idealOf answer) C.params C.airs
          (CompStark.Batch.commonWith (idealOf answer) C.params C.keyInstances)
          (evalWithAnswerFn (QueryImpl.ofFn answer) prover) (List.ofFn publicValues)) := by
  simp only [gameB, evalWithAnswerFn_bind, evalWithAnswerFn_logged, evalWithAnswerFn_pure,
    evalWithAnswerFn_setupAndProveB, evalWithAnswerFn_verifyBatchWith]

theorem tableQueryLog_gameB :
    tableQueryLog (gameB C publicValues prover) answer =
      tableQueryLog (setupAndProveB C prover) answer ++
      tableQueryLog (CompStark.Batch.verifyBatchWith (ideal F (C.streamLen EF)) C.params C.airs
        (CompStark.Batch.commonWith (idealOf answer) C.params C.keyInstances)
        (evalWithAnswerFn (QueryImpl.ofFn answer) prover) (List.ofFn publicValues)) answer := by
  simp only [gameB]
  rw [tableQueryLog_bind, evalWithAnswerFn_logged, tableQueryLog_logged, tableQueryLog_bind,
    tableQueryLog_pure, List.append_nil, evalWithAnswerFn_setupAndProveB]

end Game

/-! ### The verifier at the proof's lengths -/

/-- On a proof whose degree bits the common data accepts, of admitted lengths, against common data
of the statement's lookups, the batch verifier checks the instances of the setup at those
lengths. -/
theorem verifyBatchWith_eq_setupAt (C : Iop.Batch.Statement F) {m : Type → Type} [Monad m]
    (H : Primitives F m) (common : CompStark.Batch.Common F)
    (hl : common.lookups = List.ofFn C.lookups) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F))
    (hkey : CompStark.Batch.keyOk C.airs common proof.degreeBits.toList = true)
    (h : C.Admits (C.lengthsOf proof)) :
    CompStark.Batch.verifyBatchWith H C.params C.airs common proof pis =
      CompStark.Batch.verifyInstancesWith H (C.setupAt EF _ h).params
        (C.setupAt EF _ h).instances common proof pis := by
  rw [CompStark.Batch.verifyBatchWith_of_keyOk _ _ _ _ _ _ hkey,
    C.instancesOf_eq common hl proof (C.length_degreeBits_of_keyOk common proof hkey)]
  rfl

/-! ### The bound -/

section Bound
variable (C : Iop.Batch.Statement F) (publicValues : Fin C.k → List F)
  (δ δ' : (Fin C.k → ℕ) → NNReal)

/-- The event of knowledge soundness: an accepted proof, no tuple of traces of its lengths close
to the committed ones satisfying the batch at those lengths. -/
def UnopenedB
    (result : CompStark.Batch.BatchProof F EF × QueryLog (spec F (C.streamLen EF)) ×
      Except String Unit) : Prop :=
  result.2.2 = .ok () ∧
    ∀ h : C.Admits (C.lengthsOf result.1),
      ∀ traces ∈ Iop.Batch.closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf result.1))
          (Iop.Batch.committedTraces (C.setupAt EF _ h) result.2.1 result.1),
        ¬ (C.setupAt EF _ h).Satisfied traces publicValues

variable (EF) in
/-- The largest batch round bound over the admitted vectors of lengths at proximity losses
`loss n`. -/
noncomputable def roundBoundCB (loss : (Fin C.k → ℕ) → NNReal) : ENNReal :=
  ⨆ (m : Fin C.k → ℕ) (h : C.Admits m), roundBoundB (C.setupAt EF m h) (δ m) (δ' m) (loss m)

theorem le_roundBoundCB (loss : (Fin C.k → ℕ) → NNReal) (m : Fin C.k → ℕ) (h : C.Admits m) :
    roundBoundB (C.setupAt EF m h) (δ m) (δ' m) (loss m) ≤ roundBoundCB EF C δ δ' loss :=
  le_iSup_of_le m (le_iSup (fun h ↦ roundBoundB (C.setupAt EF m h) (δ m) (δ' m) (loss m)) h)

theorem le_roundErrorCB (m : Fin C.k → ℕ) (h : C.Admits m) :
    Iop.Batch.roundError (C.setupAt EF m h) (δ m) (δ' m) ≤ C.roundError EF δ δ' :=
  le_iSup_of_le m (le_iSup (fun h ↦ Iop.Batch.roundError (C.setupAt EF m h) (δ m) (δ' m)) h)

/-- A duplex call is bad at some admitted vector of lengths. -/
def RoundBadCB (loss : (Fin C.k → ℕ) → NNReal) (pre : QueryLog (spec F (C.streamLen EF)))
    (t : Query F) (u : Answer (C.streamLen EF) t) : Prop :=
  ∃ (m : Fin C.k → ℕ) (h : C.Admits m),
    RoundBadB (C.setupAt EF m h) publicValues (δ m) (δ' m) (loss m) pre t u

/-- **A fresh answer is bad at one vector of lengths.** A uniform answer is round-bad at some
admitted vector with probability at most the largest round bound: the call's first round observes
the degree bits of at most one admitted vector (`eq_of_seedB_prefix`). -/
theorem prob_roundBadCB_le (loss : (Fin C.k → ℕ) → NNReal)
    (pre : QueryLog (spec F (C.streamLen EF))) (t : Query F) :
    Pr{let u ← $ᵗ (Answer (C.streamLen EF) t)}[
      RoundBadCB C publicValues δ δ' loss pre t u] ≤ roundBoundCB EF C δ δ' loss := by
  by_cases hex : ∃ (m : Fin C.k → ℕ) (h : C.Admits m),
      seedB (C.setupAt EF m h) <+: firstBlock pre t
  · obtain ⟨m, h, hpre⟩ := hex
    have key : ∀ u, RoundBadCB C publicValues δ δ' loss pre t u →
        RoundBadB (C.setupAt EF m h) publicValues (δ m) (δ' m) (loss m) pre t u := by
      rintro u ⟨m', h', hb⟩
      have hp' := prefix_firstBlockB (C.setupAt EF m' h') publicValues _ _ _ pre t u hb
      have hm : m' = m := C.eq_of_seedB_prefix h' h _ hp' hpre
      subst hm
      exact hb
    exact (prEvent_mono _ _ _ key).trans ((prob_roundBadB_le (C.setupAt EF m h) publicValues
      (δ m) (δ' m) (loss m) pre t).trans (le_roundBoundCB C δ δ' loss m h))
  · refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (?_ : _ ↔ False)) (by
      simp only [prEvent_false, zero_le])
    refine ⟨fun ⟨m, h, hb⟩ ↦ hex ⟨m, h,
      prefix_firstBlockB (C.setupAt EF m h) publicValues _ _ _ pre t u hb⟩, False.elim⟩

/-- The infimum over the losses of the largest round bound at the chosen losses is at most the
largest round error. -/
theorem le_roundError_of_forallB (n : Nat) (hn : n ≠ 0) (H P : ℝ≥0∞)
    (hall : ∀ loss : (Fin C.k → ℕ) → NNReal, P ≤ n * roundBoundCB EF C δ δ' loss + H) :
    P ≤ n * C.roundError EF δ δ' + H := by
  classical
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have hR : C.roundError EF δ δ' < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.mul_top hn', top_add] at hlt
    exact lt_irrefl _ hlt
  set ε₁ : ℝ≥0∞ := (ε : ℝ≥0∞) / n
  have hε₁ : ε₁ ≠ 0 := by
    simp only [ε₁, ne_eq, ENNReal.div_eq_zero_iff, ENNReal.coe_eq_zero, ENNReal.natCast_ne_top,
      or_false]
    exact hε.ne'
  have hex : ∀ m (h : C.Admits m), ∃ l,
      roundBoundB (C.setupAt EF m h) (δ m) (δ' m) l <
        Iop.Batch.roundError (C.setupAt EF m h) (δ m) (δ' m) + ε₁ := fun m h ↦ by
    have hfin := lt_of_le_of_lt (le_roundErrorCB C δ δ' m h) hR
    rw [roundError_eqB] at hfin ⊢
    exact iInf_lt_iff.mp (ENNReal.lt_add_right hfin.ne hε₁)
  let loss : (Fin C.k → ℕ) → NNReal := fun m ↦ if hm : C.Admits m then (hex m hm).choose else 0
  have hloss : roundBoundCB EF C δ δ' loss ≤ C.roundError EF δ δ' + ε₁ := by
    refine iSup_le fun m ↦ iSup_le fun h ↦ ?_
    have hl : loss m = (hex m h).choose := by simp only [loss, h, ↓reduceDIte]
    rw [hl]
    exact (hex m h).choose_spec.le.trans (add_le_add (le_roundErrorCB C δ δ' m h) le_rfl)
  calc P ≤ n * roundBoundCB EF C δ δ' loss + H := hall loss
    _ ≤ n * (C.roundError EF δ δ' + ε₁) + H := by gcongr
    _ = n * C.roundError EF δ δ' + H + ε := by
        rw [mul_add, ENNReal.mul_div_cancel hn' (ENNReal.natCast_ne_top n)]
        ring

/-- **Knowledge soundness of the batch STARK in the random-oracle model**, for any event that,
on every answer table, implies `UnopenedB`. -/
theorem prob_le_of_unopenedB (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat)
    (prover : C.NIProver EF) (hQ : prover.IsTotalQueryBound Q)
    (E : CompStark.Batch.BatchProof F EF × QueryLog (spec F (C.streamLen EF)) ×
      Except String Unit → Prop)
    (hE : ∀ answer, E (evalWithAnswerFn (QueryImpl.ofFn answer) (gameB C publicValues prover)) →
      UnopenedB C publicValues δ' (evalWithAnswerFn (QueryImpl.ofFn answer)
        (gameB C publicValues prover))) :
    Pr{let result ← C.run publicValues prover}[E result] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) := by
  set N := Q + C.verifierQueries EF
  set c := 2 ^ (C.params.capHeight + 1) + 2
  have hn0 : 0 < N := by
    have h3 : 3 ≤ CompStark.Batch.verifierCallsOf EF C.params (C.instancesAt fun _ ↦ 0) := by
      unfold CompStark.Batch.verifierCallsOf; dsimp only; omega
    have h4 := le_foldr_max _ _ (List.mem_map_of_mem (f := fun n ↦
      CompStark.Batch.verifierCallsOf EF C.params (C.instancesAt n))
      (Iop.Batch.mem_lengthVectors C.k (twoAdicity F) (fun _ ↦ 0) fun _ ↦ Nat.zero_le _))
    have : 0 < C.verifierCalls EF := lt_of_lt_of_le (by omega) (h3.trans h4)
    unfold N Iop.Batch.Statement.verifierQueries
    omega
  by_cases hbig : Fintype.card (Digest F) ≤ c * N
  · refine (prEvent_le_one _).trans (le_add_left ?_)
    rw [hashError_eq]
    have hcard : (Fintype.card (Digest F) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
    calc (1 : ℝ≥0∞) ≤ ((c * N : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ := by
          rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hcard)
            (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
          exact_mod_cast hbig
      _ ≤ _ := le_mul_of_one_le_left (by positivity)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0.ne')
  have hsmall : c * N < Fintype.card (Digest F) := by omega
  set bd := C.boundDigests EF
  rw [show ((Q : ℝ≥0∞) + (C.verifierQueries EF : ℕ)) = (N : ℝ≥0∞) by simp only [N, Nat.cast_add]]
  refine le_roundError_of_forallB (EF := EF) C δ δ' N hn0.ne' _ _ fun loss ↦ ?_
  rw [run_eqB]
  refine (prEvent_exists_fresh_bad_le (gameB C publicValues prover) N
    (isTotalQueryBound_gameB C publicValues prover Q hQ) E
    (fun pre t u ↦ Clash bd pre t u ∨ RoundBadCB C publicValues δ δ' loss pre t u)
    (((c * N : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ +
      roundBoundCB EF C δ δ' loss)
    (fun pre t hlen _ ↦ (prEvent_or_le _ _ _).trans
      (add_le_add (prob_clash_le bd _ Nat.one_le_two_pow
        (fun c i ↦ length_boundDigestsOf_le _ _ c i) _ N pre hlen t)
        (prob_roundBadCB_le C publicValues δ δ' loss pre t)))
    fun answer hev ↦ ?_).trans ?_
  · replace hev := hE answer hev
    rw [evalWithAnswerFn_gameB] at hev
    obtain ⟨hok, hfail⟩ := hev
    dsimp only at hok hfail
    set proof := evalWithAnswerFn (QueryImpl.ofFn answer) prover
    have h := C.admits_of_ok answer proof _ hok
    set n := C.lengthsOf proof
    set S := C.setupAt EF n h
    obtain ⟨-, hl⟩ := C.commonWith_keyInstances (idealOf answer)
    have hkey := keyOk_of_ok _ _ _ _ _ _ hok
    have hlog := tableQueryLog_gameB C publicValues answer prover
    have hlen := length_tableQueryLog_le answer _ N
      (isTotalQueryBound_gameB C publicValues prover Q hQ)
    rw [hlog] at hlen
    rw [verifyBatchWith_eq_setupAt C _ _ hl _ _ hkey h] at hok hlog hlen
    have hsetup : ∀ e ∈ tableQueryLog S.setupRo answer,
        e ∈ tableQueryLog (setupAndProveB C prover) answer := fun e he ↦ by
      rw [tableQueryLog_setupAndProveB]
      exact List.mem_append_left _ he
    set L : QueryLog (spec F S.streamLen) :=
      (tableQueryLog (setupAndProveB C prover) answer : QueryLog (spec F S.streamLen)) ++
      tableQueryLog (CompStark.Batch.verifyInstancesWith (ideal F S.streamLen) S.params S.instances
        (CompStark.Batch.commonWith (idealOf answer) S.params S.keyInstances) proof
        (List.ofFn publicValues)) answer
    have hL : tableQueryLog (gameB C publicValues prover) answer = L := hlog
    obtain ⟨p, hp, hfresh, hbad⟩ : ∃ p hp, BadAtB S publicValues (δ n) (δ' n) (loss n) L p hp :=
      exists_badAtB S publicValues (δ n) (δ' n) (loss n) (hδ' n h) answer _ proof
        (tableQueryLog (setupAndProveB C prover) answer) (consistent_tableQueryLog _) rfl hsetup
        hok (lt_of_le_of_lt (Nat.mul_le_mul_left _ hlen) hsmall) (hfail h)
    rw [hL]
    refine ⟨_, _, _, (List.take_append_drop p L).symm.trans
      (by rw [List.drop_eq_getElem_cons hp]; rfl), hfresh, ?_⟩
    rcases hbad with hc | hr
    · left
      rw [C.boundDigestsB_setupAt n h] at hc
      exact hc
    · exact Or.inr ⟨n, h, hr⟩
  · rw [mul_add, add_comm, hashError_eq]

/-- **Knowledge soundness of the batch STARK in the random-oracle model**, with the event spelled
out. -/
theorem prob_unopenedB_le (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat)
    (prover : C.NIProver EF) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let result ← C.run publicValues prover}[UnopenedB C publicValues δ' result] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) :=
  prob_le_of_unopenedB C publicValues δ δ' hδ' Q prover hQ _ fun _ h ↦ h

/-- The event of knowledge soundness with lookup inclusion: an accepted proof, no tuple of traces
of its lengths close to the committed ones satisfying the batch at those lengths with lookup
inclusion. -/
def UnopenedInclusionB
    (result : CompStark.Batch.BatchProof F EF × QueryLog (spec F (C.streamLen EF)) ×
      Except String Unit) : Prop :=
  result.2.2 = .ok () ∧
    ∀ h : C.Admits (C.lengthsOf result.1),
      ∀ traces ∈ Iop.Batch.closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf result.1))
          (Iop.Batch.committedTraces (C.setupAt EF _ h) result.2.1 result.1),
        ¬ (C.setupAt EF _ h).SatisfiedWithInclusion traces publicValues

/-- **Knowledge soundness of the batch STARK in the random-oracle model, with lookup inclusion**,
with the event spelled out: admitted lengths pass the multiplicity bound, so with AIRs
bounding their queries' multiplicities at every admitted vector of lengths, traces satisfying the
batch satisfy it with lookup inclusion. -/
theorem prob_unopenedInclusionB_le (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat)
    (prover : C.NIProver EF) (hQ : prover.IsTotalQueryBound Q)
    (hcounts : ∀ n, C.Admits n → ∀ i, (C.air i).CountsBounded (n i)) :
    Pr{let result ← C.run publicValues prover}[
      UnopenedInclusionB C publicValues δ' result] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) := by
  refine prob_le_of_unopenedB C publicValues δ δ' hδ' Q prover hQ _ fun answer h ↦ ?_
  rw [evalWithAnswerFn_gameB] at h ⊢
  obtain ⟨hok, hfail⟩ := h
  refine ⟨hok, fun hn traces ht hsat ↦ hfail hn traces ht ?_⟩
  exact Sound.Batch.satisfiedWithInclusion_of_satisfied _ traces publicValues
    (C.heightBounded_setupAt _ hn) (hcounts _ hn) hsat

end Bound

end CompStark.Ni
