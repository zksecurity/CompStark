/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Zero

/-! # Knowledge soundness in the random-oracle model, assembled

The game of `run` (`game`) makes at most `Q + verifierQueries` oracle calls: the setup's, the
prover's and the verifier's. B's
`prEvent_exists_fresh_bad_le` bounds the probability of an event that forces a fresh bad query by
the number of calls times the probability that one fresh answer is bad. Here a fresh answer is bad
if its digest clashes (`prob_clash_le`: `(2 ^ h + 2) q / |F|^8` for caps of height `h`) or it
makes its round bad (`prob_roundBad_le`: the largest round error at the proximity loss), and the
event, an accepted proof the extractor cannot open, forces such a query (`exists_badAt`). The
bound holds at every loss, so at the infimum: `q · roundError + hashError F h q`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Sound CompStark.Iop CompStark.RandomOracle
open OracleSpec OracleComp
open scoped ENNReal

variable {F : Type}

/-! ### Logged computations on an answer table -/

section Logged
variable {K : Nat} (answer : (q : Query F) → Answer K q)

theorem tableQueryLog_map {α β : Type} (f : α → β) (oa : OracleComp (spec F K) α) :
    tableQueryLog (f <$> oa) answer = tableQueryLog oa answer := by
  rw [map_eq_bind_pure_comp, tableQueryLog_bind, Function.comp_apply, tableQueryLog_pure,
    List.append_nil]

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

theorem tableQueryLog_logged {α : Type} (oa : OracleComp (spec F K) α) :
    tableQueryLog (simulateQ loggingOracle oa).run answer = tableQueryLog oa answer := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [run_simulateQ_loggingOracle_query_bind, tableQueryLog_query_bind, tableQueryLog_map,
      ih, tableQueryLog_query_bind]

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

variable [BaseField F] {EF : Type} [Challenge F EF]

/-! ### The game -/

section Game
variable (C : Statement F) (publicValues : List F)

/-- The setup, then the prover. -/
def setupAndProve (prover : C.NIProver EF) :
    OracleComp (spec F (C.streamLen EF)) (Option (PreprocessedKey F) × Proof F EF) := do
  let vk ← C.setupRo EF
  return (vk, ← prover)

/-- The game of `Statement.run`: the setup and the prover, logged, then the verifier on the proof
against the setup's key. -/
def game (prover : C.NIProver EF) :
    OracleComp (spec F (C.streamLen EF))
        (Proof F EF × QueryLog (spec F (C.streamLen EF)) × Except String Unit) := do
  let ((vk, proof), log) ← (simulateQ loggingOracle (setupAndProve C prover)).run
  return (proof, log,
    ← verifyWith (ideal F (C.streamLen EF)) C.params C.air vk proof publicValues)

theorem run_eq (prover : C.NIProver EF) :
    C.run publicValues prover = (simulateQ randomOracle (game C publicValues prover)).run' ∅ :=
  rfl

theorem le_foldr_max : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr max 0
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: l, x, .tail _ h => (le_foldr_max l x h).trans (le_max_right _ _)

/-- **The verifier's oracle calls on any proof.** -/
theorem isTotalQueryBound_verifyWith_max (vk : Option (PreprocessedKey F)) (proof : Proof F EF) :
    IsTotalQueryBound (verifyWith (ideal F (C.streamLen EF)) C.params C.air vk proof
      publicValues) (C.verifierCallsMax EF) := by
  by_cases hdb : proof.degreeBits ≤ twoAdicity F
  · exact (Iop.Setup.isTotalQueryBound_verifyWith C.params C.air vk proof publicValues).mono
      (le_foldr_max _ _ (List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.lt_succ_of_le hdb), rfl⟩))
  · refine (show IsTotalQueryBound (verifyWith (ideal F (C.streamLen EF)) C.params C.air vk proof
        publicValues) 0 from ?_).mono (Nat.zero_le _)
    unfold verifyWith
    dsimp only
    rw [ite_eq_right (by omega)]
    trivial

theorem isTotalQueryBound_game (prover : C.NIProver EF) (Q : Nat)
    (hQ : prover.IsTotalQueryBound Q) :
    (game C publicValues prover).IsTotalQueryBound (Q + C.verifierQueries EF) := by
  have hsp : (setupAndProve C prover).IsTotalQueryBound (C.setupQueries + Q) :=
    isTotalQueryBound_bind (Iop.Setup.isTotalQueryBound_preprocessedKeyWith C.params C.air
      C.preprocessedLogN (C.streamLen EF)) fun vk ↦
      (isTotalQueryBound_bind (n₂ := 0) hQ fun proof ↦
        (show IsTotalQueryBound (pure (vk, proof) : OracleComp (spec F (C.streamLen EF)) _) 0
          from trivial)).mono (by omega)
  refine (isTotalQueryBound_bind (n₂ := C.verifierCallsMax EF)
    ((isTotalQueryBound_run_simulateQ_loggingOracle_iff _ _).mpr hsp) fun x ↦ ?_).mono
    (by unfold Statement.verifierQueries; omega)
  obtain ⟨⟨vk, proof⟩, log⟩ := x
  exact (isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_verifyWith_max C publicValues vk proof)
    fun v ↦ (show IsTotalQueryBound (pure (proof, log, v) :
      OracleComp (spec F (C.streamLen EF)) _) 0 from trivial)).mono (by omega)

variable (answer : (q : Query F) → Answer (C.streamLen EF) q) (prover : C.NIProver EF)

theorem evalWithAnswerFn_setupAndProve :
    evalWithAnswerFn (QueryImpl.ofFn answer) (setupAndProve C prover) =
      (preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN,
        evalWithAnswerFn (QueryImpl.ofFn answer) prover) := by
  simp only [setupAndProve, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Statement.setupRo]
  exact Prod.ext (simulateQ_preprocessedKeyWith (QueryImpl.ofFn answer) _ _ _) rfl

theorem tableQueryLog_setupAndProve :
    tableQueryLog (setupAndProve C prover) answer =
      tableQueryLog (C.setupRo EF) answer ++ tableQueryLog prover answer := by
  simp only [setupAndProve]
  rw [tableQueryLog_bind, tableQueryLog_bind]
  simp only [tableQueryLog_pure, List.append_nil]

theorem evalWithAnswerFn_game :
    evalWithAnswerFn (QueryImpl.ofFn answer) (game C publicValues prover) =
      (evalWithAnswerFn (QueryImpl.ofFn answer) prover,
        tableQueryLog (setupAndProve C prover) answer,
        verifyWith (idealOf answer) C.params C.air
          (preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN)
          (evalWithAnswerFn (QueryImpl.ofFn answer) prover) publicValues) := by
  simp only [game, evalWithAnswerFn_bind, evalWithAnswerFn_logged, evalWithAnswerFn_pure,
    evalWithAnswerFn_setupAndProve, evalWithAnswerFn_verifyWith]

theorem tableQueryLog_game :
    tableQueryLog (game C publicValues prover) answer =
      tableQueryLog (setupAndProve C prover) answer ++
      tableQueryLog (verifyWith (ideal F (C.streamLen EF)) C.params C.air
        (preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN)
        (evalWithAnswerFn (QueryImpl.ofFn answer) prover) publicValues) answer := by
  simp only [game]
  rw [tableQueryLog_bind, evalWithAnswerFn_logged, tableQueryLog_logged, tableQueryLog_bind,
    tableQueryLog_pure, List.append_nil, evalWithAnswerFn_setupAndProve]

end Game

/-! ### The bound -/

section Bound
variable (C : Statement F) (publicValues : List F) (δ δ' : ℕ → NNReal)

/-- The event of knowledge soundness: an accepted proof, no trace of its length close to the
committed one satisfying the AIR at that length. -/
def Unopened (result : Proof F EF × QueryLog (spec F (C.streamLen EF)) × Except String Unit) :
    Prop :=
  result.2.2 = .ok () ∧
    ∀ h : C.Admits result.1.degreeBits,
      ∀ trace ∈ closeTraces (C.setupAt EF _ h) (δ' result.1.degreeBits)
          (committedTrace (C.setupAt EF _ h) result.2.1 result.1),
        ¬ C.air.Satisfied result.1.degreeBits trace publicValues

theorem hashError_eq (h q : Nat) :
    hashError F h q =
      q * ((((2 ^ h + 2) * q : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹) := by
  rw [hashError, card_digest, Nat.cast_pow, div_eq_mul_inv]
  push_cast
  ring

/-- A duplex call's bad event at the setup's length: the folding rounds' where FRI folds, the
rounds without folds otherwise. -/
def RoundBadL (S : Iop.Setup EF) (δ δ' loss : NNReal) (pre : QueryLog (spec F S.streamLen))
    (t : Query F) (u : Answer S.streamLen t) : Prop :=
  if hf : S.params.logFinalPolyLen < S.logN then
    haveI : S.Folds := ⟨hf⟩
    RoundBad S publicValues δ δ' loss pre t u
  else RoundBad0 S publicValues δ δ' pre t u

/-- The bound on one fresh answer at the setup's length, at proximity loss `loss`. -/
noncomputable def roundBoundL (S : Iop.Setup EF) (δ δ' loss : NNReal) : ENNReal :=
  if hf : S.params.logFinalPolyLen < S.logN then
    haveI : S.Folds := ⟨hf⟩
    roundBound S δ δ' loss
  else roundError0 S δ δ'

theorem prob_roundBadL_le (S : Iop.Setup EF) (δ δ' loss : NNReal)
    (pre : QueryLog (spec F S.streamLen)) (t : Query F) :
    Pr{let u ← $ᵗ (Answer S.streamLen t)}[RoundBadL publicValues S δ δ' loss pre t u] ≤
      roundBoundL S δ δ' loss := by
  unfold RoundBadL roundBoundL
  split
  · rename_i hf
    have : S.Folds := ⟨hf⟩
    exact prob_roundBad_le S publicValues δ δ' loss pre t
  · exact prob_roundBad0_le S publicValues δ δ' pre t

theorem prefix_firstBlockL (S : Iop.Setup EF) (δ δ' loss : NNReal)
    (pre : QueryLog (spec F S.streamLen)) (t : Query F) (u : Answer S.streamLen t)
    (h : RoundBadL publicValues S δ δ' loss pre t u) : starkSeedS S <+: firstBlock pre t := by
  unfold RoundBadL at h
  split at h
  · rename_i hf
    have : S.Folds := ⟨hf⟩
    exact prefix_firstBlock S publicValues δ δ' loss pre t u h
  · exact prefix_firstBlock0 S publicValues δ δ' pre t u h

theorem roundError_eq_iInf (S : Iop.Setup EF) (δ δ' : NNReal) :
    S.lengthError δ δ' = ⨅ loss, roundBoundL S δ δ' loss := by
  unfold Setup.lengthError roundBoundL
  by_cases hf : S.params.logFinalPolyLen < S.logN
  · have : S.Folds := ⟨hf⟩
    simp only [hf, ↓reduceIte, ↓reduceDIte]
    rfl
  · simp only [hf, ↓reduceIte, ↓reduceDIte, iInf_const]

variable (EF) in
/-- The largest round bound over the admitted lengths at proximity losses `loss n`. -/
noncomputable def roundBoundC (loss : ℕ → NNReal) : ENNReal :=
  ⨆ (m : ℕ) (h : C.Admits m), roundBoundL (C.setupAt EF m h) (δ m) (δ' m) (loss m)

theorem le_roundBoundC (loss : ℕ → NNReal) (m : ℕ) (h : C.Admits m) :
    roundBoundL (C.setupAt EF m h) (δ m) (δ' m) (loss m) ≤ roundBoundC EF C δ δ' loss :=
  le_iSup_of_le m (le_iSup (fun h ↦ roundBoundL (C.setupAt EF m h) (δ m) (δ' m) (loss m)) h)

theorem le_roundErrorC (m : ℕ) (h : C.Admits m) :
    (C.setupAt EF m h).lengthError (δ m) (δ' m) ≤ C.roundError EF δ δ' :=
  le_iSup_of_le m (le_iSup (fun h ↦ (C.setupAt EF m h).lengthError (δ m) (δ' m)) h)

/-- A duplex call is bad at some admitted length. -/
def RoundBadC (loss : ℕ → NNReal) (pre : QueryLog (spec F (C.streamLen EF))) (t : Query F)
    (u : Answer (C.streamLen EF) t) : Prop :=
  ∃ (m : ℕ) (h : C.Admits m),
    RoundBadL publicValues (C.setupAt EF m h) (δ m) (δ' m) (loss m) pre t u

/-- **A fresh answer is bad at one length.** On fields of at least `2 ^ 8` elements with
two-adicity below `2 ^ 64`, a uniform answer is round-bad at some admitted length with probability
at most the largest round bound: the call is parsed with one domain separator, so at most one
length can find it bad. -/
theorem prob_roundBadC_le (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64)
    (loss : ℕ → NNReal) (pre : QueryLog (spec F (C.streamLen EF))) (t : Query F) :
    Pr{let u ← $ᵗ (Answer (C.streamLen EF) t)}[
      RoundBadC C publicValues δ δ' loss pre t u] ≤ roundBoundC EF C δ δ' loss := by
  by_cases hex : ∃ (m : ℕ) (_ : C.Admits m), starkSeedOf EF C.params C.air m <+: firstBlock pre t
  · obtain ⟨m, h, hpre⟩ := hex
    have key : ∀ u, RoundBadC C publicValues δ δ' loss pre t u →
        RoundBadL publicValues (C.setupAt EF m h) (δ m) (δ' m) (loss m) pre t u := by
      rintro u ⟨m', h', hb⟩
      have hp' : starkSeedOf EF C.params C.air m' <+: firstBlock pre t :=
        prefix_firstBlockL publicValues (C.setupAt EF m' h') _ _ _ pre t u hb
      have hm : m' = m := eq_of_seed_prefix C h8 h64 h' h _ hp' hpre
      subst hm
      exact hb
    exact (prEvent_mono _ _ _ key).trans ((prob_roundBadL_le publicValues (C.setupAt EF m h)
      (δ m) (δ' m) (loss m) pre t).trans (le_roundBoundC C δ δ' loss m h))
  · refine le_of_eq_of_le (prEvent_congr_iff _ fun u ↦ (?_ : _ ↔ False)) (by
      simp only [prEvent_false, zero_le])
    refine ⟨fun ⟨m, h, hb⟩ ↦ hex ⟨m, h,
      prefix_firstBlockL publicValues (C.setupAt EF m h) _ _ _ pre t u hb⟩, False.elim⟩

/-- The infimum over the losses of the largest round bound at the chosen losses is at most the
largest round error. -/
theorem le_roundError_of_forall (n : Nat) (hn : n ≠ 0) (H P : ℝ≥0∞)
    (hall : ∀ loss : ℕ → NNReal, P ≤ n * roundBoundC EF C δ δ' loss + H) :
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
      roundBoundL (C.setupAt EF m h) (δ m) (δ' m) l <
        (C.setupAt EF m h).lengthError (δ m) (δ' m) + ε₁ := fun m h ↦ by
    have hfin := lt_of_le_of_lt (le_roundErrorC C δ δ' m h) hR
    rw [roundError_eq_iInf] at hfin ⊢
    exact iInf_lt_iff.mp (ENNReal.lt_add_right hfin.ne hε₁)
  let loss : ℕ → NNReal := fun m ↦ if hm : C.Admits m then (hex m hm).choose else 0
  have hloss : roundBoundC EF C δ δ' loss ≤ C.roundError EF δ δ' + ε₁ := by
    refine iSup_le fun m ↦ iSup_le fun h ↦ ?_
    have hl : loss m = (hex m h).choose := by simp only [loss, h, ↓reduceDIte]
    rw [hl]
    exact (hex m h).choose_spec.le.trans (add_le_add (le_roundErrorC C δ δ' m h) le_rfl)
  calc P ≤ n * roundBoundC EF C δ δ' loss + H := hall loss
    _ ≤ n * (C.roundError EF δ δ' + ε₁) + H := by gcongr
    _ = n * C.roundError EF δ δ' + H + ε := by
        rw [mul_add, ENNReal.mul_div_cancel hn' (ENNReal.natCast_ne_top n)]
        ring

/-- **Knowledge soundness in the random-oracle model**, with the event spelled out. -/
theorem prob_unopened_le (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat) (prover : C.NIProver EF)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let result ← C.run publicValues prover}[Unopened C publicValues δ' result] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) := by
  set n := Q + C.verifierQueries EF
  set c := 2 ^ (C.params.capHeight + 1) + 2
  have hn0 : 0 < n := by
    have h3 : 3 ≤ verifierCallsAt EF C.params C.air 0 := by
      unfold verifierCallsAt; dsimp only; omega
    have h4 := le_foldr_max ((List.range (twoAdicity F + 1)).map
      (verifierCallsAt EF C.params C.air)) _
      (List.mem_map_of_mem (List.mem_range.mpr (Nat.succ_pos (twoAdicity F))))
    have : 0 < C.verifierCallsMax EF := lt_of_lt_of_le (by omega) (h3.trans h4)
    unfold n Statement.verifierQueries
    omega
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
  set bd := Statement.boundDigestsC (EF := EF) C
  rw [show ((Q : ℝ≥0∞) + (C.verifierQueries EF : ℕ)) = (n : ℝ≥0∞) by simp only [n, Nat.cast_add]]
  refine le_roundError_of_forall (EF := EF) C δ δ' n hn0.ne' _ _ fun loss ↦ ?_
  rw [run_eq]
  refine (prEvent_exists_fresh_bad_le (game C publicValues prover) n
    (isTotalQueryBound_game C publicValues prover Q hQ) (Unopened C publicValues δ')
    (fun pre t u ↦ Clash bd pre t u ∨ RoundBadC C publicValues δ δ' loss pre t u)
    (((c * n : Nat) : ℝ≥0∞) * (Fintype.card (Digest F) : ℝ≥0∞)⁻¹ +
      roundBoundC EF C δ δ' loss)
    (fun pre t hlen _ ↦ (prEvent_or_le _ _ _).trans
      (add_le_add (prob_clash_le bd _ Nat.one_le_two_pow
        (fun c i ↦ length_boundDigestsOf_le _ _ c i) _ n pre hlen t)
        (prob_roundBadC_le C publicValues δ δ' h8 h64 loss pre t)))
    fun answer hev ↦ ?_).trans ?_
  · rw [evalWithAnswerFn_game] at hev
    obtain ⟨hok, hfail⟩ := hev
    dsimp only at hok hfail
    set proof := evalWithAnswerFn (QueryImpl.ofFn answer) prover
    have h := C.admits_of_ok answer proof publicValues hok
    set S := C.setupAt EF proof.degreeBits h
    have hlog := tableQueryLog_game C publicValues answer prover
    have hlen := length_tableQueryLog_le answer _ n
      (isTotalQueryBound_game C publicValues prover Q hQ)
    rw [hlog] at hlen
    have hsetup : ∀ e ∈ tableQueryLog S.setupRo answer,
        e ∈ tableQueryLog (setupAndProve C prover) answer := fun e he ↦ by
      rw [C.setupRo_setupAt _ h] at he
      erw [tableQueryLog_setupAndProve C answer prover]
      exact List.mem_append_left _ he
    have hδS : (δ' proof.degreeBits : ℝ) < 1 - S.rate := by
      rw [Statement.rate_setupAt]; exact hδ' _ h
    have hsmall' := lt_of_le_of_lt (Nat.mul_le_mul_left c hlen) hsmall
    set L : QueryLog (spec F S.streamLen) :=
      (tableQueryLog (setupAndProve C prover) answer : QueryLog (spec F S.streamLen)) ++
        tableQueryLog (verifyWith (ideal F S.streamLen) S.params S.air
          (preprocessedKeyWith (idealOf answer) C.params C.air C.preprocessedLogN) proof
          publicValues) answer with hLdef
    have hL : tableQueryLog (game C publicValues prover) answer = L := hlog
    rw [hL]
    have hbad : ∃ (p : Nat) (hp : p < L.length), L[p].1 ∉ (L.take p).map Sigma.fst ∧
        (Clash (boundDigests S) (L.take p) L[p].1 L[p].2 ∨
          RoundBadL publicValues S (δ proof.degreeBits) (δ' proof.degreeBits)
            (loss proof.degreeBits) (L.take p) L[p].1 L[p].2) := by
      by_cases hf : C.params.logFinalPolyLen < proof.degreeBits
      · have : S.Folds := ⟨hf⟩
        obtain ⟨p, hp, hfresh, hb⟩ := exists_badAt S publicValues (δ proof.degreeBits)
          (δ' proof.degreeBits) (loss proof.degreeBits) hδS answer _ proof
          (tableQueryLog (setupAndProve C prover) answer) (consistent_tableQueryLog _)
          (C.preprocessedKeyWith_setupAt answer _ h) hsetup rfl hok hsmall' (hfail h)
        refine ⟨p, hp, hfresh, hb.imp id fun hr ↦ ?_⟩
        have hf' : S.params.logFinalPolyLen < S.logN := hf
        unfold RoundBadL
        simp only [hf', ↓reduceDIte]
        exact hr
      · have h0 : C.params.logFinalPolyLen = proof.degreeBits := by
          have := h.sound.finalPolyFits; omega
        obtain ⟨p, hp, hfresh, hb⟩ := exists_badAt0 S publicValues (δ proof.degreeBits)
          (δ' proof.degreeBits) h0 hδS answer _ proof
          (tableQueryLog (setupAndProve C prover) answer) (consistent_tableQueryLog _)
          (C.preprocessedKeyWith_setupAt answer _ h) hsetup rfl hok hsmall' (hfail h)
        refine ⟨p, hp, hfresh, hb.imp id fun hr ↦ ?_⟩
        have hf' : ¬ S.params.logFinalPolyLen < S.logN := hf
        unfold RoundBadL
        simp only [hf', ↓reduceDIte]
        exact hr
    obtain ⟨p, hp, hfresh, hb⟩ := hbad
    refine ⟨_, _, _, (List.take_append_drop p _).symm.trans
      (by rw [List.drop_eq_getElem_cons hp]; rfl), hfresh, ?_⟩
    rcases hb with hc | hr
    · left
      rw [C.boundDigests_setupAt (EF := EF) _ h] at hc
      exact hc
    · exact Or.inr ⟨_, h, hr⟩
  · rw [mul_add, add_comm, hashError_eq]

end Bound

end CompStark.Ni
