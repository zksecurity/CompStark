/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.StarkStable
public import CompStark.Fs.StarkFiatShamir
public import CompStark.Ni.Answers
public import CompStark.Ni.Lengths
public import CompStark.Ni.QueryBound
public import CompStark.Ni.Setup

/-! # Knowledge soundness of Plonky3's STARK verifier with Merkle commitments

The game (`Statement.starkGame`) computes the verifying key of the AIR's preprocessed trace on the
verifier's random oracles, runs an adversary that outputs public values and a proof, and runs
Plonky3's verifier on them, all through `translate` against ArkLib's logged lazy oracle
`Bcs.realImpl`. `Statement.knowledgeSoundness_bcs` bounds the probability that the verifier
accepts while no trace of the proof's length close to the trace extracted from the log's hash
answers under the proof's trace commitment satisfies the AIR, by ArkLib's BCS theorem
(`KnowledgeCertificate.bcs_knowledge_soundness`) on the STARK's snapshot protocol plus the
digest-clash bound `hashBadError`.

* `selfLog`, `run_simulateQ_selfLog`: a program keeping its own log of the real oracles ends with
  the real log; `run_realImpl_of_replay`, `replay_of_mem_support_realImpl`: a logged run is the
  replay from its final log; `evalWithAnswerFn_of_replay`: a replayed program of the verifier's
  oracles runs on the log's answers (`logAnswer`).
* `Statement.bcsAdversary`: the BCS theorem's adversary runs the game with its own log, reads the
  proof's selection off it (`selectionOf`, `parse`), runs the duplex verifier's completion of it so
  that the completion's chain queries are logged, and outputs the selection with its snapshots
  filled from its log (`fillSelection`, `Bcs.fill`). The BCS theorem's real game on it is the game
  followed by the two completions (`run_realExecution_bcsAdversary`); it makes at most the
  adversary's duplex calls, the setup's and the verifier's oracle calls and the completion's chain
  queries (`isQueryBoundP_bcsAdversary`).
* `Statement.bcsEvent_of_mem_support`: on a run without digest clashes (`HashBad`) where the
  verifier accepts while the extracted trace is far, the completions end in the BCS theorem's
  event. The real completion of the filled selection replays on the log to the path the verifier's
  challenges give (`replay_realCompletion`); its commitments open at the filled snapshots as at
  the final hash answers (`openedPath_fill`, `opensStable_parse`), so the opened path is
  `Setup.proofPath`; the commitments bind the words extracted from the log (`capBinding_of_log`,
  with a digest `dstar` outside the log's digests and the commitments', `capDigests`), so the
  STARK's terminal holds (`Setup.terminal_of_verifyWith`), while the far trace makes the
  extraction fail.
-/

@[expose] public section

/-! ### Logged runs of the real oracles -/

namespace CompStark.Fs
open OracleComp OracleSpec
open Interaction.Oracle.Security Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

section RealLog

variable {S I O ι : Type} [DecidableEq S] [DecidableEq I] [DecidableEq ι]
  [SampleableType S] [SampleableType O] {hs : OracleSpec ι} [∀ t, SampleableType (hs.Range t)]

/-- A program's queries forwarded with the log `Bcs.realImpl` keeps: a query logged before is
answered from the log without asking, any other is asked and appended with its answer. -/
def selfLog : QueryImpl (unifSpec + (chainSpec S I O + hs))
    (StateT (QueryLog (chainSpec S I O + hs)) (OracleComp (unifSpec + (chainSpec S I O + hs))))
  | .inl n => StateT.mk fun log =>
      (fun u => (u, log)) <$> liftM ((unifSpec + (chainSpec S I O + hs)).query (.inl n))
  | .inr t => StateT.mk fun log => match Bcs.cacheOf log t with
    | some u => pure (u, log)
    | none => (fun u => (u, log ++ [⟨t, u⟩])) <$>
        liftM ((unifSpec + (chainSpec S I O + hs)).query (.inr t))

/-- **A program's own log is the real log.** Run on the logged real oracles from a log, a
program forwarding its queries with `selfLog` from the same log ends with its log equal to the
real one. -/
theorem run_simulateQ_selfLog {α : Type} (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α)
    (log : QueryLog (chainSpec S I O + hs)) :
    (simulateQ Bcs.realImpl ((simulateQ selfLog P).run log)).run log =
      (fun z => (z, z.2)) <$> (simulateQ Bcs.realImpl P).run log := by
  induction P using OracleComp.inductionOn generalizing log with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | t
    · simp only [selfLog, StateT.run_mk, simulateQ_map, simulateQ_spec_query, StateT.run_map,
        bind_map_left, Bcs.realImpl_run_unif]
      exact bind_congr fun u => ih u log
    · cases h : Bcs.cacheOf log t with
      | some u =>
        simp only [selfLog, StateT.run_mk, h, simulateQ_pure, StateT.run_pure, pure_bind,
          Bcs.realImpl_run_of_some h]
        exact ih u log
      | none =>
        simp only [selfLog, StateT.run_mk, h, simulateQ_map, simulateQ_spec_query,
          StateT.run_map, bind_map_left, Bcs.realImpl_run_of_none h]
        exact bind_congr fun u => ih u _

/-- **A replay is a logged run.** A program whose replay from a log's cache succeeds runs on the
logged real oracles to the replayed result, the log unchanged. -/
theorem run_realImpl_of_replay {α : Type} (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α)
    (log : QueryLog (chainSpec S I O + hs)) (a : α) (h : replay (Bcs.cacheOf log) P = some a) :
    (simulateQ Bcs.realImpl P).run log = pure (a, log) := by
  induction P using OracleComp.inductionOn with
  | pure b =>
    simp only [replay_pure, Option.some.injEq] at h
    simp [h]
  | query_bind q k ih =>
    rw [replay_query_bind] at h
    rcases q with n | x
    · simp [cacheAnswers] at h
    · cases hx : Bcs.cacheOf log x with
      | none => simp [cacheAnswers, hx] at h
      | some u =>
        simp only [cacheAnswers, hx] at h
        change replay _ (k u) = some a at h
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        rw [Bcs.realImpl_run_of_some hx, pure_bind]
        exact ih u h

/-- **A logged run replays.** A program drawing no private coin, run on the logged real oracles,
returns what its replay from the final log's cache returns. -/
theorem replay_of_mem_support_realImpl {α : Type}
    (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α)
    (hP : IsQueryBoundP P (fun t => isUnif t = true) 0) (log : QueryLog (chainSpec S I O + hs))
    (z : α × QueryLog (chainSpec S I O + hs))
    (hz : z ∈ support ((simulateQ Bcs.realImpl P).run log)) :
    replay (Bcs.cacheOf z.2) P = some z.1 := by
  have h := Bcs.map_run_simulateQ_realImpl P log
  have hz' : Prod.map id Bcs.cacheOf z ∈ support
      ((simulateQ (chainSpec S I O + hs).romImpl P).run (Bcs.cacheOf log)) := by
    rw [← h, support_map]
    exact ⟨z, hz, rfl⟩
  exact replay_of_mem_support_run P hP _ _ hz'

/-- Whether a query of a private coin, a chain or a hash oracle asks the hash oracle. -/
def isHashQuery {α β γ : Type} : α ⊕ (β ⊕ γ) → Bool
  | .inr (.inr _) => true
  | _ => false

/-- A logged run asking no hash query appends only chain entries to its log. -/
theorem append_of_mem_support_realImpl {α : Type}
    (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α)
    (hP : IsQueryBoundP P (fun t => isHashQuery t = true) 0)
    (log : QueryLog (chainSpec S I O + hs)) (z : α × QueryLog (chainSpec S I O + hs))
    (hz : z ∈ support ((simulateQ Bcs.realImpl P).run log)) :
    ∃ l, z.2 = log ++ l ∧ ∀ e ∈ l, e.1.isLeft = true := by
  induction P using OracleComp.inductionOn generalizing log with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact ⟨[], by rw [hz, List.append_nil], fun _ h => absurd h List.not_mem_nil⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨w, hw, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rcases t with n | t
    · rw [Bcs.realImpl_run_unif, support_map] at hw
      obtain ⟨u, -, rfl⟩ := hw
      have h2 : IsQueryBoundP (k u) (fun t => isHashQuery t = true) 0 := by
        have := hP.2 u
        split_ifs at this <;> exact this
      exact ih u h2 log hz
    · have hk : IsQueryBoundP (k w.1) (fun t => isHashQuery t = true) 0 := by
        have := hP.2 w.1
        split_ifs at this
        · simpa using this
        · exact this
      cases hc : Bcs.cacheOf log t with
      | some u =>
        rw [Bcs.realImpl_run_of_some hc, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact ih _ hk log hz
      | none =>
        rw [Bcs.realImpl_run_of_none hc, support_map] at hw
        obtain ⟨u, -, rfl⟩ := hw
        obtain ⟨l, hl, hle⟩ := ih u hk _ hz
        rcases t with q | e
        · refine ⟨⟨.inl q, u⟩ :: l, by rw [hl, List.append_assoc]; rfl, fun e he => ?_⟩
          rcases List.mem_cons.mp he with rfl | he
          · rfl
          · exact hle e he
        · simp [isHashQuery] at hP

/-- A logged run grows its log by at most one entry per oracle query. -/
theorem length_le_of_mem_support_realImpl {α : Type}
    (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α) {n : ℕ}
    (hP : IsQueryBoundP P (fun t => t.isRight = true) n)
    (log : QueryLog (chainSpec S I O + hs)) (z : α × QueryLog (chainSpec S I O + hs))
    (hz : z ∈ support ((simulateQ Bcs.realImpl P).run log)) :
    z.2.length ≤ log.length + n := by
  induction P using OracleComp.inductionOn generalizing log n with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨w, hw, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rcases t with m | t
    · rw [Bcs.realImpl_run_unif, support_map] at hw
      obtain ⟨u, -, rfl⟩ := hw
      exact ih u (by simpa using hP.2 u) log hz
    · have hn : 0 < n := by simpa using hP.1
      have hk : IsQueryBoundP (k w.1) (fun t => t.isRight = true) (n - 1) := by
        simpa using hP.2 w.1
      cases hc : Bcs.cacheOf log t with
      | some u =>
        rw [Bcs.realImpl_run_of_some hc, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        have := ih _ hk log hz
        omega
      | none =>
        rw [Bcs.realImpl_run_of_none hc, support_map] at hw
        obtain ⟨u, -, rfl⟩ := hw
        have := ih u hk _ hz
        simp only [List.length_append, List.length_singleton] at this
        omega

omit [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
/-- Forwarding a query with `selfLog` asks at most that query of the chain. -/
theorem isQueryBoundP_selfLog_step (t : (unifSpec + (chainSpec S I O + hs)).Domain)
    (log : QueryLog (chainSpec S I O + hs)) :
    IsQueryBoundP ((selfLog t).run log) (fun t => isChain t = true)
      (if isChain t = true then 1 else 0) := by
  rcases t with n | t
  · simp only [selfLog, StateT.run_mk, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    simp [isChain]
  · simp only [selfLog, StateT.run_mk]
    cases Bcs.cacheOf log t with
    | some u => trivial
    | none =>
      simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      intro h
      simp only [h, ↓reduceIte, Nat.lt_add_one]

omit [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
/-- A program making at most `n` chain queries makes at most `n` forwarded with `selfLog`. -/
theorem isQueryBoundP_selfLog {α : Type} {P : OracleComp (unifSpec + (chainSpec S I O + hs)) α}
    {n : ℕ} (hP : IsQueryBoundP P (fun t => isChain t = true) n)
    (log : QueryLog (chainSpec S I O + hs)) :
    IsQueryBoundP ((simulateQ selfLog P).run log) (fun t => isChain t = true) n :=
  hP.simulateQ_run_StateT_of_step isQueryBoundP_selfLog_step log

omit [DecidableEq S] [DecidableEq I] [DecidableEq ι] [SampleableType S] [SampleableType O]
  [∀ t, SampleableType (hs.Range t)] in
/-- Asking a program of the chain beside the hash oracle asks no hash query. -/
theorem isQueryBoundP_liftHash_hash {α : Type}
    (P : OracleComp (unifSpec + (chainSpec S I O + []ₒ)) α) :
    IsQueryBoundP (simulateQ (liftHash (hs := hs)) P) (fun t => isHashQuery t = true) 0 := by
  induction P using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with n | q | e
    · simp only [liftHash]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [isHashQuery]), fun u => by split_ifs <;> exact ih u⟩
    · simp only [liftHash]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [isHashQuery]), fun u => by split_ifs <;> exact ih u⟩
    · exact e.elim

end RealLog

/-! ### The verifier's oracles replayed from a log -/

section Replay
open CompStark.Stark CompStark.RandomOracle

variable {F : Type} [BaseField F] {K : ℕ}

/-- **A replayed program runs on the logged answers.** A program of the verifier's oracles whose
translation replays from a log's cache returns the same on the log's answers, whatever answer
`dstar` stands for the queries the log misses. -/
theorem evalWithAnswerFn_of_replay {α : Type} (P : OracleComp (spec F K) α)
    (L : QueryLog (sumSpec F K)) (dstar : Digest F) (a : α)
    (h : replay (Bcs.cacheOf L) (simulateQ translate P) = some a) :
    evalWithAnswerFn (QueryImpl.ofFn (logAnswer L dstar)) P = a := by
  induction P using OracleComp.inductionOn with
  | pure b =>
    simp only [simulateQ_pure, replay_pure, Option.some.injEq] at h
    exact h
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, replay_bind] at h
    unfold evalWithAnswerFn at ih ⊢
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases q with ⟨cap, input⟩ | row | ⟨left, right⟩
    · simp only [translate] at h
      erw [replay_query] at h
      cases hc : Bcs.cacheOf L (.inl (cap, input)) with
      | none => rw [hc] at h; cases h
      | some u =>
        rw [hc] at h
        have hu : logAnswer L dstar (.duplex cap input) = u := by
          simp only [logAnswer, hc, Option.getD_some]
        simp only [QueryImpl.ofFn_apply, hu]
        exact ih u h
    · simp only [translate] at h
      erw [replay_query] at h
      cases hc : Bcs.cacheOf L (.inr (.inl row)) with
      | none => rw [hc] at h; cases h
      | some u =>
        rw [hc] at h
        have hu : logAnswer L dstar (.leaf row) = u := by
          simp only [logAnswer, logHash, hashCacheOf_apply, hc, Option.getD_some]
        simp only [QueryImpl.ofFn_apply, hu]
        exact ih u h
    · simp only [translate] at h
      erw [replay_query] at h
      cases hc : Bcs.cacheOf L (.inr (.inr (left, right))) with
      | none => rw [hc] at h; cases h
      | some u =>
        rw [hc] at h
        have hu : logAnswer L dstar (.node left right) = u := by
          simp only [logAnswer, logCompress, hashCacheOf_apply, hc, Option.getD_some]
        simp only [QueryImpl.ofFn_apply, hu]
        exact ih u h

omit [BaseField F] in
/-- A program making at most `q` oracle calls asks at most `q` queries of the verifier's oracles
through `translate`, and no private coin. -/
theorem isQueryBoundP_translate_isRight {α : Type} {P : OracleComp (spec F K) α} {q : ℕ}
    (hq : IsTotalQueryBound P q) :
    IsQueryBoundP (simulateQ translate P) (fun t => t.isRight = true) q := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at hq
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with ⟨cap, input⟩ | row | ⟨left, right⟩ <;>
    · simp only [translate]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr hq.1, fun u => by simpa using ih u (hq.2 u)⟩

omit [BaseField F] in
/-- A program of the verifier's oracles draws no private coin through `translate`. -/
theorem isQueryBoundP_translate_unif {α : Type} (P : OracleComp (spec F K) α) :
    IsQueryBoundP (simulateQ translate P) (fun t => isUnif t = true) 0 := by
  induction P using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with ⟨cap, input⟩ | row | ⟨left, right⟩ <;>
    · simp only [translate]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [isUnif]), fun u => by split_ifs <;> exact ih u⟩

end Replay

end CompStark.Fs

/-! ### Chain entries appended to a log, and binding -/

namespace CompStark.Fs
open CompStark.Stark CompStark.RandomOracle OracleComp OracleSpec
open Interaction.Oracle.Security

section Append
variable {κ₁ κ₂ : Type} [DecidableEq κ₁] [DecidableEq κ₂] {spec₁ : OracleSpec κ₁}
  {spec₂ : OracleSpec κ₂}

/-- Appending entries of the first oracle keeps the cache of the second. -/
theorem cacheOf_append_inl {L l : QueryLog (spec₁ + spec₂)} (hl : ∀ e ∈ l, e.1.isLeft = true)
    (t : κ₂) : Bcs.cacheOf (L ++ l) (.inr t) = Bcs.cacheOf L (.inr t) := by
  induction L with
  | nil =>
    rw [List.nil_append, Bcs.cacheOf_nil, QueryCache.empty_apply]
    refine cacheOf_eq_none_iff.mpr fun hmem => ?_
    obtain ⟨e, he, hk⟩ := List.mem_map.mp hmem
    have := hl e he
    rw [hk] at this
    cases this
  | cons e L ih =>
    rw [List.cons_append, Bcs.cacheOf_cons, Bcs.cacheOf_cons]
    by_cases h : Sum.inr t = e.1
    · obtain ⟨k, u⟩ := e
      subst h
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ h, QueryCache.cacheQuery_of_ne _ _ h, ih]

end Append

variable {F : Type} [BaseField F] {K : ℕ}

/-- Appending chain entries keeps the hash answers of a log. -/
theorem hashCacheOf_append_chain {L l : QueryLog (sumSpec F K)}
    (hl : ∀ e ∈ l, e.1.isLeft = true) : Bcs.hashCacheOf (L ++ l) = Bcs.hashCacheOf L :=
  QueryCache.ext fun t => cacheOf_append_inl hl t

/-- Appending chain entries makes no digest clash. -/
theorem not_hashBad_append_chain {offs : List ℕ} {capLen : ℕ}
    {L l : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    (hl : ∀ e ∈ l, e.1.isLeft = true) : ¬ HashBad offs capLen (L ++ l) := by
  rintro ⟨pre, t, u, post, h, hfresh, hu⟩
  rcases List.append_eq_append_iff.mp h with ⟨a, rfl, hl'⟩ | ⟨c, rfl, hc⟩
  · have := hl _ (hl' ▸ List.mem_append_right _ List.mem_cons_self)
    cases this
  · rcases c with _ | ⟨x, c⟩
    · simp only [List.nil_append] at hc
      have := hl _ (hc ▸ List.mem_cons_self)
      cases this
    · obtain ⟨rfl, -⟩ := List.cons.inj hc
      exact hL ⟨pre, t, u, c, rfl, hfresh, hu⟩

/-- A digest outside a log's digests and a list of digests, when there are more digests. -/
theorem exists_not_mem_logDigests_append {offs : List ℕ} {capLen : ℕ}
    (hB : 0 < offs.length * capLen) (L : QueryLog (sumSpec F K)) (D : List (Digest F))
    (h : 1 + (2 + offs.length * capLen) * L.length + D.length < Nat.card F ^ 8) :
    ∃ dstar, dstar ∉ logDigests offs capLen L ∧ dstar ∉ D := by
  classical
  by_contra hall
  simp only [not_exists, not_and_or, not_not] at hall
  have hsub : (Finset.univ : Finset (Digest F)) ⊆ (logDigests offs capLen L ++ D).toFinset :=
    fun d _ ↦ List.mem_toFinset.mpr (List.mem_append.mpr (hall d))
  have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_digest, List.length_append] at hcard
  have := length_logDigests_le hB L
  omega

/-- A log's chain answers are the duplex answers of its logged answers. -/
theorem chainPart_le_duplexCache (L : QueryLog (sumSpec F K)) (dstar : Digest F) :
    ∀ t u, Bcs.chainPart (Bcs.cacheOf L) t = some u →
      duplexCache (logAnswer L dstar) t = some u := by
  rintro (q | e) u h
  · simp only [Bcs.chainPart, QueryCache.inl_apply_inl, QueryCache.fst_apply] at h
    simp only [duplexCache, QueryCache.ofFn_apply, logAnswer, h, Option.getD_some]
  · exact e.elim

/-- **Binding of a cap from a log.** Without digest clashes, accepted openings on primitives
answering the leaf hashes and compressions as the log does, `dstar` outside the log's digests
otherwise, bind every entry of a cap that misses `dstar`. -/
theorem capBinding_of_log {offs : List ℕ} {capLen : ℕ}
    {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L) {dstar : Digest F}
    (hd : dstar ∉ logDigests offs capLen L) (H : Primitives F Id)
    (hH : H.hash = logHash L dstar) (hC : H.compress = logCompress L dstar) (cap : Cap F)
    (hcap : ∀ d ∈ cap.toList, d ≠ dstar) :
    Ni.CapBinding (merkleCache (Bcs.hashCacheOf L)) H cap := by
  intro j n k i values path hn hv
  have hroot : cap.toList.getD j 0 ≠ dstar := by
    rcases getD_cap cap.toList j with h0 | h0
    · rw [h0]
      exact fun h => hd (h ▸ initCap_mem_logDigests L)
    · exact hcap _ h0
  simp only [Ni.verifyBatchH, hH, hC] at hv
  exact extractRow_of_logVerifyBatch hL hd hroot n k i hn values path hv

end CompStark.Fs

/-- An event is at most itself without a second event, plus the second event. -/
theorem prEvent_le_and_not_add {α : Type} (mx : ProbComp α) (p q : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[p x ∧ ¬ q x] + Pr{let x ← mx}[q x] :=
  (prEvent_mono_of_support mx p _ fun x _ hx =>
    (em (q x)).symm.imp (fun h => ⟨hx, h⟩) id).trans (prEvent_or_le mx _ _)

/-! ### The game and the adversary of the BCS theorem -/

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fs CompStark.RandomOracle OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- The game on the verifier's oracles: the verifying key of the AIR's preprocessed trace, the
adversary's public values and proof, and Plonky3's verifier's verdict on them. -/
def starkGame (adversary : OracleComp (spec F K) (List F × Proof F EF)) :
    OracleComp (spec F K)
      (Option (PreprocessedKey F) × List F × Proof F EF × Except String Unit) :=
  preprocessedKeyWith (ideal F K) C.params C.air C.preprocessedLogN >>= fun vk =>
    adversary >>= fun x =>
      verifyWith (ideal F K) C.params C.air vk x.2 x.1 >>= fun v => pure (vk, x.1, x.2, v)

/-- A selection of the snapshot protocol of the STARK, with draws from `coinCount` squeezes. -/
abbrev BcsSelection : Type :=
  SnapSelection (hs := merkleSpec F) Unit (fun _ : C.Input => C.publicCoin EF)
    (fun _ => C.decoder EF K (C.coinCount EF K)) fun _ => C.layout EF K (C.coinCount EF K)

/-- The selection read off the game's outcome, every snapshot move `T`: the statement's input
and the proof's messages, if the proof's length is admitted, its key observed with the
statement's length, and its messages readable (`parse`). -/
noncomputable def selectionOf (T : (merkleSpec F).QueryCache)
    (out : Option (PreprocessedKey F) × List F × Proof F EF × Except String Unit) :
    C.BcsSelection EF K := by
  classical exact
    if h : C.Admits out.2.2.1.degreeBits ∧ (preprocessedDigest out.1).length = C.digestLength
    then (C.parse EF K T ⟨_, h.1⟩ out.2.2.1).map fun msgs =>
      ⟨C.inputOf out.1 out.2.1 h.2, msgs, ()⟩
    else none

/-- A selection with the snapshot move of each block set to the log's snapshot at the block's
chain query (`Bcs.fill`). -/
noncomputable def fillSelection (L : QueryLog (sumSpec F K)) (sel : C.BcsSelection EF K) :
    C.BcsSelection EF K :=
  sel.map fun x => ⟨x.1, fill (fun _ : C.Input => C.publicCoin EF)
    (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K))
    tail (Bcs.snapshotAt L) (Bcs.answerAt L) initCap x.1 x.2.1, x.2.2⟩

/-- The duplex verifier's completion of a selection, asked of the chain beside the Merkle
hashes. -/
noncomputable def completionOf (sel : C.BcsSelection EF K) :
    OracleComp (unifSpec + sumSpec F K)
      (SnapOutcome (hs := merkleSpec F) Unit (fun _ : C.Input => C.publicCoin EF)
        (fun _ => C.decoder EF K (C.coinCount EF K))
        fun _ => C.layout EF K (C.coinCount EF K)) :=
  simulateQ (liftHash (hs := merkleSpec F))
    (realCompletion initCap (fun _ : C.Input => C.publicCoin EF)
      (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K))
      tail sel)

/-- **The adversary of the BCS theorem.** It runs the game itself, keeping its own log of the
oracles: the verifying key, the adversary, Plonky3's verifier. It reads the proof's selection off
the outcome and runs the duplex verifier's completion of it, so that the completion's chain
queries are logged, and outputs the selection with its snapshots filled from its log. -/
noncomputable def bcsAdversary (adversary : OracleComp (spec F K) (List F × Proof F EF)) :
    OracleComp (unifSpec + sumSpec F K) (C.BcsSelection EF K) :=
  (simulateQ selfLog (simulateQ translate (C.starkGame EF K adversary))).run [] >>= fun x =>
    (simulateQ selfLog (C.completionOf EF K
      (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1))).run x.2 >>= fun y =>
      pure (C.fillSelection EF K y.2 (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1))

/-- The BCS theorem's real game on `bcsAdversary` is the game, then the completion the adversary
runs, then the real completion of the filled selection. -/
theorem run_realExecution_bcsAdversary (adversary : OracleComp (spec F K) (List F × Proof F EF)) :
    (simulateQ Bcs.realImpl (realExecution initCap (fun _ : C.Input => C.publicCoin EF)
      (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K))
      tail (C.bcsAdversary EF K adversary))).run [] =
      (simulateQ Bcs.realImpl (simulateQ translate (C.starkGame EF K adversary))).run [] >>=
        fun x => (simulateQ Bcs.realImpl (C.completionOf EF K
          (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1))).run x.2 >>= fun y =>
          (fun o => ((C.fillSelection EF K y.2 (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1),
            o.1), o.2)) <$> (simulateQ Bcs.realImpl (C.completionOf EF K (C.fillSelection EF K y.2
              (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1)))).run y.2 := by
  simp only [realExecution, bcsAdversary, simulateQ_bind, simulateQ_map,
    StateT.run_bind, StateT.run_map, pure_bind, bind_assoc,
    run_simulateQ_selfLog, bind_map_left]
  rfl

variable {C EF K}

/-- **The verifier's oracle calls on any proof**: at most `verifierCallsMax`. -/
theorem isTotalQueryBound_verifyWith_max (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (pis : List F) :
    IsTotalQueryBound (verifyWith (ideal F K) C.params C.air vk proof pis)
      (C.verifierCallsMax EF) := by
  by_cases hdb : proof.degreeBits ≤ twoAdicity F
  · exact (Iop.Setup.isTotalQueryBound_verifyWith C.params C.air vk proof pis).mono
      (Ni.le_foldr_max _ _ (List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.lt_succ_of_le hdb), rfl⟩))
  · refine (show IsTotalQueryBound (verifyWith (ideal F K) C.params C.air vk proof pis) 0
      from ?_).mono (Nat.zero_le _)
    unfold verifyWith
    dsimp only
    rw [ite_eq_right (by omega)]
    trivial

/-- The game makes at most the adversary's oracle calls and the setup's and the verifier's. -/
theorem isTotalQueryBound_starkGame {adversary : OracleComp (spec F K) (List F × Proof F EF)}
    {q : ℕ} (hq : IsTotalQueryBound adversary q) :
    IsTotalQueryBound (C.starkGame EF K adversary) (q + C.verifierQueries EF) := by
  refine (isTotalQueryBound_bind (Iop.Setup.isTotalQueryBound_preprocessedKeyWith C.params C.air
    C.preprocessedLogN K) fun vk => isTotalQueryBound_bind hq fun x =>
      isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_verifyWith_max vk x.2 x.1) fun v =>
        (show IsTotalQueryBound (pure (vk, x.1, x.2, v) : OracleComp (spec F K) _) 0
          from trivial)).mono ?_
  unfold verifierQueries setupQueries
  omega

/-- The game makes at most the adversary's duplex calls and the setup's and the verifier's
oracle calls. -/
theorem isQueryBoundP_starkGame {adversary : OracleComp (spec F K) (List F × Proof F EF)}
    {Q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q) :
    IsQueryBoundP (C.starkGame EF K adversary) (fun t => isDuplex t = true)
      (Q + C.verifierQueries EF) := by
  refine (isQueryBoundP_bind (Iop.Setup.isTotalQueryBound_preprocessedKeyWith C.params C.air
    C.preprocessedLogN K).isQueryBoundP fun vk _ => isQueryBoundP_bind hQ fun x _ =>
      isQueryBoundP_bind (m := 0) (isTotalQueryBound_verifyWith_max vk x.2 x.1).isQueryBoundP
        fun v _ => isQueryBoundP_pure _ _ _).mono ?_
  unfold verifierQueries setupQueries
  omega

/-- The adversary of the BCS theorem makes at most the adversary's duplex calls, the setup's
and the verifier's oracle calls, and the completion's chain queries. -/
theorem isQueryBoundP_bcsAdversary {adversary : OracleComp (spec F K) (List F × Proof F EF)}
    {Q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q) :
    IsQueryBoundP (C.bcsAdversary EF K adversary) (fun t => isChain t = true)
      (Q + C.verifierQueries EF + C.verifierChainQueries EF K) := by
  have hN : ∀ _ : C.Input, (C.publicCoin EF).ChallengesLE (maxChallenges (F := F)) :=
    fun _ n ↦ (C.setup EF n).challengesLE_publicCoin
  refine (isQueryBoundP_bind (isQueryBoundP_selfLog (isQueryBoundP_translate
    (isQueryBoundP_starkGame hQ)) []) fun x _ => isQueryBoundP_bind (m := 0)
      (isQueryBoundP_selfLog (isQueryBoundP_liftHash_chain (isQueryBoundP_realCompletion initCap
        _ _ _ tail hN (fun _ node => squeezes_le node) _)) _)
      fun _ _ => isQueryBoundP_pure _ _ _).mono le_rfl

/-- The completion draws no private coin. -/
theorem isQueryBoundP_completionOf_unif (sel : C.BcsSelection EF K) :
    IsQueryBoundP (C.completionOf EF K sel) (fun t => isUnif t = true) 0 := by
  unfold completionOf
  exact isQueryBoundP_realCompletion_unif initCap _ _ _ tail sel

/-- The completion asks no hash query. -/
theorem isQueryBoundP_completionOf_hash (sel : C.BcsSelection EF K) :
    IsQueryBoundP (C.completionOf EF K sel) (fun t => isHashQuery t = true) 0 := by
  unfold completionOf
  exact isQueryBoundP_liftHash_hash _

/-- A logged run of the completion replays from its final log. -/
theorem replay_completionOf (sel : C.BcsSelection EF K) (L : QueryLog (sumSpec F K))
    (w : SnapOutcome (hs := merkleSpec F) Unit (fun _ : C.Input => C.publicCoin EF)
        (fun _ => C.decoder EF K (C.coinCount EF K))
        (fun _ => C.layout EF K (C.coinCount EF K)) × QueryLog (sumSpec F K))
    (hw : w ∈ support ((simulateQ Bcs.realImpl (C.completionOf EF K sel)).run L)) :
    replay (Bcs.cacheOf w.2) (C.completionOf EF K sel) = some w.1 :=
  replay_of_mem_support_realImpl _ (isQueryBoundP_completionOf_unif sel) L w hw

/-- The game on fixed answers: the verifying key on them, the adversary's output, and the
verifier's verdict on them. -/
theorem evalWithAnswerFn_starkGame (ans : (q : Query F) → Answer K q)
    (adversary : OracleComp (spec F K) (List F × Proof F EF)) :
    evalWithAnswerFn (QueryImpl.ofFn ans) (C.starkGame EF K adversary) =
      (preprocessedKeyWith (idealOf ans) C.params C.air C.preprocessedLogN,
        (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).1,
        (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).2,
        verifyWith (idealOf ans) C.params C.air
          (preprocessedKeyWith (idealOf ans) C.params C.air C.preprocessedLogN)
          (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).2
          (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).1) := by
  unfold evalWithAnswerFn starkGame
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_preprocessedKeyWith, simulateQ_verifyWith]
  rfl

/-- The digests of a proof's commitments and of a verifying key's commitment. -/
def capDigests (vk : Option (PreprocessedKey F)) (proof : Proof F EF) : List (Digest F) :=
  proof.traceCommit.toList ++ proof.quotientCommit.toList ++
    proof.fri.commits.toList.flatMap Array.toList ++ (vk.map fun k => k.commit.toList).getD []

/-- A list's lists of at most `c` elements each, flattened, have at most `c` per list. -/
theorem length_flatMap_le {α β : Type} (f : α → List β) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).length ≤ c) → (l.flatMap f).length ≤ l.length * c
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := length_flatMap_le f c l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have := h a List.mem_cons_self
    omega

/-- An accepted proof's commitments and its key's commitment have at most `2 ^ capHeight`
digests each, and FRI's are at most `twoAdicity F`: at most `|capOffsets| 2 ^ capHeight`. -/
theorem length_capDigests_le (n : C.Length) (H : Primitives F Id)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = n.1) (h : verifyWith H C.params C.air vk proof pis = .ok ())
    (hvk : ∀ k, vk = some k → k.commit.size ≤ 2 ^ C.params.capHeight) :
    (capDigests vk proof).length ≤ (C.capOffsets EF).length * 2 ^ C.params.capHeight := by
  obtain ⟨htr, hqu, hn, hc⟩ := (C.setup EF n).capSizes_of_verifyWith H vk proof pis hdb h
  have hf := length_flatMap_le Array.toList (2 ^ C.params.capHeight) proof.fri.commits.toList
    fun c hc' => by rw [Array.length_toList]; exact hc c (Array.mem_toList_iff.mp hc')
  have hv : ((vk.map fun k => k.commit.toList).getD []).length ≤ 2 ^ C.params.capHeight := by
    cases vk with
    | none => exact Nat.zero_le _
    | some k =>
      simp only [Option.map_some, Option.getD_some, Array.length_toList]
      exact hvk k rfl
  rw [Array.length_toList (xs := proof.fri.commits)] at hf
  simp only [capDigests, List.length_append, Array.length_toList, C.length_capOffsets EF]
  have := Nat.mul_le_mul_right (2 ^ C.params.capHeight) hn
  have htr' : proof.traceCommit.size ≤ 2 ^ C.params.capHeight := htr
  have hqu' : proof.quotientCommit.size ≤ 2 ^ C.params.capHeight := hqu
  nlinarith

/-- **The deterministic core.** On a run of the game without digest clashes in which the verifier
accepts while no trace close to the one extracted under the proof's trace commitment satisfies
the AIR, the completion the adversary of the BCS theorem runs, then the real completion of its
filled selection, end in the BCS theorem's event. -/
theorem bcsEvent_of_mem_support (hK : 0 < K) (δ δ' : ℕ → ℝ≥0)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (loss : C.Length → ℝ≥0)
    (adversary : OracleComp (spec F K) (List F × Proof F EF))
    (x : (Option (PreprocessedKey F) × List F × Proof F EF × Except String Unit) ×
      QueryLog (sumSpec F K))
    (hx : x ∈ support ((simulateQ Bcs.realImpl
      (simulateQ translate (C.starkGame EF K adversary))).run []))
    (hacc : x.1.2.2.2 = .ok ())
    (hfar : ∀ h : C.Admits x.1.2.2.1.degreeBits, ∀ trace ∈ closeTraces (C.setupAt EF _ h)
      (δ' x.1.2.2.1.degreeBits) ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
        (merkleCache (Bcs.hashCacheOf x.2)) x.1.2.2.1.traceCommit)),
      ¬ C.air.Satisfied x.1.2.2.1.degreeBits trace x.1.2.1)
    (hL : ¬ HashBad (C.capOffsets EF) (2 ^ C.params.capHeight) x.2)
    (hlen : 1 + (2 + (C.capOffsets EF).length * 2 ^ C.params.capHeight) * x.2.length +
      (C.capOffsets EF).length * 2 ^ C.params.capHeight < Nat.card F ^ 8)
    (w : _) (hw : w ∈ support ((simulateQ Bcs.realImpl (C.completionOf EF K
      (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1))).run x.2))
    (o : _) (ho : o ∈ support ((simulateQ Bcs.realImpl (C.completionOf EF K
      (C.fillSelection EF K w.2 (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1)))).run w.2)) :
    ∃ zz messages wt path,
      C.fillSelection EF K w.2 (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1) =
        some ⟨zz, messages, wt⟩ ∧ o.1 = some ⟨zz, path, wt⟩ ∧
      SnapsOK (fun _ : C.Input => C.publicCoin EF) (fun _ => C.decoder EF K (C.coinCount EF K))
        (fun _ => C.layout EF K (C.coinCount EF K)) tail (Bcs.snapshotAt o.2) (Bcs.answerAt o.2)
        initCap zz messages ∧
      ∃ p, decodePath (snapCoin (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
          (C.layout EF K (C.coinCount EF K)) true)
          (snapDecoder (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
            (C.layout EF K (C.coinCount EF K)) true) path = some p ∧
        ∃ witness, ((certificate EF zz.1.2 δ δ' hδ' loss
            fun n ↦ (C.setup EF n).queryPositions).extractor.terminalState
              (openPath (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
                (C.layout EF K (C.coinCount EF K)) true ∅ p)).holds witness ∧
          ¬ (C.rootState EF zz.1.2 δ').holds ((certificate EF zz.1.2 δ δ' hδ' loss
            fun n ↦ (C.setup EF n).queryPositions).extractor.extractWitness
              (openPath (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
                (C.layout EF K (C.coinCount EF K)) true ∅ p) witness) := by
  obtain ⟨⟨vk, pis, proof, verdict⟩, L1⟩ := x
  dsimp only at hacc hfar hL hlen hw ho ⊢
  subst hacc
  -- the game replays on its log, and the logs after it only add chain entries
  have hrep1 := replay_of_mem_support_realImpl _ (isQueryBoundP_translate_unif _) [] _ hx
  obtain ⟨l, hL2, hl⟩ := append_of_mem_support_realImpl _
    (isQueryBoundP_completionOf_hash (C := C) (EF := EF) (K := K) _) _ _ hw
  have hrepw := replay_completionOf _ _ w hw
  have hhash : Bcs.hashCacheOf w.2 = Bcs.hashCacheOf L1 := by
    rw [hL2]
    exact hashCacheOf_append_chain hl
  have hL2bad : ¬ HashBad (C.capOffsets EF) (2 ^ C.params.capHeight) w.2 := by
    rw [hL2]
    exact not_hashBad_append_chain hL hl
  have hsub : ∀ t u, Bcs.cacheOf L1 t = some u → Bcs.cacheOf w.2 t = some u :=
    fun t u h => hL2 ▸ cacheOf_append_of_eq_some h l
  have hrep2 := replay_mono hsub _ _ hrep1
  -- the game on the final log's answers, whatever answers the queries it misses
  have heval (d : Digest F) := evalWithAnswerFn_of_replay _ w.2 d _ hrep2
  have hgame (d : Digest F) :
      vk = preprocessedKeyWith (idealOf (logAnswer w.2 d)) C.params C.air C.preprocessedLogN ∧
        verifyWith (idealOf (logAnswer w.2 d)) C.params C.air vk proof pis = .ok () := by
    have h := heval d
    rw [evalWithAnswerFn_starkGame] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun y => y.2.1) h
    have h3 := congrArg (fun y => y.2.2.1) h
    have h4 := congrArg (fun y => y.2.2.2) h
    simp only at h1 h2 h3 h4
    rw [h1, h2, h3] at h4
    exact ⟨h1.symm, h4⟩
  have hadm : C.Admits proof.degreeBits := by
    have h := (hgame initCap).2
    rw [(hgame initCap).1] at h
    exact C.admits_of_ok _ proof pis h
  obtain ⟨n, hn⟩ : ∃ n : C.Length, proof.degreeBits = n.1 := ⟨⟨_, hadm⟩, rfl⟩
  have hz := length_preprocessedDigest (C := C) (idealOf (logAnswer w.2 initCap)) n vk proof pis
    hn (hgame initCap).2
  obtain ⟨msgs, hmsgs⟩ := Option.isSome_iff_exists.mp (isSome_parse (C := C) K
    (Bcs.hashCacheOf L1) (idealOf (logAnswer w.2 initCap)) n vk proof pis hn (hgame initCap).2)
  have hsel : C.selectionOf EF K (Bcs.hashCacheOf L1) (vk, pis, proof, .ok ()) =
      some ⟨C.inputOf vk pis hz, msgs, ()⟩ := by
    unfold selectionOf
    rw [dite_eq_left_of_eq_true (eq_true ⟨hadm, hz⟩)]
    have e : (⟨proof.degreeBits, hadm⟩ : C.Length) = n := Subtype.ext hn
    simp only [e, hmsgs, Option.map_some]
  -- a digest outside the log's digests and the commitments' digests
  have hD := length_capDigests_le n _ vk proof pis hn (hgame initCap).2 fun k hk =>
    size_commit_preprocessedKeyWith _ _ _ _ k ((hgame initCap).1 ▸ hk)
  obtain ⟨dstar, hd1, hd2⟩ := exists_not_mem_logDigests_append
    (offs := C.capOffsets EF) (capLen := 2 ^ C.params.capHeight) (by
      rw [C.length_capOffsets EF]; exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)) L1
    (capDigests vk proof) (by omega)
  obtain ⟨hvk, hok⟩ := hgame dstar
  rw [hsel] at hrepw ho ⊢
  -- the real completion of the filled messages, on the duplex answers
  obtain ⟨path, hrepP, hdP⟩ := replay_realCompletion initCap (fun _ : C.Input => C.publicCoin EF)
    (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K)) tail
    (duplexCache (logAnswer w.2 dstar)) (squeezeAnswer (logAnswer w.2 dstar))
    (replay_squeezeAt (logAnswer w.2 dstar)) (C.inputOf vk pis hz)
    (fill (fun _ : C.Input => C.publicCoin EF) (fun _ => C.decoder EF K (C.coinCount EF K))
      (fun _ => C.layout EF K (C.coinCount EF K)) tail (Bcs.snapshotAt w.2) (Bcs.answerAt w.2)
      initCap (C.inputOf vk pis hz) msgs) ()
  have hfs : C.fillSelection EF K w.2 (some ⟨C.inputOf vk pis hz, msgs, ()⟩) =
      some ⟨C.inputOf vk pis hz, fill (fun _ : C.Input => C.publicCoin EF)
        (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K))
        tail (Bcs.snapshotAt w.2) (Bcs.answerAt w.2) initCap (C.inputOf vk pis hz) msgs, ()⟩ :=
    rfl
  have hrepF : replay (Bcs.cacheOf w.2) (C.completionOf EF K (C.fillSelection EF K w.2
      (some ⟨C.inputOf vk pis hz, msgs, ()⟩))) = some (some ⟨C.inputOf vk pis hz, path, ()⟩) := by
    unfold completionOf realCompletion at hrepw ⊢
    unfold realCompletion at hrepP
    rw [replay_simulateQ_liftHash] at hrepw ⊢
    rw [hfs, squeezeCompletionAfter_fill, replay_map, hrepw]
    rw [squeezeCompletionAfter_fill, replay_map,
      replay_mono (chainPart_le_duplexCache w.2 dstar) _ _ hrepw] at hrepP
    exact hrepP
  rw [run_realImpl_of_replay _ _ _ hrepF, support_pure, Set.mem_singleton_iff] at ho
  subst ho
  -- the filled messages open as the parsed ones, on the final hash answers
  have hstable := opensStable_parse (C := C) hK w.2 hL2bad n proof msgs (by rw [hhash]; exact hmsgs)
    ∅ (tail (C.inputOf vk pis hz))
  have hfillP := openedPath_fill
    (fun r n => coinsOf ((List.range n).map (squeezeAnswer (logAnswer w.2 dstar) r.1 r.2)))
    (Bcs.snapshotAt w.2) (Bcs.answerAt w.2) (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
    (C.layout EF K (C.coinCount EF K)) true initCap ∅ ∅ [] (tail (C.inputOf vk pis hz)) [] msgs
    hstable (fun h => by cases h)
  have hdF := hdP.trans hfillP
  unfold parse at hmsgs
  obtain ⟨smsgs, hsp, rfl⟩ := Option.map_eq_some_iff.mp hmsgs
  have hs := (C.setup EF n).openedPath_parse (logAnswer w.2 dstar) hK le_rfl (Bcs.hashCacheOf L1)
    vk proof pis hn hok smsgs hsp
  have hd' := hdF.trans (map_eq_some_of (f := fun r => C.pathAt EF n r) hs rfl)
  obtain ⟨p, hp, hpo⟩ := Option.map_eq_some_iff.mp hd'
  -- the commitments bind the words extracted from the log, and the verifier's checks pass
  have hH : (idealOf (logAnswer w.2 dstar)).hash = logHash L1 dstar :=
    (idealOf_logAnswer_hash w.2 dstar).trans (by unfold logHash; rw [hhash])
  have hC : (idealOf (logAnswer w.2 dstar)).compress = logCompress L1 dstar :=
    (idealOf_logAnswer_compress w.2 dstar).trans (by unfold logCompress; rw [hhash])
  have hbind (cap : Cap F) (hc : ∀ d ∈ cap.toList, d ∈ capDigests vk proof) :=
    capBinding_of_log hL hd1 _ hH hC cap fun d hd h => hd2 (h ▸ hc d hd)
  have htrace := hbind proof.traceCommit fun d hd => by simp [capDigests, hd]
  have hquot := hbind proof.quotientCommit fun d hd => by simp [capDigests, hd]
  have hfri : ∀ c ∈ proof.fri.commits, Ni.CapBinding (merkleCache (Bcs.hashCacheOf L1))
      (idealOf (logAnswer w.2 dstar)) c := fun c hc => hbind c fun d hd => by
    simp only [capDigests, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨c, Array.mem_toList_iff.mpr hc, hd⟩)
  have hprepBind : ∀ k ∈ vk, Ni.CapBinding (merkleCache (Bcs.hashCacheOf L1))
      (idealOf (logAnswer w.2 dstar)) k.commit := fun k hk => hbind k.commit fun d hd => by
    simp only [capDigests, List.mem_append]
    exact Or.inr (by rw [show vk = some k from hk]; exact hd)
  have hprep : ∀ k ∈ vk, ∀ j < (C.setup EF n).air.preprocessedWidth,
      Ni.committedColumn (C.setup EF n) (merkleCache (Bcs.hashCacheOf L1)) k.commit j =
        (C.setup EF n).preprocessedWord j := fun k hk =>
    Ni.committedColumn_setup (C.setup EF n) _ (logAnswer w.2 dstar) k
      (by rw [C.preprocessedKeyWith_setupAt (EF := EF) _ n.1 n.2, ← hvk]; exact hk)
      (hprepBind k hk)
  have hterm := (C.setup EF n).terminal_of_verifyWith (merkleCache (Bcs.hashCacheOf L1)) _ vk
    proof pis hn htrace hquot hfri hprepBind hprep hok
  obtain ⟨wt, hwt⟩ := (C.setup EF n).terminal_holds_of_eval pis (δ n.1) (δ' n.1)
    (by rw [rate_setup]; exact hδ' n.1 n.2) (loss n) (C.setup EF n).queryPositions _ hterm
  refine ⟨C.inputOf vk pis hz, _, (), path, hfs, rfl, snapsOK_fill _ _ _ tail _ _ initCap _
    (C.layout_fills EF K (C.coinCount EF K)) _, p, hp, ?_⟩
  rw [hpo]
  obtain ⟨n1, hn1⟩ := n
  dsimp only at hn
  subst hn
  exact ⟨wt, hwt, fun hroot => hfar hn1 _ hroot.1 hroot.2⟩

variable (C EF K) in
/-- **Knowledge soundness of Plonky3's STARK verifier with Merkle commitments.** On a base field
of at least `2 ^ 8` elements with two-adicity below `2 ^ 64`, the game computes the verifying key
of the AIR's preprocessed trace on the verifier's random oracles (the duplex challenger with
squeezes of `K > 0` samples, the leaf hash and the compression), runs an adversary making at most
`Q` duplex calls and `q` oracle calls in all, which outputs public values and a proof, and runs
Plonky3's verifier on them, all against one logged lazy random oracle. The verifier accepts while
no trace of the proof's length within `δ' n` of the trace extracted from the log's hash answers
under the proof's trace commitment satisfies the AIR with the public values with probability at
most `chainError (Digest F) Q' + hashBadError F (2 ^ capHeight) |capOffsets| (q + verifierQueries)
+ maxError · Q' + sumError` of the node errors, each times its draw's ratio,
`Q' = Q + verifierQueries + 3 verifierChainQueries`: FRI tests proximity `δ n`, the extractor
list-decodes at `δ' n` below `1 - rate`, at proximity loss `loss n`, each query position `1/p`
more likely to land where the checks pass than a uniform one. -/
theorem knowledgeSoundness_bcs (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64)
    (hK : 0 < K) (δ δ' : ℕ → ℝ≥0) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) (adversary : OracleComp (spec F K) (List F × Proof F EF)) {Q q : ℕ}
    (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (C.starkGame EF K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧ ∀ h : C.Admits z.1.2.2.1.degreeBits,
        ∀ trace ∈ closeTraces (C.setupAt EF _ h) (δ' z.1.2.2.1.degreeBits)
          ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
            (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.traceCommit)),
        ¬ C.air.Satisfied z.1.2.2.1.degreeBits trace z.1.2.1] ≤
      chainError (Digest F) (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K) +
        hashBadError F (2 ^ C.params.capHeight) (C.capOffsets EF).length
          (q + C.verifierQueries EF) +
        (maxError (fun (_ : C.Input) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss (1 / Nat.card F) node) *
            (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K : ℕ) +
          sumError (fun (_ : C.Input) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss (1 / Nat.card F) node)) := by
  have hB : 0 < (C.capOffsets EF).length * 2 ^ C.params.capHeight := by
    rw [C.length_capOffsets EF]
    exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have hq2 : 2 ≤ q + C.verifierQueries EF := (C.two_le_verifierQueries EF).trans le_add_self
  have hgameq := isQueryBoundP_translate_isRight (isTotalQueryBound_starkGame (C := C) hq)
  by_cases hbig : Nat.card F ^ 8 ≤ 1 + (2 + (C.capOffsets EF).length * 2 ^ C.params.capHeight) *
      (q + C.verifierQueries EF) + (C.capOffsets EF).length * 2 ^ C.params.capHeight
  · refine (prEvent_le_one _).trans ((one_le_hashBadError F _ _ _ hq2 hbig).trans ?_)
    exact le_add_right (le_add_self)
  rw [not_le] at hbig
  have hHB := prEvent_hashBad_le (offs := C.capOffsets EF) (capLen := 2 ^ C.params.capHeight) hB
    _ _ hgameq
  have : NeZero (C.coinCount EF K) := ⟨fun h0 ↦ by
    have := le_squeezesFor_mul hK (Challenge.d EF + C.params.numQueries + 1)
    unfold coinCount at h0
    rw [h0, Nat.zero_mul] at this
    omega⟩
  have hbcs := KnowledgeCertificate.bcs_knowledge_soundness initCap (C.publicCoin EF)
    (C.decoder EF K (C.coinCount EF K)) (C.layout EF K (C.coinCount EF K)) (fun _ => C.ratio EF)
    (fun node => squeezes_le node) (reads_decoder _ hK) tail (tail_injective C)
    (layout_prefixFree (C := C) _ h8 h64) (fun z : C.Input => C.rootState EF z.1.2 δ')
    (fun z => certificate EF z.1.2 δ δ' hδ' loss fun n ↦ (C.setup EF n).queryPositions)
    (fun z => bounded_decoder hK z.1.2 δ δ' hδ' loss) (C.bcsAdversary EF K adversary)
    (N := maxChallenges (F := F)) (fun n ↦ (C.setup EF n).challengesLE_publicCoin)
    (isQueryBoundP_bcsAdversary hQ)
  have herr (z : C.Input) (node : Prefix PUnit (C.publicCoin EF)) :
      supErrors (C.publicCoin EF) (certificate EF z.1.2 δ δ' hδ' loss
        fun n ↦ (C.setup EF n).queryPositions).challenges node =
        C.nodeErrors EF δ δ' loss (1 / Nat.card F) node :=
    congrFun ((C.setup EF node.1).supErrors_certificate z.1.2 (δ node.1.1) (δ' node.1.1) _
      (loss node.1) _) node.2
  have hcount : Q + C.verifierQueries EF + C.verifierChainQueries EF K +
      2 * Bcs.completionQueries (maxChallenges (F := F)) (C.coinCount EF K) =
      Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K := by
    unfold verifierChainQueries Bcs.completionQueries
    ring
  simp only [herr] at hbcs
  rw [hcount] at hbcs
  refine (prEvent_le_and_not_add _ _ fun z => HashBad (C.capOffsets EF)
    (2 ^ C.params.capHeight) z.2).trans ?_
  refine (add_le_add_right hHB _).trans ?_
  rw [add_right_comm (chainError _ _)]
  refine add_le_add_left (le_trans ?_ hbcs) _
  rw [run_realExecution_bcsAdversary]
  refine prEvent_le_prEvent_bind_of_support _ _ _ _ fun x hx hE =>
    prEvent_eq_one_of_forall_mem_support _ _ fun y hy => ?_
  obtain ⟨⟨hacc, hfar⟩, hL⟩ := hE
  obtain ⟨w, hw, hy⟩ := (mem_support_bind_iff _ _ _).mp hy
  rw [support_map] at hy
  obtain ⟨o, ho, rfl⟩ := hy
  have hlen : x.2.length ≤ q + C.verifierQueries EF := by
    simpa using length_le_of_mem_support_realImpl _ hgameq [] x hx
  exact bcsEvent_of_mem_support (C := C) (EF := EF) (K := K) hK δ δ' hδ' loss adversary x hx
    hacc hfar hL (lt_of_le_of_lt (by gcongr) hbig) w hw o ho

end CompStark.Iop.Statement
