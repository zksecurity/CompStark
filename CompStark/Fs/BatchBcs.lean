/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.StarkBcs
public import CompStark.Fs.BatchStable
public import CompStark.Fs.BatchTerminal
public import CompStark.Fs.BatchFiatShamir
public import CompStark.Ni.BatchNatural
public import CompStark.Ni.BatchQueryBound
public import CompStark.Ni.BatchLengths

/-! # Knowledge soundness of Plonky3's batch STARK verifier with Merkle commitments

As for the STARK (`StarkBcs.lean`, whose logged-run lemmas are used here): the game
(`Statement.batchGame`) computes the batch's common data, the commitment to the instances'
preprocessed traces at their keygen heights, on the verifier's random oracles, runs an adversary
that outputs public values and a batch proof, and runs Plonky3's batch verifier on them, all
through `translate` against ArkLib's logged lazy oracle `Bcs.realImpl`.
`Statement.knowledgeSoundness_bcs` bounds the probability that the verifier accepts while no
tuple of traces of the proof's lengths close to the traces extracted from the log's hash answers
under the proof's main commitment satisfies the batch, by ArkLib's BCS theorem
(`KnowledgeCertificate.bcs_knowledge_soundness`) on the batch's snapshot protocol plus the
digest-clash bound `hashBadError`. The proof's lengths are told apart by the degree bits the
verifier observes, on every base field.

* `capBindingM_of_log`: without `HashBad`, accepted openings of matrices of mixed heights on the
  log's answers bind every entry of a cap that misses `dstar`.
* `Statement.bcsAdversary`: the BCS theorem's adversary runs the game with its own log, reads the
  proof's selection off it (`selectionOf`, `parse`), runs the duplex verifier's completion of it,
  and outputs the selection with its snapshots filled from its log.
* `Statement.bcsEvent_of_mem_support`: on a run without digest clashes where the verifier accepts
  while the extracted traces are far, the completions end in the BCS theorem's event: the filled
  selection opens to the proof's execution path (`Setup.proofPath`, `opensStable_parse`), whose
  commitments bind the words extracted from the log (`capDigests`), so the batch's terminal holds
  (`Setup.terminal_of_verifyWith`), while the far traces make the extraction fail.
-/

@[expose] public section

/-! ### Binding of caps of mixed heights from a log -/

namespace CompStark.Fs
open CompStark.Stark CompStark.RandomOracle OracleComp OracleSpec
open Interaction.Oracle.Security

variable {F : Type} [BaseField F] {K : ℕ} {offs : List ℕ} {capLen : ℕ}

/-- **Binding of a cap of mixed heights from a log.** Without digest clashes, accepted openings,
on primitives answering the leaf hashes and compressions as the log does and `dstar` outside the
log's digests otherwise, of matrices of heights `2 ^ j`, `c ≤ j ≤ top` for the cap's levels `c`,
some of height `2 ^ top`, bind every entry of a cap that misses `dstar`. -/
theorem capBindingM_of_log {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {dstar : Digest F} (hd : dstar ∉ logDigests offs capLen L) (H : Primitives F Id)
    (hH : H.hash = logHash L dstar) (hC : H.compress = logCompress L dstar) (cap : Cap F)
    (hcap : ∀ d ∈ cap.toList, d ≠ dstar) (capHeight top : ℕ) (hs : List ℕ)
    (hpow : ∀ h ∈ hs, ∃ j, min capHeight top ≤ j ∧ j ≤ top ∧ h = 2 ^ j) (htop : 2 ^ top ∈ hs) :
    Ni.CapBindingM (merkleCache (Bcs.hashCacheOf L)) H cap capHeight top hs := by
  intro e i values path hv
  have hroot : cap.toList.getD e 0 ≠ dstar := by
    rcases getD_cap cap.toList e with h0 | h0
    · rw [h0]
      exact fun h => hd (h ▸ initCap_mem_logDigests L)
    · exact hcap _ h0
  simp only [Ni.verifyBatchH, hH, hC] at hv
  refine extractGroup_of_logVerifyBatch hL hd hroot _ _ (fun h hh => ?_)
    (List.mem_map.mpr ⟨_, htop, by rw [Nat.pow_div (Nat.min_le_right _ _) (by decide)]⟩) i values
    path hv
  obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
  obtain ⟨j, hcj, hjL, rfl⟩ := hpow h' hh'
  exact ⟨j - min capHeight top, by omega, by rw [Nat.pow_div hcj (by decide)]⟩

end CompStark.Fs

/-! ### Sizes of the batch's commitments -/

namespace CompStark.Batch
open CompStark.Stark

variable {F : Type} [BaseField F]

/-- The commitment to the preprocessed traces on pure primitives has at most `2 ^ capHeight`
digests. -/
theorem size_preprocessedCapWith_le (H : Primitives F Id) (P : Fri.Params)
    (instances : List (Instance F)) (root : Cap F)
    (hr : preprocessedCapWith H P instances = some root) : root.size ≤ 2 ^ P.capHeight := by
  unfold preprocessedCapWith at hr
  split at hr
  · exact absurd hr (by simp)
  · have hr' : some ((List.range (2 ^ min P.capHeight (preprocessedLogHeight P instances))).mapM
        (injNodeWith H ((preprocessedMats P instances).map Mat.toMatrix)
          (preprocessedLogHeight P instances) (preprocessedLogHeight P instances -
            min P.capHeight (preprocessedLogHeight P instances)))).run.toArray = some root := hr
    rw [List.idRun_mapM] at hr'
    obtain rfl := Option.some.inj hr'
    rw [List.size_toArray, List.length_map, List.length_range]
    exact Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)

end CompStark.Batch

/-! ### The game and the adversary of the BCS theorem -/

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Fs CompStark.Ni CompStark.RandomOracle OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- The game on the verifier's oracles: the batch's common data, the adversary's public values
and batch proof, and Plonky3's batch verifier's verdict on them. -/
def batchGame
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF)) :
    OracleComp (spec F K) (CompStark.Batch.Common F × (Fin C.k → List F) ×
      CompStark.Batch.BatchProof F EF × Except String Unit) :=
  CompStark.Batch.commonWith (ideal F K) C.params C.keyInstances >>= fun common =>
    adversary >>= fun x =>
      CompStark.Batch.verifyBatchWith (ideal F K) C.params C.airs common x.2 (List.ofFn x.1) >>=
        fun v => pure (common, x.1, x.2, v)

/-- A selection of the snapshot protocol of the batch, with draws from `coinCount` squeezes. -/
abbrev BcsSelection : Type :=
  SnapSelection (hs := merkleSpec F) Unit (fun _ : C.Input => C.publicCoin EF)
    (fun _ => C.decoder EF K (C.coinCount EF K)) fun _ => C.layout EF K (C.coinCount EF K)

/-- The selection read off the game's outcome, every snapshot move `T`: the statement's input
of the public values and the common data and the proof's messages, if the proof's lengths are
admitted, the public values of the lengths the AIRs declare, and its messages readable
(`parse`). -/
noncomputable def selectionOf (T : (merkleSpec F).QueryCache)
    (out : CompStark.Batch.Common F × (Fin C.k → List F) × CompStark.Batch.BatchProof F EF ×
      Except String Unit) :
    C.BcsSelection EF K := by
  classical exact
    if h : C.Admits (C.lengthsOf out.2.2.1) ∧
        ∀ i, (out.2.1 i).length = (C.air i).numPublicValues
    then (C.parse EF K T ⟨_, h.1⟩ out.2.2.1).map fun msgs =>
      ⟨inputOf out.1 ⟨out.2.1, h.2⟩, msgs, ()⟩
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
oracles: the common data, the adversary, Plonky3's batch verifier. It reads the proof's selection
off the outcome and runs the duplex verifier's completion of it, so that the completion's chain
queries are logged, and outputs the selection with its snapshots filled from its log. -/
noncomputable def bcsAdversary
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF)) :
    OracleComp (unifSpec + sumSpec F K) (C.BcsSelection EF K) :=
  (simulateQ selfLog (simulateQ translate (C.batchGame EF K adversary))).run [] >>= fun x =>
    (simulateQ selfLog (C.completionOf EF K
      (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1))).run x.2 >>= fun y =>
      pure (C.fillSelection EF K y.2 (C.selectionOf EF K (Bcs.hashCacheOf x.2) x.1))

/-- The BCS theorem's real game on `bcsAdversary` is the game, then the completion the adversary
runs, then the real completion of the filled selection. -/
theorem run_realExecution_bcsAdversary
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF)) :
    (simulateQ Bcs.realImpl (realExecution initCap (fun _ : C.Input => C.publicCoin EF)
      (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K))
      tail (C.bcsAdversary EF K adversary))).run [] =
      (simulateQ Bcs.realImpl (simulateQ translate (C.batchGame EF K adversary))).run [] >>=
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

/-- The game makes at most the adversary's oracle calls and the setup's and the verifier's. -/
theorem isTotalQueryBound_batchGame
    {adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF)}
    {q : ℕ} (hq : IsTotalQueryBound adversary q) :
    IsTotalQueryBound (C.batchGame EF K adversary) (q + C.verifierQueries EF) := by
  refine (isTotalQueryBound_bind_of_mem_support (C.isTotalQueryBound_commonWith (K := K))
    fun common hc => isTotalQueryBound_bind hq fun x => isTotalQueryBound_bind (n₂ := 0)
      (C.isTotalQueryBound_verifyBatchWith common (C.lookups_of_mem_support_commonWith common hc)
        x.2 _) fun v =>
        (show IsTotalQueryBound (pure (common, x.1, x.2, v) : OracleComp (spec F K) _) 0
          from trivial)).mono ?_
  unfold verifierQueries
  omega

/-- The game makes at most the adversary's duplex calls and the setup's and the verifier's
oracle calls. -/
theorem isQueryBoundP_batchGame
    {adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF)}
    {Q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q) :
    IsQueryBoundP (C.batchGame EF K adversary) (fun t => isDuplex t = true)
      (Q + C.verifierQueries EF) := by
  refine (isQueryBoundP_bind (C.isTotalQueryBound_commonWith (K := K)).isQueryBoundP
    fun common hc => isQueryBoundP_bind hQ fun x _ => isQueryBoundP_bind (m := 0)
      (C.isTotalQueryBound_verifyBatchWith common (C.lookups_of_mem_support_commonWith common hc)
        x.2 _).isQueryBoundP fun v _ => isQueryBoundP_pure _ _ _).mono ?_
  unfold verifierQueries
  omega

/-- The adversary of the BCS theorem makes at most the adversary's duplex calls, the setup's
and the verifier's oracle calls, and the completion's chain queries. -/
theorem isQueryBoundP_bcsAdversary
    {adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF)}
    {Q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q) :
    IsQueryBoundP (C.bcsAdversary EF K adversary) (fun t => isChain t = true)
      (Q + C.verifierQueries EF + C.verifierChainQueries EF K) := by
  have hN : ∀ _ : C.Input, (C.publicCoin EF).ChallengesLE (maxChallenges (F := F)) :=
    fun _ n ↦ (C.setup EF n).challengesLE_publicCoin
  refine (isQueryBoundP_bind (isQueryBoundP_selfLog (isQueryBoundP_translate
    (isQueryBoundP_batchGame hQ)) []) fun x _ => isQueryBoundP_bind (m := 0)
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

/-- The game on fixed answers: the common data on them, the adversary's output, and the
verifier's verdict on them. -/
theorem evalWithAnswerFn_batchGame (ans : (q : Query F) → Answer K q)
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF)) :
    evalWithAnswerFn (QueryImpl.ofFn ans) (C.batchGame EF K adversary) =
      (CompStark.Batch.commonWith (idealOf ans) C.params C.keyInstances,
        (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).1,
        (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).2,
        CompStark.Batch.verifyBatchWith (idealOf ans) C.params C.airs
          (CompStark.Batch.commonWith (idealOf ans) C.params C.keyInstances)
          (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).2
          (List.ofFn (evalWithAnswerFn (QueryImpl.ofFn ans) adversary).1)) := by
  unfold evalWithAnswerFn batchGame
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_commonWith, simulateQ_verifyBatchWith]
  rfl

/-- The digests of a proof's commitments and of the common data's preprocessed commitment. -/
def capDigests (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF) :
    List (Digest F) :=
  proof.mainCommit.toList ++ proof.quotientCommit.toList ++
    (proof.permutationCommit.map Array.toList).getD [] ++
    proof.fri.commits.toList.flatMap Array.toList ++ (common.preprocessed.map Array.toList).getD []

/-- An accepted proof's commitments and the preprocessed commitment have at most `2 ^ capHeight`
digests each, and FRI's are at most `twoAdicity F`: at most `2 |capOffsets| 2 ^ capHeight`. -/
theorem length_capDigests_le (n : C.Length) (H : Primitives F Id)
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F))
    (h : CompStark.Batch.verifyInstancesWith H C.params (C.setup EF n).instances common proof
      pis = .ok ())
    (hprep : ∀ root ∈ common.preprocessed, root.size ≤ 2 ^ C.params.capHeight) :
    (capDigests common proof).length ≤ 2 * ((C.capOffsets EF).length * 2 ^ C.params.capHeight) := by
  have hle (h k : ℕ) : 2 ^ min h k ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
  obtain ⟨hmsz, hqsz, hpsz, -, hfsz⟩ :=
    (C.setup EF n).caps_of_verifyInstancesWith H common proof pis h
  obtain ⟨-, -, -, hcs, -⟩ :=
    shape_of_verifyInstancesWith (C.setup EF n) H common proof pis h
  have hc : ∀ c ∈ proof.fri.commits.toList, c.toList.length ≤ 2 ^ C.params.capHeight := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hi' : i < (C.setup EF n).friArities.length := by
      rw [Array.length_toList] at hi
      rw [← hcs]
      exact hi
    have := hfsz i hi'
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [Array.length_toList, this]
    exact hle _ _
  have hf := Iop.Statement.length_flatMap_le Array.toList (2 ^ C.params.capHeight)
    proof.fri.commits.toList hc
  have hp : ((proof.permutationCommit.map Array.toList).getD []).length ≤
      2 ^ C.params.capHeight := by
    cases hr : proof.permutationCommit with
    | none => exact Nat.zero_le _
    | some r =>
      simp only [Option.map_some, Option.getD_some, Array.length_toList]
      rw [hpsz r hr]
      exact hle _ _
  have hv : ((common.preprocessed.map Array.toList).getD []).length ≤ 2 ^ C.params.capHeight := by
    cases hr : common.preprocessed with
    | none => exact Nat.zero_le _
    | some r =>
      simp only [Option.map_some, Option.getD_some, Array.length_toList]
      exact hprep r hr
  have hcl : proof.fri.commits.toList.length ≤ twoAdicity F := by
    rw [Array.length_toList, hcs]
    exact (C.setup EF n).length_friArities_le
  have hmain : proof.mainCommit.size ≤ 2 ^ C.params.capHeight := hmsz ▸ hle _ _
  have hquot : proof.quotientCommit.size ≤ 2 ^ C.params.capHeight := hqsz ▸ hle _ _
  simp only [capDigests, List.length_append, Array.length_toList, C.length_capOffsets EF]
  have := Nat.mul_le_mul_right (2 ^ C.params.capHeight) hcl
  nlinarith

/-- **The deterministic core.** On a run of the game without digest clashes in which the verifier
accepts while no tuple of traces close to the ones extracted under the proof's main commitment
satisfies the batch at the proof's lengths, the completion the adversary of the BCS theorem runs,
then the real completion of its filled selection, end in the BCS theorem's event. -/
theorem bcsEvent_of_mem_support (hK : 0 < K) (δ δ' : (Fin C.k → ℕ) → ℝ≥0)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (loss : C.Length → ℝ≥0)
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF))
    (x : (CompStark.Batch.Common F × (Fin C.k → List F) × CompStark.Batch.BatchProof F EF ×
      Except String Unit) × QueryLog (sumSpec F K))
    (hx : x ∈ support ((simulateQ Bcs.realImpl
      (simulateQ translate (C.batchGame EF K adversary))).run []))
    (hacc : x.1.2.2.2 = .ok ())
    (hfar : ∀ h : C.Admits (C.lengthsOf x.1.2.2.1),
      ∀ traces ∈ closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf x.1.2.2.1))
        ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
          (merkleCache (Bcs.hashCacheOf x.2)) x.1.2.2.1.mainCommit)),
      ¬ (C.setupAt EF _ h).Satisfied traces x.1.2.1)
    (hL : ¬ HashBad (C.capOffsets EF) (2 ^ C.params.capHeight) x.2)
    (hlen : 1 + (2 + (C.capOffsets EF).length * 2 ^ C.params.capHeight) * x.2.length +
      2 * ((C.capOffsets EF).length * 2 ^ C.params.capHeight) < Nat.card F ^ 8)
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
        ∃ witness, ((certificate EF zz.1.1 δ δ' hδ' loss
            fun n ↦ (C.setup EF n).domainSetup.queryPositions).extractor.terminalState
              (openPath (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
                (C.layout EF K (C.coinCount EF K)) true ∅ p)).holds witness ∧
          ¬ (C.rootState EF zz.1.1 δ').holds ((certificate EF zz.1.1 δ δ' hδ' loss
            fun n ↦ (C.setup EF n).domainSetup.queryPositions).extractor.extractWitness
              (openPath (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
                (C.layout EF K (C.coinCount EF K)) true ∅ p) witness) := by
  obtain ⟨⟨common, pv, proof, verdict⟩, L1⟩ := x
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
      common = CompStark.Batch.commonWith (idealOf (logAnswer w.2 d)) C.params C.keyInstances ∧
        CompStark.Batch.verifyBatchWith (idealOf (logAnswer w.2 d)) C.params C.airs common proof
          (List.ofFn pv) = .ok () := by
    have h := heval d
    rw [evalWithAnswerFn_batchGame] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun y => y.2.1) h
    have h3 := congrArg (fun y => y.2.2.1) h
    have h4 := congrArg (fun y => y.2.2.2) h
    simp only at h1 h2 h3 h4
    rw [h1, h2, h3] at h4
    exact ⟨h1.symm, h4⟩
  have hlk (d : Digest F) : common.lookups = List.ofFn C.lookups := by
    rw [(hgame d).1]
    exact (C.commonWith_keyInstances _).2
  have hadm : C.Admits (C.lengthsOf proof) := by
    have h := (hgame initCap).2
    rw [(hgame initCap).1] at h
    exact C.admits_of_ok _ proof _ h
  set n : C.Length := ⟨_, hadm⟩ with hn
  -- the verifier checks the instances at the proof's lengths
  have hok' (d : Digest F) : CompStark.Batch.verifyInstancesWith (idealOf (logAnswer w.2 d))
      C.params (C.setup EF n).instances common proof (List.ofFn pv) = .ok () := by
    have h := (hgame d).2
    have hkey := keyOk_of_ok _ _ _ _ _ _ h
    rw [CompStark.Batch.verifyBatchWith_of_keyOk _ _ _ _ _ _ hkey, C.instancesOf_eq common (hlk d)
      proof (C.length_degreeBits_of_keyOk common proof hkey)] at h
    exact h
  have hpl : ∀ i, (pv i).length = (C.air i).numPublicValues := by
    obtain ⟨-, -, -, -, -, -, hpub, -⟩ := verifyInstancesWith_ok _ _ _ _ _ _ (hok' initCap)
    intro i
    have hz : (i : ℕ) < ((C.setup EF n).instances.zip (List.ofFn pv)).length := by
      simp only [Iop.Batch.Setup.instances, List.length_zip, List.length_ofFn]
      exact lt_min i.isLt i.isLt
    have := hpub _ (List.getElem_mem hz)
    simp only [List.getElem_zip, Iop.Batch.Setup.instances, List.getElem_ofFn] at this
    exact this
  set pis : C.PublicValues := ⟨pv, hpl⟩ with hpis
  obtain ⟨msgs, hmsgs⟩ := Option.isSome_iff_exists.mp (isSome_parse (C := C) K
    (Bcs.hashCacheOf L1) (idealOf (logAnswer w.2 initCap)) n common proof (List.ofFn pv)
    (hok' initCap))
  have hsel : C.selectionOf EF K (Bcs.hashCacheOf L1) (common, pv, proof, .ok ()) =
      some ⟨inputOf common pis, msgs, ()⟩ := by
    unfold selectionOf
    rw [dite_eq_left_of_eq_true (eq_true ⟨hadm, hpl⟩)]
    exact congrArg (Option.map _) hmsgs
  -- a digest outside the log's digests and the commitments' digests
  have hprepSize : ∀ root ∈ common.preprocessed, root.size ≤ 2 ^ C.params.capHeight :=
    fun root hr => CompStark.Batch.size_preprocessedCapWith_le (idealOf (logAnswer w.2 initCap))
      C.params C.keyInstances root (by rw [(hgame initCap).1] at hr; exact hr)
  have hD := length_capDigests_le n _ common proof _ (hok' initCap) hprepSize
  obtain ⟨dstar, hd1, hd2⟩ := exists_not_mem_logDigests_append
    (offs := C.capOffsets EF) (capLen := 2 ^ C.params.capHeight) (by
      rw [C.length_capOffsets EF]; exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)) L1
    (capDigests common proof) (by omega)
  have hok := hok' dstar
  have hcommon := (hgame dstar).1
  rw [hsel] at hrepw ho ⊢
  -- the real completion of the filled messages, on the duplex answers
  obtain ⟨path, hrepP, hdP⟩ := replay_realCompletion initCap (fun _ : C.Input => C.publicCoin EF)
    (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K)) tail
    (duplexCache (logAnswer w.2 dstar)) (squeezeAnswer (logAnswer w.2 dstar))
    (replay_squeezeAt (logAnswer w.2 dstar)) (inputOf common pis)
    (fill (fun _ : C.Input => C.publicCoin EF) (fun _ => C.decoder EF K (C.coinCount EF K))
      (fun _ => C.layout EF K (C.coinCount EF K)) tail (Bcs.snapshotAt w.2) (Bcs.answerAt w.2)
      initCap (inputOf common pis) msgs) ()
  have hfs : C.fillSelection EF K w.2 (some ⟨inputOf common pis, msgs, ()⟩) =
      some ⟨inputOf common pis, fill (fun _ : C.Input => C.publicCoin EF)
        (fun _ => C.decoder EF K (C.coinCount EF K)) (fun _ => C.layout EF K (C.coinCount EF K))
        tail (Bcs.snapshotAt w.2) (Bcs.answerAt w.2) initCap (inputOf common pis) msgs, ()⟩ :=
    rfl
  have hrepF : replay (Bcs.cacheOf w.2) (C.completionOf EF K (C.fillSelection EF K w.2
      (some ⟨inputOf common pis, msgs, ()⟩))) = some (some ⟨inputOf common pis, path, ()⟩) := by
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
  have hstable := opensStable_parse (C := C) hK w.2 hL2bad n proof msgs
    (by rw [hhash]; exact hmsgs) ∅ (tail (inputOf common pis))
  have hfillP := openedPath_fill
    (fun r n => coinsOf ((List.range n).map (squeezeAnswer (logAnswer w.2 dstar) r.1 r.2)))
    (Bcs.snapshotAt w.2) (Bcs.answerAt w.2) (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
    (C.layout EF K (C.coinCount EF K)) true initCap ∅ ∅ [] (tail (inputOf common pis)) [] msgs
    hstable (fun h => by cases h)
  have hdF := hdP.trans hfillP
  unfold parse at hmsgs
  obtain ⟨smsgs, hsp, rfl⟩ := Option.map_eq_some_iff.mp hmsgs
  obtain ⟨-, -, hprepIs, -, -, -, -, -, -, -, hperm⟩ :=
    shape_of_verifyInstancesWith (C.setup EF n) _ common proof _ hok
  have hs := (C.setup EF n).openedPath_parse (logAnswer w.2 dstar) hK le_rfl (Bcs.hashCacheOf L1)
    common proof (List.ofFn pv) hok smsgs hsp
  rw [seed_eq n common hprepIs] at hs
  have hd' := hdF.trans (map_eq_some_of (f := fun r => C.pathAt EF n r) hs rfl)
  obtain ⟨p, hp, hpo⟩ := Option.map_eq_some_iff.mp hd'
  -- the commitments bind the words extracted from the log, and the verifier's checks pass
  have hH : (idealOf (logAnswer w.2 dstar)).hash = logHash L1 dstar :=
    (idealOf_logAnswer_hash w.2 dstar).trans (by unfold logHash; rw [hhash])
  have hC : (idealOf (logAnswer w.2 dstar)).compress = logCompress L1 dstar :=
    (idealOf_logAnswer_compress w.2 dstar).trans (by unfold logCompress; rw [hhash])
  have hne (cap : Cap F) (hc : ∀ d ∈ cap.toList, d ∈ capDigests common proof) :
      ∀ d ∈ cap.toList, d ≠ dstar := fun d hd h => hd2 (h ▸ hc d hd)
  obtain ⟨-, -, hpsz, hfit, -⟩ :=
    (C.setup EF n).caps_of_verifyInstancesWith _ common proof _ hok
  have hfit' : ∀ i, min C.params.capHeight (C.setup EF n).logTop ≤
      (C.setup EF n).logN i + C.params.logBlowup := hfit
  have hmain : CapBindingM (merkleCache (Bcs.hashCacheOf L1)) (idealOf (logAnswer w.2 dstar))
      proof.mainCommit C.params.capHeight (C.setup EF n).logTop (C.setup EF n).mainHeights := by
    refine capBindingM_of_log hL hd1 _ hH hC _ (hne _ fun d hd => by simp [capDigests, hd]) _ _ _
      (fun h hh => ?_) (List.mem_ofFn.mpr ⟨(C.setup EF n).top, rfl⟩)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hh
    exact ⟨_, hfit i, logTop_ge _ i, rfl⟩
  have hquot : CapBindingM (merkleCache (Bcs.hashCacheOf L1)) (idealOf (logAnswer w.2 dstar))
      proof.quotientCommit C.params.capHeight (C.setup EF n).logTop
      (quotHeights (C.setup EF n)) := by
    refine capBindingM_of_log hL hd1 _ hH hC _ (hne _ fun d hd => by simp [capDigests, hd]) _ _ _
      (fun h hh => ?_) (List.mem_flatMap.mpr ⟨(C.setup EF n).top, List.mem_finRange _,
        List.mem_replicate.mpr ⟨(Nat.two_pow_pos _).ne', rfl⟩⟩)
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hh
    exact ⟨_, hfit i, logTop_ge _ i, List.eq_of_mem_replicate hi⟩
  have hfri : ∀ c ∈ proof.fri.commits, CapBinding (merkleCache (Bcs.hashCacheOf L1))
      (idealOf (logAnswer w.2 dstar)) c := fun c hc =>
    capBinding_of_log hL hd1 _ hH hC c (hne _ fun d hd => by
      simp only [capDigests, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨c, Array.mem_toList_iff.mpr hc, hd⟩))
  have hprepBind : ∀ root ∈ common.preprocessed,
      CapBindingM (merkleCache (Bcs.hashCacheOf L1)) (idealOf (logAnswer w.2 dstar)) root
        C.params.capHeight (prepLog (C.setup EF n)) (prepHeights (C.setup EF n)) := by
    intro root hr
    obtain ⟨i, hi⟩ : ∃ i : Fin C.k, 0 < (C.air i).preprocessedWidth := by
      rw [show common.preprocessed.isSome = true by rw [Option.isSome_iff_exists]; exact ⟨_, hr⟩]
        at hprepIs
      obtain ⟨I, hI, hp⟩ := List.any_eq_true.mp hprepIs.symm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
      exact ⟨i, decide_eq_true_iff.mp hp⟩
    refine capBindingM_of_log hL hd1 _ hH hC _ (hne _ fun d hd => by
      simp only [capDigests, List.mem_append]
      exact Or.inr (by rw [show common.preprocessed = some root from hr]; exact hd)) _
      (prepLog (C.setup EF n)) (prepHeights (C.setup EF n)) (fun h hh => ?_) ?_
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hh
      have hp' : 0 < ((C.setup EF n).air i').preprocessedWidth := by
        simpa using (List.mem_filter.mp hi').2
      refine ⟨_, ?_, le_prepLog (C.setup EF n) i' hp', rfl⟩
      show min C.params.capHeight (prepLog (C.setup EF n)) ≤
        (C.setup EF n).logN i' + C.params.logBlowup
      have := prepLog_le (C.setup EF n)
      have := hfit' i'
      omega
    · rcases foldl_max_mem ((prepInsts (C.setup EF n)).map fun i ↦
          (C.setup EF n).logN i + C.params.logBlowup) 0 with h | h
      · have : prepLog (C.setup EF n) = 0 := h
        have := le_prepLog (C.setup EF n) i hi
        have := ((C.setup EF n).valid i).blowup
        omega
      · obtain ⟨i', hi', he⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨i', hi', congrArg (2 ^ ·) he⟩
  have hprep : ∀ root ∈ common.preprocessed, ∀ i : Fin C.k,
      0 < ((C.setup EF n).air i).preprocessedWidth →
      ∀ j < ((C.setup EF n).air i).preprocessedWidth,
      ∀ r < 2 ^ ((C.setup EF n).logN i + C.params.logBlowup),
        Merkle.matColumnCap (merkleCache (Bcs.hashCacheOf L1)) root.toList C.params.capHeight
          (prepLog (C.setup EF n)) (prepHeights (C.setup EF n)) (prepWidths (C.setup EF n))
          (prepIndex (C.setup EF n) i) j ((C.setup EF n).logN i + C.params.logBlowup) r =
        ((C.setup EF n).instanceSetup i).preprocessedWord j
          (finMod _ (reverseBits r ((C.setup EF n).logN i + C.params.logBlowup))) := by
    intro root hr i hp j hj r hrr
    have hroot : CompStark.Batch.preprocessedCapWith (idealOf (logAnswer w.2 dstar))
        (C.setup EF n).params (C.setup EF n).instances = some root := by
      rw [← preprocessed_commonWith (C.setup EF n) (logAnswer w.2 dstar)]
      rw [hcommon] at hr
      exact hr
    refine matColumn_setup (C.setup EF n) _ (logAnswer w.2 dstar) root hroot (hprepBind root hr)
      (fun i' _ ↦ ?_) i hp j hj r hrr
    show min C.params.capHeight (prepLog (C.setup EF n)) ≤
      (C.setup EF n).logN i' + C.params.logBlowup
    have := prepLog_le (C.setup EF n)
    have := hfit' i'
    omega
  have hpermBind : ∀ root ∈ proof.permutationCommit,
      CapBindingM (merkleCache (Bcs.hashCacheOf L1)) (idealOf (logAnswer w.2 dstar)) root
        C.params.capHeight (permLog (C.setup EF n)) (permHeights (C.setup EF n)) := by
    intro root hr
    have hl : (C.setup EF n).hasLookups = true :=
      hperm.symm.trans (Option.isSome_iff_exists.mpr ⟨_, hr⟩)
    obtain ⟨i, hi⟩ : ∃ i : Fin C.k, ((C.setup EF n).lookups i).isEmpty = false := by
      obtain ⟨I, hI, hp⟩ := List.any_eq_true.mp hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
      refine ⟨i, ?_⟩
      rw [lookups_eq]
      simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using hp
    have hpi : i ∈ permInsts (C.setup EF n) :=
      List.mem_filter.mpr ⟨List.mem_finRange _, by rw [hi]; rfl⟩
    have hrd : ∀ d ∈ root.toList, d ∈ capDigests common proof := fun d hd => by
      simp only [capDigests, List.mem_append]
      refine Or.inl (Or.inl (Or.inr ?_))
      rw [show proof.permutationCommit = some root from hr]
      exact hd
    refine capBindingM_of_log hL hd1 _ hH hC _ (hne _ hrd) _ (permLog (C.setup EF n))
      (permHeights (C.setup EF n)) (fun h hh => ?_) ?_
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hh
      refine ⟨_, ?_, (le_foldl_max _ 0).2 _ (List.mem_map.mpr ⟨i', hi', rfl⟩), rfl⟩
      show min C.params.capHeight (permLog (C.setup EF n)) ≤
        (C.setup EF n).logN i' + C.params.logBlowup
      have := permLog_le (C.setup EF n)
      have := hfit' i'
      omega
    · rcases foldl_max_mem ((permInsts (C.setup EF n)).map fun i ↦
          (C.setup EF n).logN i + C.params.logBlowup) 0 with h | h
      · have h0 : permLog (C.setup EF n) = 0 := h
        have := (le_foldl_max ((permInsts (C.setup EF n)).map fun i ↦
          (C.setup EF n).logN i + C.params.logBlowup) 0).2 _ (List.mem_map.mpr ⟨i, hpi, rfl⟩)
        have : 0 < C.params.logBlowup := ((C.setup EF n).valid i).blowup
        rw [permLog] at h0
        omega
      · obtain ⟨i', hi', he⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨i', hi', congrArg (2 ^ ·) he⟩
  have hterm := (C.setup EF n).terminal_of_verifyWith (merkleCache (Bcs.hashCacheOf L1)) _ common
    proof pv hmain hquot hfri hprepBind hprep hpermBind hok
  obtain ⟨wt, hwt⟩ := (C.setup EF n).terminal_holds_of_eval pv (δ n.1) (δ' n.1) (hδ' n.1 n.2)
    (loss n) (C.setup EF n).domainSetup.queryPositions _ hterm
  refine ⟨inputOf common pis, _, (), path, hfs, rfl, snapsOK_fill _ _ _ tail _ _ initCap _
    (C.layout_fills EF K (C.coinCount EF K)) _, p, hp, ?_⟩
  rw [hpo]
  exact ⟨wt, hwt, fun hroot => hfar hadm _ hroot.1 hroot.2⟩

variable (C EF) in
/-- The setup and the verifier make at least two oracle calls. -/
theorem two_le_verifierQueries : 2 ≤ C.verifierQueries EF := by
  have h := Ni.le_foldr_max ((lengthVectors C.k (twoAdicity F)).map fun n ↦
    CompStark.Batch.verifierCallsOf EF C.params (C.instancesAt n))
    (CompStark.Batch.verifierCallsOf EF C.params (C.instancesAt fun _ ↦ 0))
    (List.mem_map.mpr ⟨_, mem_lengthVectors C.k _ _ fun _ ↦ Nat.zero_le _, rfl⟩)
  have h3 : 3 ≤ CompStark.Batch.verifierCallsOf EF C.params (C.instancesAt fun _ ↦ 0) := by
    unfold CompStark.Batch.verifierCallsOf
    dsimp only
    omega
  unfold verifierQueries verifierCalls
  omega

variable (C EF K) in
/-- **Knowledge soundness of Plonky3's batch STARK verifier with Merkle commitments.** The game
computes the batch's common data, the commitment to the instances' preprocessed traces at their
keygen heights, on the verifier's random oracles (the duplex challenger with squeezes of `K > 0`
samples, the leaf hash and the compression), runs an adversary making at most `Q` duplex calls and
`q` oracle calls in all, which outputs public values and a batch proof, and runs Plonky3's batch
verifier on them, all against one logged lazy random oracle. The verifier accepts while no tuple
of traces of the proof's lengths `n`, each within `δ' n` of the trace extracted from the log's
hash answers under the proof's main commitment, satisfies the batch with the public values with
probability at most `chainError (Digest F) Q' + hashBadError F (2 ^ capHeight) |capOffsets|
(q + verifierQueries) + maxError · Q' + sumError` of the node errors, each times its draw's ratio,
`Q' = Q + verifierQueries + 3 verifierChainQueries`: FRI tests proximity `δ n`, the extractor
list-decodes at `δ' n` below `1 - rate`, at proximity loss `loss n`, each query position `1/p`
more likely to land where the checks pass than a uniform one. -/
theorem knowledgeSoundness_bcs (hK : 0 < K) (δ δ' : (Fin C.k → ℕ) → ℝ≥0)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (loss : C.Length → ℝ≥0)
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF))
    {Q q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (C.batchGame EF K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧ ∀ h : C.Admits (C.lengthsOf z.1.2.2.1),
        ∀ traces ∈ closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf z.1.2.2.1))
          ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
            (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.mainCommit)),
        ¬ (C.setupAt EF _ h).Satisfied traces z.1.2.1] ≤
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
  have hgameq := isQueryBoundP_translate_isRight (isTotalQueryBound_batchGame (C := C) hq)
  by_cases hbig : Nat.card F ^ 8 ≤ 1 + (2 + (C.capOffsets EF).length * 2 ^ C.params.capHeight) *
      (q + C.verifierQueries EF) + 2 * ((C.capOffsets EF).length * 2 ^ C.params.capHeight)
  · refine (prEvent_le_one _).trans ((one_le_hashBadError F _ _ _ hq2 hbig).trans ?_)
    exact le_add_right (le_add_self)
  rw [not_le] at hbig
  have hHB := prEvent_hashBad_le (offs := C.capOffsets EF) (capLen := 2 ^ C.params.capHeight) hB
    _ _ hgameq
  have : NeZero (C.coinCount EF K) := ⟨fun h0 ↦ by
    have := le_squeezesFor_mul hK (2 * Challenge.d EF + C.params.numQueries + 1)
    unfold coinCount at h0
    rw [h0, Nat.zero_mul] at this
    omega⟩
  have hbcs := KnowledgeCertificate.bcs_knowledge_soundness initCap (C.publicCoin EF)
    (C.decoder EF K (C.coinCount EF K)) (C.layout EF K (C.coinCount EF K)) (fun _ => C.ratio EF)
    (fun node => squeezes_le node) (reads_decoder _ hK) tail (tail_injective C)
    (layout_prefixFree (C := C) _) (fun z : C.Input => C.rootState EF z.1.1 δ')
    (fun z => certificate EF z.1.1 δ δ' hδ' loss
      fun n ↦ (C.setup EF n).domainSetup.queryPositions)
    (fun z => bounded_decoder hK z.1.1 δ δ' hδ' loss) (C.bcsAdversary EF K adversary)
    (N := maxChallenges (F := F)) (fun n ↦ (C.setup EF n).challengesLE_publicCoin)
    (isQueryBoundP_bcsAdversary hQ)
  have hle (z : C.Input) (node : Prefix PUnit (C.publicCoin EF)) :
      C.ratio EF node * supErrors (C.publicCoin EF) (certificate EF z.1.1 δ δ' hδ' loss
        fun n ↦ (C.setup EF n).domainSetup.queryPositions).challenges node ≤
        C.ratio EF node * C.nodeErrors EF δ δ' loss (1 / Nat.card F) node :=
    mul_le_mul_right ((C.setup EF node.1).supErrors_certificate_le z.1.1 (δ node.1.1)
      (δ' node.1.1) _ (loss node.1) _ node.2) _
  have hcount : Q + C.verifierQueries EF + C.verifierChainQueries EF K +
      2 * Bcs.completionQueries (maxChallenges (F := F)) (C.coinCount EF K) =
      Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K := by
    unfold verifierChainQueries Bcs.completionQueries
    ring
  rw [hcount] at hbcs
  refine (prEvent_le_and_not_add _ _ fun z => HashBad (C.capOffsets EF)
    (2 ^ C.params.capHeight) z.2).trans ?_
  refine (add_le_add_right hHB _).trans ?_
  rw [add_right_comm (chainError _ _)]
  refine add_le_add_left (le_trans ?_ (hbcs.trans (add_le_add le_rfl (add_le_add
    (mul_le_mul_left (maxError_mono hle) _) (sumError_mono hle))))) _
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

end CompStark.Iop.Batch.Statement
