/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchRoundBounds
public import CompStark.Ni.BatchExtracted
public import CompStark.Ni.BatchAccepted
public import CompStark.Ni.BatchSetup
public import CompStark.Ni.BadQuery

/-! # An accepted batch proof the extractor cannot open makes a bad query

The deterministic half of the Fiat–Shamir argument for the batch STARK (`exists_badAtB`), as for
the STARK (`Ni/BadQuery.lean`): run the batch setup, a prover and then the batch verifier against
one answer table. If the verifier accepts and no tuple of traces close to the traces extracted
from the prover's queries satisfies every AIR, some query of the run is fresh and its answer
clashes with a known digest (`Clash`) or makes its round bad (`RoundBadB`).

Suppose not. Then the rounds of the proof's schedule are first queried in order and parse to the
proof's prefixes, so no round is bad for its prefix transcript; every cap is among the digests its
round binds (`boundDigestsB`), FRI's first commitment in the window ending before its grinding
witness and the others at the start of their windows, at the sizes the verifier clamps them to
(`size_capsB`); extraction under the digests the rounds bind is stable, so the prefix transcripts
are the run's, which `bcsB` extracts (`extractB_eq_prefixTranscriptB`); on answers changed outside
the run the commitments bind, at mixed heights for the main, quotient and preprocessed commitments
(`bindingM_fresh`), and the setup's commitment holds the preprocessed traces (`matColumn_setup`), so
`bcsB` gives the terminal lemma's checks, and with every round safe some tuple of candidate traces
satisfies every AIR (`Sound.Batch.exists_satisfied_of_safe`), a contradiction.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial OracleSpec OracleComp FriGame

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Folds past the last -/

theorem foldFails_of_le {K : Type} [Field K] [DecidableEq K] (d : ℕ) (θ loss : ℝ) (β : K) :
    ∀ (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) (j : ℕ) {n : ℕ}
      (ω : Domain.SmoothCosetFftDomain n K) (r : Rounds K n), r.numFolds ≤ j →
      ¬ Rounds.FoldFails d θ loss β words j ω r
  | _, _, _, _, .final, _ => fun h ↦ h
  | _, 0, _, _, .fold _ _ _ _, h => absurd h (by simp only [Rounds.numFolds]; omega)
  | words, j + 1, _, ω, .fold k _ none rest, h => by
    exact foldFails_of_le d θ loss β _ j _ rest (by simp only [Rounds.numFolds] at h; omega)
  | words, j + 1, _, ω, .fold k _ (some _) rest, h => by
    exact foldFails_of_le d θ loss β _ j _ rest (by simp only [Rounds.numFolds] at h; omega)

theorem length_friArities (S : Iop.Batch.Setup EF) :
    S.friArities.length = S.friRounds.numFolds := by
  rw [Iop.Batch.Setup.friArities, Nat.add_comm S.params.logBlowup, ← FriRounds.arities_schedule _ _
    (fun _ _ ↦ (0 : 𝕂)), FriRounds.length_arities]
  rfl

/-! ### The prefix transcript of all rounds -/

section Congr
variable (S : Iop.Batch.Setup EF) {cache cache' : Merkle.Cache F (Digest F)}
  {block block' : ℕ → List F} {sample sample' : ℕ → Vector F S.streamLen}

/-- The prefix transcript of all rounds depends on their inputs and answers, and on the rows
extracted under the observed digests. -/
theorem prefixTranscriptB_congr
    (hb : ∀ k ≤ lookupRounds S + 3 + S.friArities.length, block k = block' k)
    (hs : ∀ k < lookupRounds S + 3 + S.friArities.length, sample k = sample' k)
    (htrace : CapSameUnderM cache cache'
      (capFrom (block' 0) (mainOffsetB S) (2 ^ min S.params.capHeight S.logTop)))
    (hperm : S.hasLookups = true → CapSameUnderM cache cache'
      (capFrom (block' (lookupRounds S)) 0 (2 ^ min S.params.capHeight (permLog S))))
    (hquot : CapSameUnderM cache cache'
      (capFrom (block' (lookupRounds S + 1)) 0 (2 ^ min S.params.capHeight S.logTop)))
    (hfri : ∀ f < S.friArities.length, CapSameUnder cache cache'
      (capFrom (block' (lookupRounds S + 3 + f)) (friOffsetB S f)
        (2 ^ min S.params.capHeight (friDepthB S f)))) :
    prefixTranscriptB S cache block sample = prefixTranscriptB S cache' block' sample' := by
  rw [prefixTranscriptB_sample_congr S cache block hs]
  refine transcript_ext S (prefixTranscriptB_trace S (hb 0 (by omega)) htrace) rfl rfl
    (prefixTranscriptB_perm S (hb _ (by omega)) hperm) ?_ rfl
    (prefixTranscriptB_quotient S (hb _ (by omega)) hquot) rfl ?_ rfl ?_ ?_ rfl
  · funext i
    show (if (S.lookups i).isEmpty then 0 else Challenge.toSpec (extFrom (EF := EF)
        ((block (lookupRounds S)).drop (8 * 2 ^ min S.params.capHeight (permLog S)))
          (terminalIndex S i))) =
      (if (S.lookups i).isEmpty then 0 else Challenge.toSpec (extFrom (EF := EF)
        ((block' (lookupRounds S)).drop (8 * 2 ^ min S.params.capHeight (permLog S)))
          (terminalIndex S i)))
    rw [hb _ (by omega)]
  · show openingsAtB S ((block (lookupRounds S + 2)).drop (pcsSeedB S).length) =
      openingsAtB S ((block' (lookupRounds S + 2)).drop (pcsSeedB S).length)
    rw [hb _ (by omega)]
  · funext f
    by_cases hf : f < S.friArities.length
    · exact prefixTranscriptB_words S f (hb _ (by omega)) (hfri f hf)
    · funext m z
      show (if f < S.friArities.length then _ else 0) =
        (if f < S.friArities.length then _ else 0)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hf), ite_eq_right_of_eq_false _ _ (eq_false hf)]
  · show finalPoly S.domainSetup (finalPolyAt S.domainSetup
        ((block (lookupRounds S + 3 + S.friArities.length)).drop
          (friOffsetB S S.friArities.length))) =
      finalPoly S.domainSetup (finalPolyAt S.domainSetup
        ((block' (lookupRounds S + 3 + S.friArities.length)).drop
          (friOffsetB S S.friArities.length)))
    rw [hb _ le_rfl]

end Congr

/-! ### The bad query -/

section Bad
variable (S : Iop.Batch.Setup EF) (publicValues : Fin S.k → List F) (δ δ' loss : NNReal)

/-- Query `p` of `log` is fresh, and its answer clashes with a known digest or makes its batch
round bad. -/
def BadAtB (log : QueryLog (spec F S.streamLen)) (p : Nat) (hp : p < log.length) : Prop :=
  log[p].1 ∉ (log.take p).map Sigma.fst ∧
    (Clash (boundDigestsB S) (log.take p) log[p].1 log[p].2 ∨
      RoundBadB S publicValues δ δ' loss (log.take p) log[p].1 log[p].2)

/-- **The bad query.** If the batch verifier, run after the setup and a prover whose queries
`log` an answer table answers, accepts a proof against the setup's common data `common`, and no
tuple of traces close to the traces committed in `log` satisfies the batch, then some query of the
run is fresh and clashes or is round-bad. -/
theorem exists_badAtB (hδ' : (δ' : ℝ) < 1 - S.rate)
    (answer : (q : Query F) → Answer S.streamLen q) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (log : QueryLog (spec F S.streamLen))
    (hcons : Consistent answer log)
    (hcommon : CompStark.Batch.commonWith (idealOf answer) S.params S.keyInstances = common)
    (hsetup : ∀ e ∈ tableQueryLog S.setupRo answer, e ∈ log)
    (hok : CompStark.Batch.verifyInstancesWith (idealOf answer) S.params S.instances common proof
      (List.ofFn publicValues) = .ok ())
    (hsmall : (2 ^ (S.params.capHeight + 1) + 2) * (log ++ tableQueryLog
      (CompStark.Batch.verifyInstancesWith (ideal F S.streamLen) S.params S.instances common proof
        (List.ofFn publicValues)) answer).length < Fintype.card (Digest F))
    (hfail : ∀ traces ∈ Iop.Batch.closeTraces S δ' (Iop.Batch.committedTraces S log proof),
      ¬ S.Satisfied traces publicValues) :
    ∃ p hp, BadAtB S publicValues δ δ' loss (log ++ tableQueryLog
      (CompStark.Batch.verifyInstancesWith (ideal F S.streamLen) S.params S.instances common proof
        (List.ofFn publicValues)) answer) p hp := by
  set pis := List.ofFn publicValues with hpis
  set vlog := tableQueryLog (CompStark.Batch.verifyInstancesWith (ideal F S.streamLen) S.params
    S.instances common proof pis) answer with hvlog
  set L := log ++ vlog with hL
  by_contra hno
  have hconsL : Consistent answer L := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hcons e h
    · exact consistent_tableQueryLog _ e h
  have hclash : NoClash (boundDigestsB S) L :=
    fun p hp hfresh hc ↦ hno ⟨p, hp, hfresh, Or.inl hc⟩
  have hround : ∀ t ∈ L.map Sigma.fst,
      ¬ RoundBadB S publicValues δ δ' loss (L.take (idx L t)) t (answer t) :=
    fun t ht ↦ of_first hconsL (fun pre t u ↦ ¬ RoundBadB S publicValues δ δ' loss pre t u)
      (fun p hp hfresh hr ↦ hno ⟨p, hp, hfresh, Or.inr hr⟩) ht
  set nf := S.friArities.length with hnf
  set blocks := inputsB S common pis proof with hblocks
  have hz := length_zip_commitsB S (idealOf answer) common proof pis hok
  have hlen : blocks.length = lookupRounds S + 4 + nf := by
    rw [hblocks, length_inputsB, hz]
  have hkeys : ∀ j < blocks.length, keyAt answer blocks j ∈ L.map Sigma.fst := fun j hj ↦ by
    rw [List.map_append]
    exact List.mem_append_right _
      (hasRounds_verifyInstancesWith S answer common proof pis hok j hj)
  have hinjL : CapsInjective answer L := capsInjective hconsL hclash L fun t ht ↦ ht
  have hcap : ∀ j, j < blocks.length → capAt answer blocks (j + 1) ≠ initCap :=
    fun j hj ↦ capAt_ne_initCap hinjL (fun k hk ↦ hkeys k hk) j hj
  -- the caps the rounds bind
  obtain ⟨-, -, -, -, -, -, -, -, -, hlkA, -, -, -, -, ⟨stA, hfriA⟩, -⟩ :=
    verifyInstancesWith_ok (idealOf answer) S.params S.instances common proof pis hok
  obtain ⟨-, hpermA, hpne⟩ := lookupShapeOk_spec S.params S.instances proof hlkA
  have hqne := size_quotientCommit_neB _ _ _ _ _ _ hok
  have hcne := size_commits_ne _ _ _ _ _ _ _ hfriA
  obtain ⟨hmsz, hqsz, hpsz, hfit, hfsz⟩ := size_capsB S answer hok
  have hinit0 : initCap ∈ keyDigests (boundDigestsB S) (keyAt answer blocks 0) := by
    simp only [keyAt, keyDigests, capAt, List.mem_cons, true_or]
  have hcapLe : ∀ m, 2 ^ min S.params.capHeight m ≤ 2 ^ S.params.capHeight := fun m ↦
    Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
  -- an entry of a cap read off round `r` at an offset whose window its key binds is a key digest
  have hcapMem : ∀ r off n, n ≤ 2 ^ S.params.capHeight →
      (∀ d ∈ (capFrom (blocks.getD r []) off (2 ^ S.params.capHeight)).toList,
        d ∈ boundDigestsB S (capAt answer blocks r) (blocks.getD r [])) →
      ∀ j, (capFrom (blocks.getD r []) off n).toList.getD j 0 ∈
        keyDigests (boundDigestsB S) (keyAt answer blocks r) ∨
        (capFrom (blocks.getD r []) off n).toList.getD j 0 = initCap := by
    intro r off n hn hbd j
    rcases getD_capFrom_mem (blocks.getD r []) off n _ hn j with h | h
    · left
      simp only [keyAt, keyDigests]
      exact List.mem_cons_of_mem _ (hbd _ h)
    · exact Or.inr h
  -- the leading window of a round on a capacity that is not the initial one
  have hfront : ∀ r, capAt answer blocks r ≠ initCap →
      ∀ d ∈ (capFrom (blocks.getD r []) 0 (2 ^ S.params.capHeight)).toList,
        d ∈ boundDigestsB S (capAt answer blocks r) (blocks.getD r []) := by
    intro r hr d hd
    simp only [boundDigestsB, boundDigestsOf, hr, ↓reduceIte]
    exact List.mem_append_left _ hd
  have hcap0 : ∀ j, (capFrom (blocks.getD 0 []) (mainOffsetB S)
      (2 ^ min S.params.capHeight S.logTop)).toList.getD j 0 ∈
        keyDigests (boundDigestsB S) (keyAt answer blocks 0) ∨
      (capFrom (blocks.getD 0 []) (mainOffsetB S)
        (2 ^ min S.params.capHeight S.logTop)).toList.getD j 0 = initCap :=
    hcapMem 0 _ _ (hcapLe _) (fun d hd ↦ by
      simpa only [boundDigestsB, boundDigestsOf, capAt, ↓reduceIte] using hd)
  -- with lookups, the permutation commitment opens the second round
  have hcapP : S.hasLookups = true → ∀ j, (capFrom (blocks.getD (lookupRounds S) []) 0
      (2 ^ min S.params.capHeight (permLog S))).toList.getD j 0 ∈
        keyDigests (boundDigestsB S) (keyAt answer blocks (lookupRounds S)) ∨
      (capFrom (blocks.getD (lookupRounds S) []) 0
        (2 ^ min S.params.capHeight (permLog S))).toList.getD j 0 = initCap := by
    intro hl
    have h1 : lookupRounds S = 1 := by simp only [lookupRounds, hl, ↓reduceIte]
    rw [h1]
    exact hcapMem 1 _ _ (hcapLe _) (hfront 1 (hcap 0 (by omega)))
  have hcapQ : ∀ j, (capFrom (blocks.getD (lookupRounds S + 1) []) 0
      (2 ^ min S.params.capHeight S.logTop)).toList.getD j 0 ∈
        keyDigests (boundDigestsB S) (keyAt answer blocks (lookupRounds S + 1)) ∨
      (capFrom (blocks.getD (lookupRounds S + 1) []) 0
        (2 ^ min S.params.capHeight S.logTop)).toList.getD j 0 = initCap :=
    hcapMem _ _ _ (hcapLe _) (hfront _ (hcap (lookupRounds S) (by omega)))
  have hcapF : ∀ f < nf, ∀ j, (capFrom (blocks.getD (lookupRounds S + 3 + f) []) (friOffsetB S f)
      (2 ^ min S.params.capHeight (friDepthB S f))).toList.getD j 0 ∈
        keyDigests (boundDigestsB S) (keyAt answer blocks (lookupRounds S + 3 + f)) ∨
      (capFrom (blocks.getD (lookupRounds S + 3 + f) []) (friOffsetB S f)
        (2 ^ min S.params.capHeight (friDepthB S f))).toList.getD j 0 = initCap := by
    intro f hf
    have hcap3 := hcap (lookupRounds S + 2 + f) (by omega)
    rw [show lookupRounds S + 2 + f + 1 = lookupRounds S + 3 + f by omega] at hcap3
    by_cases hf0 : f = 0
    · subst hf0
      have hblk3 := inputsB_getD_fold S common pis proof 0 (by omega)
      rw [← hblocks] at hblk3
      have hsz : ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[0]'(by
          omega)).1.size = 2 ^ min S.params.capHeight (friDepthB S 0) := by
        have h := hfsz 0 hf
        rw [List.getD_eq_getElem _ _ (by
          obtain ⟨-, -, -, hcs, -⟩ := shape_of_verifyInstancesWith S (idealOf answer) common proof
              pis hok
          rw [Array.length_toList, hcs]; exact hf)] at h
        rw [List.getElem_zip]
        exact h
      simp only [seedAt, ↓reduceIte] at hblk3
      intro j
      rw [hblk3, ← hsz, show friOffsetB S 0 = (friSeedB S).length from rfl]
      by_cases hj : j < ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[0]'(by
          omega)).1.size
      · left
        simp only [keyAt, keyDigests]
        refine List.mem_cons_of_mem _ ?_
        rw [← hblk3]
        simp only [boundDigestsB, boundDigestsOf, hcap3, ↓reduceIte]
        refine List.mem_append_right _ ?_
        rw [hblk3, ← length_witnessInput S.params.commitPowBits
          ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[0]'(by omega)).2]
        exact capFrom_mem_capBack _ _ _ _ (hsz ▸ hcapLe _) j hj
      · right
        rw [List.getD_eq_default _ _ (by
          simp only [capFrom, Array.length_toList, Array.size_ofFn]; omega)]
        exact zero_eq_initCap
    · have hoff : friOffsetB S f = 0 := by simp only [friOffsetB, hf0, ↓reduceIte]
      rw [hoff]
      exact hcapMem _ _ _ (hcapLe _) (hfront _ hcap3)
  -- extraction is stable after the round binding the digest
  have hnp : ∀ j0 j, j0 ≤ j → j < blocks.length →
      ∀ r ∈ keyDigests (boundDigestsB S) (keyAt answer blocks j0),
      (logCache (L.take (idx L (keyAt answer blocks j)))).NoPrediction (logCache L) r := by
    intro j0 j hj0 hj r hr
    have hle : idx L (keyAt answer blocks j0) ≤ idx L (keyAt answer blocks j) := by
      rcases Nat.lt_or_eq_of_le hj0 with h | rfl
      · exact (idx_keyAt_lt hconsL hclash blocks blocks.length hkeys j0 j h hj).le
      · exact le_refl _
    have hnp := noPrediction_take hconsL hclash r _ (hkeys j0 (by omega)) hr _ L.length hle
      (idx_lt (hkeys j hj)).le
    rwa [List.take_length] at hnp
  have hsame : ∀ j0 j, j0 ≤ j → j < blocks.length →
      ∀ r ∈ keyDigests (boundDigestsB S) (keyAt answer blocks j0),
      SameUnder (logCache (L.take (idx L (keyAt answer blocks j)))) (logCache L) r :=
    fun j0 j hj0 hj r hr k i ↦
      (Merkle.extractRow_eq_of_noPrediction _ _ r (hnp j0 j hj0 hj r hr) k i).symm
  have hsameM : ∀ j0 j, j0 ≤ j → j < blocks.length →
      ∀ r ∈ keyDigests (boundDigestsB S) (keyAt answer blocks j0),
      SameUnderM (logCache (L.take (idx L (keyAt answer blocks j)))) (logCache L) r :=
    fun j0 j hj0 hj r hr inj K t i ↦
      (Merkle.extractGroup_eq_of_noPrediction _ _ inj r (hnp j0 j hj0 hj r hr) K t i).symm
  -- the rounds' prefixes, kept opaque
  obtain ⟨C, hC⟩ : ∃ C : ℕ → Merkle.Cache F (Digest F),
      C = fun j ↦ logCache (L.take (idx L (keyAt answer blocks j))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℕ → List F,
      B = fun j k ↦ ((history answer blocks j).map Prod.fst ++ [blocks.getD j []]).getD k [] :=
    ⟨_, rfl⟩
  obtain ⟨Sm, hSm⟩ : ∃ Sm : ℕ → ℕ → Vector F S.streamLen,
      Sm = fun j k ↦ ((history answer blocks j).map Prod.snd ++
        [(answer (keyAt answer blocks j)).2]).getD k (Vector.replicate _ 0) := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : ℕ → List F, blk = fun k ↦ blocks.getD k [] := ⟨_, rfl⟩
  obtain ⟨smp, hsmp⟩ : ∃ smp : ℕ → Vector F S.streamLen,
      smp = fun k ↦ (answer (keyAt answer blocks k)).2 := ⟨_, rfl⟩
  have hBk : ∀ j k, k ≤ j → B j k = blk k := fun j k hk ↦ by
    rw [hB, hblk]; exact history_fst answer blocks j k hk
  have hSk : ∀ j k, k ≤ j → Sm j k = smp k := fun j k hk ↦ by
    rw [hSm, hsmp]; exact history_snd answer blocks j k hk _
  -- no round is bad for its prefix transcript
  have hbad : ∀ j < blocks.length, ¬ roundBadAtB S publicValues δ δ' loss j
      (prefixTranscriptB S (C j) (B j) (Sm j)) (smp j) := by
    intro j hj
    have h := hround _ (hkeys j hj)
    have hparse : parse (L.take (idx L (keyAt answer blocks j))) (keyAt answer blocks j) =
        some (history answer blocks j, blocks.getD j []) :=
      parse_keyAt (consistent_take hconsL _)
        (capsInjective hconsL hclash _ fun t ht ↦ mem_map_fst_take ht)
        (hasRounds_take hconsL hclash blocks blocks.length hkeys j hj)
    have hseed : seedB S <+:
        ((history answer blocks j).map Prod.fst ++ [blocks.getD j []]).getD 0 [] := by
      rw [history_fst answer blocks j 0 (Nat.zero_le _), hblocks]
      exact seedB_prefix S common proof pis
        (shape_of_verifyInstancesWith S (idealOf answer) common proof pis hok).2.2.1
    rw [hC, hB, hSm, hsmp]
    simp only [keyAt] at h hparse ⊢
    unfold RoundBadB at h
    dsimp only at h
    rw [hparse] at h
    dsimp only at h
    rw [length_history] at h
    exact fun hb ↦ h ⟨hseed, hb⟩
  -- the transcript of the run
  obtain ⟨T, hT⟩ : ∃ T, T = prefixTranscriptB S (logCache L) blk smp := ⟨_, rfl⟩
  -- a cap read off round `r` at its bound offset stays extracted after round `r`
  have hcapS : ∀ (c : Cap F) (r j : ℕ), r ≤ j → j < blocks.length →
      (∀ i, c.toList.getD i 0 ∈ keyDigests (boundDigestsB S) (keyAt answer blocks r)
        ∨ c.toList.getD i 0 = initCap) → CapSameUnder (C j) (logCache L) c := by
    intro c r j hrj hj h i
    rw [hC]
    rcases h i with h | h
    · exact hsame r j hrj hj _ h
    · rw [h]; exact hsame 0 j (Nat.zero_le _) hj _ hinit0
  have hcapSM : ∀ (c : Cap F) (r j : ℕ), r ≤ j → j < blocks.length →
      (∀ i, c.toList.getD i 0 ∈ keyDigests (boundDigestsB S) (keyAt answer blocks r)
        ∨ c.toList.getD i 0 = initCap) → CapSameUnderM (C j) (logCache L) c := by
    intro c r j hrj hj h i
    rw [hC]
    rcases h i with h | h
    · exact hsameM r j hrj hj _ h
    · rw [h]; exact hsameM 0 j (Nat.zero_le _) hj _ hinit0
  have htraceS : ∀ j < blocks.length, CapSameUnderM (C j) (logCache L)
      (capFrom (blk 0) (mainOffsetB S) (2 ^ min S.params.capHeight S.logTop)) :=
    fun j hj ↦ by rw [hblk]; exact hcapSM _ 0 j (Nat.zero_le _) hj hcap0
  have hpermS : ∀ j, lookupRounds S ≤ j → j < blocks.length → S.hasLookups = true →
      CapSameUnderM (C j) (logCache L)
        (capFrom (blk (lookupRounds S)) 0 (2 ^ min S.params.capHeight (permLog S))) :=
    fun j h1 hj hl ↦ by rw [hblk]; exact hcapSM _ _ j h1 hj (hcapP hl)
  have hquotS : ∀ j, lookupRounds S + 1 ≤ j → j < blocks.length →
      CapSameUnderM (C j) (logCache L)
        (capFrom (blk (lookupRounds S + 1)) 0 (2 ^ min S.params.capHeight S.logTop)) :=
    fun j h1 hj ↦ by rw [hblk]; exact hcapSM _ _ j h1 hj hcapQ
  have hfoldS : ∀ j f, lookupRounds S + 3 + f ≤ j → j < blocks.length → f < nf →
      CapSameUnder (C j) (logCache L) (capFrom (blk (lookupRounds S + 3 + f)) (friOffsetB S f)
        (2 ^ min S.params.capHeight (friDepthB S f))) :=
    fun j f hf hj hf' ↦ by rw [hblk]; exact hcapS _ _ j hf hj (hcapF f hf')
  have hlkeq : ∀ j, (prefixTranscriptB S (C j) (B j) (Sm j)).lookupAlpha = T.lookupAlpha ∧
      (prefixTranscriptB S (C j) (B j) (Sm j)).lookupBeta = T.lookupBeta := fun j ↦ by
    rw [hT]
    exact prefixTranscriptB_lookup_congr S _ _ fun _ ↦ hSk j 0 (Nat.zero_le _)
  have htreq : ∀ j < blocks.length, (prefixTranscriptB S (C j) (B j) (Sm j)).trace = T.trace :=
    fun j hj ↦ by
      rw [hT]; exact prefixTranscriptB_trace S (hBk j 0 (Nat.zero_le _)) (htraceS j hj)
  have hpermeq : ∀ j, lookupRounds S ≤ j → j < blocks.length →
      (prefixTranscriptB S (C j) (B j) (Sm j)).perm = T.perm := fun j h1 hj ↦ by
    rw [hT]; exact prefixTranscriptB_perm S (hBk j _ h1) (hpermS j h1 hj)
  have htermeq : ∀ j, lookupRounds S ≤ j →
      (prefixTranscriptB S (C j) (B j) (Sm j)).terminal = T.terminal := fun j h1 ↦ by
    rw [hT]
    funext i
    show (if (S.lookups i).isEmpty then 0 else Challenge.toSpec (extFrom (EF := EF)
        ((B j (lookupRounds S)).drop (8 * 2 ^ min S.params.capHeight (permLog S)))
          (terminalIndex S i))) =
      (if (S.lookups i).isEmpty then 0 else Challenge.toSpec (extFrom (EF := EF)
        ((blk (lookupRounds S)).drop (8 * 2 ^ min S.params.capHeight (permLog S)))
          (terminalIndex S i)))
    rw [hBk j _ h1]
  have hαeq : ∀ j, lookupRounds S ≤ j →
      (prefixTranscriptB S (C j) (B j) (Sm j)).alpha = T.alpha := fun j hj ↦ by
    rw [hT]
    show extAt (Sm j (lookupRounds S)) 0 = extAt (smp (lookupRounds S)) 0
    rw [hSk j _ hj]
  have hζeq : ∀ j, lookupRounds S + 1 ≤ j →
      (prefixTranscriptB S (C j) (B j) (Sm j)).zeta = T.zeta := fun j hj ↦ by
    rw [hT]
    show extAt (Sm j (lookupRounds S + 1)) (challengeOffset S.params.oodPowBits) =
      extAt (smp (lookupRounds S + 1)) (challengeOffset S.params.oodPowBits)
    rw [hSk j _ hj]
  have hbeq : ∀ j, lookupRounds S + 2 ≤ j →
      (prefixTranscriptB S (C j) (B j) (Sm j)).batch = T.batch := fun j hj ↦ by
    rw [hT]
    show extAt (Sm j (lookupRounds S + 2)) (challengeOffset S.params.batchPowBits) =
      extAt (smp (lookupRounds S + 2)) (challengeOffset S.params.batchPowBits)
    rw [hSk j _ hj]
  have hoeq : ∀ j, lookupRounds S + 2 ≤ j →
      (prefixTranscriptB S (C j) (B j) (Sm j)).openings = T.openings := fun j hj ↦ by
    rw [hT]
    show openingsAtB S ((B j (lookupRounds S + 2)).drop (pcsSeedB S).length) =
      openingsAtB S ((blk (lookupRounds S + 2)).drop (pcsSeedB S).length)
    rw [hBk j _ hj]
  have hqeq : ∀ j, lookupRounds S + 1 ≤ j → j < blocks.length →
      (prefixTranscriptB S (C j) (B j) (Sm j)).quotient = T.quotient := fun j h1 hj ↦ by
    rw [hT]; exact prefixTranscriptB_quotient S (hBk j _ h1) (hquotS j h1 hj)
  have hReq : ∀ j, lookupRounds S + 2 ≤ j → j < blocks.length →
      (prefixTranscriptB S (C j) (B j) (Sm j)).rounds = T.rounds := fun j h2 hj ↦ by
    unfold Sound.Batch.Transcript.rounds Sound.Batch.Transcript.deepWords
      Sound.Batch.Transcript.prover
    rw [htreq j hj, hpermeq j (by omega) hj, htermeq j (by omega), (hlkeq j).1, (hlkeq j).2,
      hqeq j (by omega) hj, hαeq j (by omega), hζeq j (by omega), hbeq j h2, hoeq j h2]
  -- the grinding checks and the run of FRI
  obtain ⟨hsize, -, -, -, -, -, -, -, -, hlk, hlc, hood, -, hbc, ⟨st, hfriOk⟩, -⟩ :=
    verifyInstancesWith_ok (idealOf answer) S.params S.instances common proof pis hok
  rw [length_instances] at hsize
  have hperm := (lookupShapeOk_spec S.params S.instances proof hlk).2.1
  have hK : 2 * Challenge.d EF + 1 ≤ S.streamLen := by unfold Iop.Batch.Setup.streamLen; omega
  -- the lookup round
  have hlookup : ¬ Sound.Batch.LookupBad S publicValues δ' T.trace T.lookupAlpha T.lookupBeta := by
    cases hl : S.hasLookups
    · exact Sound.Batch.not_lookupBad S publicValues (lookups_eq_nil_of S hl) δ' _ _ _
    · have h1 : lookupRounds S = 1 := by simp only [lookupRounds, hl, ↓reduceIte]
      have h := hbad 0 (by omega)
      have hpow : S.params.lookupPowBits ≠ 0 → CompPoly.CanonicalNat.toNat
          ((smp 0).toList.getD 0 0) % 2 ^ S.params.lookupPowBits = 0 := fun hb ↦ by
        rw [hsmp]
        exact lookupWitnessB_idealOf answer S common proof pis hl (hlc hl) hb
      rw [roundBadAtB, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), htreq 0 (by omega),
        (hlkeq 0).1, (hlkeq 0).2] at h
      exact fun hlb ↦ h ⟨hpow, hlb⟩
  -- round `α`
  have hα : ¬ Sound.Batch.AlphaBad S publicValues δ' T.trace T.perm T.terminal T.lookupAlpha
      T.lookupBeta T.alpha := by
    have h := hbad (lookupRounds S) (by omega)
    rw [roundBadAtB, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), htreq _ (by omega),
      hpermeq _ le_rfl (by omega), htermeq _ le_rfl, (hlkeq _).1, (hlkeq _).2, hαeq _ le_rfl] at h
    exact h
  -- round `ζ`
  have hζ : ¬ Sound.Batch.ZetaBad S publicValues δ' T.trace T.perm T.terminal T.lookupAlpha
      T.lookupBeta T.alpha T.quotient T.zeta := by
    have h := hbad (lookupRounds S + 1) (by omega)
    have hpow : S.params.oodPowBits ≠ 0 → CompPoly.CanonicalNat.toNat
        ((smp (lookupRounds S + 1)).toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0 := fun hb ↦ by
      rw [hsmp]
      exact oodWitnessB_idealOf answer S common proof pis hK hperm hpne hqne hood hb
    rw [roundBadAtB, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), htreq _ (by omega),
      hpermeq _ (by omega) (by omega), htermeq _ (by omega), (hlkeq _).1, (hlkeq _).2,
      hqeq _ le_rfl (by omega), hαeq _ (by omega), hζeq _ le_rfl] at h
    exact fun hzb ↦ h ⟨hpow, hzb⟩
  -- the batching round
  have ha : ¬ Sound.Batch.BatchBad S publicValues δ δ' T.trace T.perm T.terminal T.lookupAlpha
      T.lookupBeta T.alpha T.quotient T.zeta T.openings T.batch := by
    have h := hbad (lookupRounds S + 2) (by omega)
    have hpow : S.params.batchPowBits ≠ 0 → CompPoly.CanonicalNat.toNat
        ((smp (lookupRounds S + 2)).toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0 :=
      fun hb ↦ by
        rw [hsmp]
        exact batchWitnessB_idealOf answer S common proof pis hK hperm hpne hqne hbc hb
    rw [roundBadAtB, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), htreq _ (by omega),
      hpermeq _ (by omega) (by omega), htermeq _ (by omega), (hlkeq _).1, (hlkeq _).2,
      hqeq _ (by omega) (by omega), hαeq _ (by omega), hζeq _ (by omega), hbeq _ le_rfl,
      hoeq _ le_rfl] at h
    exact fun hbb ↦ h ⟨hpow, hbb⟩
  -- the folds
  set zeta := zetaOfB (idealOf answer) S.params S.instances common proof pis
  have hD := descHeights_batchRounds S common proof zeta hsize
  have hfolds : ∀ f, ¬ Sound.Batch.FoldBad S δ loss T.rounds T.words f (T.betas f) := by
    intro f
    by_cases hf : f < nf
    · have h := hbad (lookupRounds S + 3 + f) (by omega)
      have hpow : S.params.commitPowBits ≠ 0 → CompPoly.CanonicalNat.toNat
          ((smp (lookupRounds S + 3 + f)).toList.getD 0 0) % 2 ^ S.params.commitPowBits = 0 :=
        fun hb ↦ by
          rw [hsmp]
          exact commitWitnessB_idealOf answer S common proof pis (le_refl _) hperm hpne hqne _ hD
            st hfriOk f (by omega) hb
      rw [roundBadAtB, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (by omega :
          lookupRounds S + 3 + f - lookupRounds S - 3 < nf)),
        show lookupRounds S + 3 + f - lookupRounds S - 3 = f by omega,
        hReq _ (by omega) (by omega)] at h
      have hw : (prefixTranscriptB S (C (lookupRounds S + 3 + f)) (B (lookupRounds S + 3 + f))
          (Sm (lookupRounds S + 3 + f))).words f = T.words f := by
        rw [hT]
        exact prefixTranscriptB_words S f (hBk _ _ le_rfl) (hfoldS _ f le_rfl (by omega) hf)
      have hβ : (prefixTranscriptB S (C (lookupRounds S + 3 + f)) (B (lookupRounds S + 3 + f))
          (Sm (lookupRounds S + 3 + f))).betas f = T.betas f := by
        rw [hT]
        show betasAtB S (Sm (lookupRounds S + 3 + f)) f = betasAtB S smp f
        unfold betasAtB
        rw [hSk _ _ le_rfl]
      intro hfb
      refine h ⟨hpow, ?_⟩
      unfold Sound.Batch.FoldBad at hfb ⊢
      rw [hβ]
      exact (Rounds.foldFails_congr _ _ _ _ _ _ f hw _ _).mpr hfb
    · refine foldFails_of_le _ _ _ _ _ f _ _ ?_
      rw [Sound.Batch.numFolds_rounds, ← length_friArities]
      omega
  -- the query round
  have hq : ¬ Sound.Batch.QueryBad S δ loss T (powAtB S (smp (lookupRounds S + 3 + nf)))
      (queriesAtB S (smp (lookupRounds S + 3 + nf))) := by
    have h := hbad (lookupRounds S + 3 + nf) (by omega)
    rw [roundBadAtB, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at h
    rwa [prefixTranscriptB_congr S (fun k hk ↦ hBk _ k hk) (fun k hk ↦ hSk _ k (by omega))
      (htraceS _ (by omega)) (hpermS _ (by omega) (by omega)) (hquotS _ (by omega) (by omega))
      (fun f hf ↦ hfoldS _ f (by omega) (by omega) hf), ← hT] at h
  -- binding commitments on answers changed outside the run
  obtain ⟨dstar, hdstar⟩ := exists_not_mem (logDigests (boundDigestsB S) L)
    ((length_logDigests_le (boundDigestsB S) (2 ^ (S.params.capHeight + 1))
      Nat.one_le_two_pow (fun c i ↦ length_boundDigestsOf_le _ _ c i) L).trans_lt hsmall)
  set g' := fresh L answer dstar with hg'
  have hagree : ∀ e ∈ vlog, g' e.1 = answer e.1 := fun e he ↦
    fresh_of_mem L answer dstar _ (by
      rw [List.map_append]; exact List.mem_append_right _ (List.mem_map_of_mem he))
  have hok' : CompStark.Batch.verifyInstancesWith (idealOf g') S.params S.instances common proof
      pis =
      .ok () := by
    rw [← evalWithAnswerFn_verifyInstancesWith, evalWithAnswerFn_congr answer g' _ hagree,
      evalWithAnswerFn_verifyInstancesWith]
    exact hok
  have hsetupL : ∀ e ∈ tableQueryLog S.setupRo answer, g' e.1 = answer e.1 := fun e he ↦
    fresh_of_mem L answer dstar _ (by
      rw [List.map_append]; exact List.mem_append_left _ (List.mem_map_of_mem (hsetup e he)))
  have hcommon' : CompStark.Batch.commonWith (idealOf g') S.params S.keyInstances = common := by
    rw [← evalWithAnswerFn_setupRoB S g', evalWithAnswerFn_congr answer g' _ hsetupL,
      evalWithAnswerFn_setupRoB, hcommon]
  have hshapeA := shape_of_verifyInstancesWith S (idealOf answer) common proof pis hok
  have hne : ∀ r ∈ logDigests (boundDigestsB S) L, r ≠ dstar :=
    fun r hr he ↦ hdstar (he ▸ hr)
  have hinitL : initCap ∈ logDigests (boundDigestsB S) L :=
    mem_logDigests (hkeys 0 (by omega)) hinit0
  -- the entries of a cap read off round `r` at its bound offset are digests of the log
  have hcapNe : ∀ (c : Cap F) (r : ℕ), r < blocks.length →
      (∀ i, c.toList.getD i 0 ∈ keyDigests (boundDigestsB S) (keyAt answer blocks r)
        ∨ c.toList.getD i 0 = initCap) → ∀ i, c.toList.getD i 0 ≠ dstar := by
    intro c r hr h i
    rcases h i with h | h
    · exact hne _ (mem_logDigests (hkeys r hr) h)
    · rw [h]; exact hne _ hinitL
  have htopI : ∀ i : Fin S.k, S.logN i + S.params.logBlowup ≤ S.logTop := logTop_ge S
  have hmain : CapBindingM (logCache L) (idealOf g') proof.mainCommit S.params.capHeight S.logTop
      S.mainHeights := by
    refine capBindingM_fresh answer L hconsL hclash dstar hdstar _ ?_ _ S.logTop S.mainHeights
      (fun h hh ↦ ?_) (List.mem_ofFn.mpr ⟨S.top, rfl⟩)
    · rw [← mainRoot_eq S common proof pis hshapeA.2.2.1 hmsz]
      exact hcapNe _ 0 (by omega) hcap0
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hh
      exact ⟨_, hfit i, htopI i, rfl⟩
  have hquot : CapBindingM (logCache L) (idealOf g') proof.quotientCommit S.params.capHeight
      S.logTop (quotHeights S) := by
    refine capBindingM_fresh answer L hconsL hclash dstar hdstar _ ?_ _ S.logTop (quotHeights S)
      (fun h hh ↦ ?_) (List.mem_flatMap.mpr ⟨S.top, List.mem_finRange _, List.mem_replicate.mpr
        ⟨(Nat.two_pow_pos _).ne', rfl⟩⟩)
    · rw [← quotientRoot_eqB S common proof pis hqsz]
      exact hcapNe _ _ (by omega) hcapQ
    · obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hh
      exact ⟨_, hfit i, htopI i, List.eq_of_mem_replicate hi⟩
  have hfri : ∀ c ∈ proof.fri.commits, CapBinding (logCache L) (idealOf g') c := by
    intro c hc j
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hc
    obtain ⟨-, -, -, hcs, -⟩ := hshapeA
    have hi' : i < nf := by rw [hnf, ← hcs]; exact hi
    have h := foldRoot_eqB S answer hok i hi' (hfsz i hi')
    rw [List.getD_eq_getElem proof.fri.commits.toList #[] (by rw [Array.length_toList]; exact hi),
      Array.getElem_toList] at h
    rw [← h]
    exact binding_fresh answer L hconsL hclash dstar hdstar _
      (hcapNe _ _ (by omega) (hcapF i hi') j)
  have hprepNe : ∀ root ∈ common.preprocessed, ∀ e, root.toList.getD e 0 ≠ dstar := by
    intro root hr e
    by_cases he : e < root.size
    · have hr' : CompStark.Batch.preprocessedCapWith (idealOf answer) S.params S.instances =
          some root := by rw [← preprocessed_commonWith, hcommon]; exact hr
      obtain ⟨q, hq, hd⟩ := exists_prep_mem S answer root hr' e he
      rw [List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact he), Array.getElem_toList,
        ← hd]
      exact hne _ (List.mem_flatMap.mpr ⟨q, List.mem_append_left _ (hsetup q hq),
        List.mem_cons_self⟩)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [Array.length_toList]; omega),
        Option.getD_none, zero_eq_initCap]
      exact hne _ hinitL
  have hprepBind : ∀ root ∈ common.preprocessed,
      CapBindingM (logCache L) (idealOf g') root S.params.capHeight (prepLog S)
        (prepHeights S) := by
    intro root hr
    obtain ⟨i, hi⟩ : ∃ i : Fin S.k, 0 < (S.air i).preprocessedWidth := by
      have hprep := hshapeA.2.2.1
      rw [show common.preprocessed.isSome = true by rw [Option.isSome_iff_exists]; exact ⟨_, hr⟩]
        at hprep
      obtain ⟨I, hI, hp⟩ := List.any_eq_true.mp hprep.symm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
      exact ⟨i, decide_eq_true_iff.mp hp⟩
    refine capBindingM_fresh answer L hconsL hclash dstar hdstar _ (hprepNe root hr) _
      (prepLog S) (prepHeights S) (fun h hh ↦ ?_) ?_
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hh
      have hp' : 0 < (S.air i').preprocessedWidth := by simpa using (List.mem_filter.mp hi').2
      exact ⟨_, by have := prepLog_le S; have := hfit i'; omega, le_prepLog S i' hp', rfl⟩
    · rcases foldl_max_mem ((prepInsts S).map fun i ↦ S.logN i + S.params.logBlowup) 0 with
        h | h
      · have : prepLog S = 0 := h
        have := le_prepLog S i hi
        have := (S.valid i).blowup
        omega
      · obtain ⟨i', hi', he⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨i', hi', congrArg (2 ^ ·) he⟩
  have hprep : ∀ root ∈ common.preprocessed, ∀ i : Fin S.k, 0 < (S.air i).preprocessedWidth →
      ∀ j < (S.air i).preprocessedWidth, ∀ r < 2 ^ (S.logN i + S.params.logBlowup),
        Merkle.matColumnCap (logCache L) root.toList S.params.capHeight (prepLog S)
          (prepHeights S) (prepWidths S) (prepIndex S i) j (S.logN i + S.params.logBlowup) r =
        (S.instanceSetup i).preprocessedWord j
          (finMod _ (reverseBits r (S.logN i + S.params.logBlowup))) :=
    fun root hr i hp j hj r hrr ↦ matColumn_setup S (logCache L) g' root
      (by rw [← preprocessed_commonWith, hcommon']; exact hr) (hprepBind root hr)
      (fun i' _ ↦ by have := prepLog_le S; have := hfit i'; omega) i hp j hj r hrr
  have hpermBind : ∀ root ∈ proof.permutationCommit,
      CapBindingM (logCache L) (idealOf g') root S.params.capHeight (permLog S)
        (permHeights S) := by
    intro root hr
    have hl : S.hasLookups = true := hperm.symm.trans (Option.isSome_iff_exists.mpr ⟨_, hr⟩)
    obtain ⟨i, hi⟩ : ∃ i : Fin S.k, (S.lookups i).isEmpty = false := by
      obtain ⟨I, hI, hp⟩ := List.any_eq_true.mp hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
      refine ⟨i, ?_⟩
      rw [lookups_eq]
      simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using hp
    have hpi : i ∈ permInsts S :=
      List.mem_filter.mpr ⟨List.mem_finRange _, by rw [hi]; rfl⟩
    refine capBindingM_fresh answer L hconsL hclash dstar hdstar _ ?_ _ (permLog S)
      (permHeights S) (fun h hh ↦ ?_) ?_
    · rw [← permRoot_eqB S common proof pis hl hr (hpsz root hr)]
      exact hcapNe _ _ (by omega) (hcapP hl)
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hh
      exact ⟨_, by have := permLog_le S; have := hfit i'; omega,
        (le_foldl_max _ 0).2 _ (List.mem_map.mpr ⟨i', hi', rfl⟩), rfl⟩
    · rcases foldl_max_mem ((permInsts S).map fun i ↦ S.logN i + S.params.logBlowup) 0 with
        h | h
      · have h0 : permLog S = 0 := h
        have := (le_foldl_max ((permInsts S).map fun i ↦ S.logN i + S.params.logBlowup) 0).2 _
          (List.mem_map.mpr ⟨i, hpi, rfl⟩)
        have := (S.valid i).blowup
        rw [permLog] at h0
        omega
      · obtain ⟨i', hi', he⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨i', hi', congrArg (2 ^ ·) he⟩
  have hbcs := bcsB S (logCache L) (idealOf g') common proof publicValues hmain hquot hfri
    hprepBind hprep hpermBind hok'
  have hext : extractB S (logCache L) (idealOf g') common proof pis = T := by
    rw [extractB_eq_prefixTranscriptB S g' (logCache L) hok', hT, hblk, hsmp]
    congr 1
    funext k
    exact samples_keyAt_fresh answer _ L dstar k
  dsimp only at hbcs
  rw [hext] at hbcs
  obtain ⟨hsum, hcheck, hdeg, hpow, hqueries⟩ := hbcs
  obtain ⟨-, -, hfp, -⟩ := hshapeA.2.2.2
  have hfpne : proof.fri.finalPoly.toList ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [Array.length_toList, hfp]
    exact Nat.two_pow_pos _
  obtain ⟨-, -, -, -, -, -, hpowEq, hqEq⟩ := challengesB_idealOf g' S common proof pis (le_refl _)
    hfpne hperm hpne hqne hcne
  rw [hz, hg'] at hpowEq hqEq
  dsimp only at hpowEq hqEq
  rw [samples_keyAt_fresh answer _ L dstar] at hpowEq hqEq
  have hpow' : CompPoly.CanonicalNat.toNat (powAtB S (smp (lookupRounds S + 3 + nf))) %
      2 ^ S.params.queryPowBits = 0 := by
    by_cases hb : S.params.queryPowBits = 0
    · simp only [hb, pow_zero, Nat.mod_one]
    · rw [powAtB, ite_eq_right_of_eq_false _ _ (eq_false hb), hsmp]
      dsimp only
      rw [← hpowEq hb]
      exact hpow
  have hqueries' : ∀ j, queryPoint S.domainSetup (queriesAtB S (smp (lookupRounds S + 3 + nf)) j) ∈
      T.consistentQueries := fun j ↦ by
    rw [queriesAtB, hsmp]
    dsimp only
    rw [← hqEq j.val j.isLt]
    exact hqueries j
  obtain ⟨traces, hP, hsat⟩ := Sound.Batch.exists_satisfied_of_safe S publicValues δ δ' loss hδ' T
    _ _ hsum hcheck hdeg hpow' hqueries' hlookup hα hζ ha hfolds hq
  -- the traces committed in the prover's queries are the run's
  have hhead : idx L (keyAt answer blocks 0) ≤ log.length := by
    by_cases hin : keyAt answer blocks 0 ∈ log.map Sigma.fst
    · have := List.idxOf_lt_length_of_mem hin
      rw [List.length_map] at this
      unfold idx
      rw [List.map_append, List.idxOf_append_of_mem hin]
      exact this.le
    · obtain ⟨rest, hrest⟩ := verifyInstancesWith_log_head answer S (le_refl _) common proof pis
        (by rw [run_idealLoggedB]; exact hok)
      rw [run_idealLoggedB] at hrest
      dsimp only at hrest
      rw [← hvlog] at hrest
      unfold idx
      rw [List.map_append, List.idxOf_append_of_notMem hin, hrest, List.map_cons,
        List.idxOf_cons_self, List.length_map, Nat.add_zero]
  have hlogL : CapSameUnderM (logCache log) (logCache L) proof.mainCommit := by
    rw [← mainRoot_eq S common proof pis hshapeA.2.2.1 hmsz]
    intro idx inj K' t i
    have hmem : (capFrom (blocks.getD 0 []) (mainOffsetB S)
        (2 ^ min S.params.capHeight S.logTop)).toList.getD idx 0 ∈
          keyDigests (boundDigestsB S) (keyAt answer blocks 0) := by
      rcases hcap0 idx with h | h
      · exact h
      · rw [h]; exact hinit0
    have hnp := noPrediction_take hconsL hclash _ _ (hkeys 0 (by omega)) hmem log.length L.length
      hhead (by rw [hL, List.length_append]; omega)
    rw [List.take_length, hL, List.take_left' rfl] at hnp
    exact (Merkle.extractGroup_eq_of_noPrediction _ _ inj _ hnp K' t i).symm
  have htraceT : Iop.Batch.committedTraces S log proof = T.trace := by
    rw [hT, hblk]
    funext i c x
    show Merkle.matColumnCap (logCache log) proof.mainCommit.toList _ _ _ _ _ _ _ _ =
      Merkle.matColumnCap (logCache L) (capFrom (blocks.getD 0 []) (mainOffsetB S)
        (2 ^ min S.params.capHeight S.logTop)).toList _ _ _ _ _ _ _ _
    rw [mainRoot_eq S common proof pis hshapeA.2.2.1 hmsz, matColumnCap_congr hlogL]
  rw [← htraceT] at hP
  exact hfail traces hP hsat

end Bad

end CompStark.Ni
