/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.RoundBounds
public import CompStark.Ni.Binding
public import CompStark.Ni.Accepted
public import CompStark.Ni.Extracted
public import CompStark.Ni.Setup

/-! # An accepted proof the extractor cannot open makes a bad query

The deterministic half of the Fiat–Shamir argument (`exists_badAt`): run a prover and then the
verifier against one answer table. If the verifier accepts a proof for `2 ^ logN` rows and no
trace close to the trace extracted from the prover's queries satisfies the AIR, some query of the
run is fresh and its answer clashes with a known digest (`Clash`) or makes its round bad
(`RoundBad`).

Suppose not. Then, with no clashes:

1. the duplex calls of the proof's rounds are first queried in order, and the queries before
   round `i`'s call parse it to the proof's prefix up to round `i` (`hasRounds_take`, C's
   `parse_keyAt`), so round `i` is not bad for the prefix transcript on the hash queries before
   it;
2. extraction under a digest a round binds does not change after the round
   (`noPrediction_take`), so these prefix transcripts agree with the transcript of the whole run,
   which is the transcript F's `bcs` extracts (`extract_eq_prefixTranscript`); and since the
   verifier queries the trace commitment's round first (`verifyWith_log_head`), the trace extracted
   from the prover's queries is the run's;
3. on answers changed outside the run (`fresh`) the commitments bind (`binding_fresh`), so `bcs`
   gives the terminal lemma's checks, and with every round safe some candidate trace satisfies the
   AIR (`Sound.exists_satisfied_of_safe`), a contradiction.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Fri.Spec OracleSpec OracleComp

variable {F : Type}

/-! ### First occurrences -/

theorem mem_map_fst_take {K : Nat} {log : QueryLog (spec F K)} {t : Query F} {n : Nat}
    (h : t ∈ (log.take n).map Sigma.fst) : t ∈ log.map Sigma.fst := by
  rw [List.map_take] at h
  exact List.mem_of_mem_take h

theorem mem_logDigests {bd : Digest F → List F → List (Digest F)} {K : Nat}
    {log : QueryLog (spec F K)} {t : Query F} (ht : t ∈ log.map Sigma.fst) {d : Digest F}
    (hd : d ∈ keyDigests bd t) : d ∈ logDigests bd log := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  exact List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _ hd⟩

variable [BaseField F] {EF : Type} [Challenge F EF]

/-- A property of every fresh query holds at the first query of each key. -/
theorem of_first {K : Nat} {answer : (q : Query F) → Answer K q} {log : QueryLog (spec F K)}
    (hcons : Consistent answer log) (P : QueryLog (spec F K) → (t : Query F) → Answer K t → Prop)
    (h : ∀ p (hp : p < log.length), log[p].1 ∉ (log.take p).map Sigma.fst →
      P (log.take p) log[p].1 log[p].2)
    {t : Query F} (ht : t ∈ log.map Sigma.fst) : P (log.take (idx log t)) t (answer t) := by
  have h1 := h (idx log t) (idx_lt ht) (by rw [getElem_idx_fst ht]; exact not_mem_take_idx ht)
  have hfst := getElem_idx_fst ht
  have hmem := List.getElem_mem (idx_lt ht)
  generalize log[idx log t]'(idx_lt ht) = e at h1 hfst hmem
  obtain ⟨t', a⟩ := e
  dsimp only at hfst h1
  subst hfst
  have ha : a = answer t' := hcons _ hmem
  subst ha
  exact h1

/-! ### The schedule's rounds -/

section Rounds
variable {K : Nat} (answer : (q : Query F) → Answer K q) (blocks : List (List F))

theorem length_history (j : Nat) : (history answer blocks j).length = j := by
  simp only [history, List.length_map, List.length_range]

theorem history_fst (j k : Nat) (hk : k ≤ j) :
    ((history answer blocks j).map Prod.fst ++ [blocks.getD j []]).getD k [] =
      blocks.getD k [] := by
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · rw [getD_append_singleton_lt _ _ _ _ (by rw [List.length_map, length_history]; exact hlt),
      List.getD_eq_getElem _ _ (by rw [List.length_map, length_history]; exact hlt)]
    simp only [history, List.getElem_map, List.getElem_range]
  · exact getD_append_singleton _ _ _ _ (by rw [List.length_map, length_history])

theorem history_snd (j k : Nat) (hk : k ≤ j) (d : Vector F K) :
    ((history answer blocks j).map Prod.snd ++ [(answer (keyAt answer blocks j)).2]).getD k d =
      (answer (keyAt answer blocks k)).2 := by
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · rw [getD_append_singleton_lt _ _ _ _ (by rw [List.length_map, length_history]; exact hlt),
      List.getD_eq_getElem _ _ (by rw [List.length_map, length_history]; exact hlt)]
    simp only [history, List.getElem_map]
    rw [List.getElem_range]
  · exact getD_append_singleton _ _ _ _ (by rw [List.length_map, length_history])

theorem capAt_fresh (log : QueryLog (spec F K)) (dstar : Digest F) :
    ∀ j, capAt (fresh log answer dstar) blocks j = capAt answer blocks j
  | 0 => rfl
  | j + 1 => by
    show (fresh log answer dstar (.duplex (capAt (fresh log answer dstar) blocks j) _)).1 = _
    rw [capAt_fresh log dstar j]
    rfl

theorem keyAt_fresh (log : QueryLog (spec F K)) (dstar : Digest F) (j : Nat) :
    keyAt (fresh log answer dstar) blocks j = keyAt answer blocks j := by
  simp only [keyAt, capAt_fresh]

theorem samples_keyAt_fresh (log : QueryLog (spec F K)) (dstar : Digest F) (j : Nat) :
    (fresh log answer dstar (keyAt (fresh log answer dstar) blocks j)).2 =
      (answer (keyAt answer blocks j)).2 := by
  show (fresh log answer dstar (.duplex (capAt (fresh log answer dstar) blocks j) _)).2 = _
  rw [capAt_fresh]
  rfl

theorem fresh_keyAt (log : QueryLog (spec F K)) (dstar : Digest F) (j : Nat) :
    fresh log answer dstar (keyAt answer blocks j) = answer (keyAt answer blocks j) := rfl

end Rounds

/-! ### The bad query -/

section Bad
variable (S : Iop.Setup EF) [S.Folds] (publicValues : List F) (δ δ' loss : NNReal)

/-- Query `p` of `log` is fresh, and its answer clashes with a known digest or makes its round
bad. -/
def BadAt (log : QueryLog (spec F S.streamLen)) (p : Nat) (hp : p < log.length) : Prop :=
  log[p].1 ∉ (log.take p).map Sigma.fst ∧
    (Clash (boundDigests S) (log.take p) log[p].1 log[p].2 ∨
      RoundBad S publicValues δ δ' loss (log.take p) log[p].1 log[p].2)

/-- **The bad query.** If the verifier, run after the setup and a prover whose queries `log` an
answer table answers, accepts a proof for `2 ^ logN` rows against the setup's key `vk`, and no
trace close to the trace committed in `log` satisfies the AIR, then some query of the run is fresh
and clashes or is round-bad. -/
theorem exists_badAt (hδ' : (δ' : ℝ) < 1 - S.rate) (answer : (q : Query F) → Answer S.streamLen q)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (log : QueryLog (spec F S.streamLen))
    (hcons : Consistent answer log)
    (hvk : preprocessedKeyWith (idealOf answer) S.params S.air S.logN = vk)
    (hsetup : ∀ e ∈ tableQueryLog S.setupRo answer, e ∈ log)
    (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof publicValues = .ok ())
    (hsmall : (2 ^ (S.params.capHeight + 1) + 2) * (log ++ tableQueryLog
      (verifyWith (ideal F S.streamLen) S.params S.air vk proof publicValues) answer).length <
        Fintype.card (Digest F))
    (hfail : ∀ trace ∈ closeTraces S δ' (committedTrace S log proof),
      ¬ S.air.Satisfied S.logN trace publicValues) :
    ∃ p hp, BadAt S publicValues δ δ' loss (log ++ tableQueryLog
      (verifyWith (ideal F S.streamLen) S.params S.air vk proof publicValues) answer) p hp := by
  set vlog := tableQueryLog (verifyWith (ideal F S.streamLen) S.params S.air vk proof
    publicValues) answer with hvlog
  set L := log ++ vlog with hL
  by_contra hno
  have hclash : NoClash (boundDigests S) L := fun p hp hfresh hc ↦ hno ⟨p, hp, hfresh, Or.inl hc⟩
  have hconsL : Consistent answer L := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hcons e h
    · exact consistent_tableQueryLog _ e h
  have hround : ∀ t ∈ L.map Sigma.fst,
      ¬ RoundBad S publicValues δ δ' loss (L.take (idx L t)) t (answer t) :=
    fun t ht ↦ of_first hconsL (fun pre t u ↦ ¬ RoundBad S publicValues δ δ' loss pre t u)
      (fun p hp hfresh hr ↦ hno ⟨p, hp, hfresh, Or.inr hr⟩) ht
  set blocks := inputs S.params S.air vk publicValues proof with hblocks
  have hz := length_zip_commits S answer hdb hok
  have hlen : blocks.length = S.lastFold + 5 := by
    rw [hblocks, length_inputs, hz]
    omega
  have hkeys : ∀ j < blocks.length, keyAt answer blocks j ∈ L.map Sigma.fst := fun j hj ↦ by
    rw [List.map_append]
    exact List.mem_append_right _ (hasRounds_verifyWith S answer vk proof publicValues hok j hj)
  have hinjL : CapsInjective answer L := capsInjective hconsL hclash L fun t ht ↦ ht
  have hcap : ∀ j, j < blocks.length → capAt answer blocks (j + 1) ≠ initCap :=
    fun j hj ↦ capAt_ne_initCap hinjL (fun k hk ↦ hkeys k hk) j hj
  -- the caps the rounds bind
  have hqne := size_quotientCommit_ne (idealOf answer) S.params S.air vk proof publicValues hok
  obtain ⟨-, hqsize, hfsize⟩ := size_caps S answer hdb hok
  have hcapLe : ∀ m, capSize S m ≤ 2 ^ S.params.capHeight := fun m ↦
    Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
  have hinit0 : initCap ∈ keyDigests (boundDigests S) (keyAt answer blocks 0) := by
    simp only [keyAt, keyDigests, capAt, List.mem_cons, true_or]
  -- an entry of a cap read off round `r` at an offset whose window its key binds is a key digest
  have hcapMem : ∀ r off n, n ≤ 2 ^ S.params.capHeight →
      (∀ d ∈ (capFrom (blocks.getD r []) off (2 ^ S.params.capHeight)).toList,
        d ∈ boundDigests S (capAt answer blocks r) (blocks.getD r [])) →
      ∀ j, (capFrom (blocks.getD r []) off n).toList.getD j 0 ∈
        keyDigests (boundDigests S) (keyAt answer blocks r) ∨
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
        d ∈ boundDigests S (capAt answer blocks r) (blocks.getD r []) := by
    intro r hr d hd
    simp only [boundDigests, boundDigestsOf, hr, ↓reduceIte]
    exact List.mem_append_left _ hd
  have hcap0 : ∀ j, (capFrom (blocks.getD 0 []) (starkSeedS S).length
      (capSize S S.logSize)).toList.getD j 0 ∈ keyDigests (boundDigests S) (keyAt answer blocks 0) ∨
      (capFrom (blocks.getD 0 []) (starkSeedS S).length (capSize S S.logSize)).toList.getD j 0 =
        initCap :=
    hcapMem 0 _ _ (hcapLe _) (fun d hd ↦ by
      simpa only [boundDigests, boundDigestsOf, capAt, ↓reduceIte] using hd)
  have hcap1 : ∀ j, (capFrom (blocks.getD 1 []) 0 (capSize S S.logSize)).toList.getD j 0 ∈
      keyDigests (boundDigests S) (keyAt answer blocks 1) ∨
      (capFrom (blocks.getD 1 []) 0 (capSize S S.logSize)).toList.getD j 0 = initCap :=
    hcapMem 1 _ _ (hcapLe _) (hfront 1 (hcap 0 (by omega)))
  have hcapF : ∀ f < S.lastFold + 1, ∀ j, (capFrom (blocks.getD (3 + f) []) (friOffset S f)
      (capSize S (friDepth S f))).toList.getD j 0 ∈
        keyDigests (boundDigests S) (keyAt answer blocks (3 + f)) ∨
      (capFrom (blocks.getD (3 + f) []) (friOffset S f) (capSize S (friDepth S f))).toList.getD j
        0 = initCap := by
    intro f hf
    have hcap3 := hcap (2 + f) (by omega)
    rw [show 2 + f + 1 = 3 + f by omega] at hcap3
    by_cases hf0 : f = 0
    · subst hf0
      have hblk3 := inputs_getD_fold S.params S.air vk publicValues proof 0 (by omega)
      rw [friSeedOf_eq S proof hdb] at hblk3
      rw [← hblocks] at hblk3
      have hsz : ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[0]'(by
          omega)).1.size = capSize S (friDepth S 0) := by
        rw [List.getElem_zip, Array.getElem_toList]
        exact hfsize 0 (by rw [(length_commits S answer hdb hok).2]; exact hf)
      simp only [seedAt, ↓reduceIte] at hblk3
      intro j
      rw [hblk3, ← hsz, show friOffset S 0 = (friSeedS S).length from rfl]
      by_cases hj : j < ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[0]'(by
          omega)).1.size
      · left
        simp only [keyAt, keyDigests]
        refine List.mem_cons_of_mem _ ?_
        rw [← hblk3]
        simp only [boundDigests, boundDigestsOf, hcap3, ↓reduceIte]
        refine List.mem_append_right _ ?_
        rw [hblk3, ← length_witnessInput S.params.commitPowBits
          ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[0]'(by omega)).2]
        exact capFrom_mem_capBack _ _ _ _ (hsz ▸ hcapLe _) j hj
      · right
        rw [List.getD_eq_default _ _ (by
          simp only [capFrom, Array.length_toList, Array.size_ofFn]; omega)]
        exact zero_eq_initCap
    · have hfront' := hfront (3 + f) hcap3
      have hoff : friOffset S f = 0 := by simp only [friOffset, hf0, ↓reduceIte]
      rw [hoff]
      exact hcapMem (3 + f) _ _ (hcapLe _) hfront'
  -- extraction is stable after the round binding the digest
  have hsame : ∀ j0 j, j0 ≤ j → j < blocks.length →
      ∀ r ∈ keyDigests (boundDigests S) (keyAt answer blocks j0),
      SameUnder (logCache (L.take (idx L (keyAt answer blocks j)))) (logCache L) r := by
    intro j0 j hj0 hj r hr k i
    have hle : idx L (keyAt answer blocks j0) ≤ idx L (keyAt answer blocks j) := by
      rcases Nat.lt_or_eq_of_le hj0 with h | rfl
      · exact (idx_keyAt_lt hconsL hclash blocks blocks.length hkeys j0 j h hj).le
      · exact le_refl _
    have hnp := noPrediction_take hconsL hclash r _ (hkeys j0 (by omega)) hr _ L.length hle
      (idx_lt (hkeys j hj)).le
    rw [List.take_length] at hnp
    exact (Merkle.extractRow_eq_of_noPrediction _ _ r hnp k i).symm
  -- the rounds' prefixes, kept opaque
  obtain ⟨C, hC⟩ : ∃ C : Nat → Merkle.Cache F (Digest F),
      C = fun j ↦ logCache (L.take (idx L (keyAt answer blocks j))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Nat → Nat → List F,
      B = fun j k ↦ ((history answer blocks j).map Prod.fst ++ [blocks.getD j []]).getD k [] :=
    ⟨_, rfl⟩
  obtain ⟨Sm, hSm⟩ : ∃ Sm : Nat → Nat → Vector F S.streamLen,
      Sm = fun j k ↦ ((history answer blocks j).map Prod.snd ++
        [(answer (keyAt answer blocks j)).2]).getD k (Vector.replicate _ 0) := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Nat → List F, blk = fun k ↦ blocks.getD k [] := ⟨_, rfl⟩
  obtain ⟨smp, hsmp⟩ : ∃ smp : Nat → Vector F S.streamLen,
      smp = fun k ↦ (answer (keyAt answer blocks k)).2 := ⟨_, rfl⟩
  have hBk : ∀ j k, k ≤ j → B j k = blk k := fun j k hk ↦ by
    rw [hB, hblk]; exact history_fst answer blocks j k hk
  have hSk : ∀ j k, k ≤ j → Sm j k = smp k := fun j k hk ↦ by
    rw [hSm, hsmp]; exact history_snd answer blocks j k hk _
  -- no round is bad for its prefix transcript
  have hbad : ∀ j < blocks.length, ¬ roundBadAt S publicValues δ δ' loss j
      (prefixTranscript S (C j) (B j) (Sm j)) (smp j) := by
    intro j hj
    have h := hround _ (hkeys j hj)
    have hparse : parse (L.take (idx L (keyAt answer blocks j))) (keyAt answer blocks j) =
        some (history answer blocks j, blocks.getD j []) :=
      parse_keyAt (consistent_take hconsL _)
        (capsInjective hconsL hclash _ fun t ht ↦ mem_map_fst_take ht)
        (hasRounds_take hconsL hclash blocks blocks.length hkeys j hj)
    have hseed : starkSeedS S <+:
        ((history answer blocks j).map Prod.fst ++ [blocks.getD j []]).getD 0 [] := by
      rw [history_fst answer blocks j 0 (Nat.zero_le _), hblocks, inputs_getD_zero, hdb]
      exact List.prefix_append_of_prefix (List.prefix_append_of_prefix
        (List.prefix_append_of_prefix (List.prefix_refl _)))
    rw [hC, hB, hSm, hsmp]
    simp only [keyAt] at h hparse ⊢
    unfold RoundBad at h
    dsimp only at h
    rw [hparse] at h
    dsimp only at h
    rw [length_history] at h
    exact fun hb ↦ h ⟨hseed, hb⟩
  -- the transcript of the run
  obtain ⟨T, hT⟩ : ∃ T, T = prefixTranscript S (logCache L) blk smp := ⟨_, rfl⟩
  -- extraction is stable after the round binding the digest
  have hsameC : ∀ j0 j, j0 ≤ j → j < blocks.length →
      ∀ r ∈ keyDigests (boundDigests S) (keyAt answer blocks j0),
      SameUnder (C j) (logCache L) r := fun j0 j hj0 hj r hr ↦ by
    rw [hC]; exact hsame j0 j hj0 hj r hr
  -- a cap read off round `r` at its bound offset stays extracted after round `r`
  have hcapS : ∀ (c : Cap F) (r j : Nat), r ≤ j → j < blocks.length →
      (∀ i, c.toList.getD i 0 ∈ keyDigests (boundDigests S) (keyAt answer blocks r) ∨
        c.toList.getD i 0 = initCap) → CapSameUnder (C j) (logCache L) c := by
    intro c r j hrj hj h i
    rcases h i with h | h
    · exact hsameC r j hrj hj _ h
    · rw [h]; exact hsameC 0 j (Nat.zero_le _) hj _ hinit0
  have htraceS : ∀ j < blocks.length, CapSameUnder (C j) (logCache L)
      (capFrom (blk 0) (starkSeedS S).length (capSize S S.logSize)) :=
    fun j hj ↦ by rw [hblk]; exact hcapS _ 0 j (Nat.zero_le _) hj hcap0
  have hquotS : ∀ j, 1 ≤ j → j < blocks.length →
      CapSameUnder (C j) (logCache L) (capFrom (blk 1) 0 (capSize S S.logSize)) :=
    fun j h1 hj ↦ by rw [hblk]; exact hcapS _ 1 j h1 hj hcap1
  have hfoldS : ∀ j f, 3 + f ≤ j → j < blocks.length → f < S.lastFold + 1 →
      CapSameUnder (C j) (logCache L)
        (capFrom (blk (3 + f)) (friOffset S f) (capSize S (friDepth S f))) :=
    fun j f hf hj hf' ↦ by rw [hblk]; exact hcapS _ (3 + f) j hf hj (hcapF f hf')
  have hαeq : ∀ j, (prefixTranscript S (C j) (B j) (Sm j)).alpha = T.alpha := fun j ↦ by
    rw [hT]; show extAt (Sm j 0) 0 = extAt (smp 0) 0; rw [hSk j 0 (Nat.zero_le _)]
  -- round `α`
  have hα : ¬ AlphaBad S publicValues δ' T.trace T.alpha := by
    have h := hbad 0 (by omega)
    rw [roundBadAt, ite_eq_left rfl, prefixTranscript_trace S (hBk 0 0 le_rfl)
      (htraceS 0 (by omega)), hαeq, ← hT] at h
    exact h
  -- the grinding checks and the run of FRI
  obtain ⟨-, htn, -, -, hshape, -, -, hood, -, hbc, ⟨st, hfriOk⟩, -⟩ := verifyWith_ok
    (idealOf answer) S.params S.air vk proof publicValues hok
  have hK : Challenge.d EF + 1 ≤ S.streamLen := by unfold Iop.Setup.streamLen; omega
  -- round `ζ`
  have hζ : ¬ ZetaBad S publicValues δ' T.trace T.alpha T.quotient T.zeta := by
    have h := hbad 1 (by omega)
    have hpow : S.params.oodPowBits ≠ 0 → CompPoly.CanonicalNat.toNat
        ((smp 1).toList.getD 0 0) % 2 ^ S.params.oodPowBits = 0 := fun hb ↦ by
      rw [hsmp]
      exact oodWitness_idealOf answer S.params S.air vk proof publicValues (by omega) hqne hood hb
    have hz : (prefixTranscript S (C 1) (B 1) (Sm 1)).zeta = T.zeta := by
      rw [hT]
      show extAt (Sm 1 1) (challengeOffset S.params.oodPowBits) =
        extAt (smp 1) (challengeOffset S.params.oodPowBits)
      rw [hSk 1 1 le_rfl]
    rw [roundBadAt, ite_eq_right (by omega), ite_eq_left rfl,
      prefixTranscript_trace S (hBk 1 0 (by omega)) (htraceS 1 (by omega)),
      prefixTranscript_quotient S (hBk 1 1 le_rfl) (hquotS 1 le_rfl (by omega)), hαeq, hz,
      ← hT] at h
    exact fun hzb ↦ h ⟨hpow, hzb⟩
  -- the batching round
  have ha : ¬ BatchBad S δ δ' T.trace T.alpha T.quotient T.zeta T.openings T.batch := by
    have h := hbad 2 (by omega)
    have hpow : S.params.batchPowBits ≠ 0 → CompPoly.CanonicalNat.toNat
        ((smp 2).toList.getD 0 0) % 2 ^ S.params.batchPowBits = 0 := fun hb ↦ by
      rw [hsmp]
      exact batchWitness_idealOf answer S.params S.air vk proof publicValues hK hqne htn hshape hbc
        hb
    have hz : (prefixTranscript S (C 2) (B 2) (Sm 2)).zeta = T.zeta := by
      rw [hT]
      show extAt (Sm 2 1) (challengeOffset S.params.oodPowBits) =
        extAt (smp 1) (challengeOffset S.params.oodPowBits)
      rw [hSk 2 1 (by omega)]
    have hb : (prefixTranscript S (C 2) (B 2) (Sm 2)).batch = T.batch := by
      rw [hT]
      show extAt (Sm 2 2) (challengeOffset S.params.batchPowBits) =
        extAt (smp 2) (challengeOffset S.params.batchPowBits)
      rw [hSk 2 2 le_rfl]
    have ho : (prefixTranscript S (C 2) (B 2) (Sm 2)).openings = T.openings := by
      rw [hT]
      show openingsAt S ((B 2 2).drop (pcsSeedS S).length) =
        openingsAt S ((blk 2).drop (pcsSeedS S).length)
      rw [hBk 2 2 le_rfl]
    rw [roundBadAt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl,
      prefixTranscript_trace S (hBk 2 0 (by omega)) (htraceS 2 (by omega)),
      prefixTranscript_quotient S (hBk 2 1 (by omega)) (hquotS 2 (by omega) (by omega)), hαeq,
      hz, hb, ho, ← hT] at h
    exact fun hbb ↦ h ⟨hpow, hbb⟩
  obtain ⟨-, hfp⟩ := nonempty_of_verify S (idealOf answer) vk proof publicValues hdb hok
  -- the folds
  have hfolds : ∀ f : Fin (S.lastFold + 1), ¬ FoldBad S δ loss f T.fri (T.betas f) := by
    intro f
    have hf := f.isLt
    have h := hbad (3 + f.val) (by omega)
    rw [roundBadAt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      dite_eq_left (by omega)] at h
    have hfin : (⟨3 + f.val - 3, by omega⟩ : Fin (S.lastFold + 1)) = f := Fin.ext (by simp)
    rw [hfin] at h
    have hpow : S.params.commitPowBits ≠ 0 → CompPoly.CanonicalNat.toNat
        ((smp (3 + f.val)).toList.getD 0 0) % 2 ^ S.params.commitPowBits = 0 := fun hb ↦ by
      rw [hsmp]
      exact commitWitness_idealOf answer S.params S.air vk proof publicValues (le_refl _) _
        (heights_openingRounds S.params S.air vk proof _) st hqne htn hshape hfriOk f.val (by omega)
        hb
    have h' := fun hfb ↦ h ⟨hpow, hfb⟩
    rw [foldBad_congr S δ loss f (prefixTranscript_committedWord S f
        (hBk _ _ le_rfl) (hfoldS _ f.val le_rfl (by omega) hf)),
      prefixTranscript_betas S f (hSk _ _ le_rfl), ← hT] at h'
    exact h'
  -- the query round
  have hq : ¬ QueryBad S δ loss T (powAt S (smp (4 + S.lastFold)))
      (queriesAt S (smp (4 + S.lastFold))) := by
    have h := hbad (4 + S.lastFold) (by omega)
    rw [roundBadAt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      dite_eq_right (by omega), ite_eq_left rfl] at h
    rwa [prefixTranscript_congr S (fun k hk ↦ hBk _ k hk) (fun k hk ↦ hSk _ k (by omega))
      (htraceS _ (by omega)) (hquotS _ (by omega) (by omega))
      (fun i hi ↦ hfoldS _ i (by omega) (by omega) hi), ← hT] at h
  -- binding commitments on answers changed outside the run
  obtain ⟨dstar, hdstar⟩ := exists_not_mem (logDigests (boundDigests S) L)
    ((length_logDigests_le (boundDigests S) (2 ^ (S.params.capHeight + 1)) Nat.one_le_two_pow
      (fun c i ↦ length_boundDigests_le S c i) L).trans_lt hsmall)
  set g' := fresh L answer dstar with hg'
  have hagree : ∀ e ∈ vlog, g' e.1 = answer e.1 := fun e he ↦
    fresh_of_mem L answer dstar _ (by
      rw [List.map_append]; exact List.mem_append_right _ (List.mem_map_of_mem he))
  have hok' : verifyWith (idealOf g') S.params S.air vk proof publicValues = .ok () := by
    rw [← evalWithAnswerFn_verifyWith, evalWithAnswerFn_congr answer g' _ hagree,
      evalWithAnswerFn_verifyWith]
    exact hok
  have hne : ∀ r ∈ logDigests (boundDigests S) L, r ≠ dstar := fun r hr he ↦ hdstar (he ▸ hr)
  have hbind : ∀ r ∈ logDigests (boundDigests S) L, Binding (logCache L) (idealOf g') r :=
    fun r hr ↦ binding_fresh answer L hconsL hclash dstar hdstar r (hne r hr)
  have hinitL : initCap ∈ logDigests (boundDigests S) L :=
    mem_logDigests (hkeys 0 (by omega)) hinit0
  -- a cap read off round `r` at its bound offset binds
  have hcapB : ∀ (c : Cap F) (r : Nat), r < blocks.length →
      (∀ i, c.toList.getD i 0 ∈ keyDigests (boundDigests S) (keyAt answer blocks r) ∨
        c.toList.getD i 0 = initCap) → CapBinding (logCache L) (idealOf g') c := by
    intro c r hr h i
    rcases h i with h | h
    · exact hbind _ (mem_logDigests (hkeys r hr) h)
    · rw [h]; exact hbind _ hinitL
  have htr : CapBinding (logCache L) (idealOf g') proof.traceCommit := by
    rw [← traceRoot_eq S answer hdb hok]; exact hcapB _ 0 (by omega) hcap0
  have hqu : CapBinding (logCache L) (idealOf g') proof.quotientCommit := by
    rw [← quotientRoot_eq S answer hdb hok]; exact hcapB _ 1 (by omega) hcap1
  -- the setup's key: its cap's entries are digests of the setup's queries, on which `g'` is
  -- `answer`
  have hsetupL : ∀ e ∈ tableQueryLog S.setupRo answer, g' e.1 = answer e.1 := fun e he ↦
    fresh_of_mem L answer dstar _ (by
      rw [List.map_append]; exact List.mem_append_left _ (List.mem_map_of_mem (hsetup e he)))
  have hvk' : preprocessedKeyWith (idealOf g') S.params S.air S.logN = vk := by
    rw [← evalWithAnswerFn_setupRo S g', evalWithAnswerFn_congr answer g' _ hsetupL,
      evalWithAnswerFn_setupRo, hvk]
  have hprepBind : ∀ k ∈ vk, CapBinding (logCache L) (idealOf g') k.commit := by
    intro k hk i
    by_cases hi : i < k.commit.size
    · obtain ⟨e, he, hd⟩ := exists_cap_mem S answer k (by rw [hvk]; exact hk) i hi
      rw [List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact hi), Array.getElem_toList,
        ← hd]
      exact hbind _ (List.mem_flatMap.mpr ⟨e, List.mem_append_left _ (hsetup e he),
        List.mem_cons_self⟩)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [Array.length_toList]; omega),
        Option.getD_none, zero_eq_initCap]
      exact hbind _ hinitL
  have hbcs := bcs S (logCache L) (idealOf g') vk proof publicValues hdb htr hqu
    (fun c hc ↦ by
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hc
      have hsize := (length_commits S answer hdb hok).2
      rw [← foldRoot_eq S answer hdb hok i (by omega)]
      exact hcapB _ (3 + i) (by omega) (hcapF i (by omega)))
    hprepBind
    (fun k hk ↦ committedColumn_setup S (logCache L) g' k (by rw [hvk']; exact hk)
      (hprepBind k hk))
    hok'
  have hext : extract S (logCache L) (idealOf g') vk proof publicValues = T := by
    rw [extract_eq_prefixTranscript S g' (logCache L) hdb hok', hT, hblk, hsmp]
    congr 1
    funext k
    exact samples_keyAt_fresh answer _ L dstar k
  dsimp only at hbcs
  rw [hext] at hbcs
  obtain ⟨hcheck, hdeg, hpow, hqueries⟩ := hbcs
  obtain ⟨-, -, -, -, -, hpowEq, hqEq⟩ := challenges_idealOf g' S.params S.air vk proof
    publicValues (le_refl _) htn hshape hfp hqne
    (size_commits_ne (idealOf answer) S.params proof.fri _ _ _ _ hfriOk)
  have h4 : 3 + (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length =
      4 + S.lastFold := by rw [hz]; omega
  rw [h4, hg'] at hpowEq hqEq
  dsimp only at hpowEq hqEq
  rw [samples_keyAt_fresh answer _ L dstar] at hpowEq hqEq
  have hpow' : CompPoly.CanonicalNat.toNat (powAt S (smp (4 + S.lastFold))) %
      2 ^ S.params.queryPowBits = 0 := by
    by_cases hb : S.params.queryPowBits = 0
    · simp only [hb, pow_zero, Nat.mod_one]
    · rw [powAt, ite_eq_right hb, hsmp]
      dsimp only
      rw [← hpowEq hb]
      exact hpow
  have hqueries' : ∀ j, queryPoint S (queriesAt S (smp (4 + S.lastFold)) j) ∈
      T.consistentQueries := fun j ↦ by
    rw [queriesAt, hsmp]
    dsimp only
    rw [← hqEq j.val j.isLt]
    exact hqueries j
  obtain ⟨P, hP, hsat⟩ := exists_satisfied_of_safe S publicValues δ δ' loss hδ' T _ _ hcheck hdeg
    hpow' hqueries' hα hζ ha hfolds hq
  -- the trace committed in the prover's queries is the run's
  have hhead : idx L (keyAt answer blocks 0) ≤ log.length := by
    by_cases hin : keyAt answer blocks 0 ∈ log.map Sigma.fst
    · have := List.idxOf_lt_length_of_mem hin
      rw [List.length_map] at this
      unfold idx
      rw [List.map_append, List.idxOf_append_of_mem hin]
      exact this.le
    · obtain ⟨rest, hrest⟩ := verifyWith_log_head answer (by unfold Iop.Setup.streamLen; omega)
        S.params S.air vk proof publicValues (by rw [run_idealLogged]; exact hok)
      rw [run_idealLogged] at hrest
      dsimp only at hrest
      rw [← hvlog] at hrest
      unfold idx
      rw [List.map_append, List.idxOf_append_of_notMem hin, hrest, List.map_cons,
        List.idxOf_cons_self, List.length_map, Nat.add_zero]
  have hlogL : CapSameUnder (logCache log) (logCache L) proof.traceCommit := by
    rw [← traceRoot_eq S answer hdb hok]
    intro idx k i
    have hmem : (capFrom (blocks.getD 0 []) (starkSeedS S).length
        (capSize S S.logSize)).toList.getD idx 0 ∈
          keyDigests (boundDigests S) (keyAt answer blocks 0) := by
      rcases hcap0 idx with h | h
      · exact h
      · rw [h]; exact hinit0
    have hnp := noPrediction_take hconsL hclash _ _ (hkeys 0 (by omega)) hmem log.length L.length
      hhead (by rw [hL, List.length_append]; omega)
    rw [List.take_length, hL, List.take_left' rfl] at hnp
    exact (Merkle.extractRow_eq_of_noPrediction _ _ _ hnp k i).symm
  have htraceT : committedTrace S log proof = T.trace := by
    rw [committedTrace_eq, hT, hblk]
    show traceWords S (logCache log) proof = fun j : Fin S.air.width ↦
      committedColumn S (logCache L)
      (capFrom ((inputs S.params S.air vk publicValues proof).getD 0 [])
        (starkSeedS S).length (capSize S S.logSize)) j.val
    rw [traceRoot_eq S answer hdb hok, ← committedColumn_congr S hlogL]
    rfl
  rw [← htraceT] at hP
  exact hfail _ ⟨P, hP.1, hP.2, rfl⟩ hsat

end Bad

end CompStark.Ni
