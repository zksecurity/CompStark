/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.QueryBound
public import CompStark.Ni.BatchRun
public import CompStark.Merkle.Mixed
public import CompStark.Ni.BatchBcs

/-! # The batch verifier's oracle calls

A Merkle multi-opening of `n` queries into matrices of heights `2 ^ j ≤ 2 ^ L` of at most `G + 1`
distinct heights hashes at most `n` leaves, compresses at most `n` nodes per layer, and hashes and
compresses once more per node where it injects a shorter height
(`isTotalQueryBound_verifyMultiM_mixed`): at most `n (1 + L + 2 G)` calls. So FRI on rounds of
mixed heights makes at most so many calls per query and round (`costs_verifyFri_mixed`), and the
batch verifier at most `Setup.verifierCalls` (`isTotalQueryBound_verifyBatchWith`). The batch
setup makes at most four calls per leaf of its tree (`isTotalQueryBound_setupRo`).
-/

@[expose] public section
namespace CompStark.Merkle
open OracleSpec OracleComp

variable {ι : Type} {spec : OracleSpec ι} {F : Type} {d : Nat} [Zero F]

/-- A walk compresses at most once per node and level, and hashes and compresses once more per
node where it injects a group. -/
theorem walkM_bound_groups (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hh : ∀ xs, IsTotalQueryBound (hash xs) 1)
    (hc : ∀ a b, IsTotalQueryBound (compress a b) 1) (rows : List (List (List F))) :
    ∀ levels groups padded (nodes : List (Nat × Nat × Vector F d)) sibs,
      IsTotalQueryBound (walkM hash compress rows levels groups padded nodes sibs)
        (nodes.length * (levels + 2 * groups.length))
  | 0, _, _, _, _ => trivial
  | levels + 1, groups, padded, nodes, sibs => by
    rw [walkM]
    have hlev := levelM_bound compress hc nodes sibs
    refine (isTotalQueryBound_bind_of_mem_support hlev.1
      (suffixBound := nodes.length * (levels + 2 * groups.length))
      fun r hr ↦ ?_).mono (by rw [Nat.mul_add, Nat.mul_add, Nat.mul_succ]; omega)
    obtain ⟨ps, sibs'⟩ := r
    have hps : ps.length ≤ nodes.length := hlev.2 _ hr
    dsimp only
    rcases groups with _ | ⟨⟨h, is⟩, rest⟩
    · exact (walkM_bound_groups hash compress hh hc rows levels [] _ ps sibs').mono
        (by simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; nlinarith)
    · dsimp only
      split
      · have hm := mapM_bound (spec := spec) (fun (x : Nat × Nat × Vector F d) ↦ do
          return (x.1, x.2.1, ← compress x.2.2 (← hash (is.flatMap fun k ↦
            (rows.getD x.2.1 []).getD k [])))) 2
          (fun x ↦ (isTotalQueryBound_bind (hh _) fun _ ↦ isTotalQueryBound_bind (hc _ _)
            fun _ ↦ isTotalQueryBound_pure _).mono (by omega)) ps
        refine (isTotalQueryBound_bind_of_mem_support hm.1
          (suffixBound := ps.length * (levels + 2 * rest.length)) fun ps' hps' ↦ ?_).mono ?_
        · have := walkM_bound_groups hash compress hh hc rows levels rest (padded / 2) ps' sibs'
          rwa [hm.2 _ hps'] at this
        · simp only [List.length_cons]
          nlinarith
      · exact (walkM_bound_groups hash compress hh hc rows levels _ _ ps sibs').mono
          (by nlinarith)

/-- **A multi-opening of mixed heights.** A multi-opening of `n` queries into matrices of
heights `2 ^ j ≤ 2 ^ L`, among at most `G + 1` heights `hs`, makes at most `n (1 + L + 2 G)`
calls. -/
theorem isTotalQueryBound_verifyMultiM_mixed [DecidableEq F]
    (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hhash : ∀ xs, IsTotalQueryBound (hash xs) 1)
    (hcompress : ∀ a b, IsTotalQueryBound (compress a b) 1) (commit : Vector F d)
    (dims : List (Nat × Nat)) (L G : Nat) (hpow : ∀ x ∈ dims, ∃ j ≤ L, x.1 = 2 ^ j)
    (hs : List Nat) (hhs : ∀ x ∈ dims, x.1 ∈ hs) (hG : hs.length ≤ G + 1)
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Vector F d)) :
    IsTotalQueryBound (verifyMultiM hash compress commit dims indices rows sibs)
      (indices.length * (1 + L + 2 * G)) := by
  obtain ⟨keys, hk, hmem, hGeq⟩ := heightGroups_eq (dims.map (·.1))
  have hsub : keys ⊆ hs := fun h hh ↦ by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hmem h).mp hh)
    exact hhs x hx
  have hklen : keys.length ≤ hs.length :=
    (List.Nodup.subperm (hk.imp fun h ↦ Nat.ne_of_gt h) hsub).length_le
  unfold verifyMultiM
  rw [hGeq]
  rcases keys with _ | ⟨maxH, ks⟩
  · trivial
  have hmaxH : maxH ∈ dims.map (·.1) := (hmem maxH).mp List.mem_cons_self
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmaxH
  obtain ⟨j, hj, hxj⟩ := hpow x hx
  rw [← hxe, hxj] at *
  simp only [List.map_cons]
  rw [nextPowerOfTwo_two_pow, Nat.log2_two_pow]
  split
  · have hleaves := mapM_bound (spec := spec) (fun (iq : Nat × Nat) ↦ do
      return (iq.1, iq.2, ← hash (((List.range (dims.map (·.1)).length).filter
        ((dims.map (·.1)).getD · 0 == 2 ^ j)).flatMap fun k ↦ (rows.getD iq.2 []).getD k [])))
      1 (fun _ ↦ isTotalQueryBound_bind (hhash _) fun _ ↦ isTotalQueryBound_pure _)
      (frontier indices)
    have hf := length_frontier_le indices
    simp only [List.length_cons] at hklen
    refine (isTotalQueryBound_bind_of_mem_support hleaves.1
      (suffixBound := indices.length * (L + 2 * G)) fun leaves hl ↦ ?_).mono
      (by rw [Nat.mul_one]; nlinarith)
    refine (isTotalQueryBound_bind (walkM_bound_groups hash compress hhash hcompress rows j _ _
      leaves sibs) fun _ ↦ isTotalQueryBound_pure _).mono ?_
    rw [hleaves.2 _ hl, Nat.add_zero, List.length_map]
    exact Nat.mul_le_mul hf (by omega)
  · trivial

end CompStark.Merkle

namespace CompStark.Fri
open CompStark.Stark CompStark.RandomOracle CompStark.Ni OracleSpec OracleComp

variable {F : Type} {EF : Type} {K : Nat} [BaseField F] [Challenge F EF]

/-- A multi-opening of mixed heights costs at most `n (1 + L + 2 G)` calls. -/
theorem costs_checkMulti_mixed (commit : Digest F) (dims : List (Nat × Nat)) (L G : Nat)
    (hpow : ∀ x ∈ dims, ∃ j ≤ L, x.1 = 2 ^ j) (hs : List Nat) (hhs : ∀ x ∈ dims, x.1 ∈ hs)
    (hG : hs.length ≤ G + 1) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Digest F)) :
    Costs (checkMulti (ideal F K) commit dims indices rows sibs) (indices.length * (1 + L + 2 * G))
      fun _ ↦ True := fun s ↦ by
  refine ⟨?_, fun _ _ _ ↦ trivial⟩
  change IsTotalQueryBound ((ExceptT.lift (Merkle.verifyMultiM (ideal F K).hash
    (ideal F K).compress commit dims indices rows sibs) >>=
      fun a ↦ pure (a, s) : ExceptT String (OracleComp (spec F K)) _).run)
    (indices.length * (1 + L + 2 * G))
  simp only [ExceptT.run_bind, ExceptT.run_lift, bind_map_left, ExceptT.run_pure]
  simpa only [Nat.add_zero] using isTotalQueryBound_bind
    (Merkle.isTotalQueryBound_verifyMultiM_mixed _ _ (fun _ ↦ isTotalQueryBound_query _)
      (fun _ _ ↦ isTotalQueryBound_query _) commit dims L G hpow hs hhs hG indices rows sibs)
    fun x ↦ (show IsTotalQueryBound (pure (Except.ok (x, s)) : OracleComp (spec F K) _) 0
      from trivial)

/-- The input multi-openings of rounds of mixed heights: at most `n (1 + L + 2 G)` calls per
round. -/
theorem costs_verifyInputs_mixed (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF)) (L G : Nat)
    (hL : ∀ h ∈ matHeights P rounds, h ≤ L) (hs : List Nat)
    (hhs : ∀ h ∈ matHeights P rounds, h ∈ hs) (hG : hs.length ≤ G + 1) :
    Costs (verifyInputs (ideal F K) P logMax indices inputs rounds)
      (rounds.length * (indices.length * (1 + L + 2 * G))) fun _ ↦ True := by
  unfold verifyInputs
  refine costs_mono (costs_bind (a := 0)
    (b := rounds.length * (indices.length * (1 + L + 2 * G))) (costs_ensure _ _)
    fun _ _ ↦ costs_bind (b := 0) (costs_forIn_le _ _ _
    rounds.length (indices.length * (1 + L + 2 * G)) ?_ (fun _ ↦ True) trivial
    fun a ha b _ ↦ ?_) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) (by omega) fun _ _ ↦ trivial
  · rw [List.length_zip]; exact Nat.min_le_right _ _
  · obtain ⟨bo, commit, mats⟩ := a
    have hmat : ∀ mat ∈ mats, mat.1.logSize + P.logBlowup ∈ matHeights P rounds :=
      fun mat hm ↦ List.mem_map.mpr ⟨mat, List.mem_flatMap.mpr ⟨_, (List.of_mem_zip ha).2, hm⟩,
        rfl⟩
    dsimp only
    refine costs_mono (P := fun _ ↦ True) (costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_bind (costs_checkMulti_mixed _ _ L G ?_ (hs.map (2 ^ ·)) ?_
        (by rw [List.length_map]; exact hG) _ _ _) fun _ _ ↦
      costs_bind (costs_ensure _ _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) ?_
      fun _ _ ↦ trivial
    · intro x hx
      obtain ⟨mat, hm, rfl⟩ := List.mem_map.mp hx
      exact ⟨_, hL _ (hmat mat hm), rfl⟩
    · intro x hx
      obtain ⟨mat, hm, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map_of_mem (hhs _ (hmat mat hm))
    · rw [List.length_map]
      omega

/-- FRI's oracle calls after `α` on rounds of mixed heights: `d + 1` per fold, one for the query
grinding, and per query its index, its input openings and its folds' openings. -/
theorem costs_verifyFri_mixed (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF))
    (alpha : EF) (L G : Nat) (hL : ∀ h ∈ matHeights P rounds, h ≤ L) (hs : List Nat)
    (hhs : ∀ h ∈ matHeights P rounds, h ∈ hs) (hG : hs.length ≤ G + 1) :
    Costs (verifyFri (ideal F K) P proof rounds alpha)
      (1 + (Challenge.d EF + 1) * (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
          ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length +
        P.numQueries * (1 + (rounds.length + (foldSchedule P.maxLogArity
          (P.logBlowup + P.logFinalPolyLen) ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length) * (1 + L + 2 * G))) fun _ ↦ True := by
  have hmax : (descHeights (matHeights P rounds)).headD 0 ≤ L := by
    rcases hD : descHeights (matHeights P rounds) with _ | ⟨a, t⟩
    · exact Nat.zero_le _
    · exact hL a ((mem_descHeights _ a).mp (hD ▸ List.mem_cons_self))
  unfold verifyFri
  dsimp only
  change Costs (ensure _ _ >>= fun _ ↦ ensure _ _ >>= fun _ ↦
    ensure ((descHeights (matHeights P rounds)).headD 0 ≤ twoAdicity F) _ >>= _) _ _
  set A := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
    ((descHeights (matHeights P rounds)).headD 0) (descHeights (matHeights P rounds))
  set N := P.numQueries
  set c := 1 + L + 2 * G
  refine costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_free_bind (costs_observeList _) fun _ _ ↦ costs_ensure_bind fun hcs ↦ ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hcs
  -- the commit loop
  refine costs_bind_le (b := 1 + N * (1 + (rounds.length + A.length) * c))
    (costs_forIn_le _ _ _ A.length (Challenge.d EF + 1) ?_ (fun _ ↦ True) trivial
      fun _ _ _ _ ↦ ?_) (fun betas _ ↦ ?_) (le_of_eq (by ring))
  · rw [List.length_zip, Array.length_toList, hcs.1]; exact Nat.min_le_left _ _
  · exact costs_free_bind (costs_observeList _) fun _ _ ↦ costs_bind_le (costs_checkWitness _ _)
      (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind costs_sampleExt fun _ _ ↦
        costs_pure _ (fun _ ↦ True) trivial) (by omega)
  -- the final polynomial, the query grinding and the indices
  refine costs_free_bind (costs_observeExts _) fun _ _ ↦ costs_bind_le (costs_checkWitness _ _)
    (b := N * (1 + (rounds.length + A.length) * c)) (fun _ _ ↦ costs_ensure_bind fun _ ↦ ?_)
    le_rfl
  refine costs_bind_le (costs_mapM _ 1 (fun _ ↦ costs_sampleBits _) _)
    (b := rounds.length * (N * c) + A.length * (N * c)) (fun indices hind ↦ ?_)
    (by rw [List.length_range]; exact le_of_eq (by ring))
  rw [List.length_range] at hind
  -- the input openings
  refine costs_bind_le (costs_verifyInputs_mixed P _ indices _ rounds L G hL hs hhs hG)
    (b := A.length * (N * c)) (fun _ _ ↦ ?_) (by rw [hind])
  -- the queries' folds and the commit-phase openings
  refine costs_free_bind (costs_mapM _ 0 (fun iq ↦ ?_) _) fun groups hg ↦ ?_
  · refine costs_bind_zero (costs_reduceQuery _ _ _ _ _ _) fun _ ↦
      costs_bind_zero (costs_foldQuery _ _ _ _ _ _ _ _) fun _ ↦ ?_
    costs_zero
  rw [List.length_zipIdx, hind] at hg
  refine costs_bind_le (b := 0) (costs_forIn_le _ _ _ A.length (N * c) ?_
    (fun logH ↦ logH ≤ L) hmax fun x _ logH hlog ↦ ?_)
    (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl
  · rw [List.length_zip, List.length_zipIdx]; exact Nat.min_le_right _ _
  obtain ⟨⟨cm, o⟩, la, i⟩ := x
  dsimp only
  refine costs_bind_le (costs_checkMulti_mixed _ _ (logH - la) 0
    (fun y hy ↦ ⟨logH - la, le_rfl, by rw [List.mem_singleton.mp hy]⟩) [2 ^ (logH - la)]
    (fun y hy ↦ by rw [List.mem_singleton.mp hy]; exact List.mem_singleton_self _) le_rfl _ _ _)
    (b := 0)
    (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_pure _ _ (by simp only [ForInStep.value]; omega))
    ?_
  rw [List.length_map, List.length_map, hg, Nat.add_zero]
  exact Nat.mul_le_mul_left _ (by omega)

theorem costs_verifyPcs_mixed (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF)
    (L G : Nat) (hL : ∀ h ∈ matHeights P rounds, h ≤ L) (hs : List Nat)
    (hhs : ∀ h ∈ matHeights P rounds, h ∈ hs) (hG : hs.length ≤ G + 1) :
    Costs (verifyPcs (ideal F K) P rounds proof)
      (Challenge.d EF + 2 + (Challenge.d EF + 1) * (foldSchedule P.maxLogArity
          (P.logBlowup + P.logFinalPolyLen) ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length +
        P.numQueries * (1 + (rounds.length + (foldSchedule P.maxLogArity
          (P.logBlowup + P.logFinalPolyLen) ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length) * (1 + L + 2 * G))) fun _ ↦ True := by
  unfold verifyPcs
  refine costs_ensure_bind fun _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
    costs_free_bind (costs_forIn_zero _ _ _ fun _ _ ↦ costs_bind_zero (costs_forIn_zero _ _ _
      fun _ _ ↦ costs_bind_zero (costs_forIn_zero _ _ _ fun _ _ ↦ costs_bind_zero
        (costs_observeExts _) fun _ ↦ costs_pure _ (fun _ ↦ True) trivial) fun _ ↦
          costs_pure _ (fun _ ↦ True) trivial) fun _ ↦ costs_pure _ (fun _ ↦ True) trivial)
      fun _ _ ↦ costs_bind_le (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦
        costs_bind costs_sampleExt fun alpha _ ↦
          costs_verifyFri_mixed P proof rounds alpha L G hL hs hhs hG)
      (by omega)

end CompStark.Fri

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Ni OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (S : Setup EF)

/-- A failed `unless` check makes no calls; a passed one costs what the rest costs. -/
theorem bound_unless {ι : Type} {spec : OracleSpec ι} {α : Type} (b : Bool) (e : String)
    (k : PUnit → ExceptT String (OracleComp spec) α) (n : Nat)
    (h : b = true → IsTotalQueryBound (k PUnit.unit).run n) :
    IsTotalQueryBound (have jp := k
      if b = true then jp PUnit.unit else (throw e >>= fun r ↦ jp r) :
        ExceptT String (OracleComp spec) α).run n := by
  cases b
  · show IsTotalQueryBound (pure (Except.error e) : OracleComp spec _) n
    trivial
  · exact h rfl

theorem isTotalQueryBound_verifyBatchWith (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F)) :
    IsTotalQueryBound (CompStark.Batch.verifyBatchWith (ideal F S.streamLen) S.params S.instances
      common proof pis) S.verifierCalls := by
  unfold CompStark.Batch.verifyBatchWith
  refine bound_unless _ _ _ _ fun hcount ↦ ?_
  refine bound_unless _ _ _ _ fun hdb ↦ ?_
  refine bound_unless _ _ _ _ fun hq ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  refine bound_unless _ _ _ _ fun hprep ↦ ?_
  refine bound_unless _ _ _ _ fun _ ↦ ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hcount hprep
  have hsize : proof.opened.size = S.k := by rw [hcount.1, length_instances]
  dsimp only
  rw [ExceptT.run_bind]
  refine (isTotalQueryBound_bind (n₂ := 0) ((?_ : Costs (H := ideal F S.streamLen) _
    S.verifierCalls fun _ ↦ True) _).1 fun r ↦ ?_).mono (by omega)
  swap
  · rcases r with _ | ⟨⟨alpha, zeta⟩, s⟩
    · trivial
    · dsimp only
      split
      · trivial
      · trivial
  set G := S.friHeights.length
  set c := 1 + S.logTop + 2 * G
  set V := Challenge.d EF + 2 + (Challenge.d EF + 1) * S.friRounds.numFolds +
    S.params.numQueries * (1 + (S.inputRounds + S.friRounds.numFolds) * c)
  have hpcs : ∀ zeta : EF, Costs (H := ideal F S.streamLen) (verifyPcs (ideal F S.streamLen)
      S.params (CompStark.Batch.batchRounds S.instances common proof zeta) proof.fri) V
      fun _ ↦ True := by
    intro zeta
    have hD := descHeights_batchRounds S common proof zeta hsize
    have hmem := mem_matHeights S common proof zeta hsize
    refine costs_mono (costs_verifyPcs_mixed S.params _ proof.fri S.logTop G
      (fun h hh ↦ ?_) (S.logTop :: S.friHeights) (fun h hh ↦ ?_) le_rfl) ?_ fun _ h ↦ h
    · obtain ⟨i, rfl⟩ := (hmem h).mp hh
      exact logTop_ge S i
    · obtain ⟨i, rfl⟩ := (hmem h).mp hh
      rw [← hD, mem_descHeights]
      exact (hmem _).mpr ⟨i, rfl⟩
    · rw [hD, List.headD_cons]
      have hA : (foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
          S.logTop (S.logTop :: S.friHeights)).length = S.friRounds.numFolds := by
        rw [Nat.add_comm S.params.logBlowup, ← FriRounds.arities_schedule _ _
          (fun _ _ ↦ (0 : Challenge.Spec EF)), FriRounds.length_arities]
        rfl
      have hlen : (CompStark.Batch.batchRounds S.instances common proof zeta).length ≤
          S.inputRounds := by
        rw [batchRounds_cases, inputRounds]
        cases hc : common.preprocessed with
        | none => simp only [List.length_append, List.length_cons, List.length_nil]; split <;> omega
        | some root =>
          have hhas : S.hasPreprocessed = true := by
            rw [hc] at hprep
            rw [hasPreprocessed, List.ofFn_eq_map, List.any_map]
            rw [Iop.Batch.Setup.instances, List.ofFn_eq_map, List.any_map] at hprep
            exact hprep.symm
          simp only [hhas, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
          omega
      rw [hA]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen _)) 1)) _
  refine costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeExts _)
    fun _ _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
    costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeList _)
    fun _ _ ↦ costs_bind_le (b := 1 + Challenge.d EF + V) costs_sampleExt (fun alpha _ ↦
      costs_free_bind (costs_observeList _) fun _ _ ↦ costs_bind_le (b := Challenge.d EF + V)
      (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (b := V)
        costs_sampleExt (fun zeta _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (a := V) (b := 0)
          (hpcs zeta) (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl) le_rfl)
      (by omega)) ?_
  simp only [V, c, G, verifierCalls, openingQueries]
  exact le_of_eq (by ring)

/-- A node of the batch setup's tree at level `l` costs at most `4 · 2 ^ l - 3` calls: a hash per
leaf, a compression per node, and a hash and a compression where a node injects. -/
theorem isTotalQueryBound_injNodeWith {K : Nat} (ms : List (Merkle.Matrix F)) (k : Nat) :
    ∀ l i, IsTotalQueryBound (CompStark.Batch.injNodeWith (ideal F K) ms k l i) (4 * 2 ^ l - 3)
  | 0, i => isTotalQueryBound_query _
  | l + 1, i => by
    have ih := isTotalQueryBound_injNodeWith (K := K) ms k l
    have hp := Nat.one_le_two_pow (n := l)
    rw [CompStark.Batch.injNodeWith]
    refine (isTotalQueryBound_bind (ih _) fun _ ↦ isTotalQueryBound_bind (ih _) fun _ ↦
      isTotalQueryBound_bind (n₂ := 2) (isTotalQueryBound_query _) fun _ ↦ ?_).mono ?_
    · split
      · refine isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) ?_ fun _ ↦ ?_
        · exact isTotalQueryBound_query _
        · exact isTotalQueryBound_query _
      · trivial
    · rw [Nat.pow_succ]
      omega

/-- **The batch setup's oracle calls.** -/
theorem isTotalQueryBound_setupRo : IsTotalQueryBound S.setupRo S.setupQueries := by
  unfold setupRo CompStark.Batch.commonWith setupQueries
  split
  · trivial
  · rename_i hne
    have hhas : S.hasPreprocessed = true := by
      rw [List.isEmpty_iff] at hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨I, hI, hf⟩ := List.mem_filterMap.mp hx
      split at hf
      · simp only [reduceCtorEq] at hf
      · rename_i hpw
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (show _ ∈ List.ofFn _ from hI)
        exact List.any_eq_true.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩,
          decide_eq_true (Nat.pos_of_ne_zero hpw)⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hhas)]
    refine (isTotalQueryBound_bind (isTotalQueryBound_injNodeWith _ _ _ 0)
      fun _ ↦ Merkle.isTotalQueryBound_pure _).mono (by omega)

end CompStark.Iop.Batch.Setup
