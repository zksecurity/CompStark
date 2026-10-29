/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.QueryBound
public import CompStark.Ni.BatchBcs
public import CompStark.Ni.BatchSetup

/-! # The batch verifier's oracle calls

FRI on rounds of mixed heights makes at most `n (1 + L + 2 G)` calls per query and round
(`Fri.costs_verifyPcs`, `Ni/QueryBound.lean`), so the batch verifier makes at most
`Batch.verifierCallsOf` calls on a proof of the instances it checks
(`Batch.isTotalQueryBound_verifyInstancesWith`), the lookup round's included, and at most
`Statement.verifierCalls` on a proof of any lengths (`isTotalQueryBound_verifyBatchWith`), which
`verifierCalls_le` bounds in closed form. The batch setup makes at most four calls per leaf of its
tree (`isTotalQueryBound_setupRo`).
-/

@[expose] public section
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

end CompStark.Iop.Batch.Setup

namespace CompStark.Batch
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Ni OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- Every matrix the verifier opens has an instance's height, and every instance's extended
trace is opened. -/
theorem mem_matHeights_batchRounds (P : Params) (instances : List (Instance F))
    (common : Common F) (proof : BatchProof F EF) (zeta : EF)
    (hsize : proof.opened.size = instances.length) (a : ℕ) :
    a ∈ matHeights P (batchRounds instances common proof zeta) ↔
      ∃ I ∈ instances, I.logN + P.logBlowup = a := by
  have hos : proof.opened.toList.length = instances.length := by rw [Array.length_toList, hsize]
  constructor
  · intro ha
    simp only [matHeights, List.mem_map, List.mem_flatMap] at ha
    obtain ⟨d, ⟨r, hr, hd⟩, rfl⟩ := ha
    unfold batchRounds at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | rfl | hr | hr
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      exact ⟨x.1, (List.of_mem_zip hx).1, rfl⟩
    · obtain ⟨x, hx, hd⟩ := List.mem_flatMap.mp hd
      obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hd
      exact ⟨x.1, (List.of_mem_zip hx).1, rfl⟩
    · split at hr
      · rw [List.mem_singleton] at hr
        subst hr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        exact ⟨x.1, (List.of_mem_zip (List.mem_filter.mp hx).1).1, rfl⟩
      · exact absurd hr List.not_mem_nil
    · split at hr
      · rw [List.mem_singleton] at hr
        subst hr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        exact ⟨x.1, (List.of_mem_zip (List.mem_filter.mp hx).1).1, rfl⟩
      · exact absurd hr List.not_mem_nil
  · rintro ⟨I, hI, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
    have hz : i < (instances.zip proof.opened.toList).length := by
      rw [List.length_zip, hos, Nat.min_self]; exact hi
    simp only [matHeights, List.mem_map, List.mem_flatMap]
    refine ⟨((⟨1, instances[i].logN⟩ : Domain F), traceOpenings instances[i].air
      (proof.opened.toList[i]'(by rw [hos]; exact hi)) zeta
      (zeta * Ext.ofBase (twoAdicGen instances[i].logN))),
      ⟨(proof.mainCommit, (instances.zip proof.opened.toList).map fun (I, o) ↦
        ((⟨1, I.logN⟩ : Domain F), traceOpenings I.air o zeta
          (zeta * Ext.ofBase (twoAdicGen I.logN)))), ?_, ?_⟩, rfl⟩
    · unfold batchRounds
      exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)
    · refine List.mem_map.mpr ⟨_, List.getElem_mem hz, ?_⟩
      simp only [List.getElem_zip]

theorem mem_extHeights (P : Params) (instances : List (Instance F)) (a : ℕ) :
    a ∈ extHeights P instances ↔ ∃ I ∈ instances, I.logN + P.logBlowup = a := by
  simp only [extHeights, List.mem_filter, List.mem_reverse, List.mem_range, List.any_eq_true,
    beq_iff_eq]
  constructor
  · exact fun h ↦ h.2
  · rintro ⟨I, hI, rfl⟩
    exact ⟨Nat.lt_succ_of_le ((le_foldl_max _ 0).2 _ (List.mem_map_of_mem hI)), I, hI, rfl⟩

theorem pairwise_extHeights (P : Params) (instances : List (Instance F)) :
    (extHeights P instances).Pairwise (· > ·) := by
  refine List.Pairwise.filter _ ?_
  rw [List.pairwise_reverse]
  exact List.pairwise_lt_range.imp fun h ↦ h

/-- The FRI verifier's heights are the instances' extended traces'. -/
theorem descHeights_batchRounds (P : Params) (instances : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (zeta : EF) (hsize : proof.opened.size = instances.length) :
    descHeights (matHeights P (batchRounds instances common proof zeta)) =
      extHeights P instances := by
  refine List.Pairwise.eq_of_mem_iff (r := (· > ·)) (pairwise_descHeights _)
    (pairwise_extHeights P instances) fun a ↦ ?_
  rw [mem_descHeights, mem_matHeights_batchRounds P instances common proof zeta hsize,
    mem_extHeights]

/-- The verifier opens at most `inputRoundsOf` committed rounds. -/
theorem length_batchRounds_le (instances : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (zeta : EF)
    (hprep : common.preprocessed.isSome = instances.any (0 < ·.air.preprocessedWidth))
    (hperm : proof.permutationCommit.isSome = hasLookups instances) :
    (batchRounds instances common proof zeta).length ≤ inputRoundsOf instances := by
  unfold batchRounds inputRoundsOf
  rw [← hprep, ← hperm]
  cases common.preprocessed <;> cases proof.permutationCommit <;>
    simp only [List.length_append, List.length_cons, List.length_nil, Option.isSome_none,
      Option.isSome_some, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem headD_le_of_mem {l : List ℕ} (hl : l.Pairwise (· > ·)) {h : ℕ} (hh : h ∈ l) :
    h ≤ l.headD 0 := by
  cases l with
  | nil => exact absurd hh List.not_mem_nil
  | cons a l =>
    rcases List.mem_cons.mp hh with rfl | hh
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hl hh).le

/-- **The verifier's oracle calls on a proof of the instances `instances`.** -/
theorem isTotalQueryBound_verifyInstancesWith {K : ℕ} (P : Params) (instances : List (Instance F))
    (common : Common F) (proof : BatchProof F EF) (pis : List (List F)) :
    IsTotalQueryBound (verifyInstancesWith (ideal F K) P instances common proof pis)
      (verifierCallsOf EF P instances) := by
  unfold verifyInstancesWith
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun hcount ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun hq ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun _ ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun _ ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun _ ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun hprep ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun hlk ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun _ ↦ ?_
  refine Iop.Batch.Setup.bound_unless _ _ _ _ fun _ ↦ ?_
  have hperm := (lookupShapeOk_spec P instances proof hlk).2.1
  simp only [Bool.and_eq_true, beq_iff_eq] at hcount hprep
  have hsize : proof.opened.size = instances.length := hcount.1.1.1.1
  set lc : ℕ := if hasLookups instances then 2 * Challenge.d EF + 1 else 0
  have hlp : Costs (H := ideal F K) (lookupPhase P instances proof : M _ (EF × EF)) lc
      fun _ ↦ True := by
    unfold lookupPhase lc
    cases hasLookups instances
    · exact costs_free_bind (costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦
        costs_free_bind (costs_observeList _) fun _ _ ↦
        costs_free_bind (costs_observeExts _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial
    · simp only [↓reduceIte]
      exact costs_bind_le (costs_checkWitness _ _) (b := 2 * Challenge.d EF)
        (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (b := Challenge.d EF)
          (costs_sampleExt (EF := EF)) (fun _ _ ↦
          costs_bind_le (b := 0) (costs_sampleExt (EF := EF)) (fun _ _ ↦
            costs_free_bind (costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦
            costs_free_bind (costs_observeList _) fun _ _ ↦
            costs_free_bind (costs_observeExts _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial)
            (by omega)) (by omega)) (by omega)
  dsimp only
  rw [ExceptT.run_bind]
  refine (isTotalQueryBound_bind (n₂ := 0) ((?_ : Costs (H := ideal F K) _
    (verifierCallsOf EF P instances) fun _ ↦ True) _).1 fun r ↦ ?_).mono (by omega)
  swap
  · rcases r with _ | ⟨⟨la, lb, alpha, zeta⟩, s⟩
    · trivial
    · dsimp only
      split
      · split
        · trivial
        · trivial
      · trivial
  set hs := extHeights P instances
  set G := hs.length - 1
  set c := 1 + hs.headD 0 + 2 * G
  set A := (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) (hs.headD 0) hs).length
  set V := Challenge.d EF + 2 + (Challenge.d EF + 1) * A +
    P.numQueries * (1 + (inputRoundsOf instances + A) * c)
  have hpcs : ∀ zeta : EF, Costs (H := ideal F K) (verifyPcs (ideal F K)
      P (batchRounds instances common proof zeta) proof.fri) V fun _ ↦ True := by
    intro zeta
    have hD := descHeights_batchRounds P instances common proof zeta hsize
    have hmem := mem_matHeights_batchRounds P instances common proof zeta hsize
    refine costs_mono (costs_verifyPcs P _ proof.fri (hs.headD 0) G
      (fun h hh ↦ ?_) hs (fun h hh ↦ ?_) (by omega)) ?_ fun _ h ↦ h
    · rw [← mem_descHeights, hD] at hh
      exact headD_le_of_mem (pairwise_extHeights P instances) hh
    · rw [← mem_descHeights, hD] at hh
      exact hh
    · rw [hD]
      have hlen := length_batchRounds_le instances common proof zeta hprep hperm
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen _)) 1)) _
  refine costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeExts _)
    fun _ _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
    costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeList _)
    fun _ _ ↦ costs_bind_le (b := Challenge.d EF + 1 + Challenge.d EF + V) hlp (fun _ _ ↦
    costs_bind_le (b := 1 + Challenge.d EF + V) costs_sampleExt (fun alpha _ ↦
      costs_free_bind (costs_observeList _) fun _ _ ↦ costs_bind_le (b := Challenge.d EF + V)
      (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (b := V)
        costs_sampleExt (fun zeta _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (a := V) (b := 0)
          (hpcs zeta) (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl) le_rfl)
      (by omega)) (by omega)) ?_
  simp only [V, c, G, A, hs, lc, verifierCallsOf]
  exact le_of_eq (by ring)

/-- Plonky3's schedule from a height `h` folds at most `h - logFinal` times: each fold is by at
least one bit. -/
theorem length_foldSchedule_le {m lf : ℕ} (hm : 0 < m) : ∀ (fuel h : ℕ) (rest : List ℕ),
    (h :: rest).Pairwise (· > ·) → (foldSchedule m lf fuel (h :: rest)).length ≤ h - lf
  | 0, _, _, _ => Nat.zero_le _
  | fuel + 1, h, rest, hp => by
    unfold foldSchedule
    split
    · exact Nat.zero_le _
    · rename_i hlt
      have hhead : rest.headD lf < h ∨ rest = [] := by
        cases rest with
        | nil => exact Or.inr rfl
        | cons a rest => exact Or.inl (List.rel_of_pairwise_cons hp List.mem_cons_self)
      have hla1 : 1 ≤ min (min (h - rest.headD lf) (h - lf)) m := by
        rcases hhead with hh | rfl
        · omega
        · simp only [List.headD_nil]; omega
      have hlaH : min (min (h - rest.headD lf) (h - lf)) m ≤ h - rest.headD lf :=
        (min_le_left _ _).trans (min_le_left _ _)
      rw [List.length_cons]
      split
      · rename_i heq
        cases rest with
        | nil => exact absurd heq (by simp only [List.head?_nil, reduceCtorEq, not_false_eq_true])
        | cons a rest =>
          have hrest := (List.pairwise_cons.mp hp).2
          have ha : a < h := List.rel_of_pairwise_cons hp List.mem_cons_self
          simp only [List.head?_cons, Option.some.injEq] at heq
          rw [← heq, List.tail_cons]
          have := length_foldSchedule_le (lf := lf) hm fuel a rest hrest
          omega
      · rename_i hne
        have hpw : ((h - min (min (h - rest.headD lf) (h - lf)) m) :: rest).Pairwise (· > ·) := by
          refine List.pairwise_cons.mpr ⟨fun x hx ↦ ?_, (List.pairwise_cons.mp hp).2⟩
          cases rest with
          | nil => exact absurd hx List.not_mem_nil
          | cons a rest =>
            have hne' : a ≠ h - min (min (h - a) (h - lf)) m := fun h' ↦ hne (by
              rw [List.head?_cons, List.headD_cons, ← h'])
            rw [List.headD_cons] at hlaH ⊢
            have ha : a < h := List.rel_of_pairwise_cons hp List.mem_cons_self
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · have := List.rel_of_pairwise_cons (List.pairwise_cons.mp hp).2 hx
              omega
        have := length_foldSchedule_le (lf := lf) hm fuel _ rest hpw
        omega

/-- The verifier's oracle calls on a proof of at most `k` instances of heights up to `2 ^ t`: at
most `d (2 ^ t / 2 ^ logFinalPolyLen)`-many folds and the tallest domain of `2 ^ (t + logBlowup)`
points, `k` heights. -/
theorem verifierCallsOf_le (P : Params) (instances : List (Instance F)) (t k : ℕ)
    (hk : instances.length ≤ k) (ht : ∀ I ∈ instances, I.logN ≤ t) (hm : 0 < P.maxLogArity) :
    verifierCallsOf EF P instances ≤
      (if hasLookups instances then 2 * Challenge.d EF + 1 else 0) + 3 * Challenge.d EF + 3 +
        (Challenge.d EF + 1) * (t - P.logFinalPolyLen) +
        P.numQueries * (1 + (t - P.logFinalPolyLen + inputRoundsOf instances) *
          (1 + (t + P.logBlowup) + 2 * (k - 1))) := by
  have hL : (extHeights P instances).headD 0 ≤ t + P.logBlowup := by
    cases h : extHeights P instances with
    | nil => exact Nat.zero_le _
    | cons a l =>
      have ha : a ∈ extHeights P instances := by rw [h]; exact List.mem_cons_self
      obtain ⟨I, hI, rfl⟩ := (mem_extHeights P instances a).mp ha
      have := ht I hI
      simp only [List.headD_cons]
      omega
  have hA : (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
      ((extHeights P instances).headD 0) (extHeights P instances)).length ≤
        t - P.logFinalPolyLen := by
    have hp := pairwise_extHeights P instances
    cases h : extHeights P instances with
    | nil => exact Nat.zero_le _
    | cons a l =>
      rw [h] at hp hL
      simp only [List.headD_cons] at hL ⊢
      have := length_foldSchedule_le (lf := P.logBlowup + P.logFinalPolyLen) hm a a l hp
      omega
  have hG : (extHeights P instances).length ≤ k := by
    have hsub : extHeights P instances ⊆ instances.map (·.logN + P.logBlowup) := fun a ha ↦ by
      obtain ⟨I, hI, rfl⟩ := (mem_extHeights P instances a).mp ha
      exact List.mem_map_of_mem hI
    have := List.Nodup.subperm (l₁ := extHeights P instances)
      ((pairwise_extHeights P instances).imp fun h ↦ Nat.ne_of_gt h) hsub
    have := this.length_le
    rw [List.length_map] at this
    omega
  unfold verifierCallsOf
  dsimp only
  gcongr <;> omega

end CompStark.Batch

namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Ni OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

theorem mem_lengthVectors : ∀ (k t : ℕ) (n : Fin k → ℕ), (∀ i, n i ≤ t) → n ∈ lengthVectors k t
  | 0, _, n, _ => by
    rw [lengthVectors, List.mem_singleton]
    exact funext fun i ↦ i.elim0
  | k + 1, t, n, h => by
    rw [lengthVectors, List.mem_flatMap]
    refine ⟨n 0, List.mem_range.mpr (Nat.lt_succ_of_le (h 0)), List.mem_map.mpr
      ⟨Fin.tail n, mem_lengthVectors k t _ fun i ↦ h i.succ, Fin.cons_self_tail n⟩⟩

theorem le_of_mem_lengthVectors : ∀ (k t : ℕ) (n : Fin k → ℕ), n ∈ lengthVectors k t →
    ∀ i, n i ≤ t
  | 0, _, _, _, i => i.elim0
  | k + 1, t, n, hn, i => by
    rw [lengthVectors, List.mem_flatMap] at hn
    obtain ⟨a, ha, hn⟩ := hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.cons_zero]; exact Nat.lt_succ_iff.mp (List.mem_range.mp ha)
    · rw [Fin.cons_succ]; exact le_of_mem_lengthVectors k t m hm j

theorem foldr_max_le (B : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ B) → l.foldr max 0 ≤ B
  | [], _ => Nat.zero_le _
  | x :: l, h => max_le (h x List.mem_cons_self)
      (foldr_max_le B l fun y hy ↦ h y (List.mem_cons_of_mem _ hy))

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

namespace Statement
variable (C : Statement F)

theorem hasLookups_instancesAt (n : Fin C.k → ℕ) :
    CompStark.Batch.hasLookups (C.instancesAt n) = C.hasLookups := by
  simp only [CompStark.Batch.hasLookups, instancesAt, hasLookups, keyInstances, List.ofFn_eq_map,
    List.any_map, Function.comp_def]

theorem inputRoundsOf_instancesAt (n : Fin C.k → ℕ) :
    CompStark.Batch.inputRoundsOf (C.instancesAt n) =
      CompStark.Batch.inputRoundsOf C.keyInstances := by
  unfold CompStark.Batch.inputRoundsOf
  rw [hasLookups_instancesAt, keyInstances, hasLookups_instancesAt]
  simp only [instancesAt, List.ofFn_eq_map, List.any_map, Function.comp_def]

variable (EF) in
/-- The verifier's oracle calls on proofs of any lengths, for FRI folding at least once per
round: at most `twoAdicity - logFinalPolyLen` folds, the tallest domain of
`2 ^ (twoAdicity + logBlowup)` points and `k` heights. -/
theorem verifierCalls_le (hm : 0 < C.params.maxLogArity) :
    C.verifierCalls EF ≤
      (if C.hasLookups then 2 * Challenge.d EF + 1 else 0) + 3 * Challenge.d EF + 3 +
        (Challenge.d EF + 1) * (twoAdicity F - C.params.logFinalPolyLen) +
        C.params.numQueries * (1 + (twoAdicity F - C.params.logFinalPolyLen +
          CompStark.Batch.inputRoundsOf C.keyInstances) *
          (1 + (twoAdicity F + C.params.logBlowup) + 2 * (C.k - 1))) := by
  refine foldr_max_le _ _ fun x hx ↦ ?_
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  have h := CompStark.Batch.verifierCallsOf_le (EF := EF) C.params (C.instancesAt n)
    (twoAdicity F) C.k (by rw [instancesAt, List.length_ofFn])
    (fun I hI ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
      exact le_of_mem_lengthVectors _ _ n hn i) hm
  rwa [hasLookups_instancesAt, inputRoundsOf_instancesAt] at h

variable (EF) in
/-- The setup's and the verifier's oracle calls on proofs of any lengths, for FRI folding at
least once per round (`verifierCalls_le`). -/
theorem verifierQueries_le (hm : 0 < C.params.maxLogArity) :
    C.verifierQueries EF ≤ C.setupQueries +
      ((if C.hasLookups then 2 * Challenge.d EF + 1 else 0) + 3 * Challenge.d EF + 3 +
        (Challenge.d EF + 1) * (twoAdicity F - C.params.logFinalPolyLen) +
        C.params.numQueries * (1 + (twoAdicity F - C.params.logFinalPolyLen +
          CompStark.Batch.inputRoundsOf C.keyInstances) *
          (1 + (twoAdicity F + C.params.logBlowup) + 2 * (C.k - 1)))) :=
  Nat.add_le_add_left (C.verifierCalls_le EF hm) _

/-- On a proof whose degree bits pass `keyOk`, against common data of the statement's lookups,
the verifier checks the statement's instances at the proof's lengths. -/
theorem instancesOf_eq (common : CompStark.Batch.Common F)
    (hl : common.lookups = List.ofFn C.lookups) (proof : CompStark.Batch.BatchProof F EF)
    (hdl : proof.degreeBits.toList.length = C.k) :
    CompStark.Batch.instancesOf C.airs common proof.degreeBits.toList =
      C.instancesAt (C.lengthsOf proof) := by
  unfold CompStark.Batch.instancesOf instancesAt airs lengthsOf
  rw [hl]
  refine List.ext_getElem (by simp only [List.length_map, List.length_zip, List.length_ofFn,
    hdl, Nat.min_self]) fun j h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by rw [hdl]; simpa only [List.length_ofFn] using h2)]

/-- `keyOk` checks one degree bit per AIR. -/
theorem length_degreeBits_of_keyOk (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF)
    (hkey : CompStark.Batch.keyOk C.airs common proof.degreeBits.toList = true) :
    proof.degreeBits.toList.length = C.k := by
  simp only [CompStark.Batch.keyOk, Bool.and_eq_true, beq_iff_eq] at hkey
  rw [hkey.1.2, airs, List.length_ofFn]

/-- **The batch verifier's oracle calls on a proof of any lengths**, against common data of the
statement's lookups. -/
theorem isTotalQueryBound_verifyBatchWith (common : CompStark.Batch.Common F)
    (hl : common.lookups = List.ofFn C.lookups) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F)) :
    IsTotalQueryBound (CompStark.Batch.verifyBatchWith (ideal F (C.streamLen EF)) C.params C.airs
      common proof pis) (C.verifierCalls EF) := by
  unfold CompStark.Batch.verifyBatchWith
  split
  · rename_i hkey
    rw [C.instancesOf_eq common hl proof (C.length_degreeBits_of_keyOk common proof hkey)]
    set n := C.lengthsOf proof
    by_cases hle : ∀ i, n i ≤ twoAdicity F
    · exact (CompStark.Batch.isTotalQueryBound_verifyInstancesWith C.params _ common proof
        pis).mono (Ni.le_foldr_max _ _ (List.mem_map_of_mem
          (mem_lengthVectors C.k _ n hle)))
    · refine (show IsTotalQueryBound (CompStark.Batch.verifyInstancesWith
          (ideal F (C.streamLen EF)) C.params (C.instancesAt n) common proof pis) 0
          from ?_).mono (Nat.zero_le _)
      push Not at hle
      obtain ⟨i, hi⟩ := hle
      unfold CompStark.Batch.verifyInstancesWith
      refine Setup.bound_unless _ _ _ _ fun _ ↦ ?_
      have hq : (List.all (C.instancesAt n) fun I ↦
          decide (I.logN + I.logQuotientChunks ≤ twoAdicity F)) = false := by
        rw [List.all_eq_false]
        exact ⟨⟨C.air i, n i, C.lookups i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, by
          simp only [decide_eq_true_eq]; omega⟩
      simp only [hq, Bool.false_eq_true, ↓reduceIte]
      trivial
  · trivial

/-- **The batch setup's oracle calls.** -/
theorem isTotalQueryBound_setupRo : IsTotalQueryBound (C.setupRo EF) C.setupQueries := by
  unfold setupRo CompStark.Batch.commonWith
  refine (isTotalQueryBound_bind (n₂ := 0) ?_ fun _ ↦ Merkle.isTotalQueryBound_pure _).mono
    (Nat.add_zero _).le
  unfold CompStark.Batch.preprocessedCapWith setupQueries
  split
  · trivial
  · rename_i hne
    have hhas : C.hasPreprocessed = true := by
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
    refine (isTotalQueryBound_bind (Merkle.mapM_bound _ _
      (isTotalQueryBound_injNodeWith _ _ _) _).1 fun _ ↦ Merkle.isTotalQueryBound_pure _).mono ?_
    rw [List.length_range, Nat.add_zero]
    have hc := Nat.min_le_right C.params.capHeight
      (CompStark.Batch.preprocessedLogHeight C.params C.keyInstances)
    generalize min C.params.capHeight
      (CompStark.Batch.preprocessedLogHeight C.params C.keyInstances) = c at hc ⊢
    calc 2 ^ c * (4 * 2 ^ (CompStark.Batch.preprocessedLogHeight C.params C.keyInstances - c) - 3)
        ≤ 2 ^ c * (4 * 2 ^ (CompStark.Batch.preprocessedLogHeight C.params C.keyInstances - c)) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 4 * 2 ^ CompStark.Batch.preprocessedLogHeight C.params C.keyInstances := by
          rw [Nat.mul_left_comm, ← Nat.pow_add, Nat.add_sub_cancel' hc]

end Statement

end CompStark.Iop.Batch
