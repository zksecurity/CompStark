/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Fri
public import CompStark.Complete.Deep
public import CompStark.Complete.Quotient
public import CompStark.Stark.Verifier
public import CompStark.Stark.Prover

/-! # The specification prover's proofs verify

The STARK layer of completeness: the verifier replays the prover's transcript. It observes the
same domain separator, commitments and public values, checks the same grinding witnesses, so it
samples the same `α` and `ζ`, and `ζ` off the base field is off the trace domain; `verifyPcs`
observes the same opened values as `openPcs` and then accepts `proveFri`'s proof
(`verifyFri_proveFri`), whose input openings are honest multi-openings (`verifyInputs_honest`)
and whose inputs are the batched quotients of the honest openings (`reduceQuery_honest`).
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri CompStark.Complete

variable {F : Type} [BaseField F]
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

variable {EF : Type} [Challenge F EF]

/-! ### Before hashing

The trace's extension, the opened values and the out-of-domain check need no hash. -/

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- The trace's extension. -/
def hExt : Mat F := ldeRef logN P.logBlowup gen A.width trace

theorem height_hExt (hin : Fits P A logN trace) :
    (hExt P A logN trace).height = 2 ^ (logN + P.logBlowup) := by
  obtain ⟨ps, hl, -⟩ := trace_lde P A logN trace hin
  exact hl.2.1

/-- The preprocessed trace's extension. -/
def hPrepExt : Mat F := ldeRef logN P.logBlowup gen A.preprocessedWidth A.preprocessed

theorem height_hPrepExt (hin : Fits P A logN trace) :
    (hPrepExt P A logN).height = 2 ^ (logN + P.logBlowup) := by
  obtain ⟨ps, hl, -⟩ := prep_lde P A logN trace hin
  exact hl.2.1

end Honest

theorem observeExts_append (t : Transcript F 24) (a b : List EF) :
    t.observeExts (a ++ b) = (t.observeExts a).observeExts b := by
  simp only [Transcript.observeExts, List.foldl_append]

theorem forM_observeExts (ov : List (Array EF)) (t : Transcript F 24) :
    (ov.forM fun ys ↦ pObserveExts ys.toList).run t =
      ((), t.observeExts (ov.flatMap (·.toList))) := by
  induction ov generalizing t with
  | nil => rfl
  | cons ys ov ih =>
    show (pObserveExts ys.toList >>= fun _ ↦ ov.forM fun ys ↦ pObserveExts ys.toList).run t = _
    rw [prun_bind, List.flatMap_cons, observeExts_append]
    exact ih _

/-- The values the specification opens of a matrix at its points. -/
def openedOf (b : Nat) (x : Mat F × List EF) : List (Array EF) := x.2.map (Fri.openedAt b x.1)

theorem flatMap_zip_openedOf (b : Nat) (m : Mat F) (zs : List EF) :
    ((zs.zip (openedOf b (m, zs))).map fun y ↦ (y.1, y.2.toList)).flatMap (·.2) =
      (openedOf b (m, zs)).flatMap (·.toList) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [openedOf, List.map_cons, List.zip_cons_cons, List.flatMap_cons] at ih ⊢
    rw [ih]

theorem mem_zip_map {α β : Type} (f : α → β) (zs : List α) :
    ∀ y ∈ zs.zip (zs.map f), y.1 ∈ zs ∧ y.2 = f y.1 := by
  induction zs with
  | nil => intro y hy; simp only [List.map_nil, List.zip_nil_right, List.not_mem_nil] at hy
  | cons z zs ih =>
    intro y hy
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := ih y hy
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- An LDE opened at points outside the base field is an honest item of the batched quotients. -/
theorem honestItem_of (b h : Nat) (m : Mat F) (zs : List EF) (ps : List (Polynomial F))
    (hm : CompStark.Mat.IsLde b h m ps) (hzs : ∀ z ∈ zs, Ext.OutsideBase z) :
    Deep.HonestItem b h (m, zs.zip (openedOf b (m, zs))) := by
  refine ⟨ps, hm, fun y hy ↦ ?_⟩
  obtain ⟨hz, hy2⟩ := mem_zip_map (Fri.openedAt b m) zs y hy
  obtain ⟨hs, hv⟩ := openedAt_isLde b h m ps y.1 hm (hzs _ hz)
  exact ⟨hzs _ hz, hy2 ▸ hs, fun j hj ↦ hy2 ▸ hv j hj⟩

/-- The out-of-domain check of `verify`, after the transcript. -/
def verifyCheck (A : Air F) (proof : Proof F EF) (pis : List F)
    (x : (EF × EF) × Transcript F 24) : ExceptT String Id Unit :=
  unless checkConstraints A pis proof.opened proof.degreeBits x.1.2 x.1.1
      (recompose (chunkDomains proof.degreeBits (A.logQuotientChunks proof.degreeBits))
        proof.opened.quotientChunks.toList x.1.2) do
    throw "out-of-domain evaluation mismatch"

theorem verifyCheck_ok (A : Air F) (proof : Proof F EF) (pis : List F)
    (x : (EF × EF) × Transcript F 24)
    (h : checkConstraints A pis proof.opened proof.degreeBits x.1.2 x.1.1
      (recompose (chunkDomains proof.degreeBits (A.logQuotientChunks proof.degreeBits))
        proof.opened.quotientChunks.toList x.1.2) = true) :
    verifyCheck A proof pis x = pure () := by
  unfold verifyCheck
  rw [h]
  rfl

theorem forM_mats (b : Nat) (ms : List (Mat F × List EF)) (t : Transcript F 24) :
    ((ms.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))).forM
        fun x ↦ x.1.forM fun ys ↦ pObserveExts ys.toList : PM F 24 Unit).run t =
      ((), t.observeExts ((ms.flatMap (openedOf b)).flatMap (·.toList))) := by
  induction ms generalizing t with
  | nil => rfl
  | cons x ms ih =>
    simp only [List.map_cons, List.forM]
    rw [prun_bind, forM_observeExts, ih, List.flatMap_cons,
      List.flatMap_append, observeExts_append]

theorem logSize_openingRounds (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (zeta : EF) :
    ∀ x ∈ (openingRounds A vk proof zeta).flatMap (·.2), x.1.logSize = proof.degreeBits := by
  intro x hx
  simp only [openingRounds, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.flatMap_append] at hx
  rcases hx with (rfl | ⟨ch, -, rfl⟩) | hx
  · rfl
  · rfl
  · unfold preprocessedRound at hx
    split at hx
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hx
      rw [hx]
    · exact absurd hx List.not_mem_nil

theorem powTwo_ne_one {zeta : EF} (hz : Ext.OutsideBase zeta) {n : Nat} (hn : n ≤ twoAdicity F) :
    (Ext.powTwo zeta n - 1 != 0) = true := by
  rw [bne_iff_ne, ne_eq]
  intro he
  have hne := pow_ne_of_outsideBase hz (specDomain n hn) one_ne_zero
  rw [map_one, one_pow] at hne
  apply hne
  have h2 := congrArg Challenge.toSpec he
  rw [Challenge.toSpec_sub, Ext.toSpec_powTwo, Challenge.toSpec_one, Challenge.toSpec_zero,
    sub_eq_zero] at h2
  exact h2

theorem grind_canonical (t : Transcript F 24) (bits : Nat) :
    (bits != 0 || (t.grind bits).1 == 0) = true := by
  by_cases h : bits = 0
  · subst h
    simp only [Transcript.grind, ↓reduceIte, beq_self_eq_true, Bool.or_true]
  · rw [bne_iff_ne.mpr h, Bool.true_or]

variable [Poseidon2Field F]

/-- A round's matrices with their opened values at their points. -/
def roundItems (b : Nat) (r : OpenRound (specBackend EF)) :
    List (List (Array EF) × Mat F × List (EF × Array EF)) :=
  r.2.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))

/-- A round's opened values. -/
def roundOpened (b : Nat) (r : OpenRound (specBackend EF)) : List (Array EF) :=
  r.2.flatMap (openedOf b)

/-! ### The prover's run, step by step -/

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- The preprocessed trace's extension and commitment, if the AIR has preprocessed columns. -/
def hPrep : Option (Mat F × Committed F) := setupWith (specBackend EF) P A logN

theorem hPrep_eq : hPrep EF P A logN = if A.preprocessedWidth = 0 then none else
    some (hPrepExt P A logN, Committed.ofMats hashF compF [hPrepExt P A logN]) := rfl

/-- The transcript after the trace and preprocessed commitments and the public values. -/
def hTA : Transcript F 24 :=
  (((Poseidon2.initTranscript.observeList (starkSeedOf EF P A logN)).observeList
    (Committed.ofMats hashF compF [hExt P A logN trace]).root.toList).observeList
    (((hPrep EF P A logN).map fun x ↦ ((specBackend EF).root x.2).toList).getD [])).observeList
    pis

/-- The constraint-folding challenge. -/
def hAlpha : EF := ((hTA EF P A logN trace pis).sampleExtValue : EF)

/-- The quotient's chunks' extensions. -/
def hChunks : List (Mat F) :=
  let lc := A.logQuotientChunks logN
  let qs := quotientOfLde A pis logN lc (hExt P A logN trace) ((hPrep EF P A logN).map (·.1))
    (hAlpha EF P A logN trace pis)
  (List.range (2 ^ lc)).map fun c ↦
    ldeRef logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ lc) c (2 ^ logN))

/-- The transcript after the quotient commitment. -/
def hTC : Transcript F 24 :=
  (Transcript.sampleExtState EF ((hTA EF P A logN trace pis))).observeList
    (Committed.ofMats hashF compF (hChunks EF P A logN trace pis)).root.toList

/-- The out-of-domain grinding: its witness and the transcript after it. -/
def hOod : F × Transcript F 24 := (hTC EF P A logN trace pis).grind P.oodPowBits

/-- The out-of-domain point. -/
def hZeta : EF := ((hOod EF P A logN trace pis).2.sampleExtValue : EF)

theorem commitAndSample_run :
    (commitAndSample (specBackend EF) P A logN (hPrep EF P A logN) trace pis).run
      Poseidon2.initTranscript =
      ((hExt P A logN trace, Committed.ofMats hashF compF [hExt P A logN trace],
        hChunks EF P A logN trace pis, Committed.ofMats hashF compF (hChunks EF P A logN trace pis),
        hZeta EF P A logN trace pis, (hOod EF P A logN trace pis).1),
        Transcript.sampleExtState EF (hOod EF P A logN trace pis).2) := rfl

theorem outOfDomainPoint_eq :
    outOfDomainPoint EF P A logN trace pis = hZeta EF P A logN trace pis :=
  rfl

end Honest

/-! ### Opening -/

theorem forM_rounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) (t : Transcript F 24) :
    ((rounds.map fun r ↦ r.2.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))).forM
        fun os ↦ os.forM fun x ↦ x.1.forM fun ys ↦ pObserveExts ys.toList : PM F 24 Unit).run t =
      ((), t.observeExts
        ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf b)).flatMap (·.toList))) := by
  induction rounds generalizing t with
  | nil => rfl
  | cons r rounds ih =>
    simp only [List.map_cons, List.forM]
    rw [prun_bind]
    erw [forM_mats]
    rw [ih, List.flatMap_cons,
      List.flatMap_append, observeExts_append]

/-- The claimed evaluation counts of opened values: per round, per matrix, per point. -/
def countsOf (opened : List (List (List (Array EF) × Mat F × List (EF × Array EF)))) :
    List (List (List Nat)) :=
  opened.map (·.map fun x ↦ x.1.map (·.size))

theorem openPcs_run (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (t : Transcript F 24) :
    (openPcs (specBackend EF) P rounds).run t =
      let opened := rounds.map fun r ↦ r.2.map fun x ↦
        (openedOf P.logBlowup x, x.1, x.2.zip (openedOf P.logBlowup x))
      let t1 := (t.observeList (DomainSeparator.pcsSeed F EF (countsOf opened)
        P.batchPowBits)).observeExts
          ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap (·.toList))
      let g := t1.grind P.batchPowBits
      let fri := proveFri (specBackend EF) P rounds
        ((Fri.reduce (g.2.sampleExtValue : EF) (opened.flatten.map (·.2))).map (·.2)) g.1
      ((opened.map (·.map (·.1)), (fri.run (Transcript.sampleExtState EF g.2)).1),
        (fri.run (Transcript.sampleExtState EF g.2)).2) := by
  unfold openPcs
  simp only [prun_bind]
  erw [forM_rounds]
  rfl

/-! ### The proof -/

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- `ζ ω`. -/
def hZetaNext : EF := hZeta EF P A logN trace pis * Ext.ofBase (twoAdicGen logN)

/-- The points the trace is opened at. -/
abbrev hTracePts : List EF :=
  tracePoints A (hZeta EF P A logN trace pis) (hZetaNext EF P A logN trace pis)

/-- The points the preprocessed trace is opened at. -/
abbrev hPrepPts : List EF :=
  preprocessedPoints A (hZeta EF P A logN trace pis) (hZetaNext EF P A logN trace pis)

/-- The trace's and the quotient's rounds. -/
def hBaseRounds : List (OpenRound (specBackend EF)) :=
  [(Committed.ofMats hashF compF [hExt P A logN trace],
      [(hExt P A logN trace, hTracePts EF P A logN trace pis)]),
    (Committed.ofMats hashF compF (hChunks EF P A logN trace pis),
      (hChunks EF P A logN trace pis).map fun m ↦ (m, [hZeta EF P A logN trace pis]))]

/-- The preprocessed trace's round, if any. -/
def hPrepRounds : List (OpenRound (specBackend EF)) :=
  ((setupWith (specBackend EF) P A logN).map fun (pext, pc) ↦
    (pc, [(pext, hPrepPts EF P A logN trace pis)])).toList

/-- The rounds the prover opens. -/
def hRounds : List (OpenRound (specBackend EF)) :=
  hBaseRounds EF P A logN trace pis ++ hPrepRounds EF P A logN trace pis

/-- The opened values, with their matrices and points. -/
def hOpened : List (List (List (Array EF) × Mat F × List (EF × Array EF))) :=
  (hRounds EF P A logN trace pis).map (roundItems P.logBlowup)

/-- The transcript after the PCS's domain separator and the opened values. -/
def hTP : Transcript F 24 :=
  ((Transcript.sampleExtState EF (hOod EF P A logN trace pis).2).observeList
    (DomainSeparator.pcsSeed F EF (countsOf (hOpened EF P A logN trace pis))
      P.batchPowBits)).observeExts
    (((hRounds EF P A logN trace pis).flatMap (roundOpened P.logBlowup)).flatMap
      (·.toList))

/-- The batching grinding: its witness and the transcript after it. -/
def hBatch : F × Transcript F 24 := (hTP EF P A logN trace pis).grind P.batchPowBits

/-- The batching challenge. -/
def hBatchAlpha : EF := ((hBatch EF P A logN trace pis).2.sampleExtValue : EF)

/-- The transcript FRI starts from. -/
def hT2 : Transcript F 24 := Transcript.sampleExtState EF (hBatch EF P A logN trace pis).2

/-- FRI's inputs for the batching challenge `α`. -/
def hInputs (alpha : EF) : List (Array EF) :=
  (Fri.reduce alpha ((hOpened EF P A logN trace pis).flatten.map (·.2))).map (·.2)

/-- FRI's run. -/
def hFriRun : FriProof F EF × Transcript F 24 :=
  (proveFri (specBackend EF) P (hRounds EF P A logN trace pis)
    (hInputs EF P A logN trace pis (hBatchAlpha EF P A logN trace pis))
    (hBatch EF P A logN trace pis).1).run (hT2 EF P A logN trace pis)

theorem prove_eq : prove EF P A logN trace pis =
    { traceCommit := (Committed.ofMats hashF compF [hExt P A logN trace]).root
      quotientCommit := (Committed.ofMats hashF compF (hChunks EF P A logN trace pis)).root
      opened := honestOpened P.logBlowup A logN (hExt P A logN trace)
        (hChunks EF P A logN trace pis) (hZeta EF P A logN trace pis)
      fri := (hFriRun EF P A logN trace pis).1
      degreeBits := logN
      oodWitness := (hOod EF P A logN trace pis).1 } := by
  unfold prove proveWith
  dsimp only
  rw [prun_bind]
  erw [commitAndSample_run]
  unfold openAndAssemble
  simp only [prun_bind]
  erw [openPcs_run]
  simp only [StateT.run_pure]
  show Proof.mk _ _ _ _ _ _ = Proof.mk _ _ _ _ _ _
  congr 1
  unfold honestOpened
  congr 1
  · simp only [List.cons_append, List.map_cons, List.headD_cons, openedOf, tracePoints]
    split <;> rfl
  · by_cases hn : A.mainNextRow = true
    · simp only [hn, ↓reduceIte, List.cons_append, List.map_cons, List.map_nil,
        List.getD_cons_succ, List.getD_cons_zero, List.headD_cons, openedOf, tracePoints]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
  · by_cases hpw : A.preprocessedWidth = 0
    · simp only [setupWith, hpw, ↓reduceIte, Option.map_none]
    · simp only [setupWith, hpw, ↓reduceIte, Option.map_some, Option.toList_some,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_succ,
        List.getD_cons_zero, List.headD_cons, openedOf, preprocessedPoints, Option.some.injEq]
      split <;> rfl
  · by_cases hn : A.opensPreprocessedNext = true
    · have hpw : A.preprocessedWidth ≠ 0 := by
        simp only [Air.opensPreprocessedNext, Bool.and_eq_true, decide_eq_true_eq] at hn
        omega
      simp only [setupWith, hpw, hn, ↓reduceIte, Option.map_some, Option.toList_some,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_succ,
        List.getD_cons_zero, List.headD_cons, openedOf, preprocessedPoints]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
  · simp only [List.cons_append, List.nil_append, List.map_cons, List.getD_cons_succ,
      List.getD_cons_zero, List.map_map]
    refine congrArg List.toArray ?_
    induction hChunks EF P A logN trace pis with
    | nil => rfl
    | cons m ms ih => exact congrArg (List.cons _) ih

/-- The prover's final transcript is FRI's. -/
theorem proveTranscript_eq :
    proveTranscript EF P A logN trace pis = (hFriRun EF P A logN trace pis).2 := by
  unfold proveTranscript
  dsimp only
  rw [prun_bind]
  erw [commitAndSample_run]
  unfold openAndAssemble
  simp only [prun_bind]
  erw [openPcs_run]
  rfl

end Honest

/-! ### The verifier's observations -/

/-- The innermost body of `verifyPcs`'s observation loop. -/
def obsPts (p : EF × List EF) (_ : PUnit) : M (poseidon2 F) (ForInStep PUnit) := do
  observeExts (poseidon2 F) p.2
  pure (ForInStep.yield PUnit.unit)

/-- The middle body of `verifyPcs`'s observation loop. -/
def obsMats (x : Domain F × List (EF × List EF)) (_ : PUnit) : M (poseidon2 F) (ForInStep PUnit) :=
  do
  forIn x.2 PUnit.unit obsPts
  pure (ForInStep.yield PUnit.unit)

/-- The outer body of `verifyPcs`'s observation loop. -/
def obsRounds (r : Round F EF) (_ : PUnit) : M (poseidon2 F) (ForInStep PUnit) := do
  forIn r.2 PUnit.unit obsMats
  pure (ForInStep.yield PUnit.unit)

theorem verifyPcs_eq (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF) : verifyPcs
    (poseidon2 F) P rounds proof = (do
      ensure (P.batchPowBits != 0 || proof.batchWitness == 0) "batch witness"
      observeList (poseidon2 F) (DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits)
      forIn rounds PUnit.unit obsRounds
      ensure (← checkWitness (poseidon2 F) P.batchPowBits proof.batchWitness) "batch witness"
      let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      verifyFri (poseidon2 F) P proof rounds alpha) :=
  rfl

theorem forIn_obsPts (pts : List (EF × List EF)) (t : Transcript F 24) :
    forIn pts PUnit.unit obsPts t = .ok (PUnit.unit, t.observeExts (pts.flatMap (·.2))) := by
  induction pts generalizing t with
  | nil => rfl
  | cons p pts ih =>
    rw [forIn_cons_ok p pts _ PUnit.unit obsPts t (t.observeExts p.2)
      (bind_ok (observeExts_run t p.2)), ih,
      List.flatMap_cons, observeExts_append]

theorem forIn_obsMats (mats : List (Domain F × List (EF × List EF)))
    (t : Transcript F 24) : forIn mats PUnit.unit obsMats t =
      .ok (PUnit.unit, t.observeExts (mats.flatMap fun x ↦ x.2.flatMap (·.2))) := by
  induction mats generalizing t with
  | nil => rfl
  | cons x mats ih =>
    have h : obsMats x PUnit.unit t =
        .ok (.yield PUnit.unit, t.observeExts (x.2.flatMap (·.2))) := by
      unfold obsMats
      rw [bind_ok (forIn_obsPts x.2 t)]
      rfl
    rw [forIn_cons_ok x mats _ PUnit.unit obsMats t _ h, ih, List.flatMap_cons,
      observeExts_append]

theorem forIn_obsRounds (rounds : List (Round F EF)) (t : Transcript F 24) :
    forIn rounds PUnit.unit obsRounds t =
      .ok (PUnit.unit,
        t.observeExts (rounds.flatMap fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2))) := by
  induction rounds generalizing t with
  | nil => rfl
  | cons r rounds ih =>
    have h : obsRounds r PUnit.unit t =
        .ok (.yield PUnit.unit, t.observeExts (r.2.flatMap fun x ↦ x.2.flatMap (·.2))) := by
      unfold obsRounds
      rw [bind_ok (forIn_obsMats r.2 t)]
      rfl
    rw [forIn_cons_ok r rounds _ PUnit.unit obsRounds t _ h, ih, List.flatMap_cons,
      observeExts_append]

theorem verifyPcs_run (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF)
    (t : Transcript F 24) (hbw : (P.batchPowBits != 0 || proof.batchWitness == 0) = true) :
    verifyPcs (poseidon2 F) P rounds proof t = (do
      ensure (← checkWitness (poseidon2 F) P.batchPowBits proof.batchWitness) "batch witness"
      let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      verifyFri (poseidon2 F) P proof rounds alpha)
      ((t.observeList (DomainSeparator.pcsSeed F EF (claimCounts rounds)
        P.batchPowBits)).observeExts (rounds.flatMap fun (r : Round F EF) ↦
          r.2.flatMap fun (x : Domain F × List (EF × List EF)) ↦
            x.2.flatMap fun (y : EF × List EF) ↦ y.2)) := by
  rw [verifyPcs_eq, hbw, ensure_true, pure_bind, bind_ok (observeList_run _ _),
    bind_ok (forIn_obsRounds rounds _)]

/-! ### The verifier -/

/-- The verifier's transcript after the trace and preprocessed commitments and the public
values. -/
def vTA (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (pis : List F) : Transcript F 24 :=
  (((Poseidon2.initTranscript.observeList (starkSeedOf EF P A proof.degreeBits)).observeList
    proof.traceCommit.toList).observeList (preprocessedDigest vk)).observeList pis

/-- The verifier's transcript after the quotient commitment. -/
def vTC (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (pis : List F) : Transcript F 24 :=
  (Transcript.sampleExtState EF (vTA P A vk proof pis)).observeList proof.quotientCommit.toList

/-- The transcript part of `verify`. -/
def verifyRun (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (pis : List F) : M (poseidon2 F) (EF × EF) := do
  let db := proof.degreeBits
  observeList (poseidon2 F) (starkSeedOf EF P A db)
  observeList (poseidon2 F) proof.traceCommit.toList
  observeList (poseidon2 F) (preprocessedDigest vk)
  observeList (poseidon2 F) pis
  let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  observeList (poseidon2 F) proof.quotientCommit.toList
  ensure (← checkWitness (poseidon2 F) P.oodPowBits proof.oodWitness) "out-of-domain witness"
  let zeta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  ensure (Ext.powTwo zeta db - 1 != 0) "out-of-domain point in the trace domain"
  verifyPcs (poseidon2 F) P (openingRounds A vk proof zeta) proof.fri
  return (alpha, zeta)

theorem verify_eq (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (pis : List F) :
    verify P A vk proof pis = ExceptT.run (do
      let o := proof.opened
      unless proof.degreeBits + A.logQuotientChunks proof.degreeBits ≤ twoAdicity F do
        throw "degree bits"
      unless A.periodicFits proof.degreeBits do
        throw "periodic columns"
      unless pis.length == A.numPublicValues do
        throw "public values"
      unless o.traceLocal.size == A.width && traceNextOk A o &&
          o.quotientChunks.size == 2 ^ A.logQuotientChunks proof.degreeBits &&
          o.quotientChunks.all (·.size == Challenge.d EF) &&
          preprocessedShapeOk A vk o proof.degreeBits do
        throw "invalid proof shape"
      unless P.oodPowBits != 0 || proof.oodWitness == 0 do
        throw "out-of-domain witness"
      (verifyRun P A vk proof pis).run Poseidon2.initTranscript >>= verifyCheck A proof pis) := by
  delta verify verifyWith verifyRun verifyCheck
  rfl

theorem observe_bind {β : Type} (x : F) (f : Unit → M (poseidon2 F) β) (t : Transcript F 24) :
    (observe (poseidon2 F) x >>= f) t = f () (t.observe x) := bind_ok rfl

theorem observeList_bind {β : Type} (xs : List F) (f : Unit → M (poseidon2 F) β)
    (t : Transcript F 24) :
    (observeList (poseidon2 F) xs >>= f) t = f () (t.observeList xs) :=
  bind_ok (observeList_run t xs)

theorem sampleExt_bind {β : Type} (f : EF → M (poseidon2 F) β) (t : Transcript F 24) :
    ((sampleExt (poseidon2 F) : M (poseidon2 F) EF) >>= f) t = f (t.sampleExtValue : EF)
        (Transcript.sampleExtState EF t) := bind_ok (sampleExt_run t)

theorem verifyRun_run (P : Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (pis : List F) :
    verifyRun P A vk proof pis Poseidon2.initTranscript = (do
      ensure (← checkWitness (poseidon2 F) P.oodPowBits proof.oodWitness) "out-of-domain witness"
      let zeta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      ensure (Ext.powTwo zeta proof.degreeBits - 1 != 0) "out-of-domain point in the trace domain"
      verifyPcs (poseidon2 F) P (openingRounds A vk proof zeta) proof.fri
      pure (((vTA P A vk proof pis).sampleExtValue : EF), zeta)) (vTC P A vk proof pis) := by
  simp only [verifyRun, observeList_bind, sampleExt_bind]
  rfl

/-! ### The honest openings -/

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- The verifying key of the preprocessed trace, with its Poseidon2 Merkle root. -/
theorem setup_eq : setup P A logN = if A.preprocessedWidth = 0 then none else
    some ⟨A.preprocessedWidth, logN, Merkle.Poseidon2.root F [(hPrepExt P A logN).toMatrix]⟩ := by
  unfold setup preprocessedKeyWith
  split
  · rfl
  · show some (⟨_, _, merkleNodeWith (poseidon2 F) _ _ 0⟩ : PreprocessedKey F) =
      some (⟨_, _, _⟩ : PreprocessedKey F)
    rw [merkleNodeWith_pure (poseidon2 F) hashF compF (fun _ ↦ rfl) (fun _ _ ↦ rfl),
      Merkle.Poseidon2.root, Merkle.root_eq_nodeValue _ _ _ _
        (shape_ldeRef logN P.logBlowup gen A.preprocessedWidth A.preprocessed).2.1]
    simp only [rowOf_toList]
    rfl

/-- The preprocessed trace's commitment is the verifying key's. -/
theorem prepDigest_eq :
    ((hPrep EF P A logN).map fun x ↦ ((specBackend EF).root x.2).toList).getD [] =
      preprocessedDigest (setup P A logN) := by
  rw [hPrep_eq]
  by_cases hpw : A.preprocessedWidth = 0
  · simp only [setup_eq, hpw, ↓reduceIte]
    rfl
  · simp only [setup_eq, hpw, ↓reduceIte, Option.map_some, Option.getD_some, preprocessedDigest]
    show (Committed.ofMats hashF compF [_]).root.toList = _
    rw [root_ofMats]
    rfl

/-- The preprocessed trace's item, if any: its extension with its points and opened values. -/
def hPrepItems : List (Mat F × List (EF × Array EF)) :=
  ((hPrep EF P A logN).map fun x ↦ (x.1, (hPrepPts EF P A logN trace pis).zip
    (openedOf P.logBlowup (x.1, hPrepPts EF P A logN trace pis)))).toList

/-- The matrices FRI batches, with their opened points and values. -/
def hItems : List (Mat F × List (EF × Array EF)) :=
  (hOpened EF P A logN trace pis).flatten.map (·.2)

theorem hItems_eq : hItems EF P A logN trace pis =
    (hExt P A logN trace, (hTracePts EF P A logN trace pis).zip
      (openedOf P.logBlowup (hExt P A logN trace,
        hTracePts EF P A logN trace pis))) ::
    ((hChunks EF P A logN trace pis).map fun m ↦
      (m, [hZeta EF P A logN trace pis].zip
        (openedOf P.logBlowup (m, [hZeta EF P A logN trace pis])))) ++
    hPrepItems EF P A logN trace pis := by
  have hsplit : hOpened EF P A logN trace pis =
      (hBaseRounds EF P A logN trace pis).map (roundItems P.logBlowup) ++
        (hPrepRounds EF P A logN trace pis).map (roundItems P.logBlowup) := by
    rw [hOpened, hRounds, List.map_append]
  rw [hItems, hsplit, List.flatten_append, List.map_append]
  congr 1
  · simp only [hBaseRounds, roundItems, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    rw [List.map_append]
    refine congrArg (List.cons _) ?_
    induction hChunks EF P A logN trace pis with
    | nil => rfl
    | cons m ms ih => exact congrArg (List.cons _) ih
  · unfold hPrepRounds hPrepItems hPrep
    cases setupWith (specBackend EF) P A logN <;> rfl

theorem hPrepItems_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) :
    ∀ x ∈ hPrepItems EF P A logN trace pis,
      Deep.HonestItem P.logBlowup (logN + P.logBlowup) x := by
  have hzn : Ext.OutsideBase (hZetaNext EF P A logN trace pis) :=
    Ext.outsideBase_mul_ofBase hz
        (BaseField.twoAdicGen_ne_zero logN (by have := hin.twoAdic; omega))
  have hpts : ∀ z ∈ hPrepPts EF P A logN trace pis, Ext.OutsideBase z := by
    intro z hz'
    simp only [hPrepPts, preprocessedPoints] at hz'
    split at hz'
    · rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hz
      · rw [List.mem_singleton] at hz'; exact hz' ▸ hzn
    · rw [List.mem_singleton] at hz'; exact hz' ▸ hz
  obtain ⟨ps, hlde, -⟩ := prep_lde P A logN trace hin
  have hitems : hPrepItems EF P A logN trace pis = if A.preprocessedWidth = 0 then [] else
      [(hPrepExt P A logN, (hPrepPts EF P A logN trace pis).zip
        (openedOf P.logBlowup (hPrepExt P A logN, hPrepPts EF P A logN trace pis)))] := by
    unfold hPrepItems
    rw [hPrep_eq]
    split <;> rfl
  intro x hx
  rw [hitems] at hx
  split at hx
  · exact absurd hx List.not_mem_nil
  · rw [List.mem_singleton] at hx
    subst hx
    exact honestItem_of _ _ _ _ ps hlde hpts

theorem hItems_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) :
    ∀ x ∈ hItems EF P A logN trace pis, Deep.HonestItem P.logBlowup (logN + P.logBlowup) x := by
  have hzn : Ext.OutsideBase (hZetaNext EF P A logN trace pis) :=
    Ext.outsideBase_mul_ofBase hz
        (BaseField.twoAdicGen_ne_zero logN (by have := hin.twoAdic; omega))
  rw [hItems_eq]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · obtain ⟨ps, hlde, -⟩ := trace_lde P A logN trace hin
    refine honestItem_of _ _ _ _ ps hlde fun z hz' ↦ ?_
    simp only [hTracePts, tracePoints] at hz'
    split at hz'
    · rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hz
      · rw [List.mem_singleton] at hz'; exact hz' ▸ hzn
    · rw [List.mem_singleton] at hz'; exact hz' ▸ hz
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
    obtain ⟨ps, hlde, -⟩ := chunk_isLde (EF := EF) P A logN _ hin.twoAdic hin.chunks c
    exact honestItem_of _ _ _ _ ps hlde fun z hz' ↦ (List.mem_singleton.mp hz') ▸ hz
  · exact hPrepItems_honest EF P A logN trace pis hin hz x hx

end Honest

theorem eq_singleton_of_pairwise {α : Type} (L : List (Nat × α)) (H : Nat)
    (hp : (L.map (·.1)).Pairwise (· > ·)) (hH : ∀ y ∈ L, y.1 = H) (hne : L ≠ []) :
    ∃ v, L = [(H, v)] := by
  match L, hp, hne with
  | [y], _, _ => exact ⟨y.2, by rw [← hH y List.mem_cons_self]⟩
  | y :: z :: _, hp, _ =>
    have := List.rel_of_pairwise_cons hp (List.mem_cons_self (a := z.1))
    have e1 := hH y List.mem_cons_self
    have e2 := hH z (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [gt_iff_lt] at this
    omega

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- FRI has one input, low degree, of the extension's height. -/
theorem reduce_hItems (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (alpha : EF) :
    ∃ v, Fri.reduce alpha (hItems EF P A logN trace pis) = [(logN + P.logBlowup, v)] ∧
      LowDegree (logN + P.logBlowup) logN v := by
  have hon := hItems_honest EF P A logN trace pis hin hz
  have hh : ∀ x ∈ hItems EF P A logN trace pis, x.1.height = 2 ^ (logN + P.logBlowup) :=
    fun x hx ↦ by obtain ⟨ps, hl, -⟩ := hon x hx; exact hl.2.1
  obtain ⟨hpw, hmem, -⟩ := reduce_heights alpha (hItems EF P A logN trace pis)
    fun x hx ↦ by rw [hh x hx, Nat.log2_two_pow]
  have hH : ∀ y ∈ Fri.reduce alpha (hItems EF P A logN trace pis), y.1 = logN + P.logBlowup := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (hmem y.1).mp (List.mem_map_of_mem hy)
    rw [← hxy, hh x hx, Nat.log2_two_pow]
  have hne : Fri.reduce alpha (hItems EF P A logN trace pis) ≠ [] := by
    intro h0
    have := (hmem (logN + P.logBlowup)).mpr ⟨_, by rw [hItems_eq]; exact List.mem_cons_self,
      by rw [hh _ (by rw [hItems_eq]; exact List.mem_cons_self), Nat.log2_two_pow]⟩
    rw [h0] at this
    exact List.not_mem_nil this
  obtain ⟨v, hv⟩ := eq_singleton_of_pairwise _ _ hpw hH hne
  refine ⟨v, hv, ?_⟩
  have := reduce_lowDegree P.logBlowup alpha _ (fun x hx ↦ ⟨_, hon x hx⟩) (logN + P.logBlowup, v)
    (by rw [hv]; exact List.mem_singleton_self _)
  rwa [Nat.add_sub_cancel] at this

end Honest

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- A chunk with its opening at `ζ`. -/
def hItemC (m : Mat F) : Mat F × List (EF × Array EF) :=
  (m, [hZeta EF P A logN trace pis].zip (openedOf P.logBlowup (m, [hZeta EF P A logN trace pis])))

/-- The trace's and the quotient's rounds with their openings. -/
def hBaseDRounds : List (Committed F × List (Mat F × List (EF × Array EF))) :=
  [(Committed.ofMats hashF compF [hExt P A logN trace],
      [(hExt P A logN trace, (hTracePts EF P A logN trace pis).zip
        (openedOf P.logBlowup (hExt P A logN trace,
          hTracePts EF P A logN trace pis)))]),
    (Committed.ofMats hashF compF (hChunks EF P A logN trace pis),
      (hChunks EF P A logN trace pis).map (hItemC EF P A logN trace pis))]

/-- The preprocessed trace's round with its openings, if any. -/
def hPrepDRounds : List (Committed F × List (Mat F × List (EF × Array EF))) :=
  ((hPrep EF P A logN).map fun x ↦ (x.2, [(x.1, (hPrepPts EF P A logN trace pis).zip
    (openedOf P.logBlowup (x.1, hPrepPts EF P A logN trace pis)))])).toList

theorem hPrepDRounds_eq : hPrepDRounds EF P A logN trace pis =
    if A.preprocessedWidth = 0 then [] else
      [(Committed.ofMats hashF compF [hPrepExt P A logN], [(hPrepExt P A logN,
        (hPrepPts EF P A logN trace pis).zip
          (openedOf P.logBlowup (hPrepExt P A logN, hPrepPts EF P A logN trace pis)))])] := by
  unfold hPrepDRounds
  rw [hPrep_eq]
  split <;> rfl

/-- The rounds with their openings, as `reduceQuery_honest` takes them. -/
def hDRounds : List (Committed F × List (Mat F × List (EF × Array EF))) :=
  hBaseDRounds EF P A logN trace pis ++ hPrepDRounds EF P A logN trace pis

theorem map_fst_hItemC (ms : List (Mat F)) :
    (ms.map (hItemC EF P A logN trace pis)).map (·.1) = ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => exact congrArg (List.cons m) ih

theorem flatMap_hDRounds :
    (hDRounds EF P A logN trace pis).flatMap (·.2) = hItems EF P A logN trace pis := by
  rw [hItems_eq, hDRounds, List.flatMap_append]
  congr 1
  · simp only [hBaseDRounds, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  · unfold hPrepDRounds hPrepItems
    cases hPrep EF P A logN <;> rfl

theorem hChunks_ne_nil : hChunks EF P A logN trace pis ≠ [] := by
  simp only [hChunks, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)

end Honest

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

theorem height_hChunks (hin : Fits P A logN trace) :
    ∀ m ∈ hChunks EF P A logN trace pis, m.height = 2 ^ (logN + P.logBlowup) := by
  intro m hm
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
  obtain ⟨ps, hl, -⟩ := chunk_isLde (EF := EF) P A logN _ hin.twoAdic hin.chunks c
  exact hl.2.1

theorem vChunks_eq (ms : List (Mat F)) (hms : ∀ m ∈ ms, m.height = 2 ^ (logN + P.logBlowup)) :
    (ms.map fun m ↦ Fri.openedAt P.logBlowup m (hZeta EF P A logN trace pis)).map
      (fun ch ↦ ((⟨1, logN⟩ : Domain F), [(hZeta EF P A logN trace pis, ch.toList)])) =
    (ms.map (hItemC EF P A logN trace pis)).map fun x ↦
      ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F), x.2.map fun y ↦ (y.1, y.2.toList)) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons]
    rw [ih fun m' hm' ↦ hms m' (List.mem_cons_of_mem _ hm')]
    simp only [hItemC]
    rw [hms m List.mem_cons_self, Nat.log2_two_pow, Nat.add_sub_cancel]
    rfl

theorem openingRounds_eq (hin : Fits P A logN trace) :
    openingRounds A (setup P A logN) (prove EF P A logN trace pis) (hZeta EF P A logN trace pis) =
      (hDRounds EF P A logN trace pis).map fun r ↦ (r.1.root, r.2.map fun x ↦
        ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
          x.2.map fun y ↦ (y.1, y.2.toList))) := by
  rw [prove_eq]
  simp only [openingRounds]
  rw [hDRounds, List.map_append]
  congr 1
  · simp only [hBaseDRounds, honestOpened, List.map_cons, List.map_nil,
      height_hExt P A logN trace hin, Nat.log2_two_pow, Nat.add_sub_cancel]
    rw [vChunks_eq EF P A logN trace pis _ (height_hChunks EF P A logN trace pis hin)]
    simp only [traceOpenings, hTracePts, tracePoints, openedOf]
    cases A.mainNextRow <;> rfl
  · rw [hPrepDRounds_eq]
    by_cases hpw : A.preprocessedWidth = 0
    · simp only [preprocessedRound, setup_eq, hpw, ↓reduceIte, List.map_nil]
    · have hh := height_hPrepExt P A logN trace hin
      simp only [setup_eq, hpw, ↓reduceIte, List.map_cons, List.map_nil, preprocessedRound,
        honestOpened, Option.getD_some]
      rw [root_ofMats, hh, Nat.log2_two_pow, Nat.add_sub_cancel]
      simp only [hPrepPts, preprocessedPoints, openedOf, hPrepExt]
      split <;> rfl

end Honest

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

theorem hInputs_eq (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (alpha : EF) :
    ∃ v, hInputs EF P A logN trace pis alpha = [v] ∧
      Fri.reduce alpha (hItems EF P A logN trace pis) = [(logN + P.logBlowup, v)] ∧
      LowDegree (logN + P.logBlowup) logN v := by
  obtain ⟨v, hv, hl⟩ := reduce_hItems EF P A logN trace pis hin hz alpha
  refine ⟨v, ?_, hv, hl⟩
  show (Fri.reduce alpha (hItems EF P A logN trace pis)).map (·.2) = _
  rw [hv]
  rfl

end Honest

/-- The verifier's input checks accept the honest multi-openings of rounds of matrices of the
largest height. -/
theorem verifyInputs_honest (P : Params) (logMax : Nat) (indices : List Nat)
    (rounds : List (Committed F × List (Mat F × List (EF × Array EF))))
    (hidx : ∀ i ∈ indices, i < 2 ^ logMax)
    (hrounds : ∀ r ∈ rounds, r.2 ≠ [] ∧ r.1 = Committed.ofMats hashF compF (r.2.map (·.1)) ∧
      ∀ x ∈ r.2, x.2 ≠ [] ∧ Deep.HonestItem P.logBlowup logMax x) (t : Transcript F 24) :
    verifyInputs (poseidon2 F) P logMax indices
      (rounds.map fun r ↦ openMulti (specBackend EF) r.1
        (indices.map (· >>> (logMax - (specBackend EF).logHeight r.1))))
      (rounds.map fun r ↦ (r.1.root, r.2.map fun x ↦
        ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F), x.2.map fun y ↦ (y.1, y.2.toList))))
      t = .ok ((), t) := by
  unfold verifyInputs
  simp only [List.length_map, beq_self_eq_true, ensure_true, pure_bind, List.zip_map']
  refine (bind_ok (a := PUnit.unit) (t' := t) ?_).trans rfl
  induction rounds with
  | nil => rfl
  | cons r rounds ih =>
    obtain ⟨hne, hc, hits⟩ := hrounds r List.mem_cons_self
    rw [List.map_cons]
    refine (forIn_cons_ok _ _ _ PUnit.unit _ t t ?_).trans
      (ih fun r' hr' ↦ hrounds r' (List.mem_cons_of_mem _ hr'))
    obtain ⟨c, its⟩ := r
    dsimp only at hne hc hits ⊢
    subst hc
    have hms : ∀ m ∈ its.map (·.1), m.height = 2 ^ logMax ∧ m.values.size = m.width * m.height := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      obtain ⟨ps, hl, -⟩ := (hits x hx).2
      exact ⟨hl.2.1, hl.2.2.1⟩
    have hne' : its.map (·.1) ≠ [] := by rwa [Ne, List.map_eq_nil_iff]
    have hmx : Nat.log2 (Committed.ofMats hashF compF (its.map (·.1))).maxHeight = logMax := by
      rw [Fri.maxHeight_ofMats _ _ hne' fun m hm ↦ (hms m hm).1, Nat.log2_two_pow]
    have hlh : (specBackend EF).logHeight (Committed.ofMats hashF compF (its.map (·.1))) = logMax :=
      hmx
    have hdims : ((its.map fun x ↦ ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
        x.2.map fun y ↦ (y.1, y.2.toList))).map fun x ↦
          (2 ^ (x.1.logSize + P.logBlowup), (x.2.headD default).2.length)) =
        (its.map (·.1)).map fun m ↦ (m.height, m.width) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun x hx ↦ ?_
      obtain ⟨hpne, ps, hl, hpts⟩ := hits x hx
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hpne
      have hys := (hpts y (by rw [hy]; exact List.mem_cons_self)).2.1
      simp only [Function.comp_apply, hy, List.map_cons, List.headD_cons, Array.length_toList]
      rw [hys, ← hl.1, hl.2.1, Nat.log2_two_pow, Nat.sub_add_cancel hl.2.2.2.1]
    have hbatch : ((its.map fun x ↦ ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
        x.2.map fun y ↦ (y.1, y.2.toList))).map fun x ↦ x.1.logSize + P.logBlowup).foldl max 0 =
          logMax := by
      refine foldl_max_const logMax _ 0 (fun z hz ↦ ?_) (by simpa only [ne_eq, List.map_eq_nil_iff])
        (Nat.zero_le _)
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      obtain ⟨-, ps, hl, -⟩ := hits x hx
      dsimp only
      rw [hl.2.1, Nat.log2_two_pow, Nat.sub_add_cancel hl.2.2.2.1]
    have hrows : ∀ i, ((Committed.ofMats hashF compF (its.map (·.1))).openAt i).values.size =
        its.length := fun i ↦ by
      rw [Fri.openAt_values _ logMax (fun m hm ↦ (hms m hm).1), List.size_toArray, List.length_map,
        List.length_map]
    have hpts : (its.map fun x ↦ ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
        x.2.map fun y ↦ (y.1, y.2.toList))).all (fun x ↦ !x.2.isEmpty) = true := by
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.isEmpty_eq_false_iff, ne_eq, List.map_eq_nil_iff]
      exact fun x hx ↦ (hits x hx).1
    simp only [hmx, Nat.sub_self, Nat.shiftRight_zero, List.map_id', openMulti,
      List.size_toArray, List.length_map, beq_self_eq_true, ensure_true, pure_bind, hdims, hbatch,
      hpts]
    have hall : ((indices.map
        (Committed.ofMats hashF compF (its.map (·.1))).openAt).map (·.values)).toArray.all
          (fun a ↦ a.size == its.length) 0 indices.length = true := by
      rw [show indices.length = ((indices.map
        (Committed.ofMats hashF compF (its.map (·.1))).openAt).map (·.values)).toArray.size by
          simp only [List.size_toArray, List.length_map], List.all_toArray]
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, beq_iff_eq]
      exact fun i _ ↦ hrows i
    rw [hall, ensure_true, pure_bind]
    have hv := Fri.verifyMulti_openMulti (its.map (·.1)) logMax hne' hms indices hidx
    set C := Committed.ofMats hashF compF (its.map (·.1))
    have e1 : (((indices.map ((specBackend EF).openAt C)).map (·.values)).map fun r ↦
        r.toList.map (·.toList)) =
        indices.map fun i ↦ (C.openAt i).values.toList.map (·.toList) := by
      rw [List.map_map, List.map_map]; rfl
    have e2 : (indices.map ((specBackend EF).openAt C)).map (·.path.toList) =
        indices.map fun i ↦ (C.openAt i).path.toList := by
      rw [List.map_map]; rfl
    rw [bind_ok (checkMulti_eq _ _ _ _ _ t), e1, e2, hv]
    rfl

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

theorem flat_chunks (ms : List (Mat F)) :
    ((ms.map (hItemC EF P A logN trace pis)).map fun x ↦
      ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
        x.2.map fun y ↦ (y.1, y.2.toList))).flatMap
        (fun x ↦ x.2.flatMap (·.2)) =
      ((ms.map fun m ↦ (m, [hZeta EF P A logN trace pis])).flatMap (openedOf P.logBlowup)).flatMap
        (·.toList) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.flatMap_cons, List.flatMap_append] at ih ⊢
    rw [ih, hItemC, flatMap_zip_openedOf]

theorem flat_eq (hin : Fits P A logN trace) :
    (openingRounds A (setup P A logN) (prove EF P A logN trace pis)
        (hZeta EF P A logN trace pis)).flatMap
      (fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) =
    ((hRounds EF P A logN trace pis).flatMap (roundOpened P.logBlowup)).flatMap
      (·.toList) := by
  rw [openingRounds_eq EF P A logN trace pis hin, hDRounds, hRounds, List.map_append,
    List.flatMap_append, List.flatMap_append, List.flatMap_append]
  congr 1
  · simp only [hBaseDRounds, hBaseRounds, roundOpened, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append]
    rw [flat_chunks, flatMap_zip_openedOf]
  · unfold hPrepDRounds hPrepRounds hPrep
    cases setupWith (specBackend EF) P A logN with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, roundOpened]
      exact flatMap_zip_openedOf _ _ _

theorem good_hInputs (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (hfin : P.logFinalPolyLen ≤ logN)
    (alpha : EF) : ∃ v, hInputs EF P A logN trace pis alpha = [v] ∧
      Nat.log2 v.size = logN + P.logBlowup ∧ Good P (Nat.log2 v.size) v := by
  obtain ⟨v, hv, -, hl⟩ := hInputs_eq EF P A logN trace pis hin hz alpha
  have hs := log2_size hl
  refine ⟨v, hv, hs, ?_⟩
  rw [hs]
  exact ⟨by omega, by rwa [Nat.add_sub_cancel]⟩

theorem hDRounds_ok (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) :
    ∀ r ∈ hDRounds EF P A logN trace pis, r.2 ≠ [] ∧
      r.1 = Committed.ofMats hashF compF (r.2.map (·.1)) ∧
      ∀ x ∈ r.2, x.2 ≠ [] ∧ Deep.HonestItem P.logBlowup (logN + P.logBlowup) x := by
  have hon := hItems_honest EF P A logN trace pis hin hz
  rw [← flatMap_hDRounds] at hon
  intro r hr
  have hpts : hPrepPts EF P A logN trace pis ≠ [] := by
    simp only [hPrepPts, preprocessedPoints]
    split <;> exact List.cons_ne_nil _ _
  have htpts : hTracePts EF P A logN trace pis ≠ [] := by
    simp only [hTracePts, tracePoints]
    split <;> exact List.cons_ne_nil _ _
  refine ⟨?_, ?_, fun x hx ↦ ⟨?_, hon x (List.mem_flatMap.mpr ⟨r, hr, hx⟩)⟩⟩
  all_goals
    simp only [hDRounds, hBaseDRounds, hPrepDRounds_eq, List.cons_append, List.nil_append,
      List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
  · exact List.cons_ne_nil _ _
  · simp only [ne_eq, List.map_eq_nil_iff]
    exact hChunks_ne_nil EF P A logN trace pis
  · split at hr
    · exact absurd hr List.not_mem_nil
    · rw [List.mem_singleton.mp hr]
      exact List.cons_ne_nil _ _
  · rfl
  · exact congrArg (Committed.ofMats hashF compF) (map_fst_hItemC EF P A logN trace pis _).symm
  · split at hr
    · exact absurd hr List.not_mem_nil
    · rw [List.mem_singleton.mp hr]
      rfl
  · rw [List.mem_singleton] at hx
    subst hx
    obtain ⟨z, zs, hzs⟩ := List.exists_cons_of_ne_nil htpts
    simp only [hzs, openedOf, List.map_cons, List.zip_cons_cons]
    exact List.cons_ne_nil _ _
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    simp only [hItemC, openedOf, List.map_cons, List.zip_cons_cons]
    exact List.cons_ne_nil _ _
  · split at hr
    · exact absurd hr List.not_mem_nil
    · rw [List.mem_singleton.mp hr, List.mem_singleton] at hx
      subst hx
      obtain ⟨z, zs, hzs⟩ := List.exists_cons_of_ne_nil hpts
      simp only [hzs, openedOf, List.map_cons, List.zip_cons_cons]
      exact List.cons_ne_nil _ _

/-- Maps of the commitments of rounds with the same commitments agree. -/
theorem map_fst_congr {C X Y β : Type} (g : C → β) :
    ∀ (rs : List (C × X)) (rs' : List (C × Y)),
      rs.map (·.1) = rs'.map (·.1) → (rs.map fun (c, _) ↦ g c) = rs'.map fun r ↦ g r.1
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (List.cons_ne_nil _ _).symm
  | _ :: _, [], h => absurd h (List.cons_ne_nil _ _)
  | (c, x) :: rs, (c', y) :: rs', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons]
    rw [h.1, map_fst_congr g rs rs' h.2]

theorem fst_hRounds : (hRounds EF P A logN trace pis).map (·.1) =
    ((hDRounds EF P A logN trace pis).map (·.1) : List (specBackend EF).C) := by
  rw [hRounds, hDRounds, List.map_append, List.map_append]
  congr 1
  unfold hPrepRounds hPrepDRounds hPrep
  cases setupWith (specBackend EF) P A logN <;> rfl

theorem hreduce (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (alpha : EF) (index : Nat)
    (t : Transcript F 24) (hidx : index < 2 ^ (logN + P.logBlowup)) :
    reduceQuery (poseidon2 F) P (logN + P.logBlowup) index alpha
      ((hRounds EF P A logN trace pis).map fun (c, _) ↦ ((specBackend EF).openAt c
        (index >>> (logN + P.logBlowup - (specBackend EF).logHeight c))).values.toList)
      (openingRounds A (setup P A logN) (prove EF P A logN trace pis)
        (hZeta EF P A logN trace pis)) t =
      .ok ((Fri.reduce alpha (hItems EF P A logN trace pis)).map fun y ↦
        (y.1, y.2.getD (index >>> (logN + P.logBlowup - y.1)) 0), t) := by
  rw [openingRounds_eq EF P A logN trace pis hin]
  have hD := reduceQuery_honest P (logN + P.logBlowup) index alpha (hDRounds EF P A logN trace pis)
    hidx fun r hr ↦ by
      obtain ⟨h1, h2, h3⟩ := hDRounds_ok EF P A logN trace pis hin hz r hr
      exact ⟨h1, h2, _, le_rfl, fun x hx ↦ (h3 x hx).2⟩
  rw [flatMap_hDRounds] at hD
  have hmap : ((hRounds EF P A logN trace pis).map fun (c, _) ↦ ((specBackend EF).openAt c
      (index >>> (logN + P.logBlowup - (specBackend EF).logHeight c))).values.toList) =
      (hDRounds EF P A logN trace pis).map fun r ↦ ((specBackend EF).openAt r.1
        (index >>> (logN + P.logBlowup - (specBackend EF).logHeight r.1))).values.toList :=
    map_fst_congr (fun c ↦ ((specBackend EF).openAt c
      (index >>> (logN + P.logBlowup - (specBackend EF).logHeight c))).values.toList) _ _
      (fst_hRounds EF P A logN trace pis)
  rw [hmap]
  exact congrFun hD t

theorem hinputs (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (indices : List Nat)
    (t : Transcript F 24) (hidx : ∀ i ∈ indices, i < 2 ^ (logN + P.logBlowup)) :
    verifyInputs (poseidon2 F) P (logN + P.logBlowup) indices
      ((hRounds EF P A logN trace pis).map fun (c, _) ↦ openMulti (specBackend EF) c
        (indices.map (· >>> (logN + P.logBlowup - (specBackend EF).logHeight c))))
      (openingRounds A (setup P A logN) (prove EF P A logN trace pis)
        (hZeta EF P A logN trace pis)) t = .ok ((), t) := by
  rw [openingRounds_eq EF P A logN trace pis hin]
  have hmap : ((hRounds EF P A logN trace pis).map fun (c, _) ↦ openMulti (specBackend EF) c
      (indices.map (· >>> (logN + P.logBlowup - (specBackend EF).logHeight c)))) =
      (hDRounds EF P A logN trace pis).map fun r ↦ openMulti (specBackend EF) r.1
        (indices.map (· >>> (logN + P.logBlowup - (specBackend EF).logHeight r.1))) :=
    map_fst_congr (fun c ↦ openMulti (specBackend EF) c
      (indices.map (· >>> (logN + P.logBlowup - (specBackend EF).logHeight c)))) _ _
      (fst_hRounds EF P A logN trace pis)
  rw [hmap]
  exact verifyInputs_honest P _ indices (hDRounds EF P A logN trace pis) hidx
    (hDRounds_ok EF P A logN trace pis hin hz) t

theorem hheights :
    ((((openingRounds A (setup P A logN) (prove EF P A logN trace pis)
        (hZeta EF P A logN trace pis)).flatMap (·.2)).map
      (·.1.logSize + P.logBlowup)).mergeSort (fun a b ↦ b ≤ a)).dedup = [logN + P.logBlowup] := by
  have hdb : (prove EF P A logN trace pis).degreeBits = logN := by rw [prove_eq]
  refine dedup_mergeSort_const _ _ _ (fun x hx ↦ ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [logSize_openingRounds _ _ _ _ y hy, hdb]
  · simp only [openingRounds, List.flatMap_cons, List.map_append, List.map_cons, ne_eq,
      List.cons_append, List.flatMap_append, reduceCtorEq, not_false_eq_true]

theorem claimCounts_eq :
    claimCounts (openingRounds A (setup P A logN) (prove EF P A logN trace pis)
      (hZeta EF P A logN trace pis)) = countsOf (hOpened EF P A logN trace pis) := by
  rw [prove_eq]
  simp only [claimCounts, openingRounds, countsOf, hOpened, hRounds, List.map_cons,
    List.map_nil, List.map_map, List.cons_append, List.nil_append, List.map_append]
  refine congrArg₂ (fun a b ↦ a :: b) ?_ (congrArg₂ (fun a b ↦ a :: b) ?_ ?_)
  · simp only [traceOpenings, honestOpened, hTracePts, tracePoints]
    cases A.mainNextRow <;> rfl
  · induction hChunks EF P A logN trace pis with
    | nil => rfl
    | cons m ms ih => exact congrArg (List.cons _) ih
  · unfold hPrepRounds
    by_cases hpw : A.preprocessedWidth = 0
    · simp only [preprocessedRound, setup_eq, setupWith, hpw, ↓reduceIte, Option.map_none,
        Option.toList_none, List.map_nil]
      rfl
    · simp only [preprocessedRound, setup_eq, setupWith, hpw, ↓reduceIte, Option.map_some,
        Option.toList_some, List.map_cons, List.map_nil, honestOpened, Option.getD_some,
        preprocessedPoints, Function.comp_def, Array.length_toList, roundItems, openedOf]
      split <;> simp only [List.map_cons, List.map_nil, Option.getD_some, Array.length_toList] <;>
        rfl

end Honest

/-! ### Completeness -/

theorem verify_ok_of (P : Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (pis : List F) (alpha zeta : EF) (t : Transcript F 24)
    (hdeg : proof.degreeBits + A.logQuotientChunks proof.degreeBits ≤ twoAdicity F)
    (hper : A.periodicFits proof.degreeBits = true) (hpis : pis.length = A.numPublicValues)
    (hshape : (proof.opened.traceLocal.size == A.width && traceNextOk A proof.opened &&
      proof.opened.quotientChunks.size == 2 ^ A.logQuotientChunks proof.degreeBits &&
      proof.opened.quotientChunks.all (·.size == Challenge.d EF) &&
      preprocessedShapeOk A vk proof.opened proof.degreeBits) = true)
    (hood : (P.oodPowBits != 0 || proof.oodWitness == 0) = true)
    (hrun : verifyRun P A vk proof pis Poseidon2.initTranscript = .ok ((alpha, zeta), t))
    (hcheck : checkConstraints A pis proof.opened proof.degreeBits zeta alpha
      (recompose (chunkDomains proof.degreeBits (A.logQuotientChunks proof.degreeBits))
        proof.opened.quotientChunks.toList zeta) = true) :
    verify P A vk proof pis = .ok () := by
  have hrun' : StateT.run (verifyRun P A vk proof pis) Poseidon2.initTranscript = pure
      ((alpha, zeta), t) := hrun
  rw [verify_eq, hrun', pure_bind, verifyCheck_ok A proof pis ((alpha, zeta), t) hcheck]
  simp only [hdeg, hper, hpis, hshape, hood, beq_self_eq_true, ↓reduceIte]
  rfl

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

theorem verifyRun_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis))
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hb : 0 < P.logBlowup)
    (hfin : P.logFinalPolyLen ≤ logN)
    (hgrind : (proveTranscript EF P A logN trace pis).grindFailed = false) :
    ∃ t, verifyRun P A (setup P A logN) (prove EF P A logN trace pis) pis
      Poseidon2.initTranscript =
      .ok ((hAlpha EF P A logN trace pis, hZeta EF P A logN trace pis), t) := by
  obtain ⟨v, hv, hs, hgood⟩ := good_hInputs EF P A logN trace pis hin hz hfin
    (hBatchAlpha EF P A logN trace pis)
  have hrun : hFriRun EF P A logN trace pis = (proveFri (specBackend EF) P
      (hRounds EF P A logN trace pis) [v] (hBatch EF P A logN trace pis).1).run
      (hT2 EF P A logN trace pis) := by
    rw [hFriRun, hv]
  -- the grinding flags
  have hgF : ((proveFri (specBackend EF) P (hRounds EF P A logN trace pis) [v]
      (hBatch EF P A logN trace pis).1).run (hT2 EF P A logN trace pis)).2.grindFailed = false := by
    rw [← hrun, ← proveTranscript_eq]; exact hgrind
  have hg2 := flag_proveFri P _ v _ _ hgF
  have hgB : (hBatch EF P A logN trace pis).2.grindFailed = false := by
    rwa [hT2, flag_sampleExt] at hg2
  have hgO : (hOod EF P A logN trace pis).2.grindFailed = false := by
    have := flag_grind _ _ hgB
    rwa [hTP, flag_observeExts, flag_observeList, flag_sampleExt] at this
  -- the duplexes
  have hdC : (hTC EF P A logN trace pis).duplex = Poseidon2.duplex := by
    rw [Stark.hTC, duplex_observeList, duplex_sampleExt, Stark.hTA, duplex_observeList,
      duplex_observeList, duplex_observeList]
    rfl
  have hdP : (hTP EF P A logN trace pis).duplex = Poseidon2.duplex := by
    rw [hTP, duplex_observeExts, duplex_observeList, duplex_sampleExt, hOod, duplex_grind, hdC]
  have hd2 : (hT2 EF P A logN trace pis).duplex = Poseidon2.duplex := by
    rw [hT2, duplex_sampleExt, hBatch, duplex_grind, hdP]
  -- the proof's fields
  have hp := prove_eq EF P A logN trace pis
  have hTA' : vTA P A (setup P A logN) (prove EF P A logN trace pis) pis =
      hTA EF P A logN trace pis := by
    rw [hp, vTA, hTA, prepDigest_eq]
  have hTC' : vTC P A (setup P A logN) (prove EF P A logN trace pis) pis =
      hTC EF P A logN trace pis := by
    rw [vTC, hTA', hp]; rfl
  have how : (prove EF P A logN trace pis).oodWitness = (hOod EF P A logN trace pis).1 := by
    rw [hp]
  have hdb : (prove EF P A logN trace pis).degreeBits = logN := by rw [hp]
  have hfri : (prove EF P A logN trace pis).fri = (hFriRun EF P A logN trace pis).1 := by rw [hp]
  have hbw : (hFriRun EF P A logN trace pis).1.batchWitness = (hBatch EF P A logN trace pis).1 := by
    rw [hrun, proveFri_run]
  have hTP' : ((Transcript.sampleExtState EF (hOod EF P A logN trace pis).2).observeList
      (DomainSeparator.pcsSeed F EF (claimCounts (openingRounds A (setup P A logN)
        (prove EF P A logN trace pis) (hZeta EF P A logN trace pis))) P.batchPowBits)).observeExts
      ((openingRounds A (setup P A logN) (prove EF P A logN trace pis)
        (hZeta EF P A logN trace pis)).flatMap
        fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) = hTP EF P A logN trace pis := by
    rw [claimCounts_eq, flat_eq EF P A logN trace pis hin]
    rfl
  have hF := verifyFri_proveFri P (hRounds EF P A logN trace pis) v (hBatch EF P A logN trace pis).1
    (openingRounds A (setup P A logN) (prove EF P A logN trace pis) (hZeta EF P A logN trace pis))
    (hBatchAlpha EF P A logN trace pis) (hT2 EF P A logN trace pis) hd2 hgood hP hq hb hgF rfl
    (by rw [hs]; exact hheights EF P A logN trace pis)
    (fun indices t hidx ↦ by
      rw [hs] at hidx ⊢; exact hinputs EF P A logN trace pis hin hz indices t hidx)
    (fun index t hidx ↦ by
      rw [hs] at hidx ⊢
      obtain ⟨v', hv', hred, -⟩ := hInputs_eq EF P A logN trace pis hin hz
        (hBatchAlpha EF P A logN trace pis)
      rw [hv, List.cons.injEq] at hv'
      rw [hreduce EF P A logN trace pis hin hz _ index t hidx, hred, hv'.1]
      simp only [List.map_cons, List.map_nil, Nat.sub_self, Nat.shiftRight_zero])
  refine ⟨((proveFri (specBackend EF) P (hRounds EF P A logN trace pis) [v]
    (hBatch EF P A logN trace pis).1).run (hT2 EF P A logN trace pis)).2, ?_⟩
  have hcO : checkWitness (poseidon2 F) P.oodPowBits (hOod EF P A logN trace pis).1
      (hTC EF P A logN trace pis) = .ok (true, (hOod EF P A logN trace pis).2) :=
    (checkWitness_run _ _ _ hdC).trans (congrArg Except.ok (checkWitness_grind _ _ hgO))
  have hcB : checkWitness (poseidon2 F) P.batchPowBits (hBatch EF P A logN trace pis).1
      (hTP EF P A logN trace pis) = .ok (true, (hBatch EF P A logN trace pis).2) :=
    (checkWitness_run _ _ _ hdP).trans (congrArg Except.ok (checkWitness_grind _ _ hgB))
  rw [verifyRun_run, hTC', hTA', how, bind_ok hcO]
  rw [ensure_true, pure_bind, bind_ok (sampleExt_run _), hdb]
  have hzeta : ((hOod EF P A logN trace pis).2.sampleExtValue : EF) = hZeta EF P A logN trace pis :=
    rfl
  rw [hzeta, powTwo_ne_one hz (by have := hin.twoAdic; omega), ensure_true, pure_bind]
  have hPcs : verifyPcs (poseidon2 F) P (openingRounds A (setup P A logN)
      (prove EF P A logN trace pis) (hZeta EF P A logN trace pis)) (hFriRun EF P A logN trace pis).1
      (Transcript.sampleExtState EF (hOod EF P A logN trace pis).2) =
      .ok ((), ((proveFri (specBackend EF) P (hRounds EF P A logN trace pis) [v]
        (hBatch EF P A logN trace pis).1).run (hT2 EF P A logN trace pis)).2) := by
    rw [verifyPcs_run _ _ _ _ (by rw [hbw]; exact grind_canonical _ _), hTP', hbw, bind_ok hcB,
      ensure_true, pure_bind, bind_ok (sampleExt_run _), hrun]
    exact hF
  rw [hfri, bind_ok hPcs]
  rfl

end Honest

/-- Completeness with every assumption spelled out; `completeness` (`CompStark/Completeness.lean`)
groups them. -/
theorem verify_prove_of (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)
    (hin : Fits P A logN trace) (hsat : A.ConstraintsVanish logN trace pis)
    (hpis : pis.length = A.numPublicValues)
    (hdeg : A.DegreeFits logN) (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries)
    (hb : 0 < P.logBlowup) (hfin : P.logFinalPolyLen ≤ logN)
    (hgrind : (proveTranscript EF P A logN trace pis).grindFailed = false)
    (hz : Ext.OutsideBase (outOfDomainPoint EF P A logN trace pis)) :
    verify P A (setup P A logN) (prove EF P A logN trace pis) pis = .ok () := by
  rw [outOfDomainPoint_eq] at hz
  obtain ⟨t, hrun⟩ := verifyRun_honest EF P A logN trace pis hin hz hP hq hb hfin hgrind
  have hdb : (prove EF P A logN trace pis).degreeBits = logN := by rw [prove_eq]
  have hprep : (hPrep EF P A logN).map (·.1) = prepLde P.logBlowup A logN := by
    by_cases hpw : A.preprocessedWidth = 0
    · simp only [hPrep, setupWith, prepLde, hpw, ↓reduceIte, Option.map_none]
    · simp only [hPrep, setupWith, prepLde, hpw, ↓reduceIte, Option.map_some]
  refine verify_ok_of P A _ _ pis _ _ t
    (by rw [hdb]; have := hin.twoAdic; have := hin.chunks; omega) (by rw [hdb]; exact hin.periodic)
    hpis ?_ ?_ hrun ?_
  · rw [prove_eq, setup_eq]
    have := honest_shape (EF := EF) P A logN trace pis (hAlpha EF P A logN trace pis)
      (hZeta EF P A logN trace pis)
      (Merkle.Poseidon2.root F [(hPrepExt P A logN).toMatrix])
    rw [← hprep] at this
    exact this
  · rw [prove_eq]
    exact grind_canonical _ _
  · rw [prove_eq]
    have := checkConstraints_honest P A logN trace pis (hAlpha EF P A logN trace pis)
      (hZeta EF P A logN trace pis) hin hsat hdeg hz
    rw [← hprep] at this
    exact this

end CompStark.Stark
