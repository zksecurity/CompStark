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
same degree, commitments and public values, so it samples the same `α` and `ζ`; `verifyPcs`
observes the same opened values as `openPcs` and then accepts `proveFri`'s proof
(`verifyFri_proveFri`), whose inputs are the batched quotients of the honest openings
(`openInput_honest`).
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri CompStark.Complete

variable {F : Type} [BaseField F] [Poseidon2Field F]
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

variable {EF : Type} [Challenge F EF]

/-! ### The prover's run, step by step -/

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- The trace's extension. -/
def hExt : Mat F := ldeRef logN P.logBlowup gen A.width trace

/-- The transcript after the trace commitment and the public values. -/
def hTA : Transcript F 24 :=
  (((((Poseidon2.initTranscript.observe (logN : F)).observe (logN : F)).observe 0).observeList
    (Committed.ofMats hashF compF [hExt P A logN trace]).root.toList).observeList pis)

/-- The constraint-folding challenge. -/
def hAlpha : EF := ((hTA P A logN trace pis).sampleExtValue : EF)

/-- The quotient's chunks' extensions. -/
def hChunks : List (Mat F) :=
  let lc := A.logQuotientChunks
  let qs := quotientOfLde A pis logN lc (hExt P A logN trace) (hAlpha EF P A logN trace pis)
  (List.range (2 ^ lc)).map fun c ↦
    ldeRef logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ lc) c (2 ^ logN))

/-- The transcript after the quotient commitment. -/
def hTC : Transcript F 24 :=
  (Transcript.sampleExtState EF ((hTA P A logN trace pis))).observeList
    (Committed.ofMats hashF compF (hChunks EF P A logN trace pis)).root.toList

/-- The out-of-domain point. -/
def hZeta : EF := ((hTC EF P A logN trace pis).sampleExtValue : EF)

theorem commitAndSample_run :
    (commitAndSample (specBackend EF) P A logN trace pis).run Poseidon2.initTranscript =
      ((hExt P A logN trace, Committed.ofMats hashF compF [hExt P A logN trace],
        hChunks EF P A logN trace pis, Committed.ofMats hashF compF (hChunks EF P A logN trace pis),
        hZeta EF P A logN trace pis),
        (Transcript.sampleExtState EF ((hTC EF P A logN trace pis)))) := rfl

theorem outOfDomainPoint_eq :
    outOfDomainPoint EF P A logN trace pis = hZeta EF P A logN trace pis :=
  rfl

end Honest

/-! ### Opening -/

omit [Poseidon2Field F] in
theorem observeExts_append (t : Transcript F 24) (a b : List EF) :
    t.observeExts (a ++ b) = (t.observeExts a).observeExts b := by
  simp only [Transcript.observeExts, List.foldl_append]

omit [Poseidon2Field F] in
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

theorem mapM_open (b : Nat) (ms : List (Mat F × List EF)) (t : Transcript F 24) :
    (ms.mapM fun x ↦ do
        ((specBackend EF).openedAt b x.1 x.2).forM fun ys ↦ pObserveExts ys.toList
        pure ((specBackend EF).openedAt b x.1 x.2, x.1,
            x.2.zip ((specBackend EF).openedAt b x.1 x.2)) :
      PM F 24 _).run t =
      (ms.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x)),
        t.observeExts ((ms.flatMap (openedOf b)).flatMap (·.toList))) := by
  induction ms generalizing t with
  | nil => rfl
  | cons x ms ih =>
    rw [List.mapM_cons]
    simp only [prun_bind, forM_observeExts, StateT.run_pure] at ih ⊢
    rw [ih]
    simp only [List.flatMap_cons, List.flatMap_append, observeExts_append, List.map_cons]
    rfl

theorem mapM_rounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) (t : Transcript F 24) :
    (rounds.mapM fun r ↦ r.2.mapM fun x ↦ do
        ((specBackend EF).openedAt b x.1 x.2).forM fun ys ↦ pObserveExts ys.toList
        pure ((specBackend EF).openedAt b x.1 x.2, x.1,
            x.2.zip ((specBackend EF).openedAt b x.1 x.2)) :
      PM F 24 _).run t =
      (rounds.map fun r ↦ r.2.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x)),
        t.observeExts ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf b)).flatMap (·.toList))) := by
  induction rounds generalizing t with
  | nil => rfl
  | cons r rounds ih =>
    rw [List.mapM_cons]
    simp only [prun_bind, StateT.run_pure] at ih ⊢
    erw [mapM_open, ih]
    simp only [List.flatMap_cons, List.flatMap_append, observeExts_append, List.map_cons]
    rfl

theorem openPcs_run (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (t : Transcript F 24) :
    (openPcs (specBackend EF) P rounds).run t =
      let opened := rounds.map fun r ↦ r.2.map fun x ↦
        (openedOf P.logBlowup x, x.1, x.2.zip (openedOf P.logBlowup x))
      let t2 := t.observeExts
        ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap (·.toList))
      let fri := proveFri (specBackend EF) P rounds fun alpha ↦
        (Fri.reduce alpha (opened.flatten.map (·.2))).map (·.2)
      ((opened.map (·.map (·.1)), (fri.run t2).1), (fri.run t2).2) := by
  unfold openPcs
  simp only [prun_bind]
  rw [mapM_rounds]
  rfl

/-! ### The proof -/

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- `ζ ω`. -/
def hZetaNext : EF := hZeta EF P A logN trace pis * Ext.ofBase (twoAdicGen logN)

/-- The rounds the prover opens. -/
def hRounds : List (OpenRound (specBackend EF)) :=
  [(Committed.ofMats hashF compF [hExt P A logN trace],
      [(hExt P A logN trace, [hZeta EF P A logN trace pis, hZetaNext EF P A logN trace pis])]),
    (Committed.ofMats hashF compF (hChunks EF P A logN trace pis),
      (hChunks EF P A logN trace pis).map fun m ↦ (m, [hZeta EF P A logN trace pis]))]

/-- The opened values, with their matrices and points. -/
def hOpened : List (List (List (Array EF) × Mat F × List (EF × Array EF))) :=
  (hRounds EF P A logN trace pis).map fun r ↦ r.2.map fun x ↦
    (openedOf P.logBlowup x, x.1, x.2.zip (openedOf P.logBlowup x))

/-- The transcript after observing the opened values. -/
def hT2 : Transcript F 24 :=
  (Transcript.sampleExtState EF ((hTC EF P A logN trace pis))).observeExts
    (((hRounds EF P A logN trace pis).flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap
      (·.toList))

/-- FRI's inputs for the batching challenge `α`. -/
def hInputs (alpha : EF) : List (Array EF) :=
  (Fri.reduce alpha ((hOpened EF P A logN trace pis).flatten.map (·.2))).map (·.2)

/-- The FRI proof. -/
def hFri : FriProof F EF :=
  ((proveFri (specBackend EF) P (hRounds EF P A logN trace pis)
    (hInputs EF P A logN trace pis)).run
    (hT2 EF P A logN trace pis)).1

theorem prove_eq : prove EF P A logN trace pis =
    { traceCommit := (Committed.ofMats hashF compF [hExt P A logN trace]).root
      quotientCommit := (Committed.ofMats hashF compF (hChunks EF P A logN trace pis)).root
      opened := ⟨Fri.openedAt P.logBlowup (hExt P A logN trace) (hZeta EF P A logN trace pis),
        Fri.openedAt P.logBlowup (hExt P A logN trace) (hZetaNext EF P A logN trace pis),
        ((hChunks EF P A logN trace pis).map fun m ↦
          Fri.openedAt P.logBlowup m (hZeta EF P A logN trace pis)).toArray⟩
      fri := hFri EF P A logN trace pis
      degreeBits := logN } := by
  unfold prove proveWith
  rw [prun_bind]
  erw [commitAndSample_run]
  unfold openAndAssemble
  simp only [prun_bind]
  erw [openPcs_run]
  simp only [StateT.run_pure]
  show Proof.mk _ _ _ _ _ = Proof.mk _ _ _ _ _
  simp only [Proof.mk.injEq, OpenedValues.mk.injEq, and_true, List.map_cons,
    List.map_nil, List.getD_cons_succ, List.getD_cons_zero, List.map_map]
  repeat' apply And.intro
  all_goals try rfl
  refine congrArg List.toArray ?_
  induction hChunks EF P A logN trace pis with
  | nil => rfl
  | cons m ms ih => exact congrArg (List.cons _) ih

omit [Poseidon2Field F] in
/-- The prover's final transcript is FRI's. -/
theorem proveTranscript_eq [Poseidon2Field F] : proveTranscript EF P A logN trace pis =
    ((proveFri (specBackend EF) P (hRounds EF P A logN trace pis)
      (hInputs EF P A logN trace pis)).run
      (hT2 EF P A logN trace pis)).2 := by
  unfold proveTranscript
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

theorem verifyPcs_eq (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF) :
    verifyPcs (poseidon2 F) P rounds proof =
      (do forIn rounds PUnit.unit obsRounds; verifyFri (poseidon2 F) P proof rounds) :=
  rfl

theorem forIn_obsPts (pts : List (EF × List EF)) (t : Transcript F 24) :
    forIn pts PUnit.unit obsPts t = .ok (PUnit.unit, t.observeExts (pts.flatMap (·.2))) := by
  induction pts generalizing t with
  | nil => rfl
  | cons p pts ih =>
    rw [forIn_cons_ok p pts _ PUnit.unit obsPts t (t.observeExts p.2)
      (bind_ok (observeExts_run t p.2)), ih,
      List.flatMap_cons, observeExts_append]

theorem forIn_obsMats (mats : List (Domain F × List (EF × List EF))) (t : Transcript F 24) :
    forIn mats PUnit.unit obsMats t =
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

theorem verifyPcs_run (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF) (t :
    Transcript F 24) :
    verifyPcs (poseidon2 F) P rounds proof t = verifyFri (poseidon2 F) P proof rounds
      (t.observeExts (rounds.flatMap fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2))) := by
  rw [verifyPcs_eq, bind_ok (forIn_obsRounds rounds t)]

/-! ### The verifier -/

/-- The verifier's transcript after the trace commitment and the public values. -/
def vTA (proof : Proof F EF) (pis : List F) : Transcript F 24 :=
  (((((Poseidon2.initTranscript.observe (proof.degreeBits : F)).observe
      (proof.degreeBits : F)).observe
    0).observeList proof.traceCommit.toList).observeList pis)

/-- The verifier's transcript after the quotient commitment. -/
def vTC (proof : Proof F EF) (pis : List F) : Transcript F 24 :=
  (Transcript.sampleExtState EF ((vTA proof pis))).observeList proof.quotientCommit.toList

/-- The transcript part of `verify`. -/
def verifyRun (P : Params) (proof : Proof F EF) (pis : List F) : M (poseidon2 F) (EF × EF) := do
  let db := proof.degreeBits
  let o := proof.opened
  observe (poseidon2 F) (db : F)
  observe (poseidon2 F) (db : F)
  observe (poseidon2 F) 0
  observeList (poseidon2 F) proof.traceCommit.toList
  observeList (poseidon2 F) pis
  let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  observeList (poseidon2 F) proof.quotientCommit.toList
  let zeta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  let zetaNext := zeta * Ext.ofBase (twoAdicGen db)
  let traceDomain : Domain F := ⟨1, db⟩
  verifyPcs (poseidon2 F) P
    [(proof.traceCommit, [(traceDomain, [(zeta, o.traceLocal.toList),
        (zetaNext, o.traceNext.toList)])]),
     (proof.quotientCommit, o.quotientChunks.toList.map fun ch ↦
        (traceDomain, [(zeta, ch.toList)]))]
    proof.fri
  return (alpha, zeta)

/-- The out-of-domain check of `verify`, after the transcript. -/
def verifyCheck (A : Air F) (proof : Proof F EF) (pis : List F) (x : (EF × EF) × Transcript F 24) :
    ExceptT String Id Unit :=
  unless checkConstraints A pis proof.opened proof.degreeBits x.1.2 x.1.1
      (recompose (chunkDomains proof.degreeBits A.logQuotientChunks)
        proof.opened.quotientChunks.toList x.1.2) do
    throw "out-of-domain evaluation mismatch"

omit [Poseidon2Field F] in
theorem verifyCheck_ok (A : Air F) (proof : Proof F EF) (pis : List F)
    (x : (EF × EF) × Transcript F 24)
    (h : checkConstraints A pis proof.opened proof.degreeBits x.1.2 x.1.1
      (recompose (chunkDomains proof.degreeBits A.logQuotientChunks)
        proof.opened.quotientChunks.toList x.1.2) = true) :
    verifyCheck A proof pis x = pure () := by
  unfold verifyCheck
  rw [h]
  rfl

theorem verify_eq (P : Params) (A : Air F) (proof : Proof F EF) (pis : List F) :
    verify P A proof pis = ExceptT.run (do
      let o := proof.opened
      unless o.traceLocal.size == A.width && o.traceNext.size == A.width &&
          o.quotientChunks.size == 2 ^ A.logQuotientChunks &&
          o.quotientChunks.all (·.size == Challenge.d EF) do
        throw "invalid proof shape"
      unless arities proof.fri ==
          foldArities P.maxLogArity (proof.degreeBits - P.logFinalPolyLen) do
        throw "fold arities"
      (verifyRun P proof pis).run Poseidon2.initTranscript >>= verifyCheck A proof pis) := by
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

theorem verifyRun_run (P : Params) (proof : Proof F EF) (pis : List F) :
    verifyRun P proof pis Poseidon2.initTranscript =
      (verifyPcs (poseidon2 F) P (vRounds proof ((vTC proof pis).sampleExtValue : EF)) proof.fri >>=
          fun _ ↦
        pure (((vTA proof pis).sampleExtValue : EF), ((vTC proof pis).sampleExtValue : EF)))
        (Transcript.sampleExtState EF ((vTC proof pis))) := by
  simp only [verifyRun, observe_bind, observeList_bind, sampleExt_bind]
  rfl

/-! ### The honest openings -/

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

omit [Poseidon2Field F] in
/-- An LDE opened at points outside the base field is an honest item of the batched quotients. -/
theorem honestItem_of (b h : Nat) (m : Mat F) (zs : List EF) (ps : List (Polynomial F))
    (hm : CompStark.Mat.IsLde b h m ps) (hzs : ∀ z ∈ zs, Ext.OutsideBase z) :
    Deep.HonestItem b h (m, zs.zip (openedOf b (m, zs))) := by
  refine ⟨ps, hm, fun y hy ↦ ?_⟩
  obtain ⟨hz, hy2⟩ := mem_zip_map (Fri.openedAt b m) zs y hy
  obtain ⟨hs, hv⟩ := openedAt_isLde b h m ps y.1 hm (hzs _ hz)
  exact ⟨hzs _ hz, hy2 ▸ hs, fun j hj ↦ hy2 ▸ hv j hj⟩

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

/-- The matrices FRI batches, with their opened points and values. -/
def hItems : List (Mat F × List (EF × Array EF)) :=
  (hOpened EF P A logN trace pis).flatten.map (·.2)

theorem hItems_eq : hItems EF P A logN trace pis =
    (hExt P A logN trace, [hZeta EF P A logN trace pis, hZetaNext EF P A logN trace pis].zip
      (openedOf P.logBlowup (hExt P A logN trace,
        [hZeta EF P A logN trace pis, hZetaNext EF P A logN trace pis]))) ::
    (hChunks EF P A logN trace pis).map fun m ↦
      (m, [hZeta EF P A logN trace pis].zip
        (openedOf P.logBlowup (m, [hZeta EF P A logN trace pis]))) := by
  simp only [hItems, hOpened, hRounds, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [List.map_append]
  refine congrArg (List.cons _) ?_
  induction hChunks EF P A logN trace pis with
  | nil => rfl
  | cons m ms ih => exact congrArg (List.cons _) ih

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
    rcases List.mem_cons.mp hz' with rfl | hz'
    · exact hz
    · rw [List.mem_singleton] at hz'; exact hz' ▸ hzn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
    obtain ⟨ps, hlde, -⟩ := chunk_isLde (EF := EF) P A logN _ hin.twoAdic hin.chunks c
    exact honestItem_of _ _ _ _ ps hlde fun z hz' ↦ (List.mem_singleton.mp hz') ▸ hz

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

/-- The rounds with their openings, as `openInput_honest` takes them. -/
def hDRounds : List (Committed F × List (Mat F × List (EF × Array EF))) :=
  [(Committed.ofMats hashF compF [hExt P A logN trace],
      [(hExt P A logN trace, [hZeta EF P A logN trace pis, hZetaNext EF P A logN trace pis].zip
        (openedOf P.logBlowup (hExt P A logN trace,
          [hZeta EF P A logN trace pis, hZetaNext EF P A logN trace pis])))]),
    (Committed.ofMats hashF compF (hChunks EF P A logN trace pis),
      (hChunks EF P A logN trace pis).map (hItemC EF P A logN trace pis))]

theorem map_fst_hItemC (ms : List (Mat F)) :
    (ms.map (hItemC EF P A logN trace pis)).map (·.1) = ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => exact congrArg (List.cons m) ih

theorem flatMap_hDRounds :
    (hDRounds EF P A logN trace pis).flatMap (·.2) = hItems EF P A logN trace pis := by
  rw [hItems_eq]
  simp only [hDRounds, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem hChunks_ne_nil : hChunks EF P A logN trace pis ≠ [] := by
  simp only [hChunks, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)

end Honest

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

omit [Poseidon2Field F] in
theorem height_hExt (hin : Fits P A logN trace) :
    (hExt P A logN trace).height = 2 ^ (logN + P.logBlowup) := by
  obtain ⟨ps, hl, -⟩ := trace_lde P A logN trace hin
  exact hl.2.1

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

theorem vRounds_eq (hin : Fits P A logN trace) :
    vRounds (prove EF P A logN trace pis) (hZeta EF P A logN trace pis) =
      (hDRounds EF P A logN trace pis).map fun r ↦ (r.1.root, r.2.map fun x ↦
        ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
          x.2.map fun y ↦ (y.1, y.2.toList))) := by
  rw [prove_eq]
  simp only [vRounds, hDRounds, List.map_cons, List.map_nil, height_hExt P A logN trace hin,
    Nat.log2_two_pow, Nat.add_sub_cancel]
  rw [vChunks_eq EF P A logN trace pis _ (height_hChunks EF P A logN trace pis hin)]
  rfl

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

theorem inputsOk_hInputs (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (hfin : P.logFinalPolyLen ≤ logN)
    (alpha : EF) : InputsOk P (hInputs EF P A logN trace pis alpha) := by
  obtain ⟨v, hv, -, hl⟩ := hInputs_eq EF P A logN trace pis hin hz alpha
  have hs := log2_size hl
  refine ⟨v, [], hv, ?_⟩
  rw [hs]
  refine ⟨by omega, by rwa [Nat.add_sub_cancel], List.Pairwise.nil, fun w hw ↦ ?_⟩
  exact absurd hw List.not_mem_nil

theorem hopen (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (alpha : EF) (index : Nat)
    (hidx : index < 2 ^ Nat.log2 (((hInputs EF P A logN trace pis alpha).map Array.size).headD 0)) :
    openInput (poseidon2 F) P
        (Nat.log2 (((hInputs EF P A logN trace pis alpha).map Array.size).headD 0))
        index alpha ((hRounds EF P A logN trace pis).map fun (c, _) ↦ c.openAt (index >>>
          (Nat.log2 (((hInputs EF P A logN trace pis alpha).map Array.size).headD 0) -
            Nat.log2 c.maxHeight)))
        (vRounds (prove EF P A logN trace pis) (hZeta EF P A logN trace pis)) =
      pure ((hInputs EF P A logN trace pis alpha).map fun v ↦ (Nat.log2 v.size, v.getD (index >>>
        (Nat.log2 (((hInputs EF P A logN trace pis alpha).map Array.size).headD 0) -
          Nat.log2 v.size)) 0)) := by
  obtain ⟨v, hv, hred, hl⟩ := hInputs_eq EF P A logN trace pis hin hz alpha
  have hs := log2_size hl
  have hL : Nat.log2 (((hInputs EF P A logN trace pis alpha).map Array.size).headD 0) =
      logN + P.logBlowup := by
    rw [hv]; exact hs
  rw [hL] at hidx ⊢
  rw [vRounds_eq EF P A logN trace pis hin, hv]
  have hon := hItems_honest EF P A logN trace pis hin hz
  rw [← flatMap_hDRounds] at hon
  have hD := openInput_honest P (logN + P.logBlowup) index alpha (hDRounds EF P A logN trace pis)
    hidx fun r hr ↦ by
      refine ⟨?_, ?_, logN + P.logBlowup, le_rfl, fun x hx ↦
        hon x (List.mem_flatMap.mpr ⟨r, hr, hx⟩)⟩
      · simp only [hDRounds, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.cons_ne_nil _ _
        · simp only [ne_eq, List.map_eq_nil_iff]
          exact hChunks_ne_nil EF P A logN trace pis
      · simp only [hDRounds, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · rfl
        · exact congrArg (Committed.ofMats hashF compF)
            (map_fst_hItemC EF P A logN trace pis _).symm
  rw [flatMap_hDRounds, hred] at hD
  rw [List.map_singleton, hs]
  exact hD

end Honest

omit [Poseidon2Field F] in
theorem flatMap_zip_openedOf (b : Nat) (m : Mat F) (zs : List EF) :
    ((zs.zip (openedOf b (m, zs))).map fun y ↦ (y.1, y.2.toList)).flatMap (·.2) =
      (openedOf b (m, zs)).flatMap (·.toList) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [openedOf, List.map_cons, List.zip_cons_cons, List.flatMap_cons] at ih ⊢
    rw [ih]

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
    (vRounds (prove EF P A logN trace pis) (hZeta EF P A logN trace pis)).flatMap
      (fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) =
    ((hRounds EF P A logN trace pis).flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap
      (·.toList) := by
  rw [vRounds_eq EF P A logN trace pis hin]
  simp only [hDRounds, hRounds, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_append]
  rw [flat_chunks, flatMap_zip_openedOf]
  rfl

end Honest

/-! ### Completeness -/

theorem verify_ok_of (P : Params) (A : Air F) (proof : Proof F EF) (pis : List F) (alpha zeta : EF)
    (t : Transcript F 24)
    (hshape : (proof.opened.traceLocal.size == A.width && proof.opened.traceNext.size == A.width &&
      proof.opened.quotientChunks.size == 2 ^ A.logQuotientChunks &&
      proof.opened.quotientChunks.all (·.size == Challenge.d EF)) = true)
    (harities :
      arities proof.fri = foldArities P.maxLogArity (proof.degreeBits - P.logFinalPolyLen))
    (hrun : verifyRun P proof pis Poseidon2.initTranscript = .ok ((alpha, zeta), t))
    (hcheck : checkConstraints A pis proof.opened proof.degreeBits zeta alpha
      (recompose (chunkDomains proof.degreeBits A.logQuotientChunks)
        proof.opened.quotientChunks.toList zeta) = true) :
    verify P A proof pis = .ok () := by
  have hrun' : StateT.run (verifyRun P proof pis) Poseidon2.initTranscript = pure
      ((alpha, zeta), t) := hrun
  rw [verify_eq, hrun', pure_bind, verifyCheck_ok A proof pis ((alpha, zeta), t) hcheck]
  simp only [hshape, harities, beq_self_eq_true]
  rfl

section Honest
variable (EF) (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)

theorem verifyRun_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis))
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hfin : P.logFinalPolyLen ≤ logN)
    (hgrind : (proveTranscript EF P A logN trace pis).grindFailed = false) :
    ∃ t, verifyRun P (prove EF P A logN trace pis) pis Poseidon2.initTranscript =
      .ok ((hAlpha EF P A logN trace pis, hZeta EF P A logN trace pis), t) := by
  have hTC : vTC (prove EF P A logN trace pis) pis = hTC EF P A logN trace pis := by
    rw [prove_eq]; rfl
  have hTA : vTA (prove EF P A logN trace pis) pis = hTA P A logN trace pis := by
    rw [prove_eq]; rfl
  rw [verifyRun_run, hTC, hTA]
  have hzeta :
      ((Stark.hTC EF P A logN trace pis).sampleExtValue : EF) = hZeta EF P A logN trace pis :=
      rfl
  rw [hzeta]
  have hfri : (prove EF P A logN trace pis).fri = hFri EF P A logN trace pis := by rw [prove_eq]
  have hF := verifyFri_proveFri P (hRounds EF P A logN trace pis) (hInputs EF P A logN trace pis)
    (vRounds (prove EF P A logN trace pis) (hZeta EF P A logN trace pis))
    (hT2 EF P A logN trace pis)
    (by rw [hT2, duplex_observeExts, duplex_sampleExt, Stark.hTC, duplex_observeList,
      duplex_sampleExt, Stark.hTA]; rfl)
    (inputsOk_hInputs EF P A logN trace pis hin hz hfin) hP hq
    (by rw [← proveTranscript_eq]; exact hgrind)
    (fun alpha index hidx ↦ hopen EF P A logN trace pis hin hz alpha index hidx)
  refine ⟨((proveFri (specBackend EF) P (hRounds EF P A logN trace pis)
    (hInputs EF P A logN trace pis)).run (hT2 EF P A logN trace pis)).2, ?_⟩
  rw [bind_ok (by rw [verifyPcs_run, hfri, flat_eq EF P A logN trace pis hin]; exact hF)]
  rfl

end Honest

/-- The honest proof folds by Plonky3's schedule. -/
theorem arities_prove (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)
    (hin : Fits P A logN trace) (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries)
    (hfin : P.logFinalPolyLen ≤ logN) (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) :
    arities (prove EF P A logN trace pis).fri =
      foldArities P.maxLogArity ((prove EF P A logN trace pis).degreeBits - P.logFinalPolyLen) := by
  obtain ⟨v, hv, -,
    hl⟩ := hInputs_eq EF P A logN trace pis hin hz ((hT2 EF P A logN trace pis).sampleExtValue : EF)
  obtain ⟨f0, rest, hf, hg⟩ := inputsOk_hInputs EF P A logN trace pis hin hz hfin
    ((hT2 EF P A logN trace pis).sampleExtValue : EF)
  rw [hv, List.cons.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have hdb : (prove EF P A logN trace pis).degreeBits = logN := by rw [prove_eq]
  have hfri : (prove EF P A logN trace pis).fri = hFri EF P A logN trace pis := by rw [prove_eq]
  rw [hfri, hdb, hFri,
      arities_proveFri P (hRounds EF P A logN trace pis) (hInputs EF P A logN trace pis)
    (hT2 EF P A logN trace pis) v hv hg hP hq]
  have hlog : Nat.log2 v.size - (P.logBlowup + P.logFinalPolyLen) = logN - P.logFinalPolyLen := by
    rw [log2_size hl]; omega
  exact congrArg _ hlog

/-- Completeness with every assumption spelled out; `completeness` (`CompStark/Completeness.lean`)
groups them. -/
theorem verify_prove_of (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)
    (hin : Fits P A logN trace) (hsat : A.ConstraintsVanish logN trace pis)
    (hdeg : A.DegreeFits logN) (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries)
    (hfin : P.logFinalPolyLen ≤ logN)
    (hgrind : (proveTranscript EF P A logN trace pis).grindFailed = false)
    (hz : Ext.OutsideBase (outOfDomainPoint EF P A logN trace pis)) :
    verify P A (prove EF P A logN trace pis) pis = .ok () := by
  rw [outOfDomainPoint_eq] at hz
  obtain ⟨t, hrun⟩ := verifyRun_honest EF P A logN trace pis hin hz hP hq hfin hgrind
  refine verify_ok_of P A _ pis _ _ t ?_ ?_ hrun ?_
  · rw [prove_eq]
    exact honest_shape P A logN trace pis (hAlpha EF P A logN trace pis)
      (hZeta EF P A logN trace pis)
  · exact arities_prove P A logN trace pis hin hP hq hfin hz
  · rw [prove_eq]
    exact checkConstraints_honest P A logN trace pis (hAlpha EF P A logN trace pis)
      (hZeta EF P A logN trace pis) hin hsat hdeg hz

end CompStark.Stark
