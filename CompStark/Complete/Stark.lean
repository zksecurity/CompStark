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
open CompStark.Fri CompStark.KoalaBear CompStark.Complete

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-! ### The prover's run, step by step -/

section Honest
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

/-- The trace's extension. -/
def hExt : Mat := ldeRef logN P.logBlowup gen A.width trace

/-- The transcript after the trace commitment and the public values. -/
def hTA : Transcript :=
  (((((Transcript.init.observe (logN : F)).observe (logN : F)).observe 0).observeList
    (Committed.ofMats [hExt P A logN trace]).root.toList).observeList pis)

/-- The constraint-folding challenge. -/
def hAlpha : EF := (hTA P A logN trace pis).sampleExt.1

/-- The quotient's chunks' extensions. -/
def hChunks : List Mat :=
  let lc := A.logQuotientChunks
  let qs := quotientOfLde A pis logN lc (hExt P A logN trace) (hAlpha P A logN trace pis)
  (List.range (2 ^ lc)).map fun c ↦
    ldeRef logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) 4
      (chunkValues qs (2 ^ lc) c (2 ^ logN))

/-- The transcript after the quotient commitment. -/
def hTC : Transcript :=
  (hTA P A logN trace pis).sampleExt.2.observeList
    (Committed.ofMats (hChunks P A logN trace pis)).root.toList

/-- The out-of-domain point. -/
def hZeta : EF := (hTC P A logN trace pis).sampleExt.1

theorem commitAndSample_run :
    (commitAndSample Backend.spec P A logN trace pis).run Transcript.init =
      ((hExt P A logN trace, Committed.ofMats [hExt P A logN trace],
        hChunks P A logN trace pis, Committed.ofMats (hChunks P A logN trace pis),
        hZeta P A logN trace pis), (hTC P A logN trace pis).sampleExt.2) := rfl

theorem outOfDomainPoint_eq : outOfDomainPoint P A logN trace pis = hZeta P A logN trace pis := rfl

end Honest

/-! ### Opening -/

theorem observeExts_append (t : Transcript) (a b : List EF) :
    t.observeExts (a ++ b) = (t.observeExts a).observeExts b := by
  simp only [Transcript.observeExts, List.foldl_append]

theorem forM_observeExts (ov : List (Array EF)) (t : Transcript) :
    (ov.forM fun ys ↦ pObserveExts ys.toList).run t =
      ((), t.observeExts (ov.flatMap (·.toList))) := by
  induction ov generalizing t with
  | nil => rfl
  | cons ys ov ih =>
    show (pObserveExts ys.toList >>= fun _ ↦ ov.forM fun ys ↦ pObserveExts ys.toList).run t = _
    rw [prun_bind, List.flatMap_cons, observeExts_append]
    exact ih _

/-- The values the specification opens of a matrix at its points. -/
def openedOf (b : Nat) (x : Mat × List EF) : List (Array EF) := x.2.map (Fri.openedAt b x.1)

theorem mapM_open (b : Nat) (ms : List (Mat × List EF)) (t : Transcript) :
    (ms.mapM fun x ↦ do
        (Backend.spec.openedAt b x.1 x.2).forM fun ys ↦ pObserveExts ys.toList
        pure (Backend.spec.openedAt b x.1 x.2, x.1, x.2.zip (Backend.spec.openedAt b x.1 x.2)) :
      PM _).run t =
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

theorem mapM_rounds (b : Nat) (rounds : List (OpenRound Backend.spec)) (t : Transcript) :
    (rounds.mapM fun r ↦ r.2.mapM fun x ↦ do
        (Backend.spec.openedAt b x.1 x.2).forM fun ys ↦ pObserveExts ys.toList
        pure (Backend.spec.openedAt b x.1 x.2, x.1, x.2.zip (Backend.spec.openedAt b x.1 x.2)) :
      PM _).run t =
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

theorem openPcs_run (P : Params) (rounds : List (OpenRound Backend.spec)) (t : Transcript) :
    (openPcs Backend.spec P rounds).run t =
      let opened := rounds.map fun r ↦ r.2.map fun x ↦
        (openedOf P.logBlowup x, x.1, x.2.zip (openedOf P.logBlowup x))
      let t2 := t.observeExts
        ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap (·.toList))
      let fri := proveFri Backend.spec P rounds fun alpha ↦
        (Fri.reduce alpha (opened.flatten.map (·.2))).map (·.2)
      ((opened.map (·.map (·.1)), (fri.run t2).1), (fri.run t2).2) := by
  unfold openPcs
  simp only [prun_bind]
  rw [mapM_rounds]
  rfl

/-! ### The proof -/

section Honest
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

/-- `ζ ω`. -/
def hZetaNext : EF := hZeta P A logN trace pis * Ext.ofBase (twoAdicGen logN)

/-- The rounds the prover opens. -/
def hRounds : List (OpenRound Backend.spec) :=
  [(Committed.ofMats [hExt P A logN trace],
      [(hExt P A logN trace, [hZeta P A logN trace pis, hZetaNext P A logN trace pis])]),
    (Committed.ofMats (hChunks P A logN trace pis),
      (hChunks P A logN trace pis).map fun m ↦ (m, [hZeta P A logN trace pis]))]

/-- The opened values, with their matrices and points. -/
def hOpened : List (List (List (Array EF) × Mat × List (EF × Array EF))) :=
  (hRounds P A logN trace pis).map fun r ↦ r.2.map fun x ↦
    (openedOf P.logBlowup x, x.1, x.2.zip (openedOf P.logBlowup x))

/-- The transcript after observing the opened values. -/
def hT2 : Transcript :=
  (hTC P A logN trace pis).sampleExt.2.observeExts
    (((hRounds P A logN trace pis).flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap
      (·.toList))

/-- FRI's inputs for the batching challenge `α`. -/
def hInputs (alpha : EF) : List (Array EF) :=
  (Fri.reduce alpha ((hOpened P A logN trace pis).flatten.map (·.2))).map (·.2)

/-- The FRI proof. -/
def hFri : FriProof :=
  ((proveFri Backend.spec P (hRounds P A logN trace pis) (hInputs P A logN trace pis)).run
    (hT2 P A logN trace pis)).1

theorem prove_eq : prove P A logN trace pis =
    { traceCommit := (Committed.ofMats [hExt P A logN trace]).root
      quotientCommit := (Committed.ofMats (hChunks P A logN trace pis)).root
      opened := ⟨Fri.openedAt P.logBlowup (hExt P A logN trace) (hZeta P A logN trace pis),
        Fri.openedAt P.logBlowup (hExt P A logN trace) (hZetaNext P A logN trace pis),
        ((hChunks P A logN trace pis).map fun m ↦
          Fri.openedAt P.logBlowup m (hZeta P A logN trace pis)).toArray⟩
      fri := hFri P A logN trace pis
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
  induction hChunks P A logN trace pis with
  | nil => rfl
  | cons m ms ih => exact congrArg (List.cons _) ih

end Honest

/-! ### The verifier's observations -/

/-- The innermost body of `verifyPcs`'s observation loop. -/
def obsPts (p : EF × List EF) (_ : PUnit) : M (ForInStep PUnit) := do
  observeExts p.2
  pure (ForInStep.yield PUnit.unit)

/-- The middle body of `verifyPcs`'s observation loop. -/
def obsMats (x : Domain × List (EF × List EF)) (_ : PUnit) : M (ForInStep PUnit) := do
  forIn x.2 PUnit.unit obsPts
  pure (ForInStep.yield PUnit.unit)

/-- The outer body of `verifyPcs`'s observation loop. -/
def obsRounds (r : Round) (_ : PUnit) : M (ForInStep PUnit) := do
  forIn r.2 PUnit.unit obsMats
  pure (ForInStep.yield PUnit.unit)

theorem verifyPcs_eq (P : Params) (rounds : List Round) (proof : FriProof) :
    verifyPcs P rounds proof = (do forIn rounds PUnit.unit obsRounds; verifyFri P proof rounds) :=
  rfl

theorem forIn_obsPts (pts : List (EF × List EF)) (t : Transcript) :
    forIn pts PUnit.unit obsPts t = .ok (PUnit.unit, t.observeExts (pts.flatMap (·.2))) := by
  induction pts generalizing t with
  | nil => rfl
  | cons p pts ih =>
    rw [forIn_cons_ok p pts _ PUnit.unit obsPts t (t.observeExts p.2) rfl, ih,
      List.flatMap_cons, observeExts_append]

theorem forIn_obsMats (mats : List (Domain × List (EF × List EF))) (t : Transcript) :
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

theorem forIn_obsRounds (rounds : List Round) (t : Transcript) :
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

theorem verifyPcs_run (P : Params) (rounds : List Round) (proof : FriProof) (t : Transcript) :
    verifyPcs P rounds proof t = verifyFri P proof rounds
      (t.observeExts (rounds.flatMap fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2))) := by
  rw [verifyPcs_eq, bind_ok (forIn_obsRounds rounds t)]

/-! ### The verifier -/

/-- The verifier's rounds of a proof. -/
def vRounds (proof : Proof) (zeta : EF) : List Round :=
  let o := proof.opened
  let traceDomain : Domain := ⟨1, proof.degreeBits⟩
  [(proof.traceCommit, [(traceDomain, [(zeta, o.traceLocal.toList),
      (zeta * Ext.ofBase (twoAdicGen proof.degreeBits), o.traceNext.toList)])]),
    (proof.quotientCommit, o.quotientChunks.toList.map fun ch ↦
      (traceDomain, [(zeta, ch.toList)]))]

/-- The verifier's transcript after the trace commitment and the public values. -/
def vTA (proof : Proof) (pis : List F) : Transcript :=
  (((((Transcript.init.observe (proof.degreeBits : F)).observe (proof.degreeBits : F)).observe
    0).observeList proof.traceCommit.toList).observeList pis)

/-- The verifier's transcript after the quotient commitment. -/
def vTC (proof : Proof) (pis : List F) : Transcript :=
  (vTA proof pis).sampleExt.2.observeList proof.quotientCommit.toList

/-- The transcript part of `verify`. -/
def verifyRun (P : Params) (proof : Proof) (pis : List F) : M (EF × EF) := do
  let db := proof.degreeBits
  let o := proof.opened
  observe (db : F)
  observe (db : F)
  observe 0
  observeList proof.traceCommit.toList
  observeList pis
  let alpha ← sampleExt
  observeList proof.quotientCommit.toList
  let zeta ← sampleExt
  let zetaNext := zeta * Ext.ofBase (twoAdicGen db)
  let traceDomain : Domain := ⟨1, db⟩
  verifyPcs P
    [(proof.traceCommit, [(traceDomain, [(zeta, o.traceLocal.toList),
        (zetaNext, o.traceNext.toList)])]),
     (proof.quotientCommit, o.quotientChunks.toList.map fun ch ↦
        (traceDomain, [(zeta, ch.toList)]))]
    proof.fri
  return (alpha, zeta)

/-- The out-of-domain check of `verify`, after the transcript. -/
def verifyCheck (A : Air) (proof : Proof) (pis : List F) (x : (EF × EF) × Transcript) :
    Except String Unit :=
  unless checkConstraints A pis proof.opened proof.degreeBits x.1.2 x.1.1
      (recompose (chunkDomains proof.degreeBits A.logQuotientChunks)
        proof.opened.quotientChunks.toList x.1.2) do
    throw "out-of-domain evaluation mismatch"

theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem verifyCheck_ok (A : Air) (proof : Proof) (pis : List F) (x : (EF × EF) × Transcript)
    (h : checkConstraints A pis proof.opened proof.degreeBits x.1.2 x.1.1
      (recompose (chunkDomains proof.degreeBits A.logQuotientChunks)
        proof.opened.quotientChunks.toList x.1.2) = true) :
    verifyCheck A proof pis x = .ok () := by
  unfold verifyCheck
  rw [h]
  rfl

theorem verify_eq (P : Params) (A : Air) (proof : Proof) (pis : List F) :
    verify P A proof pis = (do
      let o := proof.opened
      unless o.traceLocal.size == A.width && o.traceNext.size == A.width &&
          o.quotientChunks.size == 2 ^ A.logQuotientChunks &&
          o.quotientChunks.all (·.size == 4) do
        throw "invalid proof shape"
      (verifyRun P proof pis).run Transcript.init >>= verifyCheck A proof pis) := by
  delta verify verifyRun verifyCheck
  rfl

theorem observe_bind {β : Type} (x : F) (f : Unit → M β) (t : Transcript) :
    (observe x >>= f) t = f () (t.observe x) := bind_ok rfl

theorem observeList_bind {β : Type} (xs : List F) (f : Unit → M β) (t : Transcript) :
    (observeList xs >>= f) t = f () (t.observeList xs) := bind_ok rfl

theorem sampleExt_bind {β : Type} (f : EF → M β) (t : Transcript) :
    (sampleExt >>= f) t = f t.sampleExt.1 t.sampleExt.2 := bind_ok rfl

theorem verifyRun_run (P : Params) (proof : Proof) (pis : List F) :
    verifyRun P proof pis Transcript.init =
      (verifyPcs P (vRounds proof (vTC proof pis).sampleExt.1) proof.fri >>= fun _ ↦
        pure ((vTA proof pis).sampleExt.1, (vTC proof pis).sampleExt.1))
        (vTC proof pis).sampleExt.2 := by
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

/-- An LDE opened at points outside the base field is an honest item of the batched quotients. -/
theorem honestItem_of (b h : Nat) (m : Mat) (zs : List EF) (ps : List (Polynomial KoalaBear.Field))
    (hm : CompStark.Mat.IsLde b h m ps) (hzs : ∀ z ∈ zs, Ext.OutsideBase z) :
    Deep.HonestItem b h (m, zs.zip (openedOf b (m, zs))) := by
  refine ⟨ps, hm, fun y hy ↦ ?_⟩
  obtain ⟨hz, hy2⟩ := mem_zip_map (Fri.openedAt b m) zs y hy
  obtain ⟨hs, hv⟩ := openedAt_isLde b h m ps y.1 hm (hzs _ hz)
  exact ⟨hzs _ hz, hy2 ▸ hs, fun j hj ↦ hy2 ▸ hv j hj⟩

section Honest
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

/-- The matrices FRI batches, with their opened points and values. -/
def hItems : List (Mat × List (EF × Array EF)) :=
  (hOpened P A logN trace pis).flatten.map (·.2)

theorem hItems_eq : hItems P A logN trace pis =
    (hExt P A logN trace, [hZeta P A logN trace pis, hZetaNext P A logN trace pis].zip
      (openedOf P.logBlowup (hExt P A logN trace,
        [hZeta P A logN trace pis, hZetaNext P A logN trace pis]))) ::
    (hChunks P A logN trace pis).map fun m ↦
      (m, [hZeta P A logN trace pis].zip
        (openedOf P.logBlowup (m, [hZeta P A logN trace pis]))) := by
  simp only [hItems, hOpened, hRounds, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [List.map_append]
  refine congrArg (List.cons _) ?_
  induction hChunks P A logN trace pis with
  | nil => rfl
  | cons m ms ih => exact congrArg (List.cons _) ih

theorem hItems_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta P A logN trace pis)) :
    ∀ x ∈ hItems P A logN trace pis, Deep.HonestItem P.logBlowup (logN + P.logBlowup) x := by
  have hzn : Ext.OutsideBase (hZetaNext P A logN trace pis) :=
    outsideBase_mul_ofBase hz (twoAdicGen_ne_zero logN (by have := hin.twoAdic; omega))
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
    obtain ⟨ps, hlde, -⟩ := chunk_isLde P A logN _ hin.twoAdic hin.chunks c
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
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

/-- FRI has one input, low degree, of the extension's height. -/
theorem reduce_hItems (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta P A logN trace pis)) (alpha : EF) :
    ∃ v, Fri.reduce alpha (hItems P A logN trace pis) = [(logN + P.logBlowup, v)] ∧
      LowDegree (logN + P.logBlowup) logN v := by
  have hon := hItems_honest P A logN trace pis hin hz
  have hh : ∀ x ∈ hItems P A logN trace pis, x.1.height = 2 ^ (logN + P.logBlowup) :=
    fun x hx ↦ by obtain ⟨ps, hl, -⟩ := hon x hx; exact hl.2.1
  obtain ⟨hpw, hmem, -⟩ := reduce_heights alpha (hItems P A logN trace pis)
    fun x hx ↦ by rw [hh x hx, Nat.log2_two_pow]
  have hH : ∀ y ∈ Fri.reduce alpha (hItems P A logN trace pis), y.1 = logN + P.logBlowup := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (hmem y.1).mp (List.mem_map_of_mem hy)
    rw [← hxy, hh x hx, Nat.log2_two_pow]
  have hne : Fri.reduce alpha (hItems P A logN trace pis) ≠ [] := by
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
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

/-- A chunk with its opening at `ζ`. -/
def hItemC (m : Mat) : Mat × List (EF × Array EF) :=
  (m, [hZeta P A logN trace pis].zip (openedOf P.logBlowup (m, [hZeta P A logN trace pis])))

/-- The rounds with their openings, as `openInput_honest` takes them. -/
def hDRounds : List (Committed × List (Mat × List (EF × Array EF))) :=
  [(Committed.ofMats [hExt P A logN trace],
      [(hExt P A logN trace, [hZeta P A logN trace pis, hZetaNext P A logN trace pis].zip
        (openedOf P.logBlowup (hExt P A logN trace,
          [hZeta P A logN trace pis, hZetaNext P A logN trace pis])))]),
    (Committed.ofMats (hChunks P A logN trace pis),
      (hChunks P A logN trace pis).map (hItemC P A logN trace pis))]

theorem map_fst_hItemC (ms : List Mat) : (ms.map (hItemC P A logN trace pis)).map (·.1) = ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => exact congrArg (List.cons m) ih

theorem flatMap_hDRounds :
    (hDRounds P A logN trace pis).flatMap (·.2) = hItems P A logN trace pis := by
  rw [hItems_eq]
  simp only [hDRounds, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem hChunks_ne_nil : hChunks P A logN trace pis ≠ [] := by
  simp only [hChunks, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)

end Honest

section Honest
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

theorem height_hExt (hin : Fits P A logN trace) :
    (hExt P A logN trace).height = 2 ^ (logN + P.logBlowup) := by
  obtain ⟨ps, hl, -⟩ := trace_lde P A logN trace hin
  exact hl.2.1

theorem height_hChunks (hin : Fits P A logN trace) :
    ∀ m ∈ hChunks P A logN trace pis, m.height = 2 ^ (logN + P.logBlowup) := by
  intro m hm
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
  obtain ⟨ps, hl, -⟩ := chunk_isLde P A logN _ hin.twoAdic hin.chunks c
  exact hl.2.1

theorem vChunks_eq (ms : List Mat) (hms : ∀ m ∈ ms, m.height = 2 ^ (logN + P.logBlowup)) :
    (ms.map fun m ↦ Fri.openedAt P.logBlowup m (hZeta P A logN trace pis)).map
      (fun ch ↦ ((⟨1, logN⟩ : Domain), [(hZeta P A logN trace pis, ch.toList)])) =
    (ms.map (hItemC P A logN trace pis)).map fun x ↦
      ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain), x.2.map fun y ↦ (y.1, y.2.toList)) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons]
    rw [ih fun m' hm' ↦ hms m' (List.mem_cons_of_mem _ hm')]
    simp only [hItemC]
    rw [hms m List.mem_cons_self, Nat.log2_two_pow, Nat.add_sub_cancel]
    rfl

theorem vRounds_eq (hin : Fits P A logN trace) :
    vRounds (prove P A logN trace pis) (hZeta P A logN trace pis) =
      (hDRounds P A logN trace pis).map fun r ↦ (r.1.root, r.2.map fun x ↦
        ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain),
          x.2.map fun y ↦ (y.1, y.2.toList))) := by
  rw [prove_eq]
  simp only [vRounds, hDRounds, List.map_cons, List.map_nil, height_hExt P A logN trace hin,
    Nat.log2_two_pow, Nat.add_sub_cancel]
  rw [vChunks_eq P A logN trace pis _ (height_hChunks P A logN trace pis hin)]
  rfl

end Honest

section Honest
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

theorem hInputs_eq (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta P A logN trace pis)) (alpha : EF) :
    ∃ v, hInputs P A logN trace pis alpha = [v] ∧
      Fri.reduce alpha (hItems P A logN trace pis) = [(logN + P.logBlowup, v)] ∧
      LowDegree (logN + P.logBlowup) logN v := by
  obtain ⟨v, hv, hl⟩ := reduce_hItems P A logN trace pis hin hz alpha
  refine ⟨v, ?_, hv, hl⟩
  show (Fri.reduce alpha (hItems P A logN trace pis)).map (·.2) = _
  rw [hv]
  rfl

theorem inputsOk_hInputs (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta P A logN trace pis)) (hfin : P.logFinalPolyLen ≤ logN)
    (alpha : EF) : InputsOk P (hInputs P A logN trace pis alpha) := by
  obtain ⟨v, hv, -, hl⟩ := hInputs_eq P A logN trace pis hin hz alpha
  have hs := log2_size hl
  refine ⟨v, [], hv, ?_⟩
  rw [hs]
  refine ⟨by omega, by rwa [Nat.add_sub_cancel], List.Pairwise.nil, fun w hw ↦ ?_⟩
  exact absurd hw List.not_mem_nil

theorem hopen (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta P A logN trace pis)) (alpha : EF) (index : Nat)
    (hidx : index < 2 ^ Nat.log2 (((hInputs P A logN trace pis alpha).map Array.size).headD 0)) :
    openInput P (Nat.log2 (((hInputs P A logN trace pis alpha).map Array.size).headD 0)) index
        alpha ((hRounds P A logN trace pis).map fun (c, _) ↦ c.openAt (index >>>
          (Nat.log2 (((hInputs P A logN trace pis alpha).map Array.size).headD 0) -
            Nat.log2 c.maxHeight)))
        (vRounds (prove P A logN trace pis) (hZeta P A logN trace pis)) =
      pure ((hInputs P A logN trace pis alpha).map fun v ↦ (Nat.log2 v.size, v.getD (index >>>
        (Nat.log2 (((hInputs P A logN trace pis alpha).map Array.size).headD 0) -
          Nat.log2 v.size)) 0)) := by
  obtain ⟨v, hv, hred, hl⟩ := hInputs_eq P A logN trace pis hin hz alpha
  have hs := log2_size hl
  have hL : Nat.log2 (((hInputs P A logN trace pis alpha).map Array.size).headD 0) =
      logN + P.logBlowup := by
    rw [hv]; exact hs
  rw [hL] at hidx ⊢
  rw [vRounds_eq P A logN trace pis hin, hv]
  have hon := hItems_honest P A logN trace pis hin hz
  rw [← flatMap_hDRounds] at hon
  have hD := openInput_honest P (logN + P.logBlowup) index alpha (hDRounds P A logN trace pis)
    hidx fun r hr ↦ by
      refine ⟨?_, ?_, logN + P.logBlowup, le_rfl, fun x hx ↦
        hon x (List.mem_flatMap.mpr ⟨r, hr, hx⟩)⟩
      · simp only [hDRounds, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.cons_ne_nil _ _
        · simp only [ne_eq, List.map_eq_nil_iff]
          exact hChunks_ne_nil P A logN trace pis
      · simp only [hDRounds, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · rfl
        · exact congrArg Committed.ofMats (map_fst_hItemC P A logN trace pis _).symm
  rw [flatMap_hDRounds, hred] at hD
  rw [List.map_singleton, hs]
  exact hD

end Honest

theorem flatMap_zip_openedOf (b : Nat) (m : Mat) (zs : List EF) :
    ((zs.zip (openedOf b (m, zs))).map fun y ↦ (y.1, y.2.toList)).flatMap (·.2) =
      (openedOf b (m, zs)).flatMap (·.toList) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [openedOf, List.map_cons, List.zip_cons_cons, List.flatMap_cons] at ih ⊢
    rw [ih]

section Honest
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

theorem flat_chunks (ms : List Mat) :
    ((ms.map (hItemC P A logN trace pis)).map fun x ↦
      ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain),
        x.2.map fun y ↦ (y.1, y.2.toList))).flatMap
        (fun x ↦ x.2.flatMap (·.2)) =
      ((ms.map fun m ↦ (m, [hZeta P A logN trace pis])).flatMap (openedOf P.logBlowup)).flatMap
        (·.toList) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.flatMap_cons, List.flatMap_append] at ih ⊢
    rw [ih, hItemC, flatMap_zip_openedOf]

theorem flat_eq (hin : Fits P A logN trace) :
    (vRounds (prove P A logN trace pis) (hZeta P A logN trace pis)).flatMap
      (fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) =
    ((hRounds P A logN trace pis).flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap
      (·.toList) := by
  rw [vRounds_eq P A logN trace pis hin]
  simp only [hDRounds, hRounds, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_append]
  rw [flat_chunks, flatMap_zip_openedOf]
  rfl

end Honest

/-! ### Completeness -/

theorem verify_ok_of (P : Params) (A : Air) (proof : Proof) (pis : List F) (alpha zeta : EF)
    (t : Transcript)
    (hshape : (proof.opened.traceLocal.size == A.width && proof.opened.traceNext.size == A.width &&
      proof.opened.quotientChunks.size == 2 ^ A.logQuotientChunks &&
      proof.opened.quotientChunks.all (·.size == 4)) = true)
    (hrun : verifyRun P proof pis Transcript.init = .ok ((alpha, zeta), t))
    (hcheck : checkConstraints A pis proof.opened proof.degreeBits zeta alpha
      (recompose (chunkDomains proof.degreeBits A.logQuotientChunks)
        proof.opened.quotientChunks.toList zeta) = true) :
    verify P A proof pis = .ok () := by
  rw [verify_eq]
  simp only [hshape]
  show (verifyRun P proof pis Transcript.init >>= verifyCheck A proof pis) = _
  rw [hrun, except_ok_bind]
  exact verifyCheck_ok A proof pis ((alpha, zeta), t) hcheck

section Honest
variable (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)

theorem same_hT2 : Same Transcript.init (hT2 P A logN trace pis) := by
  unfold hT2 hTC hTA
  exact same_observeExts (same_sampleExt (same_observeList (same_sampleExt (same_observeList
    (same_observeList (same_observe (same_observe (same_observe ⟨rfl, rfl⟩ _) _) _) _) _)) _)) _

theorem verifyRun_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta P A logN trace pis))
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hfin : P.logFinalPolyLen ≤ logN)
    (hgrind : ∀ c, ∀ bits ∈ [P.commitPowBits, P.queryPowBits],
      (Challenger.checkWitness Transcript.init.duplex c bits
        (Transcript.init.grinder c bits)).1 = true) :
    ∃ t, verifyRun P (prove P A logN trace pis) pis Transcript.init =
      .ok ((hAlpha P A logN trace pis, hZeta P A logN trace pis), t) := by
  have hTC : vTC (prove P A logN trace pis) pis = hTC P A logN trace pis := by
    rw [prove_eq]; rfl
  have hTA : vTA (prove P A logN trace pis) pis = hTA P A logN trace pis := by
    rw [prove_eq]; rfl
  rw [verifyRun_run, hTC, hTA]
  have hzeta : (Stark.hTC P A logN trace pis).sampleExt.1 = hZeta P A logN trace pis := rfl
  rw [hzeta]
  have hfri : (prove P A logN trace pis).fri = hFri P A logN trace pis := by rw [prove_eq]
  have hsame := same_hT2 P A logN trace pis
  have hF := verifyFri_proveFri P (hRounds P A logN trace pis) (hInputs P A logN trace pis)
    (vRounds (prove P A logN trace pis) (hZeta P A logN trace pis)) (hT2 P A logN trace pis)
    (inputsOk_hInputs P A logN trace pis hin hz hfin) hP hq
    (by rw [hsame.1, hsame.2]; exact hgrind)
    (fun alpha index hidx ↦ hopen P A logN trace pis hin hz alpha index hidx)
  refine ⟨((proveFri Backend.spec P (hRounds P A logN trace pis)
    (hInputs P A logN trace pis)).run (hT2 P A logN trace pis)).2, ?_⟩
  rw [bind_ok (by rw [verifyPcs_run, hfri, flat_eq P A logN trace pis hin]; exact hF)]
  rfl

end Honest

/-- Completeness with every assumption spelled out; `completeness` (`CompStark/Complete.lean`)
groups them. -/
theorem verify_prove_of (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)
    (hin : Fits P A logN trace) (hsat : A.ConstraintsVanish logN trace pis)
    (hdeg : A.DegreeFits logN) (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries)
    (hfin : P.logFinalPolyLen ≤ logN)
    (hgrind : ∀ c, ∀ bits ∈ [P.commitPowBits, P.queryPowBits],
      (Challenger.checkWitness Transcript.init.duplex c bits
        (Transcript.init.grinder c bits)).1 = true)
    (hz : Ext.OutsideBase (outOfDomainPoint P A logN trace pis)) :
    verify P A (prove P A logN trace pis) pis = .ok () := by
  rw [outOfDomainPoint_eq] at hz
  obtain ⟨t, hrun⟩ := verifyRun_honest P A logN trace pis hin hz hP hq hfin hgrind
  refine verify_ok_of P A _ pis _ _ t ?_ hrun ?_
  · rw [prove_eq]
    exact honest_shape P A logN trace pis (hAlpha P A logN trace pis) (hZeta P A logN trace pis)
  · rw [prove_eq]
    exact checkConstraints_honest P A logN trace pis (hAlpha P A logN trace pis)
      (hZeta P A logN trace pis) hin hsat hdeg hz

end CompStark.Stark
