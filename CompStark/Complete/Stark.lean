/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Pcs
public import CompStark.Complete.Quotient

/-! # The specification prover's proofs verify

The STARK layer of completeness: the verifier replays the prover's transcript. It observes the
same domain separator, commitments and public values, checks the same grinding witness, so it
samples the same `α` and `ζ`, and `ζ` off the base field is off the trace domain. Its rounds are
the honest rounds of the prover's openings (`openingRounds_eq`, `hDRounds_eq`), which the prover
opens honestly (`hRounds_honest`), so `verifyPcs` accepts `openPcs`'s proof
(`verifyPcs_openPcs`, `CompStark/Complete/Pcs.lean`); and the honest openings pass the constraint
check (`checkConstraints_honest`).
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

variable [Poseidon2Field F]

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

/-- The opening argument's run: the opened values, the FRI proof and the final transcript. -/
def hPcs : (List (List (List (Array EF))) × FriProof F EF) × Transcript F 24 :=
  (openPcs (specBackend EF) P (hRounds EF P A logN trace pis)).run
    (Transcript.sampleExtState EF (hOod EF P A logN trace pis).2)

theorem prove_eq : prove EF P A logN trace pis =
    { traceCommit := (Committed.ofMats hashF compF [hExt P A logN trace]).root
      quotientCommit := (Committed.ofMats hashF compF (hChunks EF P A logN trace pis)).root
      opened := honestOpened P.logBlowup A logN (hExt P A logN trace)
        (hChunks EF P A logN trace pis) (hZeta EF P A logN trace pis)
      fri := (hPcs EF P A logN trace pis).1.2
      degreeBits := logN
      oodWitness := (hOod EF P A logN trace pis).1 } := by
  unfold prove proveWith hPcs
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

/-- The prover's final transcript is the opening argument's. -/
theorem proveTranscript_eq :
    proveTranscript EF P A logN trace pis = (hPcs EF P A logN trace pis).2 := by
  unfold proveTranscript
  dsimp only
  rw [prun_bind]
  erw [commitAndSample_run]
  unfold openAndAssemble
  simp only [prun_bind]
  rfl

end Honest

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
  obtain ⟨ps, hl, -⟩ := chunk_isLde (EF := EF) P logN _ _ hin.twoAdic hin.chunks c
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

/-- The prover's rounds, with their openings, are the honest rounds of `verifyPcs_openPcs`. -/
theorem hDRounds_eq : hDRounds EF P A logN trace pis =
    honestRounds P.logBlowup (hRounds EF P A logN trace pis) := by
  unfold hDRounds hRounds hBaseDRounds hBaseRounds hPrepDRounds hPrepRounds hPrep honestRounds
  rw [List.map_append]
  congr 1
  · simp only [List.map_cons, List.map_nil, List.map_map]
    rfl
  · cases setupWith (specBackend EF) P A logN <;> rfl

/-- The prover opens honest rounds. -/
theorem hRounds_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis)) (hfin : P.logFinalPolyLen ≤ logN) :
    HonestRounds P (hRounds EF P A logN trace pis) := by
  have hzn : Ext.OutsideBase (hZetaNext EF P A logN trace pis) :=
    Ext.outsideBase_mul_ofBase hz
      (BaseField.twoAdicGen_ne_zero logN (by have := hin.twoAdic; omega))
  have hpts : ∀ zs : List EF, (zs = [hZeta EF P A logN trace pis] ∨
      zs = [hZeta EF P A logN trace pis, hZetaNext EF P A logN trace pis]) →
      zs ≠ [] ∧ ∀ z ∈ zs, Ext.OutsideBase z := by
    rintro zs (rfl | rfl)
    · exact ⟨List.cons_ne_nil _ _, fun z hz' ↦ (List.mem_singleton.mp hz') ▸ hz⟩
    · refine ⟨List.cons_ne_nil _ _, fun z hz' ↦ ?_⟩
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hz
      · exact (List.mem_singleton.mp hz') ▸ hzn
  have htp := hpts (hTracePts EF P A logN trace pis) (by
    simp only [hTracePts, tracePoints]; split <;> simp only [true_or, or_true])
  have hpp := hpts (hPrepPts EF P A logN trace pis) (by
    simp only [hPrepPts, preprocessedPoints]; split <;> simp only [true_or, or_true])
  have hhl : P.logBlowup + P.logFinalPolyLen ≤ logN + P.logBlowup := by omega
  refine ⟨List.cons_ne_nil _ _, fun r hr ↦ ?_, fun r hr x hx ↦ ?_, fun r hr x hx ↦ ?_⟩
  all_goals
    simp only [hRounds, hBaseRounds, hPrepRounds, List.cons_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
  · exact ⟨List.cons_ne_nil _ _, rfl⟩
  · refine ⟨by simpa only [ne_eq, List.map_eq_nil_iff] using hChunks_ne_nil EF P A logN trace pis,
      ?_⟩
    rw [List.map_map]
    simp only [Function.comp_def, List.map_id']
  · simp only [setupWith] at hr
    split at hr
    · exact absurd hr List.not_mem_nil
    · rw [Option.map_some, Option.toList_some, List.nil_append, List.mem_singleton] at hr
      subst hr
      exact ⟨List.cons_ne_nil _ _, rfl⟩
  · rw [List.mem_singleton.mp hx]; exact htp
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    exact hpts _ (Or.inl rfl)
  · simp only [setupWith] at hr
    split at hr
    · exact absurd hr List.not_mem_nil
    · rw [Option.map_some, Option.toList_some, List.nil_append, List.mem_singleton] at hr
      subst hr
      rw [List.mem_singleton.mp hx]
      exact hpp
  · rw [List.mem_singleton.mp hx]
    obtain ⟨ps, hl, -⟩ := trace_lde P A logN trace hin
    exact ⟨_, ps, hl, hhl⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
    obtain ⟨ps, hl, -⟩ := chunk_isLde (EF := EF) P logN _ _ hin.twoAdic hin.chunks c
    exact ⟨_, ps, hl, hhl⟩
  · simp only [setupWith] at hr
    split at hr
    · exact absurd hr List.not_mem_nil
    · rw [Option.map_some, Option.toList_some, List.nil_append, List.mem_singleton] at hr
      subst hr
      rw [List.mem_singleton.mp hx]
      obtain ⟨ps, hl, -⟩ := prep_lde P A logN trace hin
      exact ⟨_, ps, hl, hhl⟩

theorem verifyRun_honest (hin : Fits P A logN trace)
    (hz : Ext.OutsideBase (hZeta EF P A logN trace pis))
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hb : 0 < P.logBlowup)
    (hfin : P.logFinalPolyLen ≤ logN)
    (hgrind : (proveTranscript EF P A logN trace pis).grindFailed = false) :
    ∃ t, verifyRun P A (setup P A logN) (prove EF P A logN trace pis) pis
      Poseidon2.initTranscript =
      .ok ((hAlpha EF P A logN trace pis, hZeta EF P A logN trace pis), t) := by
  rw [proveTranscript_eq] at hgrind
  -- the grinding flag and the duplexes
  have hgO : (hOod EF P A logN trace pis).2.grindFailed = false := by
    have := flag_openPcs P (hRounds EF P A logN trace pis) _ hgrind
    rwa [flag_sampleExt] at this
  have hdC : (hTC EF P A logN trace pis).duplex = Poseidon2.duplex := by
    rw [Stark.hTC, duplex_observeList, duplex_sampleExt, Stark.hTA, duplex_observeList,
      duplex_observeList, duplex_observeList]
    rfl
  have hd2 : (Transcript.sampleExtState EF (hOod EF P A logN trace pis).2).duplex =
      Poseidon2.duplex := by
    rw [duplex_sampleExt, hOod, duplex_grind, hdC]
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
  have hfri : (prove EF P A logN trace pis).fri = (hPcs EF P A logN trace pis).1.2 := by rw [hp]
  -- the opening argument
  have hPcs' : verifyPcs (poseidon2 F) P (openingRounds A (setup P A logN)
      (prove EF P A logN trace pis) (hZeta EF P A logN trace pis))
      (hPcs EF P A logN trace pis).1.2
      (Transcript.sampleExtState EF (hOod EF P A logN trace pis).2) =
      .ok ((), (hPcs EF P A logN trace pis).2) := by
    rw [openingRounds_eq EF P A logN trace pis hin]
    rw [hDRounds_eq]
    exact verifyPcs_openPcs P (hRounds EF P A logN trace pis) _ hd2
      (hRounds_honest EF P A logN trace pis hin hz hfin) hP hq hb hgrind
  refine ⟨(hPcs EF P A logN trace pis).2, ?_⟩
  have hcO : checkWitness (poseidon2 F) P.oodPowBits (hOod EF P A logN trace pis).1
      (hTC EF P A logN trace pis) = .ok (true, (hOod EF P A logN trace pis).2) :=
    (checkWitness_run _ _ _ hdC).trans (congrArg Except.ok (checkWitness_grind _ _ hgO))
  rw [verifyRun_run, hTC', hTA', how, bind_ok hcO]
  rw [ensure_true, pure_bind, bind_ok (sampleExt_run _), hdb]
  have hzeta : ((hOod EF P A logN trace pis).2.sampleExtValue : EF) = hZeta EF P A logN trace pis :=
    rfl
  rw [hzeta, powTwo_ne_one hz (by have := hin.twoAdic; omega), ensure_true, pure_bind]
  rw [hfri, bind_ok hPcs']
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
