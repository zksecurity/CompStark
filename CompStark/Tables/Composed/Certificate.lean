/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Compose.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Budget
public import CompStark.Pcs.Parameters
public import CompStark.Tables.Argument
public import ArkLib.ProofSystem.Whir.Certificate

/-! The composed proof system for a set of tables: the commitment of the stack, the bus, the table
sumcheck, the external argument, and the WHIR opening of the claim pool. The first message fixes
the received word and its list of proximate stacks; every outer challenge pays the list's real
Johnson bound once, and WHIR pays its own level-local errors (`knowledgeSoundness`). The extracted
stack interprets to a witness that satisfies the system unless an extraction-path challenge was bad
(`extracted_satisfied`). -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp

/-- The parameters of a composed system: its side conditions and a certified WHIR opening of the
stack. -/
structure Parameters (S : System K) (L : Layout S.tables.length) (k M : ℕ) extends Setup S L k M where
  /-- The encoded levels and closing rounds. -/
  schedule : Whir.Schedule K M
  /-- Integer Johnson choices, one per level. -/
  johnson : Pcs.JohnsonParameters schedule
  /-- Encoding contracts and positive folding dimensions. -/
  valid : schedule.Valid (algebraMap K E) (Pcs.johnsonSecurity schedule johnson)
  /-- The initial list decoder. -/
  decoder : Whir.InitialDecoder schedule
  /-- Its coverage and real list bound. -/
  correct : Whir.InitialDecoder.Correct decoder (Pcs.johnsonSecurity schedule johnson)
  /-- The decoders of the later levels. -/
  decoders : Whir.DecoderFamily (E := E) schedule
  /-- Their coverage and list bounds. -/
  familyCorrect : Whir.DecoderFamily.Correct (algebraMap K E) schedule decoders
    (Pcs.johnsonSecurity schedule johnson)

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- The analytical security of the opening. -/
noncomputable def Parameters.security (params : Parameters S L k M) :
    Whir.SecurityParameters params.schedule :=
  Pcs.johnsonSecurity params.schedule params.johnson

/-- The list of stacks proximate to the received word, from the decoder WHIR uses. -/
def candidates : {vars : ℕ} → (schedule : Whir.Schedule K vars) → Whir.InitialDecoder schedule →
    Whir.oracleMessage K schedule → Finset (Whir.Table K vars)
  | _, .last _ _ _ _, decoder, word => (decoder.decode word).toFinset
  | _, .more _ _ _ _, decoder, word => (decoder.decode word).toFinset

/-- The list has at most the real Johnson bound of elements. -/
theorem candidates_card_le {vars : ℕ} (schedule : Whir.Schedule K vars)
    (security : Whir.SecurityParameters schedule) (decoder : Whir.InitialDecoder schedule)
    (correct : Whir.InitialDecoder.Correct decoder security) (word : Whir.oracleMessage K schedule) :
    ((candidates schedule decoder word).card : ℝ) ≤ Pcs.initialListBound schedule security := by
  cases schedule with
  | last lanes tail encoding queries =>
      have card_le : (((decoder.decode word).toFinset).card : ℝ) ≤
          ((decoder.decode word).length : ℝ) := by
        exact_mod_cast List.toFinset_card_le (decoder.decode word)
      exact card_le.trans (correct.length_le word)
  | more lanes encoding queries rest =>
      have card_le : (((decoder.decode word).toFinset).card : ℝ) ≤
          ((decoder.decode word).length : ℝ) := by
        exact_mod_cast List.toFinset_card_le (decoder.decode word)
      exact card_le.trans (correct.length_le word)

/-- WHIR's input relation is membership in the list and the claims. -/
theorem candidates_mem_iff {vars : ℕ} (schedule : Whir.Schedule K vars)
    (security : Whir.SecurityParameters schedule) (decoder : Whir.InitialDecoder schedule)
    (correct : Whir.InitialDecoder.Correct decoder security) (word : Whir.oracleMessage K schedule)
    (claims : List (Whir.Claim E vars)) (q : Whir.Table K vars) :
    (Whir.openingState (algebraMap K E) schedule security word claims).holds q ↔
      q ∈ candidates schedule decoder word ∧
        ∀ claim ∈ claims, claim.Holds (fun u => ofK (q u)) := by
  cases schedule with
  | last lanes tail encoding queries =>
      exact and_congr ((correct.mem_iff word q).symm.trans List.mem_toFinset.symm) Iff.rfl
  | more lanes encoding queries rest =>
      exact and_congr ((correct.mem_iff word q).symm.trans List.mem_toFinset.symm) Iff.rfl

/-- The outer protocol starts with the bus's draw. -/
theorem outer_ne_done (setup : Setup S L k M) : (outerProtocol setup).tree ≠ .done := by
  intro equal
  cases equal

/-- WHIR starts with its batching draw. -/
theorem opening_ne_done {vars : ℕ} (schedule : Whir.Schedule K vars) :
    (Whir.opening E schedule).tree ≠ .done := by
  cases schedule <;> intro equal <;> cases equal

variable (params : Parameters S L k M)

/-- The union of the outer reductions' certificates over the list, each keeping its candidate. -/
noncomputable def taggedOuter (word : Whir.oracleMessage K params.schedule) :=
  ListLift.certificate (candidates params.schedule params.decoder word)
    (Pcs.initialListBound params.schedule params.security)
    (candidates_card_le params.schedule params.security params.decoder params.correct word)
    (outerReduction params.toSetup).certificate (outerReduction params.toSetup).challenges
    (outerReduction params.toSetup).schedule_eq

/-- After the commitment: a member of the list satisfies the outer reductions' input. -/
def committedState (word : Whir.oracleMessage K params.schedule) : KnowledgeState :=
  ⟨Whir.Table K M, fun q => q ∈ candidates params.schedule params.decoder word ∧
    (outerReduction params.toSetup).input q⟩

/-- The outer certificate over the list, with the redundant root tag erased. -/
noncomputable def outerCertificate (word : Whir.oracleMessage K params.schedule) :
    KnowledgeCertificate (outerProtocol params.toSetup).tree
      (outerProtocol params.toSetup).roles (committedState params word) :=
  ListLift.rebase (taggedOuter params word) (outer_ne_done params.toSetup)
    (committedState params word) (fun witness => witness.2) (by
      rintro ⟨fixed, witness⟩ ⟨member, bound, good⟩
      exact ⟨bound ▸ member, good⟩)

/-- The outer endpoint's witness: the candidate and the same stack. -/
noncomputable def outerTerminalEquiv (word : Whir.oracleMessage K params.schedule)
    (path : (outerProtocol params.toSetup).tree.ExecutionPath) :
    ((outerCertificate params word).extractor.terminalState path).Witness ≃
      (Whir.Table K M × Whir.Table K M) :=
  (ListLift.rebaseTerminalEquiv (target := committedState params word)
    (outer_ne_done params.toSetup) (taggedOuter params word).extractor
    (fun witness => witness.2) path).trans
    ((ListLift.terminalEquiv (candidates params.schedule params.decoder word)
      (fun fixed => ((outerReduction params.toSetup).certificate fixed).extractor) path).trans
      (Equiv.sigmaEquivProdOfEquiv fun fixed =>
        ((outerReduction params.toSetup).terminal fixed).witnessEquiv path))

/-- The outer endpoint names a member of the list and that stack satisfies the outer relation. -/
theorem outer_terminal_iff (word : Whir.oracleMessage K params.schedule)
    (path : (outerProtocol params.toSetup).tree.ExecutionPath)
    (witness : ((outerCertificate params word).extractor.terminalState path).Witness) :
    ((outerCertificate params word).extractor.terminalState path).holds witness ↔
      (outerTerminalEquiv params word path witness).1 ∈ candidates params.schedule params.decoder word ∧
      (outerTerminalEquiv params word path witness).2 = (outerTerminalEquiv params word path witness).1 ∧
      (outerReduction params.toSetup).relation ((outerReduction params.toSetup).output path)
        (outerTerminalEquiv params word path witness).2 := by
  exact (ListLift.rebase_terminal_holds (target := committedState params word)
    (outer_ne_done params.toSetup) (taggedOuter params word).extractor (fun witness => witness.2) path
    witness).trans
      ((ListLift.terminal_holds (candidates params.schedule params.decoder word)
        (fun fixed => ((outerReduction params.toSetup).certificate fixed).extractor) path _).trans
          (and_congr_right fun _ =>
            ((outerReduction params.toSetup).terminal _).knowledge_iff path _))

/-- Outer extraction keeps the stack named at the endpoint. -/
theorem outer_extractWitness (word : Whir.oracleMessage K params.schedule)
    (path : (outerProtocol params.toSetup).tree.ExecutionPath)
    (witness : ((outerCertificate params word).extractor.terminalState path).Witness) :
    (outerCertificate params word).extractor.extractWitness path witness =
      (outerTerminalEquiv params word path witness).2 := by
  let tagged := ListLift.rebaseTerminalEquiv (target := committedState params word)
    (outer_ne_done params.toSetup) (taggedOuter params word).extractor
    (fun witness => witness.2) path witness
  have erase := ListLift.rebase_extractWitness (target := committedState params word)
    (outer_ne_done params.toSetup) (taggedOuter params word).extractor
    (fun witness => witness.2) path witness
  have union := ListLift.extractWitness_eq (candidates params.schedule params.decoder word)
    (fun fixed => ((outerReduction params.toSetup).certificate fixed).extractor) path tagged
  exact erase.trans ((congrArg (fun witness => witness.2) union).trans
    ((outerReduction params.toSetup).extract_eq _ path _))

/-- WHIR's certificate on the claim pool, framed by the outer public checks. -/
noncomputable def framedWhir (word : Whir.oracleMessage K params.schedule)
    (out : (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M) :
    KnowledgeCertificate (Whir.opening E params.schedule).tree (Whir.opening E params.schedule).roles
      (ListLift.frameState (publicAccepted out)
        (Whir.openingState (algebraMap K E) params.schedule params.security word (openingClaims out))) :=
  ListLift.frame
    (Whir.certificate (algebraMap K E) params.schedule params.security
      params.decoders params.familyCorrect params.valid word
      (openingClaims out) params.decoder params.correct)
    (publicAccepted out)

/-- WHIR's extracted stack lifts to the outer endpoint as its own candidate. -/
noncomputable def openingCertificate (word : Whir.oracleMessage K params.schedule)
    (path : (outerProtocol params.toSetup).tree.ExecutionPath) :
    KnowledgeCertificate (Whir.opening E params.schedule).tree (Whir.opening E params.schedule).roles
      ((outerCertificate params word).extractor.terminalState path) :=
  ListLift.rebase
    (framedWhir params word ((outerReduction params.toSetup).output path))
    (opening_ne_done params.schedule) ((outerCertificate params word).extractor.terminalState path)
    (fun q => (outerTerminalEquiv params word path).symm (q, q)) (by
      intro q known
      apply (outer_terminal_iff params word path _).mpr
      rw [Equiv.apply_symm_apply]
      exact ⟨((candidates_mem_iff params.schedule params.security params.decoder params.correct word
        _ q).mp known.2).1, rfl,
        (outer_endpoint_iff params.toSetup _ q).mpr
          ⟨known.1, ((candidates_mem_iff params.schedule params.security params.decoder params.correct word
            _ q).mp known.2).2⟩⟩)

/-- The outer certificate over the list with WHIR appended at its endpoint. -/
noncomputable def committedCertificate (word : Whir.oracleMessage K params.schedule) :
    KnowledgeCertificate
      (appendProtocol (outerProtocol params.toSetup) (Whir.opening E params.schedule)).tree
      (appendProtocol (outerProtocol params.toSetup) (Whir.opening E params.schedule)).roles
      (committedState params word) :=
  (outerCertificate params word).append (fun _ => (Whir.opening E params.schedule).tree)
    (fun _ => (Whir.opening E params.schedule).roles) (openingCertificate params word)

/-- The composed protocol: the stack's commitment, the outer reductions, the opening. -/
def protocol : Protocol :=
  .oracle (Whir.oracleMessage K params.schedule)
    (appendProtocol (outerProtocol params.toSetup) (Whir.opening E params.schedule))

/-- Before the commitment: a stack satisfying the outer reductions' input. -/
def inputState : KnowledgeState :=
  ⟨Whir.Table K M, (outerReduction params.toSetup).input⟩

/-- The composed knowledge certificate. -/
noncomputable def certificate :
    KnowledgeCertificate (protocol params).tree (protocol params).roles (inputState params) where
  extractor word := ⟨committedState params word, id, (committedCertificate params word).extractor⟩
  challenges word := (committedCertificate params word).challenges
  prover_preserving :=
    ⟨fun _ _ good => good.2, fun word => (committedCertificate params word).prover_preserving⟩
  local_bound := fun word => (committedCertificate params word).local_bound

/-- The composed schedule. -/
noncomputable def challenges :
    RoundExtractor.ChallengeSchedule (protocol params).tree (protocol params).roles :=
  (certificate params).challenges

/-- The outer endpoint and the opening of a transcript. -/
def executionParts (path : (protocol params).tree.ExecutionPath) :=
  splitPath (outerProtocol params.toSetup) (Whir.opening E params.schedule) path.2

/-- The specification verifier: the outer public checks and WHIR's acceptance of the claim pool. -/
def Accepts (path : (protocol params).tree.ExecutionPath) : Prop :=
  let parts := executionParts params path
  let out := (outerReduction params.toSetup).output parts.1
  publicAccepted out ∧
    Whir.accepts (algebraMap K E) params.schedule (Whir.mapMasked ofK path.1)
      (openingClaims out) parts.2 = true

/-- A bound on the number of pool claims. -/
def poolBound : ℕ :=
  (S.boundaryColumns L).length +
    ∑ t : Fin S.tables.length, (TableSumcheck.transmitted S t).length

/-- The pool has at most `poolBound` claims. -/
theorem pool_length_le (o : TableSumcheck.Output S L k) :
    (pool S L k M o).length ≤ poolBound (S := S) (L := L) := by
  unfold pool poolBound
  rw [List.length_append]
  apply Nat.add_le_add
  · unfold boundaryClaims
    exact (List.length_filterMap_le _ _).trans (by simp only [List.length_finRange, le_refl])
  · unfold valueClaims
    rw [List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
    apply Finset.sum_le_sum
    intro t _
    dsimp only [Function.comp_apply]
    split
    · exact (List.length_filterMap_le _ _).trans (by simp only [List.length_finRange, le_refl])
    · simp only [List.length_nil, Nat.zero_le]

/-- The opening's claims are at most the pool's bound plus the external argument's. -/
def claimBound : ℕ := poolBound (S := S) (L := L) + params.external.claimBound

/-- The composed error: the outer error over the initial list, and WHIR's level errors at the
claim bound. -/
noncomputable def totalError : ENNReal :=
  ENNReal.ofReal (Pcs.initialListBound params.schedule params.security) * outerError params.toSetup +
    whirBudget params.schedule params.security (claimBound params)

/-- The external phase's output has at most the argument's claims. -/
theorem external_claims_le (setup : Setup S L k M) (table : Option (TableSumcheck.Output S L k))
    (path : setup.external.protocol.tree.ExecutionPath) :
    ((externalReduction setup table).output path).claims.length ≤ setup.external.claimBound := by
  cases table with
  | none => exact Nat.zero_le _
  | some o => exact setup.external.claims_le o path

/-- Every outer endpoint owes at most `claimBound` claims. -/
theorem openingClaims_length_le (path : (outerProtocol params.toSetup).tree.ExecutionPath) :
    (openingClaims ((outerReduction params.toSetup).output path)).length ≤ claimBound params := by
  let parts := splitPath (appendProtocol (Bus.protocol S L k) (TableSumcheck.protocol S L))
    params.external.protocol path
  have hout : (outerReduction params.toSetup).output path =
      (((busReduction params.toSetup).then (tableReduction params.toSetup) _).output parts.1,
        (externalReduction params.toSetup
          (((busReduction params.toSetup).then (tableReduction params.toSetup) _).output parts.1).2).output
            parts.2) := rfl
  rw [hout]
  generalize ((busReduction params.toSetup).then (tableReduction params.toSetup) _).output parts.1 = first
  rcases first with ⟨bus, table⟩
  cases table with
  | none => exact Nat.zero_le _
  | some o =>
    change (pool S L k M o ++ _).length ≤ _
    rw [List.length_append]
    exact Nat.add_le_add (pool_length_le o) (external_claims_le params.toSetup (some o) parts.2)

/-- The composed schedule meets the composed error. -/
theorem challenges_budget :
    Retained.Budget (protocol params).roles (challenges params) (totalError params) := by
  intro word
  exact budget_append (outerProtocol params.toSetup).roles
    (fun _ => (Whir.opening E params.schedule).tree)
    (fun _ => (Whir.opening E params.schedule).roles)
    (ListLift.scale (outerProtocol params.toSetup).roles
      (Pcs.initialListBound params.schedule params.security) (outerReduction params.toSetup).challenges)
    (fun path => Whir.challenges params.schedule params.security
      (openingClaims ((outerReduction params.toSetup).output path)).length)
    _ _ (budget_scale _ _ _ _ (outer_budget params.toSetup))
    (fun path => budget_mono _ _ (whir_budget params.schedule params.security _)
      (whirBudget_mono params.schedule params.security (openingClaims_length_le params path)))

/-- Knowledge soundness: against every prover, extraction fails with probability at most the
composed error. -/
theorem knowledgeSoundness (prover : Retained.Strategy (protocol params).tree (protocol params).roles) :
    Pr{let path ← Retained.play (protocol params).roles (certificate params).challenges prover}[
      Retained.Failure (certificate params).extractor path] ≤ totalError params :=
  Retained.failure_le (certificate params).extractor (protocol params).roles
    (certificate params).challenges (certificate params).prover_preserving
    (certificate params).local_bound _ (challenges_budget params) prover

/-- An accepted transcript has terminal knowledge. -/
theorem accepts_terminal (path : (protocol params).tree.ExecutionPath) (accepted : Accepts params path) :
    ∃ witness, ((certificate params).extractor.terminalState path).holds witness := by
  change ∃ witness, ((committedCertificate params path.1).extractor.terminalState path.2).holds witness
  apply (ListLift.exists_append_terminal_iff (outerCertificate params path.1).extractor
    (fun _ => (Whir.opening E params.schedule).tree)
    (fun outer => (openingCertificate params path.1 outer).extractor) path.2).mpr
  change ∃ witness, ((openingCertificate params path.1 (executionParts params path).1).extractor.terminalState
    (executionParts params path).2).holds witness
  apply (ListLift.exists_rebase_terminal_iff (opening_ne_done params.schedule)
    (framedWhir params path.1 ((outerReduction params.toSetup).output (executionParts params path).1)).extractor
    (fun q => (outerTerminalEquiv params path.1 (executionParts params path).1).symm (q, q))
    (executionParts params path).2).mpr
  apply (ListLift.exists_frame_terminal_iff _ _ (executionParts params path).2).mpr
  exact ⟨accepted.1, Whir.accepts_terminal (algebraMap K E) params.schedule params.security
      params.decoders params.familyCorrect params.valid
    path.1 _ params.decoder params.correct (executionParts params path).2 accepted.2⟩

/-- The composed input relation on a stack: its interpreted witness satisfies the system. -/
theorem inputState_satisfied (q : Whir.Table K M) (known : (inputState params).holds q) :
    S.Satisfied L (params.external.interpret q) := by
  obtain ⟨input, rider⟩ := (outer_input_iff params.toSetup q).mp known
  exact (Argument.input_satisfied S L _).mp ⟨input, params.external.external_of_rider q rider⟩

/-- At terminal knowledge with no bad challenge on its extraction path, the extracted stack
interprets to a witness that satisfies the system. -/
theorem extracted_satisfied (path : (protocol params).tree.ExecutionPath)
    (witness : ((certificate params).extractor.terminalState path).Witness)
    (terminal : ((certificate params).extractor.terminalState path).holds witness)
    (good : ¬ (certificate params).extractor.BadChallengeOnPath (protocol params).roles path witness) :
    S.Satisfied L (params.external.interpret ((certificate params).extractor.extractWitness path witness)) := by
  apply inputState_satisfied params
  by_contra unknown
  exact good ((certificate params).extractor.extraction_failure_implies_bad_challenge
    (protocol params).roles (certificate params).prover_preserving path witness terminal unknown)

end CompStark.Tables.Composed
