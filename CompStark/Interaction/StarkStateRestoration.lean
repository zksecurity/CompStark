/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.StarkKnowledge
public import ArkLib.ProofSystem.Fri.Interaction.StateRestoration

/-! # State-restoration knowledge soundness of the STARK

The STARK on ArkLib's interaction layer is public-coin (`Statement.publicCoin`): the trace length
is the prover's first public move, every challenge (`α`, `ζ`, `a`, FRI's folding challenges and
query positions) has one continuation for all its values, and FRI's presentation
(`Fri.Interaction.publicCoin`) is appended after `a`. The STARK's knowledge certificate samples
every challenge uniformly (`Setup.uniformChallenges_certificate`), and so does the statement's
(`Statement.certificate`), which conditions on the length the prover sends.

The verifier's checks are a program of the branch (`Statement.terminal`): the constraints at `ζ`,
then FRI's checks on the DEEP word. In the state-restoration game, where an adversary making at
most `Q` random-oracle queries chooses the public values and every prover message, the checks pass
while no trace of the claimed length close to the committed one satisfies the AIR with probability
at most `Q * maxError + sumError` of the node errors (`Statement.stateRestoration_le`): at each
length, the folding, out-of-domain and batching errors, each FRI fold's lossy MCA error and FRI's
query error at the length's proximity loss (`Setup.nodeErrors`). The path sum at a length is the
interactive knowledge error at that proximity loss (`Setup.pathError_nodeErrors`,
`Statement.lengthBound`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound CompStark.Interaction _root_.Interaction
open _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp OracleSpec
open _root_.Interaction.Oracle.Security.StateRestoration _root_.Interaction.Oracle.TypeTree
open scoped NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Claimed values exist: all zero. -/
instance {lookups : List (Lookup F)} (S : Iop.Setup EF lookups) : Nonempty (Openings S) :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

namespace Setup
variable (S : Setup EF)

/-- The STARK at a length is public-coin: the trace, `α`, the quotient, `ζ`, the claimed values,
`a`, and FRI's public-coin presentation. -/
noncomputable def publicCoin : PublicCoin S.protocol :=
  open Classical in
  .oracle (.challenge (.oracle (.challenge (.sender fun _ => .challenge
    (Fri.Interaction.publicCoin 𝕂 (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      S.params.numQueries (S.friSchedule []))))))

variable (publicValues : List F) (δ δ' : ℝ≥0)

/-- The STARK's certificate samples every challenge uniformly. -/
theorem uniformChallenges_certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    UniformChallenges S.publicCoin (S.certificate publicValues δ δ' hδ' loss).challenges :=
  fun T => ⟨rfl, fun α Q => ⟨rfl, fun ζ o => ⟨rfl, fun a =>
    Fri.Interaction.uniformChallenges_certificate (S.logN + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries
      (S.deepInputs (S.deepOf T α Q ζ o a)) δ loss (Nat.two_pow_pos _) loss.coe_nonneg le_rfl
      S.friDomain (S.friSchedule []) 0 (S.deepOf T α Q ζ o a) Finset.univ⟩⟩⟩

/-- The verifier's checks on a branch: the constraints at `ζ`, and FRI's checks on the DEEP word
read through the trace and the quotient. -/
noncomputable def terminal (p : S.protocol.tree.BranchPath) :
    OracleComp (OracleSpec.ofPFunctor (accessAfter S.protocol.tree S.protocol.oracles noAccess p))
      Bool :=
  open Classical in
  (fun b ↦ decide (ConstraintsHoldAt S publicValues p.2.1 p.2.2.2.1 p.2.2.2.2.1) && b) <$>
    Fri.Interaction.terminal (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      S.params.numQueries S.friDomain S.quotientAccess
      (S.deepReader p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) (S.friSchedule [])
      p.2.2.2.2.2.2

set_option backward.isDefEq.respectTransparency false in
/-- When the checks pass on a complete execution, closed with its trace and quotient, the
certificate's terminal state holds. -/
theorem terminal_holds_of_eval (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    (path : S.protocol.tree.ExecutionPath)
    (h : evalWithAnswerFn (path.closingImpl S.protocol.oracles noAccess noImpl)
      (S.terminal publicValues path.toBranchPath) = true) :
    ∃ w, ((S.certificate publicValues δ δ' hδ' loss).extractor.terminalState path).holds w := by
  obtain ⟨T, α, Q, ζ, o, a, p⟩ := path
  have h' : (@decide _ (Classical.propDecidable (ConstraintsHoldAt S publicValues α ζ o)) &&
      evalWithAnswerFn (ExecutionPath.closingImpl (tree := (S.friProtocol []).tree) p
        (S.friProtocol []).oracles S.quotientAccess (S.messagesImpl T Q))
        (Fri.Interaction.terminal (S.logN + S.params.logBlowup)
        (2 ^ S.params.logFinalPolyLen) S.params.numQueries S.friDomain S.quotientAccess
        (S.deepReader α ζ o a) (S.friSchedule [])
        (ExecutionPath.toBranchPath (tree := (S.friProtocol []).tree) p))) = true := by
    unfold evalWithAnswerFn at h ⊢
    rw [terminal, simulateQ_map] at h
    exact h
  rw [Bool.and_eq_true] at h'
  obtain ⟨w, hw⟩ := Fri.Interaction.terminal_holds_of_eval (S.logN + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.deepInputs (S.deepOf T α Q ζ o a)) δ
    loss (Nat.two_pow_pos _) loss.coe_nonneg (S.friSchedule []) le_rfl S.friDomain _ _ _ 0
    (S.deepOf T α Q ζ o a) Finset.univ (S.reads_deepReader T Q α ζ o a)
    (fun x ↦ by simp only [Finset.mem_univ, decide_true]; rfl) p h'.2
  rw [terminalState_certificate]
  simp only [friCertificate, gateCertificate]
  rw [terminalState_gateExtractor]
  exact ⟨w, @of_decide_eq_true _ (Classical.propDecidable _) h'.1, hw⟩

/-- FRI's erased prefixes in the STARK. -/
abbrev FriPrefix : Type :=
  Prefix PUnit (Fri.Interaction.publicCoin 𝕂 (S.logN + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.friSchedule []))

/-- The node errors of the STARK at a length, at proximity `δ`, extraction radius `δ'` and
proximity loss `loss`: the folding error at `α`, the out-of-domain error at `ζ`, the batching
error at `a`, and FRI's node errors on the DEEP word. -/
noncomputable def nodeErrors (loss : ℝ≥0) : Errors S.publicCoin := fun node ↦
  match (node : S.TraceMessage × (PUnit ⊕ (PUnit × (S.QuotientMessage × (PUnit ⊕
      (PUnit × ((_ : Openings S) × (PUnit ⊕ (PUnit × S.FriPrefix))))))))) with
  | ⟨_, .inl _⟩ => foldingError S δ'
  | ⟨_, .inr ⟨_, _, .inl _⟩⟩ => outOfDomainError S δ'
  | ⟨_, .inr ⟨_, _, .inr ⟨_, _, .inl _⟩⟩⟩ => batchingError S δ δ'
  | ⟨_, .inr ⟨_, _, .inr ⟨_, _, .inr ⟨_, node⟩⟩⟩⟩ =>
      Fri.Interaction.nodeErrors (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries δ loss S.friDomain (S.friSchedule []) 0 node

/-- The certificate's error at each node is the node error. -/
theorem supErrors_certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    supErrors S.publicCoin (S.certificate publicValues δ δ' hδ' loss).challenges =
      S.nodeErrors δ δ' loss := by
  funext node
  obtain ⟨T, _ | ⟨_, Q, _ | ⟨_, o, _ | ⟨_, node⟩⟩⟩⟩ :=
    (node : S.TraceMessage × (PUnit ⊕ (PUnit × (S.QuotientMessage × (PUnit ⊕
      (PUnit × ((_ : Openings S) × (PUnit ⊕ (PUnit × S.FriPrefix)))))))))
  · rfl
  · exact iSup_const
  · exact (iSup_congr fun _ => iSup_const).trans iSup_const
  · refine (iSup_congr fun α => (iSup_congr fun ζ => (iSup_congr fun a => ?_).trans
      iSup_const).trans iSup_const).trans iSup_const
    exact Fri.Interaction.supErrors_certificate (S.logN + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.deepInputs (S.deepOf T α Q ζ o a)) δ
      loss (Nat.two_pow_pos _) loss.coe_nonneg le_rfl S.friDomain (S.friSchedule []) 0
      (S.deepOf T α Q ζ o a) Finset.univ node

/-- The path sum of the node errors is the STARK's error at the proximity loss. -/
theorem pathError_nodeErrors (loss : ℝ≥0) :
    pathError S.publicCoin (S.nodeErrors δ δ' loss) =
      foldingError S δ' + outOfDomainError S δ' + batchingError S δ δ' + S.friBound [] δ loss := by
  change (⨆ _ : S.TraceMessage, foldingError S δ' + ⨆ _ : S.QuotientMessage,
    outOfDomainError S δ' + ⨆ _ : Openings S, batchingError S δ δ' +
      pathError (Fri.Interaction.publicCoin 𝕂 (S.logN + S.params.logBlowup)
        (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.friSchedule []))
        (Fri.Interaction.nodeErrors (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
          S.params.numQueries δ loss S.friDomain (S.friSchedule []) 0)) = _
  rw [Fri.Interaction.pathError_nodeErrors, iSup_const, iSup_const, iSup_const]
  simp only [friBound, Fri.Interaction.threshold, zero_add, add_assoc]

end Setup

namespace Statement
variable (C : Statement F) (EF : Type) [Challenge F EF]

/-- The STARK for a statement is public-coin: the length the prover sends, then the STARK at that
length. -/
noncomputable def publicCoin : PublicCoin (C.protocol EF) :=
  .sender fun n ↦ (C.setup EF n).publicCoin

variable (publicValues : List F) (δ δ' : ℕ → ℝ≥0)

/-- The input state: an admitted length, and a trace message and a trace there, the trace close to
the message and satisfying the AIR at that length. -/
def rootState : KnowledgeState where
  Witness := (n : C.Length) × ((C.setup EF n).rootState publicValues (δ' n.1)).Witness
  holds w := ((C.setup EF w.1).rootState publicValues (δ' w.1.1)).holds w.2

variable {C}

/-- **The statement's knowledge certificate**: whatever length the prover sends, the STARK's
certificate at that length, at its proximity loss `loss n`. -/
noncomputable def certificate (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) :
    KnowledgeCertificate (C.protocol EF).tree (C.protocol EF).roles
      (C.rootState EF publicValues δ') where
  extractor n := ⟨_, fun w ↦ ⟨n, w⟩, ((C.setup EF n).certificate publicValues (δ n.1) (δ' n.1)
    (by rw [rate_setup]; exact hδ' n.1 n.2) (loss n)).extractor⟩
  challenges := ⟨PUnit.unit, fun n ↦ ((C.setup EF n).certificate publicValues (δ n.1) (δ' n.1)
    (by rw [rate_setup]; exact hδ' n.1 n.2) (loss n)).challenges⟩
  prover_preserving := ⟨fun _ _ _ h ↦ h, fun n ↦ ((C.setup EF n).certificate publicValues
    (δ n.1) (δ' n.1) (by rw [rate_setup]; exact hδ' n.1 n.2) (loss n)).prover_preserving⟩
  local_bound n := ((C.setup EF n).certificate publicValues (δ n.1) (δ' n.1)
    (by rw [rate_setup]; exact hδ' n.1 n.2) (loss n)).local_bound

/-- The statement's certificate samples every challenge uniformly. -/
theorem uniformChallenges_certificate (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) :
    UniformChallenges (C.publicCoin EF) (certificate EF publicValues δ δ' hδ' loss).challenges :=
  fun n ↦ (C.setup EF n).uniformChallenges_certificate publicValues (δ n.1) (δ' n.1) _ (loss n)

variable (C)

/-- The verifier's checks on a branch: the STARK's checks at the length it sends. -/
noncomputable def terminal (p : (C.protocol EF).tree.BranchPath) :
    OracleComp (OracleSpec.ofPFunctor (accessAfter (C.protocol EF).tree (C.protocol EF).oracles
      noAccess p)) Bool :=
  (C.setup EF p.1).terminal publicValues p.2

/-- The node errors of the STARK for a statement: at each length, the STARK's node errors there,
at that length's proximity loss. -/
noncomputable def nodeErrors (loss : C.Length → ℝ≥0) : Errors (C.publicCoin EF) := fun node ↦
  (C.setup EF node.1).nodeErrors (δ node.1.1) (δ' node.1.1) (loss node.1) node.2

/-- The path sum of the node errors is the largest over the lengths of the STARK's error there,
at that length's proximity loss. -/
theorem pathError_nodeErrors (loss : C.Length → ℝ≥0) :
    pathError (C.publicCoin EF) (C.nodeErrors EF δ δ' loss) =
      ⨆ n, C.lengthBound EF δ δ' n (loss n) :=
  iSup_congr fun n ↦ (C.setup EF n).pathError_nodeErrors (δ n.1) (δ' n.1) (loss n)

/-- **State-restoration knowledge soundness of the STARK.** In the state-restoration game of the
STARK's public-coin presentation, where an adversary making at most `Q` random-oracle queries
chooses the public values and every prover message, the verifier's checks pass while no trace of
the claimed length close to the committed one satisfies the AIR with probability at most
`Q * maxError + sumError` of the node errors: at each length, the folding, out-of-domain and
batching errors, FRI's fold and query errors at the length's proximity loss `loss n`. The path sum
is the largest over the lengths of the interactive error at that loss (`pathError_nodeErrors`). -/
theorem stateRestoration_le (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) {Salt W : Type} [DecidableEq Salt]
    (adversary : OracleComp (oracleSpec (List F) Salt fun _ ↦ C.publicCoin EF)
      (Selection (List F) Salt W fun _ ↦ C.publicCoin EF))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (verificationGame (fun _ ↦ C.publicCoin EF) noAccess
        (fun _ ↦ noImpl) (fun _ _ ↦ Bool) (C.terminal EF) adversary)).run' ∅}[
      result.2.2.1 = true ∧ C.Far EF result.1 δ' result.2.1] ≤
      Q * maxError (fun _ : List F ↦ C.nodeErrors EF δ δ' loss) +
        sumError (fun _ : List F ↦ C.nodeErrors EF δ δ' loss) := by
  have h := KnowledgeCertificate.stateRestoration_extraction_le (fun _ ↦ C.publicCoin EF)
    (fun publicValues ↦ C.rootState EF publicValues δ')
    (fun publicValues ↦ certificate EF publicValues δ δ' hδ' loss)
    (fun publicValues ↦ uniformChallenges_certificate EF publicValues δ δ' hδ' loss) noAccess
    (fun _ ↦ noImpl) (fun _ _ ↦ Bool) (C.terminal EF) adversary Q queryBound
  have herr : (fun publicValues : List F ↦ supErrors (C.publicCoin EF)
      (certificate EF publicValues δ δ' hδ' loss).challenges) =
      fun _ ↦ C.nodeErrors EF δ δ' loss :=
    funext fun publicValues ↦ funext fun node ↦ congrFun ((C.setup EF node.1).supErrors_certificate
      publicValues (δ node.1.1) (δ' node.1.1) _ (loss node.1)) node.2
  rw [herr, verificationGame_eq, simulateQ_map] at h
  rw [verificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map] at h ⊢
  refine (prEvent_mono _ _ _ fun result hres ↦ ?_).trans h
  obtain ⟨hacc, hfar⟩ := hres
  obtain ⟨w, hw⟩ := (C.setup EF result.2.1.1).terminal_holds_of_eval result.1
    (δ result.2.1.1.1) (δ' result.2.1.1.1) _ (loss result.2.1.1) result.2.1.2 hacc
  exact ⟨w, hw, fun hroot ↦ hfar _ hroot.1 hroot.2⟩

end Statement

end CompStark.Iop
