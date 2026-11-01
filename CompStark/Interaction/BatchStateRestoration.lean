/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.BatchKnowledge
public import CompStark.Interaction.StarkStateRestoration

/-! # State-restoration knowledge soundness of the batch STARK

The batch STARK on ArkLib's interaction layer is public-coin (`Statement.publicCoin`): the vector
of trace lengths is the prover's first public move, every challenge has one continuation for all
its values, and FRI's presentation is appended after `a`. The batch's knowledge certificate
draws the query positions from a law `L` and every other challenge uniformly; with uniform
positions it samples every challenge uniformly (`Setup.uniformChallenges_certificate`), and so
does the statement's (`Statement.certificate`), which conditions on the lengths the prover
sends.

The verifier's checks are a program of the branch (`Statement.terminal`): the lookup terminals and
every instance's constraints at `ζ`, then FRI's checks on the batched DEEP words. In the
state-restoration game, where an adversary making at most `Q` random-oracle queries chooses the
public values and every prover message, the checks pass while no tuple of traces of the claimed
lengths close to the committed ones satisfies the batch with probability at most
`Q * maxError + sumError` of the node errors (`Statement.stateRestoration_le`): at each vector of
lengths, the lookup error, the largest over the instances of the folding, out-of-domain and
batching errors, and FRI's fold and query errors at the lengths' proximity loss
(`Setup.nodeErrors`, path sum `Setup.pathError_nodeErrors`). A node's error is the largest over
the instances because the instance a doomed transcript fails on is chosen after the lookup
challenges, which state restoration lets the adversary resample.
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound CompStark.Interaction _root_.Interaction
open _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp OracleSpec
open _root_.Interaction.Oracle.Security.StateRestoration _root_.Interaction.Oracle.TypeTree
open scoped NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Setup
variable {withLookups : Bool} (S : Setup EF withLookups)

/-- The batch at its lengths is public-coin: the traces, the lookup challenges, the permutation
traces and terminals, `α`, the quotients, `ζ`, the claimed values, `a`, and FRI's public-coin
presentation. -/
noncomputable def publicCoin : PublicCoin S.protocol :=
  open Classical in
  .oracle (.challenge (.oracle (.sender fun _ ↦ .challenge (.oracle (.challenge (.sender fun _ ↦
    .challenge (Fri.Interaction.publicCoin 𝕂 (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries
      (S.domainSetup.friSchedule S.friHeights))))))))

variable (publicValues : Fin S.k → List F) (δ δ' : ℝ≥0)

/-- The batch's certificate with uniform query positions samples every challenge uniformly. -/
theorem uniformChallenges_certificate (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    UniformChallenges S.publicCoin
      (S.certificate publicValues δ δ' hδ' loss S.domainSetup.uniformPositions).challenges :=
  fun T ↦ ⟨rfl, fun l P τ ↦ ⟨rfl, fun α Q ↦ ⟨rfl, fun ζ o ↦ ⟨rfl, fun a ↦
    Fri.Interaction.uniformChallenges_certificate (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries
      (S.deepWords T l.1 l.2 P τ α Q ζ o a) δ loss (Nat.two_pow_pos _) loss.coe_nonneg le_rfl
      S.domainSetup.friDomain (S.domainSetup.friSchedule S.friHeights) 0
      (S.deepWords T l.1 l.2 P τ α Q ζ o a _) Finset.univ⟩⟩⟩⟩

/-- The verifier's checks on a branch: the lookup terminals and the constraints at `ζ`, and FRI's
checks on the batched DEEP words read through the traces and the quotients. -/
noncomputable def terminal (p : S.protocol.tree.BranchPath) :
    OracleComp (OracleSpec.ofPFunctor (accessAfter S.protocol.tree S.protocol.oracles noAccess p))
      Bool :=
  open Classical in
  (fun b ↦ decide (S.Checks publicValues p.2.1.1 p.2.1.2 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2.1
      p.2.2.2.2.2.2.2.1) && b) <$>
    Fri.Interaction.terminal (S.logN S.top + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      S.params.numQueries S.domainSetup.friDomain S.quotientAccess
      (S.deepReader p.2.1.1 p.2.1.2 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
        p.2.2.2.2.2.2.2.2.1) (S.domainSetup.friSchedule S.friHeights) p.2.2.2.2.2.2.2.2.2

set_option backward.isDefEq.respectTransparency false in
/-- When the checks pass on a complete execution, closed with its traces, permutation traces and
quotients, the certificate's terminal state holds. -/
theorem terminal_holds_of_eval (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    (L : S.domainSetup.QueryPositions) (path : S.protocol.tree.ExecutionPath)
    (h : evalWithAnswerFn (path.closingImpl S.protocol.oracles noAccess noImpl)
      (S.terminal publicValues path.toBranchPath) = true) :
    ∃ w, ((S.certificate publicValues δ δ' hδ' loss L).extractor.terminalState path).holds w := by
  obtain ⟨T, l, P, τ, α, Q, ζ, o, a, p⟩ := path
  have h' : (@decide _ (Classical.propDecidable (S.Checks publicValues l.1 l.2 τ α ζ o)) &&
      evalWithAnswerFn (ExecutionPath.closingImpl (tree := S.friProtocol.tree) p
        S.friProtocol.oracles S.quotientAccess (S.messagesImpl T P Q))
        (Fri.Interaction.terminal (S.logN S.top + S.params.logBlowup)
        (2 ^ S.params.logFinalPolyLen) S.params.numQueries S.domainSetup.friDomain
        S.quotientAccess (S.deepReader l.1 l.2 τ α ζ o a) (S.domainSetup.friSchedule S.friHeights)
        (ExecutionPath.toBranchPath (tree := S.friProtocol.tree) p))) = true := by
    unfold evalWithAnswerFn at h ⊢
    rw [terminal, simulateQ_map] at h
    exact h
  rw [Bool.and_eq_true] at h'
  obtain ⟨w, hw⟩ := Fri.Interaction.terminal_holds_of_eval (S.logN S.top + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.deepWords T l.1 l.2 P τ α Q ζ o a) δ
    loss L (Nat.two_pow_pos _) loss.coe_nonneg (S.domainSetup.friSchedule S.friHeights) le_rfl
    S.domainSetup.friDomain _ _ _ 0 (S.deepWords T l.1 l.2 P τ α Q ζ o a _) Finset.univ
    (S.reads_deepReader T l.1 l.2 P τ α Q ζ o a)
    (fun x ↦ by simp only [Finset.mem_univ, decide_true]; rfl) p h'.2
  rw [terminalState_certificate]
  simp only [friCertificate, gateCertificate]
  rw [terminalState_gateExtractor]
  exact ⟨w, @of_decide_eq_true _ (Classical.propDecidable _) h'.1, hw⟩

/-- FRI's erased prefixes in the batch. -/
abbrev FriPrefix : Type :=
  Prefix PUnit (Fri.Interaction.publicCoin 𝕂 (S.logN S.top + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.domainSetup.friSchedule S.friHeights))

/-- The erased prefixes of the batch. -/
abbrev PrefixShape : Type :=
  S.TraceMessage × (PUnit ⊕ (PUnit × (S.PermMessage × ((_ : Fin S.k → 𝕂) × (PUnit ⊕
    (PUnit × (S.QuotientMessage × (PUnit ⊕ (PUnit × ((_ : S.OpeningsMessage) ×
      (PUnit ⊕ (PUnit × S.FriPrefix))))))))))))

/-- The node errors of the batch at its lengths, at proximity `δ`, extraction radius `δ'`,
proximity loss `loss` and query positions of slack `slack`: the lookup error at the lookup
challenges, the largest over the instances of the folding error at `α`, of the out-of-domain error
at `ζ` and of the batching error at `a`, and FRI's node errors on the batched DEEP words. -/
noncomputable def nodeErrors (loss : ℝ≥0) (slack : ENNReal) : Errors S.publicCoin := fun node ↦
  match (node : S.PrefixShape) with
  | ⟨_, .inl _⟩ => S.lookupError δ'
  | ⟨_, .inr ⟨_, _, _, .inl _⟩⟩ => ⨆ i, foldingError (S.instanceSetup i) δ'
  | ⟨_, .inr ⟨_, _, _, .inr ⟨_, _, .inl _⟩⟩⟩ => ⨆ i, outOfDomainError (S.instanceSetup i) δ'
  | ⟨_, .inr ⟨_, _, _, .inr ⟨_, _, .inr ⟨_, _, .inl _⟩⟩⟩⟩ =>
      ⨆ i, batchingErrorOf (S.instanceSetup i) (S.groupNumOpened (S.logN i + S.params.logBlowup))
        δ δ'
  | ⟨_, .inr ⟨_, _, _, .inr ⟨_, _, .inr ⟨_, _, .inr ⟨_, node⟩⟩⟩⟩⟩ =>
      Fri.Interaction.nodeErrors (S.logN S.top + S.params.logBlowup)
        (2 ^ S.params.logFinalPolyLen) S.params.numQueries δ loss slack S.domainSetup.friDomain
        (S.domainSetup.friSchedule S.friHeights) 0 node

/-- The certificate's error at each node is at most the node error at its positions' slack. -/
theorem supErrors_certificate_le (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0)
    (L : S.domainSetup.QueryPositions) (node : Prefix PUnit S.publicCoin) :
    supErrors S.publicCoin (S.certificate publicValues δ δ' hδ' loss L).challenges node ≤
      S.nodeErrors δ δ' loss L.slack node := by
  obtain ⟨T, _ | ⟨_, P, τ, _ | ⟨_, Q, _ | ⟨_, o, _ | ⟨_, node⟩⟩⟩⟩⟩ := (node : S.PrefixShape)
  · exact le_rfl
  · exact iSup_le fun l ↦ le_iSup (fun i ↦ foldingError (S.instanceSetup i) δ') _
  · exact iSup_le fun l ↦ iSup_le fun α ↦
      le_iSup (fun i ↦ outOfDomainError (S.instanceSetup i) δ') _
  · exact iSup_le fun l ↦ iSup_le fun α ↦ iSup_le fun ζ ↦ le_iSup (fun i ↦
      batchingErrorOf (S.instanceSetup i) (S.groupNumOpened (S.logN i + S.params.logBlowup))
        δ δ') _
  · refine iSup_le fun l ↦ iSup_le fun α ↦ iSup_le fun ζ ↦ iSup_le fun a ↦ le_of_eq ?_
    exact Fri.Interaction.supErrors_certificate (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.deepWords T l.1 l.2 P τ α Q ζ o a) δ
      loss L (Nat.two_pow_pos _) loss.coe_nonneg le_rfl S.domainSetup.friDomain
      (S.domainSetup.friSchedule S.friHeights) 0 (S.deepWords T l.1 l.2 P τ α Q ζ o a _)
      Finset.univ node

/-- The path sum of the node errors for uniform positions: the lookup error, the largest folding,
out-of-domain and batching errors over the instances, and FRI's error at the proximity loss. -/
theorem pathError_nodeErrors (loss : ℝ≥0) :
    pathError S.publicCoin (S.nodeErrors δ δ' loss 0) =
      S.lookupError δ' + (⨆ i, foldingError (S.instanceSetup i) δ') +
        (⨆ i, outOfDomainError (S.instanceSetup i) δ') +
        (⨆ i, batchingErrorOf (S.instanceSetup i)
          (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ δ') +
        S.domainSetup.friBound S.friHeights δ loss := by
  change (⨆ _ : S.TraceMessage, S.lookupError δ' + ⨆ _ : S.PermMessage, ⨆ _ : Fin S.k → 𝕂,
    (⨆ i, foldingError (S.instanceSetup i) δ') + ⨆ _ : S.QuotientMessage,
    (⨆ i, outOfDomainError (S.instanceSetup i) δ') + ⨆ _ : S.OpeningsMessage,
    (⨆ i, batchingErrorOf (S.instanceSetup i) (S.groupNumOpened (S.logN i + S.params.logBlowup))
      δ δ') +
      pathError (Fri.Interaction.publicCoin 𝕂 (S.logN S.top + S.params.logBlowup)
        (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.domainSetup.friSchedule S.friHeights))
        (Fri.Interaction.nodeErrors (S.logN S.top + S.params.logBlowup)
          (2 ^ S.params.logFinalPolyLen) S.params.numQueries δ loss 0 S.domainSetup.friDomain
          (S.domainSetup.friSchedule S.friHeights) 0)) = _
  rw [Fri.Interaction.pathError_nodeErrors]
  simp only [iSup_const, Iop.Setup.friBound, Fri.Interaction.threshold, zero_add, add_assoc,
    add_zero]

end Setup

namespace Statement
variable (C : Statement F) (EF : Type) [Challenge F EF]

/-- The batch STARK for a statement is public-coin: the lengths the prover sends, then the batch
at those lengths. -/
noncomputable def publicCoin : PublicCoin (C.protocol EF) :=
  .sender fun n ↦ (C.setup EF n).publicCoin

variable (publicValues : Fin C.k → List F) (δ δ' : (Fin C.k → ℕ) → ℝ≥0)

/-- The input state: admitted lengths, and a trace message and traces there, close to the message
and satisfying the batch at those lengths. -/
def rootState : KnowledgeState where
  Witness := (n : C.Length) × ((C.setup EF n).rootState publicValues (δ' n.1)).Witness
  holds w := ((C.setup EF w.1).rootState publicValues (δ' w.1.1)).holds w.2

variable {C}

/-- **The statement's knowledge certificate**: whatever lengths the prover sends, the batch's
certificate at those lengths, at their proximity loss `loss n` and query positions `L n`. -/
noncomputable def certificate (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) (L : (n : C.Length) → (C.setup EF n).domainSetup.QueryPositions) :
    KnowledgeCertificate (C.protocol EF).tree (C.protocol EF).roles
      (C.rootState EF publicValues δ') where
  extractor n := ⟨_, fun w ↦ ⟨n, w⟩, ((C.setup EF n).certificate publicValues (δ n.1) (δ' n.1)
    (hδ' n.1 n.2) (loss n) (L n)).extractor⟩
  challenges := ⟨PUnit.unit, fun n ↦ ((C.setup EF n).certificate publicValues (δ n.1) (δ' n.1)
    (hδ' n.1 n.2) (loss n) (L n)).challenges⟩
  prover_preserving := ⟨fun _ _ _ h ↦ h, fun n ↦ ((C.setup EF n).certificate publicValues
    (δ n.1) (δ' n.1) (hδ' n.1 n.2) (loss n) (L n)).prover_preserving⟩
  local_bound n := ((C.setup EF n).certificate publicValues (δ n.1) (δ' n.1)
    (hδ' n.1 n.2) (loss n) (L n)).local_bound

/-- The statement's certificate with uniform query positions samples every challenge uniformly. -/
theorem uniformChallenges_certificate (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) :
    UniformChallenges (C.publicCoin EF) (certificate EF publicValues δ δ' hδ' loss
      fun n ↦ (C.setup EF n).domainSetup.uniformPositions).challenges :=
  fun n ↦ (C.setup EF n).uniformChallenges_certificate publicValues (δ n.1) (δ' n.1) _ (loss n)

variable (C)

/-- The verifier's checks on a branch: the batch's checks at the lengths it sends. -/
noncomputable def terminal (p : (C.protocol EF).tree.BranchPath) :
    OracleComp (OracleSpec.ofPFunctor (accessAfter (C.protocol EF).tree (C.protocol EF).oracles
      noAccess p)) Bool :=
  (C.setup EF p.1).terminal publicValues p.2

/-- The node errors of the batch for a statement: at each vector of lengths, the batch's node
errors there, at its proximity loss and query positions of slack `slack`. -/
noncomputable def nodeErrors (loss : C.Length → ℝ≥0) (slack : ENNReal) :
    Errors (C.publicCoin EF) := fun node ↦
  (C.setup EF node.1).nodeErrors (δ node.1.1) (δ' node.1.1) (loss node.1) slack node.2

/-- **State-restoration knowledge soundness of the batch STARK.** In the state-restoration game
of the batch's public-coin presentation, where an adversary making at most `Q` random-oracle
queries chooses the public values and every prover message, the verifier's checks pass while no
tuple of traces of the claimed lengths close to the committed ones satisfies the batch with
probability at most `Q * maxError + sumError` of the node errors: at each vector of lengths, the
lookup error, the largest folding, out-of-domain and batching errors over the instances, and FRI's
fold and query errors at the proximity loss `loss n` (`Setup.pathError_nodeErrors`). -/
theorem stateRestoration_le (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) {Salt W : Type} [DecidableEq Salt]
    (adversary : OracleComp (oracleSpec (Fin C.k → List F) Salt fun _ ↦ C.publicCoin EF)
      (Selection (Fin C.k → List F) Salt W fun _ ↦ C.publicCoin EF))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (verificationGame (fun _ ↦ C.publicCoin EF) noAccess
        (fun _ ↦ noImpl) (fun _ _ ↦ Bool) (C.terminal EF) adversary)).run' ∅}[
      result.2.2.1 = true ∧ C.Far EF result.1 δ' result.2.1] ≤
      Q * maxError (fun _ : Fin C.k → List F ↦ C.nodeErrors EF δ δ' loss 0) +
        sumError (fun _ : Fin C.k → List F ↦ C.nodeErrors EF δ δ' loss 0) := by
  have h := KnowledgeCertificate.stateRestoration_extraction_le (fun _ ↦ C.publicCoin EF)
    (fun publicValues ↦ C.rootState EF publicValues δ')
    (fun publicValues ↦ certificate EF publicValues δ δ' hδ' loss
      fun n ↦ (C.setup EF n).domainSetup.uniformPositions)
    (fun publicValues ↦ uniformChallenges_certificate EF publicValues δ δ' hδ' loss) noAccess
    (fun _ ↦ noImpl) (fun _ _ ↦ Bool) (C.terminal EF) adversary Q queryBound
  have hle : ∀ (publicValues : Fin C.k → List F) node, supErrors (C.publicCoin EF)
      (certificate EF publicValues δ δ' hδ' loss
        fun n ↦ (C.setup EF n).domainSetup.uniformPositions).challenges node ≤
      C.nodeErrors EF δ δ' loss 0 node := fun publicValues node ↦
    (C.setup EF node.1).supErrors_certificate_le publicValues (δ node.1.1) (δ' node.1.1) _
      (loss node.1) _ node.2
  rw [verificationGame_eq, simulateQ_map] at h
  rw [verificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map] at h ⊢
  refine (prEvent_mono _ _ _ fun result hres ↦ ?_).trans (h.trans ?_)
  · obtain ⟨pv, ⟨n, p⟩, wit⟩ := result
    obtain ⟨hacc, hfar⟩ := hres
    obtain ⟨w, hw⟩ := (C.setup EF n).terminal_holds_of_eval pv (δ n.1) (δ' n.1) (hδ' n.1 n.2)
      (loss n) (C.setup EF n).domainSetup.uniformPositions p hacc
    exact ⟨w, hw, fun hroot ↦ hfar _ hroot.1 hroot.2⟩
  · gcongr
    · exact maxError_mono hle
    · exact sumError_mono hle

end Statement

end CompStark.Iop.Batch
