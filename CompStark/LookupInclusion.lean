/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Security
public import CompStark.Sound.Range
public import CompStark.Fs.BatchBcs

/-! # Lookup inclusion, applied

The batch STARK's knowledge soundness with lookup inclusion (`batchKnowledgeSoundness_inclusion`,
and `Batch.Statement.knowledgeSoundness_bcs_inclusion` for Plonky3's batch verifier with Merkle
commitments) asks every AIR to keep its queries' multiplicities within their weights
(`Air.CountsBounded`). A syntactic check discharges it for any AIR
(`Air.countsChecked`, sound by `Sound.Batch.countsBounded_of_countsChecked`): the batches of
`wideBus 64` pass it by `decide`.

A range check: range tables (`rangeTable`), each providing the values `0, …, 2 ^ logN - 1` on the
bus `range` with unconstrained multiplicities, and range queries (`rangeQuery`), each querying a
value `v` there with a boolean multiplicity `s`. In a batch of them (`Setup.IsRangeBatch`, and
`Statement.IsRangeBatch` for a statement, its tables at their keygen heights), lookup
inclusion makes every query with `s = 1` a row index of some table (`Setup.RangeChecked`), so the
verifier accepts with probability at most the knowledge error while no tuple of close traces
satisfies the AIRs with every real query in range (`rangeKnowledgeSoundness`,
`Batch.Statement.rangeKnowledgeSoundness_bcs`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound OracleSpec

/-! ### The count check on `wideBus` -/

section WideBus

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize

/-- `wideBus 64` passes the count check: its multiplicities are the constants `1` and `-1`, each of
weight `1`. -/
theorem wideBus_countsChecked : (wideBus 64 : Air F).countsChecked = true := by decide

theorem wideBatch_countsBounded (n : Fin wideBatchStatement.k → ℕ)
    (hn : wideBatchStatement.Admits n) (i : Fin wideBatchStatement.k) :
    (wideBatchStatement.air i).CountsBounded (n i) :=
  wideBatchStatement.countsBounded_of_countsChecked (fun _ ↦ wideBus_countsChecked) n hn i

theorem wideBatch5_countsBounded (n : Fin wideBatch5Statement.k → ℕ)
    (hn : wideBatch5Statement.Admits n) (i : Fin wideBatch5Statement.k) :
    (wideBatch5Statement.air i).CountsBounded (n i) :=
  wideBatch5Statement.countsBounded_of_countsChecked (fun _ ↦ wideBus_countsChecked) n hn i

theorem wideBatchGrind_countsBounded (n : Fin wideBatchGrindStatement.k → ℕ)
    (hn : wideBatchGrindStatement.Admits n) (i : Fin wideBatchGrindStatement.k) :
    (wideBatchGrindStatement.air i).CountsBounded (n i) :=
  wideBatchGrindStatement.countsBounded_of_countsChecked (fun _ ↦ wideBus_countsChecked) n hn i

end WideBus

/-! ### A range check -/

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of a range check.** For a batch statement of range tables and range
queries: against any prover, the verifier accepts while no tuple of traces of the prover's claimed
lengths, each close to its instance's committed trace, satisfies every AIR with every real query
in range, with probability at most the statement's knowledge error. -/
theorem rangeKnowledgeSoundness (C : Batch.Statement F) (hC : C.IsRangeBatch)
    (publicValues : Fin C.k → List F) {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP)
    (δ δ' : (Fin C.k → ℕ) → NNReal) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) :
    C.farAcceptance EF publicValues δ' (fun n traces ↦
      (∀ i, (C.air i).Satisfied (n.1 i) (traces i) (publicValues i)) ∧
        (C.setup EF n).RangeChecked traces) prover ≤ C.knowledgeError EF δ δ' :=
  (C.farAcceptance_mono EF publicValues δ' (fun n traces hsat ↦
    ⟨hsat.air, Batch.rangeChecked_of_satisfiedWithInclusion _ (C.isRangeBatch_setupAt hC n.1 n.2)
      traces publicValues hsat⟩) prover).trans
    (batchKnowledgeSoundness_inclusion C publicValues prover δ δ' hδ'
      fun n hn ↦ Batch.countsBounded_of_isRangeBatch _ (C.isRangeBatch_setupAt (EF := EF) hC n hn))

end CompStark.Iop

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs CompStark.RandomOracle OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {C : Statement F} {EF : Type} [Challenge F EF] {K : ℕ}

/-- **Knowledge soundness of Plonky3's batch STARK verifier with Merkle commitments, with lookup
inclusion.** For AIRs that keep their queries' multiplicities within their weights at every
admitted vector of lengths: the verifier accepts while no tuple of traces of the proof's lengths,
each close to the trace extracted from the log under the proof's main commitment, satisfies every
AIR with every bus's queries included in what is provided, with probability at most the bound of
`knowledgeSoundness_bcs`. -/
theorem knowledgeSoundness_bcs_inclusion (hK : 0 < K) (δ δ' : (Fin C.k → ℕ) → ℝ≥0)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (loss : C.Length → ℝ≥0)
    (hcounts : ∀ n, C.Admits n → ∀ i, (C.air i).CountsBounded (n i))
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF))
    {Q q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (C.batchGame EF K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧ ∀ h : C.Admits (C.lengthsOf z.1.2.2.1),
        ∀ traces ∈ closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf z.1.2.2.1))
          ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
            (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.mainCommit)),
        ¬ (C.setupAt EF _ h).SatisfiedWithInclusion traces z.1.2.1] ≤
      chainError (Digest F) (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K) +
        hashBadError F (2 ^ C.params.capHeight) (C.capOffsets EF).length
          (q + C.verifierQueries EF) +
        (maxError (fun (_ : C.Input) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss (1 / Nat.card F) node) *
            (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K : ℕ) +
          sumError (fun (_ : C.Input) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss (1 / Nat.card F) node)) :=
  (prEvent_mono _ _ _ fun _ h ↦ ⟨h.1, fun hn traces ht hsat ↦ h.2 hn traces ht
    (Batch.satisfiedWithInclusion_of_satisfied _ traces _ (C.heightBounded_setupAt _ hn)
      (hcounts _ hn) hsat)⟩).trans
    (C.knowledgeSoundness_bcs EF K hK δ δ' hδ' loss adversary hQ hq)

/-- **Knowledge soundness of a range check on Plonky3's batch verifier with Merkle commitments.**
For a batch statement of range tables and range queries: the verifier accepts while no tuple of
traces of the proof's lengths, each close to the trace extracted from the log under the proof's
main commitment, satisfies every AIR with every real query in range, with probability at most the
bound of `knowledgeSoundness_bcs`. -/
theorem rangeKnowledgeSoundness_bcs (hC : C.IsRangeBatch) (hK : 0 < K)
    (δ δ' : (Fin C.k → ℕ) → ℝ≥0) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0)
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF))
    {Q q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (C.batchGame EF K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧ ∀ h : C.Admits (C.lengthsOf z.1.2.2.1),
        ∀ traces ∈ closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf z.1.2.2.1))
          ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
            (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.mainCommit)),
        ¬ ((∀ i, (C.air i).Satisfied (C.lengthsOf z.1.2.2.1 i) (traces i) (z.1.2.1 i)) ∧
          (C.setupAt EF _ h).RangeChecked traces)] ≤
      chainError (Digest F) (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K) +
        hashBadError F (2 ^ C.params.capHeight) (C.capOffsets EF).length
          (q + C.verifierQueries EF) +
        (maxError (fun (_ : C.Input) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss (1 / Nat.card F) node) *
            (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K : ℕ) +
          sumError (fun (_ : C.Input) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss (1 / Nat.card F) node)) :=
  (prEvent_mono _ _ _ fun _ h ↦ ⟨h.1, fun hn traces ht hsat ↦ h.2 hn traces ht
    ⟨hsat.air, Batch.rangeChecked_of_satisfiedWithInclusion _ (C.isRangeBatch_setupAt hC _ hn)
      traces _ hsat⟩⟩).trans
    (knowledgeSoundness_bcs_inclusion hK δ δ' hδ' loss
      (fun n hn ↦ Batch.countsBounded_of_isRangeBatch _
        (C.isRangeBatch_setupAt (EF := EF) hC n hn)) adversary hQ hq)

end CompStark.Iop.Batch.Statement
