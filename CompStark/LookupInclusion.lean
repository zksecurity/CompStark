/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Security
public import CompStark.Sound.Range

/-! # Lookup inclusion, applied

The batch STARK's knowledge soundness with lookup inclusion (`batchKnowledgeSoundness_inclusion`,
`batchKnowledgeSoundness_ro_inclusion`) asks every AIR to keep its queries' multiplicities within
their weights (`Air.CountsBounded`). A syntactic check discharges it for any AIR
(`Air.countsChecked`, sound by `Sound.Batch.countsBounded_of_countsChecked`): the batches of
`wideBus 64` pass it by `decide`.

A range check: range tables (`rangeTable`), each providing the values `0, …, 2 ^ logN - 1` on the
bus `range` with unconstrained multiplicities, and range queries (`rangeQuery`), each querying a
value `v` there with a boolean multiplicity `s`. In a batch of them (`Setup.IsRangeBatch`), lookup
inclusion makes every query with `s = 1` a row index of some table (`Setup.RangeChecked`), so the
verifier accepts with probability at most the knowledge error while no tuple of close traces
satisfies the AIRs with every real query in range (`rangeKnowledgeSoundness`,
`rangeKnowledgeSoundness_ro`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

/-! ### The count check on `wideBus` -/

section WideBus

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize

/-- `wideBus 64` passes the count check: its multiplicities are the constants `1` and `-1`, each of
weight `1`. -/
theorem wideBus_countsChecked : (wideBus 64 : Air F).countsChecked = true := by decide

theorem wideBatch_countsBounded (i : Fin wideBatchSetup.k) :
    (wideBatchSetup.air i).CountsBounded (wideBatchSetup.logN i) :=
  Batch.Setup.countsBounded_of_countsChecked _ (fun _ ↦ wideBus_countsChecked) i

theorem wideBatch5_countsBounded (i : Fin wideBatch5Setup.k) :
    (wideBatch5Setup.air i).CountsBounded (wideBatch5Setup.logN i) :=
  Batch.Setup.countsBounded_of_countsChecked _ (fun _ ↦ wideBus_countsChecked) i

theorem wideBatchGrind_countsBounded (i : Fin wideBatchGrindSetup.k) :
    (wideBatchGrindSetup.air i).CountsBounded (wideBatchGrindSetup.logN i) :=
  Batch.Setup.countsBounded_of_countsChecked _ (fun _ ↦ wideBus_countsChecked) i

end WideBus

/-! ### A range check -/

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **Knowledge soundness of a range check.** For a batch of range tables and range queries
within the verifier's multiplicity bound: if no tuple of traces, each close to its instance's
committed trace, satisfies every AIR with every real query in range, the verifier accepts with
probability at most the knowledge error. -/
theorem rangeKnowledgeSoundness (S : Batch.Setup EF) (hS : S.IsRangeBatch)
    (publicValues : Fin S.k → List F) (prover : Batch.Prover S) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate) (hbound : S.HeightBounded) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace,
      ¬ ((∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)) ∧
        S.RangeChecked traces)) →
      Batch.acceptance publicValues prover ≤ Batch.knowledgeError S δ δ' :=
  fun h ↦ batchKnowledgeSoundness_inclusion S publicValues prover δ δ' hδ' hbound
    (Batch.countsBounded_of_isRangeBatch S hS) fun traces ht hsat ↦ h traces ht
      ⟨hsat.air, Batch.rangeChecked_of_satisfiedWithInclusion S hS traces publicValues hsat⟩

/-- **Knowledge soundness of a range check in the random-oracle model.** For a batch of range
tables and range queries: a prover making at most `Q` oracle calls gets a proof for the
instances' trace lengths accepted, while no tuple of traces close to the ones it committed to
satisfies every AIR with every real query in range, with probability at most
`q · roundError + hashError F h q`, `q = Q + verifierQueries`. -/
theorem rangeKnowledgeSoundness_ro (S : Batch.Setup EF) (hS : S.IsRangeBatch)
    (publicValues : Fin S.k → List F) (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : Nat)
    (prover : Batch.NIProver S) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn S.logN ∧
        ∀ traces ∈ Batch.closeTraces S δ' (Batch.committedTraces S log proof),
          ¬ ((∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)) ∧
            S.RangeChecked traces)] ≤
      (Q + S.verifierQueries) * Batch.roundError S δ δ' +
        hashError F S.params.capHeight (Q + S.verifierQueries) :=
  (prEvent_mono _ _ _ fun ⟨_, _, _⟩ h ↦ ⟨h.1, h.2.1, fun traces ht hsat ↦ h.2.2 traces ht
    ⟨hsat.air, Batch.rangeChecked_of_satisfiedWithInclusion S hS traces publicValues hsat⟩⟩).trans
    (Batch.batchKnowledgeSoundness_ro_inclusion S publicValues δ δ' hδ' Q prover hQ
      (Batch.countsBounded_of_isRangeBatch S hS))

end CompStark.Iop
