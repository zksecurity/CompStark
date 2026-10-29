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
value `v` there with a boolean multiplicity `s`. In a batch of them (`Setup.IsRangeBatch`, and
`Statement.IsRangeBatch` for a statement, its tables at their keygen heights), lookup
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
queries: if no tuple of traces of the prover's claimed lengths, each close to its instance's
committed trace, satisfies every AIR with every real query in range, the verifier accepts with
probability at most the statement's knowledge error. -/
theorem rangeKnowledgeSoundness (C : Batch.Statement F) (hC : C.IsRangeBatch)
    (publicValues : Fin C.k → List F) (prover : C.Prover EF) (δ δ' : (Fin C.k → ℕ) → NNReal)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) :
    (∀ traces ∈ Batch.closeTraces prover.setup (δ' prover.logN) prover.prover.trace,
      ¬ ((∀ i, (C.air i).Satisfied (prover.logN i) (traces i) (publicValues i)) ∧
        prover.setup.RangeChecked traces)) →
      Batch.acceptance publicValues prover.prover ≤ C.knowledgeError EF δ δ' :=
  fun h ↦ batchKnowledgeSoundness_inclusion C publicValues prover δ δ' hδ'
    (fun n hn ↦ Batch.countsBounded_of_isRangeBatch _ (C.isRangeBatch_setupAt (EF := EF) hC n hn))
    fun traces ht hsat ↦ h traces ht ⟨hsat.air, Batch.rangeChecked_of_satisfiedWithInclusion
      _ (C.isRangeBatch_setupAt hC _ prover.admits) traces publicValues hsat⟩

/-- **Knowledge soundness of a range check in the random-oracle model.** For a batch statement
of range tables and range queries: a prover making at most `Q` oracle calls gets a proof accepted,
while no tuple of traces of the proof's lengths close to the ones it committed to satisfies every
AIR with every real query in range, with probability at most
`q · roundError + hashError F (h + 1) q`, `q = Q + verifierQueries`. -/
theorem rangeKnowledgeSoundness_ro (C : Batch.Statement F) (hC : C.IsRangeBatch)
    (publicValues : Fin C.k → List F) (δ δ' : (Fin C.k → ℕ) → NNReal)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (Q : Nat) (prover : C.NIProver EF)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← C.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : C.Admits (C.lengthsOf proof),
          ∀ traces ∈ Batch.closeTraces (C.setupAt EF _ h) (δ' (C.lengthsOf proof))
              (Batch.committedTraces (C.setupAt EF _ h) log proof),
            ¬ ((∀ i, (C.air i).Satisfied (C.lengthsOf proof i) (traces i) (publicValues i)) ∧
              (C.setupAt EF _ h).RangeChecked traces)] ≤
      (Q + C.verifierQueries EF) * C.roundError EF δ δ' +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) :=
  (prEvent_mono _ _ _ fun ⟨_, _, _⟩ h ↦ ⟨h.1, fun hn traces ht hsat ↦ h.2 hn traces ht
    ⟨hsat.air, Batch.rangeChecked_of_satisfiedWithInclusion _ (C.isRangeBatch_setupAt hC _ hn)
      traces publicValues hsat⟩⟩).trans
    (Batch.batchKnowledgeSoundness_ro_inclusion C publicValues δ δ' hδ' Q prover hQ
      fun n hn ↦ Batch.countsBounded_of_isRangeBatch _
        (C.isRangeBatch_setupAt (EF := EF) hC n hn))

end CompStark.Iop
