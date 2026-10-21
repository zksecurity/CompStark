/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Batch
public import CompStark.Stark.Config

/-! # Completeness of the batch-STARK verifier

Over any base field with Plonky3's Poseidon2 instances and any challenge field, if every
instance's trace satisfies its AIR with as many public values as the AIR declares
(`Batch.Satisfied`), the honest prover's batch proof verifies against the batch's common data
(`setupBatch`) (`Batch.completeness`). Besides this premise, the theorem assumes two things, each
a structure with one documented field per condition:

* `Batch.ValidConfig`: the batch is one the prover supports: it has an instance, and every
  instance's AIR and trace length are a valid configuration (`ValidConfig`,
  `CompStark/Stark/Config.lean`). Traces of different lengths share FRI's parameters, so FRI's
  final polynomial must be no longer than the shortest trace.
* `Batch.NoBadLuck`: the honest run avoids two events of negligible probability that make it
  fail: the out-of-domain point lands in the base field, or a proof-of-work search finds no
  witness.

The proof is in `CompStark/Complete/`: the batch layer in `CompStark/Complete/Batch.lean`, the
openings of matrices of mixed heights in `CompStark/Complete/Pcs.lean`.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark

variable {F : Type} [BaseField F] [Poseidon2Field F] {EF : Type} [Challenge F EF]

/-- A batch the prover supports, checkable before proving and independent of the traces. -/
structure ValidConfig (params : Params) (instances : List (Instance F)) : Prop where
  /-- The batch has an instance. -/
  nonempty : instances ≠ []
  /-- Every instance's AIR and trace length are a valid configuration; in particular FRI's final
  polynomial is no longer than the instance's trace. -/
  valid : ∀ I ∈ instances, Stark.ValidConfig params I.air I.logN

/-- One trace and one list of public values per instance; every instance's trace satisfies its
AIR with its public values, as many as the AIR declares. -/
structure Satisfied (instances : List (Instance F)) (traces : List (Array F))
    (publicValues : List (List F)) : Prop where
  /-- One trace per instance. -/
  tracesLength : traces.length = instances.length
  /-- One list of public values per instance. -/
  publicValuesLength : publicValues.length = instances.length
  /-- Every instance's trace satisfies its AIR with its public values. -/
  satisfied : ∀ x ∈ instances.zip (traces.zip publicValues),
    x.1.air.Satisfied x.1.logN x.2.1 x.2.2
  /-- Every instance has as many public values as its AIR declares. -/
  publicValueCounts : ∀ x ∈ instances.zip publicValues, x.2.length = x.1.air.numPublicValues

variable (EF) in
/-- The honest batch run over the extension `EF` avoids two unlikely events in which it fails. -/
structure NoBadLuck (params : Params) (instances : List (Instance F)) (traces : List (Array F))
    (publicValues : List (List F)) : Prop where
  /-- The out-of-domain point `ζ` (`batchOutOfDomainPoint`), a random element of the extension of
  degree `d`, does not lie in the base field. It does with probability `|F| ^ (1 - d)`; then
  `ζ - x` vanishes for some point `x` of the domains and the openings divide by zero. -/
  outOfDomain : Ext.OutsideBase (batchOutOfDomainPoint EF params instances traces publicValues)
  /-- Every proof-of-work search of the honest run finds a witness (`proveBatchTranscript`
  records a failed search, where Plonky3's grinder would panic). A search for `b` bits tries every
  field element, each a witness with probability `2 ^ -b`, so it fails with probability about
  `exp (-|F| / 2 ^ b)`. -/
  grinding : (proveBatchTranscript EF params instances traces publicValues).grindFailed = false

/-- **Batch completeness.** For a valid batch and an honest run over any challenge field `EF`
without bad luck, if every instance's trace satisfies its AIR with its public values, the honest
prover's batch proof verifies against the batch's common data. -/
theorem completeness {params : Params} {instances : List (Instance F)} {traces : List (Array F)}
    {publicValues : List (List F)} (config : ValidConfig params instances)
    (luck : NoBadLuck EF params instances traces publicValues) :
    Satisfied instances traces publicValues →
      verifyBatch params instances (setupBatch params instances)
        (proveBatch EF params instances traces publicValues) publicValues = .ok () := by
  intro sat
  have hmem : ∀ i (hi : i < instances.length),
      (instances[i], (traces[i]'(sat.tracesLength ▸ hi), publicValues[i]'(sat.publicValuesLength ▸ hi))) ∈
        instances.zip (traces.zip publicValues) := fun i hi ↦ by
    have h := List.getElem_mem (l := instances.zip (traces.zip publicValues)) (n := i) (by
      simp only [List.length_zip, sat.tracesLength, sat.publicValuesLength, Nat.min_self]; exact hi)
    simpa only [List.getElem_zip] using h
  obtain ⟨I0, hI0⟩ := List.exists_mem_of_ne_nil _ config.nonempty
  have v0 := config.valid I0 hI0
  refine verifyBatch_proveBatch_of EF params instances traces publicValues config.nonempty
    sat.tracesLength sat.publicValuesLength (fun i hi ↦ ?_) (fun i hi ↦ (sat.satisfied _ (hmem i hi)).vanish)
    (fun i hi ↦ ?_) (fun I hI ↦ (config.valid I hI).degreeFits) v0.folds v0.queries v0.blowup
    (fun I hI ↦ (config.valid I hI).finalPolyFits) luck.grinding luck.outOfDomain
  · have v := config.valid _ (List.getElem_mem hi)
    exact ⟨(sat.satisfied _ (hmem i hi)).size, v.colsInWidth, v.twoAdic, v.chunksFit,
      v.periodicFits⟩
  · have h := List.getElem_mem (l := instances.zip publicValues) (n := i) (by
      simp only [List.length_zip, sat.publicValuesLength, Nat.min_self]; exact hi)
    simpa only [List.getElem_zip] using sat.publicValueCounts _ h

end CompStark.Batch
