/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Batch
public import CompStark.Stark.Config

/-! # Completeness of the batch-STARK verifier

Over any base field with Plonky3's Poseidon2 instances and any challenge field, if every
instance's trace satisfies its AIR with as many public values as the AIR declares, every bus of
the batch's lookups balances and the multiplicities stay below the characteristic
(`Batch.Satisfied`), the honest prover's batch proof verifies against the batch's common data
(`setupBatch`) (`Batch.completeness`). Besides this premise, the theorem assumes two things, each
a structure with one documented field per condition:

* `Batch.ValidConfig`: the batch is one the prover supports: it has an instance; every
  instance's AIR and trace length are a valid configuration (`ValidConfig`,
  `CompStark/Stark/Config.lean`); its quotient, its lookups' LogUp constraints included, fits the
  blowup and its constraints fit the quotient's chunks; its lookups are row-local and read its
  columns; and the batch's tuples have one width per lookup and per bus. Traces of different
  lengths share FRI's parameters, so FRI's final polynomial must be no longer than the shortest
  trace.
* `Batch.NoBadLuck`: the honest run avoids three events of negligible probability that make it
  fail: the out-of-domain point lands in the base field, a lookup challenge makes a denominator
  of non-zero multiplicity vanish, or a proof-of-work search finds no witness.

The proof is in `CompStark/Complete/`: the batch layer in `CompStark/Complete/Batch.lean`, the
openings of matrices of mixed heights in `CompStark/Complete/Pcs.lean`, the LogUp gadget in
`CompStark/Complete/LogUp.lean` and `CompStark/Complete/LogUpQuotient.lean`.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark CompStark.Lookup

variable {F : Type} [BaseField F] [Poseidon2Field F] {EF : Type} [Challenge F EF]

/-- A batch the prover supports, checkable before proving and independent of the traces. -/
structure ValidConfig (params : Params) (instances : List (Instance F)) : Prop where
  /-- The batch has an instance. -/
  nonempty : instances ≠ []
  /-- Every instance's AIR and trace length are a valid configuration; in particular FRI's final
  polynomial is no longer than the instance's trace. -/
  valid : ∀ I ∈ instances, Stark.ValidConfig params I.air I.logN
  /-- Every instance's quotient chunks, its lookups' LogUp constraints included, fit the
  blowup. -/
  chunksFit : ∀ I ∈ instances, I.logQuotientChunks ≤ params.logBlowup
  /-- Every instance's constraints divided by the trace domain's vanishing polynomial fit its
  quotient's chunks (`Air.DegreeFitsAt`). -/
  degreeFits : ∀ I ∈ instances, I.air.DegreeFitsAt I.logN I.logQuotientChunks
  /-- So do its lookups' LogUp constraints. -/
  lookupDegreeFits : ∀ I ∈ instances, ∀ g ∈ I.air.lookupConstraints I.logN,
    g.degBound (2 ^ I.logN) (I.air.periodicDegree (2 ^ I.logN)) <
      2 ^ (I.logN + I.logQuotientChunks) + 2 ^ I.logN
  /-- Every lookup's tuples and multiplicities read only the trace's and the preprocessed trace's
  columns of the AIR, the next rows only if opened, and the public values (`Lookup.Fits`). -/
  lookupsFit : ∀ I ∈ instances, ∀ l ∈ I.lookups,
    l.Fits I.air.width I.air.mainNextWidth I.air.preprocessedWidth I.air.preprocessedNextWidth
  /-- Every lookup's tuples share one width, and so do every bus's (`widthsOk`). -/
  widths : widthsOk (instances.flatMap (·.lookups)) = true

/-- One trace and one list of public values per instance; every instance's trace satisfies its
AIR with its public values, as many as the AIR declares; every bus balances; and the
multiplicities stay below the characteristic. -/
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
  /-- Every bus balances: the multiplicities of every bus and tuple of values sum to zero in the
  field (`Balanced`), as LogUp checks. -/
  balanced : Balanced instances traces publicValues
  /-- The verifier's multiplicity bound holds: the instances' count weights times their trace
  heights sum below the characteristic `p` (`heightBoundOk`), so that with multiplicities that
  respect their count weights a balance in the field is one over the integers. -/
  multiplicityBound : heightBoundOk (CompPoly.CanonicalNat.bound F)
    (instances.map fun I ↦ (I.lookups, I.logN)) = true

variable (EF) in
/-- The honest batch run over the extension `EF` avoids three unlikely events in which it
fails. -/
structure NoBadLuck (params : Params) (instances : List (Instance F)) (traces : List (Array F))
    (publicValues : List (List F)) : Prop where
  /-- The out-of-domain point `ζ` (`batchOutOfDomainPoint`), a random element of the extension of
  degree `d`, does not lie in the base field. It does with probability `|F| ^ (1 - d)`; then
  `ζ - x` vanishes for some point `x` of the domains and the openings divide by zero. -/
  outOfDomain : Ext.OutsideBase (batchOutOfDomainPoint EF params instances traces publicValues)
  /-- Under the lookup challenges (`batchLookupChallenges`), no tuple of non-zero multiplicity
  on any row has a zero denominator `α + (b + 1) βᵂ - ∑ⱼ tⱼ βᵏ⁻¹⁻ʲ` (`NoPoleAt`). For a bus `b`
  and a tuple `t`, a uniformly random pair `(α, β)` makes it zero with probability
  `1 / |EF|`. -/
  noPole : ∀ x ∈ instances.zip (traces.zip (publicValues.zip
      (batchLookupChallenges EF params instances traces publicValues))),
    ∀ r < 2 ^ x.1.logN, NoPoleAt x.1.air x.1.lookups x.1.logN x.2.1 x.2.2.1 x.2.2.2 r
  /-- Every proof-of-work search of the honest run finds a witness (`proveBatchTranscript`
  records a failed search, where Plonky3's grinder would panic). A search for `b` bits tries every
  field element, each a witness with probability `2 ^ -b`, so it fails with probability about
  `exp (-|F| / 2 ^ b)`. -/
  grinding : (proveBatchTranscript EF params instances traces publicValues).grindFailed = false

/-- **Batch completeness.** For a valid batch and an honest run over any challenge field `EF`
without bad luck, if every instance's trace satisfies its AIR with its public values, every bus
balances and the multiplicities stay below the characteristic, the honest prover's batch proof
verifies against the batch's common data. -/
theorem completeness {params : Params} {instances : List (Instance F)} {traces : List (Array F)}
    {publicValues : List (List F)} (config : ValidConfig params instances)
    (luck : NoBadLuck EF params instances traces publicValues) :
    Satisfied instances traces publicValues →
      verifyBatch params instances (setupBatch params instances)
        (proveBatch EF params instances traces publicValues) publicValues = .ok () := by
  intro sat
  have hmem : ∀ i (hi : i < instances.length),
      (instances[i], (traces[i]'(sat.tracesLength ▸ hi),
        publicValues[i]'(sat.publicValuesLength ▸ hi))) ∈
        instances.zip (traces.zip publicValues) := fun i hi ↦ by
    have h := List.getElem_mem (l := instances.zip (traces.zip publicValues)) (n := i) (by
      simp only [List.length_zip, sat.tracesLength, sat.publicValuesLength, Nat.min_self]; exact hi)
    simpa only [List.getElem_zip] using h
  obtain ⟨I0, hI0⟩ := List.exists_mem_of_ne_nil _ config.nonempty
  have v0 := config.valid I0 hI0
  have hcl : (batchLookupChallenges EF params instances traces publicValues).length =
      instances.length := by
    rw [batchLookupChallenges_eq, length_bChs]
  refine verifyBatch_proveBatch_of EF params instances traces publicValues config.nonempty
    sat.tracesLength sat.publicValuesLength (fun i hi ↦ ?_)
    (fun i hi ↦ (sat.satisfied _ (hmem i hi)).vanish)
    (fun i hi ↦ ?_) config.chunksFit config.degreeFits config.lookupDegreeFits config.lookupsFit
    config.widths sat.multiplicityBound sat.balanced (fun i hi r hr ↦ ?_) v0.folds v0.queries
    v0.blowup (fun I hI ↦ (config.valid I hI).finalPolyFits) luck.grinding luck.outOfDomain
  · have v := config.valid _ (List.getElem_mem hi)
    exact ⟨(sat.satisfied _ (hmem i hi)).size, v.colsInWidth, v.twoAdic, v.chunksFit,
      v.periodicFits⟩
  · have h := List.getElem_mem (l := instances.zip publicValues) (n := i) (by
      simp only [List.length_zip, sat.publicValuesLength, Nat.min_self]; exact hi)
    simpa only [List.getElem_zip] using sat.publicValueCounts _ h
  · have h := List.getElem_mem (l := instances.zip (traces.zip (publicValues.zip
      (batchLookupChallenges EF params instances traces publicValues)))) (n := i) (by
        simp only [List.length_zip, sat.tracesLength, sat.publicValuesLength, hcl,
          Nat.min_self]; exact hi)
    have := luck.noPole _ h r (by simpa only [List.getElem_zip] using hr)
    simp only [List.getElem_zip] at this
    rwa [getD_of_lt _ _ (by rw [hcl]; exact hi)]

end CompStark.Batch
