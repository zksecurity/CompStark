/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Parse
public import CompStark.Ni.BatchNatural
public import CompStark.Ni.BatchQueryBound

/-! # The batch verifier's observed digests

`prepDigest`: the preprocessed commitment's elements as the batch verifier observes them, none
without one. `friSeedB`: FRI's domain separator on a batch proof for a setup.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type}

variable [BaseField F] {EF : Type} [Challenge F EF]

/-! ### The schedule -/

section Schedule
variable (instances : List (CompStark.Batch.Instance F)) (common : CompStark.Batch.Common F)
  (proof : CompStark.Batch.BatchProof F EF)

end Schedule

/-- The preprocessed commitment's elements, none without one. -/
def prepDigest (common : CompStark.Batch.Common F) : List F :=
  (common.preprocessed.map capElems).getD []

/-- FRI's domain separator on a batch proof for `S`. -/
noncomputable def friSeedB (S : Iop.Batch.Setup EF) : List F :=
  DomainSeparator.friSeed F EF S.friArities (2 ^ S.params.logFinalPolyLen)
    S.params.commitPowBits S.params.queryPowBits S.params.numQueries S.logTop S.params.logBlowup
    S.params.maxLogArity

section Getters
variable (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F) (pis : List (List F))
  (proof : CompStark.Batch.BatchProof F EF)

end Getters

end CompStark.Ni
