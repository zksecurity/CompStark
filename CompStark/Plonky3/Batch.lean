/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Batch.Prover
public import CompStark.Plonky3.Prover

/-! # Plonky3's batch-STARK

Over a base field with Plonky3's Poseidon2 instances: the common data of a batch (`setupBatch`,
the Poseidon2 Merkle root of its preprocessed traces' extensions), the prover `proveBatch` on the
specification backend with its out-of-domain point (`outOfDomainPoint`), and Plonky3's verifier
`verifyBatch`, `verifyBatchWith` on Poseidon2.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark

variable {F : Type} [BaseField F] [Poseidon2Field F]

/-- The common data of the instances `instances` (Plonky3's `ProverData::from_airs_and_degrees`):
the Poseidon2 Merkle root of the extensions of their preprocessed traces, in instance order, if
any has preprocessed columns. -/
def setupBatch (P : Params) (instances : List (Instance F)) : Common F :=
  let mats := instances.filterMap fun I ↦
    if I.air.preprocessedWidth = 0 then none
    else some (ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed)
  ⟨if mats.isEmpty then none
    else some (Committed.ofMats (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F) mats).root⟩

/-- A batch proof of the instances `instances` for their row-major traces `traces` and public
values `pis`, by the specification backend. -/
def proveBatch (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : BatchProof F EF :=
  proveBatchWith (specBackend EF) P instances traces pis

/-- The out-of-domain point `ζ` of the specification's batch proof. -/
def outOfDomainPoint (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : EF :=
  ((batchCommitAndSample (specBackend EF) P instances (setupBatchWith (specBackend EF) P instances)
    traces pis).run (specBackend EF).transcript).1.2.2.2.2.1

variable {EF : Type} [Challenge F EF]

/-- Plonky3's batch verifier: `verifyBatchWith` on Poseidon2, against the common data `common`. -/
def verifyBatch (P : Params) (instances : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) : Except String Unit :=
  verifyBatchWith (poseidon2 F) P instances common proof pis

end CompStark.Batch
