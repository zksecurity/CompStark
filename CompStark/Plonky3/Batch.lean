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
specification backend with its out-of-domain point and final transcript, and Plonky3's verifier
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
    else some ((Committed.ofMats (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F) mats).cap
      P.capHeight)⟩

/-- The out-of-domain point `ζ` of the specification's batch proof: the challenge, sampled after
the main and quotient commitments, at which the prover opens every instance's traces and quotient
chunks and the verifier checks every instance's constraints. -/
def batchOutOfDomainPoint (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : EF :=
  ((batchCommitAndSample (specBackend EF) P instances (setupBatchWith (specBackend EF) P instances)
    traces pis).run (specBackend EF).transcript).1.zeta

/-- The lookup challenges of the specification's batch proof: for every instance, its lookups'
denominator bases and combiners laid out from the pair `(α_L, β_L)` the prover samples after the
main and preprocessed commitments (`challengeLayout`). -/
def batchLookupChallenges (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : List (List EF) :=
  ((batchCommitAndSample (specBackend EF) P instances (setupBatchWith (specBackend EF) P instances)
    traces pis).run (specBackend EF).transcript).1.challenges

/-- The specification prover's transcript at the end of `proveBatch`. Its `grindFailed` flag
records whether a grinding search found no witness. -/
def proveBatchTranscript (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : Transcript F 24 :=
  let prep := setupBatchWith (specBackend EF) P instances
  ((batchCommitAndSample (specBackend EF) P instances prep traces pis >>=
    batchOpenAndAssemble (specBackend EF) P instances prep).run (specBackend EF).transcript).2

/-- A batch proof of the instances `instances` for their row-major traces `traces` and public
values `pis`, by the specification backend. -/
def proveBatch (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : BatchProof F EF :=
  proveBatchWith (specBackend EF) P instances traces pis

variable {EF : Type} [Challenge F EF]

/-- Plonky3's batch verifier: `verifyBatchWith` on Poseidon2, against the common data `common`. -/
def verifyBatch (P : Params) (instances : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) : Except String Unit :=
  verifyBatchWith (poseidon2 F) P instances common proof pis

end CompStark.Batch
