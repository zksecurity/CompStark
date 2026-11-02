/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.RandomOracle
public import CompStark.BatchSoundnessError
public import CompStark.Batch.Setup
public import CompStark.Merkle.ExtractMixed

/-! # The batch verifier's random oracles

The batch verifier `verifyBatchWith` runs on the verifier's random oracles
(`CompStark/RandomOracle.lean`): the duplex challenger, the Merkle leaf hash and the compression.

* `Setup.instances`: every instance's AIR, trace length and lookups; `Setup.keyInstances` the
  same at the keygen heights; `Setup.airs` the AIRs the verifier checks; and the same for a
  statement (`Statement.instancesAt`). `Statement.lengthsOf`: the trace lengths a proof claims.
* `Batch.verifierCallsOf`: the verifier's oracle calls on a proof of the instances `instances`: a
  leaf hash and a compression per level of every Merkle opening, and a hash and a compression where
  it injects a shorter domain's matrices. With the common data's computation
  (`Statement.setupQueries`), at most `Statement.verifierQueries` calls on a proof of any lengths.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Stark

variable {F : Type} [BaseField F]

/-- The log sizes of the instances' extended traces, tallest first, each once: the heights of
the verifier's openings. -/
def extHeights (P : Fri.Params) (instances : List (Instance F)) : List ℕ :=
  (List.range ((instances.map (·.logN + P.logBlowup)).foldl max 0 + 1)).reverse.filter fun h ↦
    instances.any (·.logN + P.logBlowup == h)

/-- The committed rounds the verifier opens at every query: the main traces, the quotients, the
preprocessed traces if some instance has them, and the permutation traces if some instance has
lookups. -/
def inputRoundsOf (instances : List (Instance F)) : ℕ :=
  2 + (if instances.any (0 < ·.air.preprocessedWidth) then 1 else 0) +
    if hasLookups instances then 1 else 0

variable (EF : Type) [Challenge F EF] in
/-- The verifier's oracle calls on a proof of the instances `instances`, at most one per sample
(the lookup round's grinding sample and `d` each for `α_L` and `β_L`, with lookups; `α`, `ζ` and
the batching challenge take `d` samples each, the out-of-domain and batching grinding one each,
every fold a grinding sample and `d` for `β`, the query round a grinding sample), and per query
its index and its openings of the committed rounds and every fold: a leaf hash, a compression
per level of the tallest domain, and a hash and a compression where a shorter domain's matrices
are injected. -/
def verifierCallsOf (P : Fri.Params) (instances : List (Instance F)) : ℕ :=
  let hs := extHeights P instances
  let arities := Fri.foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) (hs.headD 0) hs
  (if hasLookups instances then 2 * Challenge.d EF + 1 else 0) + 3 * Challenge.d EF + 3 +
    (Challenge.d EF + 1) * arities.length +
    P.numQueries * (1 + (arities.length + inputRoundsOf instances) *
      (1 + hs.headD 0 + 2 * (hs.length - 1)))

end CompStark.Batch

namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The vectors of `k` lengths up to `t`. -/
def lengthVectors : (k t : ℕ) → List (Fin k → ℕ)
  | 0, _ => [Fin.elim0]
  | k + 1, t => (List.range (t + 1)).flatMap fun n ↦ (lengthVectors k t).map (Fin.cons n)

namespace Setup
variable (S : Setup EF)

/-- The instances: every instance's AIR, trace length and lookups, in order. -/
def instances : List (CompStark.Batch.Instance F) :=
  List.ofFn fun i ↦ ⟨S.air i, S.logN i, S.lookups i⟩

/-- The instances at their keygen heights, of which the common data is computed. -/
def keyInstances : List (CompStark.Batch.Instance F) :=
  List.ofFn fun i ↦ ⟨S.air i, S.keyLogN i, S.lookups i⟩

/-- Some instance has lookups: the batch verifier runs its lookup round. -/
def hasLookups : Bool := CompStark.Batch.hasLookups S.instances

/-- Some instance has preprocessed columns. -/
def hasPreprocessed : Bool := (List.ofFn fun i ↦ (S.air i).preprocessedWidth).any (0 < ·)

/-- FRI's fold arities: Plonky3's schedule from the tallest domain, through the shorter domains'
sizes. -/
def friArities : List ℕ :=
  Fri.foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen) S.logTop
    (S.logTop :: S.friHeights)

/-- The heights of the main commitment's matrices: every instance's extended trace. -/
def mainHeights : List ℕ := List.ofFn fun i ↦ 2 ^ (S.logN i + S.params.logBlowup)

/-- The widths of the main commitment's matrices: every instance's trace. -/
def mainWidths : List ℕ := List.ofFn fun i ↦ (S.air i).width

end Setup

namespace Statement
variable (C : Statement F)

/-- The instances at the trace lengths `2 ^ n i`, with their lookups. -/
def instancesAt (n : Fin C.k → ℕ) : List (CompStark.Batch.Instance F) :=
  List.ofFn fun i ↦ ⟨C.air i, n i, C.lookups i⟩

/-- The instances at their keygen heights, of which the common data is computed. -/
def keyInstances : List (CompStark.Batch.Instance F) := C.instancesAt C.keyLogN

/-- The AIRs the verifier checks, in order. -/
def airs : List (Air F) := List.ofFn C.air

/-- Some instance has lookups: the batch verifier runs its lookup round. -/
def hasLookups : Bool := CompStark.Batch.hasLookups C.keyInstances

/-- Some instance has preprocessed columns. -/
def hasPreprocessed : Bool := (List.ofFn fun i ↦ (C.air i).preprocessedWidth).any (0 < ·)

/-- The oracle calls of the common data's computation: at most four per leaf of the preprocessed
traces' tree, none without preprocessed columns. -/
def setupQueries : Nat :=
  if C.hasPreprocessed then
    4 * 2 ^ CompStark.Batch.preprocessedLogHeight C.params C.keyInstances
  else 0

/-- The trace lengths a proof claims: its degree bits, `0` past their end. -/
def lengthsOf (proof : CompStark.Batch.BatchProof F EF) (i : Fin C.k) : ℕ :=
  proof.degreeBits.toList.getD i 0

variable (EF) in
/-- The verifier's oracle calls on a proof of any trace lengths: at most `verifierCallsOf` at
one of the vectors of lengths up to the two-adicity, none at longer ones, which the verifier
rejects first. -/
def verifierCalls : Nat :=
  ((lengthVectors C.k (twoAdicity F)).map fun n ↦
    CompStark.Batch.verifierCallsOf EF C.params (C.instancesAt n)).foldr max 0

variable (EF) in
/-- The oracle calls of the common data's computation and of the verifier. -/
def verifierQueries : Nat := C.setupQueries + C.verifierCalls EF

end Statement

end CompStark.Iop.Batch
