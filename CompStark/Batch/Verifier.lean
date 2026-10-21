/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Batch.Proof
public import CompStark.Stark.Verifier

/-! # The batch-STARK verifier

Plonky3's `batch-stark` `verify_batch` (revision `a4982ec`) without lookups or zero knowledge, over
a base field `F` with challenges in the extension `EF`. `verifyBatchWith` runs on any challenger
and Merkle hashes (`Primitives`). Each instance is checked as `uni-stark` checks a proof
(`checkConstraints`, `recompose`), under one transcript and one opening argument:

* The proof's shape is checked first: one opened value set, one list of public values and one
  degree per instance; every instance's degree is its statement's (Plonky3 lets the prover choose
  it); the degrees and quotient domains fit the two-adic subgroups and the periodic columns the
  traces; the public values are as many as each AIR declares; every instance's opened values
  have its AIR's shape; and the preprocessed commitment is present exactly when an instance has
  preprocessed columns.
* The transcript observes the batch's domain separator (`batchSeed`), every instance's degree
  bits, the main commitment, every instance's public values and the preprocessed commitment if
  any, samples the constraint-folding challenge `α`, observes the quotient commitment, checks the
  out-of-domain grinding witness and samples the out-of-domain point `ζ`, which must lie outside
  every instance's trace domain.
* The commitment scheme verifies every instance's trace and preprocessed trace at `ζ` and, if its
  AIR reads their next rows, at `ζ ω`, `ω` the instance's generator, and every quotient chunk at
  `ζ`: one opening argument over matrices of mixed heights (`batchRounds`).
* Every instance's quotient at `ζ`, recomposed from its chunks, must equal its constraints folded
  by `α` and divided by its trace domain's vanishing polynomial.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The opened values have `A`'s shape on `2 ^ logN` rows: the trace's rows of `A`'s width, the
next row exactly when `A` reads it, the quotient's chunks of `d` coordinates each, and the
preprocessed trace's rows of its width exactly when `A` has preprocessed columns, the next row
exactly when `A` reads it. -/
def openedShapeOk (A : Air F) (o : OpenedValues EF) (logN : Nat) : Bool :=
  o.traceLocal.size == A.width && traceNextOk A o &&
    o.quotientChunks.size == 2 ^ A.logQuotientChunks logN &&
    o.quotientChunks.all (·.size == Challenge.d EF) &&
    match o.preprocessedLocal, o.preprocessedNext with
    | none, none => A.preprocessedWidth == 0
    | some l, n =>
      0 < A.preprocessedWidth && l.size == A.preprocessedWidth &&
        match n with
        | some r => A.opensPreprocessedNext && r.size == A.preprocessedWidth
        | none => !A.opensPreprocessedNext
    | none, some _ => false

/-- The commitment scheme's rounds of a proof at `ζ`, on every instance's trace domain: the main
traces' `traceOpenings`, every quotient chunk at `ζ`, instance by instance, and the preprocessed
traces at `ζ` and, if their AIRs read their next rows, at `ζ ω`. -/
def batchRounds (instances : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (zeta : EF) : List (Round F EF) :=
  let insts := instances.zip proof.opened.toList
  let domain (I : Instance F) : Domain F := ⟨1, I.logN⟩
  let zetaNext (I : Instance F) := zeta * Ext.ofBase (twoAdicGen I.logN)
  [(proof.mainCommit, insts.map fun (I, o) ↦
      (domain I, traceOpenings I.air o zeta (zetaNext I))),
    (proof.quotientCommit, insts.flatMap fun (I, o) ↦
      o.quotientChunks.toList.map fun ch ↦ (domain I, [(zeta, ch.toList)]))] ++
    match common.preprocessed with
    | some root => [(root, (insts.filter (0 < ·.1.air.preprocessedWidth)).map fun (I, o) ↦
        (domain I, (zeta, (o.preprocessedLocal.getD #[]).toList) ::
          if I.air.opensPreprocessedNext then [(zetaNext I, (o.preprocessedNext.getD #[]).toList)]
          else []))]
    | none => []

/-- The batch's domain separator (`batchSeed`). -/
def batchSeedOf (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (common : Common F) : List F :=
  DomainSeparator.batchSeed F EF (instances.map (·.air.width))
    (instances.map (·.air.preprocessedWidth)) (instances.map (·.air.numPublicValues))
    common.preprocessed.isSome P.oodPowBits

/-- Instance `I`'s constraint check at `ζ` on its opened values `o` and public values `pis`. -/
def instanceCheck (I : Instance F) (o : OpenedValues EF) (pis : List F) (zeta alpha : EF) : Bool :=
  checkConstraints I.air pis o I.logN zeta alpha
    (recompose (chunkDomains I.logN (I.air.logQuotientChunks I.logN)) o.quotientChunks.toList zeta)

/-- Verify a batch proof of the instances `instances` with the public values `pis`, one list per
instance, on the primitives `H`, against the common data `common`. -/
def verifyBatchWith {m : Type → Type} [Monad m] (H : Primitives F m) (P : Params)
    (instances : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (pis : List (List F)) : m (Except String Unit) := ExceptT.run do
  let n := instances.length
  unless proof.opened.size == n && pis.length == n do
    throw "instance count"
  unless proof.degreeBits.toList == instances.map (·.logN) do
    throw "degree bits"
  unless instances.all fun I ↦ I.logN + I.air.logQuotientChunks I.logN ≤ twoAdicity F do
    throw "quotient domain"
  unless instances.all fun I ↦ I.air.periodicFits I.logN do
    throw "periodic columns"
  unless (instances.zip pis).all fun (I, p) ↦ p.length == I.air.numPublicValues do
    throw "public values"
  unless (instances.zip proof.opened.toList).all fun (I, o) ↦ openedShapeOk I.air o I.logN do
    throw "invalid proof shape"
  unless common.preprocessed.isSome == instances.any (0 < ·.air.preprocessedWidth) do
    throw "preprocessed commitment"
  unless P.oodPowBits != 0 || proof.oodWitness == 0 do
    throw "out-of-domain witness"
  let run : M H (EF × EF) := do
    observeList H (batchSeedOf EF P instances common)
    observeExts H (instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))
    observeList H proof.mainCommit.toList
    observeList H pis.flatten
    observeList H ((common.preprocessed.map (·.toList)).getD [])
    let alpha ← sampleExt H
    observeList H proof.quotientCommit.toList
    ensure (← checkWitness H P.oodPowBits proof.oodWitness) "out-of-domain witness"
    let zeta ← sampleExt H
    ensure (instances.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0)
      "out-of-domain point in a trace domain"
    verifyPcs H P (batchRounds instances common proof zeta) proof.fri
    return (alpha, zeta)
  let ((alpha, zeta), _) ← run.run H.init
  unless (instances.zip (proof.opened.toList.zip pis)).all fun (I, o, p) ↦
      instanceCheck I o p zeta alpha do
    throw "out-of-domain evaluation mismatch"

end CompStark.Batch
