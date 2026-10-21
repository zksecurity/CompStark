/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Batch.Verifier
public import CompStark.Stark.Prover

/-! # The batch-STARK prover

Plonky3's `batch-stark` `prove_batch` (revision `a4982ec`) without lookups or zero knowledge, on a
backend (`Backend`). For the same instances, traces, public values and parameters it produces
Plonky3's proof, grinding witnesses included when Plonky3 grinds on one thread:

* Commit to the extensions of the instances' preprocessed traces, in instance order, under one
  Merkle tree of mixed heights (`setupBatchWith`, Plonky3's `ProverData::from_airs_and_degrees`).
* Observe the batch's domain separator and every instance's degree bits; commit to every
  instance's trace extension under one tree; observe the commitment, the public values and the
  preprocessed commitment; sample `α`.
* Compute every instance's quotient chunks as `uni-stark` does (`quotientChunks`), commit to all
  of them, instance by instance, under one tree, grind, and sample `ζ`.
* Open every trace at `ζ` and `ζ ω`, every chunk at `ζ`, and every preprocessed trace at `ζ` and,
  if its AIR reads its next row, at `ζ ω`, `ω` the instance's generator, in one opening argument.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {width : Nat}

/-- The extensions by the backend `B` of the instances' preprocessed traces, one per instance
that has preprocessed columns, and their commitment if there is any. -/
def setupBatchWith (B : Backend F EF width) (P : Params) (instances : List (Instance F)) :
    List (Option B.M) × Option B.C :=
  let exts := instances.map fun I ↦
    if I.air.preprocessedWidth = 0 then none
    else some (B.lde I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed)
  let mats := exts.filterMap id
  (exts, if mats.isEmpty then none else some (B.commit mats))

/-- The main traces' extensions and commitment, every instance's quotient chunks and their
commitment, the opening point `ζ` sampled after them, and the out-of-domain grinding witness
before it, by the backend `B`, with the preprocessed traces' extensions and commitment `prep`. -/
def batchCommitAndSample (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (prep : List (Option B.M) × Option B.C) (traces : List (Array F)) (pis : List (List F)) :
    PM F width (List B.M × B.C × List (List B.M) × B.C × EF × F) := do
  pObserveList (batchSeedOf EF P instances ⟨prep.2.map B.root⟩)
  pObserveExts (instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))
  let exts := (instances.zip traces).map fun (I, t) ↦ B.lde I.logN P.logBlowup gen I.air.width t
  let mainC := B.commit exts
  pObserveList (B.root mainC).toList
  pObserveList pis.flatten
  pObserveList ((prep.2.map fun c ↦ (B.root c).toList).getD [])
  let alpha : EF ← pSampleExt
  let chunks := ((instances.zip exts).zip (prep.1.zip pis)).map fun ((I, ext), (pext, p)) ↦
    quotientChunks B P I.air I.logN ext pext p alpha
  let quotC := B.commit chunks.flatten
  pObserveList (B.root quotC).toList
  let ow ← pGrind P.oodPowBits
  let zeta : EF ← pSampleExt
  return (exts, mainC, chunks, quotC, zeta, ow)

/-- Instance `i`'s opened values from the opening argument's values `opened`, by round, matrix
and point: its trace's matrix in the main round, its chunks in the quotient round after the
`chunksBefore` chunks of the instances before it, and its preprocessed trace's matrix in the
preprocessed round after those of the `prepBefore` instances before it with preprocessed
columns. -/
def instanceOpened (A : Air F) (opened : List (List (List (Array EF)))) (i chunks chunksBefore
    prepBefore : Nat) : OpenedValues EF :=
  let trace := (opened.headD []).getD i []
  let prep := (opened.getD 2 []).getD prepBefore []
  ⟨trace.headD #[], trace.getD 1 #[],
    if A.preprocessedWidth = 0 then none else some (prep.headD #[]),
    if A.opensPreprocessedNext then some (prep.getD 1 #[]) else none,
    ((List.range chunks).map fun c ↦ ((opened.getD 1 []).getD (chunksBefore + c) []).headD #[])
      |>.toArray⟩

/-- The openings of every trace at `ζ` and `ζ ω`, every chunk at `ζ` and every preprocessed trace
at its `preprocessedPoints`, and the proof assembled from them and the commitments. -/
def batchOpenAndAssemble (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (prep : List (Option B.M) × Option B.C) :
    List B.M × B.C × List (List B.M) × B.C × EF × F → PM F width (BatchProof F EF)
  | (exts, mainC, chunks, quotC, zeta, ow) => do
    let zetaNext (I : Instance F) := zeta * Ext.ofBase (twoAdicGen I.logN)
    let prepRound := prep.2.map fun pc ↦ (pc, (instances.zip prep.1).filterMap fun (I, pext) ↦
      pext.map fun e ↦ (e, preprocessedPoints I.air zeta (zetaNext I)))
    let (opened, fri) ← openPcs B P
      ([(mainC, (instances.zip exts).map fun (I, e) ↦ (e, [zeta, zetaNext I])),
        (quotC, chunks.flatten.map fun m ↦ (m, [zeta]))] ++ prepRound.toList)
    let counts := chunks.map List.length
    let prepCounts := instances.map fun I ↦ if I.air.preprocessedWidth = 0 then 0 else 1
    return {
      mainCommit := B.root mainC
      quotientCommit := B.root quotC
      opened := (instances.zipIdx.map fun (I, i) ↦ instanceOpened I.air opened i
        (counts.getD i 0) (counts.take i).sum (prepCounts.take i).sum).toArray
      fri
      degreeBits := (instances.map (·.logN)).toArray
      oodWitness := ow }

/-- A batch proof of the instances `instances` for their row-major traces `traces` and public
values `pis`, by the backend `B`. -/
def proveBatchWith (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : BatchProof F EF :=
  let prep := setupBatchWith B P instances
  ((batchCommitAndSample B P instances prep traces pis >>=
    batchOpenAndAssemble B P instances prep).run B.transcript).1

end CompStark.Batch
