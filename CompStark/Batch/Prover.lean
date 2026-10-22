/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Batch.Verifier
public import CompStark.Stark.Prover

/-! # The batch-STARK prover

Plonky3's `batch-stark` `prove_batch` (revision `a4982ec`) without zero knowledge, on a backend
(`Backend`). For the same instances, traces, public values and parameters it produces Plonky3's
proof, grinding witnesses included when Plonky3 grinds on one thread:

* Commit to the extensions of the instances' preprocessed traces, in instance order, under one
  Merkle tree of mixed heights (`setupBatchWith`, Plonky3's `ProverData::from_airs_and_degrees`).
* Observe the batch's domain separator and every instance's degree bits; commit to every
  instance's trace extension under one tree; observe the commitment, the public values and the
  preprocessed commitment.
* With lookups, grind and sample the lookup challenges `(α_L, β_L)`; compute the extension of the
  permutation trace in base coordinates and the terminal of every instance with lookups
  (`Backend.permutation`, `permutationTrace`), commit to the extensions under one tree, and observe
  the commitment and the terminals.
* Sample `α`. Compute every instance's quotient as `uni-stark` does, its LogUp constraints
  following its constraints in Horner's order (`batchQuotientChunks`), commit to all chunks,
  instance by instance, under one tree, grind, and sample `ζ`.
* Open every trace and preprocessed trace at `ζ` and, if its AIR reads their next rows, at `ζ ω`,
  `ω` the instance's generator, every chunk at `ζ`, and every permutation trace at `ζ` and `ζ ω`,
  in one opening argument.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark CompStark.Lookup

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

/-- Instance `I`'s quotient values on its quotient domain from the extensions `ext` of its trace,
`prep` of its preprocessed trace and `perm` of its permutation trace, if any: its constraints'
quotient values (`Backend.quotient`), followed in Horner's order by its LogUp constraints'
(`Backend.lookupQuotient`) over its challenges `chs` and terminal. -/
def batchQuotientValues (B : Backend F EF width) (I : Instance F) (ext : B.M) (prep : Option B.M)
    (perm : Option B.M) (pis : List F) (chs : List EF) (terminal alpha : EF) : Array EF :=
  let qs := B.quotient I.air pis I.logN I.logQuotientChunks ext prep alpha
  match perm with
  | none => qs
  | some pm =>
    let ext' := I.air.lookupConstraints I.logN
    let shift := Ext.pow alpha ext'.length
    Array.zipWith (fun q l ↦ q * shift + l) qs
      (B.lookupQuotient I.air ext' pis I.logN I.logQuotientChunks ext prep pm chs terminal alpha)

/-- The extensions of instance `I`'s quotient chunks (`chunksOf`) of its quotient values
(`batchQuotientValues`). -/
def batchQuotientChunks (B : Backend F EF width) (P : Params) (I : Instance F) (ext : B.M)
    (prep : Option B.M) (perm : Option B.M) (pis : List F) (chs : List EF) (terminal alpha : EF) :
    List B.M :=
  chunksOf B P I.logN I.logQuotientChunks
    (batchQuotientValues B I ext prep perm pis chs terminal alpha)

/-- What the batch prover commits to before `ζ`, on the backend `B`: the main traces' extensions
and commitment, every instance's lookup challenges, the permutation traces' extensions (of the
instances with lookups) and commitment, every instance's terminal, the lookup grinding witness,
every instance's quotient chunks and their commitment, the out-of-domain point `ζ` and its
grinding witness. -/
structure Commitments (B : Backend F EF width) where
  exts : List B.M
  mainC : B.C
  challenges : List (List EF)
  permExts : List (Option B.M)
  permC : Option B.C
  terminals : List (Option EF)
  lookupWitness : Option F
  chunks : List (List B.M)
  quotC : B.C
  zeta : EF
  oodWitness : F

/-- The lookup phase: with lookups, the grinding witness and the sampled pair; without, no witness
and the pair `(0, 0)`. -/
def lookupPair (P : Params) (instances : List (Instance F)) : PM F width (Option F × EF × EF) :=
  if hasLookups instances then do
    let w ← pGrind P.lookupPowBits
    let a : EF ← pSampleExt
    let b : EF ← pSampleExt
    return (some w, a, b)
  else return (none, 0, 0)

/-- The lookup phase: the grinding witness, if any, and the instances' challenges laid out from
the pair (`challengeLayout`). -/
def lookupChallenges (P : Params) (instances : List (Instance F)) :
    PM F width (Option F × List (List EF)) := do
  let (w, a, b) ← lookupPair P instances
  return (w, challengeLayout (instances.map (·.lookups)) a b)

/-- The permutation trace and terminal of every instance with lookups (`permutationTrace`). -/
def permutations (instances : List (Instance F)) (traces : List (Array F)) (pis : List (List F))
    (chs : List (List EF)) : List (Option (Array EF × EF)) :=
  (instances.zip (traces.zip (pis.zip chs))).map fun (I, t, p, c) ↦
    if I.lookups.isEmpty then none else some (permutationTrace I.air I.lookups I.logN t p c)

/-- The extension of the permutation trace in base coordinates and the terminal of every instance
with lookups, by the backend `B` (`Backend.permutation`). -/
def permutationsWith (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) (chs : List (List EF)) :
    List (Option (B.M × EF)) :=
  (instances.zip (traces.zip (pis.zip chs))).map fun (I, t, p, c) ↦
    if I.lookups.isEmpty then none
    else some (B.permutation P.logBlowup I.air I.lookups I.logN t p c)

/-- The extensions of the permutation traces `perms`, and their commitment by the backend `B` if
the batch has lookups. -/
def commitPermutations (B : Backend F EF width) (instances : List (Instance F))
    (perms : List (Option (B.M × EF))) : List (Option B.M) × Option B.C :=
  let permExts := perms.map (·.map (·.1))
  (permExts, if hasLookups instances then some (B.commit (permExts.filterMap id)) else none)

/-- Every instance's quotient chunks (`batchQuotientChunks`) from the extensions of its trace,
preprocessed trace and permutation trace, its public values, challenges and terminal, the
instances in parallel tasks. -/
def allQuotientChunks (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (exts : List B.M) (prepExts permExts : List (Option B.M)) (pis : List (List F))
    (chs : List (List EF)) (terminals : List (Option EF)) (alpha : EF) : List (List B.M) :=
  parMap (fun ((I, ext), (pext, rext), p, c, t) ↦
      batchQuotientChunks B P I ext pext rext p c (t.getD 0) alpha)
    ((instances.zip exts).zip ((prepExts.zip permExts).zip (pis.zip (chs.zip terminals))))

/-- The commitments and the out-of-domain point `ζ` by the backend `B`, with the preprocessed
traces' extensions and commitment `prep`. -/
def batchCommitAndSample (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (prep : List (Option B.M) × Option B.C) (traces : List (Array F)) (pis : List (List F)) :
    PM F width (Commitments B) := do
  pObserveList (batchSeedOf EF P instances ⟨prep.2.map B.root⟩)
  pObserveExts (instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))
  let exts := (instances.zip traces).map fun (I, t) ↦ B.lde I.logN P.logBlowup gen I.air.width t
  let mainC := B.commit exts
  pObserveList (B.root mainC).toList
  pObserveList pis.flatten
  pObserveList ((prep.2.map fun c ↦ (B.root c).toList).getD [])
  let (lw, chs) ← lookupChallenges P instances
  let perms := permutationsWith B P instances traces pis chs
  let (permExts, permC) := commitPermutations B instances perms
  pObserveList ((permC.map fun c ↦ (B.root c).toList).getD [])
  let terminals := perms.map (·.map (·.2))
  pObserveExts (terminals.filterMap id)
  let alpha : EF ← pSampleExt
  let chunks := allQuotientChunks B P instances exts prep.1 permExts pis chs terminals alpha
  let quotC := B.commit chunks.flatten
  pObserveList (B.root quotC).toList
  let ow ← pGrind P.oodPowBits
  let zeta : EF ← pSampleExt
  return ⟨exts, mainC, chs, permExts, permC, terminals, lw, chunks, quotC, zeta, ow⟩

/-- Instance `i`'s opened values from the opening argument's values `opened`, by round, matrix
and point: its trace's matrix in the main round, its chunks in the quotient round after the
`chunksBefore` chunks of the instances before it, and its preprocessed trace's matrix in the
preprocessed round after those of the `prepBefore` instances before it with preprocessed
columns. -/
def instanceOpened (A : Air F) (opened : List (List (List (Array EF)))) (i chunks chunksBefore
    prepBefore : Nat) : OpenedValues EF :=
  let trace := (opened.headD []).getD i []
  let prep := (opened.getD 2 []).getD prepBefore []
  ⟨trace.headD #[], if A.mainNextRow then some (trace.getD 1 #[]) else none,
    if A.preprocessedWidth = 0 then none else some (prep.headD #[]),
    if A.opensPreprocessedNext then some (prep.getD 1 #[]) else none,
    ((List.range chunks).map fun c ↦ ((opened.getD 1 []).getD (chunksBefore + c) []).headD #[])
      |>.toArray⟩

/-- The openings of every trace at its `tracePoints`, every chunk at `ζ`, every preprocessed
trace at its `preprocessedPoints` and every permutation trace at `ζ` and `ζ ω`, and the proof
assembled from them and the commitments. -/
def batchOpenAndAssemble (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (prep : List (Option B.M) × Option B.C) (c : Commitments B) : PM F width (BatchProof F EF) := do
  let zeta := c.zeta
  let zetaNext (I : Instance F) := zeta * Ext.ofBase (twoAdicGen I.logN)
  let prepRound := prep.2.map fun pc ↦ (pc, (instances.zip prep.1).filterMap fun (I, pext) ↦
    pext.map fun e ↦ (e, preprocessedPoints I.air zeta (zetaNext I)))
  let permRound := c.permC.map fun pc ↦ (pc, (instances.zip c.permExts).filterMap fun (I, r) ↦
    r.map fun e ↦ (e, [zeta, zetaNext I]))
  let (opened, fri) ← openPcs B P
    ([(c.mainC, (instances.zip c.exts).map fun (I, e) ↦ (e, tracePoints I.air zeta (zetaNext I))),
      (c.quotC, c.chunks.flatten.map fun m ↦ (m, [zeta]))] ++ prepRound.toList ++
      permRound.toList)
  let counts := c.chunks.map List.length
  let prepCounts := instances.map fun I ↦ if I.air.preprocessedWidth = 0 then 0 else 1
  let permCounts := instances.map fun I ↦ if I.lookups.isEmpty then 0 else 1
  let permOpened := (opened.getD (if prep.2.isSome then 3 else 2) [])
  let permAt (i : Nat) (k : Nat) : Array EF :=
    if (permCounts.getD i 0) = 0 then #[]
    else (permOpened.getD (permCounts.take i).sum []).getD k #[]
  return {
    mainCommit := B.root c.mainC
    permutationCommit := c.permC.map B.root
    quotientCommit := B.root c.quotC
    opened := (instances.zipIdx.map fun (I, i) ↦ instanceOpened I.air opened i
      (counts.getD i 0) (counts.take i).sum (prepCounts.take i).sum).toArray
    permutationLocal := ((List.range instances.length).map (permAt · 0)).toArray
    permutationNext := ((List.range instances.length).map (permAt · 1)).toArray
    fri
    lookupTerminals := c.terminals.toArray
    degreeBits := (instances.map (·.logN)).toArray
    lookupWitness := c.lookupWitness
    oodWitness := c.oodWitness }

/-- A batch proof of the instances `instances` for their row-major traces `traces` and public
values `pis`, by the backend `B`. -/
def proveBatchWith (B : Backend F EF width) (P : Params) (instances : List (Instance F))
    (traces : List (Array F)) (pis : List (List F)) : BatchProof F EF :=
  let prep := setupBatchWith B P instances
  ((batchCommitAndSample B P instances prep traces pis >>=
    batchOpenAndAssemble B P instances prep).run B.transcript).1

end CompStark.Batch
