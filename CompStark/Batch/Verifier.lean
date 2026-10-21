/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Batch.Proof
public import CompStark.Stark.Verifier

/-! # The batch-STARK verifier

Plonky3's `batch-stark` `verify_batch` (revision `a4982ec`) without zero knowledge, over a base
field `F` with challenges in the extension `EF`. `verifyBatchWith` runs on any challenger and
Merkle hashes (`Primitives`). Each instance is checked as `uni-stark` checks a proof, its
constraints followed by its lookups' LogUp constraints (`CompStark/Lookup/`), under one
transcript and one opening argument:

* The proof's shape is checked first: one opened value set, one list of public values, one
  permutation opening and one lookup terminal per instance; every instance's degree is its
  statement's (Plonky3 lets the prover choose it); the degrees and quotient domains fit the
  two-adic subgroups and the periodic columns the traces; the lookups' tuples have one width per
  lookup and per bus, and their multiplicities cannot wrap around the characteristic; the public
  values are as many as each AIR declares; every instance's opened values have its AIR's shape,
  with a permutation row and a terminal exactly when it has lookups; the preprocessed commitment
  is present exactly when an instance has preprocessed columns, the permutation commitment and
  the lookup grinding witness exactly when one has lookups.
* The transcript observes the batch's domain separator (`batchSeed`), every instance's degree
  bits, the main commitment, every instance's public values and the preprocessed commitment if
  any. With lookups, it checks the lookup grinding witness, samples the lookup challenges
  `(α_L, β_L)`, and observes the permutation commitment and the terminals. It samples the
  constraint-folding challenge `α`, observes the quotient commitment, checks the out-of-domain
  grinding witness and samples the out-of-domain point `ζ`, which must lie outside every
  instance's trace domain.
* The commitment scheme verifies every instance's trace and preprocessed trace at `ζ` and, if its
  AIR reads their next rows, at `ζ ω`, `ω` the instance's generator, every quotient chunk at `ζ`,
  and every permutation trace at `ζ` and `ζ ω`: one opening argument over matrices of mixed
  heights (`batchRounds`).
* Every instance's quotient at `ζ`, recomposed from its chunks, must equal its constraints and
  LogUp constraints folded by `α` and divided by its trace domain's vanishing polynomial, the
  LogUp constraints over its lookups' challenges (`challengeLayout`). The terminals must sum to
  zero.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark CompStark.Lookup

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The opened values have the shape of instance `I`: the trace's rows of its AIR's width, the
next row exactly when the AIR reads it, the quotient's chunks of `d` coordinates each, and the
preprocessed trace's rows of its width exactly when the AIR has preprocessed columns, the next row
exactly when the AIR reads it. -/
def openedShapeOk (I : Instance F) (o : OpenedValues EF) : Bool :=
  let A := I.air
  o.traceLocal.size == A.width && traceNextOk A o &&
    o.quotientChunks.size == 2 ^ I.logQuotientChunks &&
    o.quotientChunks.all (·.size == Challenge.d EF) &&
    match o.preprocessedLocal, o.preprocessedNext with
    | none, none => A.preprocessedWidth == 0
    | some l, n =>
      0 < A.preprocessedWidth && l.size == A.preprocessedWidth &&
        match n with
        | some r => A.opensPreprocessedNext && r.size == A.preprocessedWidth
        | none => !A.opensPreprocessedNext
    | none, some _ => false

/-- The permutation openings and terminal have the shape of instance `I`: without lookups, empty
rows and no terminal; with `k` lookups, rows of the accumulator and `k` fraction columns in base
coordinates, and a terminal. -/
def permutationShapeOk (I : Instance F) (cur next : Array EF) (terminal : Option EF) : Bool :=
  let w := if I.lookups.isEmpty then 0 else (I.lookups.length + 1) * Challenge.d EF
  cur.size == w && next.size == w && terminal.isSome == !I.lookups.isEmpty

/-- The commitment scheme's rounds of a proof at `ζ`, on every instance's trace domain: the main
traces' `traceOpenings`, every quotient chunk at `ζ`, instance by instance, the preprocessed
traces at `ζ` and, if their AIRs read their next rows, at `ζ ω`, and the permutation traces of the
instances with lookups at `ζ` and `ζ ω`. -/
def batchRounds (instances : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (zeta : EF) : List (Round F EF) :=
  let insts := instances.zip proof.opened.toList
  let domain (I : Instance F) : Domain F := ⟨1, I.logN⟩
  let zetaNext (I : Instance F) := zeta * Ext.ofBase (twoAdicGen I.logN)
  [(proof.mainCommit, insts.map fun (I, o) ↦
      (domain I, traceOpenings I.air o zeta (zetaNext I))),
    (proof.quotientCommit, insts.flatMap fun (I, o) ↦
      o.quotientChunks.toList.map fun ch ↦ (domain I, [(zeta, ch.toList)]))] ++
    (match common.preprocessed with
    | some root => [(root, (insts.filter (0 < ·.1.air.preprocessedWidth)).map fun (I, o) ↦
        (domain I, (zeta, (o.preprocessedLocal.getD #[]).toList) ::
          if I.air.opensPreprocessedNext then [(zetaNext I, (o.preprocessedNext.getD #[]).toList)]
          else []))]
    | none => []) ++
    match proof.permutationCommit with
    | some root => [(root, ((instances.zip (proof.permutationLocal.toList.zip
        proof.permutationNext.toList)).filter (!·.1.lookups.isEmpty)).map fun (I, l, n) ↦
          (domain I, [(zeta, l.toList), (zetaNext I, n.toList)]))]
    | none => []

/-- The batch's domain separator (`batchSeed`). -/
def batchSeedOf (EF : Type) [Challenge F EF] (P : Params) (instances : List (Instance F))
    (common : Common F) : List F :=
  DomainSeparator.batchSeed F EF (instances.map (·.air.width))
    (instances.map (·.air.preprocessedWidth)) (instances.map (·.air.numPublicValues))
    common.preprocessed.isSome (instances.countP (!·.lookups.isEmpty)) P.lookupPowBits
    P.oodPowBits

/-- Instance `I`'s constraint check at `ζ` on its opened values `o` and public values `pis`, its
LogUp constraints over its permutation trace's rows `cur` and `next`, its challenges `chs` and
its terminal: its constraints and then its LogUp constraints folded by `α`, divided by the
vanishing polynomial, equal the quotient recomposed from its chunks. -/
def instanceCheck (I : Instance F) (o : OpenedValues EF) (pis : List F) (cur next : Array EF)
    (chs : List EF) (terminal : EF) (zeta alpha : EF) : Bool :=
  let env := outOfDomainEnv I.air pis o I.logN zeta
  let aux : ExtExpr.Env EF := ⟨unflattenAt cur, unflattenAt next, (chs.getD · 0), terminal⟩
  (I.air.lookupConstraints I.logN).foldl (fun acc c ↦ acc * alpha + c.eval env aux)
      (foldedConstraints I.air env alpha) * (Ext.powTwo zeta I.logN - 1)⁻¹ ==
    recompose (chunkDomains I.logN I.logQuotientChunks) o.quotientChunks.toList zeta

/-- The lookup checks before the transcript: the lookups' widths, the multiplicity bound, every
instance's permutation openings and terminal, the permutation commitment, and the lookup grinding
witness, present exactly with lookups and `0` at zero difficulty. -/
def lookupShapeOk (P : Params) (instances : List (Instance F)) (proof : BatchProof F EF) :
    Bool :=
  widthsOk (instances.flatMap (·.lookups)) &&
    heightBoundOk (CompPoly.CanonicalNat.bound F) (instances.map fun I ↦ (I.lookups, I.logN)) &&
    (instances.zip (proof.permutationLocal.toList.zip (proof.permutationNext.toList.zip
      proof.lookupTerminals.toList))).all (fun (I, l, n, t) ↦ permutationShapeOk I l n t) &&
    proof.permutationCommit.isSome == hasLookups instances &&
    match proof.lookupWitness with
    | some w => hasLookups instances && (P.lookupPowBits != 0 || w == 0)
    | none => !hasLookups instances

/-- The lookup phase of the transcript: with lookups, check the grinding witness and sample the
lookup challenges `(α_L, β_L)`, then observe the permutation commitment and the terminals. -/
def lookupPhase {m : Type → Type} [Monad m] {H : Primitives F m} (P : Params)
    (instances : List (Instance F)) (proof : BatchProof F EF) : M H (EF × EF) := do
  let pair ← if hasLookups instances then do
      ensure (← checkWitness H P.lookupPowBits (proof.lookupWitness.getD 0)) "lookup witness"
      let a ← sampleExt H
      let b ← sampleExt H
      pure (a, b)
    else pure (0, 0)
  observeList H ((proof.permutationCommit.map (·.toList)).getD [])
  observeExts H (proof.lookupTerminals.toList.filterMap id)
  return pair

/-- Verify a batch proof of the instances `instances` with the public values `pis`, one list per
instance, on the primitives `H`, against the common data `common`. -/
def verifyBatchWith {m : Type → Type} [Monad m] (H : Primitives F m) (P : Params)
    (instances : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (pis : List (List F)) : m (Except String Unit) := ExceptT.run do
  let n := instances.length
  unless proof.opened.size == n && pis.length == n && proof.permutationLocal.size == n &&
      proof.permutationNext.size == n && proof.lookupTerminals.size == n do
    throw "instance count"
  unless proof.degreeBits.toList == instances.map (·.logN) do
    throw "degree bits"
  unless instances.all fun I ↦ I.logN + I.logQuotientChunks ≤ twoAdicity F do
    throw "quotient domain"
  unless instances.all fun I ↦ I.air.periodicFits I.logN do
    throw "periodic columns"
  unless (instances.zip pis).all fun (I, p) ↦ p.length == I.air.numPublicValues do
    throw "public values"
  unless (instances.zip proof.opened.toList).all fun (I, o) ↦ openedShapeOk I o do
    throw "invalid proof shape"
  unless common.preprocessed.isSome == instances.any (0 < ·.air.preprocessedWidth) do
    throw "preprocessed commitment"
  unless lookupShapeOk P instances proof do
    throw "lookups"
  unless P.oodPowBits != 0 || proof.oodWitness == 0 do
    throw "out-of-domain witness"
  let run : M H (EF × EF × EF × EF) := do
    observeList H (batchSeedOf EF P instances common)
    observeExts H (instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))
    observeList H proof.mainCommit.toList
    observeList H pis.flatten
    observeList H ((common.preprocessed.map (·.toList)).getD [])
    let (lookupAlpha, lookupBeta) ← lookupPhase P instances proof
    let alpha ← sampleExt H
    observeList H proof.quotientCommit.toList
    ensure (← checkWitness H P.oodPowBits proof.oodWitness) "out-of-domain witness"
    let zeta ← sampleExt H
    ensure (instances.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0)
      "out-of-domain point in a trace domain"
    verifyPcs H P (batchRounds instances common proof zeta) proof.fri
    return (lookupAlpha, lookupBeta, alpha, zeta)
  let ((lookupAlpha, lookupBeta, alpha, zeta), _) ← run.run H.init
  let chs := challengeLayout (instances.map (·.lookups)) lookupAlpha lookupBeta
  unless (instances.zipIdx.zip (proof.opened.toList.zip pis)).all fun ((I, i), o, p) ↦
      instanceCheck I o p (proof.permutationLocal.getD i #[]) (proof.permutationNext.getD i #[])
        (chs.getD i []) ((proof.lookupTerminals.getD i none).getD 0) zeta alpha do
    throw "out-of-domain evaluation mismatch"
  unless (proof.lookupTerminals.toList.filterMap id).foldl (· + ·) 0 == 0 do
    throw "lookup terminals do not sum to zero"

end CompStark.Batch
