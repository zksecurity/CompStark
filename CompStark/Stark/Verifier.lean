/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Verifier
public import CompStark.Stark.Air

/-! # The STARK verifier

Plonky3's `uni-stark` `verify_with_preprocessed` (revision `a4982ec`) without zero knowledge, over
a base field `F` with challenges in the extension `EF` and the two-adic FRI commitment scheme.
`verifyWith` runs on any challenger and Merkle hashes (`Primitives`); Plonky3's verifier `verify`
is it on Plonky3's Poseidon2 ones (`poseidon2`). An AIR with preprocessed columns is verified
against the verifying key of its preprocessed trace (`PreprocessedKey`).

* The proof's shape is checked first: the degree and the quotient domain fit the two-adic
  subgroups, the periodic columns fit the trace, the public values are as many as the AIR
  declares, the verifying key is present
  exactly when the AIR has preprocessed columns and matches their width and the trace's height,
  and the opened values' sizes, each next row present exactly when the AIR reads it
  (`traceNextOk`, `preprocessedShapeOk`).
* The transcript observes the STARK's domain separator (`starkSeed`), the trace commitment, the
  preprocessed commitment if any and the public values, samples the constraint-folding challenge
  `α`, observes the quotient commitment, checks the out-of-domain grinding witness and samples
  the out-of-domain point `ζ`, which must lie outside the trace domain.
* The commitment scheme verifies the trace's and the preprocessed trace's openings at `ζ` and, if
  the AIR reads their next rows, at `ζ ω`, and every quotient chunk's at `ζ`.
* The quotient at `ζ` is recomposed from its chunks, which live on the cosets of the quotient
  domain, and must equal the constraints folded by `α` and divided by the trace domain's vanishing
  polynomial. The periodic columns at `ζ` are interpolated from their periods (`periodicAt`).
-/
@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

variable {F : Type} [BaseField F]

/-- The domains of the quotient chunks: the cosets `g · ω^i · ⟨ω^k⟩` of the quotient domain
`g · ⟨ω⟩`, `ω` of order `2 ^ (degreeBits + logChunks)`, `k` the number of chunks. -/
def chunkDomains (degreeBits logChunks : Nat) : List (Domain F) :=
  let w := twoAdicGen (degreeBits + logChunks)
  (List.range (2 ^ logChunks)).map fun i ↦ ⟨gen * powF w i, degreeBits⟩

variable {EF : Type} [Challenge F EF]

/-- `Z_D(p) = (p / s) ^ |D| - 1` for `D = s · ⟨ω⟩`. -/
def vanishingAt (d : Domain F) (p : EF) : EF :=
  Ext.powTwo (p * Ext.ofBase d.shift⁻¹) d.logSize - 1

/-- Plonky3's `recompose_quotient_from_chunks`: the quotient at `ζ` from the chunks' values, each
the `d` base coordinates of a chunk at `ζ`. -/
def recompose (ds : List (Domain F)) (chunks : List (Array EF)) (zeta : EF) : EF :=
  let zps := ds.map fun di ↦ (ds.filter (fun dj ↦ dj.shift != di.shift)).foldl
    (fun acc dj ↦ acc * vanishingAt dj zeta * (vanishingAt dj (Ext.ofBase di.shift))⁻¹) 1
  (zps.zip chunks).foldl (fun acc (zp, ch) ↦
    acc + zp * ((List.range (Challenge.d EF)).foldl (fun s e ↦ s + Ext.basis e * ch.getD e 0) 0)) 0

/-- The value at `ζ` of a periodic column of period `p = 2 ^ k` on a trace of `2 ^ logN` rows:
its period's interpolant on the subgroup of order `p` at `ζ ^ (2 ^ logN / p)`. -/
def periodicAt (col : List F) (logN : Nat) (zeta : EF) : EF :=
  let k := Nat.log2 col.length
  lagrange ((List.range col.length).map fun i ↦ powF (twoAdicGen k) i)
    ((List.range col.length).map fun i ↦ Ext.ofBase (col.getD i 0)) (Ext.powTwo zeta (logN - k))

/-- The constraints folded by `α` at `ζ`, Horner style in constraint order. -/
def foldedConstraints (A : Air F) (env : Expr.Env F EF) (alpha : EF) : EF :=
  A.constraints.foldl (fun acc c ↦ acc * alpha + c.eval env) 0

/-- The constraints' environment at `ζ` on the trace domain of size `2 ^ degreeBits`: the opened
rows, an unopened next row reading as zeros, the periodic columns' values at `ζ`, and the
selectors at `ζ`. -/
def outOfDomainEnv (A : Air F) (pis : List F) (opened : OpenedValues EF) (degreeBits : Nat)
    (zeta : EF) : Expr.Env F EF :=
  let gInv := Ext.ofBase (twoAdicGen degreeBits)⁻¹
  let zh := Ext.powTwo zeta degreeBits - 1
  { cur := fun i ↦ opened.traceLocal.getD i 0
    next := fun i ↦ (opened.traceNext.getD #[]).getD i 0
    prepCur := fun i ↦ (opened.preprocessedLocal.getD #[]).getD i 0
    prepNext := fun i ↦ (opened.preprocessedNext.getD #[]).getD i 0
    periodic := fun i ↦ periodicAt (A.periodicColumn i) degreeBits zeta
    pub := fun i ↦ Ext.ofBase (pis.getD i 0)
    const := Ext.ofBase
    isFirstRow := zh * (zeta - 1)⁻¹
    isLastRow := zh * (zeta - gInv)⁻¹
    isTransition := zeta - gInv }

/-- The constraint check at `ζ` on the trace domain of size `2 ^ degreeBits` (`outOfDomainEnv`). -/
def checkConstraints (A : Air F) (pis : List F) (opened : OpenedValues EF) (degreeBits : Nat)
    (zeta alpha quotient : EF) : Bool :=
  foldedConstraints A (outOfDomainEnv A pis opened degreeBits zeta) alpha *
    (Ext.powTwo zeta degreeBits - 1)⁻¹ == quotient

/-- The proof opens the trace's next row exactly when the AIR reads it, of the AIR's width. -/
def traceNextOk (A : Air F) (o : OpenedValues EF) : Bool :=
  match o.traceNext with
  | some r => A.mainNextRow && r.size == A.width
  | none => !A.mainNextRow

/-- The verifying key matches the AIR's preprocessed trace for `2 ^ degreeBits` rows, and the
proof opens it in the AIR's shape: no key and no opening without preprocessed columns; otherwise
a key of the AIR's width and the trace's height, the current row opened, and the next row opened
exactly when the AIR reads it, every opened row of the AIR's width. -/
def preprocessedShapeOk (A : Air F) (vk : Option (PreprocessedKey F)) (o : OpenedValues EF)
    (degreeBits : Nat) : Bool :=
  match vk, o.preprocessedLocal, o.preprocessedNext with
  | none, none, none => A.preprocessedWidth == 0
  | some k, some l, n =>
    0 < A.preprocessedWidth && k.width == A.preprocessedWidth && k.degreeBits == degreeBits &&
      l.size == A.preprocessedWidth &&
      match n with
      | some r => A.opensPreprocessedNext && r.size == A.preprocessedWidth
      | none => !A.opensPreprocessedNext
  | _, _, _ => false

/-- The elements the transcript observes for the preprocessed commitment: its digest, if any. -/
def preprocessedDigest (vk : Option (PreprocessedKey F)) : List F :=
  match vk with
  | some k => k.commit.toList
  | none => []

/-- The preprocessed trace's round of the commitment scheme, if any: on the trace domain, opened
at `ζ` and, if the AIR reads its next row, at `ζ ω`. -/
def preprocessedRound (A : Air F) (vk : Option (PreprocessedKey F)) (o : OpenedValues EF)
    (traceDomain : Domain F) (zeta zetaNext : EF) : List (Round F EF) :=
  match vk with
  | some k => [(k.commit, [(traceDomain, (zeta, (o.preprocessedLocal.getD #[]).toList) ::
      if A.opensPreprocessedNext then [(zetaNext, (o.preprocessedNext.getD #[]).toList)]
      else [])])]
  | none => []

/-- The trace's points and values: at `ζ`, and at `ζ ω` if the AIR reads its next row. -/
def traceOpenings (A : Air F) (o : OpenedValues EF) (zeta zetaNext : EF) :
    List (EF × List EF) :=
  (zeta, o.traceLocal.toList) ::
    if A.mainNextRow then [(zetaNext, (o.traceNext.getD #[]).toList)] else []

/-- The commitment scheme's rounds of a proof at `ζ`: the trace's `traceOpenings`, every quotient
chunk at `ζ`, and the preprocessed trace (`preprocessedRound`), all on the trace domain. -/
def openingRounds (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (zeta : EF) : List (Round F EF) :=
  let o := proof.opened
  let traceDomain : Domain F := ⟨1, proof.degreeBits⟩
  let zetaNext := zeta * Ext.ofBase (twoAdicGen proof.degreeBits)
  [(proof.traceCommit, [(traceDomain, traceOpenings A o zeta zetaNext)]),
    (proof.quotientCommit, o.quotientChunks.toList.map fun ch ↦
      (traceDomain, [(zeta, ch.toList)]))] ++
    preprocessedRound A vk o traceDomain zeta zetaNext

/-- The STARK's domain separator for a proof of `A` with `2 ^ degreeBits` rows (`starkSeed`). -/
def starkSeedOf (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (degreeBits : Nat) :
    List F :=
  DomainSeparator.starkSeed F EF degreeBits A.width A.preprocessedWidth A.periodic.length
    A.numPublicValues (2 ^ A.logQuotientChunks degreeBits) P.oodPowBits A.mainNextRow
    A.opensPreprocessedNext

/-- Verify a proof of `A` with public values `pis` on the primitives `H`, against the verifying key
`vk` of `A`'s preprocessed trace if it has one. -/
def verifyWith {m : Type → Type} [Monad m] (H : Primitives F m) (P : Params) (A : Air F)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F) :
    m (Except String Unit) := ExceptT.run do
  let db := proof.degreeBits
  let logChunks := A.logQuotientChunks db
  let ds := chunkDomains db logChunks
  let o := proof.opened
  unless db + logChunks ≤ twoAdicity F do
    throw "degree bits"
  unless A.periodicFits db do
    throw "periodic columns"
  unless pis.length == A.numPublicValues do
    throw "public values"
  unless o.traceLocal.size == A.width && traceNextOk A o &&
      o.quotientChunks.size == 2 ^ logChunks &&
      o.quotientChunks.all (·.size == Challenge.d EF) && preprocessedShapeOk A vk o db do
    throw "invalid proof shape"
  unless P.oodPowBits != 0 || proof.oodWitness == 0 do
    throw "out-of-domain witness"
  let run : M H (EF × EF) := do
    observeList H (starkSeedOf EF P A db)
    observeList H proof.traceCommit.toList
    observeList H (preprocessedDigest vk)
    observeList H pis
    let alpha ← sampleExt H
    observeList H proof.quotientCommit.toList
    ensure (← checkWitness H P.oodPowBits proof.oodWitness) "out-of-domain witness"
    let zeta ← sampleExt H
    ensure (Ext.powTwo zeta db - 1 != 0) "out-of-domain point in the trace domain"
    verifyPcs H P (openingRounds A vk proof zeta) proof.fri
    return (alpha, zeta)
  let ((alpha, zeta), _) ← run.run H.init
  let quotient := recompose ds o.quotientChunks.toList zeta
  unless checkConstraints A pis o db zeta alpha quotient do
    throw "out-of-domain evaluation mismatch"

end CompStark.Stark
