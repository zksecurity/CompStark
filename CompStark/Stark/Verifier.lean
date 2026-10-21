/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Verifier
public import CompStark.Stark.Air

/-! # The STARK verifier

Plonky3's `uni-stark` `verify` (revision `47e442f`) without preprocessed columns or zero
knowledge, over a base field `F` with challenges in the extension `EF` and the two-adic FRI
commitment scheme. `verifyWith` runs on any challenger and Merkle hashes (`Primitives`).

* The proof's shape is checked first: the opened values' sizes, and FRI's fold arities, which must
  be Plonky3's schedule for the degree (`foldArities`). Plonky3 takes the arities from the proof;
  fixing them makes this verifier slightly stricter.

* The transcript observes the degree, the preprocessed width `0`, the trace commitment and the
  public values, samples the constraint-folding challenge `α`, observes the quotient commitment
  and samples the out-of-domain point `ζ`.
* The commitment scheme verifies the trace's openings at `ζ` and `ζ ω` and every quotient chunk's
  at `ζ`.
* The quotient at `ζ` is recomposed from its chunks, which live on the cosets of the quotient
  domain, and must equal the constraints folded by `α` and divided by the trace domain's vanishing
  polynomial.
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

/-- The constraints folded by `α` at `ζ`, Horner style in constraint order. -/
def foldedConstraints (A : Air F) (env : Expr.Env F EF) (alpha : EF) : EF :=
  A.constraints.foldl (fun acc c ↦ acc * alpha + c.eval env) 0

/-- The constraint check at `ζ` on the trace domain of size `2 ^ degreeBits`. -/
def checkConstraints (A : Air F) (pis : List F) (opened : OpenedValues EF) (degreeBits : Nat)
    (zeta alpha quotient : EF) : Bool :=
  let gInv := Ext.ofBase (twoAdicGen degreeBits)⁻¹
  let zh := Ext.powTwo zeta degreeBits - 1
  let env : Expr.Env F EF := {
    cur := fun i ↦ opened.traceLocal.getD i 0
    next := fun i ↦ opened.traceNext.getD i 0
    pub := fun i ↦ Ext.ofBase (pis.getD i 0)
    const := Ext.ofBase
    isFirstRow := zh * (zeta - 1)⁻¹
    isLastRow := zh * (zeta - gInv)⁻¹
    isTransition := zeta - gInv }
  foldedConstraints A env alpha * zh⁻¹ == quotient

/-- Verify a proof of `A` with public values `pis` on the primitives `H`. -/
def verifyWith {m : Type → Type} [Monad m] (H : Primitives F m) (P : Params) (A : Air F)
    (proof : Proof F EF) (pis : List F) : m (Except String Unit) := ExceptT.run do
  let db := proof.degreeBits
  let logChunks := A.logQuotientChunks
  let ds := chunkDomains db logChunks
  let o := proof.opened
  unless o.traceLocal.size == A.width && o.traceNext.size == A.width &&
      o.quotientChunks.size == 2 ^ logChunks &&
      o.quotientChunks.all (·.size == Challenge.d EF) do
    throw "invalid proof shape"
  unless arities proof.fri == foldArities P.maxLogArity (db - P.logFinalPolyLen) do
    throw "fold arities"
  let run : M H (EF × EF) := do
    observe H (db : F)
    observe H (db : F)
    observe H 0
    observeList H proof.traceCommit.toList
    observeList H pis
    let alpha ← sampleExt H
    observeList H proof.quotientCommit.toList
    let zeta ← sampleExt H
    let zetaNext := zeta * Ext.ofBase (twoAdicGen db)
    let traceDomain : Domain F := ⟨1, db⟩
    verifyPcs H P
      [(proof.traceCommit, [(traceDomain, [(zeta, o.traceLocal.toList),
          (zetaNext, o.traceNext.toList)])]),
       (proof.quotientCommit, o.quotientChunks.toList.map fun ch ↦
          (traceDomain, [(zeta, ch.toList)]))]
      proof.fri
    return (alpha, zeta)
  let ((alpha, zeta), _) ← run.run H.init
  let quotient := recompose ds o.quotientChunks.toList zeta
  unless checkConstraints A pis o db zeta alpha quotient do
    throw "out-of-domain evaluation mismatch"

end CompStark.Stark
