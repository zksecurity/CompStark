/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Stark.Verifier

/-! # The STARK prover

Plonky3's `uni-stark` `prove` (revision `a4982ec`) without preprocessed columns or zero knowledge,
over a base field `F` with challenges in the extension `EF` and the two-adic FRI commitment scheme,
on a backend (`Backend`). For the same AIR, trace, public values and parameters it produces
Plonky3's proof, grinding witnesses included when Plonky3 grinds on one thread:

* Commit to the trace's low-degree extension; observe the STARK's domain separator, the
  commitment and the public values; sample `α`.
* On the quotient domain `g · ⟨ω_q⟩` of size `|H| · 2 ^ logChunks`, read the trace from the
  extension, fold the constraints by `α` and divide by `Z_H`. Split the quotient's values into
  chunks on the cosets `g ω_qⁱ · ⟨ω_q^k⟩`, commit to their extensions, grind, and sample `ζ`.
* Open the trace at `ζ` and `ζ ω` and every chunk at `ζ`.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {width : Nat}

/-- The coordinates of every `stride`-th quotient value from `c`, `n` of them: chunk `c`'s values,
as rows of `d` base elements. -/
def chunkValues (qs : @& Array EF) (stride c n : Nat) : Array F := Id.run do
  let mut out := Array.emptyWithCapacity (Challenge.d EF * n)
  for r in [0:n] do
    out := out ++ (Ext.coeffs (qs.getD (r * stride + c) 0)).toArray
  return out

/-- The trace's extension and commitment, the quotient's chunks and commitment, the opening point
`ζ` sampled after them, and the out-of-domain grinding witness before it, by the backend `B`. -/
def commitAndSample (B : Backend F EF width) (P : Params) (A : Air F) (logN : Nat)
    (trace : Array F) (pis : List F) : PM F width (B.M × B.C × List B.M × B.C × EF × F) := do
  let logChunks := A.logQuotientChunks
  let qlog := logN + logChunks
  let ext := B.lde logN P.logBlowup gen A.width trace
  let traceC := B.commit [ext]
  pObserveList (DomainSeparator.starkSeed F EF logN A.width A.numPublicValues (2 ^ logChunks)
    P.oodPowBits)
  pObserveList (B.root traceC).toList
  pObserveList pis
  let alpha : EF ← pSampleExt
  let qs := B.quotient A pis logN logChunks ext alpha
  let stride := 2 ^ logChunks
  let chunks := (List.range stride).map fun c ↦
    let shift := gen * powF (twoAdicGen qlog) c
    let vals := chunkValues qs stride c (2 ^ logN)
    B.lde logN P.logBlowup (gen * shift⁻¹) (Challenge.d EF) vals
  let quotC := B.commit chunks
  pObserveList (B.root quotC).toList
  let ow ← pGrind P.oodPowBits
  let zeta : EF ← pSampleExt
  return (ext, traceC, chunks, quotC, zeta, ow)

/-- The openings at `ζ` and `ζ ω` of the trace and at `ζ` of the quotient's chunks, and the proof
assembled from them and the commitments. -/
def openAndAssemble (B : Backend F EF width) (P : Params) (logN : Nat) :
    B.M × B.C × List B.M × B.C × EF × F → PM F width (Proof F EF)
  | (ext, traceC, chunks, quotC, zeta, ow) => do
    let zetaNext := zeta * Ext.ofBase (twoAdicGen logN)
    let (opened, fri) ← openPcs B P
      [(traceC, [(ext, [zeta, zetaNext])]), (quotC, chunks.map fun m ↦ (m, [zeta]))]
    let traceOpened := (opened.headD []).headD []
    return {
      traceCommit := B.root traceC
      quotientCommit := B.root quotC
      opened := ⟨traceOpened.headD #[], traceOpened.getD 1 #[],
        ((opened.getD 1 []).map fun pts ↦ pts.headD #[]).toArray⟩
      fri
      degreeBits := logN
      oodWitness := ow }

/-- A proof of `A` for the row-major trace of `2 ^ logN` rows and public values `pis`, by the
backend `B`. -/
def proveWith (B : Backend F EF width) (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (pis : List F) : Proof F EF :=
  ((commitAndSample B P A logN trace pis >>= openAndAssemble B P logN).run B.transcript).1

end CompStark.Stark
