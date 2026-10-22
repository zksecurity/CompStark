/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Stark.Verifier

/-! # The STARK prover

Plonky3's `uni-stark` `setup_preprocessed` and `prove_with_preprocessed` (revision `a4982ec`)
without zero knowledge, over a base field `F` with challenges in the extension `EF` and the
two-adic FRI commitment scheme, on a backend (`Backend`). For the same AIR, trace, public values
and parameters it produces Plonky3's proof, grinding witnesses included when Plonky3 grinds on one
thread:

* Commit to the preprocessed trace's low-degree extension, if the AIR has one (`setupWith`).
* Commit to the trace's low-degree extension; observe the STARK's domain separator, the
  commitment, the preprocessed commitment and the public values; sample `α`.
* On the quotient domain `g · ⟨ω_q⟩` of size `|H| · 2 ^ logChunks`, read the traces from their
  extensions and the periodic columns from the extensions of their periods
  (`periodicOnQuotient`), fold the constraints by `α` and divide by `Z_H`. Split the quotient's
  values into chunks on the cosets `g ω_qⁱ · ⟨ω_q^k⟩`, commit to their extensions, grind, and
  sample `ζ`.
* Open the trace and the preprocessed trace at `ζ` and, if the AIR reads their next rows, at
  `ζ ω`, and every chunk at `ζ`.
-/
@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {width : Nat}

/-- The coordinates of every `stride`-th quotient value from `c`, `n` of them: chunk `c`'s values,
as rows of `d` base elements, in parallel row ranges. -/
def chunkValues (qs : @& Array EF) (stride c n : Nat) : Array F :=
  parChunks n (if n < 4096 then 1 else 16) fun r0 len ↦ Id.run do
    let mut out := Array.emptyWithCapacity (Challenge.d EF * len)
    for r in [r0:r0 + len] do
      out := out ++ (Ext.coeffs (qs.getD (r * stride + c) 0)).toArray
    return out

/-- The preprocessed trace's extension and commitment by the backend `B`, if the AIR has
preprocessed columns (Plonky3's `setup_preprocessed`). -/
def setupWith (B : Backend F EF width) (P : Params) (A : Air F) (logN : Nat) :
    Option (B.M × B.C) :=
  if A.preprocessedWidth = 0 then none else
    let ext := B.lde logN P.logBlowup gen A.preprocessedWidth A.preprocessed
    some (ext, B.commit [ext])

/-- The extensions of the chunks of the quotient's values `qs` on the quotient domain of
`2 ^ logChunks` cosets of the trace domain of size `2 ^ logN`: chunk `c` the values on coset `c`,
extended by the backend `B` onto `L`. -/
def chunksOf (B : Backend F EF width) (P : Params) (logN logChunks : Nat) (qs : Array EF) :
    List B.M :=
  let qlog := logN + logChunks
  let stride := 2 ^ logChunks
  (List.range stride).map fun c ↦
    let shift := gen * powF (twoAdicGen qlog) c
    let vals := chunkValues qs stride c (2 ^ logN)
    B.lde logN P.logBlowup (gen * shift⁻¹) (Challenge.d EF) vals

/-- The extensions of the quotient's chunks for `A` on `2 ^ logN` rows (`chunksOf`), from the
extensions `ext` of the trace and `prep` of the preprocessed trace, if any. -/
def quotientChunks (B : Backend F EF width) (P : Params) (A : Air F) (logN : Nat) (ext : B.M)
    (prep : Option B.M) (pis : List F) (alpha : EF) : List B.M :=
  chunksOf B P logN (A.logQuotientChunks logN)
    (B.quotient A pis logN (A.logQuotientChunks logN) ext prep alpha)

/-- The trace's extension and commitment, the quotient's chunks and commitment, the opening point
`ζ` sampled after them, and the out-of-domain grinding witness before it, by the backend `B`, with
the preprocessed trace's extension and commitment `prep`. -/
def commitAndSample (B : Backend F EF width) (P : Params) (A : Air F) (logN : Nat)
    (prep : Option (B.M × B.C)) (trace : Array F) (pis : List F) :
    PM F width (B.M × B.C × List B.M × B.C × EF × F) := do
  let ext := B.lde logN P.logBlowup gen A.width trace
  let traceC := B.commit [ext]
  pObserveList (starkSeedOf EF P A logN)
  pObserveList (B.root traceC).toList
  pObserveList ((prep.map fun x ↦ (B.root x.2).toList).getD [])
  pObserveList pis
  let alpha : EF ← pSampleExt
  let chunks := quotientChunks B P A logN ext (prep.map (·.1)) pis alpha
  let quotC := B.commit chunks
  pObserveList (B.root quotC).toList
  let ow ← pGrind P.oodPowBits
  let zeta : EF ← pSampleExt
  return (ext, traceC, chunks, quotC, zeta, ow)

/-- The points the trace is opened at: `ζ`, and `ζ ω` if the AIR reads its next row. -/
def tracePoints (A : Air F) (zeta zetaNext : EF) : List EF :=
  if A.mainNextRow then [zeta, zetaNext] else [zeta]

/-- The points the preprocessed trace is opened at: `ζ`, and `ζ ω` if the AIR reads its next
row. -/
def preprocessedPoints (A : Air F) (zeta zetaNext : EF) : List EF :=
  if A.opensPreprocessedNext then [zeta, zetaNext] else [zeta]

/-- The openings at the `tracePoints` of the trace, at `ζ` of the quotient's chunks and at the
`preprocessedPoints` of the preprocessed trace, and the proof assembled from them and the
commitments. -/
def openAndAssemble (B : Backend F EF width) (P : Params) (A : Air F) (logN : Nat)
    (prep : Option (B.M × B.C)) :
    B.M × B.C × List B.M × B.C × EF × F → PM F width (Proof F EF)
  | (ext, traceC, chunks, quotC, zeta, ow) => do
    let zetaNext := zeta * Ext.ofBase (twoAdicGen logN)
    let (opened, fri) ← openPcs B P
      ([(traceC, [(ext, tracePoints A zeta zetaNext)]), (quotC, chunks.map fun m ↦ (m, [zeta]))] ++
        (prep.map fun (pext, pc) ↦ (pc, [(pext, preprocessedPoints A zeta zetaNext)])).toList)
    let traceOpened := (opened.headD []).headD []
    let prepOpened := (opened.getD 2 []).headD []
    return {
      traceCommit := B.root traceC
      quotientCommit := B.root quotC
      opened := ⟨traceOpened.headD #[],
        if A.mainNextRow then some (traceOpened.getD 1 #[]) else none,
        prep.map fun _ ↦ prepOpened.headD #[],
        if A.opensPreprocessedNext then some (prepOpened.getD 1 #[]) else none,
        ((opened.getD 1 []).map fun pts ↦ pts.headD #[]).toArray⟩
      fri
      degreeBits := logN
      oodWitness := ow }

/-- A proof of `A` for the row-major trace of `2 ^ logN` rows and public values `pis`, by the
backend `B`. -/
def proveWith (B : Backend F EF width) (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (pis : List F) : Proof F EF :=
  let prep := setupWith B P A logN
  ((commitAndSample B P A logN prep trace pis >>= openAndAssemble B P A logN prep).run
    B.transcript).1

end CompStark.Stark
