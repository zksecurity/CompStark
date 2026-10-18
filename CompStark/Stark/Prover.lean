/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover
public import CompStark.Stark.Verifier

/-! # The STARK prover

Plonky3's `uni-stark` `prove` (revision `47e442f`) without preprocessed columns or zero knowledge,
over KoalaBear with the two-adic FRI commitment scheme. For the same AIR, trace, public values
and parameters it produces Plonky3's proof, grinding witnesses included when Plonky3 grinds on one
thread:

* Commit to the trace's low-degree extension; observe the degree, the preprocessed width `0`, the
  commitment and the public values; sample `α`.
* On the quotient domain `g · ⟨ω_q⟩` of size `|H| · 2 ^ logChunks`, read the trace from the
  extension, fold the constraints by `α` and divide by `Z_H`. Split the quotient's values into
  chunks on the cosets `g ω_qⁱ · ⟨ω_q^k⟩`, commit to their extensions, and sample `ζ`.
* Open the trace at `ζ` and `ζ ω` and every chunk at `ζ`.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri CompStark.KoalaBear

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- The coordinates of every `stride`-th quotient value from `c`, `n` of them: chunk `c`'s values,
as rows of four base elements. -/
def chunkValues (qs : @& Array EF) (stride c n : Nat) : Array F := Id.run do
  let mut out := Array.emptyWithCapacity (4 * n)
  for r in [0:n] do
    let x := qs.getD (r * stride + c) 0
    out := ((out.push x.c0).push x.c1 |>.push x.c2).push x.c3
  return out

/-- A proof of `A` for the row-major trace of `2 ^ logN` rows and public values `pis`, by the
backend `B`. -/
def proveWith (B : Backend) (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F) :
    Proof :=
  let w := A.width
  let logChunks := A.logQuotientChunks
  let qlog := logN + logChunks
  let ext := B.lde logN P.logBlowup gen w trace
  let traceC := B.commit [ext]
  let run : PM Proof := do
    pObserve (logN : F)
    pObserve (logN : F)
    pObserve 0
    pObserveList (B.root traceC).toList
    pObserveList pis
    let alpha ← pSampleExt
    let qs := B.quotient A pis logN logChunks ext alpha
    let stride := 2 ^ logChunks
    let chunks := (List.range stride).map fun c ↦
      let shift := gen * powF (twoAdicGen qlog) c
      let vals := chunkValues qs stride c (2 ^ logN)
      B.lde logN P.logBlowup (gen * shift⁻¹) 4 vals
    let quotC := B.commit chunks
    pObserveList (B.root quotC).toList
    let zeta ← pSampleExt
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
      degreeBits := logN }
  (run.run B.transcript).1

/-- A proof of `A` for the row-major trace of `2 ^ logN` rows and public values `pis`, by the
specification backend. -/
def prove (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F) : Proof :=
  proveWith Backend.spec P A logN trace pis

end CompStark.Stark
