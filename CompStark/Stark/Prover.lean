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

/-- The constraints of `A`, folded by `α`, on every row of the quotient domain `g · ⟨ω_q⟩` of size
`2 ^ (degreeBits + logChunks)`, divided by the trace domain's vanishing polynomial. `tq` is the
trace on the quotient domain in natural order. `Z_H` has period `2 ^ logChunks` there. -/
def quotientValues (A : Air) (pis : List F) (degreeBits logChunks : Nat) (tq : Mat) (alpha : EF) :
    Array EF :=
  let qlog := degreeBits + logChunks
  let xs := cosetPoints gen qlog
  let gInv := (twoAdicGen degreeBits)⁻¹
  let period := 2 ^ logChunks
  let zhs := Array.ofFn (n := period) fun k ↦ powF (xs.getD k 0) (2 ^ degreeBits) - 1
  let invZh := batchInv zhs
  let invFirst := batchInv (xs.map (· - 1))
  let invLast := batchInv (xs.map (· - gInv))
  Array.ofFn (n := 2 ^ qlog) fun i ↦
    let zh := zhs.getD (i.val % period) 0
    let env : Expr.Env F := {
      cur := fun j ↦ tq.values.getD (i.val * tq.width + j) 0
      next := fun j ↦ tq.values.getD (((i.val + period) % 2 ^ qlog) * tq.width + j) 0
      pub := fun j ↦ pis.getD j 0
      const := id
      isFirstRow := zh * invFirst.getD i 0
      isLastRow := zh * invLast.getD i 0
      isTransition := xs.getD i 0 - gInv }
    let acc := A.constraints.foldl (fun acc c ↦ acc * alpha + Ext.ofBase (c.eval env)) 0
    acc * Ext.ofBase (invZh.getD (i.val % period) 0)

/-- A proof of `A` for the row-major trace of `2 ^ logN` rows and public values `pis`, by the
backend `B`. -/
def proveWith (B : Backend) (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F) :
    Proof :=
  let w := A.width
  let logChunks := A.logQuotientChunks
  let qlog := logN + logChunks
  let traceC := B.commit [B.lde logN P.logBlowup gen w trace]
  let run : PM Proof := do
    pObserve (logN : F)
    pObserve (logN : F)
    pObserve 0
    pObserveList traceC.root.toList
    pObserveList pis
    let alpha ← pSampleExt
    -- The trace on the quotient domain, from the first rows of its bit-reversed extension.
    let ext := traceC.mats.headD ⟨0, 0, #[]⟩
    let tq : Mat := ⟨w, 2 ^ qlog, Array.ofFn (n := 2 ^ qlog * w) fun k ↦
      ext.values.getD (reverseBits (k.val / w) qlog * w + k.val % w) 0⟩
    let qs := quotientValues A pis logN logChunks tq alpha
    let chunks := (List.range (2 ^ logChunks)).map fun c ↦
      let shift := gen * powF (twoAdicGen qlog) c
      let vals := (List.range (2 ^ logN)).toArray.flatMap fun r ↦
        (Ext.coeffs (qs.getD (r * 2 ^ logChunks + c) 0)).toArray
      B.lde logN P.logBlowup (gen * shift⁻¹) 4 vals
    let quotC := B.commit chunks
    pObserveList quotC.root.toList
    let zeta ← pSampleExt
    let zetaNext := zeta * Ext.ofBase (twoAdicGen logN)
    let (opened, fri) ← openPcs B P
      [(traceC, [[zeta, zetaNext]]), (quotC, chunks.map fun _ ↦ [zeta])]
    let traceOpened := (opened.headD []).headD []
    return {
      traceCommit := traceC.root
      quotientCommit := quotC.root
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
