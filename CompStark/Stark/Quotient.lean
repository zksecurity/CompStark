/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Air
public import CompStark.Stark.Field
public import CompStark.Merkle.Tree

/-! # Quotient values

The constraints of an AIR folded by `α` on the quotient domain and divided by the trace domain's
vanishing polynomial: the quotient the prover splits into chunks and commits.
-/

@[expose] public section
namespace CompStark.Stark

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- A row-major matrix of base elements. -/
structure Mat where
  width : Nat
  height : Nat
  values : Array F

/-- A matrix of field elements. -/
def Mat.ofValues (width height : Nat) (values : Array F) : Mat := { width, height, values }

/-- The matrix as a Merkle tree's matrix of field elements. -/
def Mat.toMatrix (m : Mat) : Merkle.Matrix F := ⟨m.width, m.height, m.values⟩

/-- The values of `e` on the rows `r0, …, r0 + B - 1` of the quotient domain of size `n`, one array
operation per node: `tq` is the trace there, the next row is `period` rows on, and `first`,
`last`, `trans` are the selectors. -/
def evalBlock (tq : Mat) (n period : Nat) (pis : List F) (first last trans : Array F)
    (r0 B : Nat) : Expr → Array F
  | .cur c => Array.ofFn (n := B) fun i ↦ tq.values.getD ((r0 + i.val) * tq.width + c) 0
  | .next c => Array.ofFn (n := B) fun i ↦
      tq.values.getD (((r0 + i.val + period) % n) * tq.width + c) 0
  | .pub j => Array.replicate B (pis.getD j 0)
  | .const c => Array.replicate B c
  | .isFirstRow => first.extract r0 (r0 + B)
  | .isLastRow => last.extract r0 (r0 + B)
  | .isTransition => trans.extract r0 (r0 + B)
  | .add a b => Array.zipWith (· + ·) (evalBlock tq n period pis first last trans r0 B a)
      (evalBlock tq n period pis first last trans r0 B b)
  | .sub a b => Array.zipWith (· - ·) (evalBlock tq n period pis first last trans r0 B a)
      (evalBlock tq n period pis first last trans r0 B b)
  | .mul a b => Array.zipWith (· * ·) (evalBlock tq n period pis first last trans r0 B a)
      (evalBlock tq n period pis first last trans r0 B b)

/-- The constraints of `A`, folded by `α`, on every row of the quotient domain `g · ⟨ω_q⟩` of size
`2 ^ (degreeBits + logChunks)`, divided by the trace domain's vanishing polynomial. `tq` is the
trace on the quotient domain in natural order. `Z_H` has period `2 ^ logChunks` there.

As in Plonky3, constraint `k` of `K` is weighted by `α ^ (K - 1 - k)` (Horner's rule in
constraint order), split into its four base coordinates, so that rows accumulate base-field
products. Rows go in blocks, each node of a constraint one array operation per block. -/
def quotientValues (A : Air) (pis : List F) (degreeBits logChunks : Nat) (tq : Mat) (alpha : EF) :
    Array EF := Id.run do
  let qlog := degreeBits + logChunks
  let n := 2 ^ qlog
  let xs := cosetPoints gen qlog
  let gInv := (twoAdicGen degreeBits)⁻¹
  let period := 2 ^ logChunks
  let zhs := Array.ofFn (n := period) fun k ↦ powF (xs.getD k 0) (2 ^ degreeBits) - 1
  let invZh := batchInv zhs
  let invFirst := batchInv (xs.map (· - 1))
  let invLast := batchInv (xs.map (· - gInv))
  let first := Array.ofFn (n := n) fun i ↦ zhs.getD (i.val % period) 0 * invFirst.getD i 0
  let last := Array.ofFn (n := n) fun i ↦ zhs.getD (i.val % period) 0 * invLast.getD i 0
  let trans := xs.map (· - gInv)
  let K := A.constraints.length
  let weights := (List.range K).map fun k ↦ Ext.coeffs (Ext.pow alpha (K - 1 - k))
  let B := min n 256
  let mut out := Array.emptyWithCapacity n
  for blk in [0:n / B] do
    let r0 := blk * B
    let mut acc := #[Array.replicate B (0 : F), Array.replicate B 0, Array.replicate B 0,
      Array.replicate B 0]
    for (c, wk) in A.constraints.zip weights do
      let v := evalBlock tq n period pis first last trans r0 B c
      acc := (acc.zip wk.toArray).map fun (a, w) ↦ Array.zipWith (fun x y ↦ x + y * w) a v
    for i in [0:B] do
      let z := invZh.getD ((r0 + i) % period) 0
      out := out.push (KoalaBear.Fast.Ext4.smul z
        ⟨acc[0]!.getD i 0, acc[1]!.getD i 0, acc[2]!.getD i 0, acc[3]!.getD i 0⟩)
  return out

end CompStark.Stark
