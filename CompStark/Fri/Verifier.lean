/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Challenger
public import CompStark.Merkle.Mmcs
public import CompStark.Stark.Proof
public import CompStark.Stark.Field

/-! # The FRI verifier of the two-adic commitment scheme

Plonky3's `TwoAdicFriPcs::verify` and `verify_fri` (revision `47e442f`), over KoalaBear:

* The verifier observes every opened value, samples the batching challenge `α`, and for every
  commit-phase commitment observes it, checks its grinding witness and samples a folding
  challenge `β`. It observes the final polynomial and the arity of every fold, and checks the
  query grinding witness.
* Every query samples an index into the largest LDE domain. The input openings at that index,
  verified against their commitments, give the batched quotients `∑ αⁱ (pᵢ(z) - pᵢ(x)) / (z - x)`
  of every height. The folds then interpolate each group of `2 ^ arity` values at `β`, adding
  the next height's batched quotient times `β ^ (2 ^ arity)`, and must end at the final
  polynomial's value.
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark CompStark.KoalaBear

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- FRI parameters, as Plonky3's `FriParameters`. -/
structure Params where
  logBlowup : Nat
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitPowBits : Nat
  queryPowBits : Nat

/-- The coset `shift · ⟨ω⟩` with `ω` of order `2 ^ logSize`. -/
structure Domain where
  shift : F
  logSize : Nat

/-- A commitment with, for each committed matrix, its domain and its claimed values at points. -/
abbrev Round := Digest × List (Domain × List (EF × List EF))

/-- The verifier's monad: a transcript, and failure with a reason. -/
abbrev M := StateT Transcript (Except String)

def observe (x : F) : M Unit := modify (·.observe x)
def observeList (xs : List F) : M Unit := modify (·.observeList xs)
def observeExts (xs : List EF) : M Unit := modify (·.observeExts xs)
def sampleExt : M EF := modifyGet (·.sampleExt)
def sampleBits (bits : Nat) : M Nat := modifyGet (·.sampleBits bits)
def checkWitness (bits : Nat) (w : F) : M Bool := modifyGet (·.checkWitness bits w)

/-- Fail with `msg` unless `b`. -/
def ensure (b : Bool) (msg : String) : M Unit := if b then pure () else throw msg

/-- The value at `z` of the polynomial through `(xᵢ, yᵢ)`. -/
def lagrange (xs : List F) (ys : List EF) (z : EF) : EF :=
  let pts := xs.zip ys
  match pts.find? fun (x, _) ↦ z == Ext.ofBase x with
  | some (_, y) => y
  | none =>
    pts.foldl (fun acc (x, y) ↦
      let w := pts.foldl (fun w (x', _) ↦
        if x' == x then w else w * (z - Ext.ofBase x') * Ext.ofBase (x - x')⁻¹) 1
      acc + y * w) 0

/-- The fold of a group of `2 ^ logArity` values at the folded index `index` of the domain of
size `2 ^ logHeight`: the interpolant through the group's points, in bit-reversed order, at `β`. -/
def foldRow (index logHeight logArity : Nat) (beta : EF) (evals : List EF) : EF :=
  let arity := 2 ^ logArity
  let start := powF (twoAdicGen (logHeight + logArity)) (reverseBits index logHeight)
  let g := twoAdicGen logArity
  let xs := (List.range arity).map fun k ↦ start * powF g (reverseBits k logArity)
  lagrange xs evals beta

/-- The batched quotients of one query at `index`, by log height, tallest first. -/
def openInput (P : Params) (logMax index : Nat) (alpha : EF) (inputs : List BatchOpening)
    (rounds : List Round) : M (List (Nat × EF)) := do
  ensure (inputs.length == rounds.length) "input batches"
  let mut ro : List (Nat × EF × EF) := []
  for (b, (commit, mats)) in inputs.zip rounds do
    let heights := mats.map fun (d, _) ↦ 2 ^ (d.logSize + P.logBlowup)
    let reduced := match heights.max? with
      | some h => index >>> (logMax - Nat.log2 h)
      | none => 0
    ensure (Merkle.KoalaBear.verifyBatch F commit heights reduced (b.values.toList.map (·.toList))
      b.path.toList) "input opening"
    ensure (b.values.size == mats.length) "input rows"
    for (row, (d, pts)) in b.values.toList.zip mats do
      let logH := d.logSize + P.logBlowup
      let rev := reverseBits (index >>> (logMax - logH)) logH
      let x := gen * powF (twoAdicGen logH) rev
      let (ap, acc) := (ro.lookup logH).getD (1, 0)
      let mut ap := ap
      let mut acc := acc
      for (z, ys) in pts do
        ensure (ys.length == row.size) "opened width"
        let q := (z - Ext.ofBase x)⁻¹
        for (px, pz) in row.toList.zip ys do
          acc := acc + ap * (pz - Ext.ofBase px) * q
          ap := ap * alpha
      ro := (logH, ap, acc) :: ro.filter (·.1 != logH)
    if let some (_, acc) := ro.lookup P.logBlowup then
      ensure (acc == 0) "nonzero quotient at the blowup height"
  return (ro.mergeSort fun a b ↦ b.1 ≤ a.1).map fun (h, _, acc) ↦ (h, acc)

/-- The folds of one query from the batched quotients `ro`, ending at the final height. -/
def verifyQuery (P : Params) (logMax : Nat) (index : Nat) (betas : List EF)
    (commits : List Digest) (steps : List CommitStep) (ro : List (Nat × EF)) : M (EF × Nat) := do
  let (h0, e0) ← match ro with
    | r :: _ => pure r
    | [] => throw "no reduced openings"
  ensure (h0 == logMax) "reduced opening height"
  let mut ro := ro.tail
  let mut eval := e0
  let mut index := index
  let mut logH := logMax
  ensure (betas.length == steps.length && commits.length == steps.length) "fold count"
  for ((beta, commit), s) in (betas.zip commits).zip steps do
    let arity := 2 ^ s.logArity
    ensure (s.siblings.size == arity - 1) "sibling count"
    let pos := index % arity
    let evals := (List.range arity).map fun j ↦
      if j < pos then s.siblings.getD j 0 else if j = pos then eval else s.siblings.getD (j - 1) 0
    let logFolded := logH - s.logArity
    index := index >>> s.logArity
    ensure (Merkle.KoalaBear.verifyBatch F commit [2 ^ logFolded] index
      [evals.flatMap Ext.coeffs] s.path.toList) "commit-phase opening"
    eval := foldRow index logFolded s.logArity beta evals
    logH := logFolded
    match ro with
    | (h, r) :: rest =>
      if h == logFolded then
        eval := eval + Ext.powTwo beta s.logArity * r
        ro := rest
    | [] => pure ()
  ensure (logH == P.logBlowup + P.logFinalPolyLen) "final height"
  ensure ro.isEmpty "leftover reduced openings"
  return (eval, index)

/-- Plonky3's `verify_fri`, after the opened values were observed. -/
def verifyFri (P : Params) (proof : FriProof) (rounds : List Round) : M Unit := do
  let alpha ← sampleExt
  let arities := (proof.queries[0]?.map fun q ↦ q.steps.toList.map (·.logArity)).getD []
  ensure (proof.queries.all fun q ↦ q.steps.size == proof.commits.size &&
    q.steps.toList.map (·.logArity) == arities) "fold arities"
  let logMax := arities.sum + P.logBlowup + P.logFinalPolyLen
  ensure (proof.commitWitnesses.size == proof.commits.size) "commit witnesses"
  let mut betas := #[]
  for (c, w) in proof.commits.toList.zip proof.commitWitnesses.toList do
    observeList c.toList
    ensure (← checkWitness P.commitPowBits w) "commit witness"
    betas := betas.push (← sampleExt)
  ensure (proof.finalPoly.size == 2 ^ P.logFinalPolyLen) "final polynomial length"
  observeExts proof.finalPoly.toList
  ensure (proof.queries.size == P.numQueries) "query count"
  for a in arities do observe (a : F)
  ensure (← checkWitness P.queryPowBits proof.queryWitness) "query witness"
  for q in proof.queries do
    let index ← sampleBits logMax
    let ro ← openInput P logMax index alpha q.inputs.toList rounds
    let (eval, index) ←
      verifyQuery P logMax index betas.toList proof.commits.toList q.steps.toList ro
    let x := Ext.ofBase (powF (twoAdicGen logMax) (reverseBits index logMax))
    let expected := proof.finalPoly.foldr (fun c acc ↦ acc * x + c) 0
    ensure (expected == eval) "final polynomial mismatch"

/-- Plonky3's `TwoAdicFriPcs::verify`: observe the opened values, then verify FRI. -/
def verifyPcs (P : Params) (rounds : List Round) (proof : FriProof) : M Unit := do
  for (_, mats) in rounds do
    for (_, pts) in mats do
      for (_, ys) in pts do
        observeExts ys
  verifyFri P proof rounds

end CompStark.Fri
