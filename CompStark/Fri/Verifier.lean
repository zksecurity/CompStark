/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.DomainSeparator
public import CompStark.Primitives
public import CompStark.Merkle.Mmcs
public import CompStark.Stark.Proof
public import CompStark.Stark.Field

/-! # The FRI verifier of the two-adic commitment scheme

Plonky3's `TwoAdicFriPcs::verify` and `verify_fri` (revision `a4982ec`), over a base field `F`
with challenges in the extension `EF`, on the challenger and Merkle hashes of primitives `H`
(`Primitives`):

* The commitment scheme observes its domain separator (`pcsSeed`) and every opened value, checks
  the batching grinding witness and samples the batching challenge `α`.
* FRI folds by Plonky3's schedule for the input heights (`foldSchedule`). It observes its domain
  separator (`friSeed`), and for every commit-phase commitment observes it, checks its grinding
  witness and samples a folding challenge `β`. It observes the final polynomial, checks the
  query grinding witness and samples one index into the largest domain per query.
* The input openings at the queries, verified against their commitments as Merkle
  multi-openings, give each query the batched quotients `∑ αⁱ (pᵢ(z) - pᵢ(x)) / (z - x)` of
  every height. The folds then interpolate each group of `2 ^ arity` values at `β`, adding the
  next height's batched quotient times `β ^ (2 ^ arity)`, and must end at the final
  polynomial's value. Last, every fold's groups are verified as a multi-opening against its
  commitment.
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark

/-- FRI parameters, as Plonky3's `FriParameters`, with the STARK's out-of-domain grinding. -/
structure Params where
  logBlowup : Nat
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitPowBits : Nat
  queryPowBits : Nat
  /-- Grinding before the batching challenge. -/
  batchPowBits : Nat := 0
  /-- Grinding before the STARK's out-of-domain point (`StarkConfig`'s
  `ood_proof_of_work_bits`). -/
  oodPowBits : Nat := 0
  /-- Grinding before the batch STARK's lookup challenges (`StarkConfig`'s
  `lookup_proof_of_work_bits`). -/
  lookupPowBits : Nat := 0

/-- The coset `shift · ⟨ω⟩` with `ω` of order `2 ^ logSize`. -/
structure Domain (F : Type) where
  shift : F
  logSize : Nat

/-- A commitment with, for each committed matrix, its domain and its claimed values at points. -/
abbrev Round (F EF : Type) := Digest F × List (Domain F × List (EF × List EF))

variable {m : Type → Type} [Monad m] {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The verifier's monad on primitives `H`: the challenger's state, failure with a reason, and
the effects of `m`. -/
abbrev M (H : Primitives F m) := StateT H.State (ExceptT String m)

section Challenger
variable (H : Primitives F m)

def observe (x : F) : M H Unit := modify (H.observe · x)
def observeList (xs : List F) : M H Unit := modify (xs.foldl H.observe)
/-- Observe extension elements, lowest coefficient first. -/
def observeExts (xs : List EF) : M H Unit :=
  modify (xs.foldl fun s x ↦ (Ext.coeffs x).foldl H.observe s)
def sample : M H F := fun s ↦ ExceptT.lift (H.sample s)

/-- Sample `n` base elements. -/
def sampleList : Nat → M H (List F)
  | 0 => pure []
  | n + 1 => do
    let a ← sample H
    let r ← sampleList n
    return a :: r

/-- Sample an extension element, lowest coefficient first. -/
def sampleExt : M H EF := do
  return Challenge.ofCoeffs (← sampleList H (Challenge.d EF))

/-- Sample the low `bits` bits of an element's canonical value. -/
def sampleBits (bits : Nat) : M H Nat := do
  return CompPoly.CanonicalNat.toNat (← sample H) % 2 ^ bits

/-- Observe a grinding witness and check that the next `bits` sampled bits are zero. -/
def checkWitness (bits : Nat) (w : F) : M H Bool :=
  if bits = 0 then pure true else do
    observe H w
    return (← sampleBits H bits) == 0

/-- Verify a Merkle multi-opening with the hashes of `H` (`Merkle.verifyMultiM`). -/
def checkMulti (commit : Digest F) (dims : List (Nat × Nat)) (indices : List Nat)
    (rows : List (List (List F))) (siblings : List (Digest F)) : M H Bool :=
  monadLift (Merkle.verifyMultiM H.hash H.compress commit dims indices rows siblings)

end Challenger

/-- Fail with `msg` unless `b`. -/
def ensure {H : Primitives F m} (b : Bool) (msg : String) : M H Unit :=
  if b then pure () else throw msg

/-- Plonky3's fold arities for one input of degree `2 ^ (logFinalPolyLen + remaining)`: fold by
`maxLogArity` bits, by the remaining bits at the end, and by at least one bit. -/
def foldArities (maxLogArity : Nat) : Nat → List Nat
  | 0 => []
  | remaining + 1 =>
    let la := max 1 (min maxLogArity (remaining + 1))
    la :: foldArities maxLogArity (remaining + 1 - la)
  decreasing_by omega

/-- Plonky3's `fold_schedule`: the log arities of the folds of inputs of log heights `heights`,
tallest first, down to `logFinal`. Each round folds by at most `maxLogArity` bits and stops at
the next input's height. -/
def foldSchedule (maxLogArity logFinal : Nat) : Nat → List Nat → List Nat
  | 0, _ | _ + 1, [] => []
  | fuel + 1, h :: rest =>
    if h ≤ logFinal then [] else
      let la := min (min (h - rest.headD logFinal) (h - logFinal)) maxLogArity
      la :: foldSchedule maxLogArity logFinal fuel
        (if rest.head? = some (h - la) then (h - la) :: rest.tail else (h - la) :: rest)

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

/-- Verify the input openings at the queries `indices` into the largest domain, of log size
`logMax`: each batch's rows of every query, as a multi-opening of its matrices' extensions. -/
def verifyInputs (H : Primitives F m) (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF)) : M H Unit := do
  ensure (inputs.length == rounds.length) "input batches"
  for (b, (commit, mats)) in inputs.zip rounds do
    ensure (b.values.size == indices.length) "input queries"
    ensure (b.values.all (·.size == mats.length)) "input rows"
    ensure (mats.all (!·.2.isEmpty)) "matrix without opening points"
    let dims := mats.map fun (d, pts) ↦
      (2 ^ (d.logSize + P.logBlowup), (pts.headD default).2.length)
    let logBatch := (mats.map (·.1.logSize + P.logBlowup)).foldl max 0
    ensure (← checkMulti H commit dims (indices.map (· >>> (logMax - logBatch)))
      (b.values.toList.map fun r ↦ r.toList.map (·.toList)) b.siblings.toList) "input opening"

/-- The batched quotients of the query at `index` from its rows `rows` (per batch, per matrix),
by log height, tallest first. -/
def reduceQuery (H : Primitives F m) (P : Params) (logMax index : Nat) (alpha : EF)
    (rows : List (List (Array F))) (rounds : List (Round F EF)) : M H (List (Nat × EF)) := do
  let mut ro : List (Nat × EF × EF) := []
  for (b, (_, mats)) in rows.zip rounds do
    for (row, (d, pts)) in b.zip mats do
      let logH := d.logSize + P.logBlowup
      let rev := reverseBits (index >>> (logMax - logH)) logH
      let x := gen * powF (twoAdicGen logH) rev
      let (ap, acc) := (ro.lookup logH).getD (1, 0)
      let mut ap := ap
      let mut acc := acc
      for (z, ys) in pts do
        ensure (ys.length == row.size) "opened width"
        ensure (z - Ext.ofBase x != 0) "opening point is the query point"
        let q := (z - Ext.ofBase x)⁻¹
        for (px, pz) in row.toList.zip ys do
          acc := acc + ap * (pz - Ext.ofBase px) * q
          ap := ap * alpha
      ro := (logH, ap, acc) :: ro.filter (·.1 != logH)
  if let some (_, acc) := ro.lookup P.logBlowup then
    ensure (acc == 0) "nonzero quotient at the blowup height"
  return (ro.mergeSort fun a b ↦ b.1 ≤ a.1).map fun (h, _, acc) ↦ (h, acc)

/-- The folds of the query `q` at `index` from its batched quotients `ro`, ending at the final
height: the final value, the folded index, and every fold's group index and group values. -/
def foldQuery (H : Primitives F m) (P : Params) (logMax : Nat) (index q : Nat) (betas : List EF)
    (arities : List Nat) (folds : List (CommitOpening F EF)) (ro : List (Nat × EF)) :
    M H (EF × Nat × List (Nat × List EF)) := do
  let (h0, e0) ← match ro with
    | r :: _ => pure r
    | [] => throw "no reduced openings"
  ensure (h0 == logMax) "reduced opening height"
  let mut ro := ro.tail
  let mut eval := e0
  let mut index := index
  let mut logH := logMax
  let mut groups := []
  for ((beta, la), o) in (betas.zip arities).zip folds do
    let arity := 2 ^ la
    let sibs := o.siblings.getD q #[]
    ensure (sibs.size == arity - 1) "sibling count"
    let pos := index % arity
    let evals := (List.range arity).map fun j ↦
      if j < pos then sibs.getD j 0 else if j = pos then eval else sibs.getD (j - 1) 0
    let logFolded := logH - la
    index := index >>> la
    groups := groups ++ [(index, evals)]
    eval := foldRow index logFolded la beta evals
    logH := logFolded
    match ro with
    | (h, r) :: rest =>
      if h == logFolded then
        eval := eval + Ext.powTwo beta la * r
        ro := rest
    | [] => pure ()
  ensure (logH == P.logBlowup + P.logFinalPolyLen) "final height"
  ensure ro.isEmpty "leftover reduced openings"
  return (eval, index, groups)

/-- Plonky3's `verify_fri`, after the batching challenge `α` was sampled. -/
def verifyFri (H : Primitives F m) (P : Params) (proof : FriProof F EF)
    (rounds : List (Round F EF)) (alpha : EF) : M H Unit := do
  ensure (0 < P.numQueries && 0 < P.logBlowup && 0 < P.maxLogArity) "parameters"
  ensure (rounds.any (!·.2.isEmpty)) "no committed matrices"
  let heights := ((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
    (fun a b ↦ b ≤ a) |>.dedup
  let logMax := heights.headD 0
  ensure (logMax ≤ twoAdicity F) "largest height"
  let logFinal := P.logBlowup + P.logFinalPolyLen
  let arities := foldSchedule P.maxLogArity logFinal logMax heights
  ensure (proof.folds.size == arities.length) "fold openings"
  ensure ((proof.folds.toList.zip arities).all fun (o, la) ↦
    o.siblings.size == P.numQueries && o.siblings.all (·.size == 2 ^ la - 1)) "fold siblings"
  ensure (P.commitPowBits != 0 || proof.commitWitnesses.all (· == 0)) "commit witnesses"
  ensure (P.queryPowBits != 0 || proof.queryWitness == 0) "query witness"
  ensure (proof.finalPoly.size == 2 ^ P.logFinalPolyLen) "final polynomial length"
  observeList H (DomainSeparator.friSeed F EF arities (2 ^ P.logFinalPolyLen) P.commitPowBits
    P.queryPowBits P.numQueries logMax P.logBlowup P.maxLogArity)
  ensure (proof.commits.size == arities.length &&
    proof.commitWitnesses.size == arities.length) "commit rounds"
  let mut betas := #[]
  for (c, w) in proof.commits.toList.zip proof.commitWitnesses.toList do
    observeList H c.toList
    ensure (← checkWitness H P.commitPowBits w) "commit witness"
    betas := betas.push (← sampleExt H : EF)
  observeExts H proof.finalPoly.toList
  ensure (← checkWitness H P.queryPowBits proof.queryWitness) "query witness"
  let indices ← (List.range P.numQueries).mapM fun _ ↦ sampleBits H logMax
  verifyInputs H P logMax indices proof.inputs.toList rounds
  let groups ← indices.zipIdx.mapM fun (index, q) ↦ do
    let ro ← reduceQuery H P logMax index alpha
      (proof.inputs.toList.map fun b ↦ (b.values.getD q #[]).toList) rounds
    let (eval, index, gs) ← foldQuery H P logMax index q betas.toList arities proof.folds.toList ro
    let x := Ext.ofBase (powF (twoAdicGen logMax) (reverseBits index logMax))
    let expected := proof.finalPoly.foldr (fun c acc ↦ acc * x + c) 0
    ensure (expected == eval) "final polynomial mismatch"
    return gs
  let mut logH := logMax
  for ((c, o), (la, i)) in (proof.commits.toList.zip proof.folds.toList).zip arities.zipIdx do
    let logFolded := logH - la
    let gs := groups.map fun g ↦ g.getD i (0, [])
    ensure (← checkMulti H c [(2 ^ logFolded, Challenge.d EF * 2 ^ la)] (gs.map (·.1))
      (gs.map fun (_, evals) ↦ [evals.flatMap Ext.coeffs]) o.path.toList) "commit-phase opening"
    logH := logFolded

/-- The claimed evaluation counts of the rounds: per commitment, per matrix, per point. -/
def claimCounts (rounds : List (Round F EF)) : List (List (List Nat)) :=
  rounds.map fun (_, mats) ↦ mats.map fun (_, pts) ↦ pts.map (·.2.length)

/-- Plonky3's `TwoAdicFriPcs::verify`: observe the domain separator and the opened values, check
the batching grinding, sample `α`, then verify FRI. -/
def verifyPcs (H : Primitives F m) (P : Params) (rounds : List (Round F EF))
    (proof : FriProof F EF) :
    M H Unit := do
  ensure (P.batchPowBits != 0 || proof.batchWitness == 0) "batch witness"
  observeList H (DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits)
  for (_, mats) in rounds do
    for (_, pts) in mats do
      for (_, ys) in pts do
        observeExts H ys
  ensure (← checkWitness H P.batchPowBits proof.batchWitness) "batch witness"
  let alpha ← sampleExt H
  verifyFri H P proof rounds alpha

end CompStark.Fri
