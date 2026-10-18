/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Verifier
public import CompStark.Stark.Quotient
public import CompPoly.Fields.KoalaBear.InterpolateCoset

/-! # The FRI prover of the two-adic commitment scheme

Plonky3's `TwoAdicFriPcs::commit` and `open`, `prove_fri` (revision `47e442f`), over KoalaBear:

* A committed matrix is the low-degree extension of its columns onto the coset `g · ⟨ω_N⟩`,
  `g = 3`, rows in bit-reversed order, under the Poseidon2 Merkle tree.
* Opening observes every claimed value, samples the batching challenge `α`, and sums, for every
  height, `α^k (p(z) - p(x)) / (z - x)` over the committed columns `p` and their points `z`, at
  every row `x` of the extended domain.
* The commit phase folds the tallest sum by `2 ^ arity` per round, committing the groups as rows
  and adding each shorter sum when its height is reached, down to the final polynomial. Each
  query then opens the inputs and every round's group at a sampled index.
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark CompStark.KoalaBear

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- The low-degree extension by `2 ^ bits` of a `2 ^ logH × w` matrix of values on `⟨ω⟩`, onto
`shift · ⟨ω_N⟩`, rows in bit-reversed order: Plonky3's `coset_lde_batch` then
`bit_reverse_rows`. Row `r` holds every column's interpolant at `shift · ω_N ^ bitrev r`; this
reference interpolates with an inverse transform and evaluates by Horner's rule. -/
def ldeRef (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : Mat :=
  let n : Nat := 2 ^ logH
  let logN := logH + bits
  let wInv := (twoAdicGen logH)⁻¹
  let nInv := ((n : F))⁻¹
  let coeffs := (List.range w).map fun j ↦
    Array.ofFn (n := n) fun k ↦
      nInv * (List.range n).foldl (fun acc i ↦
        acc + m.getD (i * w + j) 0 * powF wInv (i * k.val % n)) 0
  let wN := twoAdicGen logN
  let rows := Array.ofFn (n := 2 ^ logN) fun r ↦
    let y := shift * powF wN (reverseBits r.val logN)
    coeffs.toArray.map fun c ↦ c.foldr (fun a acc ↦ acc * y + a) 0
  Mat.ofValues w (2 ^ logN) rows.flatten

/-- The kernels the prover runs, on the backend's own matrices `M`, commitments `C` and vectors
of extension elements `V`: the transcript, low-degree extension, commitments with their roots,
openings and heights, the quotient values from the trace's extension, the values of a matrix's
columns at points, and the FRI inputs and folds. Every backend computes the same functions
(`Refines`); `spec` runs the specifications. -/
structure Backend where
  transcript : Transcript
  M : Type
  C : Type
  V : Type
  lde : Nat → Nat → F → Nat → Array F → M
  commit : List M → C
  root : C → Digest
  openAt : C → Nat → BatchOpening
  /-- `log₂` of the largest committed height. -/
  logHeight : C → Nat
  quotient : Air → List F → Nat → Nat → M → EF → Array EF
  openedAt : Nat → M → List EF → List (Array EF)
  toArray : V → Array EF
  ofArray : Array EF → V
  size : V → Nat
  /-- The batched quotients by log height, tallest first, of committed matrices with their points
  and opened values, for the batching challenge `α`. -/
  reduce : EF → List (M × List (EF × Array EF)) → List (Nat × V)
  /-- The arity-2 fold at `β` of `2 ^ (logRows + 1)` values. -/
  fold2 : V → EF → Nat → V
  /-- `a + s · b`. -/
  addScaled : V → V → EF → V
  /-- The matrix of rows of `k` elements, flattened to coordinates. -/
  leaves : Nat → V → M

/-- The rows `perm[0], perm[1], …` of `m`, concatenated. -/
def permuteRows (m : Mat) (perm : Array Nat) : Array F := Id.run do
  let mut out := Array.emptyWithCapacity (perm.size * m.width)
  for r in perm do
    for j in [0:m.width] do
      out := out.push (m.values.getD (r * m.width + j) 0)
  return out

/-- A matrix's row `r` as an array. -/
def rowOf (m : Mat) (r : Nat) : Array F := Array.ofFn (n := m.width) fun j ↦
  m.values.getD (r * m.width + j) 0

/-- The extension elements of a flattened row, four coefficients each. -/
def unflatten (xs : List F) : List EF :=
  (List.range (xs.length / 4)).map fun i ↦
    ⟨xs.getD (4 * i) 0, xs.getD (4 * i + 1) 0, xs.getD (4 * i + 2) 0, xs.getD (4 * i + 3) 0⟩

/-- Matrices under one Merkle tree: the specification's commitment, with the digest layers leaves
first. -/
structure Committed where
  mats : List Mat
  layers : Array (Array Digest)

namespace Committed

/-- Commit to matrices. -/
def ofMats (ms : List Mat) : Committed :=
  ⟨ms, ((Merkle.layers (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) (ms.map Mat.toMatrix)).map
    List.toArray).toArray⟩

/-- The Merkle root. -/
def root (c : Committed) : Digest := (c.layers.back?.getD #[]).getD 0 0

/-- The largest matrix height. -/
def maxHeight (c : Committed) : Nat := c.mats.foldl (fun m a ↦ max m a.height) 0

/-- The opening at `index`: every matrix's row, shifted right by the number of layers it is
shorter than the tallest, and the sibling of every layer below the root (`Merkle.openWith`). -/
def openAt (c : Committed) (index : Nat) : BatchOpening :=
  let logMax := Merkle.log2Ceil c.maxHeight
  let rows := c.mats.map fun m ↦ rowOf m (index >>> (logMax - Merkle.log2Ceil m.height))
  ⟨rows.toArray, Array.ofFn (n := logMax) fun i ↦
    (c.layers.getD i.val #[]).getD ((index >>> i.val) ^^^ 1) 0⟩

end Committed

/-- The prover's monad: a transcript. -/
abbrev PM := StateM Transcript

def pObserveList (xs : List F) : PM Unit := modify (·.observeList xs)
def pObserveExts (xs : List EF) : PM Unit := modify (·.observeExts xs)
def pObserve (x : F) : PM Unit := modify (·.observe x)
def pSampleExt : PM EF := modifyGet (·.sampleExt)
def pSampleBits (bits : Nat) : PM Nat := modifyGet (·.sampleBits bits)
def pGrind (bits : Nat) : PM F := modifyGet (·.grind bits)

/-- Plonky3's `compute_log_arity_for_round`. -/
def logArityFor (P : Params) (logCur : Nat) (nextInput : Option Nat) : Nat :=
  let toTarget := logCur - (P.logBlowup + P.logFinalPolyLen)
  let maxFold := match nextInput with
    | some h => min (logCur - h) toTarget
    | none => toTarget
  min maxFold P.maxLogArity

/-- The coefficients of the polynomial of degree below `n` with the values `vs` on the subgroup
of order `n = 2 ^ logN`, natural order. -/
def idft (logN : Nat) (vs : Array EF) : Array EF :=
  let n : Nat := 2 ^ logN
  let wInv := (twoAdicGen logN)⁻¹
  let nInv := Ext.ofBase ((n : F)⁻¹)
  Array.ofFn (n := n) fun k ↦
    nInv * (List.range n).foldl (fun acc j ↦
      acc + Ext.ofBase (powF wInv (j * k.val)) * vs.getD j 0) 0

/-- The result of the commit phase, on commitments `C`. -/
structure CommitPhase (C : Type) where
  commits : Array Digest
  data : Array C
  witnesses : Array F
  arities : Array Nat
  finalPoly : Array EF

/-- Pairs `r0, …, r0 + len - 1` of the arity-2 fold, with one batch inversion of their `2 x`. -/
def foldRange (vs : @& Array EF) (pw : @& Array F) (perm : @& Array Nat) (beta half : EF)
    (r0 len : Nat) : Array EF := Id.run do
  let inv2x := batchInv (Array.ofFn (n := len) fun k ↦ 2 * pw.getD (perm.getD (r0 + k.val) 0) 0)
  let mut out := Array.emptyWithCapacity len
  for k in [0:len] do
    let i := r0 + k
    let lo := vs.getD (2 * i) 0
    let hi := vs.getD (2 * i + 1) 0
    out := out.push ((lo + hi) * half + beta * (lo - hi) * Ext.ofBase (inv2x.getD k 0))
  return out

/-- The arity-2 fold of `2 ^ (logRows + 1)` values at `β`: pair `i`, at the points `±x`, `x` the
`bitrev i`-th power of the generator of order `2 ^ (logRows + 1)`, folds to
`(lo + hi) / 2 + β (lo - hi) / (2 x)`, Plonky3's `fold_matrix`. It is `foldRow` with arity 2. -/
def foldPairs (vs : Array EF) (beta : EF) (logRows : Nat) : Array EF :=
  let rows := 2 ^ logRows
  let pw := cosetPoints 1 (logRows + 1)
  let perm := bitRevPerm logRows
  let half := Ext.ofBase (2 : F)⁻¹
  parChunks rows (if rows < 4096 then 1 else 16) fun r0 len ↦ foldRange vs pw perm beta half r0 len

/-- The rounds of Plonky3's `commit_phase`, at most `fuel` of them: while the folded vector is
above the final height, commit to its groups, fold them at a fresh `β`, and add the next input of
the folded height times `β ^ (2 ^ arity)`. -/
def commitRounds (B : Backend) (P : Params) :
    Nat → B.V → List B.V → CommitPhase B.C → PM (B.V × CommitPhase B.C)
  | 0, folded, _, cp => pure (folded, cp)
  | fuel + 1, folded, rest, cp => do
    if B.size folded ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen) then return (folded, cp)
    let logCur := Nat.log2 (B.size folded)
    let la := logArityFor P logCur (rest.head?.map (Nat.log2 <| B.size ·))
    let arity := 2 ^ la
    let rows := B.size folded / arity
    let c := B.commit [B.leaves arity folded]
    pObserveList (B.root c).toList
    let w ← pGrind P.commitPowBits
    let beta ← pSampleExt
    let logRows := Nat.log2 rows
    let folded := if la = 1 then B.fold2 folded beta logRows else
      let vs := B.toArray folded
      B.ofArray <| Array.ofFn (n := rows) fun i ↦
        foldRow i logRows la beta ((List.range arity).map fun k ↦ vs.getD (i * arity + k) 0)
    let (folded, rest) := match rest with
      | v :: vs => if B.size v == B.size folded then
          (B.addScaled folded v (Ext.powTwo beta la), vs) else (folded, rest)
      | [] => (folded, [])
    commitRounds B P fuel folded rest
      ⟨cp.commits.push (B.root c), cp.data.push c, cp.witnesses.push w, cp.arities.push la,
        cp.finalPoly⟩

/-- Plonky3's `commit_phase` on the batched quotients `inputs`, tallest first. -/
def commitPhase (B : Backend) (P : Params) (inputs : List B.V) : PM (CommitPhase B.C) := do
  let (folded, rest) := match inputs with
    | v :: vs => (v, vs)
    | [] => (B.ofArray #[], [])
  let (folded, cp) ← commitRounds B P (B.size folded) folded rest ⟨#[], #[], #[], #[], #[]⟩
  let fa := B.toArray folded
  let len := 2 ^ P.logFinalPolyLen
  let truncated := Array.ofFn (n := len) fun i ↦ fa.getD (reverseBits i P.logFinalPolyLen) 0
  let finalPoly := idft P.logFinalPolyLen truncated
  pObserveExts finalPoly.toList
  return { cp with finalPoly := finalPoly }

/-- The commit-phase openings of a query at `index`. -/
def answerQuery (B : Backend) (cp : CommitPhase B.C) (index : Nat) : Array CommitStep := Id.run do
  let mut cur := index
  let mut steps := #[]
  for (c, la) in cp.data.toList.zip cp.arities.toList do
    let arity := 2 ^ la
    let pos := cur % arity
    let group := cur >>> la
    let o := B.openAt c group
    let evals := unflatten ((o.values.getD 0 #[]).toList)
    let siblings := ((List.range arity).filter (· != pos)).map fun j ↦ evals.getD j 0
    steps := steps.push ⟨la, siblings.toArray, o.path⟩
    cur := group
  return steps

/-- `factor · ∑ᵢ weights[i] · m[perm[i]][j]` for the columns `j0, …, j0 + nj - 1` of the row-major
matrix `m` of width `w`: the barycentric evaluation of columns whose natural-order row `i` is
stored at row `perm[i]`. -/
def weightedColumns (m : @& Array F) (perm : @& Array Nat) (weights : @& Array EF)
    (w h j0 nj : Nat) (factor : EF) : Array EF := Id.run do
  let mut out := Array.emptyWithCapacity nj
  for j in [j0:j0 + nj] do
    let mut acc : EF := 0
    for i in [0:h] do
      acc := acc + KoalaBear.Fast.Ext4.smul (m.getD (perm.getD i 0 * w + j) 0) (weights.getD i 0)
    out := out.push (factor * acc)
  return out

/-- Rows `r0, …, r0 + len - 1` of `m` (width `w`), each batched by the powers `ap` of `α`. -/
def compressRows (m : @& Array F) (ap : @& Array EF) (w r0 len : Nat) : Array EF := Id.run do
  let mut out := Array.emptyWithCapacity len
  for r in [r0:r0 + len] do
    let mut acc : EF := 0
    for i in [0:w] do
      acc := acc + KoalaBear.Fast.Ext4.smul (m.getD (r * w + i) 0) (ap.getD i 0)
    out := out.push acc
  return out

/-- Rows `r0, …, r0 + len - 1` of the batched quotient: `acc + offset (yz - comp) / (z - x)`. -/
def accumulateRows (acc comp : @& Array EF) (xs : @& Array F) (z yz offset : EF)
    (r0 len : Nat) : Array EF := Id.run do
  let invs := batchInv ((xs.extract r0 (r0 + len)).map fun x ↦ z - Ext.ofBase x)
  let mut out := Array.emptyWithCapacity len
  for k in [0:len] do
    let r := r0 + k
    out := out.push (acc.getD r 0 + offset * (yz - comp.getD r 0) * invs.getD k 0)
  return out

/-- The values of a committed matrix's columns at `z`: the polynomials of degree below
`height / 2 ^ logBlowup` through its low coset rows. -/
def openedAt (logBlowup : Nat) (m : Mat) (z : EF) : Array EF :=
  let logH := Nat.log2 m.height - logBlowup
  let h := 2 ^ logH
  -- Barycentric weights `xᵢ / (z - xᵢ)` of the natural-order coset, and the scale.
  let xs := cosetPoints gen logH
  let invs := batchInv (xs.map fun x ↦ z - Ext.ofBase x)
  let weights := Array.zipWith KoalaBear.Fast.Ext4.smul xs invs
  let factor := KoalaBear.Fast.cosetFactor logH gen z
  let perm := bitRevPerm logH
  parChunks m.width (min m.width 16) fun j0 nj ↦
    weightedColumns m.values perm weights m.width h j0 nj factor

/-- Rows batched by the powers `ap` of `α`, in parallel row ranges. -/
def compress (m : Mat) (ap : Array EF) : Array EF :=
  parChunks m.height (if m.height < 4096 then 1 else 16) fun r0 len ↦
    compressRows m.values ap m.width r0 len

/-- The quotient values from the trace's extension `ext`: its first `2 ^ (degreeBits + logChunks)`
rows in natural order are the trace on the quotient domain. -/
def quotientOfLde (A : Air) (pis : List F) (degreeBits logChunks : Nat) (ext : Mat) (alpha : EF) :
    Array EF :=
  let qlog := degreeBits + logChunks
  let tq := Mat.ofValues ext.width (2 ^ qlog) (permuteRows ext (bitRevPerm qlog))
  quotientValues A pis degreeBits logChunks tq alpha

/-- The batched quotients `∑ αᵏ (p(z) - p(x)) / (z - x)` by log height, tallest first: each
matrix's rows batched by the powers of `α` once, then every point accumulated over the rows with
the running power of `α` of its height. -/
def reduce (alpha : EF) (items : List (Mat × List (EF × Array EF))) : List (Nat × Array EF) :=
  Id.run do
  let mut red : List (Nat × Nat × Array EF) := []
  for (m, pts) in items do
    let logH := Nat.log2 m.height
    let (cnt, acc) := (red.lookup logH).getD (0, Array.replicate m.height 0)
    let mut cnt := cnt
    let mut acc := acc
    let ap := Array.ofFn (n := m.width) fun i ↦ Ext.pow alpha i.val
    let parts := if m.height < 4096 then 1 else 16
    let comp := compress m ap
    let xs := cosetPointsBitRev gen logH
    for (z, ys) in pts do
      let offset := Ext.pow alpha cnt
      let yz := (List.range m.width).foldl (fun s i ↦ s + ap.getD i 0 * ys.getD i 0) 0
      let prev := acc
      acc := parChunks m.height parts fun r0 len ↦ accumulateRows prev comp xs z yz offset r0 len
      cnt := cnt + m.width
    red := (logH, cnt, acc) :: red.filter (·.1 != logH)
  return (red.mergeSort fun a b ↦ b.1 ≤ a.1).map fun (h, _, acc) ↦ (h, acc)

/-- The specification backend. -/
def Backend.spec : Backend where
  transcript := Transcript.init
  M := Mat
  C := Committed
  V := Array EF
  lde := ldeRef
  commit := Committed.ofMats
  root := Committed.root
  openAt := Committed.openAt
  logHeight c := Nat.log2 c.maxHeight
  quotient := quotientOfLde
  openedAt b m zs := zs.map (Fri.openedAt b m)
  toArray := id
  ofArray := id
  size := Array.size
  reduce := Fri.reduce
  fold2 := foldPairs
  addScaled a b x := Array.zipWith (fun u v ↦ u + x * v) a b
  leaves k vs := Mat.ofValues (4 * k) (vs.size / k) (vs.flatMap fun x ↦ (Ext.coeffs x).toArray)

/-- A committed batch with each of its matrices and the points at which it is opened. -/
abbrev OpenRound (B : Backend) := B.C × List (B.M × List EF)

/-- Plonky3's `TwoAdicFriPcs::open`: the opened values, by round, matrix and point, and the FRI
proof. -/
def openPcs (B : Backend) (P : Params) (rounds : List (OpenRound B)) :
    PM (List (List (List (Array EF))) × FriProof) := do
  let opened ← rounds.mapM fun (_, ms) ↦ ms.mapM fun (m, zs) ↦ do
    let ov := B.openedAt P.logBlowup m zs
    ov.forM fun ys ↦ pObserveExts ys.toList
    return ov
  let alpha ← pSampleExt
  let items := ((rounds.zip opened).map fun ((_, ms), orow) ↦
    (ms.zip orow).map fun ((m, zs), ovs) ↦ (m, zs.zip ovs)).flatten
  let inputs := (B.reduce alpha items).map (·.2)
  let logMax := match inputs with
    | v :: _ => Nat.log2 (B.size v)
    | [] => 0
  let cp ← commitPhase B P inputs
  cp.arities.toList.forM fun la ↦ pObserve (la : F)
  let qw ← pGrind P.queryPowBits
  let queries ← (List.range P.numQueries).mapM fun _ ↦ do
    let index ← pSampleBits logMax
    let ins := rounds.map fun (c, _) ↦ B.openAt c (index >>> (logMax - B.logHeight c))
    return (⟨ins.toArray, answerQuery B cp index⟩ : QueryProof)
  return (opened, ⟨cp.commits, cp.witnesses, queries.toArray, cp.finalPoly, qw⟩)

end CompStark.Fri
