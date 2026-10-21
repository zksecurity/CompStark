/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Challenger
public import CompStark.Fri.Verifier
public import CompStark.Stark.Quotient
public import CompStark.Lookup.Quotient

/-! # The FRI prover of the two-adic commitment scheme

Plonky3's `TwoAdicFriPcs::commit` and `open`, `prove_fri` (revision `a4982ec`), over a base field
`F` with challenges in the extension `EF`:

* A committed matrix is the low-degree extension of its columns onto the coset `g · ⟨ω_N⟩`, rows
  in bit-reversed order, under a Merkle tree.
* Opening observes the domain separator and every claimed value, grinds, samples the batching
  challenge `α`, and sums, for every height, `α^k (p(z) - p(x)) / (z - x)` over the committed
  columns `p` and their points `z`, at every row `x` of the extended domain.
* FRI observes its domain separator; the commit phase folds the tallest sum by `2 ^ arity` per
  round of Plonky3's schedule, committing the groups as rows and adding each shorter sum when its
  height is reached, down to the final polynomial. After the query grinding it samples every
  query's index and opens the inputs and every round's groups at them, as multi-openings with
  pruned siblings.
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark

variable {F : Type} [BaseField F]

/-- The low-degree extension by `2 ^ bits` of a `2 ^ logH × w` matrix of values on `⟨ω⟩`, onto
`shift · ⟨ω_N⟩`, rows in bit-reversed order: Plonky3's `coset_lde_batch` then
`bit_reverse_rows`. Row `r` holds every column's interpolant at `shift · ω_N ^ bitrev r`; this
reference interpolates with an inverse transform and evaluates by Horner's rule. -/
def ldeRef (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : Mat F :=
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
openings and heights, the quotient values from the extensions of the trace and the preprocessed
trace, if any, the values of a matrix's columns at points, and the FRI inputs and folds. Every
backend computes the same functions (`Refines`); `spec` runs the specifications. -/
structure Backend (F EF : Type) (width : Nat) where
  transcript : Transcript F width
  M : Type
  C : Type
  V : Type
  lde : Nat → Nat → F → Nat → Array F → M
  commit : List M → C
  root : C → Digest F
  openAt : C → Nat → BatchOpening F
  /-- `log₂` of the largest committed height. -/
  logHeight : C → Nat
  quotient : Air F → List F → Nat → Nat → M → Option M → EF → Array EF
  /-- The extension constraints of an AIR folded by `α` on the quotient domain, divided by
  `Z_H` (`lookupQuotientOfLde`), from the extensions of the trace, the preprocessed trace and the
  permutation trace in base coordinates, and the challenges and the terminal. -/
  lookupQuotient : Air F → List (Lookup.ExtExpr F) → List F → Nat → Nat → M → Option M → M →
    List EF → EF → EF → Array EF
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

variable {EF : Type} [Challenge F EF] {width : Nat}

/-- The rows `perm[0], perm[1], …` of `m`, concatenated. -/
def permuteRows (m : Mat F) (perm : Array Nat) : Array F := Id.run do
  let mut out := Array.emptyWithCapacity (perm.size * m.width)
  for r in perm do
    for j in [0:m.width] do
      out := out.push (m.values.getD (r * m.width + j) 0)
  return out

/-- A matrix's row `r` as an array. -/
def rowOf (m : Mat F) (r : Nat) : Array F := Array.ofFn (n := m.width) fun j ↦
  m.values.getD (r * m.width + j) 0

/-- The extension elements of a flattened row, `d` coefficients each. -/
def unflatten (xs : List F) : List EF :=
  (List.range (xs.length / Challenge.d EF)).map fun i ↦
    Challenge.ofCoeffs
      ((List.range (Challenge.d EF)).map fun j ↦ xs.getD (Challenge.d EF * i + j) 0)

/-- Matrices under one Merkle tree: the specification's commitment, with the digest layers leaves
first. -/
structure Committed (F : Type) where
  mats : List (Mat F)
  layers : Array (Array (Digest F))

namespace Committed

/-- Commit to matrices with the leaf hash `hash` and the compression `compress`. -/
def ofMats (hash : List F → Digest F) (compress : Digest F → Digest F → Digest F)
    (ms : List (Mat F)) : Committed F :=
  ⟨ms, ((Merkle.layers hash compress (ms.map Mat.toMatrix)).map List.toArray).toArray⟩

/-- The Merkle root. -/
def root (c : Committed F) : Digest F := (c.layers.back?.getD #[]).getD 0 0

/-- The largest matrix height. -/
def maxHeight (c : Committed F) : Nat := c.mats.foldl (fun m a ↦ max m a.height) 0

/-- The opening at `index`: every matrix's row, shifted right by the number of layers it is
shorter than the tallest, and the sibling of every layer below the root (`Merkle.openWith`). -/
def openAt (c : Committed F) (index : Nat) : BatchOpening F :=
  let logMax := Merkle.log2Ceil c.maxHeight
  let rows := c.mats.map fun m ↦ rowOf m (index >>> (logMax - Merkle.log2Ceil m.height))
  ⟨rows.toArray, Array.ofFn (n := logMax) fun i ↦
    (c.layers.getD i.val #[]).getD ((index >>> i.val) ^^^ 1) 0⟩

end Committed

/-- The prover's monad: a transcript. -/
abbrev PM (F : Type) (width : Nat) := StateM (Transcript F width)

def pObserveList (xs : List F) : PM F width Unit := modify (·.observeList xs)
def pObserveExts (xs : List EF) : PM F width Unit := modify (·.observeExts xs)
def pObserve (x : F) : PM F width Unit := modify (·.observe x)
def pSampleExt : PM F width EF := modifyGet (·.sampleExt)
def pSampleBits (bits : Nat) : PM F width Nat := modifyGet (·.sampleBits bits)
def pGrind (bits : Nat) : PM F width F := modifyGet (·.grind bits)

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
structure CommitPhase (F EF C : Type) where
  commits : Array (Digest F)
  data : List C
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

/-- The rounds of Plonky3's `commit_phase` with log arities `arities`: commit to the folded
vector's groups, fold them at a fresh `β`, and add the next input of the folded height times
`β ^ (2 ^ arity)`. -/
def commitRounds (B : Backend F EF width) (P : Params) :
    List Nat → B.V → List B.V → CommitPhase F EF B.C → PM F width (B.V × CommitPhase F EF B.C)
  | [], folded, _, cp => pure (folded, cp)
  | la :: las, folded, rest, cp => do
    let arity := 2 ^ la
    let rows := B.size folded / arity
    let c := B.commit [B.leaves arity folded]
    pObserveList (B.root c).toList
    let w ← pGrind P.commitPowBits
    let beta : EF ← pSampleExt
    let logRows := Nat.log2 rows
    let folded := if la = 1 then B.fold2 folded beta logRows else
      let vs := B.toArray folded
      B.ofArray <| Array.ofFn (n := rows) fun i ↦
        foldRow i logRows la beta ((List.range arity).map fun k ↦ vs.getD (i * arity + k) 0)
    let (folded, rest) := match rest with
      | v :: vs => if B.size v == B.size folded then
          (B.addScaled folded v (Ext.powTwo beta la), vs) else (folded, rest)
      | [] => (folded, [])
    commitRounds B P las folded rest
      ⟨cp.commits.push (B.root c), cp.data ++ [c], cp.witnesses.push w, cp.arities.push la,
        cp.finalPoly⟩

/-- Plonky3's `commit_phase` on the batched quotients `inputs`, tallest first, with log arities
`arities`. -/
def commitPhase (B : Backend F EF width) (P : Params) (arities : List Nat) (inputs : List B.V) :
    PM F width (CommitPhase F EF B.C) := do
  let (folded, rest) := match inputs with
    | v :: vs => (v, vs)
    | [] => (B.ofArray #[], [])
  let (folded, cp) ← commitRounds B P arities folded rest ⟨#[], [], #[], #[], #[]⟩
  let fa := B.toArray folded
  let len := 2 ^ P.logFinalPolyLen
  let truncated := Array.ofFn (n := len) fun i ↦ fa.getD (reverseBits i P.logFinalPolyLen) 0
  let finalPoly := idft P.logFinalPolyLen truncated
  pObserveExts finalPoly.toList
  return { cp with finalPoly := finalPoly }

/-- The multi-opening of the commitment `c` at `indices`: every query's rows, and the siblings of
their paths pruned (`Merkle.prune`). -/
def openMulti (B : Backend F EF width) (c : B.C) (indices : List Nat) : MultiOpening F :=
  let os := indices.map (B.openAt c)
  ⟨(os.map (·.values)).toArray,
    (Merkle.prune (B.logHeight c) indices (os.map (·.path.toList))).toArray⟩

/-- The openings of the commit-phase rounds with commitments `cs` and log arities `las` at the
queries' indices `cur`: each round opens the groups of `cur`, gives every query the other members
of its group, and passes the group indices on. -/
def answerFolds (B : Backend F EF width) : List B.C → List Nat → List Nat →
    List (CommitOpening F EF)
  | c :: cs, la :: las, cur =>
    let groups := cur.map (· >>> la)
    let o := openMulti B c groups
    let siblings := (cur.zip o.values.toList).map fun (i, rows) ↦
      let evals : List EF := unflatten ((rows.getD 0 #[]).toList)
      (((List.range (2 ^ la)).filter (· != i % 2 ^ la)).map fun j ↦ evals.getD j 0).toArray
    ⟨siblings.toArray, o.siblings⟩ :: answerFolds B cs las groups
  | _, _, _ => []

/-- `factor · ∑ᵢ weights[i] · m[perm[i]][j]` for the columns `j0, …, j0 + nj - 1` of the row-major
matrix `m` of width `w`: the barycentric evaluation of columns whose natural-order row `i` is
stored at row `perm[i]`. -/
def weightedColumns (m : @& Array F) (perm : @& Array Nat) (weights : @& Array EF)
    (w h j0 nj : Nat) (factor : EF) : Array EF := Id.run do
  let mut out := Array.emptyWithCapacity nj
  for j in [j0:j0 + nj] do
    let mut acc : EF := 0
    for i in [0:h] do
      acc := acc + Challenge.smul (m.getD (perm.getD i 0 * w + j) 0) (weights.getD i 0)
    out := out.push (factor * acc)
  return out

/-- Rows `r0, …, r0 + len - 1` of `m` (width `w`), each batched by the powers `ap` of `α`. -/
def compressRows (m : @& Array F) (ap : @& Array EF) (w r0 len : Nat) : Array EF := Id.run do
  let mut out := Array.emptyWithCapacity len
  for r in [r0:r0 + len] do
    let mut acc : EF := 0
    for i in [0:w] do
      acc := acc + Challenge.smul (m.getD (r * w + i) 0) (ap.getD i 0)
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

/-- `(z ^ n - s ^ n) / (n s ^ n)` for `n = 2 ^ logN`: the barycentric scale of the coset
`s · ⟨ω⟩` at `z`. -/
def cosetFactor (logN : Nat) (s : F) (z : EF) : EF :=
  let sn := powF s (2 ^ logN)
  (Ext.powTwo z logN - Ext.ofBase sn) * (Ext.ofBase (((2 ^ logN : Nat) : F) * sn))⁻¹

/-- The values of a committed matrix's columns at `z`: the polynomials of degree below
`height / 2 ^ logBlowup` through its low coset rows. -/
def openedAt (logBlowup : Nat) (m : Mat F) (z : EF) : Array EF :=
  let logH := Nat.log2 m.height - logBlowup
  let h := 2 ^ logH
  -- Barycentric weights `xᵢ / (z - xᵢ)` of the natural-order coset, and the scale.
  let xs := cosetPoints gen logH
  let invs := batchInv (xs.map fun x ↦ z - Ext.ofBase x)
  let weights := Array.zipWith Challenge.smul xs invs
  let factor := cosetFactor logH gen z
  let perm := bitRevPerm logH
  parChunks m.width (min m.width 16) fun j0 nj ↦
    weightedColumns m.values perm weights m.width h j0 nj factor

/-- Rows batched by the powers `ap` of `α`, in parallel row ranges. -/
def compress (m : Mat F) (ap : Array EF) : Array EF :=
  parChunks m.height (if m.height < 4096 then 1 else 16) fun r0 len ↦
    compressRows m.values ap m.width r0 len

/-- A periodic column of period `p = 2 ^ k` on the quotient domain `g · ⟨ω_q⟩` of a trace of
`2 ^ degreeBits` rows with `2 ^ logChunks` chunks, in natural order: its first `p · 2 ^ logChunks`
rows, after which it repeats. Its polynomial `f(X ^ (n / p))` at `g ω_qʳ` is `f` at
`g ^ (n / p) ω_Lʳ`, `ω_L` of order `L = p · 2 ^ logChunks`: the extension of its period onto that
coset (Plonky3's `build_periodic_lde_table`). -/
def periodicOnQuotient (col : List F) (degreeBits logChunks : Nat) : Array F :=
  let k := Nat.log2 col.length
  permuteRows (ldeRef k logChunks (powF gen (2 ^ (degreeBits - k))) 1 col.toArray)
    (bitRevPerm (k + logChunks))

/-- The quotient values from the extensions `ext` of the trace and `prep` of the preprocessed
trace, if any: their first `2 ^ (degreeBits + logChunks)` rows in natural order are the traces on
the quotient domain; and the AIR's periodic columns there. -/
def quotientOfLde (A : Air F) (pis : List F) (degreeBits logChunks : Nat) (ext : Mat F)
    (prep : Option (Mat F)) (alpha : EF) : Array EF :=
  let qlog := degreeBits + logChunks
  let onQuotient (m : Mat F) := Mat.ofValues m.width (2 ^ qlog) (permuteRows m (bitRevPerm qlog))
  quotientValues A pis degreeBits logChunks (onQuotient ext)
    ((prep.map onQuotient).getD (Mat.ofValues 0 (2 ^ qlog) #[]))
    (A.periodic.map fun col ↦ periodicOnQuotient col degreeBits logChunks) alpha

/-- The extension constraints `ext` of `A` folded by `α`, divided by `Z_H`, from the extensions
`ext` of the trace, `prep` of the preprocessed trace, if any, and `perm` of the permutation trace
in base coordinates: their first `2 ^ (degreeBits + logChunks)` rows in natural order are the
traces on the quotient domain (`lookupQuotientValues`). -/
def lookupQuotientOfLde (A : Air F) (ext : List (Lookup.ExtExpr F)) (pis : List F)
    (degreeBits logChunks : Nat) (tr : Mat F) (prep : Option (Mat F)) (perm : Mat F)
    (chs : List EF) (terminal alpha : EF) : Array EF :=
  let qlog := degreeBits + logChunks
  let onQuotient (m : Mat F) := Mat.ofValues m.width (2 ^ qlog) (permuteRows m (bitRevPerm qlog))
  Lookup.lookupQuotientValues ext pis degreeBits logChunks (onQuotient tr)
    ((prep.map onQuotient).getD (Mat.ofValues 0 (2 ^ qlog) #[])) (onQuotient perm)
    (A.periodic.map fun col ↦ periodicOnQuotient col degreeBits logChunks) chs terminal alpha

/-- The batched quotients `∑ αᵏ (p(z) - p(x)) / (z - x)` by log height, tallest first: each
matrix's rows batched by the powers of `α` once, then every point accumulated over the rows with
the running power of `α` of its height. -/
def reduce (alpha : EF) (items : List (Mat F × List (EF × Array EF))) : List (Nat × Array EF) :=
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

/-- The specification backend, on the transcript `t` and the Merkle hashes `hash` and
`compress`. -/
@[reducible]
def Backend.spec (EF : Type) [Challenge F EF] (t : Transcript F width) (hash : List F → Digest F)
    (compress : Digest F → Digest F → Digest F) : Backend F EF width where
  transcript := t
  M := Mat F
  C := Committed F
  V := Array EF
  lde := ldeRef
  commit := Committed.ofMats hash compress
  root := Committed.root
  openAt := Committed.openAt
  logHeight c := Nat.log2 c.maxHeight
  quotient := quotientOfLde
  lookupQuotient := lookupQuotientOfLde
  openedAt b m zs := zs.map (Fri.openedAt b m)
  toArray := id
  ofArray := id
  size := Array.size
  reduce := Fri.reduce
  fold2 := foldPairs
  addScaled a b x := Array.zipWith (fun u v ↦ u + x * v) a b
  leaves k vs :=
    Mat.ofValues (Challenge.d EF * k) (vs.size / k) (vs.flatMap fun x ↦ (Ext.coeffs x).toArray)

/-- A committed batch with each of its matrices and the points at which it is opened. -/
abbrev OpenRound (B : Backend F EF width) := B.C × List (B.M × List EF)

/-- Plonky3's `prove_fri` on the batched quotients `inputs`, tallest first, after the batching
grinding witness `batchWitness`: the domain separator, the commit phase, the query grinding, the
queries' indices, and the input and commit-phase openings at them. -/
def proveFri (B : Backend F EF width) (P : Params) (rounds : List (OpenRound B))
    (inputs : List B.V) (batchWitness : F) : PM F width (FriProof F EF) := do
  let heights := inputs.map (Nat.log2 <| B.size ·)
  let logMax := heights.headD 0
  let arities := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax heights
  pObserveList (DomainSeparator.friSeed F EF arities (2 ^ P.logFinalPolyLen) P.commitPowBits
    P.queryPowBits P.numQueries logMax P.logBlowup P.maxLogArity)
  let cp ← commitPhase B P arities inputs
  let qw ← pGrind P.queryPowBits
  let indices ← (List.range P.numQueries).mapM fun _ ↦ pSampleBits logMax
  let ins := rounds.map fun (c, _) ↦ openMulti B c (indices.map (· >>> (logMax - B.logHeight c)))
  return ⟨batchWitness, cp.commits, cp.witnesses, ins.toArray,
    (answerFolds B cp.data cp.arities.toList indices).toArray, cp.finalPoly, qw⟩

/-- Plonky3's `TwoAdicFriPcs::open`: the opened values, by round, matrix and point, observed
after the domain separator, the batching grinding and challenge `α`, and the FRI proof. -/
def openPcs (B : Backend F EF width) (P : Params) (rounds : List (OpenRound B)) :
    PM F width (List (List (List (Array EF))) × FriProof F EF) := do
  let opened := rounds.map fun (_, ms) ↦ ms.map fun (m, zs) ↦
    let ov := B.openedAt P.logBlowup m zs
    (ov, m, zs.zip ov)
  pObserveList (DomainSeparator.pcsSeed F EF
    (opened.map (·.map fun (ov, _) ↦ ov.map (·.size))) P.batchPowBits)
  opened.forM fun os ↦ os.forM fun (ov, _) ↦ ov.forM fun ys ↦ pObserveExts ys.toList
  let bw ← pGrind P.batchPowBits
  let alpha : EF ← pSampleExt
  let fri ← proveFri B P rounds ((B.reduce alpha (opened.flatten.map (·.2))).map (·.2)) bw
  return (opened.map (·.map (·.1)), fri)

end CompStark.Fri
