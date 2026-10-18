/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Verifier
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

/-- A row-major matrix of base elements. -/
abbrev Mat := Merkle.Matrix F

/-- Matrices under one Merkle tree. -/
structure Committed where
  mats : List Mat
  layers : List (List Digest)

namespace Committed

/-- Commit to matrices. -/
def ofMats (ms : List Mat) : Committed :=
  ⟨ms, Merkle.layers (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) ms⟩

/-- The Merkle root. -/
def root (c : Committed) : Digest := (c.layers.getLastD []).headD 0

/-- The opening at `index`. -/
def openAt (c : Committed) (index : Nat) : BatchOpening :=
  let (rows, path) := Merkle.openWith c.mats c.layers index
  ⟨(rows.map List.toArray).toArray, path.toArray⟩

/-- The largest matrix height. -/
def maxHeight (c : Committed) : Nat := c.mats.foldl (fun m a ↦ max m a.height) 0

end Committed

/-- The low-degree extension by `2 ^ bits` of a `2 ^ logH × w` matrix of values on `⟨ω⟩`, onto
`shift · ⟨ω_N⟩`, rows in bit-reversed order: Plonky3's `coset_lde_batch` then
`bit_reverse_rows`. Row `r` holds every column's interpolant at `shift · ω_N ^ bitrev r`; this
reference interpolates with an inverse transform and evaluates by Horner's rule. -/
def lde (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : Mat :=
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
  ⟨w, 2 ^ logN, rows.flatten⟩

/-- A matrix's row `r` as an array. -/
def rowOf (m : Mat) (r : Nat) : Array F := Array.ofFn (n := m.width) fun j ↦
  m.values.getD (r * m.width + j) 0

/-- The extension elements of a flattened row, four coefficients each. -/
def unflatten (xs : List F) : List EF :=
  (List.range (xs.length / 4)).map fun i ↦
    ⟨xs.getD (4 * i) 0, xs.getD (4 * i + 1) 0, xs.getD (4 * i + 2) 0, xs.getD (4 * i + 3) 0⟩

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

/-- The result of the commit phase. -/
structure CommitPhase where
  commits : Array Digest
  data : Array Committed
  witnesses : Array F
  arities : Array Nat
  finalPoly : Array EF

/-- Plonky3's `commit_phase` on the batched quotients `inputs`, tallest first. -/
def commitPhase (P : Params) (inputs : List (Array EF)) : PM CommitPhase := do
  let fuel := inputs.headD #[] |>.size
  let mut folded := inputs.headD #[]
  let mut rest := inputs.tail
  let mut cp : CommitPhase := ⟨#[], #[], #[], #[], #[]⟩
  for _ in List.range fuel do
    if folded.size ≤ 2 ^ (P.logBlowup + P.logFinalPolyLen) then break
    let logCur := Nat.log2 folded.size
    let la := logArityFor P logCur (rest.head?.map (Nat.log2 ·.size))
    let arity := 2 ^ la
    let rows := folded.size / arity
    let leaves : Mat := ⟨4 * arity, rows, folded.toList.flatMap Ext.coeffs |>.toArray⟩
    let c := Committed.ofMats [leaves]
    pObserveList c.root.toList
    let w ← pGrind P.commitPowBits
    let beta ← pSampleExt
    let logRows := Nat.log2 rows
    folded := Array.ofFn (n := rows) fun i ↦
      foldRow i logRows la beta ((List.range arity).map fun k ↦ folded.getD (i * arity + k) 0)
    match rest with
    | v :: vs =>
      if v.size == folded.size then
        let bp := Ext.powTwo beta la
        folded := Array.ofFn (n := folded.size) fun i ↦ folded.getD i 0 + bp * v.getD i 0
        rest := vs
    | [] => pure ()
    cp := ⟨cp.commits.push c.root, cp.data.push c, cp.witnesses.push w, cp.arities.push la,
      cp.finalPoly⟩
  let len := 2 ^ P.logFinalPolyLen
  let truncated := Array.ofFn (n := len) fun i ↦
    folded.getD (reverseBits i P.logFinalPolyLen) 0
  let finalPoly := idft P.logFinalPolyLen truncated
  pObserveExts finalPoly.toList
  return { cp with finalPoly := finalPoly }

/-- The commit-phase openings of a query at `index`. -/
def answerQuery (cp : CommitPhase) (index : Nat) : Array CommitStep := Id.run do
  let mut cur := index
  let mut steps := #[]
  for (c, la) in cp.data.toList.zip cp.arities.toList do
    let arity := 2 ^ la
    let pos := cur % arity
    let group := cur >>> la
    let o := c.openAt group
    let evals := unflatten ((o.values.getD 0 #[]).toList)
    let siblings := ((List.range arity).filter (· != pos)).map fun j ↦ evals.getD j 0
    steps := steps.push ⟨la, siblings.toArray, o.path⟩
    cur := group
  return steps

/-- A committed batch with the points at which each of its matrices is opened. -/
abbrev OpenRound := Committed × List (List EF)

/-- The values of a committed matrix's columns at `z`: the polynomials of degree below
`height / 2 ^ logBlowup` through its low coset rows. -/
def openedAt (P : Params) (m : Mat) (z : EF) : Array EF :=
  let logH := Nat.log2 m.height - P.logBlowup
  let h := 2 ^ logH
  let vals := Array.ofFn (n := h * m.width) fun k ↦
    m.values.getD (reverseBits (k.val / m.width) logH * m.width + k.val % m.width) 0
  KoalaBear.Fast.interpolateCoset logH (twoAdicGen logH) gen m.width vals z

/-- Plonky3's `TwoAdicFriPcs::open`: the opened values, by round, matrix and point, and the FRI
proof. -/
def openPcs (P : Params) (rounds : List OpenRound) :
    PM (List (List (List (Array EF))) × FriProof) := do
  let mut opened := []
  for (c, pts) in rounds do
    let mut om := []
    for (m, zs) in c.mats.zip pts do
      let mut ov := []
      for z in zs do
        let ys := openedAt P m z
        pObserveExts ys.toList
        ov := ov ++ [ys]
      om := om ++ [ov]
    opened := opened ++ [om]
  let alpha ← pSampleExt
  -- The batched quotients by log height, with the number of columns batched into each.
  let mut red : List (Nat × Nat × Array EF) := []
  for ((c, pts), orow) in (rounds.zip opened) do
    for ((m, zs), ovs) in (c.mats.zip pts).zip orow do
      let logH := Nat.log2 m.height
      let (cnt, acc) := (red.lookup logH).getD (0, Array.replicate m.height 0)
      let mut cnt := cnt
      let mut acc := acc
      for (z, ys) in zs.zip ovs do
        let offset := Ext.pow alpha cnt
        let ap := (List.range m.width).map fun i ↦ Ext.pow alpha i
        let yz := (ap.zip ys.toList).foldl (fun s (a, y) ↦ s + a * y) 0
        acc := Array.ofFn (n := m.height) fun r ↦
          let x := gen * powF (twoAdicGen logH) (reverseBits r logH)
          let row := rowOf m r
          let px := (ap.zip row.toList).foldl (fun s (a, p) ↦ s + a * Ext.ofBase p) 0
          acc.getD r 0 + offset * (yz - px) * (z - Ext.ofBase x)⁻¹
        cnt := cnt + m.width
      red := (logH, cnt, acc) :: red.filter (·.1 != logH)
  let inputs := ((red.mergeSort fun a b ↦ b.1 ≤ a.1).map (·.2.2))
  let logMax := Nat.log2 (inputs.headD #[]).size
  let cp ← commitPhase P inputs
  for la in cp.arities do pObserve (la : F)
  let qw ← pGrind P.queryPowBits
  let mut queries := #[]
  for _ in List.range P.numQueries do
    let index ← pSampleBits logMax
    let ins := rounds.map fun (c, _) ↦
      c.openAt (index >>> (logMax - Nat.log2 c.maxHeight))
    queries := queries.push ⟨ins.toArray, answerQuery cp index⟩
  return (opened, ⟨cp.commits, cp.witnesses, queries, cp.finalPoly, qw⟩)

end CompStark.Fri
