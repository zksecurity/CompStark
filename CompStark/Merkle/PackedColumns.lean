/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Packed
import CompStark.Poseidon2.Unrolled

/-! # Merkle leaves of a matrix given by its columns

The leaf digests of a matrix whose columns lie in separate buffers: column `j` of the rows
`0, 1, …` is words `os[j], os[j] + 1, …` of `cs[j]`. Eight consecutive rows share one
width-24 group, one row per lane, as for row-major matrices (`hashRange`); a block of sixteen
columns of the eight rows is sixteen lines of eight consecutive words, loaded straight into the
group's lanes. All groups of a range of rows are absorbed side by side, block by block, so that
every block's columns are read once for the range.
-/

@[expose] public section
namespace CompStark.Merkle.Packed
open CompStark.Poseidon2 CompStark.Poseidon2.Packed Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write zeroWords readUOffset putWords
  size_putWords wordOffset_toNat)

set_option maxRecDepth 16384 in
/-- Lines of eight words from words `o0, …, o15` of the columns `c0, …, c15` into coordinates
`0, …, 15` of the width-24 group at `i`: word `l` of `c{j}`'s line becomes coordinate `j` of lane
`l`. -/
@[noinline] def loadColumns24 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : @& ByteArray)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : USize) (b : ByteArray) (i : USize)
    (h0 : Fits c0 o0 7) (h1 : Fits c1 o1 7) (h2 : Fits c2 o2 7) (h3 : Fits c3 o3 7)
    (h4 : Fits c4 o4 7) (h5 : Fits c5 o5 7) (h6 : Fits c6 o6 7) (h7 : Fits c7 o7 7)
    (h8 : Fits c8 o8 7) (h9 : Fits c9 o9 7) (h10 : Fits c10 o10 7) (h11 : Fits c11 o11 7)
    (h12 : Fits c12 o12 7) (h13 : Fits c13 o13 7) (h14 : Fits c14 o14 7) (h15 : Fits c15 o15 7)
    (hb : GroupFits24 b i) : ByteArray :=
  p2_loadColumns% 24

/-- Rows `r, …, r + 7` of the columns `c0, …, c15` from the words `o0, …, o15` into coordinates
`0, …, 15` of the width-24 group at word `0` of `st`, if they fit. -/
@[inline] def loadColumnsAt (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : @& ByteArray)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : Nat) (r : Nat)
    (st : ByteArray) : ByteArray :=
  if h : Fits c0 (o0 + r).toUSize 7 ∧ Fits c1 (o1 + r).toUSize 7 ∧ Fits c2 (o2 + r).toUSize 7 ∧
      Fits c3 (o3 + r).toUSize 7 ∧ Fits c4 (o4 + r).toUSize 7 ∧ Fits c5 (o5 + r).toUSize 7 ∧
      Fits c6 (o6 + r).toUSize 7 ∧ Fits c7 (o7 + r).toUSize 7 ∧ Fits c8 (o8 + r).toUSize 7 ∧
      Fits c9 (o9 + r).toUSize 7 ∧ Fits c10 (o10 + r).toUSize 7 ∧ Fits c11 (o11 + r).toUSize 7 ∧
      Fits c12 (o12 + r).toUSize 7 ∧ Fits c13 (o13 + r).toUSize 7 ∧ Fits c14 (o14 + r).toUSize 7 ∧
      Fits c15 (o15 + r).toUSize 7 ∧
      GroupFits24 st 0 then
    loadColumns24 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 (o0 + r).toUSize
      (o1 + r).toUSize (o2 + r).toUSize (o3 + r).toUSize (o4 + r).toUSize (o5 + r).toUSize
      (o6 + r).toUSize (o7 + r).toUSize (o8 + r).toUSize (o9 + r).toUSize (o10 + r).toUSize
      (o11 + r).toUSize (o12 + r).toUSize (o13 + r).toUSize (o14 + r).toUSize (o15 + r).toUSize st
      0 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  else st

/-- Rows `r, …, r + 7` of the columns `j0, …, j0 + 15` into coordinates `0, …, 15` of the
width-24 group at word `0` of `st`, if they fit. -/
@[inline] def loadColumnLines24 (cs : @& Array ByteArray) (os : @& Array Nat) (j0 r : Nat)
    (st : ByteArray) : ByteArray :=
  loadColumnsAt (cs.getD (j0 + 0) .empty) (cs.getD (j0 + 1) .empty) (cs.getD (j0 + 2) .empty)
    (cs.getD (j0 + 3) .empty) (cs.getD (j0 + 4) .empty) (cs.getD (j0 + 5) .empty)
    (cs.getD (j0 + 6) .empty) (cs.getD (j0 + 7) .empty) (cs.getD (j0 + 8) .empty)
    (cs.getD (j0 + 9) .empty) (cs.getD (j0 + 10) .empty) (cs.getD (j0 + 11) .empty)
    (cs.getD (j0 + 12) .empty) (cs.getD (j0 + 13) .empty) (cs.getD (j0 + 14) .empty)
    (cs.getD (j0 + 15) .empty) (os.getD (j0 + 0) 0) (os.getD (j0 + 1) 0) (os.getD (j0 + 2) 0)
    (os.getD (j0 + 3) 0) (os.getD (j0 + 4) 0) (os.getD (j0 + 5) 0) (os.getD (j0 + 6) 0)
    (os.getD (j0 + 7) 0) (os.getD (j0 + 8) 0) (os.getD (j0 + 9) 0) (os.getD (j0 + 10) 0)
    (os.getD (j0 + 11) 0) (os.getD (j0 + 12) 0) (os.getD (j0 + 13) 0) (os.getD (j0 + 14) 0)
    (os.getD (j0 + 15) 0) r st

/-- Block `blk` of the rows `r0, …, r0 + 7` of the columns of a matrix of width `w` into
coordinates `0, …, 15` of the lanes of the group at word `0` of `st`, word by word: column
`16 blk + j` of row `r0 + l` becomes coordinate `j` of lane `l`, for rows below `rows` and columns
below `w`. -/
@[inline] def scatterColumns (cs : @& Array ByteArray) (os : @& Array Nat) (w rows r0 blk : Nat)
    (st : ByteArray) : ByteArray := Id.run do
  let mut st := st
  for l in [:8] do
    if r0 + l < rows then
      for j in [:min 16 (w - 16 * blk)] do
        st := write st (8 * j + l)
          (read (cs.getD (16 * blk + j) .empty) (os.getD (16 * blk + j) 0 + r0 + l))
  return st

/-- `scatterColumns`, by the load kernel for full blocks of eight rows. -/
@[inline] def absorbColumnsBlock (cs : @& Array ByteArray) (os : @& Array Nat)
    (w rows r0 blk : Nat) (st : ByteArray) : ByteArray :=
  if r0 + 8 ≤ rows ∧ 16 * blk + 16 ≤ w then loadColumnLines24 cs os (16 * blk) r0 st
  else scatterColumns cs os w rows r0 blk st

/-- Block `blk` of the `g` groups of eight rows from `r0` absorbed into the groups `sts`, each then
permuted: every group's lines loaded from the block's sixteen columns, read once for all groups. -/
@[specialize] def absorbBlockGroups (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (cs : @& Array ByteArray) (os : @& Array Nat) (w rows r0 blk g : Nat)
    (sts : Array ByteArray) : Array ByteArray :=
  if 16 * blk + 16 ≤ w then
    let c0 := cs.getD (16 * blk + 0) .empty
    let c1 := cs.getD (16 * blk + 1) .empty
    let c2 := cs.getD (16 * blk + 2) .empty
    let c3 := cs.getD (16 * blk + 3) .empty
    let c4 := cs.getD (16 * blk + 4) .empty
    let c5 := cs.getD (16 * blk + 5) .empty
    let c6 := cs.getD (16 * blk + 6) .empty
    let c7 := cs.getD (16 * blk + 7) .empty
    let c8 := cs.getD (16 * blk + 8) .empty
    let c9 := cs.getD (16 * blk + 9) .empty
    let c10 := cs.getD (16 * blk + 10) .empty
    let c11 := cs.getD (16 * blk + 11) .empty
    let c12 := cs.getD (16 * blk + 12) .empty
    let c13 := cs.getD (16 * blk + 13) .empty
    let c14 := cs.getD (16 * blk + 14) .empty
    let c15 := cs.getD (16 * blk + 15) .empty
    let o0 := os.getD (16 * blk + 0) 0
    let o1 := os.getD (16 * blk + 1) 0
    let o2 := os.getD (16 * blk + 2) 0
    let o3 := os.getD (16 * blk + 3) 0
    let o4 := os.getD (16 * blk + 4) 0
    let o5 := os.getD (16 * blk + 5) 0
    let o6 := os.getD (16 * blk + 6) 0
    let o7 := os.getD (16 * blk + 7) 0
    let o8 := os.getD (16 * blk + 8) 0
    let o9 := os.getD (16 * blk + 9) 0
    let o10 := os.getD (16 * blk + 10) 0
    let o11 := os.getD (16 * blk + 11) 0
    let o12 := os.getD (16 * blk + 12) 0
    let o13 := os.getD (16 * blk + 13) 0
    let o14 := os.getD (16 * blk + 14) 0
    let o15 := os.getD (16 * blk + 15) 0
    foldRange (fun (sts : Array ByteArray) k ↦ sts.modify k fun st ↦
      PackedPoseidon2.permute24 p (if r0 + 8 * k + 8 ≤ rows
        then loadColumnsAt c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 o0 o1 o2 o3 o4 o5
          o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 (r0 + 8 * k) st
        else scatterColumns cs os w rows (r0 + 8 * k) blk st)) g 0 sts
  else
    foldRange (fun (sts : Array ByteArray) k ↦ sts.modify k fun st ↦
      PackedPoseidon2.permute24 p (scatterColumns cs os w rows (r0 + 8 * k) blk st)) g 0 sts

/-- The width-24 groups absorbing the `g` groups of eight rows from `r0` of the columns of a matrix
of width `w` and `rows` rows, block by block, every group permuted after each block. -/
@[specialize] def absorbColumns (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (cs : @& Array ByteArray) (os : @& Array Nat) (w rows r0 g : Nat) :
    Array ByteArray :=
  foldRange (fun sts blk ↦ absorbBlockGroups p cs os w rows r0 blk g sts)
    ((w + 15) / 16) 0 (Array.replicate g (zeroWords 192))

/-- The leaf digests of the `n` rows of the columns `cs` from the words `os` of a matrix of width
`w`: all groups of eight rows absorbed side by side, so that every block of sixteen columns is read
once, `n` rows at a time. -/
@[specialize] def hashColumns (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (cs : @& Array ByteArray) (os : @& Array Nat) (w n : Nat) : ByteArray :=
  let g := (n + 7) / 8
  let sts := absorbColumns p cs os w n 0 g
  foldRange (fun out k ↦ storeRows (sts.getD k .empty) n (8 * k) out) g 0 (zeroWords (8 * n))

end CompStark.Merkle.Packed
