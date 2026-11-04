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
group's lanes, and a partial last block loads the group's other coordinates from the group itself,
so that the sponge's overwrite leaves them. All groups of a range of rows are absorbed side by side, block by block, so that
every block's columns are read once for the range.
-/

@[expose] public section
namespace CompStark.Merkle.Packed
open Montgomery.Native32.Words (Fits Fits.mono Fits.of_size inBounds)
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

/-- Lines of eight words from words `q0, …, q15` of the columns `c0, …, c15` into coordinates
`0, …, 15` of the width-24 group at word `0` of `st`, if they fit. -/
@[inline] def loadColumnsAt (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : @& ByteArray)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 : Nat) (st : ByteArray) : ByteArray :=
  if h : Fits c0 q0.toUSize 7 ∧ Fits c1 q1.toUSize 7 ∧ Fits c2 q2.toUSize 7 ∧
      Fits c3 q3.toUSize 7 ∧ Fits c4 q4.toUSize 7 ∧ Fits c5 q5.toUSize 7 ∧
      Fits c6 q6.toUSize 7 ∧ Fits c7 q7.toUSize 7 ∧ Fits c8 q8.toUSize 7 ∧
      Fits c9 q9.toUSize 7 ∧ Fits c10 q10.toUSize 7 ∧ Fits c11 q11.toUSize 7 ∧
      Fits c12 q12.toUSize 7 ∧ Fits c13 q13.toUSize 7 ∧ Fits c14 q14.toUSize 7 ∧
      Fits c15 q15.toUSize 7 ∧
      GroupFits24 st 0 then
    loadColumns24 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 q0.toUSize q1.toUSize
      q2.toUSize q3.toUSize q4.toUSize q5.toUSize q6.toUSize q7.toUSize q8.toUSize q9.toUSize
      q10.toUSize q11.toUSize q12.toUSize q13.toUSize q14.toUSize q15.toUSize st 0
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
        h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1
        h.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  else st

/-- The column of coordinate `j` of a block of `n` columns from `j0`: column `j0 + j` for `j < n`,
else the group `st` itself. -/
@[inline] def blockColumn (cs : @& Array ByteArray) (j0 n : Nat) (st : ByteArray) (j : Nat) :
    ByteArray :=
  if j < n then cs.getD (j0 + j) .empty else st

/-- The word of coordinate `j`'s line of rows from `r` of a block of `n` columns from `j0`: of
column `j0 + j` for `j < n`, else coordinate `j`'s own words in the group. -/
@[inline] def blockOffset (os : @& Array Nat) (j0 n r j : Nat) : Nat :=
  if j < n then os.getD (j0 + j) 0 + r else 8 * j

/-- Rows `r, …, r + 7` of the `n ≤ 16` columns `j0, …, j0 + n - 1` into coordinates `0, …, n - 1`
of the width-24 group at word `0` of `st`, the coordinates from `n` on loaded from themselves, if
they fit. -/
@[inline] def loadColumnLines24 (cs : @& Array ByteArray) (os : @& Array Nat) (j0 n r : Nat)
    (st : ByteArray) : ByteArray :=
  loadColumnsAt (blockColumn cs j0 n st 0) (blockColumn cs j0 n st 1) (blockColumn cs j0 n st 2)
    (blockColumn cs j0 n st 3) (blockColumn cs j0 n st 4) (blockColumn cs j0 n st 5)
    (blockColumn cs j0 n st 6) (blockColumn cs j0 n st 7) (blockColumn cs j0 n st 8)
    (blockColumn cs j0 n st 9) (blockColumn cs j0 n st 10) (blockColumn cs j0 n st 11)
    (blockColumn cs j0 n st 12) (blockColumn cs j0 n st 13) (blockColumn cs j0 n st 14)
    (blockColumn cs j0 n st 15) (blockOffset os j0 n r 0) (blockOffset os j0 n r 1)
    (blockOffset os j0 n r 2) (blockOffset os j0 n r 3) (blockOffset os j0 n r 4)
    (blockOffset os j0 n r 5) (blockOffset os j0 n r 6) (blockOffset os j0 n r 7)
    (blockOffset os j0 n r 8) (blockOffset os j0 n r 9) (blockOffset os j0 n r 10)
    (blockOffset os j0 n r 11) (blockOffset os j0 n r 12) (blockOffset os j0 n r 13)
    (blockOffset os j0 n r 14) (blockOffset os j0 n r 15) st

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

/-- `scatterColumns`, by the load kernel for blocks of eight rows. -/
@[inline] def absorbColumnsBlock (cs : @& Array ByteArray) (os : @& Array Nat)
    (w rows r0 blk : Nat) (st : ByteArray) : ByteArray :=
  if r0 + 8 ≤ rows then loadColumnLines24 cs os (16 * blk) (min 16 (w - 16 * blk)) r0 st
  else scatterColumns cs os w rows r0 blk st

/-- Block `blk` of the `g` groups of eight rows from `r0` absorbed into the groups `sts`, each then
permuted: every group's lines loaded from the block's columns, read once for all groups, the
coordinates past a partial block's columns loaded from the group itself; a full block's lines
with no selection. -/
@[specialize] def absorbBlockGroups (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (cs : @& Array ByteArray) (os : @& Array Nat) (w rows r0 blk g : Nat)
    (sts : Array ByteArray) : Array ByteArray :=
  let n := min 16 (w - 16 * blk)
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
  if 16 * blk + 16 ≤ w then
    foldRange (fun (sts : Array ByteArray) k ↦ sts.modify k fun st ↦
      PackedPoseidon2.permute24 p (if r0 + 8 * k + 8 ≤ rows then
          let r := r0 + 8 * k
          loadColumnsAt c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 (o0 + r) (o1 + r)
            (o2 + r) (o3 + r) (o4 + r) (o5 + r) (o6 + r) (o7 + r) (o8 + r) (o9 + r) (o10 + r)
            (o11 + r) (o12 + r) (o13 + r) (o14 + r) (o15 + r) st
        else scatterColumns cs os w rows (r0 + 8 * k) blk st)) g 0 sts
  else
    foldRange (fun (sts : Array ByteArray) k ↦ sts.modify k fun st ↦
      PackedPoseidon2.permute24 p (if r0 + 8 * k + 8 ≤ rows then
          let r := r0 + 8 * k
          loadColumnsAt (if 0 < n then c0 else st) (if 1 < n then c1 else st)
            (if 2 < n then c2 else st) (if 3 < n then c3 else st) (if 4 < n then c4 else st)
            (if 5 < n then c5 else st) (if 6 < n then c6 else st) (if 7 < n then c7 else st)
            (if 8 < n then c8 else st) (if 9 < n then c9 else st) (if 10 < n then c10 else st)
            (if 11 < n then c11 else st) (if 12 < n then c12 else st) (if 13 < n then c13 else st)
            (if 14 < n then c14 else st) (if 15 < n then c15 else st) (if 0 < n then o0 + r else 0)
            (if 1 < n then o1 + r else 8) (if 2 < n then o2 + r else 16)
            (if 3 < n then o3 + r else 24) (if 4 < n then o4 + r else 32)
            (if 5 < n then o5 + r else 40) (if 6 < n then o6 + r else 48)
            (if 7 < n then o7 + r else 56) (if 8 < n then o8 + r else 64)
            (if 9 < n then o9 + r else 72) (if 10 < n then o10 + r else 80)
            (if 11 < n then o11 + r else 88) (if 12 < n then o12 + r else 96)
            (if 13 < n then o13 + r else 104) (if 14 < n then o14 + r else 112)
            (if 15 < n then o15 + r else 120) st
        else scatterColumns cs os w rows (r0 + 8 * k) blk st)) g 0 sts

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
