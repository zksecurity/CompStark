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
group's lanes. Eight groups, sixty-four rows, are absorbed side by side, block by block, so that
every column is read sixty-four rows at a time.
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

/-- Rows `r, …, r + 7` of the columns `j0, …, j0 + 15` into coordinates `0, …, 15` of
the width-24 group at word `0` of `st`, if they fit. -/
@[inline] def loadColumnLines24 (cs : @& Array ByteArray) (os : @& Array Nat) (j0 r : Nat)
    (st : ByteArray) : ByteArray :=
  let c (j : Nat) : ByteArray := cs.getD (j0 + j) .empty
  let u (j : Nat) : USize := (os.getD (j0 + j) 0 + r).toUSize
  if h : Fits (c 0) (u 0) 7 ∧ Fits (c 1) (u 1) 7 ∧ Fits (c 2) (u 2) 7 ∧ Fits (c 3) (u 3) 7 ∧
      Fits (c 4) (u 4) 7 ∧ Fits (c 5) (u 5) 7 ∧ Fits (c 6) (u 6) 7 ∧ Fits (c 7) (u 7) 7 ∧
      Fits (c 8) (u 8) 7 ∧ Fits (c 9) (u 9) 7 ∧ Fits (c 10) (u 10) 7 ∧ Fits (c 11) (u 11) 7 ∧
      Fits (c 12) (u 12) 7 ∧ Fits (c 13) (u 13) 7 ∧ Fits (c 14) (u 14) 7 ∧ Fits (c 15) (u 15) 7 ∧
      GroupFits24 st 0 then
    loadColumns24 (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9) (c 10) (c 11) (c 12)
      (c 13) (c 14) (c 15) (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) (u 8) (u 9) (u 10)
      (u 11) (u 12) (u 13) (u 14) (u 15) st 0 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  else st

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

/-- The width-24 groups absorbing the `g` groups of eight rows from `r0` of the columns of a matrix
of width `w` and `rows` rows, block by block, every group permuted after each block. -/
@[specialize] def absorbColumns (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (cs : @& Array ByteArray) (os : @& Array Nat) (w rows r0 g : Nat) :
    Array ByteArray :=
  foldRange (fun sts blk ↦ foldRange (fun (sts : Array ByteArray) k ↦ sts.modify k fun st ↦
      PackedPoseidon2.permute24 p (absorbColumnsBlock cs os w rows (r0 + 8 * k) blk st)) g 0 sts)
    ((w + 15) / 16) 0 (Array.replicate g (zeroWords 192))

/-- The leaf digests of the `n` rows of the columns `cs` from the words `os` of a matrix of width
`w`, sixty-four rows at a time. -/
@[specialize] def hashColumns (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] (cs : @& Array ByteArray) (os : @& Array Nat) (w n : Nat) : ByteArray :=
  foldRange (fun out t ↦
    let g := min 16 ((n - 128 * t + 7) / 8)
    let sts := absorbColumns p cs os w n (128 * t) g
    foldRange (fun out k ↦ storeRows (sts.getD k .empty) n (128 * t + 8 * k) out) g 0 out)
    ((n + 127) / 128) 0 (zeroWords (8 * n))

end CompStark.Merkle.Packed
