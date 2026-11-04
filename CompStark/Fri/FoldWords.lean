/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.Montgomery.Native32Words
public import CompStark.Poseidon2.Arithmetic

/-! # Word kernels of the arity-2 fold

The arity-2 fold of a coordinate plane reads its pairs where they are, words `2 i` and `2 i + 1`:
`halves` gives `(x + y) / 2` of every pair and `diffs` gives `(x - y) · c_i` for a base vector
`c`, sixteen pairs at a time in straight-line kernels that the C compiler vectorizes, the rest pair
by pair. The fold is then `halves + β · diffs` on planes, with no pass that splits a plane into
its even and odd words first.
-/

@[expose] public section
namespace CompStark.Fri.FoldWords
open CompPoly.CPolynomial.NTTFast
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset read write write16U zeroWords)
open Montgomery.Native32 (Mont32Field)
open Montgomery.Native32.Words (Fits inBounds rd)
open CompStark.Poseidon2 (halve)

/-- Word `j + k`, `k ≤ 31`, of a buffer whose words `j, …, j + 31` fit. -/
@[inline] def rd32 (a : @& ByteArray) (j : USize) (k : Nat) (h : Fits a j 31)
    (hk : k ≤ 31 := by decide) : UInt32 :=
  readUOffset a j k.toUSize (inBounds h k.toUSize (by
    rw [USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]; exact hk))

/-- Words `i, …, i + 15` of `out` the halved sums of the sixteen pairs at word `j` of `b`. -/
@[noinline, specialize] def half16 (p : ℕ) [Mont32Field p] (b : @& ByteArray) (j : USize)
    (i : USize) (out : ByteArray) (hb : Fits b j 31) : ByteArray :=
  let x0 := halve p (Packed.add p (rd32 b j 0 hb) (rd32 b j 1 hb))
  let x1 := halve p (Packed.add p (rd32 b j 2 hb) (rd32 b j 3 hb))
  let x2 := halve p (Packed.add p (rd32 b j 4 hb) (rd32 b j 5 hb))
  let x3 := halve p (Packed.add p (rd32 b j 6 hb) (rd32 b j 7 hb))
  let x4 := halve p (Packed.add p (rd32 b j 8 hb) (rd32 b j 9 hb))
  let x5 := halve p (Packed.add p (rd32 b j 10 hb) (rd32 b j 11 hb))
  let x6 := halve p (Packed.add p (rd32 b j 12 hb) (rd32 b j 13 hb))
  let x7 := halve p (Packed.add p (rd32 b j 14 hb) (rd32 b j 15 hb))
  let x8 := halve p (Packed.add p (rd32 b j 16 hb) (rd32 b j 17 hb))
  let x9 := halve p (Packed.add p (rd32 b j 18 hb) (rd32 b j 19 hb))
  let x10 := halve p (Packed.add p (rd32 b j 20 hb) (rd32 b j 21 hb))
  let x11 := halve p (Packed.add p (rd32 b j 22 hb) (rd32 b j 23 hb))
  let x12 := halve p (Packed.add p (rd32 b j 24 hb) (rd32 b j 25 hb))
  let x13 := halve p (Packed.add p (rd32 b j 26 hb) (rd32 b j 27 hb))
  let x14 := halve p (Packed.add p (rd32 b j 28 hb) (rd32 b j 29 hb))
  let x15 := halve p (Packed.add p (rd32 b j 30 hb) (rd32 b j 31 hb))
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `i, …, i + 15` of `out` the differences of the sixteen pairs at word `j` of `b`, times
words `k, …, k + 15` of `c`. -/
@[noinline, specialize] def diff16 (p : ℕ) [Mont32Field p] (b c : @& ByteArray) (j k : USize)
    (i : USize) (out : ByteArray) (hb : Fits b j 31) (hc : Fits c k 15) : ByteArray :=
  let x0 := Packed.mul p (Packed.sub p (rd32 b j 0 hb) (rd32 b j 1 hb)) (rd c k 0 hc)
  let x1 := Packed.mul p (Packed.sub p (rd32 b j 2 hb) (rd32 b j 3 hb)) (rd c k 1 hc)
  let x2 := Packed.mul p (Packed.sub p (rd32 b j 4 hb) (rd32 b j 5 hb)) (rd c k 2 hc)
  let x3 := Packed.mul p (Packed.sub p (rd32 b j 6 hb) (rd32 b j 7 hb)) (rd c k 3 hc)
  let x4 := Packed.mul p (Packed.sub p (rd32 b j 8 hb) (rd32 b j 9 hb)) (rd c k 4 hc)
  let x5 := Packed.mul p (Packed.sub p (rd32 b j 10 hb) (rd32 b j 11 hb)) (rd c k 5 hc)
  let x6 := Packed.mul p (Packed.sub p (rd32 b j 12 hb) (rd32 b j 13 hb)) (rd c k 6 hc)
  let x7 := Packed.mul p (Packed.sub p (rd32 b j 14 hb) (rd32 b j 15 hb)) (rd c k 7 hc)
  let x8 := Packed.mul p (Packed.sub p (rd32 b j 16 hb) (rd32 b j 17 hb)) (rd c k 8 hc)
  let x9 := Packed.mul p (Packed.sub p (rd32 b j 18 hb) (rd32 b j 19 hb)) (rd c k 9 hc)
  let x10 := Packed.mul p (Packed.sub p (rd32 b j 20 hb) (rd32 b j 21 hb)) (rd c k 10 hc)
  let x11 := Packed.mul p (Packed.sub p (rd32 b j 22 hb) (rd32 b j 23 hb)) (rd c k 11 hc)
  let x12 := Packed.mul p (Packed.sub p (rd32 b j 24 hb) (rd32 b j 25 hb)) (rd c k 12 hc)
  let x13 := Packed.mul p (Packed.sub p (rd32 b j 26 hb) (rd32 b j 27 hb)) (rd c k 13 hc)
  let x14 := Packed.mul p (Packed.sub p (rd32 b j 28 hb) (rd32 b j 29 hb)) (rd c k 14 hc)
  let x15 := Packed.mul p (Packed.sub p (rd32 b j 30 hb) (rd32 b j 31 hb)) (rd c k 15 hc)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- `(x + y) / 2` of pairs `r0, …, r0 + len - 1` of `b`. -/
@[specialize] def halves (p : ℕ) [Mont32Field p] (b : @& ByteArray) (r0 len : Nat) : ByteArray :=
  Id.run do
  let mut out := zeroWords len
  for block in [:len / 16] do
    let i := 16 * block
    if h : 4 * (2 * (r0 + i) + 31) + 3 < b.size ∧ b.size < USize.size then
      out := half16 p b (USize.ofNatLT (2 * (r0 + i)) (by omega)) (USize.ofNatLT i (by omega)) out
        (by simp only [Fits, USize.toNat_ofNatLT]; exact h)
  for k in [16 * (len / 16):len] do
    out := write out k (halve p (Packed.add p (read b (2 * (r0 + k))) (read b (2 * (r0 + k) + 1))))
  return out

/-- `(x - y) · c_(r0 + i)` of pairs `r0 + i`, `i < len`, of `b`. -/
@[specialize] def diffs (p : ℕ) [Mont32Field p] (b c : @& ByteArray) (r0 len : Nat) : ByteArray :=
  Id.run do
  let mut out := zeroWords len
  for block in [:len / 16] do
    let i := 16 * block
    if h : 4 * (2 * (r0 + i) + 31) + 3 < b.size ∧ 4 * (r0 + i + 15) + 3 < c.size ∧
        b.size < USize.size ∧ c.size < USize.size then
      out := diff16 p b c (USize.ofNatLT (2 * (r0 + i)) (by omega))
        (USize.ofNatLT (r0 + i) (by omega)) (USize.ofNatLT i (by omega)) out
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.1, h.2.2.1⟩)
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.1, h.2.2.2⟩)
  for k in [16 * (len / 16):len] do
    out := write out k (Packed.mul p
      (Packed.sub p (read b (2 * (r0 + k))) (read b (2 * (r0 + k) + 1))) (read c (r0 + k)))
  return out

end CompStark.Fri.FoldWords
