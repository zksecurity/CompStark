/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Packed

/-! # Vectors of Montgomery words

Elementwise sums, differences, products and multiply-adds of vectors over a Montgomery field
`FastField p`, stored as packed Montgomery words. Whole blocks of sixteen words go through
straight-line kernels that the C compiler vectorizes, the rest word by word. Every function takes
the modulus `p` and is specialized for each field.
-/

@[expose] public section
namespace CompStark.Words
open CompStark.Poseidon2.Packed (Fits inBounds)
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open Montgomery.Native32 (Mont32Field)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset read write write16U zeroWords)

/-- Word `i + k`, `k ≤ 15`, of a buffer whose words `i, …, i + 15` fit. -/
@[inline] def rd (a : @& ByteArray) (i : USize) (k : Nat) (h : Fits a i 15)
    (hk : k ≤ 15 := by decide) : UInt32 :=
  readUOffset a i k.toUSize (inBounds h k.toUSize (by
    rw [USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]; exact hk))

/-- Word `i + k`, `k ≤ 63`, of a buffer whose words `i, …, i + 63` fit. -/
@[inline] def rd64 (a : @& ByteArray) (i : USize) (k : Nat) (h : Fits a i 63)
    (hk : k ≤ 63 := by decide) : UInt32 :=
  readUOffset a i k.toUSize (inBounds h k.toUSize (by
    rw [USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]; exact hk))

/-- `a b + c d + e f + g k` of canonical Montgomery words, the four products summed in 64 bits
and reduced once (`Montgomery.Native32.mulAdd4`). -/
@[inline] def mulAdd4 (p : ℕ) [P : Mont32Field p] (a b c d e f g k : UInt32) : UInt32 :=
  let z := a.toUInt64 * b.toUInt64 + c.toUInt64 * d.toUInt64 + e.toUInt64 * f.toUInt64 +
    g.toUInt64 * k.toUInt64
  let z := if z < P.modulus64 <<< 32 then z else z - P.modulus64 <<< 32
  Montgomery.Native32.reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv z

/-- Words `i, …, i + 15` of `a + b`, stored from word `i` of `out`. -/
@[noinline, specialize] def add16 (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (i : USize)
    (out : ByteArray) (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := add p (rd a i 0 ha) (rd b i 0 hb)
  let x1 := add p (rd a i 1 ha) (rd b i 1 hb)
  let x2 := add p (rd a i 2 ha) (rd b i 2 hb)
  let x3 := add p (rd a i 3 ha) (rd b i 3 hb)
  let x4 := add p (rd a i 4 ha) (rd b i 4 hb)
  let x5 := add p (rd a i 5 ha) (rd b i 5 hb)
  let x6 := add p (rd a i 6 ha) (rd b i 6 hb)
  let x7 := add p (rd a i 7 ha) (rd b i 7 hb)
  let x8 := add p (rd a i 8 ha) (rd b i 8 hb)
  let x9 := add p (rd a i 9 ha) (rd b i 9 hb)
  let x10 := add p (rd a i 10 ha) (rd b i 10 hb)
  let x11 := add p (rd a i 11 ha) (rd b i 11 hb)
  let x12 := add p (rd a i 12 ha) (rd b i 12 hb)
  let x13 := add p (rd a i 13 ha) (rd b i 13 hb)
  let x14 := add p (rd a i 14 ha) (rd b i 14 hb)
  let x15 := add p (rd a i 15 ha) (rd b i 15 hb)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `i, …, i + 15` of `a - b`, stored from word `i` of `out`. -/
@[noinline, specialize] def sub16 (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (i : USize)
    (out : ByteArray) (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := sub p (rd a i 0 ha) (rd b i 0 hb)
  let x1 := sub p (rd a i 1 ha) (rd b i 1 hb)
  let x2 := sub p (rd a i 2 ha) (rd b i 2 hb)
  let x3 := sub p (rd a i 3 ha) (rd b i 3 hb)
  let x4 := sub p (rd a i 4 ha) (rd b i 4 hb)
  let x5 := sub p (rd a i 5 ha) (rd b i 5 hb)
  let x6 := sub p (rd a i 6 ha) (rd b i 6 hb)
  let x7 := sub p (rd a i 7 ha) (rd b i 7 hb)
  let x8 := sub p (rd a i 8 ha) (rd b i 8 hb)
  let x9 := sub p (rd a i 9 ha) (rd b i 9 hb)
  let x10 := sub p (rd a i 10 ha) (rd b i 10 hb)
  let x11 := sub p (rd a i 11 ha) (rd b i 11 hb)
  let x12 := sub p (rd a i 12 ha) (rd b i 12 hb)
  let x13 := sub p (rd a i 13 ha) (rd b i 13 hb)
  let x14 := sub p (rd a i 14 ha) (rd b i 14 hb)
  let x15 := sub p (rd a i 15 ha) (rd b i 15 hb)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `i, …, i + 15` of `a · b`, stored from word `i` of `out`. -/
@[noinline, specialize] def mul16 (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (i : USize)
    (out : ByteArray) (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := mul p (rd a i 0 ha) (rd b i 0 hb)
  let x1 := mul p (rd a i 1 ha) (rd b i 1 hb)
  let x2 := mul p (rd a i 2 ha) (rd b i 2 hb)
  let x3 := mul p (rd a i 3 ha) (rd b i 3 hb)
  let x4 := mul p (rd a i 4 ha) (rd b i 4 hb)
  let x5 := mul p (rd a i 5 ha) (rd b i 5 hb)
  let x6 := mul p (rd a i 6 ha) (rd b i 6 hb)
  let x7 := mul p (rd a i 7 ha) (rd b i 7 hb)
  let x8 := mul p (rd a i 8 ha) (rd b i 8 hb)
  let x9 := mul p (rd a i 9 ha) (rd b i 9 hb)
  let x10 := mul p (rd a i 10 ha) (rd b i 10 hb)
  let x11 := mul p (rd a i 11 ha) (rd b i 11 hb)
  let x12 := mul p (rd a i 12 ha) (rd b i 12 hb)
  let x13 := mul p (rd a i 13 ha) (rd b i 13 hb)
  let x14 := mul p (rd a i 14 ha) (rd b i 14 hb)
  let x15 := mul p (rd a i 15 ha) (rd b i 15 hb)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `i, …, i + 15` of `a + b · c` for a word `c`, stored from word `i` of `out`. -/
@[noinline, specialize] def mulAdd16 (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (c : UInt32)
    (i : USize) (out : ByteArray) (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := add p (rd a i 0 ha) (mul p (rd b i 0 hb) c)
  let x1 := add p (rd a i 1 ha) (mul p (rd b i 1 hb) c)
  let x2 := add p (rd a i 2 ha) (mul p (rd b i 2 hb) c)
  let x3 := add p (rd a i 3 ha) (mul p (rd b i 3 hb) c)
  let x4 := add p (rd a i 4 ha) (mul p (rd b i 4 hb) c)
  let x5 := add p (rd a i 5 ha) (mul p (rd b i 5 hb) c)
  let x6 := add p (rd a i 6 ha) (mul p (rd b i 6 hb) c)
  let x7 := add p (rd a i 7 ha) (mul p (rd b i 7 hb) c)
  let x8 := add p (rd a i 8 ha) (mul p (rd b i 8 hb) c)
  let x9 := add p (rd a i 9 ha) (mul p (rd b i 9 hb) c)
  let x10 := add p (rd a i 10 ha) (mul p (rd b i 10 hb) c)
  let x11 := add p (rd a i 11 ha) (mul p (rd b i 11 hb) c)
  let x12 := add p (rd a i 12 ha) (mul p (rd b i 12 hb) c)
  let x13 := add p (rd a i 13 ha) (mul p (rd b i 13 hb) c)
  let x14 := add p (rd a i 14 ha) (mul p (rd b i 14 hb) c)
  let x15 := add p (rd a i 15 ha) (mul p (rd b i 15 hb) c)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Apply a sixteen-word kernel and its word operation to words `0, …, n - 1` of `a` and `b`. -/
@[inline] def zipWords
    (k16 : (a b : ByteArray) → (i : USize) → ByteArray → Fits a i 15 → Fits b i 15 → ByteArray)
        (op : UInt32 → UInt32 → UInt32) (a b : @& ByteArray) (n : Nat) :
    ByteArray := Id.run do
  let mut out := zeroWords n
  for block in [:n / 16] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < a.size ∧ 4 * (i + 15) + 3 < b.size ∧
        a.size < USize.size ∧ b.size < USize.size then
      out := k16 a b (USize.ofNatLT i (by omega)) out
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.1, h.2.2.1⟩)
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.1, h.2.2.2⟩)
  for k in [16 * (n / 16):n] do
    out := write out k (op (read a k) (read b k))
  return out

/-- `a + b` on `n` words. -/
@[specialize] def addWords (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (n : Nat) : ByteArray :=
  zipWords (add16 p) (add p) a b n

/-- `a - b` on `n` words. -/
@[specialize] def subWords (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (n : Nat) : ByteArray :=
  zipWords (sub16 p) (sub p) a b n

/-- `a · b` on `n` words. -/
@[specialize] def mulWords (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (n : Nat) : ByteArray :=
  zipWords (mul16 p) (mul p) a b n

/-- `a + b · c` on `n` words, for a word `c`. -/
@[specialize] def mulAddWords (p : ℕ) [Mont32Field p] (a b : @& ByteArray) (c : UInt32)
    (n : Nat) : ByteArray :=
  zipWords (fun a b i out ha hb ↦ mulAdd16 p a b c i out ha hb) (fun x y ↦ add p x (mul p y c))
    a b n

/-- `n` copies of the word `c`. -/
def replicateWord (c : UInt32) (n : Nat) : ByteArray := Id.run do
  let mut out := zeroWords n
  for k in [0:n] do
    out := write out k c
  return out

/-- Words `io, …, io + 15` of `out` plus `c` times words `ib, …, ib + 15` of `b`, in place. -/
@[noinline, specialize] def mulAddInto16 (p : ℕ) [Mont32Field p] (out : ByteArray) (io : USize)
    (b : @& ByteArray) (ib : USize) (c : UInt32) (hout : Fits out io 15) (hb : Fits b ib 15) :
    ByteArray :=
  let x0 := add p (rd out io 0 hout) (mul p (rd b ib 0 hb) c)
  let x1 := add p (rd out io 1 hout) (mul p (rd b ib 1 hb) c)
  let x2 := add p (rd out io 2 hout) (mul p (rd b ib 2 hb) c)
  let x3 := add p (rd out io 3 hout) (mul p (rd b ib 3 hb) c)
  let x4 := add p (rd out io 4 hout) (mul p (rd b ib 4 hb) c)
  let x5 := add p (rd out io 5 hout) (mul p (rd b ib 5 hb) c)
  let x6 := add p (rd out io 6 hout) (mul p (rd b ib 6 hb) c)
  let x7 := add p (rd out io 7 hout) (mul p (rd b ib 7 hb) c)
  let x8 := add p (rd out io 8 hout) (mul p (rd b ib 8 hb) c)
  let x9 := add p (rd out io 9 hout) (mul p (rd b ib 9 hb) c)
  let x10 := add p (rd out io 10 hout) (mul p (rd b ib 10 hb) c)
  let x11 := add p (rd out io 11 hout) (mul p (rd b ib 11 hb) c)
  let x12 := add p (rd out io 12 hout) (mul p (rd b ib 12 hb) c)
  let x13 := add p (rd out io 13 hout) (mul p (rd b ib 13 hb) c)
  let x14 := add p (rd out io 14 hout) (mul p (rd b ib 14 hb) c)
  let x15 := add p (rd out io 15 hout) (mul p (rd b ib 15 hb) c)
  write16U out io x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `io, …, io + 15` of `out` plus the four rows of words from `i0`, `i1`, `i2`, `i3` of `b`
times `c0`, `c1`, `c2`, `c3`, reduced once per word, in place. -/
@[noinline, specialize] def mulAdd4Into16 (p : ℕ) [Mont32Field p] (out : ByteArray) (io : USize)
    (b : @& ByteArray) (i0 i1 i2 i3 : USize) (c0 c1 c2 c3 : UInt32) (hout : Fits out io 15)
    (h0 : Fits b i0 15) (h1 : Fits b i1 15) (h2 : Fits b i2 15) (h3 : Fits b i3 15) :
    ByteArray :=
  let x0 := add p (rd out io 0 hout)
    (mulAdd4 p (rd b i0 0 h0) c0 (rd b i1 0 h1) c1 (rd b i2 0 h2) c2
      (rd b i3 0 h3) c3)
  let x1 := add p (rd out io 1 hout)
    (mulAdd4 p (rd b i0 1 h0) c0 (rd b i1 1 h1) c1 (rd b i2 1 h2) c2
      (rd b i3 1 h3) c3)
  let x2 := add p (rd out io 2 hout)
    (mulAdd4 p (rd b i0 2 h0) c0 (rd b i1 2 h1) c1 (rd b i2 2 h2) c2
      (rd b i3 2 h3) c3)
  let x3 := add p (rd out io 3 hout)
    (mulAdd4 p (rd b i0 3 h0) c0 (rd b i1 3 h1) c1 (rd b i2 3 h2) c2
      (rd b i3 3 h3) c3)
  let x4 := add p (rd out io 4 hout)
    (mulAdd4 p (rd b i0 4 h0) c0 (rd b i1 4 h1) c1 (rd b i2 4 h2) c2
      (rd b i3 4 h3) c3)
  let x5 := add p (rd out io 5 hout)
    (mulAdd4 p (rd b i0 5 h0) c0 (rd b i1 5 h1) c1 (rd b i2 5 h2) c2
      (rd b i3 5 h3) c3)
  let x6 := add p (rd out io 6 hout)
    (mulAdd4 p (rd b i0 6 h0) c0 (rd b i1 6 h1) c1 (rd b i2 6 h2) c2
      (rd b i3 6 h3) c3)
  let x7 := add p (rd out io 7 hout)
    (mulAdd4 p (rd b i0 7 h0) c0 (rd b i1 7 h1) c1 (rd b i2 7 h2) c2
      (rd b i3 7 h3) c3)
  let x8 := add p (rd out io 8 hout)
    (mulAdd4 p (rd b i0 8 h0) c0 (rd b i1 8 h1) c1 (rd b i2 8 h2) c2
      (rd b i3 8 h3) c3)
  let x9 := add p (rd out io 9 hout)
    (mulAdd4 p (rd b i0 9 h0) c0 (rd b i1 9 h1) c1 (rd b i2 9 h2) c2
      (rd b i3 9 h3) c3)
  let x10 := add p (rd out io 10 hout)
    (mulAdd4 p (rd b i0 10 h0) c0 (rd b i1 10 h1) c1 (rd b i2 10 h2) c2
      (rd b i3 10 h3) c3)
  let x11 := add p (rd out io 11 hout)
    (mulAdd4 p (rd b i0 11 h0) c0 (rd b i1 11 h1) c1 (rd b i2 11 h2) c2
      (rd b i3 11 h3) c3)
  let x12 := add p (rd out io 12 hout)
    (mulAdd4 p (rd b i0 12 h0) c0 (rd b i1 12 h1) c1 (rd b i2 12 h2) c2
      (rd b i3 12 h3) c3)
  let x13 := add p (rd out io 13 hout)
    (mulAdd4 p (rd b i0 13 h0) c0 (rd b i1 13 h1) c1 (rd b i2 13 h2) c2
      (rd b i3 13 h3) c3)
  let x14 := add p (rd out io 14 hout)
    (mulAdd4 p (rd b i0 14 h0) c0 (rd b i1 14 h1) c1 (rd b i2 14 h2) c2
      (rd b i3 14 h3) c3)
  let x15 := add p (rd out io 15 hout)
    (mulAdd4 p (rd b i0 15 h0) c0 (rd b i1 15 h1) c1 (rd b i2 15 h2) c2
      (rd b i3 15 h3) c3)
  write16U out io x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- The sixteen words of `out` plus, for every `t < 16`, the products of words
`ib + t, ib + 16 + t, ib + 32 + t, ib + 48 + t` of `b` and the same words from `ic` of `c`,
reduced once per word, in place. -/
@[noinline, specialize] def dot4Into16 (p : ℕ) [Mont32Field p] (out : ByteArray)
    (b : @& ByteArray) (ib : USize) (c : @& ByteArray) (ic : USize) (hout : Fits out 0 15)
    (hb : Fits b ib 63) (hc : Fits c ic 63) : ByteArray :=
  let x0 := add p (rd out 0 0 hout)
    (mulAdd4 p (rd64 b ib 0 hb) (rd64 c ic 0 hc) (rd64 b ib 16 hb) (rd64 c ic 16 hc)
      (rd64 b ib 32 hb) (rd64 c ic 32 hc) (rd64 b ib 48 hb) (rd64 c ic 48 hc))
  let x1 := add p (rd out 0 1 hout)
    (mulAdd4 p (rd64 b ib 1 hb) (rd64 c ic 1 hc) (rd64 b ib 17 hb) (rd64 c ic 17 hc)
      (rd64 b ib 33 hb) (rd64 c ic 33 hc) (rd64 b ib 49 hb) (rd64 c ic 49 hc))
  let x2 := add p (rd out 0 2 hout)
    (mulAdd4 p (rd64 b ib 2 hb) (rd64 c ic 2 hc) (rd64 b ib 18 hb) (rd64 c ic 18 hc)
      (rd64 b ib 34 hb) (rd64 c ic 34 hc) (rd64 b ib 50 hb) (rd64 c ic 50 hc))
  let x3 := add p (rd out 0 3 hout)
    (mulAdd4 p (rd64 b ib 3 hb) (rd64 c ic 3 hc) (rd64 b ib 19 hb) (rd64 c ic 19 hc)
      (rd64 b ib 35 hb) (rd64 c ic 35 hc) (rd64 b ib 51 hb) (rd64 c ic 51 hc))
  let x4 := add p (rd out 0 4 hout)
    (mulAdd4 p (rd64 b ib 4 hb) (rd64 c ic 4 hc) (rd64 b ib 20 hb) (rd64 c ic 20 hc)
      (rd64 b ib 36 hb) (rd64 c ic 36 hc) (rd64 b ib 52 hb) (rd64 c ic 52 hc))
  let x5 := add p (rd out 0 5 hout)
    (mulAdd4 p (rd64 b ib 5 hb) (rd64 c ic 5 hc) (rd64 b ib 21 hb) (rd64 c ic 21 hc)
      (rd64 b ib 37 hb) (rd64 c ic 37 hc) (rd64 b ib 53 hb) (rd64 c ic 53 hc))
  let x6 := add p (rd out 0 6 hout)
    (mulAdd4 p (rd64 b ib 6 hb) (rd64 c ic 6 hc) (rd64 b ib 22 hb) (rd64 c ic 22 hc)
      (rd64 b ib 38 hb) (rd64 c ic 38 hc) (rd64 b ib 54 hb) (rd64 c ic 54 hc))
  let x7 := add p (rd out 0 7 hout)
    (mulAdd4 p (rd64 b ib 7 hb) (rd64 c ic 7 hc) (rd64 b ib 23 hb) (rd64 c ic 23 hc)
      (rd64 b ib 39 hb) (rd64 c ic 39 hc) (rd64 b ib 55 hb) (rd64 c ic 55 hc))
  let x8 := add p (rd out 0 8 hout)
    (mulAdd4 p (rd64 b ib 8 hb) (rd64 c ic 8 hc) (rd64 b ib 24 hb) (rd64 c ic 24 hc)
      (rd64 b ib 40 hb) (rd64 c ic 40 hc) (rd64 b ib 56 hb) (rd64 c ic 56 hc))
  let x9 := add p (rd out 0 9 hout)
    (mulAdd4 p (rd64 b ib 9 hb) (rd64 c ic 9 hc) (rd64 b ib 25 hb) (rd64 c ic 25 hc)
      (rd64 b ib 41 hb) (rd64 c ic 41 hc) (rd64 b ib 57 hb) (rd64 c ic 57 hc))
  let x10 := add p (rd out 0 10 hout)
    (mulAdd4 p (rd64 b ib 10 hb) (rd64 c ic 10 hc) (rd64 b ib 26 hb) (rd64 c ic 26 hc)
      (rd64 b ib 42 hb) (rd64 c ic 42 hc) (rd64 b ib 58 hb) (rd64 c ic 58 hc))
  let x11 := add p (rd out 0 11 hout)
    (mulAdd4 p (rd64 b ib 11 hb) (rd64 c ic 11 hc) (rd64 b ib 27 hb) (rd64 c ic 27 hc)
      (rd64 b ib 43 hb) (rd64 c ic 43 hc) (rd64 b ib 59 hb) (rd64 c ic 59 hc))
  let x12 := add p (rd out 0 12 hout)
    (mulAdd4 p (rd64 b ib 12 hb) (rd64 c ic 12 hc) (rd64 b ib 28 hb) (rd64 c ic 28 hc)
      (rd64 b ib 44 hb) (rd64 c ic 44 hc) (rd64 b ib 60 hb) (rd64 c ic 60 hc))
  let x13 := add p (rd out 0 13 hout)
    (mulAdd4 p (rd64 b ib 13 hb) (rd64 c ic 13 hc) (rd64 b ib 29 hb) (rd64 c ic 29 hc)
      (rd64 b ib 45 hb) (rd64 c ic 45 hc) (rd64 b ib 61 hb) (rd64 c ic 61 hc))
  let x14 := add p (rd out 0 14 hout)
    (mulAdd4 p (rd64 b ib 14 hb) (rd64 c ic 14 hc) (rd64 b ib 30 hb) (rd64 c ic 30 hc)
      (rd64 b ib 46 hb) (rd64 c ic 46 hc) (rd64 b ib 62 hb) (rd64 c ic 62 hc))
  let x15 := add p (rd out 0 15 hout)
    (mulAdd4 p (rd64 b ib 15 hb) (rd64 c ic 15 hc) (rd64 b ib 31 hb) (rd64 c ic 31 hc)
      (rd64 b ib 47 hb) (rd64 c ic 47 hc) (rd64 b ib 63 hb) (rd64 c ic 63 hc))
  write16U out 0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- `out[k] += c · b[bo + k]` for `k < n`, in place. -/
@[specialize] def mulAddInto (p : ℕ) [Mont32Field p] (out : ByteArray) (b : @& ByteArray)
    (bo : Nat) (c : UInt32) (n : Nat) :
    ByteArray := Id.run do
  let mut out := out
  for block in [:n / 16] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < out.size ∧ 4 * (bo + i + 15) + 3 < b.size ∧
        out.size < USize.size ∧ b.size < USize.size then
      out := mulAddInto16 p out (USize.ofNatLT i (by omega)) b (USize.ofNatLT (bo + i) (by omega)) c
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.1, h.2.2.1⟩)
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.1, h.2.2.2⟩)
  for k in [16 * (n / 16):n] do
    out := write out k (add p (read out k) (mul p (read b (bo + k)) c))
  return out

/-- `out[k] += c0 · b[o0 + k] + c1 · b[o1 + k] + c2 · b[o2 + k] + c3 · b[o3 + k]` for `k < n`, in
place: four rows multiply-added at once, reduced once per word. -/
@[specialize] def mulAdd4Into (p : ℕ) [Mont32Field p] (out : ByteArray) (b : @& ByteArray)
    (o0 o1 o2 o3 : Nat) (c0 c1 c2 c3 : UInt32) (n : Nat) : ByteArray := Id.run do
  let mut out := out
  for block in [:n / 16] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < out.size ∧ 4 * (o0 + i + 15) + 3 < b.size ∧
        4 * (o1 + i + 15) + 3 < b.size ∧ 4 * (o2 + i + 15) + 3 < b.size ∧
        4 * (o3 + i + 15) + 3 < b.size ∧ out.size < USize.size ∧ b.size < USize.size then
      out := mulAdd4Into16 p out (USize.ofNatLT i (by omega)) b (USize.ofNatLT (o0 + i) (by omega))
        (USize.ofNatLT (o1 + i) (by omega)) (USize.ofNatLT (o2 + i) (by omega))
        (USize.ofNatLT (o3 + i) (by omega)) c0 c1 c2 c3
        (by simp only [Fits, USize.toNat_ofNatLT]; omega)
        (by simp only [Fits, USize.toNat_ofNatLT]; omega)
        (by simp only [Fits, USize.toNat_ofNatLT]; omega)
        (by simp only [Fits, USize.toNat_ofNatLT]; omega)
        (by simp only [Fits, USize.toNat_ofNatLT]; omega)
  for k in [16 * (n / 16):n] do
    out := write out k (add p (read out k) (mulAdd4 p (read b (o0 + k)) c0 (read b (o1 + k)) c1
      (read b (o2 + k)) c2 (read b (o3 + k)) c3))
  return out

/-- Sixteen words of the plane at `q` of `out` plus `a0 · b0[i0 + t] + a1 · b1[i1 + t] +
a2 · b2[i2 + t] + a3 · b3[i3 + t]`, reduced once per word, in place. -/
@[noinline, specialize] def mulAdd4RowsInto16 (p : ℕ) [Mont32Field p] (out : ByteArray)
    (q : USize) (b0 b1 b2 b3 : @& ByteArray) (i0 i1 i2 i3 : USize) (a0 a1 a2 a3 : UInt32)
    (hq : Fits out q 15) (h0 : Fits b0 i0 15) (h1 : Fits b1 i1 15) (h2 : Fits b2 i2 15)
    (h3 : Fits b3 i3 15) : ByteArray :=
  let y0 := add p (rd out q 0 hq)
    (mulAdd4 p (rd b0 i0 0 h0) a0 (rd b1 i1 0 h1) a1 (rd b2 i2 0 h2) a2 (rd b3 i3 0 h3) a3)
  let y1 := add p (rd out q 1 hq)
    (mulAdd4 p (rd b0 i0 1 h0) a0 (rd b1 i1 1 h1) a1 (rd b2 i2 1 h2) a2 (rd b3 i3 1 h3) a3)
  let y2 := add p (rd out q 2 hq)
    (mulAdd4 p (rd b0 i0 2 h0) a0 (rd b1 i1 2 h1) a1 (rd b2 i2 2 h2) a2 (rd b3 i3 2 h3) a3)
  let y3 := add p (rd out q 3 hq)
    (mulAdd4 p (rd b0 i0 3 h0) a0 (rd b1 i1 3 h1) a1 (rd b2 i2 3 h2) a2 (rd b3 i3 3 h3) a3)
  let y4 := add p (rd out q 4 hq)
    (mulAdd4 p (rd b0 i0 4 h0) a0 (rd b1 i1 4 h1) a1 (rd b2 i2 4 h2) a2 (rd b3 i3 4 h3) a3)
  let y5 := add p (rd out q 5 hq)
    (mulAdd4 p (rd b0 i0 5 h0) a0 (rd b1 i1 5 h1) a1 (rd b2 i2 5 h2) a2 (rd b3 i3 5 h3) a3)
  let y6 := add p (rd out q 6 hq)
    (mulAdd4 p (rd b0 i0 6 h0) a0 (rd b1 i1 6 h1) a1 (rd b2 i2 6 h2) a2 (rd b3 i3 6 h3) a3)
  let y7 := add p (rd out q 7 hq)
    (mulAdd4 p (rd b0 i0 7 h0) a0 (rd b1 i1 7 h1) a1 (rd b2 i2 7 h2) a2 (rd b3 i3 7 h3) a3)
  let y8 := add p (rd out q 8 hq)
    (mulAdd4 p (rd b0 i0 8 h0) a0 (rd b1 i1 8 h1) a1 (rd b2 i2 8 h2) a2 (rd b3 i3 8 h3) a3)
  let y9 := add p (rd out q 9 hq)
    (mulAdd4 p (rd b0 i0 9 h0) a0 (rd b1 i1 9 h1) a1 (rd b2 i2 9 h2) a2 (rd b3 i3 9 h3) a3)
  let y10 := add p (rd out q 10 hq)
    (mulAdd4 p (rd b0 i0 10 h0) a0 (rd b1 i1 10 h1) a1 (rd b2 i2 10 h2) a2 (rd b3 i3 10 h3) a3)
  let y11 := add p (rd out q 11 hq)
    (mulAdd4 p (rd b0 i0 11 h0) a0 (rd b1 i1 11 h1) a1 (rd b2 i2 11 h2) a2 (rd b3 i3 11 h3) a3)
  let y12 := add p (rd out q 12 hq)
    (mulAdd4 p (rd b0 i0 12 h0) a0 (rd b1 i1 12 h1) a1 (rd b2 i2 12 h2) a2 (rd b3 i3 12 h3) a3)
  let y13 := add p (rd out q 13 hq)
    (mulAdd4 p (rd b0 i0 13 h0) a0 (rd b1 i1 13 h1) a1 (rd b2 i2 13 h2) a2 (rd b3 i3 13 h3) a3)
  let y14 := add p (rd out q 14 hq)
    (mulAdd4 p (rd b0 i0 14 h0) a0 (rd b1 i1 14 h1) a1 (rd b2 i2 14 h2) a2 (rd b3 i3 14 h3) a3)
  let y15 := add p (rd out q 15 hq)
    (mulAdd4 p (rd b0 i0 15 h0) a0 (rd b1 i1 15 h1) a1 (rd b2 i2 15 h2) a2 (rd b3 i3 15 h3) a3)
  write16U out q y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15

theorem size_mulAdd4RowsInto16 (p : ℕ) [Mont32Field p] (out : ByteArray)
    (q : USize) (b0 b1 b2 b3 : ByteArray) (i0 i1 i2 i3 : USize) (a0 a1 a2 a3 : UInt32)
    (hq : Fits out q 15) (h0 : Fits b0 i0 15) (h1 : Fits b1 i1 15) (h2 : Fits b2 i2 15)
    (h3 : Fits b3 i3 15) :
    (mulAdd4RowsInto16 p out q b0 b1 b2 b3 i0 i1 i2 i3 a0 a1 a2 a3 hq h0 h1 h2 h3).size =
      out.size := by
  unfold mulAdd4RowsInto16
  exact CompPoly.CPolynomial.NTTFast.Packed.Native.size_storeWords ..

/-- Sixteen words of each of the four planes at `q0, q1, q2, q3` of `out`, plane `c` added
`ac0 · b0[i0 + t] + ac1 · b1[i1 + t] + ac2 · b2[i2 + t] + ac3 · b3[i3 + t]`, reduced once per
word, a plane at a time (`mulAdd4RowsInto16`). -/
@[inline] def mulAdd4x4Into16 (p : ℕ) [Mont32Field p] (out : ByteArray)
    (q0 q1 q2 q3 : USize) (b0 b1 b2 b3 : @& ByteArray) (i0 i1 i2 i3 : USize)
    (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 : UInt32)
    (hq0 : Fits out q0 15) (hq1 : Fits out q1 15) (hq2 : Fits out q2 15) (hq3 : Fits out q3 15)
    (h0 : Fits b0 i0 15) (h1 : Fits b1 i1 15) (h2 : Fits b2 i2 15) (h3 : Fits b3 i3 15) :
    ByteArray :=
  let o1 := mulAdd4RowsInto16 p out q0 b0 b1 b2 b3 i0 i1 i2 i3 a00 a01 a02 a03 hq0 h0 h1 h2 h3
  have e1 := size_mulAdd4RowsInto16 p out q0 b0 b1 b2 b3 i0 i1 i2 i3 a00 a01 a02 a03 hq0 h0 h1 h2 h3
  let o2 := mulAdd4RowsInto16 p o1 q1 b0 b1 b2 b3 i0 i1 i2 i3 a10 a11 a12 a13
    (CompStark.Poseidon2.Packed.Fits.of_size e1 hq1) h0 h1 h2 h3
  have e2 := (size_mulAdd4RowsInto16 p o1 q1 b0 b1 b2 b3 i0 i1 i2 i3 a10 a11 a12 a13
    (CompStark.Poseidon2.Packed.Fits.of_size e1 hq1) h0 h1 h2 h3).trans e1
  let o3 := mulAdd4RowsInto16 p o2 q2 b0 b1 b2 b3 i0 i1 i2 i3 a20 a21 a22 a23
    (CompStark.Poseidon2.Packed.Fits.of_size e2 hq2) h0 h1 h2 h3
  have e3 := (size_mulAdd4RowsInto16 p o2 q2 b0 b1 b2 b3 i0 i1 i2 i3 a20 a21 a22 a23
    (CompStark.Poseidon2.Packed.Fits.of_size e2 hq2) h0 h1 h2 h3).trans e2
  mulAdd4RowsInto16 p o3 q3 b0 b1 b2 b3 i0 i1 i2 i3 a30 a31 a32 a33
    (CompStark.Poseidon2.Packed.Fits.of_size e3 hq3) h0 h1 h2 h3

theorem size_mulAdd4x4Into16 (p : ℕ) [Mont32Field p] (out : ByteArray)
    (q0 q1 q2 q3 : USize) (b0 b1 b2 b3 : ByteArray) (i0 i1 i2 i3 : USize)
    (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 : UInt32)
    (hq0 : Fits out q0 15) (hq1 : Fits out q1 15) (hq2 : Fits out q2 15) (hq3 : Fits out q3 15)
    (h0 : Fits b0 i0 15) (h1 : Fits b1 i1 15) (h2 : Fits b2 i2 15) (h3 : Fits b3 i3 15) :
    (mulAdd4x4Into16 p out q0 q1 q2 q3 b0 b1 b2 b3 i0 i1 i2 i3 a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33 hq0 hq1 hq2 hq3 h0 h1 h2 h3).size = out.size := by
  simp only [mulAdd4x4Into16, size_mulAdd4RowsInto16]

/-- A sum of machine words below the machine size does not wrap. -/
theorem usize_add_toNat {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, hsize, Nat.mod_eq_of_lt h]

/-- The bounds of `k` blocks of sixteen words from word `i` of the four planes at `0, q1, q2, q3`
of `out` and of the rows at `r0, r1, r2, r3` of `b0, b1, b2, b3`. -/
abbrev Blocks4 (out b0 b1 b2 b3 : ByteArray) (q1 q2 q3 r0 r1 r2 r3 i : USize) (k : Nat) : Prop :=
  4 * (q3.toNat + i.toNat + 16 * k) ≤ out.size ∧ q1.toNat ≤ q3.toNat ∧ q2.toNat ≤ q3.toNat ∧
    out.size < USize.size ∧ 4 * (r0.toNat + i.toNat + 16 * k) ≤ b0.size ∧
    4 * (r1.toNat + i.toNat + 16 * k) ≤ b1.size ∧ 4 * (r2.toNat + i.toNat + 16 * k) ≤ b2.size ∧
    4 * (r3.toNat + i.toNat + 16 * k) ≤ b3.size ∧ b0.size < USize.size ∧ b1.size < USize.size ∧
    b2.size < USize.size ∧ b3.size < USize.size

theorem Blocks4.next {out out' b0 b1 b2 b3 : ByteArray} {q1 q2 q3 r0 r1 r2 r3 i : USize}
    {k : Nat} (h : Blocks4 out b0 b1 b2 b3 q1 q2 q3 r0 r1 r2 r3 i (k + 1))
    (hs : out'.size = out.size) :
    (i + 16).toNat = i.toNat + 16 ∧ Blocks4 out' b0 b1 b2 b3 q1 q2 q3 r0 r1 r2 r3 (i + 16) k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have e16 : (16 : USize).toNat = 16 :=
    CompPoly.CPolynomial.NTTFast.Packed.Native.usize_numeral 16 (by decide)
  have ei : (i + 16).toNat = i.toNat + 16 := by rw [usize_add_toNat (by rw [e16]; omega), e16]
  rw [ei]
  exact ⟨rfl, by omega, h2, h3, by omega, by omega, by omega, by omega, by omega, h9, h10, h11,
    h12⟩

/-- `mulAdd4x4Into16` on `k` blocks of sixteen words from word `i` of the four planes at
`0, q1, q2, q3` of `out` and of the rows at `r0, r1, r2, r3`, their bounds proved once. -/
@[specialize] def mulAddBlocks4 (p : ℕ) [Mont32Field p] (b0 b1 b2 b3 : @& ByteArray)
    (q1 q2 q3 r0 r1 r2 r3 : USize)
    (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 : UInt32) :
    (k : Nat) → (i : USize) → (out : ByteArray) →
      Blocks4 out b0 b1 b2 b3 q1 q2 q3 r0 r1 r2 r3 i k → ByteArray
  | 0, _, out, _ => out
  | k + 1, i, out, h =>
    mulAddBlocks4 p b0 b1 b2 b3 q1 q2 q3 r0 r1 r2 r3 a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22
      a23 a30 a31 a32 a33 k (i + 16)
      (mulAdd4x4Into16 p out i (q1 + i) (q2 + i) (q3 + i) b0 b1 b2 b3 (r0 + i) (r1 + i) (r2 + i)
        (r3 + i) a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33
        (by obtain ⟨h1, -, -, h4, -⟩ := h; unfold Fits; omega)
        (by obtain ⟨h1, h2, -, h4, -⟩ := h; unfold Fits; rw [usize_add_toNat (by omega)]; omega)
        (by obtain ⟨h1, -, h3, h4, -⟩ := h; unfold Fits; rw [usize_add_toNat (by omega)]; omega)
        (by obtain ⟨h1, -, -, h4, -⟩ := h; unfold Fits; rw [usize_add_toNat (by omega)]; omega)
        (by
          obtain ⟨-, -, -, -, h5, -, -, -, h9, -⟩ := h
          unfold Fits; rw [usize_add_toNat (by omega)]; omega)
        (by
          obtain ⟨-, -, -, -, -, h6, -, -, -, h10, -⟩ := h
          unfold Fits; rw [usize_add_toNat (by omega)]; omega)
        (by
          obtain ⟨-, -, -, -, -, -, h7, -, -, -, h11, -⟩ := h
          unfold Fits; rw [usize_add_toNat (by omega)]; omega)
        (by
          obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, h12⟩ := h
          unfold Fits; rw [usize_add_toNat (by omega)]; omega))
      (h.next (size_mulAdd4x4Into16 ..)).2

/-- `out[c n + k] += ac0 · b0[o0 + k] + ac1 · b1[o1 + k] + ac2 · b2[o2 + k] + ac3 · b3[o3 + k]` for
the four planes `c` of `n` words of `out` and `k < n`, in place: sixteen words of every plane at
once (`mulAddBlocks4`), then the remaining words. -/
@[specialize] def mulAdd4x4Into (p : ℕ) [Mont32Field p] (out : ByteArray)
    (b0 b1 b2 b3 : @& ByteArray) (o0 o1 o2 o3 : Nat)
    (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 : UInt32) (n : Nat) :
    ByteArray := Id.run do
  let m := 16 * (n / 16)
  let mut out := out
  if h : 4 * (3 * n + m) ≤ out.size ∧ out.size < USize.size ∧ 4 * (o0 + m) ≤ b0.size ∧
      4 * (o1 + m) ≤ b1.size ∧ 4 * (o2 + m) ≤ b2.size ∧ 4 * (o3 + m) ≤ b3.size ∧
      b0.size < USize.size ∧ b1.size < USize.size ∧ b2.size < USize.size ∧
      b3.size < USize.size then
    out := mulAddBlocks4 p b0 b1 b2 b3 (USize.ofNatLT n (by obtain ⟨h1, h2, -⟩ := h; omega))
      (USize.ofNatLT (2 * n) (by obtain ⟨h1, h2, -⟩ := h; omega))
      (USize.ofNatLT (3 * n) (by obtain ⟨h1, h2, -⟩ := h; omega))
      (USize.ofNatLT o0 (by obtain ⟨-, -, h3, -, -, -, h7, -⟩ := h; omega))
      (USize.ofNatLT o1 (by obtain ⟨-, -, -, h4, -, -, -, h8, -⟩ := h; omega))
      (USize.ofNatLT o2 (by obtain ⟨-, -, -, -, h5, -, -, -, h9, -⟩ := h; omega))
      (USize.ofNatLT o3 (by obtain ⟨-, -, -, -, -, h6, -, -, -, h10⟩ := h; omega))
      a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 (n / 16) 0 out (by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
        simp only [Blocks4, USize.toNat_ofNatLT, USize.toNat_zero]; omega)
  for k in [16 * (n / 16):n] do
    let x0 := read b0 (o0 + k)
    let x1 := read b1 (o1 + k)
    let x2 := read b2 (o2 + k)
    let x3 := read b3 (o3 + k)
    out := write out k (add p (read out k) (mulAdd4 p x0 a00 x1 a01 x2 a02 x3 a03))
    out := write out (n + k) (add p (read out (n + k)) (mulAdd4 p x0 a10 x1 a11 x2 a12 x3 a13))
    out := write out (2 * n + k)
      (add p (read out (2 * n + k)) (mulAdd4 p x0 a20 x1 a21 x2 a22 x3 a23))
    out := write out (3 * n + k)
      (add p (read out (3 * n + k)) (mulAdd4 p x0 a30 x1 a31 x2 a32 x3 a33))
  return out

theorem size_dot4Into16 (p : ℕ) [Mont32Field p] (out : ByteArray) (b : ByteArray) (ib : USize)
    (c : ByteArray) (ic : USize) (hout : Fits out 0 15) (hb : Fits b ib 63) (hc : Fits c ic 63) :
    (dot4Into16 p out b ib c ic hout hb hc).size = out.size := by
  unfold dot4Into16
  exact CompPoly.CPolynomial.NTTFast.Packed.Native.size_storeWords ..

/-- The bounds of `k` blocks of 64 words from words `ib` of `b` and `ic` of `c`, into sixteen
running sums `acc`. -/
abbrev DotBlocks (b c acc : ByteArray) (k : Nat) (ib ic : USize) : Prop :=
  4 * (ib.toNat + 64 * k) ≤ b.size ∧ 4 * (ic.toNat + 64 * k) ≤ c.size ∧ b.size < USize.size ∧
    c.size < USize.size ∧ 64 ≤ acc.size ∧ acc.size < USize.size

theorem DotBlocks.next {b c acc acc' : ByteArray} {k : Nat} {ib ic : USize}
    (h : DotBlocks b c acc (k + 1) ib ic) (hs : acc'.size = acc.size) :
    (ib + 64).toNat = ib.toNat + 64 ∧ (ic + 64).toNat = ic.toNat + 64 ∧
      DotBlocks b c acc' k (ib + 64) (ic + 64) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have e64 : (64 : USize).toNat = 64 :=
    CompPoly.CPolynomial.NTTFast.Packed.Native.usize_numeral 64 (by decide)
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have ea : (ib + 64).toNat = ib.toNat + 64 := by
    rw [USize.toNat_add, e64, hsize, Nat.mod_eq_of_lt (by omega)]
  have ec : (ic + 64).toNat = ic.toNat + 64 := by
    rw [USize.toNat_add, e64, hsize, Nat.mod_eq_of_lt (by omega)]
  exact ⟨ea, ec, by rw [ea]; omega, by rw [ec]; omega, h3, h4, by omega, by omega⟩

/-- `dot4Into16` on `k` blocks of 64 words from words `ib` of `b` and `ic` of `c`, their bounds
proved once. -/
@[specialize] def dotBlocks (p : ℕ) [Mont32Field p] (b c : @& ByteArray) :
    (k : Nat) → (ib ic : USize) → (acc : ByteArray) → DotBlocks b c acc k ib ic → ByteArray
  | 0, _, _, acc, _ => acc
  | k + 1, ib, ic, acc, h =>
    dotBlocks p b c k (ib + 64) (ic + 64)
      (dot4Into16 p acc b ib c ic (by
        obtain ⟨-, -, -, -, h5, h6⟩ := h; simp only [Fits, USize.toNat_zero]; omega)
        (by obtain ⟨h1, -, h3, -⟩ := h; unfold Fits; omega)
        (by obtain ⟨-, h2, -, h4, -⟩ := h; unfold Fits; omega))
      (h.next (size_dot4Into16 ..)).2.2

/-- `∑ₖ b[bo + k] · c[k]` for `k < n`: sixteen running sums, each adding four products reduced
once per block of 64 words (`dotBlocks`), then their total and the remaining words. -/
@[specialize] def dotAt (p : ℕ) [Mont32Field p] (b : @& ByteArray) (bo : Nat) (c : @& ByteArray)
    (n : Nat) : UInt32 := Id.run do
  let acc := if h : 4 * (bo + 64 * (n / 64)) ≤ b.size ∧ 4 * (64 * (n / 64)) ≤ c.size ∧
      b.size < USize.size ∧ c.size < USize.size then
    dotBlocks p b c (n / 64) (USize.ofNatLT bo (by obtain ⟨h1, -, h3, -⟩ := h; omega)) 0
      (zeroWords 16) (by
        obtain ⟨h1, h2, h3, h4⟩ := h
        have hz : (zeroWords 16).size = 64 := ByteArray.size_zeros _
        simp only [DotBlocks, USize.toNat_ofNatLT, USize.toNat_zero, hz]
        have := USize.le_size
        omega)
  else zeroWords 16
  let mut sum : UInt32 := 0
  for k in [0:16] do
    sum := add p sum (read acc k)
  for k in [64 * (n / 64):n] do
    sum := add p sum (mul p (read b (bo + k)) (read c k))
  return sum

end CompStark.Words
