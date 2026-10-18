/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Packed

/-! # Vectors of Montgomery words

Elementwise sums, differences, products and multiply-adds of KoalaBear vectors stored as packed
Montgomery words. Whole blocks of sixteen words go through straight-line kernels that the C
compiler vectorizes, the rest word by word.
-/

@[expose] public section
namespace CompStark.Words
open CompStark.Poseidon2.Packed (Fits inBounds)
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset read write write16U zeroWords)

/-- Word `i + k`, `k ≤ 15`, of a buffer whose words `i, …, i + 15` fit. -/
@[inline] def rd (a : @& ByteArray) (i : USize) (k : Nat) (h : Fits a i 15)
    (hk : k ≤ 15 := by decide) : UInt32 :=
  readUOffset a i k.toUSize (inBounds h k.toUSize (by
    rw [USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]; exact hk))

/-- Words `i, …, i + 15` of `a + b`, stored from word `i` of `out`. -/
@[noinline] def add16 (a b : @& ByteArray) (i : USize) (out : ByteArray)
    (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := add (rd a i 0 ha) (rd b i 0 hb)
  let x1 := add (rd a i 1 ha) (rd b i 1 hb)
  let x2 := add (rd a i 2 ha) (rd b i 2 hb)
  let x3 := add (rd a i 3 ha) (rd b i 3 hb)
  let x4 := add (rd a i 4 ha) (rd b i 4 hb)
  let x5 := add (rd a i 5 ha) (rd b i 5 hb)
  let x6 := add (rd a i 6 ha) (rd b i 6 hb)
  let x7 := add (rd a i 7 ha) (rd b i 7 hb)
  let x8 := add (rd a i 8 ha) (rd b i 8 hb)
  let x9 := add (rd a i 9 ha) (rd b i 9 hb)
  let x10 := add (rd a i 10 ha) (rd b i 10 hb)
  let x11 := add (rd a i 11 ha) (rd b i 11 hb)
  let x12 := add (rd a i 12 ha) (rd b i 12 hb)
  let x13 := add (rd a i 13 ha) (rd b i 13 hb)
  let x14 := add (rd a i 14 ha) (rd b i 14 hb)
  let x15 := add (rd a i 15 ha) (rd b i 15 hb)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `i, …, i + 15` of `a - b`, stored from word `i` of `out`. -/
@[noinline] def sub16 (a b : @& ByteArray) (i : USize) (out : ByteArray)
    (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := sub (rd a i 0 ha) (rd b i 0 hb)
  let x1 := sub (rd a i 1 ha) (rd b i 1 hb)
  let x2 := sub (rd a i 2 ha) (rd b i 2 hb)
  let x3 := sub (rd a i 3 ha) (rd b i 3 hb)
  let x4 := sub (rd a i 4 ha) (rd b i 4 hb)
  let x5 := sub (rd a i 5 ha) (rd b i 5 hb)
  let x6 := sub (rd a i 6 ha) (rd b i 6 hb)
  let x7 := sub (rd a i 7 ha) (rd b i 7 hb)
  let x8 := sub (rd a i 8 ha) (rd b i 8 hb)
  let x9 := sub (rd a i 9 ha) (rd b i 9 hb)
  let x10 := sub (rd a i 10 ha) (rd b i 10 hb)
  let x11 := sub (rd a i 11 ha) (rd b i 11 hb)
  let x12 := sub (rd a i 12 ha) (rd b i 12 hb)
  let x13 := sub (rd a i 13 ha) (rd b i 13 hb)
  let x14 := sub (rd a i 14 ha) (rd b i 14 hb)
  let x15 := sub (rd a i 15 ha) (rd b i 15 hb)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `i, …, i + 15` of `a · b`, stored from word `i` of `out`. -/
@[noinline] def mul16 (a b : @& ByteArray) (i : USize) (out : ByteArray)
    (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := mul (rd a i 0 ha) (rd b i 0 hb)
  let x1 := mul (rd a i 1 ha) (rd b i 1 hb)
  let x2 := mul (rd a i 2 ha) (rd b i 2 hb)
  let x3 := mul (rd a i 3 ha) (rd b i 3 hb)
  let x4 := mul (rd a i 4 ha) (rd b i 4 hb)
  let x5 := mul (rd a i 5 ha) (rd b i 5 hb)
  let x6 := mul (rd a i 6 ha) (rd b i 6 hb)
  let x7 := mul (rd a i 7 ha) (rd b i 7 hb)
  let x8 := mul (rd a i 8 ha) (rd b i 8 hb)
  let x9 := mul (rd a i 9 ha) (rd b i 9 hb)
  let x10 := mul (rd a i 10 ha) (rd b i 10 hb)
  let x11 := mul (rd a i 11 ha) (rd b i 11 hb)
  let x12 := mul (rd a i 12 ha) (rd b i 12 hb)
  let x13 := mul (rd a i 13 ha) (rd b i 13 hb)
  let x14 := mul (rd a i 14 ha) (rd b i 14 hb)
  let x15 := mul (rd a i 15 ha) (rd b i 15 hb)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `i, …, i + 15` of `a + b · c` for a word `c`, stored from word `i` of `out`. -/
@[noinline] def mulAdd16 (a b : @& ByteArray) (c : UInt32) (i : USize) (out : ByteArray)
    (ha : Fits a i 15) (hb : Fits b i 15) : ByteArray :=
  let x0 := add (rd a i 0 ha) (mul (rd b i 0 hb) c)
  let x1 := add (rd a i 1 ha) (mul (rd b i 1 hb) c)
  let x2 := add (rd a i 2 ha) (mul (rd b i 2 hb) c)
  let x3 := add (rd a i 3 ha) (mul (rd b i 3 hb) c)
  let x4 := add (rd a i 4 ha) (mul (rd b i 4 hb) c)
  let x5 := add (rd a i 5 ha) (mul (rd b i 5 hb) c)
  let x6 := add (rd a i 6 ha) (mul (rd b i 6 hb) c)
  let x7 := add (rd a i 7 ha) (mul (rd b i 7 hb) c)
  let x8 := add (rd a i 8 ha) (mul (rd b i 8 hb) c)
  let x9 := add (rd a i 9 ha) (mul (rd b i 9 hb) c)
  let x10 := add (rd a i 10 ha) (mul (rd b i 10 hb) c)
  let x11 := add (rd a i 11 ha) (mul (rd b i 11 hb) c)
  let x12 := add (rd a i 12 ha) (mul (rd b i 12 hb) c)
  let x13 := add (rd a i 13 ha) (mul (rd b i 13 hb) c)
  let x14 := add (rd a i 14 ha) (mul (rd b i 14 hb) c)
  let x15 := add (rd a i 15 ha) (mul (rd b i 15 hb) c)
  write16U out i x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Apply a sixteen-word kernel and its word operation to words `0, …, n - 1` of `a` and `b`. -/
@[inline] def zipWords (k16 : (a b : ByteArray) → (i : USize) → ByteArray → Fits a i 15 →
    Fits b i 15 → ByteArray) (op : UInt32 → UInt32 → UInt32) (a b : @& ByteArray) (n : Nat) :
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
def addWords (a b : @& ByteArray) (n : Nat) : ByteArray := zipWords add16 add a b n

/-- `a - b` on `n` words. -/
def subWords (a b : @& ByteArray) (n : Nat) : ByteArray := zipWords sub16 sub a b n

/-- `a · b` on `n` words. -/
def mulWords (a b : @& ByteArray) (n : Nat) : ByteArray := zipWords mul16 mul a b n

/-- `a + b · c` on `n` words, for a word `c`. -/
def mulAddWords (a b : @& ByteArray) (c : UInt32) (n : Nat) : ByteArray :=
  zipWords (fun a b i out ha hb ↦ mulAdd16 a b c i out ha hb) (fun x y ↦ add x (mul y c)) a b n

/-- `n` copies of the word `c`. -/
def replicateWord (c : UInt32) (n : Nat) : ByteArray := Id.run do
  let mut out := zeroWords n
  for k in [0:n] do
    out := write out k c
  return out

/-- Words `io, …, io + 15` of `out` plus `c` times words `ib, …, ib + 15` of `b`, in place. -/
@[noinline] def mulAddInto16 (out : ByteArray) (io : USize) (b : @& ByteArray) (ib : USize)
    (c : UInt32) (hout : Fits out io 15) (hb : Fits b ib 15) : ByteArray :=
  let x0 := add (rd out io 0 hout) (mul (rd b ib 0 hb) c)
  let x1 := add (rd out io 1 hout) (mul (rd b ib 1 hb) c)
  let x2 := add (rd out io 2 hout) (mul (rd b ib 2 hb) c)
  let x3 := add (rd out io 3 hout) (mul (rd b ib 3 hb) c)
  let x4 := add (rd out io 4 hout) (mul (rd b ib 4 hb) c)
  let x5 := add (rd out io 5 hout) (mul (rd b ib 5 hb) c)
  let x6 := add (rd out io 6 hout) (mul (rd b ib 6 hb) c)
  let x7 := add (rd out io 7 hout) (mul (rd b ib 7 hb) c)
  let x8 := add (rd out io 8 hout) (mul (rd b ib 8 hb) c)
  let x9 := add (rd out io 9 hout) (mul (rd b ib 9 hb) c)
  let x10 := add (rd out io 10 hout) (mul (rd b ib 10 hb) c)
  let x11 := add (rd out io 11 hout) (mul (rd b ib 11 hb) c)
  let x12 := add (rd out io 12 hout) (mul (rd b ib 12 hb) c)
  let x13 := add (rd out io 13 hout) (mul (rd b ib 13 hb) c)
  let x14 := add (rd out io 14 hout) (mul (rd b ib 14 hb) c)
  let x15 := add (rd out io 15 hout) (mul (rd b ib 15 hb) c)
  write16U out io x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- Words `io, …, io + 15` of `out` plus the products of words `ib, …` of `b` and `ic, …` of
`c`, in place. -/
@[noinline] def dotInto16 (out : ByteArray) (io : USize) (b : @& ByteArray) (ib : USize)
    (c : @& ByteArray) (ic : USize) (hout : Fits out io 15) (hb : Fits b ib 15)
    (hc : Fits c ic 15) : ByteArray :=
  let x0 := add (rd out io 0 hout) (mul (rd b ib 0 hb) (rd c ic 0 hc))
  let x1 := add (rd out io 1 hout) (mul (rd b ib 1 hb) (rd c ic 1 hc))
  let x2 := add (rd out io 2 hout) (mul (rd b ib 2 hb) (rd c ic 2 hc))
  let x3 := add (rd out io 3 hout) (mul (rd b ib 3 hb) (rd c ic 3 hc))
  let x4 := add (rd out io 4 hout) (mul (rd b ib 4 hb) (rd c ic 4 hc))
  let x5 := add (rd out io 5 hout) (mul (rd b ib 5 hb) (rd c ic 5 hc))
  let x6 := add (rd out io 6 hout) (mul (rd b ib 6 hb) (rd c ic 6 hc))
  let x7 := add (rd out io 7 hout) (mul (rd b ib 7 hb) (rd c ic 7 hc))
  let x8 := add (rd out io 8 hout) (mul (rd b ib 8 hb) (rd c ic 8 hc))
  let x9 := add (rd out io 9 hout) (mul (rd b ib 9 hb) (rd c ic 9 hc))
  let x10 := add (rd out io 10 hout) (mul (rd b ib 10 hb) (rd c ic 10 hc))
  let x11 := add (rd out io 11 hout) (mul (rd b ib 11 hb) (rd c ic 11 hc))
  let x12 := add (rd out io 12 hout) (mul (rd b ib 12 hb) (rd c ic 12 hc))
  let x13 := add (rd out io 13 hout) (mul (rd b ib 13 hb) (rd c ic 13 hc))
  let x14 := add (rd out io 14 hout) (mul (rd b ib 14 hb) (rd c ic 14 hc))
  let x15 := add (rd out io 15 hout) (mul (rd b ib 15 hb) (rd c ic 15 hc))
  write16U out io x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- `out[k] += c · b[bo + k]` for `k < n`, in place. -/
def mulAddInto (out : ByteArray) (b : @& ByteArray) (bo : Nat) (c : UInt32) (n : Nat) :
    ByteArray := Id.run do
  let mut out := out
  for block in [:n / 16] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < out.size ∧ 4 * (bo + i + 15) + 3 < b.size ∧
        out.size < USize.size ∧ b.size < USize.size then
      out := mulAddInto16 out (USize.ofNatLT i (by omega)) b (USize.ofNatLT (bo + i) (by omega)) c
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.1, h.2.2.1⟩)
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.1, h.2.2.2⟩)
  for k in [16 * (n / 16):n] do
    out := write out k (add (read out k) (mul (read b (bo + k)) c))
  return out

/-- `∑ₖ b[bo + k] · c[k]` for `k < n`: sixteen running sums, then their total. -/
def dotAt (b : @& ByteArray) (bo : Nat) (c : @& ByteArray) (n : Nat) : UInt32 := Id.run do
  let mut acc := zeroWords 16
  for block in [:n / 16] do
    let i := 16 * block
    if h : 4 * 15 + 3 < acc.size ∧ 4 * (bo + i + 15) + 3 < b.size ∧ 4 * (i + 15) + 3 < c.size ∧
        acc.size < USize.size ∧ b.size < USize.size ∧ c.size < USize.size then
      acc := dotInto16 acc 0 b (USize.ofNatLT (bo + i) (by omega)) c (USize.ofNatLT i (by omega))
        (by simp only [Fits]; exact ⟨by simpa using h.1, h.2.2.2.1⟩)
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.1, h.2.2.2.2.1⟩)
        (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.2.1, h.2.2.2.2.2⟩)
  let mut sum : UInt32 := 0
  for k in [0:16] do
    sum := add sum (read acc k)
  for k in [16 * (n / 16):n] do
    sum := add sum (mul (read b (bo + k)) (read c k))
  return sum

end CompStark.Words
