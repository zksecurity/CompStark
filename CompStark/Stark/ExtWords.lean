/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Words
public import CompStark.Stark.Field

/-! # Vectors of extension elements

Vectors over KoalaBear's quartic extension `F[X] / (X⁴ - 3)` as four planes of packed Montgomery
words, one per coordinate, so that every operation is a few vectorized passes over base-field
words and allocates no extension element.

`invDenoms z xs` gives `1 / (z - x)` for base points `x` without extension inversions. With `σ`
ranging over the automorphisms `X ↦ ζᵏ X`, `ζ` of order 4, `1 / (z - x)` is
`∏_{k ≠ 0} (σₖ z - x)` over the norm `∏ₖ (σₖ z - x)`: a cubic in `x` with extension coefficients
over a quartic in `x` with base coefficients, so a row costs base-field products and one shared
base-field batch inversion.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Words
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write zeroWords)

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- `n` extension elements as four coordinate planes of words. -/
structure EVec where
  n : Nat
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  c3 : ByteArray

namespace EVec

/-- A field element from a word. -/
@[inline] def ofW (w : UInt32) : F := CompPoly.CPolynomial.NTTFast.Packed.ofWord w

/-- Element `i`. -/
def get (v : EVec) (i : Nat) : EF :=
  ⟨ofW (read v.c0 i), ofW (read v.c1 i), ofW (read v.c2 i), ofW (read v.c3 i)⟩

/-- The planes of an array. -/
def ofArray (xs : Array EF) : EVec :=
  let enc := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
  ⟨xs.size, enc (xs.map (·.c0)), enc (xs.map (·.c1)), enc (xs.map (·.c2)), enc (xs.map (·.c3))⟩

/-- The elements. -/
def toArray (v : EVec) : Array EF := Array.ofFn (n := v.n) fun i ↦ v.get i

/-- Every plane holds `n` indexable words. -/
def fits (v : EVec) : Bool :=
  [v.c0, v.c1, v.c2, v.c3].all fun c ↦ c.size == 4 * v.n && c.size < USize.size

/-- The elements, decoded without bounds. -/
def decode (v : EVec) : Array EF :=
  let d (c : ByteArray) : Array F := CompPoly.PackedRepr.decode c
  Array.ofFn (n := v.n) fun i ↦
    ⟨(d v.c0).getD i 0, (d v.c1).getD i 0, (d v.c2).getD i 0, (d v.c3).getD i 0⟩

/-- Zeros. -/
def zeros (n : Nat) : EVec := ⟨n, zeroWords n, zeroWords n, zeroWords n, zeroWords n⟩

def add (a b : EVec) : EVec :=
  ⟨a.n, addWords a.c0 b.c0 a.n, addWords a.c1 b.c1 a.n, addWords a.c2 b.c2 a.n,
    addWords a.c3 b.c3 a.n⟩

def sub (a b : EVec) : EVec :=
  ⟨a.n, subWords a.c0 b.c0 a.n, subWords a.c1 b.c1 a.n, subWords a.c2 b.c2 a.n,
    subWords a.c3 b.c3 a.n⟩

/-- `s - a` for an extension scalar `s`. -/
def rsub (s : EF) (a : EVec) : EVec :=
  ⟨a.n, subWords (replicateWord s.c0.val a.n) a.c0 a.n,
    subWords (replicateWord s.c1.val a.n) a.c1 a.n,
    subWords (replicateWord s.c2.val a.n) a.c2 a.n,
    subWords (replicateWord s.c3.val a.n) a.c3 a.n⟩

/-- Every element times a base vector `b`. -/
def mulBase (a : EVec) (b : ByteArray) : EVec :=
  ⟨a.n, mulWords a.c0 b a.n, mulWords a.c1 b a.n, mulWords a.c2 b a.n, mulWords a.c3 b a.n⟩

/-- `∑ⱼ planes[j] · s[j]` for scalar words `s`. -/
def combine (n : Nat) (terms : List (ByteArray × UInt32)) : ByteArray :=
  terms.foldl (fun acc (p, s) ↦ mulAddWords acc p s n) (zeroWords n)

/-- Every element times an extension scalar `s`: with `X⁴ = 3`,
`(a s)₀ = a₀s₀ + 3 (a₁s₃ + a₂s₂ + a₃s₁)` and so on. -/
def smul (a : EVec) (s : EF) : EVec :=
  let t (x : F) : UInt32 := (3 * x).val
  ⟨a.n, combine a.n [(a.c0, s.c0.val), (a.c1, t s.c3), (a.c2, t s.c2), (a.c3, t s.c1)],
    combine a.n [(a.c0, s.c1.val), (a.c1, s.c0.val), (a.c2, t s.c3), (a.c3, t s.c2)],
    combine a.n [(a.c0, s.c2.val), (a.c1, s.c1.val), (a.c2, s.c0.val), (a.c3, t s.c3)],
    combine a.n [(a.c0, s.c3.val), (a.c1, s.c2.val), (a.c2, s.c1.val), (a.c3, s.c0.val)]⟩

/-- `3 x`. -/
def triple (x : ByteArray) (n : Nat) : ByteArray := addWords (addWords x x n) x n

/-- Elementwise products. -/
def mul (a b : EVec) : EVec :=
  let n := a.n
  let m (x y : ByteArray) := mulWords x y n
  let s (xs : List ByteArray) := xs.foldl (fun acc x ↦ addWords acc x n) (zeroWords n)
  ⟨n, addWords (m a.c0 b.c0) (triple (s [m a.c1 b.c3, m a.c2 b.c2, m a.c3 b.c1]) n) n,
    addWords (s [m a.c0 b.c1, m a.c1 b.c0]) (triple (s [m a.c2 b.c3, m a.c3 b.c2]) n) n,
    addWords (s [m a.c0 b.c2, m a.c1 b.c1, m a.c2 b.c0]) (triple (m a.c3 b.c3) n) n,
    s [m a.c0 b.c3, m a.c1 b.c2, m a.c2 b.c1, m a.c3 b.c0]⟩

end EVec

/-- The inverses of words `i0, …, i0 + len - 1` of `a`, with one inversion, by prefix products. -/
def batchInvRange (a : @& ByteArray) (i0 len : Nat) : ByteArray := Id.run do
  let mut pre := zeroWords len
  let mut acc : UInt32 := (1 : F).val
  for k in [0:len] do
    pre := write pre k acc
    acc := mul acc (read a (i0 + k))
  let mut inv := (EVec.ofW acc)⁻¹.val
  let mut out := zeroWords len
  for k in [0:len] do
    let i := len - 1 - k
    out := write out i (mul inv (read pre i))
    inv := mul inv (read a (i0 + i))
  return out

/-- The inverses of the first `n` words of `a`, by parallel ranges. -/
def batchInvWords (a : ByteArray) (n : Nat) : ByteArray :=
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    batchInvRange a (k * size) (if k + 1 = parts then n - k * size else size)
  ts.foldl (fun acc t ↦ acc ++ t.get) ByteArray.empty

/-- `1 / (z - x)` for the `n` base points `xs`, by the norm (see the module docs). -/
def invDenoms (z : EF) (xs : ByteArray) (n : Nat) : EVec :=
  let zeta := twoAdicGen 2
  let conj (k : Nat) : EF :=
    ⟨z.c0, powF zeta k * z.c1, powF zeta (2 * k) * z.c2, powF zeta (3 * k) * z.c3⟩
  let s1 := conj 1
  let s2 := conj 2
  let s3 := conj 3
  let e1 := s1 + s2 + s3
  let e2 := s1 * s2 + s1 * s3 + s2 * s3
  let e3 := s1 * s2 * s3
  -- The norm `x⁴ - E₁x³ + E₂x² - E₃x + E₄` has base coefficients.
  let E1 := (z + e1).c0
  let E2 := (e2 + z * e1).c0
  let E3 := (e3 + z * e2).c0
  let E4 := (z * e3).c0
  let x2 := mulWords xs xs n
  let x3 := mulWords x2 xs n
  let x4 := mulWords x2 x2 n
  let norm := mulAddWords (mulAddWords (mulAddWords (addWords x4
    (replicateWord E4.val n) n) x3 (-E1).val n) x2 E2.val n) xs (-E3).val n
  let invN := batchInvWords norm n
  -- `∏_{k ≠ 0} (σₖ z - x) = -x³ + e₁x² - e₂x + e₃`, coordinate by coordinate.
  let q (c : EF → F) (lead : Bool) : ByteArray :=
    let base := mulAddWords (mulAddWords (replicateWord (c e3).val n) x2 (c e1).val n) xs
      (-(c e2)).val n
    let p := if lead then mulAddWords base x3 (-1 : F).val n else base
    mulWords p invN n
  ⟨n, q (·.c0) true, q (·.c1) false, q (·.c2) false, q (·.c3) false⟩

end CompStark.Stark
