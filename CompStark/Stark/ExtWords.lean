/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Words
public import CompStark.Stark.Field
public import CompStark.Mont32.Challenge

/-! # Vectors of extension elements

Vectors over the quartic extension `Ext4 p = F[X] / (X⁴ - W)` of a Montgomery field `F` as four
planes of packed Montgomery words, one per coordinate, so that every operation is a few vectorized
passes over base-field words and allocates no extension element.

`invDenoms z xs` gives `1 / (z - x)` for base points `x` without extension inversions. With `σ`
ranging over the automorphisms `X ↦ ζᵏ X`, `ζ` of order 4 (`twoAdicGen 2`), `1 / (z - x)` is
`∏_{k ≠ 0} (σₖ z - x)` over the norm `∏ₖ (σₖ z - x)`: a cubic in `x` with extension coefficients
over a quartic in `x` with base coefficients, so a row costs base-field products and one shared
base-field batch inversion.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Words
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write zeroWords)
open Montgomery.Native32

/-- `n` elements of `Ext4 p` as four coordinate planes of words. -/
structure EVec (p : ℕ) where
  n : Nat
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  c3 : ByteArray

namespace EVec

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-- A field element from a word. -/
@[inline] def ofW (w : UInt32) : F := CompPoly.CPolynomial.NTTFast.Packed.ofWord p w

/-- Element `i`. -/
def get (v : EVec p) (i : Nat) : EF :=
  ⟨ofW (read v.c0 i), ofW (read v.c1 i), ofW (read v.c2 i), ofW (read v.c3 i)⟩

/-- The planes of an array. -/
def ofArray (xs : Array EF) : EVec p :=
  let enc := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
  ⟨xs.size, enc (xs.map (·.c0)), enc (xs.map (·.c1)), enc (xs.map (·.c2)), enc (xs.map (·.c3))⟩

/-- The elements. -/
def toArray (v : EVec p) : Array EF := Array.ofFn (n := v.n) fun i ↦ v.get i

/-- Zeros. -/
def zeros (n : Nat) : EVec p := ⟨n, zeroWords n, zeroWords n, zeroWords n, zeroWords n⟩

def add (a b : EVec p) : EVec p :=
  ⟨a.n, addWords p a.c0 b.c0 a.n, addWords p a.c1 b.c1 a.n, addWords p a.c2 b.c2 a.n,
    addWords p a.c3 b.c3 a.n⟩

def sub (a b : EVec p) : EVec p :=
  ⟨a.n, subWords p a.c0 b.c0 a.n, subWords p a.c1 b.c1 a.n, subWords p a.c2 b.c2 a.n,
    subWords p a.c3 b.c3 a.n⟩

/-- `s - a` for an extension scalar `s`. -/
def rsub (s : EF) (a : EVec p) : EVec p :=
  ⟨a.n, subWords p (replicateWord s.c0.val a.n) a.c0 a.n,
    subWords p (replicateWord s.c1.val a.n) a.c1 a.n,
    subWords p (replicateWord s.c2.val a.n) a.c2 a.n,
    subWords p (replicateWord s.c3.val a.n) a.c3 a.n⟩

/-- Every element times a base vector `b`. -/
def mulBase (a : EVec p) (b : ByteArray) : EVec p :=
  ⟨a.n, mulWords p a.c0 b a.n, mulWords p a.c1 b a.n, mulWords p a.c2 b a.n, mulWords p a.c3 b a.n⟩

/-- `∑ⱼ planes[j] · s[j]` for scalar words `s`. -/
def combine (p : ℕ) [Mont32Field p] (n : Nat) (terms : List (ByteArray × UInt32)) : ByteArray :=
  terms.foldl (fun acc (x, s) ↦ mulAddWords p acc x s n) (zeroWords n)

/-- Every element times an extension scalar `s`: with `X⁴ = W`,
`(a s)₀ = a₀s₀ + W (a₁s₃ + a₂s₂ + a₃s₁)` and so on. -/
def smul [Binomial4 p] (a : EVec p) (s : EF) : EVec p :=
  let t (x : F) : UInt32 := (Binomial4.mulW x).val
  ⟨a.n, combine p a.n [(a.c0, s.c0.val), (a.c1, t s.c3), (a.c2, t s.c2), (a.c3, t s.c1)],
    combine p a.n [(a.c0, s.c1.val), (a.c1, s.c0.val), (a.c2, t s.c3), (a.c3, t s.c2)],
    combine p a.n [(a.c0, s.c2.val), (a.c1, s.c1.val), (a.c2, s.c0.val), (a.c3, t s.c3)],
    combine p a.n [(a.c0, s.c3.val), (a.c1, s.c2.val), (a.c2, s.c1.val), (a.c3, s.c0.val)]⟩

/-- Elementwise products: with `X⁴ = W`, `(a b)₀ = a₀b₀ + (a₁b₃ + a₂b₂ + a₃b₁) W` and so on, the
multiple of `W` a multiply-add. -/
def mul [Binomial4 p] (a b : EVec p) : EVec p :=
  let n := a.n
  let w := (Binomial4.W (p := p)).val
  let m (x y : ByteArray) := mulWords p x y n
  let s (xs : List ByteArray) := xs.foldl (fun acc x ↦ addWords p acc x n) (zeroWords n)
  ⟨n, mulAddWords p (m a.c0 b.c0) (s [m a.c1 b.c3, m a.c2 b.c2, m a.c3 b.c1]) w n,
    mulAddWords p (s [m a.c0 b.c1, m a.c1 b.c0]) (s [m a.c2 b.c3, m a.c3 b.c2]) w n,
    mulAddWords p (s [m a.c0 b.c2, m a.c1 b.c1, m a.c2 b.c0]) (m a.c3 b.c3) w n,
    s [m a.c0 b.c3, m a.c1 b.c2, m a.c2 b.c1, m a.c3 b.c0]⟩

end EVec

/-- The inverses of words `i0, …, i0 + len - 1` of `a`, with one inversion, by prefix products. -/
def batchInvRange (p : ℕ) [Mont32Field p] (a : @& ByteArray) (i0 len : Nat) : ByteArray :=
  Id.run do
  let mut pre := zeroWords len
  let mut acc : UInt32 := (1 : FastField p).val
  for k in [0:len] do
    pre := write pre k acc
    acc := mul p acc (read a (i0 + k))
  let mut inv := (EVec.ofW (p := p) acc)⁻¹.val
  let mut out := zeroWords len
  for k in [0:len] do
    let i := len - 1 - k
    out := write out i (mul p inv (read pre i))
    inv := mul p inv (read a (i0 + i))
  return out

/-- The inverses of the first `n` words of `a`, by parallel ranges. -/
def batchInvWords (p : ℕ) [Mont32Field p] (a : ByteArray) (n : Nat) : ByteArray :=
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    batchInvRange p a (k * size) (if k + 1 = parts then n - k * size else size)
  ts.foldl (fun acc t ↦ acc ++ t.get) ByteArray.empty

/-- `1 / (z - x)` for the `n` base points `xs`, by the norm (see the module docs). -/
def invDenoms {p : ℕ} [Mont32Field p] [Mont32BaseField p] [Binomial4 p] (z : Ext4 p)
    (xs : ByteArray) (n : Nat) : EVec p :=
  let zeta : FastField p := twoAdicGen 2
  let conj (k : Nat) : Ext4 p :=
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
  let x2 := mulWords p xs xs n
  let x3 := mulWords p x2 xs n
  let x4 := mulWords p x2 x2 n
  let norm := mulAddWords p (mulAddWords p (mulAddWords p (addWords p x4
    (replicateWord E4.val n) n) x3 (-E1).val n) x2 E2.val n) xs (-E3).val n
  let invN := batchInvWords p norm n
  -- `∏_{k ≠ 0} (σₖ z - x) = -x³ + e₁x² - e₂x + e₃`, coordinate by coordinate.
  let q (c : Ext4 p → FastField p) (lead : Bool) : ByteArray :=
    let base := mulAddWords p (mulAddWords p (replicateWord (c e3).val n) x2 (c e1).val n) xs
      (-(c e2)).val n
    let num := if lead then mulAddWords p base x3 (-1 : FastField p).val n else base
    mulWords p num invN n
  ⟨n, q (·.c0) true, q (·.c1) false, q (·.c2) false, q (·.c3) false⟩

end CompStark.Stark
