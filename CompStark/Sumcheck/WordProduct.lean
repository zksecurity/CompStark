/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompPoly.Fields.Binary.BF64.WordExt3Proofs
/-! Cubic extension multiplication through five base-field evaluations. -/
@[expose] public section
namespace CompStark.Sumcheck
open BF64

/-- Multiply a base word by the binary polynomial generator. -/
@[inline] def timesX (a : Word) : Word := ⟨Word.xtime a.val⟩

/-- Divide a base word by the binary polynomial generator. -/
@[inline] def divideX (a : Word) : Word :=
  ⟨(a.val >>> 1) ^^^ (((0 : UInt64) - (a.val &&& 1)) &&& 0x800000000000000d)⟩

/-- Inclusive binary prefix XOR over all sixty-four coordinates. -/
@[inline] def prefixXor (a : UInt64) : UInt64 :=
  let p := a ^^^ (a <<< 1)
  let p := p ^^^ (p <<< 2)
  let p := p ^^^ (p <<< 4)
  let p := p ^^^ (p <<< 8)
  let p := p ^^^ (p <<< 16)
  let p := p ^^^ (p <<< 32)
  p

/-- Divide a base word by the binary polynomial generator plus one. -/
@[inline] def divideXOne (a : Word) : Word :=
  let p := prefixXor a.val
  ⟨p ^^^ (((0 : UInt64) - (p >>> 63)) &&& 9)⟩

/-- Divide by the product of the two adjacent interpolation points. -/
@[inline] def divideDenominator (a : Word) : Word := divideXOne (divideX a)

/-- Five-product cubic-extension multiplication at zero, one, infinity, X and X+1. -/
@[inline] def extMulFive (a b : WordExt3) : WordExt3 :=
  let add := Word.add
  let mul := Word.mulMasked
  let aAtX := add a.c0 (timesX (add a.c1 (timesX a.c2)))
  let bAtX := add b.c0 (timesX (add b.c1 (timesX b.c2)))
  let c0 := mul a.c0 b.c0
  let c4 := mul a.c2 b.c2
  let atOne := mul (add (add a.c0 a.c1) a.c2) (add (add b.c0 b.c1) b.c2)
  let atX := mul aAtX bAtX
  let atXOne := mul (add (add aAtX a.c1) a.c2) (add (add bAtX b.c1) b.c2)
  let c3 := divideDenominator (add (add atX atXOne) (add atOne c0))
  let total := add (add atOne c0) c4
  let c2 := divideDenominator (add (add (add atX c0) (timesX total))
    (add (timesX (add (timesX (timesX c3)) c3)) (timesX (timesX (timesX (timesX c4))))))
  ⟨add c0 c3, add (add total c2) c4, add c2 c4⟩

end CompStark.Sumcheck
