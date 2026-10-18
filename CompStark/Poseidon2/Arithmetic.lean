/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Arithmetic

/-! # Word arithmetic for the packed Poseidon2 rounds -/

@[expose] public section
namespace CompStark.Poseidon2

/-- Half of a canonical word modulo `p`: `x / 2` if `x` is even, `(x + p) / 2` otherwise. Halving
the Montgomery word halves the field element. -/
@[inline] def halve (x : UInt32) : UInt32 :=
  (x >>> 1) + (x &&& 1) * 0x3f800001

/-- `x · 2 ^ (-n)` of a canonical Montgomery word, `n ≤ 24`, without a product: with
`p = 127 · 2 ^ 24 + 1`, `2 ^ (-n) ≡ -127 · 2 ^ (24 - n)`, so for `x = x_lo + 2 ^ n x_hi` the
result is `x_hi - 127 · 2 ^ (24 - n) · x_lo`, which lies in `(-p, p)`; a wrapping addition of
`p` and an unsigned minimum make it canonical. -/
@[inline] def mulInvPow2 (n : UInt32) (x : UInt32) : UInt32 :=
  let d := x / (1 <<< n) - x % (1 <<< n) * (127 <<< (24 - n))
  let e := d + 0x7f000001
  if e < d then e else d

/-- The Montgomery quotient of `x · y`, left unreduced: below `2 p` when `x · y < 2 ^ 32 · p`. -/
@[inline] def mulLazy (x y : UInt32) : UInt32 :=
  let z := x.toUInt64 * y.toUInt64
  ((z + (z.toUInt32 * 0x7effffff).toUInt64 * 0x7f000001) >>> 32).toUInt32

/-- `u < 2 p` reduced below `p`: `p` is added back to `u - p` under the mask of its sign bit, which
the vectorizer keeps in 32-bit lanes where an unsigned minimum after a product moves to 64-bit
ones. -/
@[inline] def reduceSign (u : UInt32) : UInt32 :=
  let d := u - 0x7f000001
  d + (((0 : UInt32) - (d >>> 31)) &&& 0x7f000001)

/-- The Montgomery product of words with `x · y < 2 ^ 32 · p`, reduced by sign. -/
@[inline] def mulSign (x y : UInt32) : UInt32 :=
  reduceSign (mulLazy x y)

end CompStark.Poseidon2
