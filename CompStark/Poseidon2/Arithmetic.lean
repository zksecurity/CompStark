/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Arithmetic

/-! # Word arithmetic for the packed Poseidon2 rounds

Montgomery words of a `Mont32Field p`, with the field's constants taken from the instance: a
kernel over a concrete field gets them as immediates.
-/

@[expose] public section
namespace CompStark.Poseidon2
open Montgomery.Native32

variable (p : ℕ) [P : Mont32Field p]

/-- Half of a canonical word modulo the odd `p`: `x / 2` if `x` is even, `(x + p) / 2` otherwise.
Halving the Montgomery word halves the field element. -/
@[inline] def halve (x : UInt32) : UInt32 :=
  (x >>> 1) + (x &&& (1 : UInt32)) * ((P.modulus32 >>> 1) + 1)

/-- `x · 2 ^ (-n)` of a canonical Montgomery word without a product, for `K` with
`K · 2 ^ n = p - 1`: then `2 ^ (-n) ≡ -K`, so for `x = x_lo + 2 ^ n x_hi` the result is
`x_hi - K x_lo`, which lies in `(-p, p)`; a wrapping addition of `p` and an unsigned minimum make
it canonical. A field `p = r · 2 ^ s + 1` has `K = r · 2 ^ (s - n)` for every `n ≤ s`. -/
@[inline] def mulInvPow2 (n K x : UInt32) : UInt32 :=
  let d := x / (1 <<< n) - x % (1 <<< n) * K
  let e := d + P.modulus32
  if e < d then e else d

/-- The Montgomery quotient of `x · y`, left unreduced: below `2 p` when `x · y < 2 ^ 32 · p`. -/
@[inline] def mulLazy (x y : UInt32) : UInt32 :=
  let z := x.toUInt64 * y.toUInt64
  ((z + (z.toUInt32 * P.montgomeryNegInv).toUInt64 * P.modulus64) >>> 32).toUInt32

/-- `u < 2 p` reduced below `p`: `p` is added back to `u - p` under the mask of its sign bit, which
the vectorizer keeps in 32-bit lanes where an unsigned minimum after a product moves to 64-bit
ones. -/
@[inline] def reduceSign (u : UInt32) : UInt32 :=
  let d := u - P.modulus32
  d + (((0 : UInt32) - (d >>> 31)) &&& P.modulus32)

/-- The Montgomery product of words with `x · y < 2 ^ 32 · p`, reduced by sign. -/
@[inline] def mulSign (x y : UInt32) : UInt32 :=
  reduceSign p (mulLazy p x y)

/-- `x ^ 3` of a canonical word, both products left unreduced: below `2 p`. -/
@[inline] def cubeLazy (x : UInt32) : UInt32 :=
  mulLazy p (mulLazy p x x) x

/-- `x ^ 3` of a canonical word, canonical. -/
@[inline] def cubeSign (x : UInt32) : UInt32 :=
  mulSign p (mulLazy p x x) x

/-- `x ^ 7` of a canonical word as `x ^ 3 · (x ^ 2) ^ 2`, its last two products left unreduced:
below `2 p`. -/
@[inline] def pow7Lazy (x : UInt32) : UInt32 :=
  let x2 := mulSign p x x
  mulLazy p (mulSign p x2 x) (mulLazy p x2 x2)

/-- `x ^ 7` of a canonical word, canonical. -/
@[inline] def pow7Sign (x : UInt32) : UInt32 :=
  let x2 := mulSign p x x
  mulSign p (mulSign p x2 x) (mulLazy p x2 x2)

end CompStark.Poseidon2
