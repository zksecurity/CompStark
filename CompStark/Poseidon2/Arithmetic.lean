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

end CompStark.Poseidon2
