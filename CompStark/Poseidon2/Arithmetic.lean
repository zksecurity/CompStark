/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Arithmetic

/-! # Montgomery multiplication for vector lanes

`mulHi` is Montgomery multiplication in the signed form: with `m = (x y mod 2 ^ 32) · p⁻¹`, the
low halves of `x y` and `m p` agree, so `x y R⁻¹ ≡ hi (x y) - hi (m p)`, which lies in `(-p, p)`.
A wrapping subtraction and an unsigned minimum bring it into `[0, p)`, all in 32-bit lanes.
-/

@[expose] public section
namespace CompStark.Poseidon2

/-- Montgomery product of canonical words, in 32-bit lanes. -/
@[inline] def mulHi (x y : UInt32) : UInt32 :=
  let z := x.toUInt64 * y.toUInt64
  let m := z.toUInt32 * 0x81000001
  let d := (z >>> 32).toUInt32 - ((m.toUInt64 * 0x7f000001) >>> 32).toUInt32
  let e := d + 0x7f000001
  if e < d then e else d

/-- Half of a canonical word modulo `p`: `x / 2` if `x` is even, `(x + p) / 2` otherwise. Halving
the Montgomery word halves the field element. -/
@[inline] def halve (x : UInt32) : UInt32 :=
  (x >>> 1) + (x &&& 1) * 0x3f800001

end CompStark.Poseidon2
