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

end CompStark.Poseidon2
