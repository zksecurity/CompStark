/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.KoalaBear.FastExt4

/-! # Field helpers of the STARK

KoalaBear's multiplicative generator `3` and two-adic generators as Plonky3 chooses them,
exponentiation, the extension field's operations with base elements, and bit reversal.
-/

@[expose] public section
namespace CompStark.Stark

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-- Plonky3's multiplicative generator of KoalaBear. -/
def gen : F := 3

/-- Plonky3's `TWO_ADIC_GENERATORS` of KoalaBear, canonical values. -/
def twoAdicTable : Array Nat := #[0x1, 0x7f000000, 0x7e010002, 0x6832fe4a, 0x8dbd69c, 0xa28f031,
  0x5c4a5b99, 0x29b75a80, 0x17668b8a, 0x27ad539b, 0x334d48c7, 0x7744959c, 0x768fc6fa, 0x303964b2,
  0x3e687d4d, 0x45a60e61, 0x6e2f4d7a, 0x163bd499, 0x6c4a8a45, 0x143ef899, 0x514ddcad, 0x484ef19b,
  0x205d63c3, 0x68e7dd49, 0x6ac49f88]

/-- The generator of the subgroup of order `2 ^ bits`, `bits ≤ 24`. -/
def twoAdicGen (bits : Nat) : F := ((twoAdicTable.getD bits 0 : Nat) : F)

/-- `x ^ n` by squaring. -/
def powF (x : F) : Nat → F
  | 0 => 1
  | n + 1 =>
    let y := powF (x * x) ((n + 1) / 2)
    if (n + 1) % 2 = 1 then x * y else y
termination_by n => n
decreasing_by omega

namespace Ext

/-- An extension element of a base element. -/
abbrev ofBase (x : F) : EF := KoalaBear.Fast.Ext4.ofBase x

/-- `x ^ n` by squaring. -/
def pow (x : EF) : Nat → EF
  | 0 => 1
  | n + 1 =>
    let y := pow (x * x) ((n + 1) / 2)
    if (n + 1) % 2 = 1 then x * y else y
termination_by n => n
decreasing_by omega

/-- `x ^ (2 ^ k)`. -/
def powTwo (x : EF) : Nat → EF
  | 0 => x
  | k + 1 => powTwo (x * x) k

/-- `X ^ e`, the basis element `e`. -/
def basis (e : Nat) : EF :=
  match e with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | _ => ⟨0, 0, 0, 1⟩

/-- The base coefficients, lowest first. -/
def coeffs (x : EF) : List F := [x.c0, x.c1, x.c2, x.c3]

end Ext

/-- The low `bits` bits of `i`, reversed. -/
def reverseBits (i bits : Nat) : Nat :=
  (List.range bits).foldl (fun acc k ↦ acc * 2 + (i >>> k) % 2) 0

end CompStark.Stark
