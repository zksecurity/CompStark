/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.CoordinateMap
public import CompStark.Pcs.Encoding
public import CompStark.Pcs.Induction
public import CompStark.Pcs.Accumulated
/-! Deterministic inputs for binary-field PCS conformance and measurement. -/
@[expose] public section
namespace CompStark.Fixtures.Pcs
open BF64 CompStark.Pcs

/-- Deterministic test elements with all three limbs populated. -/
def value (i : Nat) : WordExt3 :=
  ⟨⟨UInt64.ofNat (0x123456789abcdef0 + 31 * i)⟩,
    ⟨UInt64.ofNat (0xfedcba9876543210 + i * i)⟩,
    ⟨UInt64.ofNat (0x8000000000000001 + 17 * i)⟩⟩

/-- The six shared map challenges. -/
def challenges : Vector WordExt3 6 := Vector.ofFn fun i => value (i.val + 19)

/-- Canonical little-endian bytes of consecutive extension words. -/
def bytes (values : Array WordExt3) : ByteArray :=
  values.foldl (fun output x =>
    [x.c0.val, x.c1.val, x.c2.val].foldl (fun output word =>
      (List.range 8).foldl (fun output j => output.push ((word >>> (8 * j).toUInt64).toUInt8))
        output) output) ByteArray.empty

/-- Full-limb cubic-extension messages in row-major lane and coefficient order. -/
def encodingInput (ell lanes : Nat) : BF64.Packed.Buffer (2 ^ ell * (3 * lanes)) :=
  AdditiveNTT.Packed.tabulate _ fun i =>
    let a := value (i.val / 3)
    if i.val % 3 = 0 then a.c0 else if i.val % 3 = 1 then a.c1 else a.c2


end CompStark.Fixtures.Pcs
