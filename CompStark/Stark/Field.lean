/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Challenge

/-! # Field helpers of the STARK

KoalaBear's multiplicative generator `3` and two-adic generators as Plonky3 chooses them,
exponentiation, and bit reversal.
-/

@[expose] public section
namespace CompStark.Stark

local notation "F" => KoalaBear.Fast.Field

/-- Plonky3's multiplicative generator of KoalaBear. -/
def gen : F := 3

/-- Plonky3's `TWO_ADIC_GENERATORS` of KoalaBear, canonical values. -/
def twoAdicTable : Array Nat := #[0x1, 0x7f000000, 0x7e010002, 0x6832fe4a, 0x8dbd69c, 0xa28f031,
  0x5c4a5b99, 0x29b75a80, 0x17668b8a, 0x27ad539b, 0x334d48c7, 0x7744959c, 0x768fc6fa, 0x303964b2,
  0x3e687d4d, 0x45a60e61, 0x6e2f4d7a, 0x163bd499, 0x6c4a8a45, 0x143ef899, 0x514ddcad, 0x484ef19b,
  0x205d63c3, 0x68e7dd49, 0x6ac49f88]

/-- The generator of the subgroup of order `2 ^ bits`, `bits ≤ 24`. -/
def twoAdicGen (bits : Nat) : F := ((twoAdicTable.getD bits 0 : Nat) : F)

/-- Plonky3's two-adic generators are nonzero. -/
theorem twoAdicGen_ne_zero (bits : Nat) (h : bits ≤ 24) : twoAdicGen bits ≠ 0 := by
  have hb : 0 < twoAdicTable.getD bits 0 ∧ twoAdicTable.getD bits 0 < KoalaBear.fieldSize := by
    have : ∀ b < 25, 0 < twoAdicTable.getD b 0 ∧ twoAdicTable.getD b 0 < KoalaBear.fieldSize := by
      decide
    exact this bits (by omega)
  intro h0
  have := congrArg Montgomery.Native32.FastField.toField h0
  rw [twoAdicGen, Montgomery.Native32.toField_natCast,
    Montgomery.Native32.toField_zero, ZMod.natCast_eq_zero_iff] at this
  exact absurd (Nat.le_of_dvd hb.1 this) (by omega)

/-- `x ^ n` by squaring. -/
def powF (x : F) : Nat → F
  | 0 => 1
  | n + 1 =>
    let y := powF (x * x) ((n + 1) / 2)
    if (n + 1) % 2 = 1 then x * y else y
termination_by n => n
decreasing_by omega

/-- `acc` followed by the low `bits` bits of `i`, reversed. -/
def reverseBitsGo : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | bits + 1, i, acc => reverseBitsGo bits (i / 2) (acc * 2 + i % 2)

/-- The low `bits` bits of `i`, reversed. -/
def reverseBits (i bits : Nat) : Nat := reverseBitsGo bits i 0

/-- The bit-reversal permutation of `0, …, 2 ^ bits - 1`, built by doubling: the reversal for
`bits + 1` is the reversal for `bits` doubled, then the same plus one. -/
def bitRevPerm : Nat → Array Nat
  | 0 => #[0]
  | bits + 1 =>
    let p := bitRevPerm bits
    p.map (2 * ·) ++ p.map (2 * · + 1)

/-- `shift · ω ^ i` for `i < 2 ^ logN`, `ω` of order `2 ^ logN`. -/
def cosetPoints (shift : F) (logN : Nat) : Array F := Id.run do
  let w := twoAdicGen logN
  let mut out := Array.emptyWithCapacity (2 ^ logN)
  let mut x := shift
  for _ in [0:2 ^ logN] do
    out := out.push x
    x := x * w
  return out

/-- The points of `shift · ⟨ω⟩` in bit-reversed order. -/
def cosetPointsBitRev (shift : F) (logN : Nat) : Array F :=
  let xs := cosetPoints shift logN
  (bitRevPerm logN).map fun i ↦ xs.getD i 0

/-- The inverses of all elements with one inversion, by prefix products. Defined when no element
is zero. -/
def batchInv {K : Type*} [Mul K] [Inv K] [One K] (xs : Array K) : Array K := Id.run do
  let mut pre := Array.emptyWithCapacity xs.size
  let mut acc : K := 1
  for x in xs do
    pre := pre.push acc
    acc := acc * x
  let mut inv := acc⁻¹
  let mut out := Array.replicate xs.size (1 : K)
  for k in [0:xs.size] do
    let i := xs.size - 1 - k
    out := out.set! i (inv * pre.getD i 1)
    inv := inv * xs.getD i 1
  return out

/-- `f start len` on `parts` consecutive ranges covering `0, …, n - 1`, as parallel tasks, results
concatenated in order. -/
def parChunks {α : Type} (n parts : Nat) (f : Nat → Nat → Array α) : Array α :=
  let size := (n + parts - 1) / parts
  let ts := (Array.range parts).map fun k ↦
    Task.spawn fun _ ↦ f (k * size) (min size (n - min n (k * size)))
  ts.foldl (fun acc t ↦ acc ++ t.get) #[]

end CompStark.Stark
