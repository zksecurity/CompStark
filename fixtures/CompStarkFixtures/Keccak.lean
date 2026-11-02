/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Stark.Air

/-! # Plonky3's Keccak AIR

Plonky3's `KeccakAir` (`keccak-air` at revision `a4982ec`) as a CompStark AIR, constraint for
constraint in Plonky3's emission order. A fixture of the tests and benchmarks, not part of the
library: its fingerprint matches Plonky3's (`tests/data`). Its traces are Plonky3's, as data
(`tests/data/keccak_example_6_trace.txt`); Clean generates them in the keccak-air showcase of its
CompStark backend.

The trace has 2633 columns and proves one Keccak-f permutation per 24 rows, one round per row:
the round flags, the export flag, the preimage and the round's input `A` as 16-bit limbs, the
column parities `C` and `C'` as bits, `A'` after θ as bits, `A''` after ρ, π and χ as limbs, the
bits of `A''[0, 0]`, and the limbs of `A'''[0, 0]` after ι. Lanes are indexed `y`-major, as in
Plonky3's `KeccakCols`.
-/

namespace CompStark.Fixtures.Keccak
open CompStark.Stark

/-- The rotation offsets `R[x][y]`. -/
def R : Array (Array Nat) := #[#[0, 36, 3, 41, 18], #[1, 44, 10, 45, 2], #[62, 6, 43, 15, 61],
  #[28, 55, 25, 21, 56], #[27, 20, 39, 8, 14]]

/-- The round constants. -/
def RC : Array UInt64 := #[0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
  0x8000000080008000, 0x000000000000808B, 0x0000000080000001, 0x8000000080008081,
  0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009,
  0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
  0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A,
  0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001,
  0x8000000080008008]

/-! ### Columns -/

/-- The export flag. -/
def exportCol : Nat := 24
/-- Limb `l` of lane `(x, y)` of the preimage. -/
def preimageCol (y x l : Nat) : Nat := 25 + (y * 5 + x) * 4 + l
/-- Limb `l` of lane `(x, y)` of the round's input `A`. -/
def aCol (y x l : Nat) : Nat := 125 + (y * 5 + x) * 4 + l
/-- Bit `z` of `C[x]`. -/
def cCol (x z : Nat) : Nat := 225 + x * 64 + z
/-- Bit `z` of `C'[x]`. -/
def cPrimeCol (x z : Nat) : Nat := 545 + x * 64 + z
/-- Bit `z` of lane `(x, y)` of `A'`. -/
def aPrimeCol (y x z : Nat) : Nat := 865 + (y * 5 + x) * 64 + z
/-- Limb `l` of lane `(x, y)` of `A''`. -/
def aPrimePrimeCol (y x l : Nat) : Nat := 2465 + (y * 5 + x) * 4 + l
/-- Bit `z` of `A''[0, 0]`. -/
def aPrimePrime00BitCol (z : Nat) : Nat := 2565 + z
/-- Limb `l` of `A'''[0, 0]`. -/
def aPrimePrimePrime00Col (l : Nat) : Nat := 2629 + l
/-- The trace's width. -/
def width : Nat := 2633

/-- Bit `z` of lane `(x, y)` of `B`, which is `A'` rotated (Plonky3's `b`). -/
def bCol (x y z : Nat) : Nat :=
  let a := (x + 3 * y) % 5
  let rot := (R.getD a #[]).getD x 0
  aPrimeCol x a ((z + 64 - rot) % 64)

/-- Limb `l` of lane `(x, y)` of `A'''`: `A''`, except at `(0, 0)`. -/
def aPrimePrimePrimeCol (y x l : Nat) : Nat :=
  if y = 0 ∧ x = 0 then aPrimePrimePrime00Col l else aPrimePrimeCol y x l

/-! ### Constraints -/

variable {F : Type} [NatCast F]

def c (n : Nat) : Expr F := .const (n : F)
def cur (i : Nat) : Expr F := .cur i
def nxt (i : Nat) : Expr F := .next i
/-- Plonky3's `xor` of two bits. -/
def xor (a b : Expr F) : Expr F := a + b - a * (c 2 * b)
/-- Plonky3's `andn` of two bits. -/
def andn (a b : Expr F) : Expr F := (c 1 - a) * b
/-- Plonky3's `assert_bool`. -/
def boolCheck (x : Expr F) : Expr F := x * (x - c 1)
/-- `Σ bit(16 limb + i) 2^i` over a limb's 16 bits, by Horner from the top bit (Plonky3's
`pack_bits_le`). -/
def limbOf (bit : Nat → Expr F) (limb : Nat) : Expr F :=
  (List.range 15).foldl (fun acc k ↦ c 2 * acc + bit (limb * 16 + 14 - k)) (bit (limb * 16 + 15))

/-- `f i j` for `i, j < 5`, `i` outer. -/
def grid {α : Type} (f : Nat → Nat → List α) : List α :=
  (List.range 5).flatMap fun i ↦ (List.range 5).flatMap fun j ↦ f i j
/-- `f l` for the four limbs. -/
def limbs {α : Type} (f : Nat → α) : List α := (List.range 4).map f

/-- The constraints, in Plonky3's order. -/
def constraints : List (Expr F) :=
  let notLast : Expr F := .isTransition * (c 1 - cur 23)
  let flags := [.isFirstRow * (cur 0 - c 1)] ++
    (List.range 23).map (fun i ↦ .isFirstRow * cur (i + 1)) ++
    (List.range 24).map fun i ↦ .isTransition * (cur i - nxt ((i + 1) % 24))
  let firstPreimage := grid fun y x ↦ limbs fun l ↦
    cur 0 * (cur (preimageCol y x l) - cur (aCol y x l))
  let samePreimage := grid fun y x ↦ limbs fun l ↦
    notLast * (cur (preimageCol y x l) - nxt (preimageCol y x l))
  let exportFlag := [boolCheck (cur exportCol), (c 1 - cur 23) * cur exportCol]
  let cs := (List.range 5).flatMap fun x ↦
    (List.range 64).map (fun z ↦ boolCheck (cur (cCol x z))) ++
    (List.range 64).map fun z ↦ cur (cPrimeCol x z) -
      xor (xor (cur (cCol x z)) (cur (cCol ((x + 4) % 5) z)))
        (cur (cCol ((x + 1) % 5) ((z + 63) % 64)))
  let aPrimes := (List.range 5).flatMap fun x ↦
    let cxc (z : Nat) : Expr F := xor (cur (cCol x z)) (cur (cPrimeCol x z))
    (List.range 5).flatMap fun y ↦
      (List.range 64).map (fun z ↦ boolCheck (cur (aPrimeCol y x z))) ++
      limbs fun l ↦ limbOf (fun z ↦ xor (cur (aPrimeCol y x z)) (cxc z)) l - cur (aCol y x l)
  let parity := (List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
    let sum := (List.range 4).foldl (fun s y ↦ s + cur (aPrimeCol (y + 1) x z))
      (cur (aPrimeCol 0 x z))
    let diff := sum - cur (cPrimeCol x z)
    diff * (diff - c 2) * (diff - c 4)
  let chi := grid fun y x ↦ limbs fun l ↦
    limbOf (fun z ↦ xor (andn (cur (bCol ((x + 1) % 5) y z)) (cur (bCol ((x + 2) % 5) y z)))
      (cur (bCol x y z))) l - cur (aPrimePrimeCol y x l)
  let bits := (List.range 64).map (fun z ↦ boolCheck (cur (aPrimePrime00BitCol z))) ++
    limbs fun l ↦ limbOf (fun z ↦ cur (aPrimePrime00BitCol z)) l - cur (aPrimePrimeCol 0 0 l)
  let rcBit (i : Nat) : Expr F :=
    match (List.range 24).filter (fun r ↦ ((RC.getD r 0).toNat).testBit i) with
    | [] => c 0
    | r :: rs => rs.foldl (fun s r ↦ s + cur r) (cur r)
  let iota := limbs fun l ↦
    limbOf (fun z ↦ xor (rcBit z) (cur (aPrimePrime00BitCol z))) l - cur (aPrimePrimePrime00Col l)
  let output := (List.range 5).flatMap fun x ↦ (List.range 5).flatMap fun y ↦
    limbs fun l ↦ notLast * (cur (aPrimePrimePrimeCol y x l) - nxt (aCol y x l))
  flags ++ firstPreimage ++ samePreimage ++ exportFlag ++ cs ++ aPrimes ++ parity ++ chi ++ bits ++
    iota ++ output

/-- Plonky3's `KeccakAir`. -/
def air : Air F where
  width := width
  numPublicValues := 0
  constraints := constraints

end CompStark.Fixtures.Keccak
