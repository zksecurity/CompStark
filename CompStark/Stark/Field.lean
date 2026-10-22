/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Challenge

/-! # Field helpers of the STARK

Exponentiation by squaring, bit reversal, the points of two-adic cosets, batch inversion and
parallel chunks.
-/

@[expose] public section
namespace CompStark.Stark

/-- `x ^ n` by squaring. -/
def powF {K : Type*} [Mul K] [One K] (x : K) : Nat → K
  | 0 => 1
  | n + 1 =>
    let y := powF (x * x) ((n + 1) / 2)
    if (n + 1) % 2 = 1 then x * y else y
termination_by n => n
decreasing_by omega

/-- `powF` is the power. -/
theorem powF_eq {K : Type*} [Monoid K] (x : K) (n : Nat) : powF x n = x ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases n with
    | zero => rw [powF, pow_zero]
    | succ k =>
      rw [powF, ih _ (by omega), ← sq, ← pow_mul]
      have h := Nat.div_add_mod (k + 1) 2
      split_ifs with hp
      · rw [← pow_succ']
        exact congrArg (x ^ ·) (by omega)
      · exact congrArg (x ^ ·) (by omega)

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
def cosetPoints {F : Type} [BaseField F] (shift : F) (logN : Nat) : Array F := Id.run do
  let w := twoAdicGen logN
  let mut out := Array.emptyWithCapacity (2 ^ logN)
  let mut x := shift
  for _ in [0:2 ^ logN] do
    out := out.push x
    x := x * w
  return out

/-- The points of `shift · ⟨ω⟩` in bit-reversed order. -/
def cosetPointsBitRev {F : Type} [BaseField F] (shift : F) (logN : Nat) : Array F :=
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

/-- `f` on every element, as parallel tasks. -/
def parMap {α β : Type} (f : α → β) (xs : List α) : List β :=
  (xs.map fun x ↦ Task.spawn fun _ ↦ f x).map Task.get

theorem parMap_eq {α β : Type} (f : α → β) (xs : List α) : parMap f xs = xs.map f := by
  rw [parMap, List.map_map]
  rfl

end CompStark.Stark
