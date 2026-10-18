/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Hash.Sponge
public import CompPoly.Fields.KoalaBear.FastExt4

/-! # The duplex challenger

Plonky3's `DuplexChallenger`, the Fiat–Shamir transcript of its STARK prover and verifier:

* Observed elements queue in an input buffer and clear the output buffer; a full buffer of `rate`
  elements overwrites the first coordinates of the sponge state, which is then permuted, and the
  first `rate` coordinates become the output buffer.
* A sample permutes first if there is pending input or no output left, then takes the last element
  of the output buffer.
* Extension elements are observed and sampled coefficient by coefficient, lowest first.
* `sampleBits` keeps the low bits of a sample's canonical value. A grinding witness `w` for `bits`
  is one whose observation makes the next `sampleBits bits` zero; `grind` finds the smallest.
-/

@[expose] public section
namespace CompStark

/-- A duplex sponge over `F`: the permutation of a width-`width` state, the rate, and the canonical
value of an element. -/
structure Duplex (F : Type*) (width : Nat) where
  perm : Vector F width → Vector F width
  rate : Nat
  canon : F → Nat

/-- The state of a duplex challenger. -/
structure Challenger (F : Type*) (width : Nat) where
  state : Vector F width
  input : Array F
  output : Array F

namespace Challenger

variable {F : Type*} [Zero F] {width : Nat} (D : Duplex F width)

/-- The challenger with a zero state and empty buffers. -/
def init : Challenger F width := ⟨Vector.replicate width 0, #[], #[]⟩

/-- Overwrite the state with the input, permute, and refill the output buffer. -/
def duplexing (c : Challenger F width) : Challenger F width :=
  let s := D.perm (Hash.overwrite c.state c.input.toList)
  ⟨s, #[], (s.toArray.extract 0 D.rate)⟩

/-- Observe one element. -/
def observe (c : Challenger F width) (x : F) : Challenger F width :=
  let c := { c with input := c.input.push x, output := #[] }
  if c.input.size = D.rate then duplexing D c else c

/-- Observe a list of elements in order. -/
def observeList (c : Challenger F width) (xs : List F) : Challenger F width :=
  xs.foldl (observe D) c

/-- Sample one element. -/
def sample (c : Challenger F width) : F × Challenger F width :=
  let c := if !c.input.isEmpty || c.output.isEmpty then duplexing D c else c
  (c.output.back?.getD 0, { c with output := c.output.pop })

/-- Sample the low `bits` bits of an element's canonical value. -/
def sampleBits (c : Challenger F width) (bits : Nat) : Nat × Challenger F width :=
  let (x, c) := sample D c
  (D.canon x % 2 ^ bits, c)

/-- Observe a grinding witness and check that the next `bits` sampled bits are zero. -/
def checkWitness (c : Challenger F width) (bits : Nat) (w : F) : Bool × Challenger F width :=
  if bits = 0 then (true, c)
  else
    let (b, c) := sampleBits D (observe D c w) bits
    (b == 0, c)

end Challenger

namespace KoalaBear

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "EF" => _root_.KoalaBear.Fast.Ext4

/-- Plonky3's `DuplexChallenger<KoalaBear, Poseidon2KoalaBear<24>, 24, 16>`. -/
def duplex : Duplex F 24 where
  perm := Poseidon2.permute (Poseidon2.KoalaBear.width24 F)
  rate := 16
  canon := Montgomery.Native32.FastField.toNat

/-- The transcript of the KoalaBear STARK. -/
abbrev Transcript := Challenger F 24

namespace Transcript

/-- The empty transcript. -/
def init : Transcript := Challenger.init

/-- Observe one base element. -/
def observe (c : Transcript) (x : F) : Transcript := Challenger.observe duplex c x

/-- Observe base elements in order. -/
def observeList (c : Transcript) (xs : List F) : Transcript := Challenger.observeList duplex c xs

/-- Observe an extension element, lowest coefficient first. -/
def observeExt (c : Transcript) (x : EF) : Transcript := observeList c [x.c0, x.c1, x.c2, x.c3]

/-- Observe extension elements in order. -/
def observeExts (c : Transcript) (xs : List EF) : Transcript := xs.foldl observeExt c

/-- Sample a base element. -/
def sample (c : Transcript) : F × Transcript := Challenger.sample duplex c

/-- Sample an extension element, lowest coefficient first. -/
def sampleExt (c : Transcript) : EF × Transcript :=
  let (a, c) := sample c
  let (b, c) := sample c
  let (d, c) := sample c
  let (e, c) := sample c
  (⟨a, b, d, e⟩, c)

/-- Sample `bits` low bits. -/
def sampleBits (c : Transcript) (bits : Nat) : Nat × Transcript :=
  Challenger.sampleBits duplex c bits

/-- Check a grinding witness. -/
def checkWitness (c : Transcript) (bits : Nat) (w : F) : Bool × Transcript :=
  Challenger.checkWitness duplex c bits w

/-- The smallest grinding witness for `bits` below `bound`, by search from `n`. -/
def grindFrom (c : Transcript) (bits : Nat) : Nat → Nat → F
  | 0, _ => 0
  | fuel + 1, n =>
    let w := (n : F)
    if (checkWitness c bits w).1 then w else grindFrom c bits fuel (n + 1)

/-- The smallest grinding witness for `bits`, and the transcript after observing it. -/
def grind (c : Transcript) (bits : Nat) : F × Transcript :=
  if bits = 0 then (0, c)
  else
    let w := grindFrom c bits _root_.KoalaBear.fieldSize 0
    (w, (checkWitness c bits w).2)

end Transcript
end KoalaBear
end CompStark
