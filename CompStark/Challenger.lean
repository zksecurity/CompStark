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

/-- The smallest grinding witness for `bits` below `bound`, by search from `n`, checking each
candidate with `D`. -/
def grindFrom (D : Duplex F 24) (c : Challenger F 24) (bits : Nat) : Nat → Nat → F
  | 0, _ => 0
  | fuel + 1, n =>
    let w := (n : F)
    if (Challenger.checkWitness D c bits w).1 then w else grindFrom D c bits fuel (n + 1)

/-- The transcript of the KoalaBear STARK: a challenger with its duplex, and a search for the
smallest grinding witness of a state. -/
structure Transcript where
  duplex : Duplex F 24
  grinder : Challenger F 24 → Nat → F
  state : Challenger F 24

namespace Transcript

/-- The empty transcript with the duplex `D` and grinder `g`. -/
def initWith (D : Duplex F 24) (g : Challenger F 24 → Nat → F) : Transcript :=
  ⟨D, g, Challenger.init⟩

/-- The empty specification transcript: the spec permutation, and grinding by search. -/
def init : Transcript :=
  initWith KoalaBear.duplex fun c bits ↦
    grindFrom KoalaBear.duplex c bits _root_.KoalaBear.fieldSize 0

/-- Observe one base element. -/
def observe (t : Transcript) (x : F) : Transcript :=
  { t with state := Challenger.observe t.duplex t.state x }

/-- Observe base elements in order. -/
def observeList (t : Transcript) (xs : List F) : Transcript :=
  { t with state := Challenger.observeList t.duplex t.state xs }

/-- Observe an extension element, lowest coefficient first. -/
def observeExt (t : Transcript) (x : EF) : Transcript := observeList t [x.c0, x.c1, x.c2, x.c3]

/-- Observe extension elements in order. -/
def observeExts (t : Transcript) (xs : List EF) : Transcript := xs.foldl observeExt t

/-- Sample a base element. -/
def sample (t : Transcript) : F × Transcript :=
  let (x, c) := Challenger.sample t.duplex t.state
  (x, { t with state := c })

/-- Sample an extension element, lowest coefficient first. -/
def sampleExt (t : Transcript) : EF × Transcript :=
  let (a, t) := sample t
  let (b, t) := sample t
  let (d, t) := sample t
  let (e, t) := sample t
  (⟨a, b, d, e⟩, t)

/-- Sample `bits` low bits. -/
def sampleBits (t : Transcript) (bits : Nat) : Nat × Transcript :=
  let (x, c) := Challenger.sampleBits t.duplex t.state bits
  (x, { t with state := c })

/-- Check a grinding witness. -/
def checkWitness (t : Transcript) (bits : Nat) (w : F) : Bool × Transcript :=
  let (b, c) := Challenger.checkWitness t.duplex t.state bits w
  (b, { t with state := c })

/-- The grinder's witness for `bits`, and the transcript after observing it. -/
def grind (t : Transcript) (bits : Nat) : F × Transcript :=
  if bits = 0 then (0, t)
  else
    let w := t.grinder t.state bits
    (w, (checkWitness t bits w).2)

end Transcript
end KoalaBear
end CompStark
