/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Hash.Sponge
public import CompStark.Stark.Challenge

/-! # The duplex challenger

Plonky3's `DuplexChallenger`, the Fiat–Shamir transcript of its STARK prover and verifier:

* Observed elements queue in an input buffer and clear the output buffer; a full buffer of `rate`
  elements is absorbed and the sponge state permuted, and the first `rate` coordinates become the
  output buffer. Absorbing `k > 0` elements writes them to the first coordinates, zeroes the rest
  of the rate and adds `k` to the first capacity coordinate, so that inputs of different lengths
  differ (`absorbInto`).
* A sample permutes first if there is pending input or no output left, then takes the last element
  of the output buffer.
* Extension elements (`Challenge`) are observed and sampled coefficient by coefficient, lowest
  first.
* `sampleBits` keeps the low bits of a sample's canonical value. A grinding witness `w` for `bits`
  is one whose observation makes the next `sampleBits bits` zero; `grindFrom` finds the smallest.

`Transcript` is the prover's: a challenger on a duplex, with a grinder.
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

variable {F : Type*} [AddMonoidWithOne F] {width : Nat} (D : Duplex F width)

/-- The state to permute after observing `xs`: unchanged if `xs` is empty (a squeeze); otherwise
`xs` in the first coordinates, zeros up to the rate, and the first capacity coordinate plus the
length of `xs`. -/
def absorbInto (rate : Nat) (s : Vector F width) (xs : List F) : Vector F width :=
  if xs.isEmpty then s else Vector.ofFn fun i ↦
    if i.val < rate then xs.getD i.val 0
    else if i.val = rate then s[i] + (xs.length : F) else s[i]

/-- The challenger with a zero state and empty buffers. -/
def init : Challenger F width := ⟨Vector.replicate width 0, #[], #[]⟩

/-- Absorb the input, permute, and refill the output buffer. -/
def duplexing (c : Challenger F width) : Challenger F width :=
  let s := D.perm (absorbInto D.rate c.state c.input.toList)
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

/-- The smallest grinding witness for `bits` below `bound`, by search from `n`, checking each
candidate with `D`. -/
def grindFrom {F : Type} [BaseField F] {width : Nat} (D : Duplex F width) (c : Challenger F width)
    (bits : Nat) : Nat → Nat → F
  | 0, _ => 0
  | fuel + 1, n =>
    let w := (n : F)
    if (Challenger.checkWitness D c bits w).1 then w else grindFrom D c bits fuel (n + 1)

/-- The prover's transcript: a challenger with its duplex, a search for the smallest grinding
witness of a state, and whether a search has failed. Plonky3's grinder panics when it finds no
witness; the flag records that instead, and no proof observes it. -/
structure Transcript (F : Type) (width : Nat) where
  duplex : Duplex F width
  grinder : Challenger F width → Nat → F
  state : Challenger F width
  grindFailed : Bool

namespace Transcript

variable {F : Type} [BaseField F] {width : Nat}

/-- The empty transcript with the duplex `D` and grinder `g`. -/
def initWith (D : Duplex F width) (g : Challenger F width → Nat → F) : Transcript F width :=
  ⟨D, g, Challenger.init, false⟩

/-- Observe one base element. -/
def observe (t : Transcript F width) (x : F) : Transcript F width :=
  { t with state := Challenger.observe t.duplex t.state x }

/-- Observe base elements in order. -/
def observeList (t : Transcript F width) (xs : List F) : Transcript F width :=
  { t with state := Challenger.observeList t.duplex t.state xs }

variable {EF : Type} [Challenge F EF]

/-- Observe an extension element, lowest coefficient first. -/
def observeExt (t : Transcript F width) (x : EF) : Transcript F width :=
  observeList t (Challenge.coeffs x)

/-- Observe extension elements in order. -/
def observeExts (t : Transcript F width) (xs : List EF) : Transcript F width :=
  xs.foldl observeExt t

/-- Sample a base element. -/
def sample (t : Transcript F width) : F × Transcript F width :=
  let (x, c) := Challenger.sample t.duplex t.state
  (x, { t with state := c })

/-- Sample `n` base elements. -/
def sampleList (t : Transcript F width) : Nat → List F × Transcript F width
  | 0 => ([], t)
  | n + 1 =>
    let a := sample t
    let r := sampleList a.2 n
    (a.1 :: r.1, r.2)

/-- The extension element `sampleExt` samples. -/
@[irreducible] def sampleExtValue (t : Transcript F width) : EF :=
  Challenge.ofCoeffs (sampleList t (Challenge.d EF)).1

/-- The transcript after `sampleExt`. -/
@[irreducible] def sampleExtState (EF : Type) [Challenge F EF] (t : Transcript F width) :
    Transcript F width :=
  (sampleList t (Challenge.d EF)).2

/-- Sample an extension element, lowest coefficient first. The value and the state are separate
irreducible definitions, so that checking a proof about them never evaluates the permutation. -/
def sampleExt (t : Transcript F width) : EF × Transcript F width :=
  (sampleExtValue t, sampleExtState EF t)

/-- Sample `bits` low bits. -/
def sampleBits (t : Transcript F width) (bits : Nat) : Nat × Transcript F width :=
  let (x, c) := Challenger.sampleBits t.duplex t.state bits
  (x, { t with state := c })

/-- Check a grinding witness. -/
def checkWitness (t : Transcript F width) (bits : Nat) (w : F) : Bool × Transcript F width :=
  let (b, c) := Challenger.checkWitness t.duplex t.state bits w
  (b, { t with state := c })

/-- The grinder's witness for `bits`, and the transcript after observing it, flagged as failed if
the witness does not check. -/
def grind (t : Transcript F width) (bits : Nat) : F × Transcript F width :=
  if bits = 0 then (0, t)
  else
    let w := t.grinder t.state bits
    let r := t.checkWitness bits w
    (w, { r.2 with grindFailed := r.2.grindFailed || !r.1 })

end Transcript
end CompStark
