/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Refines

/-! # Observed overwrite-duplex transcript writer

The caller frames messages into lanes, including domain tags. Rate lanes are
overwritten and cleared after each permutation; capacity lanes carry over.
Every squeeze permutes, including after an empty message or a previous squeeze.
Observers receive the exact permutation input and output, suitable for witness
construction. Proof transport and permutation observations are separate outputs.
-/

@[expose] public section
namespace CompStark.Keccak.Duplex

/-- A positive rate strictly smaller than the 25-lane state. -/
structure Rate where
  lanes : Nat
  positive : 0 < lanes
  capacity : lanes < 25

/-- Pure observer of each permutation, in execution order. -/
abbrev Observer (O : Type) := O → Array UInt64 → Array UInt64 → O

/-- Duplex state, including the caller's observer accumulator. -/
structure State (rate : Rate) (O : Type) where
  lanes : Array UInt64 := Array.replicate 25 0
  width : lanes.size = 25 := by rfl
  pending : Nat := 0
  pending_le : pending ≤ rate.lanes
  observed : O

/-- Empty state, with the observer's initial accumulator. -/
def State.empty (rate : Rate) (observed : O) : State rate O :=
  ⟨Array.replicate 25 0, by rfl, 0, Nat.zero_le _, observed⟩

/-- Permute and clear exactly the rate; expose the permutation output separately. -/
def flushWith (permute : Array UInt64 → Array UInt64)
    (hpermute : ∀ s, (permute s).size = 25) (rate : Rate) (observer : Observer O)
    (state : State rate O) : Array UInt64 × State rate O :=
  let output := permute state.lanes
  let cleared := output.mapIdx fun i x ↦ if i < rate.lanes then 0 else x
  (output, ⟨cleared, by simp only [cleared, Array.size_mapIdx, output, hpermute],
    0, Nat.zero_le _, observer state.observed state.lanes output⟩)

/-- Overwrite one lane, flushing a full rate only when another lane arrives. -/
def absorbLaneWith (permute : Array UInt64 → Array UInt64)
    (hpermute : ∀ s, (permute s).size = 25) (rate : Rate) (observer : Observer O)
    (state : State rate O) (lane : UInt64) : State rate O :=
  let ready := if state.pending = rate.lanes then
      (flushWith permute hpermute rate observer state).2 else state
  have hready : ready.pending < rate.lanes := by
    by_cases h : state.pending = rate.lanes
    · simpa only [ready, h, ↓reduceIte, flushWith] using rate.positive
    · simp only [ready, h, ↓reduceIte]
      have := state.pending_le
      omega
  ⟨ready.lanes.set! ready.pending lane, by simp only [Array.size_set!, ready.width],
    ready.pending + 1, by omega, ready.observed⟩

/-- Absorb framed lanes in order. -/
def absorbWith (permute : Array UInt64 → Array UInt64)
    (hpermute : ∀ s, (permute s).size = 25) (rate : Rate) (observer : Observer O)
    (state : State rate O) (lanes : Array UInt64) : State rate O :=
  lanes.foldl (absorbLaneWith permute hpermute rate observer) state

/-- Reference Keccak preserves the 25-lane state width. -/
theorem spec_width (s : Array UInt64) :
    (VCVio.Algorithms.Keccak.f1600 s).size = 25 := by
  exact Sponge.size_f1600 s

/-- Scalar Keccak preserves the state width. -/
theorem fast_width (s : Array UInt64) : (f1600 s).size = 25 := by
  rw [f1600_eq]
  exact spec_width s

/-- Scalar overwrite-duplex absorption. -/
def absorb (rate : Rate) (observer : Observer O) (state : State rate O)
    (lanes : Array UInt64) : State rate O :=
  absorbWith f1600 fast_width rate observer state lanes

/-- Every sample gets its own permutation. `count` chooses the returned rate prefix. -/
def sample (rate : Rate) (observer : Observer O) (state : State rate O)
    (count : Nat) (_hcount : count ≤ rate.lanes) : Array UInt64 × State rate O :=
  let result := flushWith f1600 fast_width rate observer state
  (result.1.extract 0 count, result.2)

/-- Complete state and observer equality with VCVio absorption, for every framed message. -/
theorem absorb_eq (rate : Rate) (observer : Observer O) (state : State rate O)
    (lanes : Array UInt64) :
    absorb rate observer state lanes =
      absorbWith VCVio.Algorithms.Keccak.f1600 spec_width rate observer state lanes := by
  have hf : f1600 = VCVio.Algorithms.Keccak.f1600 := funext f1600_eq
  unfold absorb
  simp only [hf]

/-- Complete output, carried capacity and observer equality for each squeeze. -/
theorem sample_eq (rate : Rate) (observer : Observer O) (state : State rate O)
    (count : Nat) (hcount : count ≤ rate.lanes) :
    sample rate observer state count hcount =
      let result := flushWith VCVio.Algorithms.Keccak.f1600 spec_width rate observer state
      (result.1.extract 0 count, result.2) := by
  have hf : f1600 = VCVio.Algorithms.Keccak.f1600 := funext f1600_eq
  unfold sample
  simp only [hf]

/-- A writer retains transmitted values as well as the duplex's private observations. -/
structure Writer (rate : Rate) (Message O : Type) where
  state : State rate O
  stream : Array Message := #[]

/-- Transmit and bind together. Encoding, including tags, belongs to the caller. -/
def Writer.write (rate : Rate) (observer : Observer O) (encode : Message → Array UInt64)
    (writer : Writer rate Message O) (message : Message) : Writer rate Message O :=
  ⟨absorb rate observer writer.state (encode message), writer.stream.push message⟩

/-- Draw a challenge without adding it to the transmitted stream. -/
def Writer.sample (rate : Rate) (observer : Observer O) (writer : Writer rate Message O)
    (count : Nat) (hcount : count ≤ rate.lanes) : Array UInt64 × Writer rate Message O :=
  let result := Duplex.sample rate observer writer.state count hcount
  (result.1, ⟨result.2, writer.stream⟩)

/-- Writing records exactly the sent message and observes exactly its framed lanes. -/
theorem Writer.write_eq (rate : Rate) (observer : Observer O) (encode : Message → Array UInt64)
    (writer : Writer rate Message O) (message : Message) :
    writer.write rate observer encode message =
      ⟨absorbWith VCVio.Algorithms.Keccak.f1600 spec_width rate observer writer.state
          (encode message), writer.stream.push message⟩ := by
  simp only [Writer.write, absorb_eq]

/-- Search consecutive candidates in increasing order, with an explicit work bound. -/
def findNonce (accept : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, first =>
    if accept first then some first else findNonce accept fuel (first + 1)

/-- A successful search returns the smallest accepted candidate in its interval. -/
theorem findNonce_min (accept : Nat → Bool) (fuel first nonce : Nat)
    (h : findNonce accept fuel first = some nonce) :
    first ≤ nonce ∧ nonce < first + fuel ∧ accept nonce = true ∧
      ∀ m, first ≤ m → m < nonce → accept m = false := by
  induction fuel generalizing first with
  | zero => simp only [findNonce, reduceCtorEq] at h
  | succ fuel ih =>
    simp only [findNonce] at h
    split at h
    · rename_i ha
      cases Option.some.inj h
      exact ⟨Nat.le_refl _, by omega, ha, fun m hm hlt ↦ by omega⟩
    · rename_i ha
      obtain ⟨hlo, hhi, hok, hmin⟩ := ih (first + 1) h
      refine ⟨by omega, by omega, hok, fun m hm hlt ↦ ?_⟩
      by_cases he : m = first
      · subst m
        exact Bool.eq_false_iff.mpr ha
      · exact hmin m (by omega) hlt

/-- Try nonces without reporting rejected probes; bind and observe the smallest success once. -/
def grindWith (permute : Array UInt64 → Array UInt64)
    (hpermute : ∀ s, (permute s).size = 25) (rate : Rate) (observer : Observer O)
    (state : State rate O) (frame : Nat → Array UInt64)
    (accept : Array UInt64 → Bool) (limit : Nat) : Option (Nat × State rate O) :=
  let quiet : Observer O := fun o _ _ ↦ o
  let probe n := (flushWith permute hpermute rate quiet
    (absorbWith permute hpermute rate quiet state (frame n))).1
  (findNonce (fun n ↦ accept (probe n)) limit 0).map fun nonce ↦
    (nonce, (flushWith permute hpermute rate observer
      (absorbWith permute hpermute rate observer state (frame nonce))).2)

/-- Deterministic bounded grinding, independent of thread scheduling. -/
def grind (rate : Rate) (observer : Observer O) (state : State rate O)
    (frame : Nat → Array UInt64) (accept : Array UInt64 → Bool) (limit : Nat) :
    Option (Nat × State rate O) :=
  grindWith f1600 fast_width rate observer state frame accept limit

/-- Grinding's chosen nonce, carried state and observer agree with VCVio. -/
theorem grind_eq (rate : Rate) (observer : Observer O) (state : State rate O)
    (frame : Nat → Array UInt64) (accept : Array UInt64 → Bool) (limit : Nat) :
    grind rate observer state frame accept limit =
      grindWith VCVio.Algorithms.Keccak.f1600 spec_width rate observer state frame accept limit := by
  have hf : f1600 = VCVio.Algorithms.Keccak.f1600 := funext f1600_eq
  unfold grind
  simp only [hf]

end CompStark.Keccak.Duplex
