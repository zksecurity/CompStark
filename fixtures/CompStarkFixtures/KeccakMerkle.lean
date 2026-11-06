/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Merkle
public import CompStark.Keccak.Duplex

/-! # Fixed inputs for Keccak commitment and duplex conformance and benchmarks

Framing in this fixture mirrors the pinned Rust harness. It is test data rather
than a protocol instance exported by the generic library.
-/

@[expose] public section
namespace CompStark.Fixtures.KeccakMerkle
open CompStark.Keccak

/-- Reproducible, full-width lane values, shared with the Rust harness. -/
def word (row col : Nat) : UInt64 :=
  (row.toUInt64 + 1) * 0x9e3779b97f4a7c15 ^^^
    ((col.toUInt64 + 17) * 0xd1b54a32d192ed03)

/-- A packed row with a complete leaf image of at most 512 bytes. -/
def row (width : Nat) (hw : width ≤ 64) (index : Nat) : Merkle.Row :=
  let words := Array.ofFn (n := width) fun i ↦ word index i.val
  Merkle.Row.ofWords words (by
    simp only [words, Array.size_ofFn]
    exact lt_of_lt_of_le (by omega) USize.le_size)

/-- Row-major input, packed before measurement. -/
def rows (count width : Nat) (hw : width ≤ 64) : Array Merkle.Row :=
  Array.ofFn (n := count) fun i ↦ row width hw i.val

/-- The pinned protocol's rate, used only as a conformance fixture. -/
def rate : Duplex.Rate := ⟨16, by decide, by decide⟩

/-- The pinned protocol's tagged scalar layout, used only as a fixture. -/
def framed (k : UInt64) : Array UInt64 :=
  #[k, k ^^^ 0x1234, (k <<< 17) ||| (k >>> 47), 1]

/-- Initial eight lanes, before the mandatory seed permutation. -/
def seed (observed : O) : Duplex.State rate O :=
  ⟨Array.ofFn (n := 25) (fun i ↦ if i.val < 8 then word (i.val / 4) (i.val % 4) else 0),
    Array.size_ofFn .., 0, Nat.zero_le _, observed⟩

/-- Observer-free benchmark initialization. -/
def initial : Duplex.State rate Unit :=
  (Duplex.sample rate (fun _ _ _ ↦ ()) (seed ()) 0 (by decide)).2

/-- Transmit a scalar and sample once per iteration, retaining all sent frames. -/
def duplexLoop : Nat → UInt64 → Duplex.Writer rate (Array UInt64) Unit → UInt64 →
    UInt64 × Duplex.Writer rate (Array UInt64) Unit
  | 0, _, writer, sink => (sink, writer)
  | n + 1, k, writer, sink =>
    let writer := writer.write rate (fun _ _ _ ↦ ()) id (framed k)
    let result := writer.sample rate (fun _ _ _ ↦ ()) 3 (by decide)
    duplexLoop n (k + 1) result.2 (sink + result.1[0]!)

/-- Fixed query positions, intentionally unsorted. -/
def queries : List Nat := (List.range 100).map fun i ↦ (i * 197 + 23) % 4096

end CompStark.Fixtures.KeccakMerkle
