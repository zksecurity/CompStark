/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Keccak.Refines

/-! # Scalar Keccak regressions

Known answers use the original Keccak suffix. Boundary and patterned inputs also
compare every output byte with VCVio in the compiled test driver. The approved
word accessors execute through their native implementations.
-/

namespace CompStarkTests.KeccakHash
open CompStark.Keccak

/-- Reproducible messages covering byte order and nonzero high bytes. -/
def message (n seed : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := n) fun i ↦ (i.val * 197 + seed * 83).toUInt8)

/-- All padding cases, exact rate multiples, and the leanVM leaf size. -/
def boundaryLengths : List Nat :=
  [0, 1, 7, 8, 31, 32, 63, 64, 127, 128, 134, 135, 136, 137, 263, 270, 271, 272,
    273, 407, 408, 409, 511, 512, 513, 1024]

theorem message_addressable (n seed : Nat) (hn : n < 4294967296) :
    (message n seed).size < USize.size := by
  simp only [message, ByteArray.size, Array.size_ofFn]
  exact lt_of_lt_of_le hn USize.le_size

theorem boundary_bound (n : Nat) (hn : n ∈ boundaryLengths) : n < 4294967296 := by
  simp only [boundaryLengths, List.mem_cons, List.not_mem_nil, or_false] at hn
  omega

/-- A known answer expressed as the four little-endian digest lanes. -/
def digestLanes (input : ByteArray) (hu : input.size < USize.size) : Array UInt64 :=
  let h := keccak256 input hu
  #[readLane h 0, readLane h 8, readLane h 16, readLane h 24]

/-- Original Keccak known answers, checked through the compiled sponge. -/
def knownAnswers : Bool :=
  digestLanes ByteArray.empty (lt_of_lt_of_le (by decide) USize.le_size) ==
  #[0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b] &&
  digestLanes "abc".toUTF8 (lt_of_lt_of_le (by decide) USize.le_size) ==
  #[0x4fa945ea7a65034e, 0x67d6c826a87bd4c7, 0x36a0643ae3e6d1c0, 0x456c2da18ff544ec]

/-- Compiled comparisons cover known answers, nonconstant inputs, batches and Merkle shapes. -/
def comparisons : Bool := Id.run do
  if !knownAnswers then return false
  for seed in [0:4] do
    for n in boundaryLengths.attach do
      let input := message n.val seed
      have hu := message_addressable n.val seed (boundary_bound _ n.property)
      if keccak256 input hu != VCVio.Algorithms.Keccak.keccak256 input then return false
  let states := Array.ofFn (n := 32) fun j ↦
    Array.ofFn (n := 25) fun i ↦
      (j.val.toUInt64 + 1) * 0x9e3779b97f4a7c15 ^^^
        ((i.val.toUInt64 + 17) * 0xd1b54a32d192ed03)
  if f1600Batch states != states.map VCVio.Algorithms.Keccak.f1600 then return false
  if f1600Batch #[] != #[] then return false
  let inputs := boundaryLengths.toArray.map fun n ↦ message n 42
  have hu : ∀ input ∈ inputs, input.size < USize.size := by
    intro input hi
    simp only [inputs, Array.mem_map, List.mem_toArray] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    exact message_addressable n 42 (boundary_bound n hn)
  if keccak256Batch inputs hu != inputs.map VCVio.Algorithms.Keccak.keccak256 then return false
  if keccak256Batch #[] (by simp) != #[] then return false
  let left := message 32 1
  let right := message 32 2
  if hashNode left right (by simp only [left, message, ByteArray.size, Array.size_ofFn])
      (by simp only [right, message, ByteArray.size, Array.size_ofFn]) !=
      VCVio.Algorithms.Keccak.keccak256 (left ++ right) then return false
  if hashLeaf (message 512 3) (by simp only [message, ByteArray.size, Array.size_ofFn]) !=
      VCVio.Algorithms.Keccak.keccak256 (message 512 3) then return false
  return true


/- The complete hash refinement uses only Lean’s standard logical axioms. -/
#print axioms keccak256_eq
#print axioms f1600Batch_eq
#print axioms keccak256Batch_eq

end CompStarkTests.KeccakHash
