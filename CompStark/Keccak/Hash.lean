/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Scalar

/-! # Keccak-256 and independent batches

The original Keccak domain uses a 136-byte rate, little-endian lanes, and the
`0x01 … 0x80` suffix. Fixed-size node and leaf APIs make their byte lengths explicit.
-/

public section
namespace CompStark.Keccak

/-- A little-endian lane; XOR joins the eight disjoint byte positions. -/
@[expose, inline] def readLane (input : ByteArray) (o : Nat) : UInt64 :=
  (input[o + 0]!.toUInt64 <<< 0) ^^^
  (input[o + 1]!.toUInt64 <<< 8) ^^^
  (input[o + 2]!.toUInt64 <<< 16) ^^^
  (input[o + 3]!.toUInt64 <<< 24) ^^^
  (input[o + 4]!.toUInt64 <<< 32) ^^^
  (input[o + 5]!.toUInt64 <<< 40) ^^^
  (input[o + 6]!.toUInt64 <<< 48) ^^^
  (input[o + 7]!.toUInt64 <<< 56)

/-- XOR one lane, retaining the array's width. -/
@[expose, inline] def xorAt (s : Array UInt64) (i : Nat) (v : UInt64) : Array UInt64 :=
  s.set! i (s[i]! ^^^ v)

/-- Absorb a complete 136-byte rate block, eight bytes per lane. -/
@[expose] def absorbBlock (input : ByteArray) (offset : Nat) (initial : Array UInt64) :
    Array UInt64 := Id.run do
  let mut s := initial
  for i in [0:17] do
    s := xorAt s i (readLane input (offset + i * 8))
  return s

/-- Absorb with the Keccak-256 rate and padding, using scalar permutations. -/
@[expose] def absorb (input : ByteArray) : Array UInt64 := Id.run do
  let padTotal := 136 - input.size % 136
  let padBytes : List UInt8 :=
    if padTotal = 1 then [0x81]
    else 0x01 :: (List.replicate (padTotal - 2) 0 ++ [0x80])
  let padded := input ++ ByteArray.mk padBytes.toArray
  let mut s : Array UInt64 := Array.replicate 25 0
  for b in [0:padded.size / 136] do
    s := absorbBlock padded (b * 136) s
    s := f1600 s
  return s

/-- Original Keccak-256, with a 32-byte digest. -/
@[expose] def keccak256 (input : ByteArray) : ByteArray :=
  VCVio.Algorithms.Keccak.squeeze (absorb input) 32

/-- Permute several independent states in input order. -/
@[expose] def f1600Batch (states : Array (Array UInt64)) : Array (Array UInt64) :=
  states.map f1600

/-- Hash several independent messages in input order. -/
@[expose] def keccak256Batch (inputs : Array ByteArray) : Array ByteArray :=
  inputs.map keccak256

/-- A Merkle node's two 32-byte children, concatenated left then right. -/
@[expose] def hashNode (left right : ByteArray) (_hl : left.size = 32) (_hr : right.size = 32) :
    ByteArray :=
  keccak256 (left ++ right)

/-- A leanVM Merkle leaf's 512-byte payload. -/
@[expose] def hashLeaf (payload : ByteArray) (_h : payload.size = 512) : ByteArray :=
  keccak256 payload

end CompStark.Keccak
