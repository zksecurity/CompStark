/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Keccak.Transcript.Native
public import CompStark.Keccak.Commit.Native

/-! Rust conformance of the lane-level duplex grinding and the streaming Keccak Merkle commitment
on field-word leaves. The expected bytes in `tests/data/keccak-transport` come from leanMultisig
`9d8bce818aa7c7e18e67026e522a9b1539d0a57d`, written by `tests/rust/keccak-transport.rs` and reproduced by
`scripts/check-binary-stack-reference`. -/
@[expose] public section
namespace CompStarkTests.KeccakTransport
open CompStark CompStark.BinaryFields CompStark.Keccak CompStark.Keccak.TranscriptDuplex
open CompStark.Keccak.MerkleLeaves

/-- Fixed four-word digest used by the Rust transcript fixture. -/
def digest (first : Nat) : Commit.Digest := Vector.ofFn fun i =>
  ((UInt64.ofNat (first + i.val / 8)) >>> (8 * (i.val % 8)).toUInt64).toUInt8

/-- The fixture's scalar pattern. -/
def value (i : Nat) : E :=
  BF64.WordExt3.toField ⟨⟨UInt64.ofNat (0x123456789abcdef0 + 31 * i)⟩,
    ⟨UInt64.ofNat (0xfedcba9876543210 + i * i)⟩,
    ⟨UInt64.ofNat (0x8000000000000001 + 17 * i)⟩⟩

/-- A seeded transcript that crosses a complete overwrite rate. -/
def state : Transcript.State :=
  Transcript.absorbAll (Transcript.seedDigests (digest 1) (digest 5))
    ((List.range 7).map fun i => .scalar (value i))

/-- Compare smallest-nonce grinding, the following draw, and Merkle roots, rows and hints. -/
def check : IO Unit := do
  for bits in [0, 5, 9] do
    let some (nonce, next) := grind bits (duplexState state)
      | throw (IO.userError "grinding exhausted the honest nonce space")
    let sample := CompStark.Keccak.Duplex.sample rate (fun _ _ _ => ()) next 3 (by decide)
    let actual : ByteArray := ⟨((Commit.wordBytes (K.ofBits nonce) ++ List.replicate 16 0).toArray ++
      (sample.1.toList.flatMap fun w => Commit.wordBytes (Lanes.wordLane w)).toArray)⟩
    let expected ← IO.FS.readBinFile s!"tests/data/keccak-transport/grind-{bits}.bin"
    unless actual == expected do throw (IO.userError s!"grinding mismatch at difficulty {bits}")
  let rows := Array.ofFn fun i : Fin 16 =>
    let live := (List.range 3).map fun j => K.ofBits (31 * i.val + j + 1)
    merkleRow (Commit.initialLeaf 8 live) (by
      simp only [live, Commit.initialLeaf, List.length_append, List.length_replicate,
        List.length_reverse, List.length_map, List.length_range]
      exact lt_of_lt_of_le (by decide : 64 < 4294967296) USize.le_size)
  let tree ← IO.ofExcept (CompStark.Keccak.Merkle.commit rows)
  let expected ← IO.FS.readBinFile "tests/data/keccak-transport/merkle-root.bin"
  unless tree.2.root.val == expected do throw (IO.userError "Keccak Merkle root mismatch")
  let opening ← IO.ofExcept (tree.2.open [9, 3, 9, 0, 15, 8])
  let actual := (openingRows 5 opening).foldl ByteArray.append ByteArray.empty
  let expected ← IO.FS.readBinFile "tests/data/keccak-transport/merkle-rows.bin"
  unless actual == expected do throw (IO.userError "Keccak Merkle row mismatch")
  let expected ← IO.FS.readBinFile "tests/data/keccak-transport/merkle-hashes.bin"
  unless openingHashes opening == expected do throw (IO.userError "Keccak Merkle hint mismatch")
  IO.println "duplex grinding and Keccak Merkle openings on field-word leaves match Rust"

end CompStarkTests.KeccakTransport
