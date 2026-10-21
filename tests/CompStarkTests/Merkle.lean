/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.KoalaBear.Hash
import CompStark.Merkle.RootCorrectness
import CompStark.Merkle.Extract

/-! # Merkle root known answers

Roots of Plonky3's `MerkleTreeMmcs` with the Poseidon2 sponge and compression of
`examples/src/types.rs`, on matrices whose entry `k` is `base + k` (`bench/rust`,
`cargo run --release`). They cover odd heights, single rows and injected smaller matrices.
-/

namespace CompStarkTests.Merkle
open CompStark.Merkle

/-- A `height × width` matrix with entries `base, base + 1, …`. -/
def mat (base height width : Nat) : Matrix _root_.KoalaBear.Field :=
  ⟨width, height, Array.ofFn (n := height * width) fun k ↦ ((base + k.val : Nat) : _)⟩

def rootOf (ms : List (Nat × Nat × Nat)) : Vector Nat 8 :=
  (KoalaBear.root _ (ms.map fun (b, h, w) ↦ mat b h w)).map ZMod.val

#guard rootOf [(0, 8, 3)] == #v[839328004, 1713888626, 47538326, 961529694, 1367537855,
  384103636, 1060544133, 485679400]
#guard rootOf [(0, 5, 2)] == #v[489187703, 929509427, 1512075425, 176164476, 1755927159,
  1019341202, 1923645285, 1724637561]
#guard rootOf [(0, 1, 10)] == #v[807353722, 690866596, 1884109333, 1323245552, 1700476937,
  1797497072, 1087871157, 1493878500]
#guard rootOf [(0, 4, 5), (1000, 8, 3), (2000, 2, 1), (3000, 1, 7), (4000, 8, 2)] ==
  #v[1170636731, 1464782430, 93151705, 555063351, 1082903266, 2078379327, 13779068, 1472929077]
#guard rootOf [(0, 6, 3), (500, 3, 2)] == #v[1638766218, 131982039, 1467186891, 1331228402,
  1237520776, 1318414788, 1465319517, 1282851410]

/-- info: 'CompStark.Merkle.Packed.root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Merkle.Packed.root_eq

/-- info: 'CompStark.Merkle.extractRow_eq_of_verifyBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Merkle.extractRow_eq_of_verifyBatch

/-- info: 'CompStark.Merkle.extractRow_eq_of_noPrediction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Merkle.extractRow_eq_of_noPrediction

end CompStarkTests.Merkle
