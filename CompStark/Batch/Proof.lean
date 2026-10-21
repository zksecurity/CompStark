/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Air
public import CompStark.Stark.Proof

/-! # Batch-STARK statements and proofs

Plonky3's `batch-stark` proves several AIR instances at once, of mixed heights, under shared
commitments and one opening argument. A batch's statement is its instances (`Instance`: an AIR
and the log of its trace's height) with their public values; the verifier holds the commitment to
the instances' preprocessed traces (`Common`, Plonky3's `CommonData` without lookups). A proof
(`BatchProof`) carries the commitments to all main traces and to all quotient chunks, every
instance's opened values in `uni-stark`'s format, the opening argument, every instance's degree
bits and the out-of-domain grinding witness.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Stark

/-- An instance of a batch: an AIR and its trace's height `2 ^ logN`. -/
structure Instance (F : Type) where
  air : Air F
  logN : Nat

/-- The instances' shapes: every instance's log trace height and log number of quotient
chunks. -/
def shapes {F : Type} (instances : List (Instance F)) : List (Nat × Nat) :=
  instances.map fun I ↦ (I.logN, I.air.logQuotientChunks I.logN)

/-- What the verifier shares with the prover (Plonky3's `CommonData` without lookups): the root of
the commitment to the preprocessed traces of the instances that have one, in instance order, if
any has one. -/
structure Common (F : Type) where
  preprocessed : Option (Digest F)
deriving BEq

/-- A batch-STARK proof without lookups or zero knowledge (Plonky3's `BatchProof`). -/
structure BatchProof (F EF : Type) where
  mainCommit : Digest F
  quotientCommit : Digest F
  /-- Every instance's opened values, in `uni-stark`'s format. -/
  opened : Array (OpenedValues EF)
  fri : FriProof F EF
  /-- Every instance's log trace height. -/
  degreeBits : Array Nat
  /-- The grinding witness of the out-of-domain point. -/
  oodWitness : F
deriving BEq

end CompStark.Batch
