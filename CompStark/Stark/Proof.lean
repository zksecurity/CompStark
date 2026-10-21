/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Challenge

/-! # STARK proofs

The proof of Plonky3's `uni-stark` with the two-adic FRI commitment scheme over a base field `F`,
its challenges in the extension `EF`, and Merkle digests of eight base elements.
-/

@[expose] public section
namespace CompStark.Stark

/-- A Merkle digest. -/
abbrev Digest (F : Type) := Vector F 8

/-- The rows opened at one index in a batch of committed matrices, and the sibling digests from the
leaf layer up. -/
structure BatchOpening (F : Type) where
  values : Array (Array F)
  path : Array (Digest F)
deriving BEq

/-- One FRI fold of a query: the arity, the other members of the folded group, and their path. -/
structure CommitStep (F EF : Type) where
  logArity : Nat
  siblings : Array EF
  path : Array (Digest F)
deriving BEq

/-- The openings of one FRI query: the input batches, then the folds. -/
structure QueryProof (F EF : Type) where
  inputs : Array (BatchOpening F)
  steps : Array (CommitStep F EF)
deriving BEq

/-- A FRI proof. -/
structure FriProof (F EF : Type) where
  commits : Array (Digest F)
  commitWitnesses : Array F
  queries : Array (QueryProof F EF)
  finalPoly : Array EF
  queryWitness : F
deriving BEq

/-- The values a STARK proof opens at `ζ` and `ζ ω`. -/
structure OpenedValues (EF : Type) where
  traceLocal : Array EF
  traceNext : Array EF
  quotientChunks : Array (Array EF)
deriving BEq

/-- A STARK proof, without preprocessed columns or zero knowledge. -/
structure Proof (F EF : Type) where
  traceCommit : Digest F
  quotientCommit : Digest F
  opened : OpenedValues EF
  fri : FriProof F EF
  degreeBits : Nat
deriving BEq

end CompStark.Stark
