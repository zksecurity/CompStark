/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Challenge

/-! # STARK proofs

The proof of Plonky3's `uni-stark` with the two-adic FRI commitment scheme over a base field `F`,
its challenges in the extension `EF`, and Merkle digests of eight base elements; and the
verifying key of a preprocessed trace.
-/

@[expose] public section
namespace CompStark.Stark

/-- A Merkle digest. -/
abbrev Digest (F : Type) := Vector F 8

/-- A Merkle opening at one index of a batch of committed matrices: the row of every matrix, and
the sibling digests from the leaf layer up. -/
structure BatchOpening (F : Type) where
  values : Array (Array F)
  path : Array (Digest F)
deriving BEq

/-- A Merkle opening at several indices of a batch of committed matrices: for every index, in the
order of the queries, the row of every matrix; and the sibling digests the indices' paths do not
cover, level by level from the leaves, left to right (Plonky3's pruned multi-opening). -/
structure MultiOpening (F : Type) where
  values : Array (Array (Array F))
  siblings : Array (Digest F)
deriving BEq

/-- The openings of one FRI fold: for every query the other members of its folded group, and the
pruned siblings of the groups' Merkle paths. -/
structure CommitOpening (F EF : Type) where
  siblings : Array (Array EF)
  path : Array (Digest F)
deriving BEq

/-- A FRI proof: the grinding witness of the batching challenge, the commit phase's commitments
and grinding witnesses, the input openings at the queries (one per committed batch), the folds'
openings at the queries (one per fold), the final polynomial and the query grinding witness. -/
structure FriProof (F EF : Type) where
  batchWitness : F
  commits : Array (Digest F)
  commitWitnesses : Array F
  inputs : Array (MultiOpening F)
  folds : Array (CommitOpening F EF)
  finalPoly : Array EF
  queryWitness : F
deriving BEq

/-- The values a STARK proof opens at `ζ` and `ζ ω`: the trace's (at `ζ ω` only if the AIR reads
its next row), the preprocessed trace's if the AIR has one (at `ζ ω` only if the AIR reads its next
row), and the quotient chunks'. -/
structure OpenedValues (EF : Type) where
  traceLocal : Array EF
  traceNext : Option (Array EF)
  preprocessedLocal : Option (Array EF)
  preprocessedNext : Option (Array EF)
  quotientChunks : Array (Array EF)
deriving BEq

/-- The verifying key of a preprocessed trace (Plonky3's `PreprocessedVerifierKey`): its width,
the log of its height and its commitment. -/
structure PreprocessedKey (F : Type) where
  width : Nat
  degreeBits : Nat
  commit : Digest F
deriving BEq

/-- A STARK proof, without zero knowledge. -/
structure Proof (F EF : Type) where
  traceCommit : Digest F
  quotientCommit : Digest F
  opened : OpenedValues EF
  fri : FriProof F EF
  degreeBits : Nat
  /-- The grinding witness of the out-of-domain point. -/
  oodWitness : F
deriving BEq

end CompStark.Stark
