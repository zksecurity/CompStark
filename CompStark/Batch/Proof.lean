/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Lookup.Lookup
public import CompStark.Stark.Proof

/-! # Batch-STARK statements and proofs

Plonky3's `batch-stark` proves several AIR instances at once, of mixed heights, under shared
commitments and one opening argument. An instance (`Instance`) is an AIR, the log of its trace's
height and its lookups, packed at keygen (`Instance.ofAir`, Plonky3's
`ProverData::from_airs_and_degrees`). The verifier holds the AIRs and the batch's common data
(`Common`, Plonky3's `CommonData`): the commitment to the instances' preprocessed traces, and every
instance's keygen height and packed lookups. A proof claims every instance's height
(`BatchProof.degreeBits`), which the verifier takes from it.

A proof (`BatchProof`) carries the commitments to all main traces, to the permutation traces of
the instances with lookups and to all quotient chunks, every instance's opened values in
`uni-stark`'s format with its permutation trace's rows, the opening argument, every instance's
lookup terminal and degree bits, and the grinding witnesses of the lookup challenges and of the
out-of-domain point.
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Stark CompStark.Lookup

/-- An instance of a batch: an AIR, its trace's height `2 ^ logN` and the lookups it proves. -/
structure Instance (F : Type) where
  air : Air F
  logN : Nat
  lookups : List (Stark.Lookup F)

variable {F : Type} [Zero F] [One F]

/-- The instance of `air` on `2 ^ logN` rows with its AIR's lookups packed for that height, as
Plonky3's keygen packs them (`Air.packedLookups`). -/
def Instance.ofAir (air : Air F) (logN : Nat) : Instance F := ⟨air, logN, air.packedLookups logN⟩

/-- The LogUp constraints of the instance's lookups. -/
def Instance.lookupConstraints (I : Instance F) : List (ExtExpr F) := logUpConstraints I.lookups

/-- Plonky3's log number of the instance's quotient chunks: of its AIR's constraints and its
lookups' LogUp constraints. -/
def Instance.logQuotientChunks (I : Instance F) : Nat :=
  I.air.logQuotientChunksWith I.logN I.lookupConstraints

/-- The instances' shapes: every instance's log trace height and log number of quotient
chunks. -/
def shapes (instances : List (Instance F)) : List (Nat × Nat) :=
  instances.map fun I ↦ (I.logN, I.logQuotientChunks)

/-- The batch has lookups. -/
def hasLookups (instances : List (Instance F)) : Bool := instances.any (!·.lookups.isEmpty)

section Messages
variable {F : Type} [BaseField F]

/-- The batch's lookup messages on the traces `traces` with the public values `pis`: for every
instance, row, lookup and tuple in turn, the lookup's bus (as `busIds` numbers the buses) with the
tuple's values on the row, and the tuple's multiplicity there. -/
def messages (instances : List (Instance F)) (traces : List (Array F)) (pis : List (List F)) :
    List ((Nat × List F) × F) :=
  ((instances.zip (traces.zip pis)).zip (busIds (instances.map (·.lookups)))).flatMap
    fun ((I, t, p), ids) ↦ (List.range (2 ^ I.logN)).flatMap fun r ↦
      (I.lookups.zip ids).flatMap fun (l, b) ↦ l.tuples.map fun (es, m) ↦
        ((b, es.map (·.eval (generationRow I.air I.logN t p r))),
          m.eval (generationRow I.air I.logN t p r))

/-- Every bus balances: for every bus and every tuple of values, the multiplicities of its
messages sum to zero in the field, as LogUp checks. -/
def Balanced (instances : List (Instance F)) (traces : List (Array F)) (pis : List (List F)) :
    Prop :=
  ∀ key : Nat × List F, (((messages instances traces pis).filter (·.1 = key)).map (·.2)).sum = 0

end Messages

/-- What the verifier shares with the prover (Plonky3's `CommonData`), fixed at keygen: the
commitment to the preprocessed traces of the instances that have one, in instance order, if any
has one, and every instance's keygen height and lookups. -/
structure Common (F : Type) where
  preprocessed : Option (Cap F)
  /-- Every instance's log trace height at keygen. -/
  degreeBits : List Nat
  /-- Every instance's lookups, packed at keygen. -/
  lookups : List (List (Stark.Lookup F))

/-- A batch-STARK proof without zero knowledge (Plonky3's `BatchProof`). -/
structure BatchProof (F EF : Type) where
  mainCommit : Cap F
  /-- The commitment to the permutation traces of the instances with lookups, if any. -/
  permutationCommit : Option (Cap F)
  quotientCommit : Cap F
  /-- Every instance's opened values, in `uni-stark`'s format. -/
  opened : Array (OpenedValues EF)
  /-- Every instance's permutation trace's row at `ζ`, in base coordinates; empty without
  lookups. -/
  permutationLocal : Array (Array EF)
  /-- Every instance's permutation trace's row at `ζ ω`, in base coordinates; empty without
  lookups. -/
  permutationNext : Array (Array EF)
  fri : FriProof F EF
  /-- Every instance's lookup terminal, the sum of its lookups' fractions; none without
  lookups. -/
  lookupTerminals : Array (Option EF)
  /-- Every instance's log trace height, the prover's to choose. -/
  degreeBits : Array Nat
  /-- The grinding witness of the lookup challenges, if the batch has lookups. -/
  lookupWitness : Option F
  /-- The grinding witness of the out-of-domain point. -/
  oodWitness : F
deriving BEq

end CompStark.Batch
