/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStarkFixtures.Tables
meta import CompStarkFixtures.Tables

/-! The `program` system through the composed honest prover and fast verifier: the honest
transcript is accepted, and transcripts of an unsatisfying witness or with a tampered value are
rejected. -/

@[expose] public section
namespace CompStarkTests.TablesComposed
open CompStark.Tables CompStark.Tables.Examples CompStark.Tables.Composed CompStark.BinaryFields
open CompStark.Multilinear CompStark.Fixtures.Tables

/-- Replace row `i` of table `t`. -/
def setRow {n : ℕ} (w : Witness K n) (t i : ℕ) (row : Array K) : Witness K n :=
  fun s => if s.val = t then (w s).set i row else w s

/-- The honest transcript of the program's witness is accepted. -/
def acceptsHonest : Bool := programVerify (programProof programWitness)

/-- An unbalanced witness, its final count wrong, is rejected. -/
def rejectsUnbalanced : Bool :=
  !programVerify (programProof (setRow programWitness 0 0 #[g]))

/-- A witness breaking the execution table's constraint is rejected. -/
def rejectsConstraint : Bool :=
  !programVerify (programProof (setRow programWitness 1 1 #[k 1, k 12, 1]))

#guard acceptsHonest
#guard rejectsUnbalanced
#guard rejectsConstraint

end CompStarkTests.TablesComposed
