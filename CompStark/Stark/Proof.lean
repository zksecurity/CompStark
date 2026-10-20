/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Challenge
public import Lean.Data.Json
public import CompPoly.Univariate.NTTFast.Packed.Arithmetic

/-! # STARK proofs

The proof of Plonky3's `uni-stark` with the two-adic FRI commitment scheme over KoalaBear, its
challenges in the extension `EF`, and its JSON form as Plonky3 serializes it (`serde_json`): field
elements as Montgomery words, extension elements as `{"value": [c0, …, c(d-1)]}`, digests as
`{"value": [eight words]}`.
-/

@[expose] public section
namespace CompStark.Stark

local notation "F" => KoalaBear.Fast.Field

/-- A Merkle digest. -/
abbrev Digest := Vector F 8

/-- The rows opened at one index in a batch of committed matrices, and the sibling digests from the
leaf layer up. -/
structure BatchOpening where
  values : Array (Array F)
  path : Array Digest
deriving BEq

/-- One FRI fold of a query: the arity, the other members of the folded group, and their path. -/
structure CommitStep (EF : Type) where
  logArity : Nat
  siblings : Array EF
  path : Array Digest
deriving BEq

/-- The openings of one FRI query: the input batches, then the folds. -/
structure QueryProof (EF : Type) where
  inputs : Array BatchOpening
  steps : Array (CommitStep EF)
deriving BEq

/-- A FRI proof. -/
structure FriProof (EF : Type) where
  commits : Array Digest
  commitWitnesses : Array F
  queries : Array (QueryProof EF)
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
structure Proof (EF : Type) where
  traceCommit : Digest
  quotientCommit : Digest
  opened : OpenedValues EF
  fri : FriProof EF
  degreeBits : Nat
deriving BEq

namespace Json
open Lean (Json)

/-- A field element from its Montgomery word. -/
def field (j : Json) : Except String F := do
  let n ← j.getNat?
  if n < KoalaBear.fieldSize then return CompPoly.CPolynomial.NTTFast.Packed.ofWord n.toUInt32
  else throw s!"not a canonical Montgomery word: {n}"

/-- An array. -/
def array {α : Type} (f : Json → Except String α) (j : Json) : Except String (Array α) := do
  (← j.getArr?).mapM f

/-- A vector of `n` elements. -/
def vector {α : Type} (n : Nat) (f : Json → Except String α) (j : Json) :
    Except String (Vector α n) := do
  let a ← array f j
  if h : a.size = n then return ⟨a, h⟩ else throw s!"expected {n} elements, got {a.size}"

/-- A digest `{"value": [...]}`. -/
def digest (j : Json) : Except String Digest := do vector 8 field (← j.getObjVal? "value")

variable {EF : Type} [Challenge EF]

/-- An extension element `{"value": [c0, …, c(d-1)]}`. -/
def ext (j : Json) : Except String EF := do
  let v ← vector (Challenge.d EF) field (← j.getObjVal? "value")
  return Challenge.ofCoeffs v.toList

/-- A sibling path: an array of digests, each a bare array of words. -/
def path (j : Json) : Except String (Array Digest) := array (vector 8 field) j

def batchOpening (j : Json) : Except String BatchOpening := do
  return ⟨← array (array field) (← j.getObjVal? "opened_values"),
    ← path (← j.getObjVal? "opening_proof")⟩

def commitStep (j : Json) : Except String (CommitStep EF) := do
  return ⟨← (← j.getObjVal? "log_arity").getNat?, ← array ext (← j.getObjVal? "sibling_values"),
    ← path (← j.getObjVal? "opening_proof")⟩

def queryProof (j : Json) : Except String (QueryProof EF) := do
  return ⟨← array batchOpening (← j.getObjVal? "input_proof"),
    ← array commitStep (← j.getObjVal? "commit_phase_openings")⟩

def friProof (j : Json) : Except String (FriProof EF) := do
  return ⟨← array digest (← j.getObjVal? "commit_phase_commits"),
    ← array field (← j.getObjVal? "commit_pow_witnesses"),
    ← array queryProof (← j.getObjVal? "query_proofs"),
    ← array ext (← j.getObjVal? "final_poly"),
    ← field (← j.getObjVal? "query_pow_witness")⟩

/-- Fail unless the field `k` of `j` is `null`. -/
def absent (j : Json) (k : String) : Except String Unit := do
  match ← j.getObjVal? k with
  | .null => return ()
  | _ => throw s!"unsupported: {k}"

/-- A proof, rejecting preprocessed columns and randomization. -/
def proof (j : Json) : Except String (Proof EF) := do
  let cs ← j.getObjVal? "commitments"
  absent cs "random"
  let ov ← j.getObjVal? "opened_values"
  absent ov "preprocessed_local"
  absent ov "preprocessed_next"
  absent ov "random"
  return ⟨← digest (← cs.getObjVal? "trace"), ← digest (← cs.getObjVal? "quotient_chunks"),
    ⟨← array ext (← ov.getObjVal? "trace_local"), ← array ext (← ov.getObjVal? "trace_next"),
      ← array (array ext) (← ov.getObjVal? "quotient_chunks")⟩,
    ← friProof (← j.getObjVal? "opening_proof"),
    ← (← j.getObjVal? "degree_bits").getNat?⟩

/-- A proof from its JSON text. -/
def parse (s : String) : Except String (Proof EF) := do proof (← Lean.Json.parse s)

end Json
end CompStark.Stark
