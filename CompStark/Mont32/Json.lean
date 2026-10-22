/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Challenge
public import CompStark.Batch.Proof
public import CompStark.Mont32.BaseField
public import Lean.Data.Json

/-! # STARK proofs over fast Montgomery fields as JSON

A proof's JSON form as Plonky3 serializes it (`serde_json`) for a base field `MontyField31`, here
`FastField p`: field elements as Montgomery words, extension elements as
`{"value": [c0, …, c(d-1)]}`, commitments as Merkle caps `{"cap": [[eight words], …]}`,
Merkle multi-openings with their pruned siblings `{"sibling_hashes": [...]}`, and absent openings
as `null`; and batch proofs (`parseBatch`), every instance's opened values in the same format with
its permutation trace's rows, and its lookup terminal.
-/

@[expose] public section
namespace CompStark.Stark
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

namespace Json
open Lean (Json)

/-- A field element from its Montgomery word. -/
def field (j : Json) : Except String (FastField p) := do
  let n ← j.getNat?
  if h : n < p then
    return ⟨n.toUInt32, by
      rw [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt
        (lt_trans h Mont32Field.modulus_lt_two_pow_32)]
      exact h⟩
  else throw s!"not a canonical Montgomery word: {n}"

/-- An array. -/
def array {α : Type} (f : Json → Except String α) (j : Json) : Except String (Array α) := do
  (← j.getArr?).mapM f

/-- A vector of `n` elements. -/
def vector {α : Type} (n : Nat) (f : Json → Except String α) (j : Json) :
    Except String (Vector α n) := do
  let a ← array f j
  if h : a.size = n then return ⟨a, h⟩ else throw s!"expected {n} elements, got {a.size}"

/-- A commitment: a Merkle cap `{"cap": [digest, …]}`. -/
def cap (j : Json) : Except String (Cap (FastField p)) :=
  do array (vector 8 field) (← j.getObjVal? "cap")

variable [Mont32BaseField p] {EF : Type} [Challenge (FastField p) EF]

/-- An extension element `{"value": [c0, …, c(d-1)]}`. -/
def ext (j : Json) : Except String EF := do
  let v ← vector (Challenge.d EF) field (← j.getObjVal? "value")
  return Challenge.ofCoeffs v.toList

/-- Pruned siblings `{"sibling_hashes": [...]}`, each a bare array of words. -/
def siblings (j : Json) : Except String (Array (Digest (FastField p))) :=
  do array (vector 8 field) (← j.getObjVal? "sibling_hashes")

def multiOpening (j : Json) : Except String (MultiOpening (FastField p)) := do
  return ⟨← array (array (array field)) (← j.getObjVal? "opened_values"),
    ← siblings (← j.getObjVal? "opening_proof")⟩

def commitOpening (j : Json) : Except String (CommitOpening (FastField p) EF) := do
  return ⟨← array (array ext) (← j.getObjVal? "sibling_values"),
    ← siblings (← j.getObjVal? "opening_proof")⟩

def friProof (j : Json) : Except String (FriProof (FastField p) EF) := do
  return ⟨← field (← j.getObjVal? "batch_pow_witness"),
    ← array cap (← j.getObjVal? "commit_phase_commits"),
    ← array field (← j.getObjVal? "commit_pow_witnesses"),
    ← array multiOpening (← j.getObjVal? "input_openings"),
    ← array commitOpening (← j.getObjVal? "commit_phase_openings"),
    ← array ext (← j.getObjVal? "final_poly"),
    ← field (← j.getObjVal? "query_pow_witness")⟩

/-- Fail unless the field `k` of `j` is `null`. -/
def absent (j : Json) (k : String) : Except String Unit := do
  match ← j.getObjVal? k with
  | .null => return ()
  | _ => throw s!"unsupported: {k}"

/-- `null`, or a value. -/
def optional {α : Type} (f : Json → Except String α) : Json → Except String (Option α)
  | .null => return none
  | j => some <$> f j

/-- Opened values, rejecting randomization. -/
def openedValues (ov : Json) : Except String (OpenedValues EF) := do
  absent ov "random"
  return ⟨← array ext (← ov.getObjVal? "trace_local"),
    ← optional (array ext) (← ov.getObjVal? "trace_next"),
    ← optional (array ext) (← ov.getObjVal? "preprocessed_local"),
    ← optional (array ext) (← ov.getObjVal? "preprocessed_next"),
    ← array (array ext) (← ov.getObjVal? "quotient_chunks")⟩

/-- A proof, rejecting randomization. -/
def proof (j : Json) : Except String (Proof (FastField p) EF) := do
  let cs ← j.getObjVal? "commitments"
  absent cs "random"
  return ⟨← cap (← cs.getObjVal? "trace"), ← cap (← cs.getObjVal? "quotient_chunks"),
    ← openedValues (← j.getObjVal? "opened_values"),
    ← friProof (← j.getObjVal? "opening_proof"),
    ← (← j.getObjVal? "degree_bits").getNat?,
    ← field (← j.getObjVal? "ood_pow_witness")⟩

/-- A proof from its JSON text. -/
def parse (s : String) : Except String (Proof (FastField p) EF) := do
  proof (← Lean.Json.parse s)

/-- A batch proof, rejecting randomization. -/
def batchProof (j : Json) : Except String (Batch.BatchProof (FastField p) EF) := do
  let cs ← j.getObjVal? "commitments"
  absent cs "random"
  let insts ← (← (← j.getObjVal? "opened_values").getObjVal? "instances").getArr?
  return ⟨← cap (← cs.getObjVal? "main"), ← optional cap (← cs.getObjVal? "permutation"),
    ← cap (← cs.getObjVal? "quotient_chunks"),
    ← insts.mapM fun i ↦ do openedValues (← i.getObjVal? "base_opened_values"),
    ← insts.mapM fun i ↦ do array ext (← i.getObjVal? "permutation_local"),
    ← insts.mapM fun i ↦ do array ext (← i.getObjVal? "permutation_next"),
    ← friProof (← j.getObjVal? "opening_proof"),
    ← array (optional ext) (← j.getObjVal? "lookup_terminals"),
    ← array (·.getNat?) (← j.getObjVal? "degree_bits"),
    ← optional field (← j.getObjVal? "lookup_pow_witness"),
    ← field (← j.getObjVal? "ood_pow_witness")⟩

/-- A batch proof from its JSON text. -/
def parseBatch (s : String) : Except String (Batch.BatchProof (FastField p) EF) := do
  batchProof (← Lean.Json.parse s)

end Json
end CompStark.Stark
