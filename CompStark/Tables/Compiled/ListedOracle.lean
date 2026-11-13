/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Listed
public import CompStark.Compiled.MerkleTrace

/-! The record game's deterministic core for the list form: under the table of a random-oracle
trace without collisions or late preimages (`¬ Bad`), a listing whose inputs the trace caches and
which lists every revealed operation, at its node's shape, has no unexplained opening
(`not_unexplained`). The dictionary's first listed input with the node's target is then the
revealed operation's input, since a good trace's cache is injective, and it decodes at the node's
stage to the revealed operation. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Compiled
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp OracleSpec
open MixedMerkleTree.Knowledge Keccak.Commit.RandomOracleTrace

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} {Key : Type} {Response : Key → Type}

/-- Two listed inputs a good trace caches, with one digest under its table, are equal. -/
theorem listed_inputs_eq [DecidableEq Key] (roots : Key → List Commit.Digest)
    (table : (query : ByteArray ⊕ Key) → (MerkleTrace.Spec Response).Range query)
    (log : QueryLog (MerkleTrace.Spec Response)) (good : ¬ Bad (MerkleTrace.references roots) log)
    (a b : ByteArray) (ha : Bcs.cacheOf log (.inl a) = some (table (.inl a)))
    (hb : Bcs.cacheOf log (.inl b) = some (table (.inl b))) (same : table (.inl a) = table (.inl b)) :
    a = b :=
  hash_cache_injective (MerkleTrace.references roots) log good a b _ ha (same ▸ hb)

/-- Under a good trace's table, a listing whose inputs the trace caches and which lists each
revealed operation, of its node's shape, has no unexplained opening. -/
theorem not_unexplained [DecidableEq Key] (roots : Key → List Commit.Digest)
    (table : (query : ByteArray ⊕ Key) → (MerkleTrace.Spec Response).Range query)
    (log : QueryLog (MerkleTrace.Spec Response)) (coherent : Agrees table log)
    (good : ¬ Bad (MerkleTrace.references roots) log) (params : Parameters S L k M) (o : Listing params)
    (cached : ∀ input ∈ o.2, ∃ value, Bcs.cacheOf log (.inl input) = some value)
    (explained : ∀ position ∈ merklePositions params.schedule params.semanticRowWords,
      ∀ op ∈ (listedNode (fun input => table (.inl input)) params o position PUnit.unit).2,
        position.2.opShape op = true ∧ Commit.operationBytes op ∈ o.2) :
    ¬ Unexplained (fun input => table (.inl input)) params o := by
  rintro ⟨position, member, op, opMember, opHash, opDiffers⟩
  set hash : ByteArray → Commit.Digest := fun input => table (.inl input)
  set target := (listedNode hash params o position PUnit.unit).1
  obtain ⟨shape, listed⟩ := explained position member op opMember
  have known (input : ByteArray) (h : input ∈ o.2) : Bcs.cacheOf log (.inl input) = some (table (.inl input)) := by
    obtain ⟨value, hv⟩ := cached input h
    rw [hv, cache_eq_table table log coherent _ value hv]
  have opTarget : hash (Commit.operationBytes op) = target := by
    rw [← Commit.answer_eq_hash_operationBytes hash op]
    exact opHash
  have found : ((Commit.listedEntries hash o.2).find? fun entry => entry.1 == target).isSome := by
    rw [List.find?_isSome]
    exact ⟨(hash (Commit.operationBytes op), Commit.operationBytes op),
      List.mem_map.mpr ⟨_, listed, rfl⟩, by simp only [opTarget, beq_self_eq_true]⟩
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp found
  have entryMember := List.mem_of_find?_eq_some hentry
  have entryTarget := List.find?_some hentry
  obtain ⟨input, inputListed, rfl⟩ := List.mem_map.mp entryMember
  simp only [beq_iff_eq] at entryTarget
  have same : input = Commit.operationBytes op :=
    listed_inputs_eq roots table log good input _ (known input inputListed) (known _ listed)
      (entryTarget.trans opTarget.symm)
  apply opDiffers
  change op = dictionaryOp hash o.2 position.2 target
  simp only [dictionaryOp, Commit.dictionary, Commit.lookupEntry, hentry, Option.map_some, same,
    Option.bind_some, Commit.decodeOperationInput_encode position.2 op shape, Option.getD_some]

end CompStark.Tables.Compiled
