/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Codec
public import CompStark.Keccak.Commit.Masked
public import Std.Data.HashMap.Lemmas

/-! Stage-aware inverses of the untagged Merkle hash-input encoding. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.Commit
open CompStark.BinaryFields MixedMerkleTree.Knowledge

/-- Decode all complete field words of a raw leaf hash input. -/
def decodeLeafInput (input : ByteArray) : List K :=
  (List.finRange (input.size / 8)).map fun i =>
    Keccak.Lanes.wordLane (Keccak.Commit.readWord input (8 * i.val))

/-- Leaf serialization has exactly eight bytes per field word. -/
theorem leafInput_size (values : List K) : (Keccak.Commit.leafBytes values).size = 8 * values.length := by
  simp only [Keccak.Commit.leafBytes, ByteArray.size, List.size_toArray, List.length_flatMap,
    Keccak.Commit.wordBytes_length, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

/-- Decoding a serialized leaf recovers every field word without search. -/
theorem decodeLeafInput_encode (values : List K) : decodeLeafInput (Keccak.Commit.leafBytes values) = values := by
  unfold decodeLeafInput
  rw [leafInput_size, Nat.mul_div_right _ (by decide)]
  simp only [Keccak.Commit.readWord_leafBytes, Keccak.Lanes.wordLane_laneWord]
  simpa only [List.ofFn_eq_map] using (List.ofFn_getElem (xs := values))

/-- Read a pair of fixed-width digests and reject every other input length. -/
def decodePairInput (input : ByteArray) : Option (Keccak.Commit.Digest × Keccak.Commit.Digest) := do
  let (pair, rest) ← ((bytes 32).prod (bytes 32)).read input.data.toList
  if rest.isEmpty then some pair else none

/-- Raw child-pair encoding round-trips without a domain tag. -/
theorem decodePairInput_encode (left right : Keccak.Commit.Digest) :
    decodePairInput ⟨left.toArray ++ right.toArray⟩ = some (left, right) := by
  unfold decodePairInput
  have encoded : (left.toArray ++ right.toArray).toList =
      ((bytes 32).prod (bytes 32)).write (left, right) ++ [] := by
    simp only [Codec.prod, bytes, List.append_nil, Array.toList_append, Vector.toList_toArray]
  rw [encoded, Codec.read_write]
  rfl

/-- Every raw hash input is inspected for two child digests, including leaf-shaped inputs. -/
def merkleReferences (input : ByteArray) : List Keccak.Commit.Digest :=
  match decodePairInput input with
  | none => []
  | some (left, right) => [left, right]

/-- Parsing a hash input introduces at most two referenced digests. -/
theorem merkleReferences_length (input : ByteArray) : (merkleReferences input).length ≤ 2 := by
  unfold merkleReferences
  split <;> simp only [List.length_nil, List.length_cons] <;> omega

/-- Both children of every compression input are recorded as references. -/
theorem merkleReferences_pair (left right : Keccak.Commit.Digest) :
    merkleReferences (Keccak.Commit.operationBytes (.inr (left, right))) = [left, right] := by
  simp only [merkleReferences, Keccak.Commit.operationBytes, decodePairInput_encode]

/-- Interpret a recovered raw preimage using the expected mixed-Merkle node stage. -/
def decodeOperationInput (stage : Stage) (input : ByteArray) : Option (Op (List K) Keccak.Commit.Digest) :=
  match stage with
  | .leaf | .payload =>
      let values := decodeLeafInput input
      if Keccak.Commit.leafBytes values = input then some (.inl values) else none
  | .children | .injection => (decodePairInput input).map Sum.inr

/-- Each correctly shaped operation is recovered from its exact raw hash input. -/
theorem decodeOperationInput_encode (position : Position) (operation : Op (List K) Keccak.Commit.Digest)
    (shape : position.opShape operation = true) :
    decodeOperationInput position.stage (Keccak.Commit.operationBytes operation) = some operation := by
  cases position with | mk depth index stage =>
    cases stage <;> cases operation <;>
      simp only [Position.opShape, Bool.false_eq_true] at shape
    all_goals simp only [decodeOperationInput, Keccak.Commit.operationBytes, decodeLeafInput_encode,
      ↓reduceIte, decodePairInput_encode, Option.map_some]

/-- Digest-preimage entries of listed raw hash inputs under a raw-byte hash. -/
def listedEntries (hash : ByteArray → Keccak.Commit.Digest) (inputs : List ByteArray) :
    List (Keccak.Commit.Digest × ByteArray) :=
  inputs.map fun input => (hash input, input)

/-- The preimage of the first entry with a digest. -/
def lookupEntry (entries : List (Keccak.Commit.Digest × ByteArray)) (digest : Keccak.Commit.Digest) : Option ByteArray :=
  (entries.find? fun entry => entry.1 == digest).map Prod.snd

/-- The dictionary of digest-preimage entries: a digest's first preimage, decoded at the requested
node stage. A missing or malformed preimage predicts the empty leaf. -/
def dictionary (entries : List (Keccak.Commit.Digest × ByteArray)) : Keccak.Commit.Predict :=
  fun stage digest => ((lookupEntry entries digest).bind (decodeOperationInput stage)).getD (.inl [])

/-- Index entries by digest bytes, keeping each digest's first preimage. -/
def entryIndex (entries : List (Keccak.Commit.Digest × ByteArray)) : Std.HashMap (List UInt8) ByteArray :=
  entries.foldl (fun index entry => index.insertIfNew entry.1.toList entry.2) ∅

/-- Folding first-preimage insertions keeps every earlier entry and adds the first new match. -/
theorem entryIndex_fold (entries : List (Keccak.Commit.Digest × ByteArray))
    (index : Std.HashMap (List UInt8) ByteArray) (key : List UInt8) :
    (entries.foldl (fun index entry => index.insertIfNew entry.1.toList entry.2) index)[key]? =
      index[key]?.or ((entries.find? fun entry => entry.1.toList == key).map Prod.snd) := by
  induction entries generalizing index with
  | nil => simp only [List.foldl_nil, List.find?_nil, Option.map_none, Option.or_none]
  | cons entry rest ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getElem?_insertIfNew, List.find?_cons]
    by_cases same : entry.1.toList = key
    · subst same
      by_cases present : entry.1.toList ∈ index
      · simp [present]
      · simp [present]
    · have different : (entry.1.toList == key) = false := by simpa using same
      simp [different]

/-- The digest index answers exactly the first entry's preimage. -/
theorem entryIndex_get (entries : List (Keccak.Commit.Digest × ByteArray)) (digest : Keccak.Commit.Digest) :
    (entryIndex entries)[digest.toList]? = lookupEntry entries digest := by
  have predicate : (fun entry : Keccak.Commit.Digest × ByteArray => entry.1.toList == digest.toList) =
      fun entry => entry.1 == digest := by
    funext entry
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Vector.toList_inj]
  simp only [entryIndex, entryIndex_fold, Std.HashMap.getElem?_empty, Option.none_or, lookupEntry,
    predicate]

/-- The dictionary reads a digest index built once from the entries. -/
def dictionaryIndexed (entries : List (Keccak.Commit.Digest × ByteArray)) : Keccak.Commit.Predict :=
  let index := entryIndex entries
  fun stage digest => ((index[digest.toList]?).bind (decodeOperationInput stage)).getD (.inl [])

/-- Indexing preserves every dictionary answer. -/
@[csimp] theorem dictionary_code : @dictionary = @dictionaryIndexed := by
  funext entries stage digest
  simp only [dictionary, dictionaryIndexed, entryIndex_get]

end CompStark.Keccak.Commit
