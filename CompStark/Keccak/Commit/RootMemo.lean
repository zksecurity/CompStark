/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Masked
public import CompStark.Keccak.Commit.HashMemo

/-! Exact operation and hash caches for root-only Merkle authentication. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.Commit
open CompStark.BinaryFields MixedMerkleTree.Knowledge

/-- Materialize the predicted operations at every root-only tree position. -/
@[noinline, nospecialize] def rootOperationLayers (height : Nat)
    (operations : Position → Op (List K) Digest) : Array (Array (Op (List K) Digest)) :=
  Array.ofFn fun depth : Fin (height + 1) =>
    Array.ofFn fun index : Fin (2 ^ depth.val) =>
      operations ⟨depth.val, index.val, if depth.val = height then .leaf else .children⟩

/-- Read cached root-tree operations and preserve the original operation elsewhere. -/
@[macro_inline] def rootOperationAt (height : Nat) (layers : Array (Array (Op (List K) Digest)))
    (operations : Position → Op (List K) Digest) (v : Position) : Op (List K) Digest :=
  if v.depth < height + 1 ∧ v.index < 2 ^ v.depth ∧
      v.stage = (if v.depth = height then .leaf else .children) then
    ((layers[v.depth]?.getD #[])[v.index]?).getD (.inl [])
  else operations v

/-- Materialized root-tree operations preserve the full prediction function. -/
theorem rootOperationAt_eq (height : Nat) (operations : Position → Op (List K) Digest) :
    rootOperationAt height (rootOperationLayers height operations) operations = operations := by
  funext v
  unfold rootOperationAt
  by_cases valid : v.depth < height + 1 ∧ v.index < 2 ^ v.depth ∧
      v.stage = (if v.depth = height then .leaf else .children)
  · rw [ite_eq_left valid]
    obtain ⟨depth, index, stage⟩ := valid
    simp only [rootOperationLayers, Array.getElem?_ofFn, dite_eq_left depth, Option.getD_some,
      dite_eq_left index]
    apply congrArg operations
    cases v
    congr 1
    exact stage.symm
  · rw [ite_eq_right valid]

/-- Collect the exact byte strings of the materialized root-tree operations. -/
def rootHashInputs (layers : Array (Array (Op (List K) Digest))) : List (List UInt8) :=
  [] :: layers.toList.flatMap fun level =>
    level.toList.map fun operation => (operationBytes operation).data.toList

variable (hash : ByteArray → Digest)

/-- Hash a concrete leaf through the exact memo table. -/
def rootLeafHash (memo : Std.HashMap (List UInt8) Digest) (leaf : List K) : Digest :=
  hashWithMemo hash memo (leafBytes leaf)

/-- Compress a concrete digest pair through the exact memo table. -/
def rootCompress (memo : Std.HashMap (List UInt8) Digest) (left right : Digest) : Digest :=
  hashWithMemo hash memo ⟨left.toArray ++ right.toArray⟩

/-- Memoized leaf hashing equals the leaf hash. -/
theorem rootLeafHash_eq (inputs : List (List UInt8)) :
    rootLeafHash hash (hashMemo hash inputs) = leafWith hash := by
  funext leaf
  exact hashWithMemo_eq hash inputs _

/-- Memoized digest-pair compression equals the pair hash. -/
theorem rootCompress_eq (inputs : List (List UInt8)) :
    rootCompress hash (hashMemo hash inputs) = pairWith hash := by
  funext left right
  exact hashWithMemo_eq hash inputs _

/-- Materialize the maximal root-only leaf mask using shared operations and exact hashes. -/
def rootAuthenticationMemo (height : Nat) (root : Digest)
    (original : Position → Op (List K) Digest) : MixedAuthentication height :=
  let layers := rootOperationLayers height original
  let operations := rootOperationAt height layers original
  let memo := hashMemo hash (rootHashInputs layers)
  let mask := Array.ofFn fun i : Fin (2 ^ height) =>
    if checkPositionPath (rootLeafHash hash memo) (rootCompress hash memo) [] height 0 (fun _ => false)
        [root] operations ⟨height, i.val, .leaf⟩ then
      some (opPayload [] (operations ⟨height, i.val, .leaf⟩)) else none
  { leaves := ⟨fun i => mask[i.val]?.getD none, operations⟩
    injections := fun _ => ⟨fun _ => none, operations⟩ }

/-- Cached mask construction equals the maximal hash-consistent root authentication. -/
theorem rootAuthenticationMemo_eq (height : Nat) (root : Digest)
    (operations : Position → Op (List K) Digest) :
    rootAuthentication hash height root operations = rootAuthenticationMemo hash height root operations := by
  simp only [rootAuthenticationMemo, rootAuthentication, rootOperationAt_eq, rootLeafHash_eq,
    rootCompress_eq, Array.getElem?_ofFn, dite_eq_left (Fin.isLt _), Option.getD_some]

/-- Verify root-only authentication using the generic mixed-tree checker. -/
def rootMerkleAuthenticate (height : Nat) (root : Digest) (auth : MixedAuthentication height) : Bool :=
  mixedMerkleAuthenticate hash height 0 (fun _ => false) [root] auth

/-- Verify root-only authentication using shared operations and exact hash memoization. -/
def rootMerkleAuthenticateMemo (height : Nat) (root : Digest) (auth : MixedAuthentication height) : Bool :=
  let layers := rootOperationLayers height auth.leaves.operations
  let operations := rootOperationAt height layers auth.leaves.operations
  let memo := hashMemo hash (rootHashInputs layers)
  (show MaskAuthentication (List K) Digest height from ⟨auth.leaves.word, operations⟩).check
      (rootLeafHash hash memo) (rootCompress hash memo) [] height 0 (fun _ => false) [root] &&
    (List.range height).all fun depth =>
      (auth.injections depth).check (leafWith hash) (pairWith hash) [] height 0 depth (fun _ => false) [root]

/-- Cached root-only verification equals the concrete mixed-tree check. -/
theorem rootMerkleAuthenticateMemo_eq (height : Nat) (root : Digest) (auth : MixedAuthentication height) :
    rootMerkleAuthenticate hash height root auth = rootMerkleAuthenticateMemo hash height root auth := by
  simp only [rootMerkleAuthenticateMemo, rootMerkleAuthenticate, mixedMerkleAuthenticate,
    rootOperationAt_eq, rootLeafHash_eq, rootCompress_eq]

/-- Compiled mask construction uses the proved exact cache. -/
@[csimp] theorem rootAuthentication_code : rootAuthentication = rootAuthenticationMemo := by
  funext hash height root operations
  exact rootAuthenticationMemo_eq hash height root operations

/-- Compiled production authentication uses the proved exact cache. -/
@[csimp] theorem rootMerkleAuthenticate_code : rootMerkleAuthenticate = rootMerkleAuthenticateMemo := by
  funext hash height root auth
  exact rootMerkleAuthenticateMemo_eq hash height root auth

end CompStark.Keccak.Commit
