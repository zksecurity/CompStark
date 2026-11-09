/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.MerkleGenerate

/-! # Flat worker-local leaf hashes and consumer-owned retained trees -/

@[expose] public section
namespace CompStark.Keccak.Merkle
open BinaryTree InductiveMerkleTree

/-- Concatenate digests into one flat buffer that can cross a worker boundary. -/
def packDigests : List Digest → ByteArray
  | [] => ByteArray.empty
  | x :: xs => x.val ++ packDigests xs

/-- Flat digest storage has exactly one 32-byte slot per leaf. -/
@[simp] theorem size_packDigests (xs : List Digest) : (packDigests xs).size = 32 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [packDigests, ByteArray.size_append, x.property, ih,
      List.length_cons]; omega

/-- A flat slot recovers its complete digest bytes. -/
theorem extract_packDigests (xs : List Digest) (i : Nat) (hi : i < xs.length) :
    (packDigests xs).extract (32 * i) (32 * (i + 1)) = (xs[i]).val := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [packDigests, Nat.mul_zero, Nat.zero_add, Nat.mul_one, List.getElem_cons_zero]
      exact ByteArray.extract_append_eq_left x.property.symm
    | succ i =>
      have he : 32 * (i + 1) = x.val.size + 32 * i := by rw [x.property]; omega
      have he' : 32 * (i + 1 + 1) = x.val.size + 32 * (i + 1) := by rw [x.property]; omega
      simpa only [packDigests, he, he', ByteArray.extract_append_size_add,
        List.getElem_cons_succ] using ih i (by simp only [List.length_cons] at hi; omega)

/-- Appending in a fold reuses the flat buffer's growing allocation. -/
def packDigestsFold (xs : List Digest) : ByteArray :=
  xs.foldl (fun bytes digest => bytes ++ digest.val) ByteArray.empty

/-- The growing-buffer implementation preserves every flat digest slot. -/
@[csimp] theorem packDigests_code : packDigests = packDigestsFold := by
  have aux (xs : List Digest) (bytes : ByteArray) :
      xs.foldl (fun bytes digest => bytes ++ digest.val) bytes = bytes ++ packDigests xs := by
    induction xs generalizing bytes with
    | nil => simp only [List.foldl_nil, packDigests, ByteArray.append_empty]
    | cons x xs ih =>
      rw [List.foldl_cons, ih, packDigests, ByteArray.append_assoc]
  funext xs
  simpa only [packDigestsFold, ByteArray.empty_append] using (aux xs ByteArray.empty).symm

/-- A worker result contains only one flat byte allocation, with erased leaf-hash certificates. -/
structure HashedRows (n : Nat) (row : Fin n → Row) where
  bytes : ByteArray
  size : bytes.size = 32 * n
  correct : ∀ i : Fin n, bytes.extract (32 * i.val) (32 * (i.val + 1)) = (hashRow (row i)).val

/-- Hash an encoder window on its creating worker and flatten all temporary digests there. -/
def hashRows (n : Nat) (row : Fin n → Row) : HashedRows n row where
  bytes := packDigests (List.ofFn fun i => hashRow (row i))
  size := by simp only [size_packDigests, List.length_ofFn]
  correct i := by
    rw [extract_packDigests _ i.val (by simp only [List.length_ofFn]; exact i.isLt)]
    simp only [List.getElem_ofFn]

/-- Allocate one retained digest on the consuming thread. -/
def HashedRows.get (hashes : HashedRows n row) (i : Fin n) : Digest :=
  ⟨hashes.bytes.extract (32 * i.val) (32 * (i.val + 1)), by
    rw [hashes.correct i]; exact (hashRow (row i)).property⟩

/-- A retained digest is exactly the certified hash of its retained row. -/
theorem HashedRows.get_eq (hashes : HashedRows n row) (i : Fin n) :
    hashes.get i = hashRow (row i) := Subtype.ext (hashes.correct i)

/-- Retain a consumer-allocated row and its already-computed digest. -/
def Tree.leafHashed (row : Row) (digest : Digest) (h : digest = hashRow row) : Tree 0 where
  rows := .leaf row
  nodes := .leaf digest
  correct := by rw [h, hashRow_eq]; rfl

/-- Retaining an already-computed hash preserves the complete certified leaf tree. -/
theorem Tree.leafHashed_eq (row : Row) (digest : Digest) (h : digest = hashRow row) :
    Tree.leafHashed row digest h = Tree.leaf row := by cases h; rfl

/-- Build retained tree nodes and payloads entirely on the thread consuming a flat hash batch. -/
def Tree.generateCachedAt {n : Nat} (row : Fin n → Row) (digest : Fin n → Digest)
    (agree : ∀ i, digest i = hashRow (row i)) :
    (depth start : Nat) → start + 2 ^ depth ≤ n → Tree depth
  | 0, start, bound =>
    let i : Fin n := ⟨start, by simp only [Nat.pow_zero] at bound; omega⟩
    Tree.leafHashed (row i) (digest i) (agree i)
  | depth + 1, start, bound =>
    Tree.join
      (Tree.generateCachedAt row digest agree depth start (by rw [pow_succ] at bound; omega))
      (Tree.generateCachedAt row digest agree depth (start + 2 ^ depth) (by rw [pow_succ] at bound; omega))

/-- Flat hash batches reconstruct every retained payload and internal digest exactly. -/
theorem Tree.generateCachedAt_eq {n : Nat} (row : Fin n → Row) (digest : Fin n → Digest)
    (agree : ∀ i, digest i = hashRow (row i)) (depth start : Nat) (bound : start + 2 ^ depth ≤ n) :
    Tree.generateCachedAt row digest agree depth start bound = Tree.generateAt row depth start bound := by
  induction depth generalizing start with
  | zero => simp only [Tree.generateCachedAt, Tree.generateAt, Tree.leafHashed_eq]
  | succ depth ih => simp only [Tree.generateCachedAt, Tree.generateAt, ih]

end CompStark.Keccak.Merkle
