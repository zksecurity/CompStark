/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Lanes
public import CompStark.Keccak.Native

/-! Byte encodings of leanMultisig revision `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`,
`crates/fiat_shamir/src/merkle.rs` and annex B. Initial K interleaving is reversed;
later E interleaving keeps its order and writes three little-endian limbs per element. -/

namespace CompStark.Keccak.Commit
open CompStark.BinaryFields CompStark.Keccak.Lanes
@[expose] public section

/-- A Keccak-256 digest, with exactly 32 bytes. -/
abbrev Digest := Vector UInt8 32

/-- Eight little-endian bytes of a K limb. -/
def wordBytes (x : K) : List UInt8 :=
  (List.range 8).map fun j ↦ ((laneWord x >>> (8 * j).toUInt64) &&& 255).toUInt8

/-- Serialize leaf limbs without a length prefix or domain tag. -/
def leafBytes (xs : List K) : ByteArray := ⟨(xs.flatMap wordBytes).toArray⟩

/-- A K limb always occupies eight bytes. -/
theorem wordBytes_length (x : K) : (wordBytes x).length = 8 := by
  simp only [wordBytes, List.length_map, List.length_range]

/-- Append the eight little-endian bytes of one word without allocating a byte list. -/
@[inline] def appendWord (out : ByteArray) (w : UInt64) : ByteArray :=
  let out := out.push ((w >>> 0) &&& 255).toUInt8
  let out := out.push ((w >>> 8) &&& 255).toUInt8
  let out := out.push ((w >>> 16) &&& 255).toUInt8
  let out := out.push ((w >>> 24) &&& 255).toUInt8
  let out := out.push ((w >>> 32) &&& 255).toUInt8
  let out := out.push ((w >>> 40) &&& 255).toUInt8
  let out := out.push ((w >>> 48) &&& 255).toUInt8
  let out := out.push ((w >>> 56) &&& 255).toUInt8
  out

/-- Direct word appending preserves all eight byte projections. -/
theorem appendWord_eq (out : ByteArray) (x : K) :
    appendWord out (laneWord x) = (wordBytes x).foldl ByteArray.push out := by
  simp only [wordBytes, show List.range 8 = [0,1,2,3,4,5,6,7] from rfl,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rfl

/-- Append serialized limbs directly to one growing byte buffer. -/
def leafBytesStream (xs : List K) : ByteArray :=
  xs.foldl (fun out x => appendWord out (laneWord x)) ByteArray.empty

/-- Pushing a byte sequence appends its exact transport image. -/
private theorem pushBytes_eq (xs : List UInt8) (out : ByteArray) :
    xs.foldl ByteArray.push out = out ++ xs.toByteArray := by
  induction xs generalizing out with
  | nil => simp only [List.foldl_nil, List.toByteArray_nil, ByteArray.append_empty]
  | cons x xs ih =>
    rw [List.foldl_cons, ih, ← ByteArray.append_toByteArray_singleton,
      ByteArray.append_assoc, ← List.toByteArray_append]
    rfl

/-- Streaming serialization preserves every word and byte in the leaf image. -/
@[csimp] theorem leafBytes_code : leafBytes = leafBytesStream := by
  funext xs
  have loop (xs : List K) (out : ByteArray) :
      xs.foldl (fun out x => (wordBytes x).foldl ByteArray.push out) out =
        out ++ (xs.flatMap wordBytes).toByteArray := by
    induction xs generalizing out with
    | nil => simp only [List.foldl_nil, List.flatMap_nil, List.toByteArray_nil,
        ByteArray.append_empty]
    | cons x xs ih =>
      rw [List.foldl_cons, pushBytes_eq, ih, ByteArray.append_assoc,
        List.flatMap_cons, List.toByteArray_append]
  have same := congrArg ByteArray.data (loop xs ByteArray.empty)
  apply ByteArray.ext
  simpa only [leafBytes, leafBytesStream, appendWord_eq, ByteArray.empty_append, List.data_toByteArray] using
    same.symm

/-- Equality of all eight byte projections determines a 64-bit word. -/
theorem word_eq_of_bytes (a b : UInt64)
    (h : ∀ j : Fin 8, ((a >>> (8*j.val).toUInt64) &&& 255).toUInt8 =
      ((b >>> (8*j.val).toUInt64) &&& 255).toUInt8) : a = b := by
  have hn (j : Fin 8) := congrArg UInt8.toNat (h j)
  simp at hn
  simp only [show (255 : ℕ) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.shiftRight_eq_div_pow] at hn
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have h5 := hn 5
  have h6 := hn 6
  have h7 := hn 7
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  apply UInt64.toNat_inj.mp
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  omega

/-- Fixed little-endian byte encoding is injective on K limbs. -/
theorem wordBytes_injective : Function.Injective wordBytes := by
  intro a b h
  have bits : laneWord a = laneWord b := word_eq_of_bytes _ _ fun j ↦ by
    have byte := congrArg (fun xs : List UInt8 ↦ xs[j.val]?) h
    simpa only [wordBytes, List.getElem?_map, List.getElem?_range j.isLt,
      Option.map_some, Option.some.injEq] using byte
  have := congrArg wordLane bits
  simpa only [wordLane_laneWord] using this

/-- Fixed eight-byte limb encoding uniquely determines the entire leaf word list. -/
theorem leafBytes_injective : Function.Injective leafBytes := by
  have injective : Function.Injective (List.flatMap wordBytes) := by
    intro a
    induction a with
    | nil =>
        intro b h
        cases b with
        | nil => rfl
        | cons x xs =>
            have lengths := congrArg List.length h
            simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
              List.length_append, wordBytes_length] at lengths
            omega
    | cons x xs ih =>
        intro b h
        cases b with
        | nil =>
            have lengths := congrArg List.length h
            simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
              List.length_append, wordBytes_length] at lengths
            omega
        | cons y ys =>
            obtain ⟨head, tail⟩ := List.append_inj h
              (by simp only [wordBytes_length])
            have same := wordBytes_injective head
            cases same
            exact congrArg (List.cons x) (ih tail)
  intro a b h
  apply injective
  have bytes := congrArg (fun bs : ByteArray ↦ bs.data.toList) h
  simpa only [leafBytes, List.toList_toArray] using bytes

/-- Read a little-endian word at byte offset `offset`. -/
def readWord (bytes : ByteArray) (offset : ℕ) : UInt64 :=
  (List.range 8).foldl (fun w j ↦ w ||| (bytes[offset + j]!.toUInt64 <<< (8 * j).toUInt64)) 0

/-- Extracting a byte from a decoded little-endian word recovers the corresponding input byte. -/
theorem readWord_byte (bytes : ByteArray) (offset : ℕ) (b : Fin 8) :
    ((readWord bytes offset >>> (8*b.val).toUInt64) &&& 255).toUInt8 = bytes[offset+b.val]! := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> fin_cases b <;>
    simp [readWord, show List.range 8 = [0,1,2,3,4,5,6,7] from rfl,
      UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]

/-- Keccak-256 with Ethereum's `0x01 … 0x80` padding and a 136-byte rate. -/
def hash (bytes : ByteArray) : Digest :=
  ⟨(VCVio.Algorithms.Keccak.keccak256 bytes).data, by
    simp only [VCVio.Algorithms.Keccak.keccak256, VCVio.Algorithms.Keccak.squeeze,
      Array.size_ofFn]⟩

/-- Leaf hashing includes every reconstructed leading zero limb. -/
def hashLeaf (xs : List K) : Digest := hash (leafBytes xs)

/-- Node hashing has no tag: Keccak-256 of the ordered 64-byte concatenation. -/
def compress (left right : Digest) : Digest := hash ⟨left.toArray ++ right.toArray⟩

/-- Leaf hashing with an arbitrary raw-byte hash on the exact production leaf encoding. -/
abbrev leafWith (hash : ByteArray → Digest) (xs : List K) : Digest := hash (leafBytes xs)

/-- Untagged child-pair hashing with an arbitrary raw-byte hash. -/
abbrev pairWith (hash : ByteArray → Digest) (left right : Digest) : Digest :=
  hash ⟨left.toArray ++ right.toArray⟩

/-- Keccak leaf hashing is the generic leaf hash at Keccak-256. -/
theorem leafWith_hash : leafWith hash = hashLeaf := rfl

/-- Keccak compression is the generic pair hash at Keccak-256. -/
theorem pairWith_hash : pairWith hash = compress := rfl

/-- Pointwise Keccak leaf hashing is the generic leaf hash at Keccak-256. -/
theorem leafWith_hash_apply (xs : List K) : leafWith hash xs = hashLeaf xs := rfl

/-- Pointwise Keccak compression is the generic pair hash at Keccak-256. -/
theorem pairWith_hash_apply (left right : Digest) : pairWith hash left right = compress left right := rfl

/-- Initial leaf image: reversed live interleaving, preceded by the omitted zero lanes. -/
def initialLeaf (width : ℕ) (live : List K) : List K :=
  List.replicate (width - live.length) 0 ++ live.reverse

/-- Extension leaf image: forward interleaving, each E as `(c0,c1,c2)`. -/
def extensionLeaf (row : List E) : List K :=
  row.flatMap fun x ↦ [x.limb 0, x.limb 1, x.limb 2]

/-- Transported rows omit only the announced zero prefix; they already have wire lane order. -/
def restoreLeaf (leafWords : ℕ) (row : List K) : List K :=
  List.replicate (leafWords - row.length) 0 ++ row

/-- A digest is carried by two E scalars, each with a zero third limb. -/
def digestScalars (digest : Digest) : List E :=
  let bytes := ByteArray.mk digest.toArray
  [E.ofLimbs (wordLane (readWord bytes 0)) (wordLane (readWord bytes 8)) 0,
   E.ofLimbs (wordLane (readWord bytes 16)) (wordLane (readWord bytes 24)) 0]

/-- The fixed-width digest transport is injective; it does not distinguish roots from scalar pairs. -/
theorem digestScalars_injective : Function.Injective digestScalars := by
  intro a b h
  have halves := List.cons.inj h
  have low := halves.1
  have high := (List.cons.inj halves.2).1
  have words (w : Fin 4) : readWord ⟨a.toArray⟩ (8*w.val) = readWord ⟨b.toArray⟩ (8*w.val) := by
    fin_cases w
    · have eq := congrArg (fun x : E ↦ laneWord (x.limb 0)) low
      simpa only [limb_ofLimbs, Matrix.cons_val_zero, laneWord_wordLane] using eq
    · have eq := congrArg (fun x : E ↦ laneWord (x.limb 1)) low
      simpa only [limb_ofLimbs, Matrix.cons_val_one, Matrix.cons_val_zero, laneWord_wordLane] using eq
    · have eq := congrArg (fun x : E ↦ laneWord (x.limb 0)) high
      simpa only [limb_ofLimbs, Matrix.cons_val_zero, laneWord_wordLane] using eq
    · have eq := congrArg (fun x : E ↦ laneWord (x.limb 1)) high
      simpa only [limb_ofLimbs, Matrix.cons_val_one, Matrix.cons_val_zero, laneWord_wordLane] using eq
  apply Vector.ext
  intro i hi
  let w : Fin 4 := ⟨i / 8, by omega⟩
  let j : Fin 8 := ⟨i % 8, by omega⟩
  have eq := congrArg (fun word : UInt64 ↦ ((word >>> (8*j.val).toUInt64) &&& 255).toUInt8) (words w)
  rw [readWord_byte, readWord_byte] at eq
  have index : 8*w.val+j.val = i := by dsimp [w, j]; omega
  rw [index, getElem!_pos _ i (by simpa only [ByteArray.size, Vector.size_toArray] using hi),
    getElem!_pos _ i (by simpa only [ByteArray.size, Vector.size_toArray] using hi)] at eq
  exact eq

/-- Index a concatenation of blocks of one fixed width. -/
theorem flatMap_getD {α β : Type} (encode : α → List β) (width : ℕ)
    (length : ∀ a, (encode a).length = width) (xs : List α) (i : Fin xs.length)
    (j : Fin width) (zero : β) :
    (xs.flatMap encode).getD (width * i.val + j.val) zero = (encode xs[i.val]).getD j.val zero := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons a xs ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero,
          List.flatMap_cons, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by simpa only [length a] using j.isLt)]
      · simp only [Fin.val_succ, List.getElem_cons_succ, List.flatMap_cons,
          List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [length a]; exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right width (Nat.succ_pos _))), length a]
        have index : width * (i.val + 1) + j.val - width = width * i.val + j.val := by rw [Nat.mul_add, Nat.mul_one]; omega
        rw [index]
        exact ih i

/-- Little-endian reads recover every serialized field word. -/
theorem readWord_leafBytes (xs : List K) (i : Fin xs.length) :
    readWord (leafBytes xs) (8 * i.val) = laneWord xs[i.val] := by
  apply word_eq_of_bytes
  intro j
  rw [readWord_byte]
  have byte := flatMap_getD wordBytes 8 wordBytes_length xs i j 0
  have bound : 8 * i.val + j.val < (leafBytes xs).size := by
    simp only [leafBytes, ByteArray.size, List.size_toArray, List.length_flatMap,
      wordBytes_length, List.map_const', List.sum_replicate, smul_eq_mul]
    omega
  simp only [leafBytes, ByteArray.size] at bound ⊢
  rw [getElem!_pos _ (8 * i.val + j.val) bound]
  change ((xs.flatMap wordBytes).toArray)[8 * i.val + j.val] = _
  rw [List.getElem_toArray]
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      simpa only [List.size_toArray] using bound), Option.getD_some, wordBytes,
    List.getElem?_map, List.getElem?_range j.isLt, Option.map_some] using byte

end
end CompStark.Keccak.Commit
