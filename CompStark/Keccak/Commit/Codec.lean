/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Bytes

/-! Prefix codecs for the production scalar stream. A decoder retains its unread suffix. -/

@[expose] public section
namespace CompStark.Keccak.Commit
open CompStark.BinaryFields

/-- A prefix parser and canonical serialization, with an arbitrary-suffix round trip. -/
structure Codec (α β : Type) where
  /-- Canonical transport elements. -/
  write : α → List β
  /-- Read exactly one value, leaving the unconsumed suffix. -/
  read : List β → Option (α × List β)
  /-- Reading serialized data preserves any following transport. -/
  read_write : ∀ a rest, read (write a ++ rest) = some (a, rest)

/-- One transport element. -/
def atom {α : Type} : Codec α α where
  write a := [a]
  read
    | [] => none
    | a :: rest => some (a, rest)
  read_write _ _ := rfl

/-- Concatenate two codecs in field order. -/
def Codec.prod {α β γ : Type} (first : Codec α γ) (second : Codec β γ) : Codec (α × β) γ where
  write a := first.write a.1 ++ second.write a.2
  read input := (first.read input).bind fun (a, input) =>
    (second.read input).map fun (b, input) => ((a, b), input)
  read_write a rest := by
    simp only [List.append_assoc, first.read_write, Option.bind_some, second.read_write,
      Option.map_some]

/-- Dependent concatenation when an earlier prover message selects the continuation. -/
def Codec.sigma {α γ : Type} {β : α → Type} (first : Codec α γ)
    (second : (a : α) → Codec (β a) γ) : Codec ((a : α) × β a) γ where
  write value := first.write value.1 ++ (second value.1).write value.2
  read input := (first.read input).bind fun (a, input) =>
    ((second a).read input).map fun (b, input) => (⟨a, b⟩, input)
  read_write value rest := by
    simp only [List.append_assoc, first.read_write, Option.bind_some,
      (second value.1).read_write, Option.map_some]

/-- A challenge salt contributes no bytes to the production proof. -/
def unit {α : Type} : Codec PUnit α where
  write _ := []
  read input := some (PUnit.unit, input)
  read_write _ _ := rfl

/-- Change a codec's semantic carrier through an equivalence. -/
def Codec.map {α β γ : Type} (codec : Codec α γ) (equiv : α ≃ β) : Codec β γ where
  write a := codec.write (equiv.symm a)
  read input := (codec.read input).map fun (a, rest) => (equiv a, rest)
  read_write a rest := by
    simp only [codec.read_write, Option.map_some, equiv.apply_symm_apply]

/-- Read a counted sequence without trusting any zero-filled out-of-bounds reads. -/
def readList {α β : Type} (codec : Codec α β) : ℕ → List β → Option (List α × List β)
  | 0, input => some ([], input)
  | n + 1, input => (codec.read input).bind fun (head, input) =>
      (readList codec n input).map fun (tail, input) => (head :: tail, input)

/-- Counted sequence parsing preserves any following transport. -/
theorem readList_write {α β : Type} (codec : Codec α β) (values : List α) (rest : List β) :
    readList codec values.length (values.flatMap codec.write ++ rest) = some (values, rest) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.length_cons, List.flatMap_cons, readList, List.append_assoc,
        codec.read_write, Option.bind_some, ih, Option.map_some]

/-- A fixed coordinate vector, in increasing index order, backed by one decoded list. -/
def vector {α β : Type} (codec : Codec α β) (n : ℕ) : Codec (Fin n → α) β where
  write a := (List.ofFn a).flatMap codec.write
  read input := (readList codec n input).bind fun (values, rest) =>
    if length : values.length = n then
      some (fun i => values[i.val]'(by omega), rest)
    else none
  read_write a rest := by
    have parsed := readList_write codec (List.ofFn a) rest
    rw [List.length_ofFn] at parsed
    simp only [parsed, Option.bind_some, List.length_ofFn, dite_true, List.getElem_ofFn]

/-- Dependent coordinate vectors in increasing table order. -/
def dependentVector {β : Type} : (n : ℕ) → {α : Fin n → Type} →
    ((i : Fin n) → Codec (α i) β) → Codec ((i : Fin n) → α i) β
  | 0, _, _ =>
      { write := fun _ => []
        read := fun input => some (fun i => Fin.elim0 i, input)
        read_write := fun a _ => by congr; funext i; exact Fin.elim0 i }
  | n + 1, _, codecs =>
      (((codecs 0).prod (dependentVector n (fun i => codecs i.succ))).map
        { toFun := fun (head, tail) => Fin.cons head tail
          invFun := fun a => (a 0, fun i => a i.succ)
          left_inv := fun _ => rfl
          right_inv := fun a => by funext i; exact Fin.cases rfl (fun _ => rfl) i })

/-- Vector serialization is concatenation in coordinate order. -/
theorem vector_write {α β : Type} (codec : Codec α β) (n : ℕ) (a : Fin n → α) :
    (vector codec n).write a = (List.ofFn a).flatMap codec.write := rfl

/-- All three polynomial-basis limbs of an extension scalar, in wire order. -/
def scalarBytes (value : E) : List UInt8 :=
  Keccak.Commit.wordBytes (value.limb 0) ++ Keccak.Commit.wordBytes (value.limb 1) ++
    Keccak.Commit.wordBytes (value.limb 2)

/-- A production scalar occupies exactly 24 bytes. -/
theorem scalarBytes_length (value : E) : (scalarBytes value).length = 24 := by
  simp only [scalarBytes, List.length_append, Keccak.Commit.wordBytes_length]

/-- Restrict a codec to values decoded by a checked semantic conversion. -/
def Codec.refine {α β γ : Type} (codec : Codec α γ) (encode : β → α)
    (decode : α → Option β) (inverse : ∀ b, decode (encode b) = some b) : Codec β γ where
  write b := codec.write (encode b)
  read input := (codec.read input).bind fun (a, rest) =>
    (decode a).map fun b => (b, rest)
  read_write b rest := by
    simp only [codec.read_write, Option.bind_some, inverse, Option.map_some]

/-- A fixed number of bytes, with no implicit zero extension on short input. -/
def bytes (n : ℕ) : Codec (Vector UInt8 n) UInt8 where
  write value := value.toList
  read input := if bound : (input.take n).length = n then
      some (⟨(input.take n).toArray, by simpa only [List.size_toArray] using bound⟩, input.drop n)
    else none
  read_write value rest := by
    have take : (value.toList ++ rest).take n = value.toList := by
      simpa only [Vector.length_toList] using (List.take_left (l₁ := value.toList) (l₂ := rest))
    have drop : (value.toList ++ rest).drop n = rest := by
      simpa only [Vector.length_toList] using (List.drop_left (l₁ := value.toList) (l₂ := rest))
    simp only [take, Vector.length_toList, dite_true, drop, Vector.toArray_toList]

/-- Eight bytes encode one unrestricted polynomial-basis field word. -/
def word : Codec K UInt8 := (bytes 8).refine
  (fun value => ⟨(Keccak.Commit.wordBytes value).toArray, by simp only [List.size_toArray,
    Keccak.Commit.wordBytes_length]⟩)
  (fun value => some (Keccak.Lanes.wordLane (Keccak.Commit.readWord ⟨value.toArray⟩ 0)))
  (fun value => by
    have read := Keccak.Commit.readWord_leafBytes [value] ⟨0, by simp only [List.length_cons, List.length_nil]; omega⟩
    simpa only [Keccak.Commit.leafBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Nat.mul_zero, List.getElem_cons_zero, Keccak.Lanes.wordLane_laneWord] using
        congrArg (fun v => some (Keccak.Lanes.wordLane v)) read)

/-- Read a complete little-endian field word directly from eight list cells. -/
def readWordDirect : List UInt8 → Option (K × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    let w0 := (0 : UInt64) ||| (b0.toUInt64 <<< 0)
    let w1 := w0 ||| (b1.toUInt64 <<< 8)
    let w2 := w1 ||| (b2.toUInt64 <<< 16)
    let w3 := w2 ||| (b3.toUInt64 <<< 24)
    let w4 := w3 ||| (b4.toUInt64 <<< 32)
    let w5 := w4 ||| (b5.toUInt64 <<< 40)
    let w6 := w5 ||| (b6.toUInt64 <<< 48)
    let w7 := w6 ||| (b7.toUInt64 <<< 56)
    some (Keccak.Lanes.wordLane w7, rest)
  | _ => none
/-- Direct word reading preserves all short-input failures and the unread suffix. -/
theorem readWordDirect_eq (input : List UInt8) : readWordDirect input = word.read input := by
  rcases input with _ | ⟨b0, input⟩
  · rfl
  rcases input with _ | ⟨b1, input⟩
  · rfl
  rcases input with _ | ⟨b2, input⟩
  · rfl
  rcases input with _ | ⟨b3, input⟩
  · rfl
  rcases input with _ | ⟨b4, input⟩
  · rfl
  rcases input with _ | ⟨b5, input⟩
  · rfl
  rcases input with _ | ⟨b6, input⟩
  · rfl
  rcases input with _ | ⟨b7, input⟩
  · rfl
  simp only [word, Codec.refine, bytes, List.take_succ_cons, List.take_zero,
    List.length_cons, List.length_nil, ↓reduceDIte, List.drop_succ_cons, List.drop_zero,
    Option.bind_some, Option.map_some]
  simp only [readWordDirect, Keccak.Commit.readWord, show List.range 8 = [0,1,2,3,4,5,6,7] from rfl,
    List.foldl_cons, List.foldl_nil]
  rfl

/-- The native word codec keeps canonical serialization and directly decodes eight cells. -/
def wordDirect : Codec K UInt8 where
  write := word.write
  read := readWordDirect
  read_write value rest := by
    rw [readWordDirect_eq]
    exact word.read_write value rest

/-- Every native word parse preserves the exact specification codec. -/
@[csimp] theorem word_direct : word = wordDirect := by
  have equal : readWordDirect = word.read := funext readWordDirect_eq
  unfold wordDirect
  simp only [equal]

/-- The three-limb production scalar codec; every 192-bit pattern is a field element. -/
def scalar : Codec E UInt8 := ((word.prod word).prod word).map
  { toFun := fun value => E.ofLimbs value.1.1 value.1.2 value.2
    invFun := fun value => ((value.limb 0, value.limb 1), value.limb 2)
    left_inv := fun _ => rfl
    right_inv := ofLimbs_limb }

/-- The scalar codec uses exactly the Rust coefficient order. -/
theorem scalar_write (value : E) : scalar.write value = scalarBytes value := rfl

/-- Every field scalar round-trips with no dependence on the subsequent bytes. -/
theorem scalar_read_write (value : E) (rest : List UInt8) :
    scalar.read (scalarBytes value ++ rest) = some (value, rest) := scalar.read_write value rest

/-- Fixed-width, little-endian bincode `u64`. -/
def uint64 : Codec UInt64 UInt8 := word.map
  { toFun := Keccak.Lanes.laneWord
    invFun := Keccak.Lanes.wordLane
    left_inv := Keccak.Lanes.wordLane_laneWord
    right_inv := Keccak.Lanes.laneWord_wordLane }

/-- A Rust vector whose length is representable by bincode's 64-bit length field. -/
abbrev BoundedList (α : Type) := {values : List α // values.length < 2 ^ 64}

/-- Fixed-integer bincode vectors: a little-endian 64-bit count, then the entries. -/
def sequence {α : Type} (codec : Codec α UInt8) : Codec (BoundedList α) UInt8 where
  write value := uint64.write value.val.length.toUInt64 ++ value.val.flatMap codec.write
  read input := (uint64.read input).bind fun (length, input) =>
    (readList codec length.toNat input).bind fun (values, input) =>
      if bound : values.length < 2 ^ 64 then some (⟨values, bound⟩, input) else none
  read_write value rest := by
    have length : value.val.length.toUInt64.toNat = value.val.length := by
      change value.val.length % 2 ^ 64 = value.val.length
      exact Nat.mod_eq_of_lt value.property
    simp only [List.append_assoc, uint64.read_write, Option.bind_some, length,
      readList_write, value.property, dite_true]

end CompStark.Keccak.Commit
