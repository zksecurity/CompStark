/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Bytes
public import Std.Data.HashMap.Lemmas

/-! Finite hash memo tables retain the exact hash on every byte string. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Keccak.Commit

variable (hash : ByteArray → Digest)

/-- Hash a list key through its exact byte-array representation. -/
def hashList (bytes : List UInt8) : Digest := hash ⟨bytes.toArray⟩

/-- Inserting computed hashes preserves the hash value associated with every stored key. -/
theorem hashMemo_fold_sound (inputs : List (List UInt8))
    (initial : Std.HashMap (List UInt8) Digest)
    (sound : ∀ key value, initial[key]? = some value → value = hashList hash key) :
    ∀ key value, (inputs.foldl (fun memo key => if memo.contains key then memo else memo.insert key (hashList hash key)) initial)[key]? =
      some value → value = hashList hash key := by
  induction inputs generalizing initial with
  | nil => exact sound
  | cons input rest ih =>
      apply ih
      intro key value found
      dsimp only at found
      split at found
      · exact sound key value found
      · rw [Std.HashMap.getElem?_insert] at found
        split at found
        · rename_i same
          have equal : input = key := eq_of_beq same
          subst key
          exact (Option.some.inj found).symm
        · exact sound key value found

/-- Materialize the computed hash of each requested byte string once. -/
@[noinline, nospecialize] def hashMemo (inputs : List (List UInt8)) :
    Std.HashMap (List UInt8) Digest :=
  inputs.foldl (fun memo key => if memo.contains key then memo else memo.insert key (hashList hash key)) {}

/-- Every memoized value is the hash of its key. -/
theorem hashMemo_sound (inputs : List (List UInt8)) (key : List UInt8) (value : Digest)
    (found : (hashMemo hash inputs)[key]? = some value) : value = hashList hash key := by
  exact hashMemo_fold_sound hash inputs {} (by
    intro key value impossible
    simp only [Std.HashMap.getElem?_empty] at impossible
    cases impossible) key value found

/-- Read a computed memo entry or compute the exact hash for an unlisted input. -/
@[macro_inline] def hashWithMemo (memo : Std.HashMap (List UInt8) Digest) (bytes : ByteArray) : Digest :=
  match memo[bytes.data.toList]? with
  | some value => value
  | none => hash bytes

/-- The memoized implementation equals the hash on every input, including unlisted inputs. -/
theorem hashWithMemo_eq (inputs : List (List UInt8)) (bytes : ByteArray) :
    hashWithMemo hash (hashMemo hash inputs) bytes = hash bytes := by
  unfold hashWithMemo
  split
  · rename_i value found
    rw [hashMemo_sound hash inputs _ value found]
    cases bytes
    simp only [hashList, Array.toArray_toList]
  · rfl

end CompStark.Keccak.Commit
