/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Data.ByteArray.Packed
import Mathlib.Data.List.OfFn

/-! Little-endian word generation in one preallocated byte buffer. -/

@[expose] public section
namespace CompStark.Keccak.Commit.WordBuffer
open CompPoly

/-- Fill consecutive 32-bit slots of one byte buffer through the approved word accessor. -/
def generate (n : Nat) (hu : 4 * n < USize.size) (word : Nat → UInt32) : ByteArray :=
  Fin.foldl n (fun bytes i =>
    PackedRepr.setIf (4 * n) hu bytes i.val.toUSize (word i.val))
    (PackedRepr.replicate n (0 : UInt32))

/-- A direct word store carries the fixed buffer length in its proof, without runtime checks. -/
@[inline] def store (n : Nat) (hu : 4 * n < USize.size)
    (bytes : { b : ByteArray // b.size = 4 * n }) (i : Fin n) (v : UInt32) :
    { b : ByteArray // b.size = 4 * n } :=
  ⟨PackedRepr.setAt bytes.val i.val.toUSize v
    (by rw [bytes.property, PackedRepr.width_uint32, Nat.mul_div_cancel_left _ (by decide),
        USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)]; exact i.isLt)
    (by rw [bytes.property]; exact hu), by rw [PackedRepr.size_setAt, bytes.property]⟩

/-- Direct stores and checked stores agree on every allocated word slot. -/
theorem store_eq (n : Nat) (hu : 4 * n < USize.size)
    (bytes : { b : ByteArray // b.size = 4 * n }) (i : Fin n) (v : UInt32) :
    (store n hu bytes i v).val = PackedRepr.setIf (4 * n) hu bytes.val i.val.toUSize v := by
  have valid : bytes.val.size = 4 * n ∧ i.val.toUSize.toNat < bytes.val.size / PackedRepr.width UInt32 := by
    rw [bytes.property, PackedRepr.width_uint32, Nat.mul_div_cancel_left _ (by decide),
      USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)]
    exact ⟨rfl, i.isLt⟩
  simp only [store, PackedRepr.setIf, dite_eq_left valid]

/-- Store at a native offset whose logical index is retained only in erased proofs. -/
@[inline] def storeNative (n : Nat) (hu : 4 * n < USize.size)
    (bytes : { b : ByteArray // b.size = 4 * n }) (i : Fin n) (index : USize)
    (same : index = i.val.toUSize) (v : UInt32) :
    { b : ByteArray // b.size = 4 * n } :=
  ⟨PackedRepr.setAt bytes.val index v
    (by rw [same, bytes.property, PackedRepr.width_uint32,
        Nat.mul_div_cancel_left _ (by decide),
        USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)]; exact i.isLt)
    (by rw [bytes.property]; exact hu), by rw [PackedRepr.size_setAt, bytes.property]⟩

/-- Native offset arithmetic writes exactly the logical slot. -/
theorem storeNative_eq (n : Nat) (hu : 4 * n < USize.size)
    (bytes : { b : ByteArray // b.size = 4 * n }) (i : Fin n) (index : USize)
    (same : index = i.val.toUSize) (v : UInt32) :
    storeNative n hu bytes i index same v = store n hu bytes i v := by
  subst index
  rfl

/-- Generate words in one allocated buffer with proof-only bounds. -/
@[inline] def generateDirect (n : Nat) (hu : 4 * n < USize.size) (word : Nat → UInt32) : ByteArray :=
  (Fin.foldl n (fun bytes i => store n hu bytes i (word i.val))
    ⟨PackedRepr.replicate n (0 : UInt32), by rw [PackedRepr.replicate_eq,
      PackedRepr.size_encode_uint32, Array.size_replicate]⟩).val

/-- Erasing the fixed-size invariant gives exactly the checked buffer generator. -/
@[csimp] theorem generate_direct_code : generate = generateDirect := by
  funext n hu word
  have loop : ∀ k (hk : k ≤ n) (bytes : { b : ByteArray // b.size = 4 * n }),
      (Fin.foldl k (fun bytes i => store n hu bytes ⟨i.val, by omega⟩ (word i.val)) bytes).val =
        Fin.foldl k (fun bytes i => PackedRepr.setIf (4 * n) hu bytes i.val.toUSize (word i.val)) bytes.val := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro hk bytes
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [Fin.val_castSucc, Fin.val_last, store_eq]
      rw [ih (by omega)]
  exact (loop n (Nat.le_refl _) ⟨PackedRepr.replicate n (0 : UInt32), by
    rw [PackedRepr.replicate_eq, PackedRepr.size_encode_uint32, Array.size_replicate]⟩).symm

/-- Folding a generated finite sequence is its indexed fold. -/
theorem foldOfFn {α β : Type} {n : Nat} (f : β → α → β) (xs : Fin n → α) (out : β) :
    (List.ofFn xs).foldl f out = Fin.foldl n (fun out i => f out (xs i)) out := by
  rw [Fin.foldl_eq_finRange_foldl, List.finRange]
  have mapped : List.ofFn xs = (List.ofFn (fun i : Fin n => i)).map xs := by
    rw [List.map_ofFn]; rfl
  rw [mapped, List.foldl_map]

/-- A flat indexed fold equals consecutive fixed-width row folds. -/
theorem foldl_mul {α : Type} (m n : Nat) (f : α → Fin (m * n) → α) (out : α) :
    Fin.foldl (m * n) f out = Fin.foldl m (fun out i =>
      Fin.foldl n (fun out j => f out ⟨i.val * n + j.val, by
        have h := Nat.mul_le_mul_right n i.isLt
        rw [Nat.succ_mul] at h
        omega⟩) out) out := by
  rw [Fin.foldl_eq_finRange_foldl, List.finRange, List.ofFn_mul, List.foldl_flatten]
  simp only [foldOfFn]

/-- Filling an array prefix preserves its allocated length. -/
theorem size_fill (n : Nat) (word : Nat → UInt32) (initial : Array UInt32) :
    (Fin.foldl n (fun a i => a.set! i.val (word i.val)) initial).size = initial.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Fin.foldl_succ_last, Array.size_set!]
    simpa only [Fin.val_castSucc] using ih

/-- One in-bounds update changes exactly its indexed projection. -/
theorem get_set (a : Array UInt32) (i j : Nat) (v : UInt32) (hi : i < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ hi]
  · rw [ite_eq_right h, Array.getElem!_set!_ne _ _ _ _ h]

/-- A filled prefix contains its generated words and retains the rest of the array. -/
theorem get_fill (n : Nat) (word : Nat → UInt32) (initial : Array UInt32)
    (hn : n ≤ initial.size) (j : Nat) :
    (Fin.foldl n (fun a i => a.set! i.val (word i.val)) initial)[j]! =
      if j < n then word j else initial[j]! := by
  induction n with
  | zero => simp only [Fin.foldl_zero, Nat.not_lt_zero, ↓reduceIte]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [get_set _ _ _ _ (by rw [size_fill]; omega), ih (by omega)]
    by_cases h : n = j
    · subst j
      simp only [Nat.lt_succ_self, ↓reduceIte]
    · by_cases hj : j < n
      · simp only [h, hj, show j < n + 1 by omega, ↓reduceIte]
      · simp only [h, hj, show ¬j < n + 1 by omega, ↓reduceIte]

/-- Filling all allocated slots is the generated word array. -/
theorem fill_eq (n : Nat) (word : Nat → UInt32) :
    Fin.foldl n (fun a i => a.set! i.val (word i.val)) (Array.replicate n 0) =
      Array.ofFn (fun i : Fin n => word i.val) := by
  apply Array.ext
  · simp only [size_fill, Array.size_replicate, Array.size_ofFn]
  · intro i hi hj
    have bound : i < n := by simpa only [Array.size_ofFn] using hj
    have get := get_fill n word (Array.replicate n 0) (by rw [Array.size_replicate]) i
    simpa only [bound, ↓reduceIte, getElem!_pos (Fin.foldl n (fun a i => a.set! i.val (word i.val)) (Array.replicate n 0)) i hi, Array.getElem_ofFn] using get

/-- Buffer generation has exactly the packed image of the generated words. -/
theorem generate_eq (n : Nat) (hu : 4 * n < USize.size) (word : Nat → UInt32) :
    generate n hu word = PackedRepr.encode (Array.ofFn (fun i : Fin n => word i.val)) := by
  rw [generate, PackedRepr.replicate_eq]
  have commute (a : Array UInt32) (ha : a.size = n) (i : Fin n) :
      PackedRepr.encode (a.set! i.val (word i.val)) =
        PackedRepr.setIf (4 * n) hu (PackedRepr.encode a) i.val.toUSize (word i.val) := by
    rw [PackedRepr.setIf_encode_of_eq a _ _ _ hu (by rw [PackedRepr.width_uint32, ha]),
      USize.toNat_ofNat_of_lt' (by have := i.isLt; omega)]
    rfl
  have loop : ∀ k (hk : k ≤ n), ∀ (a : Array UInt32), a.size = n →
      Fin.foldl k (fun bytes i => PackedRepr.setIf (4 * n) hu bytes i.val.toUSize (word i.val))
        (PackedRepr.encode a) =
      PackedRepr.encode (Fin.foldl k (fun a i => a.set! i.val (word i.val)) a) := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro hk a ha
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih (by omega) a ha]
      symm
      exact commute _ (by rw [size_fill, ha]) ⟨k, by omega⟩
  rw [loop n (Nat.le_refl _) _ (Array.size_replicate ..), fill_eq]

end CompStark.Keccak.Commit.WordBuffer
