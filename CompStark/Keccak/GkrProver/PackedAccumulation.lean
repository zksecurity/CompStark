/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PackedBlocks
public import CompStark.Keccak.GkrProver.ProductAccumulation
import all CompPoly.Fields.Binary.BF64.WordExt3Dot
import all CompPoly.Fields.Binary.BF64.Packed

/-! Structural accumulation invariants for the native input-opening buffers. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Add a consecutive block of field values to an existing packed buffer. -/
def addPackedBlock (out : PackedE) (offset count : Nat) (value : Nat → W) : PackedE :=
  (List.range count).foldl (fun state j => state.set (offset+j) (state.get (offset+j)+value j)) out

/-- Adding an in-bounds packed block preserves the complete buffer length. -/
theorem addPackedBlock_size (out : PackedE) (offset count : Nat) (value : Nat → W)
    (hb : offset+count ≤ out.size) : (addPackedBlock out offset count value).size = out.size := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hs := ih (by omega)
    unfold addPackedBlock
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [PackedE.size_set _ _ _ (by change offset+count < (addPackedBlock out offset count value).size; rw [hs]; omega)]
    exact hs

/-- Adding a packed block changes precisely its selected coordinates by their supplied increments. -/
theorem addPackedBlock_get (out : PackedE) (offset count : Nat) (value : Nat → W)
    (hb : offset+count ≤ out.size) (i : Nat) (hi : i < out.size) :
    (addPackedBlock out offset count value).get i =
      out.get i + if offset ≤ i ∧ i < offset+count then value (i-offset) else 0 := by
  induction count generalizing i with
  | zero => simp only [addPackedBlock,List.range_zero,List.foldl_nil,
      show ¬(offset ≤ i ∧ i < offset) by omega,ite_false,add_zero]
  | succ count ih =>
    have hs := addPackedBlock_size out offset count value (by omega)
    unfold addPackedBlock
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [PackedE.get_set _ _ _ (by change offset+count < (addPackedBlock out offset count value).size; rw [hs]; omega)
      (by change i < (addPackedBlock out offset count value).size; rw [hs]; exact hi)]
    by_cases he : offset+count = i
    · subst i
      rw [ite_eq_left rfl]
      change (addPackedBlock out offset count value).get (offset+count)+value count = _
      rw [ih (by omega) (offset+count) (by omega),ite_eq_right (by omega),add_zero,ite_eq_left (by omega)]
      exact congrArg (fun x => out.get (offset+count)+value x) (by omega)
    · rw [ite_eq_right he]
      change (addPackedBlock out offset count value).get i = _
      rw [ih (by omega) i hi]
      have heq : (offset ≤ i ∧ i < offset+count) ↔ (offset ≤ i ∧ i < offset+(count+1)) := by omega
      simp only [heq]

/-- A bounded packed-buffer fold preserves its dimension and adds exactly the selected scalar terms. -/
theorem foldl_packed_value_sum {A S : Type} (view : S → PackedE) (step : S → A → S)
    (term : A → W) {n : Nat} (i : Fin n) (xs : List A)
    (hsize : ∀ state a, a ∈ xs → (view state).size = n → (view (step state a)).size = n)
    (hget : ∀ state a, a ∈ xs → (view state).size = n →
      (view (step state a)).get i.val = (view state).get i.val+term a)
    (state : S) (hs : (view state).size = n) :
    (view (xs.foldl step state)).size = n ∧
      (view (xs.foldl step state)).get i.val = (view state).get i.val+(xs.map term).sum := by
  induction xs generalizing state with
  | nil => exact ⟨hs,(add_zero _).symm⟩
  | cons a xs ih =>
    rw [List.foldl_cons]
    obtain ⟨hlen,hval⟩ := ih
      (by intro state b hb; exact hsize state b (List.mem_cons_of_mem a hb))
      (by intro state b hb; exact hget state b (List.mem_cons_of_mem a hb))
      (step state a) (hsize state a List.mem_cons_self hs)
    refine ⟨hlen,?_⟩
    rw [hval,hget state a List.mem_cons_self hs,List.map_cons,List.sum_cons,add_assoc]

/-- Pointwise agreement on the traversed list preserves a structural accumulator fold. -/
theorem foldl_congr_mem {A S : Type} (xs : List A) (f g : S → A → S)
    (h : ∀ state a, a ∈ xs → f state a = g state a) (state : S) :
    xs.foldl f state = xs.foldl g state := by
  induction xs generalizing state with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldl_cons,List.foldl_cons,h state a List.mem_cons_self]
    exact ih (by intro state b hb; exact h state b (List.mem_cons_of_mem a hb)) _

/-- Every complete or out-of-bounds 32-bit read of the raw zero allocator is zero. -/
theorem zeroBytes_getUInt32LE (n offset : Nat) : (zeroBytes n).getUInt32LE! offset = 0 := by
  unfold ByteArray.getUInt32LE!
  rw [zeroBytes_size]
  split
  · rename_i h
    rw [zeroBytes_get _ _ (by omega),zeroBytes_get _ _ (by omega),
      zeroBytes_get _ _ (by omega),zeroBytes_get _ _ (by omega)]
    rfl
  · rfl

/-- Every in-bounds extension coordinate of the native zero buffer is the field zero. -/
theorem PackedE.get_zeros (n i : Nat) (hi : i < n) : (PackedE.zeros n).get i = 0 := by
  simp only [PackedE.get,PackedE.zeros,hi,dite_true,WordExt3.read,Packed.read,Packed.get,
    ByteArray.getUInt32LE,zeroBytes_getUInt32LE]
  rfl

end CompStark.Keccak.GkrProver
