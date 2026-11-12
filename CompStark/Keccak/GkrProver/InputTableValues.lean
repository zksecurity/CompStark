/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.InputTables

/-! Exact weighted committed-bit values of the retained native input-opening table. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

attribute [local irreducible] inputGroupValue inputGroups addPackedBlock eqTable

/-- The retained input address names one slot, one low instance and one bit position uniquely. -/
theorem inputBlock_address (slot inst : Nat) (hi : inst < 16)
    (s : Fin 64) (i : Fin 16) (z : Fin 64) :
    ((inst+16*slot)*64 ≤ (i.val+16*s.val)*64+z.val ∧
      (i.val+16*s.val)*64+z.val < (inst+16*slot)*64+64) ↔ slot = s.val ∧ inst = i.val := by
  have := i.isLt
  have := z.isLt
  omega

/-- A complete group traversal preserves the buffer size and adds exactly its selected input block. -/
theorem inputGroups_value (committed : Array UInt64) (n : Nat) (weights : Array W)
    (slot inst : Nat) (hi : inst < 16) (s : Fin 64) (i : Fin 16) (z : Fin 64)
    (out : PackedE) (hout : out.size = 65536) (hs : slot < 64) :
    (inputGroups committed n weights slot inst out).size = 65536 ∧
    (inputGroups committed n weights slot inst out).get ((i.val+16*s.val)*64+z.val) =
      out.get ((i.val+16*s.val)*64+z.val) + if slot = s.val ∧ inst = i.val then
        ∑ group ∈ Finset.range (n/128),inputGroupValue committed n weights s.val i.val group z.val else 0 := by
  let target : Fin 65536 := ⟨(i.val+16*s.val)*64+z.val,by
    have := i.isLt; have := s.isLt; have := z.isLt; omega⟩
  let term (group : Nat) : W := if slot = s.val ∧ inst = i.val then
    inputGroupValue committed n weights s.val i.val group z.val else 0
  have h := foldl_packed_value_sum id
    (fun state group => addPackedBlock state ((inst+16*slot)*64) 64
      (inputGroupValue committed n weights slot inst group)) term target (List.range (n/128))
    (by
      intro state group _ hstate
      simp only [id_eq] at hstate ⊢
      exact (addPackedBlock_size state _ _ _ (by rw [hstate]; omega)).trans hstate)
    (by
      intro state group _ hstate
      simp only [id_eq] at hstate ⊢
      rw [addPackedBlock_get _ _ _ _ (by rw [hstate]; omega) _ (by rw [hstate]; exact target.isLt)]
      change state.get target.val+_ = state.get target.val+term group
      apply congrArg (fun x => state.get target.val+x)
      change (if (inst+16*slot)*64 ≤ (i.val+16*s.val)*64+z.val ∧
        (i.val+16*s.val)*64+z.val < (inst+16*slot)*64+64 then _ else _) = _
      simp only [inputBlock_address slot inst hi s i z]
      by_cases he : slot = s.val ∧ inst = i.val
      · simp only [term,he,and_self,ite_true]
        dsimp only [target]
        rw [show (i.val+16*s.val)*64+z.val-(i.val+16*s.val)*64 = z.val by omega]
      · simp only [term,he,ite_false]) out hout
  simp only [id_eq,list_range_sum] at h
  simp only [inputGroups]
  refine ⟨h.1,?_⟩
  rw [h.2]
  apply congrArg (fun x => out.get target.val+x)
  by_cases he : slot = s.val ∧ inst = i.val <;> simp only [term,he,and_self,ite_true,ite_false,Finset.sum_const_zero]

/-- The native retained input table contains all sixty-four slots and sixteen low instance coordinates. -/
theorem inputBits_values (committed : Array UInt64) (n : Nat) (point : Array W)
    (s : Fin 64) (i : Fin 16) (z : Fin 64) :
    (inputBits committed n point).size = 65536 ∧
    (inputBits committed n point)[(i.val+16*s.val)*64+z.val]! =
      ∑ group ∈ Finset.range (n/128),inputGroupValue committed n (eqTable point) s.val i.val group z.val := by
  let target : Fin 65536 := ⟨(i.val+16*s.val)*64+z.val,by
    have := i.isLt; have := s.isLt; have := z.isLt; omega⟩
  let value := ∑ group ∈ Finset.range (n/128),inputGroupValue committed n (eqTable point) s.val i.val group z.val
  let step (out : PackedE) (slot : Nat) :=
    (List.range 16).foldl (fun state inst => inputGroups committed n (eqTable point) slot inst state) out
  have hinner (out : PackedE) (hout : out.size = 65536) (slot : Nat) (hs : slot < 64) :
      (step out slot).size = 65536 ∧
      (step out slot).get target.val = out.get target.val + if slot = s.val then value else 0 := by
    have h := foldl_packed_value_sum id
      (fun state inst => inputGroups committed n (eqTable point) slot inst state)
      (fun inst => if slot = s.val ∧ inst = i.val then value else 0) target (List.range 16)
      (by intro state inst hm hstate; exact (inputGroups_value committed n (eqTable point)
        slot inst (List.mem_range.mp hm) s i z state hstate hs).1)
      (by intro state inst hm hstate; exact (inputGroups_value committed n (eqTable point)
        slot inst (List.mem_range.mp hm) s i z state hstate hs).2) out hout
    simp only [id_eq,list_range_sum] at h
    refine ⟨h.1,?_⟩
    change (step out slot).size = 65536 ∧
      (step out slot).get target.val = out.get target.val+_ at h
    rw [h.2]
    apply congrArg (fun x => out.get target.val+x)
    by_cases he : slot = s.val
    · simp only [he,true_and,ite_true,Finset.sum_ite_eq',Finset.mem_range,i.isLt]
    · simp only [he,false_and,ite_false,Finset.sum_const_zero]
  have h := foldl_packed_value_sum id step
    (fun slot => if slot = s.val then value else 0) target (List.range 64)
    (by intro state slot hm hstate; exact (hinner state hstate slot (List.mem_range.mp hm)).1)
    (by intro state slot hm hstate; exact (hinner state hstate slot (List.mem_range.mp hm)).2)
    (PackedE.zeros 65536) rfl
  simp only [id_eq,list_range_sum] at h
  have hv : ((List.range 64).foldl step (PackedE.zeros 65536)).get target.val = value := by
    rw [h.2,PackedE.get_zeros _ _ target.isLt,zero_add,Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_range.mpr s.isLt)]
  rw [inputBits_eq_blocks]
  refine ⟨?_,?_⟩
  · change ((List.range 64).foldl step (PackedE.zeros 65536)).toArray.size = 65536
    simpa only [PackedE.toArray,Array.size_ofFn] using h.1
  · change ((List.range 64).foldl step (PackedE.zeros 65536)).toArray[target.val]! = value
    rw [PackedE.get_toArray _ _ (by rw [h.1]; exact target.isLt)]
    exact hv

end CompStark.Keccak.GkrProver
