/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.BinaryValues

/-! Segment-pack enumeration of the polynomials retained by the native product loop. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64

attribute [local irreducible] product productState productRow addProductCoefficients

/-- A fold whose list view appends each row has the exact concatenated row sequence. -/
theorem foldl_list_append {A B S : Type} (view : S → List B) (step : S → A → S)
    (rows : A → List B) (hstep : ∀ state a, view (step state a) = view state++rows a)
    (xs : List A) (state : S) :
    view (xs.foldl step state) = view state++xs.flatMap rows := by
  induction xs generalizing state with
  | nil => rw [List.foldl_nil,List.flatMap_nil,List.append_nil]
  | cons a xs ih => rw [List.foldl_cons,ih,hstep,List.flatMap_cons,List.append_assoc]

/-- A state equal to a list fold inherits its exact appended list view from an empty initial view. -/
theorem list_view_of_fold_eq {A B S : Type} (view : S → List B) (step : S → A → S)
    (rows : A → List B) (xs : List A) (state initial : S)
    (heq : state = xs.foldl step initial)
    (hfold : view (xs.foldl step initial) = view initial++xs.flatMap rows)
    (hempty : view initial = []) : view state = xs.flatMap rows := by
  rw [heq,hfold,hempty,List.nil_append]

/-- One segment-pack update of the retained production coefficient state. -/
def retainedProductStep (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (m : Nat) (state : Array W × Array PackedE) (b : Nat) : Array W × Array PackedE :=
  (addProductCoefficients state.1 (eqTable claim.point)[m*2^(w.nLog-4)+b]!
    (productRow w d claim maps m b),state.2.push (productRow w d claim maps m b))

/-- One complete segment block of the retained production coefficient state. -/
def retainedProductOuter (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (state : Array W × Array PackedE) (m : Nat) : Array W × Array PackedE :=
  (List.range (2^(w.nLog-4))).foldl (retainedProductStep w d claim maps m) state

/-- The native product state equals its named structural fold. -/
theorem productState_eq_fold (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    productState w d claim maps = (List.range 2).foldl (retainedProductOuter w d claim maps)
      (Array.replicate 47 (lane 0),#[]) := by
  simp only [productState,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  rfl

/-- A single production row appends exactly its retained polynomial. -/
theorem retainedProductStep_list (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (state : Array W × Array PackedE) (m b : Nat) :
    (retainedProductStep w d claim maps m state b).2.toList =
      state.2.toList++[productRow w d claim maps m b] :=
  Array.toList_push ..

/-- A complete segment block appends exactly its retained polynomials. -/
theorem retainedProductOuter_list (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (state : Array W × Array PackedE) (m : Nat) :
    (retainedProductOuter w d claim maps state m).2.toList =
      state.2.toList++(List.range (2^(w.nLog-4))).map (productRow w d claim maps m) := by
  have h := foldl_list_append (fun state : Array W × Array PackedE => state.2.toList)
    (retainedProductStep w d claim maps m) (fun b => [productRow w d claim maps m b])
    (fun st b => retainedProductStep_list w d claim maps st m b) (List.range (2^(w.nLog-4))) state
  rw [← List.map_eq_flatMap] at h
  exact h

/-- An arbitrary list of native segment blocks appends its exact segment-major row sequence. -/
theorem retainedProductRows_list (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (segments : List Nat) (state : Array W × Array PackedE) :
    (segments.foldl (retainedProductOuter w d claim maps) state).2.toList =
      state.2.toList++segments.flatMap
        (fun m => (List.range (2^(w.nLog-4))).map (productRow w d claim maps m)) :=
  foldl_list_append (fun state : Array W × Array PackedE => state.2.toList)
    (retainedProductOuter w d claim maps)
    (fun m => (List.range (2^(w.nLog-4))).map (productRow w d claim maps m))
    (fun st m => retainedProductOuter_list w d claim maps st m) segments state

/-- The retained production array is the second component of the structural product state. -/
theorem product_packs_eq_state (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    (product w d claim maps).packs = (productState w d claim maps).2 :=
  congrArg ProductData.packs (product_eq_state w d claim maps)

/-- The structural native product state retains all segment-pack rows in order. -/
theorem productState_packs_list (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    (productState w d claim maps).2.toList =
      (List.range 2).flatMap (fun m => (List.range (2^(w.nLog-4))).map (productRow w d claim maps m)) := by
  exact list_view_of_fold_eq (fun st : Array W × Array PackedE => st.2.toList)
    (retainedProductOuter w d claim maps)
    (fun m => (List.range (2^(w.nLog-4))).map (productRow w d claim maps m))
    (List.range 2) (productState w d claim maps) (Array.replicate 47 (lane 0),#[])
    (productState_eq_fold w d claim maps)
    (retainedProductRows_list w d claim maps (List.range 2) (Array.replicate 47 (lane 0),#[])) rfl

/-- The native product loop retains every segment-pack polynomial in segment-major order. -/
theorem product_packs_toList (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    (product w d claim maps).packs.toList =
      (List.range 2).flatMap (fun m => (List.range (2^(w.nLog-4))).map (productRow w d claim maps m)) := by
  rw [product_packs_eq_state,productState_packs_list]

/-- The retained native polynomial array contains both complete segment blocks. -/
theorem product_packs_size (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    (product w d claim maps).packs.size = 2*2^(w.nLog-4) := by
  rw [← Array.length_toList,product_packs_toList]
  have htwo : List.range 2 = [0,1] := rfl
  rw [htwo]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,
    List.length_map,List.length_range]
  omega

/-- Each retained native array entry is its exact segment-pack row. -/
theorem product_packs_get (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (m : Fin 2) (b : Nat) (hb : b < 2^(w.nLog-4)) :
    (product w d claim maps).packs[m.val*2^(w.nLog-4)+b]! = productRow w d claim maps m.val b := by
  rw [← Array.getElem!_toList,product_packs_toList]
  have htwo : List.range 2 = [0,1] := rfl
  rw [htwo]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [getElem!_pos _ _ (by simp only [List.length_append,List.length_map,List.length_range]; have := m.isLt; nlinarith)]
  fin_cases m
  · simp only [Nat.zero_mul,Nat.zero_add]
    rw [List.getElem_append_left (by simpa only [List.length_map,List.length_range] using hb)]
    simp only [List.getElem_map,List.getElem_range]
  · simp only [Nat.one_mul]
    rw [List.getElem_append_right (by simp only [List.length_map,List.length_range]; omega)]
    simp only [List.length_map,List.length_range,Nat.add_sub_cancel_left,List.getElem_map,List.getElem_range]

end CompStark.Keccak.GkrProver
