/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PayloadProofs

/-! Coefficient semantics of the retained native product-polynomial accumulation. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- Add one weighted retained polynomial to the 47 transmitted coefficients. -/
def addProductCoefficients (result : Array W) (weight : W) (coeffs : PackedE) : Array W := Id.run do
  let mut result := result
  for k in [:47] do
    result := result.set! k (WordExt3.add result[k]! (WordExt3.mul weight (coeffs.get k)))
  return result

/-- A complete coefficient addition preserves the message length. -/
theorem addProductCoefficients_size (result : Array W) (weight : W) (coeffs : PackedE) :
    (addProductCoefficients result weight coeffs).size = result.size := by
  simp only [addProductCoefficients,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure]
  simp only [Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  generalize List.range' 0 47 = xs
  induction xs generalizing result with
  | nil => rfl
  | cons k xs ih => rw [List.foldl_cons,ih,Array.size_set!]

/-- Every coefficient of the addition loop is its exact weighted field sum. -/
theorem addProductCoefficients_get (result : Array W) (hr : result.size = 47)
    (weight : W) (coeffs : PackedE) (i : Fin 47) :
    (addProductCoefficients result weight coeffs)[i.val]! = result[i.val]!+weight*coeffs.get i.val := by
  simp only [addProductCoefficients,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure]
  let step (out : Array W) (k : Nat) := out.set! k (out[k]!+weight*coeffs.get k)
  have hf (xs : List Nat) (hxs : xs.Nodup) (out : Array W) (hout : out.size = 47) :
      (xs.foldl step out)[i.val]! =
        if i.val ∈ xs then out[i.val]!+weight*coeffs.get i.val else out[i.val]! := by
    induction xs generalizing out with
    | nil => simp only [List.foldl_nil,List.not_mem_nil,ite_false]
    | cons k xs ih =>
      obtain ⟨hk,hnd⟩ := List.nodup_cons.mp hxs
      rw [List.foldl_cons,ih hnd _ (by rw [Array.size_set!,hout])]
      by_cases ht : i.val ∈ xs
      · have hne : k ≠ i.val := by intro h; subst k; exact hk ht
        rw [ite_eq_left ht,ite_eq_left (List.mem_cons_of_mem k ht),
          show step out k = out.set! k (out[k]!+weight*coeffs.get k) from rfl,
          Array.getElem!_set!_ne _ _ _ _ hne]
      · rw [ite_eq_right ht]
        by_cases he : k = i.val
        · subst k
          rw [ite_eq_left List.mem_cons_self]
          exact Array.getElem!_set!_self _ _ _ (by have := i.isLt; omega)
        · rw [ite_eq_right (by simp only [List.mem_cons,ht,or_false]; exact Ne.symm he)]
          exact Array.getElem!_set!_ne _ _ _ _ he
  change ((List.range' 0 47).foldl step result)[i.val]! = _
  rw [hf _ (List.nodup_range' 1 (by omega)) result hr,
    ite_eq_left (List.mem_range'.mpr ⟨i.val,i.isLt,by omega⟩)]

/-- A fold whose state adds one term per row has the exact accumulated coefficient sum. -/
theorem foldl_coefficient_sum {A S : Type} (view : S → Array W) (step : S → A → S)
    (term : A → W) (i : Fin 47)
    (hsize : ∀ state a, (view state).size = 47 → (view (step state a)).size = 47)
    (hget : ∀ state a, (view state).size = 47 →
      (view (step state a))[i.val]! = (view state)[i.val]!+term a)
    (xs : List A) (state : S) (hs : (view state).size = 47) :
    (view (xs.foldl step state)).size = 47 ∧
      (view (xs.foldl step state))[i.val]! = (view state)[i.val]!+(xs.map term).sum := by
  induction xs generalizing state with
  | nil => exact ⟨hs,(add_zero _).symm⟩
  | cons a xs ih =>
    rw [List.foldl_cons]
    obtain ⟨hlen,hval⟩ := ih (step state a) (hsize state a hs)
    refine ⟨hlen,?_⟩
    rw [hval,hget state a hs,List.map_cons,List.sum_cons,add_assoc]

/-- Summing a natural range list agrees with its finite-set field sum. -/
theorem list_range_sum (term : Nat → W) (n : Nat) :
    ((List.range n).map term).sum = ∑ k ∈ Finset.range n, term k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,
      List.sum_singleton,ih,Finset.sum_range_succ]

/-- One segment-pack polynomial retained by the production product loop. -/
def productRow (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (segment pack : Nat) : PackedE :=
  weightedPayload
    (productPayload w.layers[12*(segment+1)-d]! (2^w.nLog/64).toUSize (pack/4).toUSize
      (16*(pack%4)).toUInt64 maps 0 (zeroWords 1600)) (weightDigits claim.weights)

/-- Coefficients of a retained native row are the exact weighted binary-payload coefficients. -/
theorem productRow_get (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (segment pack : Nat) (i : Fin 47) :
    (productRow w d claim maps segment pack).get i.val =
      ∑ j : Fin 1600,
        if (productCell w.layers[12*(segment+1)-d]! (2^w.nLog/64).toUSize (pack/4).toUSize
          (16*(pack%4)).toUInt64 maps j.val).toNat.testBit i.val
        then claim.weights[j.val]! else 0 := by
  rw [productRow,weightedPayload_get]
  apply Finset.sum_congr rfl
  intro j _
  rw [productPayload_get _ _ _ _ _ _ _ _ j.isLt,ite_eq_left (Nat.zero_le _)]

/-- The retained and accumulated coefficient state after all segment-pack rows. -/
def productState (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    Array W × Array PackedE := Id.run do
  let packs := 2^(w.nLog-4)
  let eq := eqTable claim.point
  let mut state : Array W × Array PackedE := (Array.replicate 47 (lane 0),#[])
  for m in [:2] do
    for b in [:packs] do
      let coeffs := productRow w d claim maps m b
      state := (addProductCoefficients state.1 eq[m*packs+b]! coeffs,state.2.push coeffs)
  return state

/-- The production product loop is the same retained coefficient fold. -/
theorem product_eq_state (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) :
    product w d claim maps = ⟨(productState w d claim maps).1,(productState w d claim maps).2⟩ := by
  rfl

/-- Every transmitted product coefficient is the equality-weighted sum of all retained rows. -/
theorem product_message_get (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (i : Fin 47) :
    (product w d claim maps).message[i.val]! =
      ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)),
        (eqTable claim.point)[m*2^(w.nLog-4)+b]!*(productRow w d claim maps m b).get i.val := by
  let packs := 2^(w.nLog-4)
  let eq := eqTable claim.point
  let term (m b : Nat) := eq[m*packs+b]!*(productRow w d claim maps m b).get i.val
  let step (m : Nat) (state : Array W × Array PackedE) (b : Nat) :=
    (addProductCoefficients state.1 eq[m*packs+b]! (productRow w d claim maps m b),
      state.2.push (productRow w d claim maps m b))
  let outer (state : Array W × Array PackedE) (m : Nat) := (List.range packs).foldl (step m) state
  have hinner (m : Nat) (state : Array W × Array PackedE) (hs : state.1.size = 47) :
      (outer state m).1.size = 47 ∧ (outer state m).1[i.val]! =
        state.1[i.val]!+∑ b ∈ Finset.range packs,term m b := by
    have h := foldl_coefficient_sum Prod.fst (step m) (term m) i
      (by intro st b hst; exact (addProductCoefficients_size _ _ _).trans hst)
      (by intro st b hst; exact addProductCoefficients_get st.1 hst _ _ i)
      (List.range packs) state hs
    rw [list_range_sum] at h
    exact h
  have houter := foldl_coefficient_sum Prod.fst outer
    (fun m => ∑ b ∈ Finset.range packs,term m b) i
    (by intro st m hst; exact (hinner m st hst).1)
    (by intro st m hst; exact (hinner m st hst).2)
    (List.range 2) (Array.replicate 47 (lane 0),#[]) (Array.size_replicate ..)
  rw [product_eq_state]
  simp only [productState,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,
    Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  change ((List.range 2).foldl outer (Array.replicate 47 (lane 0),#[])).1[i.val]! = _
  rw [houter.2,list_range_sum]
  have hz : (Array.replicate 47 (lane 0))[i.val]! = 0 := by
    rw [getElem!_pos _ _ (by simpa only [Array.size_replicate] using i.isLt),Array.getElem_replicate]
    rfl
  rw [hz,zero_add]

/-- Native product messages are the complete weighted sums of their certified binary payload bits. -/
theorem product_message_payload (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts)
    (i : Fin 47) :
    (product w d claim maps).message[i.val]! =
      ∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)),
        (eqTable claim.point)[m*2^(w.nLog-4)+b]! *
          ∑ j : Fin 1600,
            if (productCell w.layers[12*(m+1)-d]! (2^w.nLog/64).toUSize (b/4).toUSize
              (16*(b%4)).toUInt64 maps j.val).toNat.testBit i.val
            then claim.weights[j.val]! else 0 := by
  rw [product_message_get]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro b _
  rw [productRow_get]

/-- Interpret a native binary payload word as a polynomial over the word extension field. -/
noncomputable def payloadWordPolynomial (p : UInt64) : Polynomial W :=
  (BinaryField.toPoly p.toBitVec).map (ZMod.castHom (dvd_refl 2) W)

/-- A binary payload coefficient is its corresponding zero-or-one extension-field bit. -/
theorem payloadWordPolynomial_coeff (p : UInt64) (i : Fin 47) :
    (payloadWordPolynomial p).coeff i.val = if p.toNat.testBit i.val then 1 else 0 := by
  rw [payloadWordPolynomial,Polynomial.coeff_map,BinaryField.toPoly_coeff]
  have hi : i.val < 64 := by have := i.isLt; omega
  rw [dite_eq_left hi]
  change (ZMod.castHom (dvd_refl 2) W)
    (if p.toNat.testBit i.val then (1 : ZMod 2) else 0) = _
  split <;> simp only [map_one,map_zero]

/-- Every native product coefficient is the coefficient of its complete weighted payload polynomial. -/
theorem product_message_polynomial (w : SlicedWitness) (d : Nat) (claim : Claim)
    (maps : RmfeProducts) (i : Fin 47) :
    (product w d claim maps).message[i.val]! =
      (∑ m ∈ Finset.range 2, ∑ b ∈ Finset.range (2^(w.nLog-4)), ∑ j : Fin 1600,
        ((eqTable claim.point)[m*2^(w.nLog-4)+b]!*claim.weights[j.val]!) •
          payloadWordPolynomial (productCell w.layers[12*(m+1)-d]!
            (2^w.nLog/64).toUSize (b/4).toUSize (16*(b%4)).toUInt64 maps j.val)).coeff i.val := by
  rw [product_message_payload]
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_smul,smul_eq_mul,
    payloadWordPolynomial_coeff,Finset.mul_sum,mul_ite,mul_one,mul_zero]

/-- A native prepared chi payload is the certified affine RMFE polynomial over the prover field. -/
theorem productCell_payloadWordPolynomial (state : Array UInt64) (groups offset : USize)
    (bits : UInt64) (j : Nat) :
    payloadWordPolynomial (productCell state groups offset bits prepareRmfeProducts j) =
      let k := j.toUSize
      let a := (state[(k*groups+offset).toNat]! >>> bits) &&& 65535
      let b := (state[(shiftU k 1*groups+offset).toNat]! >>> bits) &&& 65535
      let c := (state[(shiftU k 2*groups+offset).toNat]! >>> bits) &&& 65535
      payloadWordPolynomial (embeddingRaw 65535) * payloadWordPolynomial (embeddingRaw a) +
        (payloadWordPolynomial (embeddingRaw 65535) + payloadWordPolynomial (embeddingRaw b)) *
          payloadWordPolynomial (embeddingRaw c) := by
  simp only [payloadWordPolynomial,productCell_poly,Polynomial.map_add,Polynomial.map_mul]

end CompStark.Keccak.GkrProver
