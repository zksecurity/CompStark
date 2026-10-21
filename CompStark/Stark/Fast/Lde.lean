/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Rel
public import CompStark.Stark.Points
public import CompPoly.Univariate.NTTFast.Packed.CosetLdeCorrectness
public import CompPoly.Univariate.NTT.Interpolation
import all CompPoly.Univariate.Basic

/-! # The fast low-degree extension is the specification's

CompPoly's batched coset LDE computes `ldeSpec`: every column's interpolant on the subgroup of
order `2 ^ logH`, at the coset points in bit-reversed order. `ldeRef` computes the same values:
its inverse transform gives the interpolant's coefficients and Horner's rule evaluates them.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial
open CompPoly.CPolynomial.NTTFast.Packed (LdePlan ldeSpec column powDomain)

local notation "F" => _root_.KoalaBear.Fast.Field

/-- A plan `plan?` returns extends onto `shift · ⟨ω_N⟩`, `ω_N = twoAdicGen (logH + bits)`. -/
theorem plan?_some {logH bits : Nat} {shift : F} {P : LdePlan}
    (h : plan? logH bits shift = some P) :
    logH + bits ≤ 24 ∧ P.domain.logN = logH + bits ∧ P.bits = bits ∧ P.shift = shift ∧
      P.domain.omega = twoAdicGen (logH + bits) := by
  unfold plan? at h
  split at h
  · rename_i h24
    cases Option.some.inj h
    exact ⟨h24, rfl, rfl, rfl, (KoalaBear.twoAdicGen_eq_table ⟨logH + bits, by omega⟩).symm⟩
  · cases h

/-- Polynomial evaluation of the inverse transform is the interpolant's. -/
theorem eval_interpolatePow (D : NTT.Domain F) (col : Vector F D.n) (y : F) :
    (CLagrange.interpolatePow D.omega col).eval y =
      (NTT.Inverse.inverseSpec D col.toArray).foldr (fun a acc ↦ acc * y + a) 0 := by
  conv_lhs => rw [← NTT.loadNaturalVector_toArray D col]
  change Raw.eval y (CLagrange.interpolatePow D.omega _).val = _
  rw [← NTT.Inverse.inverseSpec_interpolatePow_eq, Raw.eval_trim_eq_eval, Raw.eval,
    ← Raw.eval₂Horner_eq_eval₂]
  rfl

/-- A left fold of additions is a sum. -/
theorem foldl_range_add (f : Nat → F) (n : Nat) (a : F) :
    (List.range n).foldl (fun acc i ↦ acc + f i) a = a + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, add_assoc]

/-- Entry `i` of a column. -/
theorem getD_column (m : Array F) (w h j i : Nat) (hi : i < h) :
    (column m w h j).toArray.getD i 0 = m.getD (i * w + j) 0 := by
  simp only [column, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  rw [dite_eq_left_of_eq_true (eq_true hi), Option.getD_some]

/-- The coefficients `ldeRef` computes are the inverse transform of the column. -/
theorem inverseSpec_column (P : LdePlan) (logH bits w j : Nat) (m : Array F)
    (hlog : P.domain.logN = logH + bits) (hb : P.bits = bits)
    (hω : P.domain.omega = twoAdicGen (logH + bits)) (h24 : logH + bits ≤ 24) :
    NTT.Inverse.inverseSpec (powDomain P.domain P.bits P.bits_le)
        (column m w (2 ^ P.logH) j).toArray =
      Array.ofFn (n := 2 ^ logH) fun k ↦ ((2 ^ logH : Nat) : F)⁻¹ *
        (List.range (2 ^ logH)).foldl (fun acc i ↦
          acc + m.getD (i * w + j) 0 * powF (twoAdicGen logH)⁻¹ (i * k.val % 2 ^ logH)) 0 := by
  have hlogH : P.logH = logH := by
    change P.domain.logN - P.bits = logH
    omega
  have hn : (powDomain P.domain P.bits P.bits_le).n = 2 ^ logH := by
    change 2 ^ P.logH = 2 ^ logH
    rw [hlogH]
  have hDω : (powDomain P.domain P.bits P.bits_le).omega = twoAdicGen logH := by
    change P.domain.omega ^ 2 ^ P.bits = _
    rw [hω, hb, BaseField.twoAdicGen_pow _ _ h24]
  have h1 : (twoAdicGen logH : F)⁻¹ ^ 2 ^ logH = 1 := by
    rw [inv_pow, ← hDω, ← hn, inv_eq_one]
    exact (powDomain P.domain P.bits P.bits_le).primitive.pow_eq_one
  have hmod (a : Nat) :
      (twoAdicGen logH : F)⁻¹ ^ (a % 2 ^ logH) = (twoAdicGen logH)⁻¹ ^ a := by
    conv_rhs => rw [← Nat.mod_add_div a (2 ^ logH), pow_add, pow_mul, h1, one_pow, mul_one]
  apply Array.ext
  · rw [NTT.Inverse.size_inverseSpec, Array.size_ofFn, hn]
  · intro k hk1 hk2
    simp only [NTT.Inverse.inverseSpec, Array.getElem_ofFn, NTT.Inverse.inttAt,
      NTT.Domain.nInv, NTT.Domain.omegaInv]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ (column m w (2 ^ P.logH) j).toArray.getD i 0 *
      (powDomain P.domain P.bits P.bits_le).omega⁻¹ ^ (k * i)), hn, hDω, foldl_range_add,
      zero_add]
    refine congrArg (_ * ·) (Finset.sum_congr rfl fun i hi ↦ ?_)
    have hi := Finset.mem_range.mp hi
    rw [getD_column _ _ _ _ _ (by rw [hlogH]; exact hi), powF_eq, hmod, Nat.mul_comm i k]

/-- Rows of width `w` flatten in row-major order. -/
theorem flatten_ofFn {α : Type} (N w : Nat) (g : Fin N → Array α) (G : Nat → Nat → α)
    (hg : ∀ r : Fin N, g r = (Array.range w).map (G r.val)) :
    (Array.ofFn g).flatten = Array.ofFn (n := N * w) fun k ↦ G (k / w) (k % w) := by
  have h : Array.ofFn g = (Array.range N).map fun r ↦ (Array.range w).map (G r) := by
    apply Array.ext
    · rw [Array.size_ofFn, Array.size_map, Array.size_range]
    · intro r h1 h2
      rw [Array.getElem_ofFn, Array.getElem_map, Array.getElem_range, hg]
  rw [h, ← Array.flatMap_def, NTTFast.Packed.flatMap_range_map]
  apply Array.ext
  · rw [Array.size_ofFn, Array.size_map, Array.size_range]
  · intro k h1 h2
    rw [Array.getElem_ofFn, Array.getElem_map, Array.getElem_range]

/-- **The coset LDE's specification is `ldeRef`** on the plan's coset. -/
theorem ldeSpec_eq (P : LdePlan) (logH bits : Nat) (shift : F) (w : Nat) (m : Array F)
    (hlog : P.domain.logN = logH + bits) (hb : P.bits = bits) (hs : P.shift = shift)
    (hω : P.domain.omega = twoAdicGen (logH + bits)) (h24 : logH + bits ≤ 24) :
    ldeSpec P w m = (ldeRef logH bits shift w m).values := by
  simp only [ldeRef, Mat.ofValues]
  rw [flatten_ofFn _ w _ fun r j ↦ (Array.ofFn (n := 2 ^ logH) fun k ↦
      ((2 ^ logH : Nat) : F)⁻¹ * (List.range (2 ^ logH)).foldl (fun acc i ↦
        acc + m.getD (i * w + j) 0 * powF (twoAdicGen logH)⁻¹ (i * k.val % 2 ^ logH)) 0).foldr
      (fun a acc ↦ acc * (shift * powF (twoAdicGen (logH + bits))
        (reverseBits r (logH + bits))) + a) 0]
  · apply Array.ext
    · simp only [ldeSpec, Array.size_ofFn, hlog]
    · intro k h1 h2
      simp only [ldeSpec, Array.getElem_ofFn]
      refine (eval_interpolatePow (powDomain P.domain P.bits P.bits_le) _ _).trans ?_
      rw [inverseSpec_column P logH bits w _ m hlog hb hω h24, hs, hω, hlog, powF_eq,
        reverseBits_eq]
  · intro r
    apply Array.ext
    · simp only [Array.size_map, List.size_toArray, List.length_map, List.length_range,
        Array.size_range]
    · intro j h1 h2
      simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map, List.getElem_range,
        Array.getElem_range]

/-- The plan `ldeWith` uses is `plan?`'s. -/
theorem ldeWith_plan (plans : List (Nat × Nat × F × LdePlan))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2)
    (logH bits : Nat) (shift : F) (P : LdePlan)
    (h : ((plans.find? fun (h, b, s, _) ↦ h == logH && b == bits && s == shift).map (·.2.2.2)
      <|> plan? logH bits shift) = some P) :
    plan? logH bits shift = some P := by
  cases hf : plans.find? fun (h, b, s, _) ↦ h == logH && b == bits && s == shift with
  | none =>
    rw [hf] at h
    exact h
  | some e =>
    rw [hf] at h
    cases Option.some.inj h
    have hm := List.find?_some hf
    have he := hplans e (List.mem_of_find?_eq_some hf)
    obtain ⟨h0, b0, s0, P0⟩ := e
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    exact he

/-- **The fast low-degree extension is `ldeRef`**, with plans `plan?` built, on a matrix of
`2 ^ logH` rows within the two-adic subgroups whose extension is addressable. -/
theorem ldeWith_rel (plans : List (Nat × Nat × F × LdePlan))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2)
    (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) (hm : m.size = 2 ^ logH * w)
    (hb : logH + bits ≤ 24) (ha : Addressable (2 ^ (logH + bits) * w)) :
    RM (ldeWith plans logH bits shift w m) (ldeRef logH bits shift w m) := by
  unfold ldeWith
  dsimp only
  split
  · rename_i P hfound
    obtain ⟨h24, hlog, hbits, hs, hω⟩ :=
      plan?_some (ldeWith_plan plans hplans logH bits shift P hfound)
    have hM : m.size = 2 ^ P.logH * w := by
      have hlogH : P.logH = logH := by
        change P.domain.logN - P.bits = logH
        omega
      rw [hlogH]
      exact hm
    have hu : 4 * (2 ^ P.domain.logN * w) < USize.size := by
      rw [hlog]
      unfold Addressable at ha
      omega
    refine ⟨rfl, rfl, ?_⟩
    change NTTFast.Packed.Native.joinRows (NTTFast.Packed.Native.cosetLde P w
      (NTTFast.Packed.Native.encodeFields m)) = encode (ldeRef logH bits shift w m).values
    rw [NTTFast.Packed.Native.encodeFields_eq,
      NTTFast.Packed.Native.joinRows_cosetLde P w m hM hu,
      ldeSpec_eq P logH bits shift w m hlog hbits hs hω h24]
  · rename_i hnone
    have hp : plan? logH bits shift ≠ none := by
      rw [plan?, dite_eq_left_of_eq_true (eq_true hb)]
      exact Option.some_ne_none _
    cases hf : (plans.find? fun (h, b, s, _) ↦ h == logH && b == bits && s == shift).map
      (·.2.2.2) with
    | none => rw [hf] at hnone; exact absurd hnone hp
    | some _ => rw [hf] at hnone; exact absurd hnone (Option.some_ne_none _)

/-- Every plan `ldePlans` prepares is `plan?`'s. -/
theorem ldePlans_valid (logN logBlowup logChunks : Nat) :
    ∀ e ∈ ldePlans logN logBlowup logChunks, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2 := by
  intro e he
  simp only [ldePlans, List.mem_filterMap, Option.map_eq_some_iff] at he
  obtain ⟨s, -, P, hP, rfl⟩ := he
  exact hP

end CompStark.Stark.Fast
