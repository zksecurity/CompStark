/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Columns
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
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

/-- Polynomial evaluation of the inverse transform is the interpolant's. -/
theorem eval_interpolatePow (D : NTT.Domain F) (col : Vector F D.n) (y : F) :
    (CLagrange.interpolatePow D.omega col).eval y =
      (NTT.Inverse.inverseSpec D col.toArray).foldr (fun a acc ↦ acc * y + a) 0 := by
  conv_lhs => rw [← NTT.loadNaturalVector_toArray D col]
  change Raw.eval y (CLagrange.interpolatePow D.omega _).val = _
  rw [← NTT.Inverse.inverseSpec_interpolatePow_eq, Raw.eval_trim_eq_eval, Raw.eval,
    ← Raw.eval₂Horner_eq_eval₂]
  rfl

/-- Entry `i` of a column. -/
theorem getD_column (m : Array F) (w h j i : Nat) (hi : i < h) :
    (column m w h j).toArray.getD i 0 = m.getD (i * w + j) 0 := by
  simp only [column, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  rw [dite_eq_left_of_eq_true (eq_true hi), Option.getD_some]

/-- Joined, the chunks of rows of a matrix are its words. -/
theorem joinRows_rowChunks (m : Array F) (w logH k : Nat) (hk : k ≤ logH)
    (hm : m.size = 2 ^ logH * w) :
    NTTFast.Packed.Native.joinRows (NTTFast.Packed.Native.rowChunks m w logH k) = encode m :=
  NTTFast.Packed.joinRows_extract m (2 ^ k) (2 ^ (logH - k) * w) (by
    rw [hm, ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hk])

/-- A matrix of `2 ^ logH` rows in one chunk. -/
theorem rowChunks_zero (m : Array F) (w logH : Nat) (hm : m.size = 2 ^ logH * w) :
    NTTFast.Packed.Native.rowChunks m w logH 0 = #[encode m] := by
  simp only [NTTFast.Packed.Native.rowChunks, Nat.pow_zero, Nat.sub_zero]
  rw [show Array.range 1 = #[0] by rw [Array.range_eq_range', Array.range'_one],
    Array.map_singleton, Nat.zero_mul, Nat.zero_add, ← hm, Array.extract_size]

open NTTFast.Packed (cosetTable getD_block getD_map_range rangesPerChunk_spec flatMap_range_map)
open NTTFast.Packed.Native (rowChunks transposeRows gatherColumn columnCoefficients cosetBlock)
  in
/-- **The column-wise extension is `ldeSpec`**, in blocks of the input's height: column `j` of
block `t` holds rows `t · 2 ^ logH, …` of column `j`. -/
theorem ldeColumns_eq (P : LdePlan p) (w : Nat) (M : Array F) (k : Nat) (hk : k ≤ P.logH)
    (hM : M.size = 2 ^ P.logH * w) (hu : 4 * (2 ^ P.domain.logN * w) < USize.size) :
    ldeColumns P w (rowChunks M w P.logH k) = (Array.range (2 ^ P.bits * w)).map fun i ↦
      encode (Array.ofFn (n := 2 ^ P.logH) fun kk ↦
        (ldeSpec P w M).getD ((i / w * 2 ^ P.logH + kk.val) * w + i % w) 0) := by
  have hlog : P.domain.logN = P.bits + P.logH := by
    have := P.bits_le; simp only [LdePlan.logH]; omega
  have hHN : 2 ^ P.logH * w ≤ 2 ^ P.domain.logN * w :=
    Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  have hMs : 4 * M.size < USize.size := by omega
  obtain ⟨hq0, hR, hq⟩ := rangesPerChunk_spec P.logH k hk
  set q := NTTFast.Packed.Native.rangesPerChunk P.logH (2 ^ k) with hqd
  set R := 2 ^ k * q with hRd
  set rows := 2 ^ P.logH / R with hrows
  have hpieces : (Array.range R).map (fun j ↦ transposeRows
      ((rowChunks M w P.logH k).getD (j / q) .empty) w (j % q * rows) rows) =
      (Array.range R).map fun j ↦ transposeRows (encode M) w (j * rows) rows := by
    apply Array.ext (by simp only [Array.size_map])
    intro j h1 _
    simp only [Array.size_map, Array.size_range] at h1
    simp only [Array.getElem_map, Array.getElem_range]
    exact NTTFast.Packed.Native.transposeRows_rowChunks M w P.logH k q rows hM hk hq0 hq hMs j h1
  -- Block `t` of column `j`, as field coordinates.
  let B (t j : Nat) : Array F := NTTFast.Packed.difSpec P.low (Array.ofFn (n := 2 ^ P.logH)
    fun l ↦ (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).getD l.val 0 *
      (NTT.Forward.forwardSpec P.low.inverse (column M w (2 ^ P.logH) j).toArray).getD l.val 0)
  have hcol (j : Nat) (hj : j < w) (t : Nat) : cosetBlock P (columnCoefficients P (gatherColumn
      ((Array.range R).map fun k ↦ transposeRows (encode M) w (k * rows) rows) rows j)) t =
      encode (B t j) := by
    rw [NTTFast.Packed.Native.gatherColumn_eq_column M w _ R rows j hj hR hM hMs,
      NTTFast.Packed.Native.columnCoefficients_encode P _ (by simp only [Vector.size_toArray]),
      NTTFast.Packed.Native.cosetBlock_encode P _ (by
        rw [NTT.Forward.forwardSpec, Array.size_ofFn]; rfl)]
  unfold ldeColumns
  simp only [Array.map_map, Function.comp_def, CompPoly.Tasks.get_bind,
    CompPoly.Tasks.get_spawn, CompPoly.Tasks.get_join, CompPoly.Tasks.map_get_spawnAll,
    rowChunks, Array.size_map, Array.size_range]
  rw [← rowChunks, hpieces, flatMap_range_map]
  apply Array.ext (by simp only [Array.size_map])
  intro c h1 _
  simp only [Array.size_map, Array.size_range] at h1
  simp only [Array.getElem_map, Array.getElem_range]
  have hw0 : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
  have hcw0 : c % w < w := Nat.mod_lt _ hw0
  have h1' : c < 2 ^ P.bits * w := h1
  have hct0 : c / w < 2 ^ P.bits := (Nat.div_lt_iff_lt_mul hw0).mpr h1'
  rw [getD_map_range _ _ _ hct0, hcol _ hcw0]
  congr 1
  apply Array.ext (by simp only [B, NTTFast.Packed.size_difSpec, Array.size_ofFn]; rfl)
  intro kk k1 k2
  simp only [Array.size_ofFn] at k2
  rw [Array.getElem_ofFn, Array.getElem_eq_getD 0]
  simp only [B]
  rw [getD_block P _ _ _ k2]
  have hcw : c % w < w := hcw0
  have hct : c / w < 2 ^ P.bits := hct0
  have hidx : (c / w * 2 ^ P.logH + kk) * w + c % w < 2 ^ P.domain.logN * w := by
    have h2 : c / w * 2 ^ P.logH + kk < 2 ^ P.domain.logN := by
      rw [hlog, Nat.pow_add]
      have := Nat.mul_le_mul_right (2 ^ P.logH) (show c / w + 1 ≤ 2 ^ P.bits by omega)
      rw [Nat.succ_mul] at this; omega
    have := Nat.mul_le_mul_right w (show c / w * 2 ^ P.logH + kk + 1 ≤ 2 ^ P.domain.logN by omega)
    rw [Nat.succ_mul] at this; omega
  rw [ldeSpec, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left_of_eq_true (eq_true
    hidx), Option.getD_some]
  have e1 : ((c / w * 2 ^ P.logH + kk) * w + c % w) % w = c % w := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcw]
  have e2 : ((c / w * 2 ^ P.logH + kk) * w + c % w) / w = 2 ^ P.logH * (c / w) + kk := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hcw, Nat.zero_add,
      Nat.mul_comm]
  simp only [e1, e2]

variable [Mont32BaseField p]

/-- A plan `plan?` returns extends onto `shift · ⟨ω_N⟩`, `ω_N = twoAdicGen (logH + bits)`. -/
theorem plan?_some {logH bits : Nat} {shift : F} {P : LdePlan p}
    (h : plan? logH bits shift = some P) :
    logH + bits ≤ twoAdicity F ∧ P.domain.logN = logH + bits ∧ P.bits = bits ∧ P.shift = shift ∧
      P.domain.omega = twoAdicGen (logH + bits) := by
  unfold plan? at h
  split at h
  · rename_i h24
    cases Option.some.inj h
    exact ⟨h24, rfl, rfl, rfl, rfl⟩
  · cases h

section
variable {K : Type} [BaseField K]

/-- A left fold of additions is a sum. -/
theorem foldl_range_add (f : Nat → K) (n : Nat) (a : K) :
    (List.range n).foldl (fun acc i ↦ acc + f i) a = a + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, add_assoc]

/-- The inverse transform on the two-adic subgroup of order `2 ^ logH`, as sums. -/
theorem inverseSpec_twoAdic (D : NTT.Domain K) (logH : Nat) (hn : D.n = 2 ^ logH)
    (hω : D.omega = twoAdicGen logH) (col : Array K) :
    NTT.Inverse.inverseSpec D col =
      Array.ofFn (n := 2 ^ logH) fun k ↦ ((2 ^ logH : Nat) : K)⁻¹ *
        (List.range (2 ^ logH)).foldl (fun acc i ↦
          acc + col.getD i 0 * powF (twoAdicGen logH)⁻¹ (i * k.val % 2 ^ logH)) 0 := by
  have h1 : (twoAdicGen logH : K)⁻¹ ^ 2 ^ logH = 1 := by
    rw [inv_pow, ← hω, ← hn, inv_eq_one]
    exact D.primitive.pow_eq_one
  have hmod (a : Nat) :
      (twoAdicGen logH : K)⁻¹ ^ (a % 2 ^ logH) = (twoAdicGen logH)⁻¹ ^ a := by
    conv_rhs => rw [← Nat.mod_add_div a (2 ^ logH), pow_add, pow_mul, h1, one_pow, mul_one]
  apply Array.ext
  · rw [NTT.Inverse.size_inverseSpec, Array.size_ofFn, hn]
  · intro k hk1 hk2
    simp only [NTT.Inverse.inverseSpec, Array.getElem_ofFn, NTT.Inverse.inttAt,
      NTT.Domain.nInv, NTT.Domain.omegaInv]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ col.getD i 0 * D.omega⁻¹ ^ (k * i)), hn, hω,
      foldl_range_add, zero_add]
    refine congrArg (_ * ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [powF_eq, hmod, Nat.mul_comm i k]

end

/-- The coefficients `ldeRef` computes are the inverse transform of the column. -/
theorem inverseSpec_column (P : LdePlan p) (logH bits w j : Nat) (m : Array F)
    (hlog : P.domain.logN = logH + bits) (hb : P.bits = bits)
    (hω : P.domain.omega = twoAdicGen (logH + bits)) (h24 : logH + bits ≤ twoAdicity F) :
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
  rw [inverseSpec_twoAdic _ logH hn hDω]
  refine congrArg (Array.ofFn (n := 2 ^ logH)) (funext fun k ↦
    congrArg (fun x ↦ ((2 ^ logH : Nat) : F)⁻¹ * x) (List.foldl_ext _ _ _ fun acc i hi ↦ ?_))
  rw [getD_column _ _ _ _ _ (by rw [hlogH]; exact List.mem_range.mp hi)]

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
theorem ldeSpec_eq (P : LdePlan p) (logH bits : Nat) (shift : F) (w : Nat) (m : Array F)
    (hlog : P.domain.logN = logH + bits) (hb : P.bits = bits) (hs : P.shift = shift)
    (hω : P.domain.omega = twoAdicGen (logH + bits)) (h24 : logH + bits ≤ twoAdicity F) :
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
theorem ldeWith_plan (plans : List (Nat × Nat × F × LdePlan p))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2)
    (logH bits : Nat) (shift : F) (P : LdePlan p)
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

/-- **The fast low-degree extension of packed words is `ldeRef`**, with plans `plan?` built, on a
matrix of `2 ^ logH` rows in `2 ^ k` chunks of rows within the two-adic subgroups whose extension
is addressable. -/
theorem ldeWordsWith_rel (plans : List (Nat × Nat × F × LdePlan p))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2)
    (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) (k : Nat) (hk : k ≤ logH)
    (hm : m.size = 2 ^ logH * w) (hb : logH + bits ≤ twoAdicity F)
    (ha : Addressable (2 ^ (logH + bits) * w)) :
    RM (ldeWordsWith plans logH bits shift w (NTTFast.Packed.Native.rowChunks m w logH k))
      (ldeRef logH bits shift w m) := by
  unfold ldeWordsWith
  dsimp only
  split
  · rename_i P hfound
    obtain ⟨h24, hlog, hbits, hs, hω⟩ :=
      plan?_some (ldeWith_plan plans hplans logH bits shift P hfound)
    have hlogH : P.logH = logH := by
      change P.domain.logN - P.bits = logH
      omega
    have hM : m.size = 2 ^ P.logH * w := by rw [hlogH]; exact hm
    have hu : 4 * (2 ^ P.domain.logN * w) < USize.size := by
      rw [hlog]
      unfold Addressable at ha
      omega
    have hv := ldeSpec_eq P logH bits shift w m hlog hbits hs hω h24
    have hsz : (ldeRef logH bits shift w m).values.size = w * 2 ^ (logH + bits) := by
      rw [← hv, ldeSpec, Array.size_ofFn, hlog, Nat.mul_comm]
    have hw : (ldeRef logH bits shift w m).width = w := rfl
    have hh : (ldeRef logH bits shift w m).height = 2 ^ (logH + bits) := rfl
    have h29 : logH + bits ≤ 29 := le_trans h24 (Mont32BaseField.twoAdicity_le_29 p)
    refine ⟨rfl, rfl, by rw [hw, hh, hsz], Nat.two_pow_pos _, ?_, ?_, ?_⟩
    · show 4 * 2 ^ logH < USize.size
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show logH ≤ 29 by omega)
      have := USize.le_size
      omega
    · rw [hh, Nat.pow_add, Nat.mul_mod_right]
    · change ldeColumns P w (NTTFast.Packed.Native.rowChunks m w logH k) = _
      have he := ldeColumns_eq P w m k (by omega) hM hu
      rw [hlogH] at he
      rw [he]
      have hsize : 2 ^ P.bits * w = ((colBlocks (ldeRef logH bits shift w m) (2 ^ logH)).map
          encode).size := by
        rw [Array.size_map, size_colBlocks, hh, hw, Nat.pow_add, Nat.mul_comm (2 ^ logH),
          Nat.mul_div_cancel _ (Nat.two_pow_pos logH), hbits]
      apply Array.ext (by rw [Array.size_map, Array.size_range]; exact hsize)
      intro i h1 h2
      simp only [Array.size_map, Array.size_range] at h1
      rw [Array.getElem_map, Array.getElem_range, Array.getElem_map]
      simp only [colBlocks, Array.getElem_ofFn, hw, hv]
  · rename_i hnone
    have hp : plan? logH bits shift ≠ none := by
      rw [plan?, dite_eq_left_of_eq_true (eq_true hb)]
      exact Option.some_ne_none _
    cases hf : (plans.find? fun (h, b, s, _) ↦ h == logH && b == bits && s == shift).map
      (·.2.2.2) with
    | none => rw [hf] at hnone; exact absurd hnone hp
    | some _ => rw [hf] at hnone; exact absurd hnone (Option.some_ne_none _)

/-- `ldeWordsWith_rel` on one chunk. -/
theorem ldeWordsWith_one_rel (plans : List (Nat × Nat × F × LdePlan p))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2)
    (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) (hm : m.size = 2 ^ logH * w)
    (hb : logH + bits ≤ twoAdicity F) (ha : Addressable (2 ^ (logH + bits) * w)) :
    RM (ldeWordsWith plans logH bits shift w #[encode m]) (ldeRef logH bits shift w m) := by
  rw [← rowChunks_zero m w logH hm]
  exact ldeWordsWith_rel plans hplans logH bits shift w m 0 (Nat.zero_le _) hm hb ha

/-- **The fast low-degree extension is `ldeRef`**, with plans `plan?` built, on a matrix of
`2 ^ logH` rows within the two-adic subgroups whose extension is addressable. -/
theorem ldeWith_rel (plans : List (Nat × Nat × F × LdePlan p))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2)
    (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) (hm : m.size = 2 ^ logH * w)
    (hb : logH + bits ≤ twoAdicity F) (ha : Addressable (2 ^ (logH + bits) * w)) :
    RM (ldeWith plans logH bits shift w m) (ldeRef logH bits shift w m) := by
  unfold ldeWith
  rw [NTTFast.Packed.Native.encodeFields_eq]
  exact ldeWordsWith_one_rel plans hplans logH bits shift w m hm hb ha

/-- Every plan `ldePlans` prepares is `plan?`'s. -/
theorem ldePlans_valid (logN logBlowup logChunks : Nat) :
    ∀ e ∈ ldePlans (p := p) logN logBlowup logChunks, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2 := by
  intro e he
  simp only [ldePlans, List.mem_filterMap, Option.map_eq_some_iff] at he
  obtain ⟨s, -, P, hP, rfl⟩ := he
  exact hP

end CompStark.Stark.Fast
