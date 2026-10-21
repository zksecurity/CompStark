/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Lde
public import CompStark.Stark.Fast.Quotient
public import CompStark.Stark.Prover
public import CompStark.Stark.Refines
public import CompStark.Stark.Satisfied
public import CompStark.Stark.Recompose

/-! # The quotient and the out-of-domain check

The honest prover's openings pass the verifier's constraint check at `ζ`.

Over the spec field, let `T_j` be the trace's column polynomials (`ldeRef_isLde`) and `C_c` the
constraint `c` evaluated on them with the selector polynomials `Z_H(X) / (X - 1)`,
`Z_H(X) / (X - ω⁻¹)` and `X - ω⁻¹` (`polyEnv`). `Air.ConstraintsVanish` says `C_c` vanishes on the trace
domain `H = ⟨ω⟩`, so `C_c = Z_H Q_c`, and `Air.DegreeFits` bounds `Q_c` below `k n`, `k` the
number of chunks (`quotientPoly`). The folded quotient `Q = ∑_c α^(K-1-c) Q_c` is a polynomial
of degree below `k n`.

* The prover's quotient values are `Q` on the quotient domain `g · ⟨ω_q⟩`
  (`quotientOfLde_toSpec`): `quotientValues` evaluates the same constraints there, with the same
  selectors, divided by `Z_H`.
* Chunk `c` holds `Q` on the coset `s_c ⟨ω⟩`, `s_c = g ω_qᶜ`; its extension's `d` coordinate
  polynomials combine to `q_c` of degree below `n`, which agrees with `Q` on that coset.
* `recompose` evaluates `∑_c L_c q_c` at `ζ`, `L_c = ∏_{d ≠ c} Z_{D_d} / Z_{D_d}(s_c)`. This
  polynomial has degree below `k n` and agrees with `Q` on the whole quotient domain (`L_c` is
  `1` on `D_c` and `0` on the other cosets), so it is `Q`.
* The verifier folds the constraints at the opened trace values, which are the `T_j` at `ζ` and
  `ζ ω`: it computes `∑_c α^(K-1-c) C_c(ζ) / Z_H(ζ) = Q(ζ)`.

A point outside the base field avoids every root the argument divides by, since the base field
holds all two-adic roots of unity.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri Polynomial Montgomery.Native32

local notation "F" => _root_.KoalaBear.Fast.Field
variable {EF : Type} [Challenge F EF]
local notation "K" => F
local notation "E" => Challenge.Spec EF

/-! ### The example AIRs fit -/

/-- The expression operators are the constructors. -/
theorem Expr.mul_eq (a b : Expr F) : a * b = .mul a b := rfl
theorem Expr.sub_eq (a b : Expr F) : a - b = .sub a b := rfl
theorem Expr.add_eq (a b : Expr F) : a + b = .add a b := rfl

/-- Powers of two are powers of two. -/
theorem isPowerOfTwo_two_pow : ∀ k, (2 ^ k).isPowerOfTwo
  | 0 => Nat.isPowerOfTwo_one
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo (isPowerOfTwo_two_pow k)

/-- Plonky3's chunk count for a largest degree `d + 1`, `d = 2 ^ k`. -/
theorem logQuotientChunks_of (A : Air F) (k : Nat) (h : max A.maxDegree 2 - 1 = 2 ^ k) :
    A.logQuotientChunks = k := by
  rw [Air.logQuotientChunks]
  simp only [h]
  rw [Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k), Nat.log2_two_pow]

/-- The Fibonacci AIR fits its single chunk for every trace length. -/
theorem fibonacci_degreeFits (logN : Nat) : (fibonacci : Air F).DegreeFits logN := by
  have hlc : (fibonacci : Air F).logQuotientChunks = 0 := logQuotientChunks_of _ 0 (by decide)
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [fibonacci, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hlc, Nat.add_zero]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Expr.sub_eq, Expr.add_eq, Expr.degBound] <;> omega

/-- The cube AIR's degree-3 transition fits its two chunks for every trace length. -/
theorem cube_degreeFits (logN : Nat) : (cube : Air F).DegreeFits logN := by
  have hlc : (cube : Air F).logQuotientChunks = 1 := logQuotientChunks_of _ 1 (by decide)
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [cube, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hlc, Nat.pow_succ]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Expr.sub_eq, Expr.add_eq, Expr.degBound] <;> omega

/-- The largest degree of a nonempty list of degree-3 constraints. -/
theorem foldl_max_degree (a : Nat) : ∀ l : List (Expr F), (∀ c ∈ l, c.degree = 3) → l ≠ [] →
    l.foldl (fun m c ↦ max m c.degree) a = max a 3
  | [], _, h => absurd rfl h
  | [c], hl, _ => by rw [List.foldl_cons, List.foldl_nil, hl c List.mem_cons_self]
  | c :: d :: l, hl, _ => by
    rw [List.foldl_cons, foldl_max_degree _ (d :: l) (fun e he ↦ hl e (List.mem_cons_of_mem _ he))
      (List.cons_ne_nil _ _), hl c List.mem_cons_self, Nat.max_assoc, Nat.max_self]

/-- The wide AIR's quotient has two chunks. -/
theorem wide_logQuotientChunks (w : Nat) (hw : 0 < w) : (wide w : Air F).logQuotientChunks = 1 := by
  have hmax : (wide w : Air F).maxDegree = 3 := by
    rw [Air.maxDegree, foldl_max_degree 0 _ (fun e he ↦ ?_)
      (by simp only [wide, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega)]
    · rfl
    · simp only [wide, List.mem_map, List.mem_range] at he
      obtain ⟨i, -, rfl⟩ := he
      rfl
  exact logQuotientChunks_of _ 1 (by rw [hmax]; rfl)

/-- The wide AIR fits its two chunks for every width and trace length. -/
theorem wide_degreeFits (w logN : Nat) : (wide w : Air F).DegreeFits logN := by
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [wide, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  rw [wide_logQuotientChunks w (by omega24), Nat.pow_succ]
  simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
  omega

/-! ### The folded quotient -/

/-- The quotient of the constraints folded by `α`: `∑_c α^(K-1-c) Q_c` over the extension. -/
noncomputable def qFold (A : Air F) (logN : Nat) (T : Nat → K[X]) (pis : List F) (a : E) : E[X] :=
  horner (A.constraints.map fun c ↦ (quotientPoly logN T pis c).map (algebraMap K E)) (C a)

/-- The folded quotient has degree below `k n`. -/
theorem natDegree_qFold (A : Air F) (logN : Nat) (pis : List F) (T : Nat → K[X])
    (hTd : TraceDeg logN T) (hdeg : A.DegreeFits logN) (a : E) :
    (qFold A logN T pis a).natDegree < 2 ^ (logN + A.logQuotientChunks) := by
  refine natDegree_horner _ a _ 0 (by rw [natDegree_zero]; exact Nat.two_pow_pos _)
    (fun p hp ↦ ?_)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact natDegree_map_le.trans_lt (natDegree_quotientPoly A logN pis T hTd hdeg c hc)

/-- The folded quotient at a point is Horner's rule over the quotients there. -/
theorem eval_qFold (A : Air F) (logN : Nat) (T : Nat → K[X]) (pis : List F) (a y : E) :
    (qFold A logN T pis a).eval y =
      horner (A.constraints.map fun c ↦ aeval y (quotientPoly logN T pis c)) a := by
  rw [qFold, ← coe_evalRingHom, horner_map, coe_evalRingHom, eval_C, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ ↦ ?_
  simp only [Function.comp_apply, eval_map_algebraMap]

/-! ### The prover's quotient values -/

section QuotientValues

/-- An element of given coordinates in the spec field. -/
theorem toSpec_ofCoeffs_sum (l : List F) : Challenge.toSpec (Challenge.ofCoeffs l : EF) =
    ∑ e ∈ Finset.range (Challenge.d EF),
      CompPoly.Extension.Ext.gen ^ e * algebraMap K E ((l.getD e 0)) := by
  rw [Challenge.toSpec_eq_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [← Challenge.coeffNat_toSpec, Challenge.toSpec_ofCoeffs,
    CompPoly.Extension.Ext.coeffNat_of_lt _ (Finset.mem_range.mp he),
    CompPoly.Extension.Ext.coeff_ofFn]

/-- Entry `e < n` of a tabulated list. -/
theorem getD_map_range {α : Type} (f : Nat → α) (n e : Nat) (d : α) (he : e < n) :
    ((List.range n).map f).getD e d = f e := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact he),
    List.getElem_map, List.getElem_range]

/-- The accumulated weighted constraints of a row as a sum in the spec field. -/
theorem toSpec_rowAcc (ev : Expr F → F) : ∀ (cw : List (Expr F × List F)) (x : Nat → F),
    Challenge.toSpec (Challenge.ofCoeffs
      ((List.range (Challenge.d EF)).map fun j ↦ rowAcc cw ev j (x j)) : EF) =
      Challenge.toSpec (Challenge.ofCoeffs ((List.range (Challenge.d EF)).map x) : EF) +
        (cw.map fun a ↦ algebraMap K E ((ev a.1)) *
          Challenge.toSpec (Challenge.ofCoeffs a.2 : EF)).sum
  | [], x => by
    rw [List.map_nil, List.sum_nil, add_zero]
    rfl
  | a :: cw, x => by
    simp only [Fast.rowAcc_cons]
    rw [toSpec_rowAcc ev cw (fun j ↦ x j + ev a.1 * a.2.getD j 0), List.map_cons, List.sum_cons,
      ← add_assoc]
    congr 1
    rw [toSpec_ofCoeffs_sum, toSpec_ofCoeffs_sum, toSpec_ofCoeffs_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he := Finset.mem_range.mp he
    rw [getD_map_range _ _ _ _ he, getD_map_range _ _ _ _ he, map_add,
      map_mul]
    ring

/-- The weighted constraints' sum is Horner's rule in `α`. -/
theorem weighted_sum (A : Air F) (alpha : EF) (g : Expr F → E) :
    ((weighted A alpha).map fun a ↦ g a.1 * Challenge.toSpec (Challenge.ofCoeffs a.2 : EF)).sum =
      horner (A.constraints.map g) (Challenge.toSpec alpha) := by
  rw [horner_eq_sum, List.length_map, weighted]
  have : (List.range A.constraints.length).map (fun k ↦ Challenge.toSpec alpha ^
      (A.constraints.length - 1 - k)) = ((List.range A.constraints.length).map fun k ↦
        Ext.coeffs (Ext.pow alpha (A.constraints.length - 1 - k))).map
          (fun l ↦ Challenge.toSpec (Challenge.ofCoeffs l : EF)) := by
    rw [List.map_map]
    refine List.map_congr_left fun k _ ↦ ?_
    simp only [Function.comp_apply]
    rw [Challenge.ofCoeffs_coeffs, toSpec_extPow]
  rw [this, List.zip_map, List.map_map]
  congr 1

/-- The prover's quotient row in the spec field. -/
theorem toSpec_quotientRow (A : Air F) (pis : List F) (d l : Nat) (tq : Mat F) (alpha : EF)
    (r : Nat) : Challenge.toSpec (quotientRow A pis d l tq alpha r) =
      algebraMap K E (((batchInv (qZh d l)).getD (r % 2 ^ l) 0)) *
        horner (A.constraints.map fun c ↦ algebraMap K E ((c.eval
          (rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r))))
          (Challenge.toSpec alpha) := by
  simp only [quotientRow]
  rw [Challenge.toSpec_smul, Algebra.smul_def]
  refine congrArg₂ (· * ·) rfl ?_
  refine (toSpec_rowAcc _ _ fun _ ↦ 0).trans ?_
  have h0 : Challenge.toSpec (Challenge.ofCoeffs
      ((List.range (Challenge.d EF)).map fun _ ↦ (0 : F)) : EF) = 0 := by
    rw [toSpec_ofCoeffs_sum]
    refine Finset.sum_eq_zero fun e he ↦ ?_
    rw [getD_map_range _ _ _ _ (Finset.mem_range.mp he), map_zero, mul_zero]
  rw [h0, zero_add]
  exact weighted_sum A alpha fun c ↦ algebraMap K E ((c.eval
    (rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r)))

/-- A batch inversion of nonzero elements, entry by entry. -/
theorem getD_batchInv (xs : Array F) (hx : ∀ x ∈ xs, x ≠ 0) (i : Nat) (hi : i < xs.size) :
    (batchInv xs).getD i 0 = (xs.getD i 0)⁻¹ := by
  rw [batchInv_eq id Function.injective_id (fun _ _ ↦ rfl) (fun _ ↦ rfl) rfl xs hx,
    Fast.getD_map_lt _ _ _ hi _ 0]

/-- The quotient domain's points. -/
theorem getD_qPoints (d l m : Nat) (hm : m < 2 ^ (d + l)) :
    (@qPoints F _ d l).getD m 0 = qpt (d + l) m := by
  rw [qPoints, cosetPoints_eq, getD_lt _ _ (by rw [Array.size_ofFn]; exact hm),
    Array.getElem_ofFn]

/-- `Z_H` on the quotient domain has period `k`. -/
theorem getD_qZh (d l r : Nat) (h : d + l ≤ 24) :
    (@qZh F _ d l).getD (r % 2 ^ l) 0 = qpt (d + l) r ^ 2 ^ d - 1 := by
  have hk : r % 2 ^ l < 2 ^ l := Nat.mod_lt _ (Nat.two_pow_pos l)
  rw [qZh, getD_lt _ _ (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn, powF_eq,
    getD_qPoints d l _ (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega24) (by omega24)))]
  congr 1
  rw [qpt, qpt, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  congr 1
  conv_rhs => rw [← Nat.mod_add_div r (2 ^ l)]
  rw [Nat.add_mul, pow_add, Nat.mul_comm (2 ^ l), Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm l,
    pow_mul' (twoAdicGen (d + l) : F) (r / 2 ^ l), twoAdicGen_pow_self (d + l) h, one_pow,
    mul_one]

/-- `Z_H` has no zero on the quotient domain. -/
theorem qZh_ne (d l : Nat) (h : d + l ≤ 24) : ∀ x ∈ @qZh F _ d l, x ≠ 0 := by
  intro x hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hx
  have hi : i.val < 2 ^ (d + l) :=
    lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by omega24) (by omega24))
  rw [powF_eq, getD_qPoints d l _ hi, sub_ne_zero]
  exact genPoint_pow_ne _ _ h d (by omega24)

/-- No quotient point is a two-adic root of unity `y`. -/
theorem points_sub_ne (d l : Nat) (h : d + l ≤ 24) (y : F) (j : Nat) (hj : j ≤ 24)
    (hy : y ^ 2 ^ j = 1) :
    ∀ x ∈ (@qPoints F _ d l).map (· - y), x ≠ 0 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hx
  rw [qPoints, cosetPoints_eq] at hp
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hp
  rw [sub_ne_zero]
  exact genPoint_ne _ _ h _ j hj hy

/-- The prover's inverse of `Z_H` at a quotient point. -/
theorem getD_invZh (d l r : Nat) (h : d + l ≤ 24) :
    (batchInv (@qZh F _ d l)).getD (r % 2 ^ l) 0 = (qpt (d + l) r ^ 2 ^ d - 1)⁻¹ := by
  have hk : r % 2 ^ l < (@qZh F _ d l).size := by
    rw [qZh, Array.size_ofFn]
    exact Nat.mod_lt _ (Nat.two_pow_pos l)
  rw [getD_batchInv _ (qZh_ne d l h) _ hk, getD_qZh d l r h]

/-- The prover's first-row selector at a quotient point is the polynomial's. -/
theorem getD_qFirst (d l r : Nat) (h : d + l ≤ 24) (hr : r < 2 ^ (d + l)) :
    (@qFirst F _ d l).getD r 0 = (firstSel (2 ^ d)).eval (qpt (d + l) r) := by
  have hs : r < ((@qPoints F _ d l).map (· - 1)).size := by
    rw [Array.size_map, qPoints, size_cosetPoints]; exact hr
  rw [qFirst, getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn,
    getD_qZh d l r h,
        getD_batchInv _ (points_sub_ne d l h (1 : F) 0 (by omega24) (by rw [one_pow])) _ hs,
    Fast.getD_map_lt _ _ _ (by rw [Array.size_map] at hs; exact hs) _ 0, getD_qPoints d l r hr]
  have hne : (qpt (d + l) r : F) - 1 ≠ 0 :=
    sub_ne_zero.mpr (genPoint_ne (d + l) r h (1 : F) 0 (by omega24) (by rw [one_pow]))
  rw [← eval_firstSel_mul (2 ^ d), mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- The prover's last-row selector at a quotient point is the polynomial's. -/
theorem getD_qLast (d l r : Nat) (h : d + l ≤ 24) (hr : r < 2 ^ (d + l)) :
    (@qLast F _ d l).getD r 0 = (lastSel (2 ^ d) (twoAdicGen d)).eval (qpt (d + l) r) := by
  have hs : r < ((@qPoints F _ d l).map (· - (twoAdicGen d)⁻¹)).size := by
    rw [Array.size_map, qPoints, size_cosetPoints]; exact hr
  have hy : ((twoAdicGen d : F))⁻¹ ^ 2 ^ d = 1 := by
    rw [inv_pow, twoAdicGen_pow_self d (by omega24), inv_one]
  rw [qLast, getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn,
    getD_qZh d l r h, getD_batchInv _ (points_sub_ne d l h _ d (by omega24) hy) _ hs,
    Fast.getD_map_lt _ _ _ (by rw [Array.size_map] at hs; exact hs) _ 0, getD_qPoints d l r hr]
  have hne : qpt (d + l) r - (twoAdicGen d : F)⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (genPoint_ne (d + l) r h _ d (by omega24) hy)
  have hd : d ≤ twoAdicity F := by omega24
  have := aeval_lastSel (S := F) (2 ^ d) (twoAdicGen d)
    (BaseField.twoAdicGen_ne_zero d hd) (twoAdicGen_pow_self d hd)
    (qpt (d + l) r)
  rw [coe_aeval_eq_eval, Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [← this, mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- The prover's transition selector at a quotient point. -/
theorem getD_qTrans (d l r : Nat) (hr : r < 2 ^ (d + l)) :
    (@qTrans F _ d l).getD r 0 = qpt (d + l) r - (twoAdicGen d)⁻¹ := by
  rw [qTrans, Fast.getD_map_lt _ _ _ (by rw [qPoints, size_cosetPoints]; exact hr) _ 0,
    getD_qPoints d l r hr]

/-- `a ^ (n mod m) = a ^ n` for `a ^ m = 1`. -/
theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] (a : M) (n m : Nat) (h : a ^ m = 1) :
    a ^ (n % m) = a ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m]
  rw [pow_add, pow_mul, h, one_pow, mul_one]

/-- The constraints at a row of the quotient domain are the constraint polynomials at its
point. -/
theorem eval_rowEnv (A : Air F) (d l : Nat) (h : d + l ≤ 24) (tq : Mat F) (pis : List F)
    (T : Nat → F[X])
    (hq : ∀ j < A.width, ∀ r < 2 ^ (d + l),
      tq.values.getD (r * tq.width + j) 0 = (T j).eval (qpt (d + l) r))
    (c : Expr F) (hc : c.colsBelow A.width = true) (r : Nat) (hr : r < 2 ^ (d + l)) :
    c.eval (rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r) =
      (constraintPoly (2 ^ d) (twoAdicGen d) T pis c).eval (qpt (d + l) r) := by
  rw [constraintPoly]
  refine (Expr.eval_hom (eval (qpt (d + l) r)) (fun _ _ ↦ eval_add) (fun a b ↦ eval_sub a b _)
    (fun _ _ ↦ eval_mul) A.width _ _ (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun _ ↦ eval_C)
    (fun _ ↦ eval_C) ?_ ?_ ?_ c hc).symm
  · change (T j).eval (qpt (d + l) r) = tq.values.getD (r * tq.width + j) 0
    rw [hq j hj r hr]
  · have hm : (r + 2 ^ l) % 2 ^ (d + l) < 2 ^ (d + l) := Nat.mod_lt _ (Nat.two_pow_pos _)
    change ((T j).comp (C (twoAdicGen d) * X)).eval (qpt (d + l) r) =
      tq.values.getD ((r + 2 ^ l) % 2 ^ (d + l) * tq.width + j) 0
    rw [hq j hj _ hm, eval_comp, eval_mul, eval_C, eval_X, qpt, qpt,
      pow_mod_of_pow_eq_one _ _ _ (twoAdicGen_pow_self (d + l) h), pow_add,
      BaseField.twoAdicGen_pow d l h, mul_comm (twoAdicGen d : F), mul_assoc]
  · exact (getD_qFirst d l r h hr).symm
  · exact (getD_qLast d l r h hr).symm
  · change (X - C (twoAdicGen d : F)⁻¹).eval (qpt (d + l) r) = (@qTrans F _ d l).getD r 0
    rw [getD_qTrans d l r hr, eval_sub, eval_X, eval_C]

/-- The trace's extension read in bit-reversed row order is the trace on the quotient domain. -/
theorem permuteRows_lde (m : Stark.Mat F) (ps : List K[X]) (b L e : Nat)
    (hm : CompStark.Mat.IsLde b (L + e) m ps) (r : Nat) (hr : r < 2 ^ L) (j : Nat)
    (hj : j < ps.length) :
    ((permuteRows m (bitRevPerm L)).getD (r * m.width + j) 0) =
      (ps.getD j 0).eval (qpt L r) := by
  obtain ⟨hw, -, -, -, h24, -, hval⟩ := hm
  have hr' := CompPoly.CPolynomial.NTT.Transform.bitRevNat_lt L r
  rw [Fast.permuteRows_getD m _ r j (by rw [Fast.size_bitRevPerm]; exact hr) (by omega24),
    Fast.bitRevPerm_getD L r hr, hval _ (lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by omega24)
      (by omega24))) j hj, reverseBits_bitRevNat L e r hr, pow_mul,
    BaseField.twoAdicGen_pow L e h24]

/-- **The prover's quotient values are the folded quotient** on the quotient domain. -/
theorem toSpec_quotientOfLde (A : Air F) (pis : List F) (logN b : Nat) (trace : Array F)
    (alpha : EF) (hlc : A.logQuotientChunks ≤ b) (h24 : logN + b ≤ 24)
    (hsat : A.ConstraintsVanish logN trace pis) (hcols : A.ColsInWidth) (ps : List K[X])
    (hps : CompStark.Mat.IsLde b (logN + b) (ldeRef logN b gen A.width trace) ps)
    (hT : TraceOn logN A.width trace (ps.getD · 0)) (r : Nat)
    (hr : r < 2 ^ (logN + A.logQuotientChunks)) :
    Challenge.toSpec ((quotientOfLde A pis logN A.logQuotientChunks
      (ldeRef logN b gen A.width trace) alpha).getD r 0) =
      (qFold A logN (ps.getD · 0) pis (Challenge.toSpec alpha)).eval
        (algebraMap K E (qpt (logN + A.logQuotientChunks) r)) := by
  set lc := A.logQuotientChunks
  set ext := ldeRef logN b gen A.width trace
  have hext : ext.width = A.width := rfl
  have hlen : ps.length = A.width := hps.1.symm.trans hext
  have hps' : CompStark.Mat.IsLde b ((logN + lc) + (b - lc)) ext ps := by
    rw [show logN + lc + (b - lc) = logN + b by omega]; exact hps
  have hq : ∀ j < A.width, ∀ r < 2 ^ (logN + lc),
      ((Mat.ofValues ext.width (2 ^ (logN + lc))
        (permuteRows ext (bitRevPerm (logN + lc)))).values.getD (r * ext.width + j) 0) =
      (ps.getD j 0).eval (qpt (logN + lc) r) := fun j hj r hr ↦
    permuteRows_lde ext ps b (logN + lc) (b - lc) hps' r hr j (by omega24)
  have hlc24 : logN + lc ≤ 24 := by omega
  have hz : (qpt (logN + lc) r : F) ^ 2 ^ logN - 1 ≠ 0 :=
    sub_ne_zero.mpr (@genPoint_pow_ne F _ (logN + lc) r hlc24 logN (by omega24))
  show Challenge.toSpec ((quotientValues A pis logN lc (Mat.ofValues ext.width (2 ^ (logN + lc))
    (permuteRows ext (bitRevPerm (logN + lc)))) alpha).getD r 0) = _
  rw [quotientValues_eq, getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn,
    toSpec_quotientRow, getD_invZh logN lc r hlc24, eval_qFold]
  have hmap : (A.constraints.map fun c ↦ algebraMap K E ((c.eval
      (rowEnv (Mat.ofValues ext.width (2 ^ (logN + lc)) (permuteRows ext (bitRevPerm (logN + lc))))
        (2 ^ (logN + lc)) (2 ^ lc) pis (qFirst logN lc) (qLast logN lc) (qTrans logN lc) r)))) =
      (A.constraints.map fun c ↦ aeval (algebraMap K E (qpt (logN + lc) r))
        (quotientPoly logN (ps.getD · 0) pis c)).map
        (· * algebraMap K E (qpt (logN + lc) r ^ 2 ^ logN - 1)) := by
    rw [List.map_map]
    refine List.map_congr_left fun c hc ↦ ?_
    rw [eval_rowEnv A logN lc hlc24 _ pis _ hq c (hcols c hc) r hr,
      constraintPoly_eq A logN (by omega24) trace pis _ hT hsat hcols c hc, eval_mul]
    simp only [Function.comp_apply]
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, ← map_mul, mul_comm]
    simp only [zH, eval_sub, eval_pow, eval_X, eval_C]
  rw [hmap, horner_mul, mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hz, map_one, mul_one]

end QuotientValues

/-! ### Recomposing the quotient from its chunks -/

section Recompose

/-- Coordinate `e` of an extension element. -/
abbrev coordOf (e : Nat) (y : EF) : F := (Ext.coeffs y).getD e 0

/-- A chunk's coordinates, tabulated. -/
theorem chunkValues_eq (qs : Array EF) (stride c n : Nat) :
    chunkValues qs stride c n = Array.ofFn (n := n * Challenge.d EF) fun k ↦
      coordOf (k.val % Challenge.d EF) (qs.getD (k.val / Challenge.d EF * stride + c) 0) := by
  simp only [chunkValues, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  show List.foldl _ _ _ = _
  have hbody : (fun (out : Array F) (r : Nat) ↦
      out ++ (Ext.coeffs (qs.getD (r * stride + c) 0)).toArray) =
      fun out r ↦ (List.range' 0 (Challenge.d EF)).foldl
        (fun o i ↦ o.push (coordOf i (qs.getD (r * stride + c) 0))) out := by
    funext out r
    have hl : (Ext.coeffs (qs.getD (r * stride + c) 0)).length = Challenge.d EF :=
      Challenge.length_coeffs _
    rw [foldl_push_range']
    congr 1
    refine Array.ext (by rw [List.size_toArray, Array.size_ofFn, hl]) fun i h1 _ ↦ ?_
    rw [Array.getElem_ofFn, List.getElem_toArray, coordOf, Nat.zero_add,
      List.getD_eq_getElem _ _ (by rw [List.size_toArray] at h1; exact h1)]
  rw [hbody, foldl_blocks (fun r i ↦ coordOf i (qs.getD (r * stride + c) 0)) (Challenge.d EF) n 0,
    Array.emptyWithCapacity_eq, Array.empty_append]
  simp only [Nat.zero_add]

/-- Coordinate `e` of chunk row `r`. -/
theorem chunkValues_getD (qs : Array EF) (stride c n r e : Nat) (hr : r < n)
    (he : e < Challenge.d EF) :
    (chunkValues qs stride c n).getD (r * Challenge.d EF + e) 0 =
      coordOf e (qs.getD (r * stride + c) 0) := by
  have hlt : r * Challenge.d EF + e < n * Challenge.d EF := by nlinarith
  rw [chunkValues_eq, getD_lt _ _ (by rw [Array.size_ofFn]; exact hlt), Array.getElem_ofFn]
  simp only
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he,
    Nat.add_mul_div_right _ _ (by omega24), Nat.div_eq_of_lt he, Nat.zero_add]

/-- An extension element is the sum of its coordinates times the basis. -/
theorem toSpec_eq_basis (y : EF) : Challenge.toSpec y = ∑ e ∈ Finset.range (Challenge.d EF),
    Challenge.toSpec (Ext.basis e : EF) * algebraMap K E ((coordOf e y)) := by
  rw [Challenge.toSpec_eq_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [Ext.toSpec_basis (Finset.mem_range.mp he)]

variable (EF) in
/-- The chunk polynomial over the extension from its `d` coordinate polynomials. -/
noncomputable def chunkPoly (ps : List K[X]) : E[X] :=
  ∑ e ∈ Finset.range (Challenge.d EF),
    C (Challenge.toSpec (Ext.basis e : EF)) * (ps.getD e 0).map (algebraMap K E)

/-- The chunk polynomial at a point, from its coordinate polynomials there. -/
theorem eval_chunkPoly (ps : List K[X]) (y : E) : (chunkPoly EF ps).eval y =
    ∑ e ∈ Finset.range (Challenge.d EF),
      Challenge.toSpec (Ext.basis e : EF) * aeval y (ps.getD e 0) := by
  rw [chunkPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [eval_mul, eval_C, eval_map_algebraMap]

/-- The chunk polynomial has the degree bound of its coordinates. -/
theorem natDegree_chunkPoly (ps : List K[X]) (N : Nat) (hN : 0 < N)
    (hps : ∀ e < Challenge.d EF, (ps.getD e 0).natDegree < N) :
    (chunkPoly EF ps).natDegree < N := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun e he ↦ ?_) (by omega24)
  refine (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans ?_)
  have := hps e (Finset.mem_range.mp he)
  omega

/-- A `natDegree` bound from a positive degree bound. -/
theorem natDegree_lt_of_degree_lt' {p : K[X]} {N : Nat} (hN : 0 < N)
    (h : p.degree < (N : WithBot Nat)) : p.natDegree < N := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero]; exact hN
  · exact (natDegree_lt_iff_degree_lt hp).mpr h

/-- Chunk `c` of the quotient values extends to an LDE whose chunk polynomial, of degree below
`n`, agrees with `Q` on the coset `s_c ⟨ω⟩`. -/
theorem chunk_lde (logN b lc : Nat) (h24 : logN + b ≤ 24) (hlc : lc ≤ b) (qs : Array EF)
    (Q : E[X]) (hqs : ∀ m < 2 ^ (logN + lc),
      Challenge.toSpec (qs.getD m 0) = Q.eval (algebraMap K E (qpt (logN + lc) m)))
    (c : Nat) (hc : c < 2 ^ lc) :
    ∃ ps, CompStark.Mat.IsLde b (logN + b) (ldeRef logN b
      (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ lc) c (2 ^ logN))) ps ∧ (chunkPoly EF ps).natDegree < 2 ^ logN ∧
      ∀ r < 2 ^ logN,
          (chunkPoly EF ps).eval (algebraMap K E (qpt (logN + lc) c * (twoAdicGen logN : F) ^ r)) =
        Q.eval (algebraMap K E (qpt (logN + lc) c * (twoAdicGen logN : F) ^ r)) := by
  have hg := gen_ne_zero
  have hw : (twoAdicGen (logN + lc) : F) ≠ 0 := BaseField.twoAdicGen_ne_zero _ (by omega24)
  have hsh : (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹ : F) ≠ 0 := by
    rw [powF_eq]
    exact mul_ne_zero hg (inv_ne_zero (mul_ne_zero hg (pow_ne_zero _ hw)))
  obtain ⟨ps, hlde, hval⟩ := ldeRef_isLde logN b (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹)
    (Challenge.d EF) (chunkValues qs (2 ^ lc) c (2 ^ logN)) (by rw [size_chunkValues, Nat.mul_comm])
    h24
    hsh
  have hlen : ps.length = Challenge.d EF := hlde.1.symm
  have hpt : (gen * (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹)⁻¹ : F) =
      qpt (logN + lc) c := by
    rw [powF_eq, qpt]
    field_simp
  refine ⟨ps, hlde, natDegree_chunkPoly ps _ (Nat.two_pow_pos _) fun e he ↦ ?_, fun r hr ↦ ?_⟩
  · have hmem : ps.getD e 0 ∈ ps := by
      rw [List.getD_eq_getElem _ _ (by omega24)]; exact List.getElem_mem _
    have := hlde.2.2.2.2.2.1 _ hmem
    rw [Nat.add_sub_cancel] at this
    exact natDegree_lt_of_degree_lt' (Nat.two_pow_pos _) this
  · have hx : qpt (logN + lc) c * (twoAdicGen logN : F) ^ r = qpt (logN + lc) (r * 2 ^ lc + c) := by
      rw [qpt_coset logN lc c r (by omega24)]; congr 1; ring
    rw [eval_chunkPoly, hx, ← hqs _ (by rw [Nat.pow_add]; nlinarith [Nat.two_pow_pos lc]),
      toSpec_eq_basis, ← hx]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he := Finset.mem_range.mp he
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, ← hpt, hval e he r hr,
      chunkValues_getD _ _ _ _ _ _ hr he]

end Recompose

/-! ### The verifier's check -/

section Check

/-- An opened chunk's coordinates combine to its chunk polynomial at the point. -/
theorem toSpec_chunkInner_openedAt (b h : Nat) (m : Stark.Mat F) (ps : List K[X]) (z : EF)
    (hm : CompStark.Mat.IsLde b h m ps) (h4 : ps.length = Challenge.d EF)
    (hz : Ext.OutsideBase z) :
    Challenge.toSpec (chunkInner (Fri.openedAt b m z)) =
      (chunkPoly EF ps).eval (Challenge.toSpec z) := by
  rw [toSpec_chunkInner, eval_chunkPoly]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [(openedAt_isLde b h m ps z hm hz).2 e (by rw [h4]; exact Finset.mem_range.mp he)]

/-- The verifier's constraints at `ζ`, from the opened trace values, are the constraint
polynomials at `ζ`. -/
theorem toSpec_eval_opened (A : Air F) (logN b : Nat) (pis : List F) (m : Stark.Mat F)
    (ps : List K[X]) (hm : CompStark.Mat.IsLde b (logN + b) m ps)
    (hw : ps.length = A.width) (z : EF) (hz : Ext.OutsideBase z) (tl tn : Array EF)
    (htl : tl = Fri.openedAt b m z) (htn : tn = Fri.openedAt b m (z * Ext.ofBase (twoAdicGen logN)))
    (c : Expr F) (hc : c.colsBelow A.width = true) :
    Challenge.toSpec (c.eval {
      cur := fun i ↦ tl.getD i 0
      next := fun i ↦ tn.getD i 0
      pub := fun i ↦ Ext.ofBase (pis.getD i 0)
      const := Ext.ofBase
      isFirstRow := (Ext.powTwo z logN - 1) * (z - 1)⁻¹
      isLastRow := (Ext.powTwo z logN - 1) * (z - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹
      isTransition := z - Ext.ofBase (twoAdicGen logN)⁻¹ }) =
      aeval (Challenge.toSpec z)
          (constraintPoly (2 ^ logN) ((twoAdicGen logN : F)) (ps.getD · 0) pis c) := by
  have h24 : logN ≤ 24 := by have := hm.2.2.2.2.1; omega
  have hw0 : (twoAdicGen logN : F) ≠ 0 := BaseField.twoAdicGen_ne_zero logN h24
  have hz' : Ext.OutsideBase (z * Ext.ofBase (twoAdicGen logN)) := Ext.outsideBase_mul_ofBase hz hw0
  have hO := (openedAt_isLde b (logN + b) m ps z hm hz).2
  have hO' := (openedAt_isLde b (logN + b) m ps _ hm hz').2
  have hone : Challenge.toSpec z - 1 ≠ 0 := by
    have := toSpec_ne_ofBase hz 1
    rwa [CompPoly.Extension.Ext.ofBase_one, ← sub_ne_zero] at this
  have hlast : Challenge.toSpec z - algebraMap K E ((twoAdicGen logN : F))⁻¹ ≠ 0 := by
    have := toSpec_ne_ofBase hz ((twoAdicGen logN : F))⁻¹
    rwa [← CompPoly.Extension.Ext.algebraMap_eq_ofBase, ← sub_ne_zero] at this
  subst htl htn
  set env : Expr.Env F EF := {
      cur := fun i ↦ (Fri.openedAt b m z).getD i 0
      next := fun i ↦ (Fri.openedAt b m (z * Ext.ofBase (twoAdicGen logN))).getD i 0
      pub := fun i ↦ Ext.ofBase (pis.getD i 0)
      const := Ext.ofBase
      isFirstRow := (Ext.powTwo z logN - 1) * (z - 1)⁻¹
      isLastRow := (Ext.powTwo z logN - 1) * (z - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹
      isTransition := z - Ext.ofBase (twoAdicGen logN)⁻¹ } with henv
  let envE : Expr.Env F E := {
    cur := fun j ↦ Challenge.toSpec (env.cur j)
    next := fun j ↦ Challenge.toSpec (env.next j)
    pub := fun j ↦ Challenge.toSpec (env.pub j)
    const := fun x ↦ Challenge.toSpec (env.const x)
    isFirstRow := Challenge.toSpec env.isFirstRow
    isLastRow := Challenge.toSpec env.isLastRow
    isTransition := Challenge.toSpec env.isTransition }
  refine (Expr.eval_hom Challenge.toSpec Challenge.toSpec_add Challenge.toSpec_sub
      Challenge.toSpec_mul A.width env
    envE (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl rfl c hc).trans ?_
  rw [constraintPoly]
  refine (Expr.eval_hom (fun p ↦ aeval (Challenge.toSpec z) p)
    (fun a b ↦ (aeval (Challenge.toSpec z)).map_add a b) (fun a b ↦ (aeval (Challenge.toSpec
        z)).map_sub a b)
    (fun a b ↦ (aeval (Challenge.toSpec z)).map_mul a b) A.width _ envE (fun j hj ↦ ?_)
    (fun j hj ↦ ?_) (fun j ↦ ?_) (fun x ↦ ?_) ?_ ?_ ?_ c hc).symm
  · exact (hO j (by rw [hw]; exact hj)).symm
  · change aeval (Challenge.toSpec z) ((ps.getD j 0).comp (C ((twoAdicGen logN : F)) * X)) =
      Challenge.toSpec ((Fri.openedAt b m (z * Ext.ofBase (twoAdicGen logN))).getD j 0)
    rw [hO' j (by rw [hw]; exact hj), aeval_comp, map_mul, aeval_C, aeval_X, Challenge.toSpec_mul,
      Challenge.toSpec_ofBase, ← CompPoly.Extension.Ext.algebraMap_eq_ofBase, mul_comm]
  · change aeval (Challenge.toSpec z) (C ((pis.getD j 0))) =
      Challenge.toSpec (Ext.ofBase (pis.getD j 0))
    rw [aeval_C, Challenge.toSpec_ofBase, CompPoly.Extension.Ext.algebraMap_eq_ofBase]
  · change aeval (Challenge.toSpec z) (C (x)) = Challenge.toSpec (Ext.ofBase x)
    rw [aeval_C, Challenge.toSpec_ofBase, CompPoly.Extension.Ext.algebraMap_eq_ofBase]
  · change aeval (Challenge.toSpec z) (firstSel (2 ^ logN)) =
      Challenge.toSpec ((Ext.powTwo z logN - 1) * (z - 1)⁻¹)
    rw [Challenge.toSpec_mul, Challenge.toSpec_inv, Challenge.toSpec_sub, Challenge.toSpec_sub,
      toSpec_extPowTwo, Challenge.toSpec_one, ← @aeval_firstSel F _ _ _ _,
          mul_mul_inv_cancel_ext _ _ hone]
  · change aeval (Challenge.toSpec z) (lastSel (2 ^ logN) ((twoAdicGen logN : F))) =
      Challenge.toSpec ((Ext.powTwo z logN - 1) * (z - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹)
    rw [Challenge.toSpec_mul, Challenge.toSpec_inv, Challenge.toSpec_sub, Challenge.toSpec_sub,
      toSpec_extPowTwo, Challenge.toSpec_one, Challenge.toSpec_ofBase,
          ← CompPoly.Extension.Ext.algebraMap_eq_ofBase,
      ← aeval_lastSel (2 ^ logN) ((twoAdicGen logN : F)) (BaseField.twoAdicGen_ne_zero logN h24)
        (twoAdicGen_pow_self logN h24),
      mul_mul_inv_cancel_ext _ _ hlast]
  · change aeval (Challenge.toSpec z) (X - C ((twoAdicGen logN : F))⁻¹) =
      Challenge.toSpec (z - Ext.ofBase (twoAdicGen logN)⁻¹)
    rw [map_sub, aeval_X, aeval_C, Challenge.toSpec_sub, Challenge.toSpec_ofBase,
        CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- The trace's extension is an LDE of polynomials that take the trace on `⟨ω⟩`. -/
theorem trace_lde (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (hin : Fits P A logN trace) :
    ∃ ps, CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup)
      (ldeRef logN P.logBlowup gen A.width trace) ps ∧
      TraceOn logN A.width trace (ps.getD · 0) ∧ TraceDeg logN (ps.getD · 0) := by
  obtain ⟨ps, hlde, hval⟩ := ldeRef_isLde logN P.logBlowup gen A.width trace hin.trace
    hin.twoAdic gen_ne_zero
  refine ⟨ps, hlde, fun j hj i hi ↦ ?_, fun j ↦ ?_⟩
  · have := hval j hj i hi
    rwa [mul_inv_cancel₀ gen_ne_zero, one_mul] at this
  · by_cases hj : j < ps.length
    · have hmem : ps.getD j 0 ∈ ps := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
      have := hlde.2.2.2.2.2.1 _ hmem
      rw [Nat.add_sub_cancel] at this
      have := natDegree_lt_of_degree_lt' (Nat.two_pow_pos _) this
      show (ps.getD j 0).natDegree ≤ 2 ^ logN - 1
      omega
    · show (ps.getD j 0).natDegree ≤ 2 ^ logN - 1
      rw [List.getD_eq_default _ _ (by omega24), natDegree_zero]
      exact Nat.zero_le _

/-- The check passes when the folded constraints over `Z_H(ζ)` equal the quotient in the spec
field. -/
theorem checkConstraints_of (A : Air F) (pis : List F) (o : OpenedValues EF) (logN : Nat)
    (zeta alpha quotient : EF)
    (h : Challenge.toSpec (foldedConstraints A {
      cur := fun i ↦ o.traceLocal.getD i 0
      next := fun i ↦ o.traceNext.getD i 0
      pub := fun i ↦ Ext.ofBase (pis.getD i 0)
      const := Ext.ofBase
      isFirstRow := (Ext.powTwo zeta logN - 1) * (zeta - 1)⁻¹
      isLastRow := (Ext.powTwo zeta logN - 1) * (zeta - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹
      isTransition := zeta - Ext.ofBase (twoAdicGen logN)⁻¹ } alpha *
      (Ext.powTwo zeta logN - 1)⁻¹) = Challenge.toSpec quotient) :
    checkConstraints A pis o logN zeta alpha quotient = true := by
  rw [checkConstraints_eq_fun]
  exact beq_iff_eq.mpr (Challenge.toSpec_injective h)

/-- **The out-of-domain check passes on the honest openings.** -/
theorem checkConstraints_honest (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (pis : List F) (alpha zeta : EF) (hin : Fits P A logN trace)
    (hsat : A.ConstraintsVanish logN trace pis) (hdeg : A.DegreeFits logN)
    (hz : Ext.OutsideBase zeta) :
    let ext := ldeRef logN P.logBlowup gen A.width trace
    let qs := quotientOfLde A pis logN A.logQuotientChunks ext alpha
    let lc := A.logQuotientChunks
    let chunks := (List.range (2 ^ lc)).map fun c ↦
      ldeRef logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
        (chunkValues qs (2 ^ lc) c (2 ^ logN))
    let o : OpenedValues EF := ⟨Fri.openedAt P.logBlowup ext zeta,
      Fri.openedAt P.logBlowup ext (zeta * Ext.ofBase (twoAdicGen logN)),
      (chunks.map fun m ↦ Fri.openedAt P.logBlowup m zeta).toArray⟩
    checkConstraints A pis o logN zeta alpha
      (recompose (chunkDomains logN lc) o.quotientChunks.toList zeta) = true := by
  intro ext qs lc chunks o
  have h24 := hin.twoAdic
  have hlc : lc ≤ P.logBlowup := hin.chunks
  have hq24 : logN + lc ≤ 24 := by omega
  obtain ⟨ps, hlde, hT, hTd⟩ := trace_lde P A logN trace hin
  set Q := qFold A logN (ps.getD · 0) pis (Challenge.toSpec alpha)
  have hQ := natDegree_qFold A logN pis _ hTd hdeg (Challenge.toSpec alpha)
  have hqs : ∀ m < 2 ^ (logN + lc), Challenge.toSpec (qs.getD m 0) =
      Q.eval (algebraMap K E (qpt (logN + lc) m)) := fun m hm ↦
    toSpec_quotientOfLde A pis logN P.logBlowup trace alpha hlc h24 hsat hin.cols ps hlde hT m hm
  have hch : ∀ c, ∃ cps : List K[X], c < 2 ^ lc →
      CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup) (ldeRef logN P.logBlowup
        (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
        (chunkValues qs (2 ^ lc) c (2 ^ logN))) cps ∧ (chunkPoly EF cps).natDegree < 2 ^ logN ∧
      ∀ r < 2 ^ logN,
          (chunkPoly EF cps).eval (algebraMap K E (qpt (logN + lc) c * (twoAdicGen logN : F) ^ r)) =
        Q.eval (algebraMap K E (qpt (logN + lc) c * (twoAdicGen logN : F) ^ r)) := by
    intro c
    by_cases hc : c < 2 ^ lc
    · obtain ⟨cps, h1⟩ := chunk_lde logN P.logBlowup lc h24 hlc qs Q hqs c hc
      exact ⟨cps, fun _ ↦ h1⟩
    · exact ⟨[], fun h ↦ absurd h hc⟩
  choose cps hcps using hch
  -- The recomposed quotient is `Q(ζ)`.
  have hrec : Challenge.toSpec (recompose (chunkDomains logN lc) o.quotientChunks.toList zeta) =
      Q.eval (Challenge.toSpec zeta) := by
    have hl : o.quotientChunks.toList = (List.range (2 ^ lc)).map fun c ↦
        Fri.openedAt P.logBlowup (ldeRef logN P.logBlowup
          (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
          (chunkValues qs (2 ^ lc) c (2 ^ logN))) zeta := by
      show (chunks.map fun m ↦ Fri.openedAt P.logBlowup m zeta) = _
      simp only [chunks, List.map_map, Function.comp_def]
    rw [hl, toSpec_recompose logN lc hq24, ← sum_chunkSel logN lc hq24 Q hQ
      (fun c ↦ chunkPoly EF (cps c)) (fun c hc ↦ (hcps c hc).2.1) (fun c hc ↦ (hcps c hc).2.2)]
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    have hc := Finset.mem_range.mp hc
    have h4 : (cps c).length = Challenge.d EF := (hcps c hc).1.1.symm
    rw [toSpec_chunkInner_openedAt _ _ _ _ _ (hcps c hc).1 h4 hz]
  -- The folded constraints at `ζ` over `Z_H(ζ)` are `Q(ζ)`.
  have hzh : Challenge.toSpec zeta ^ 2 ^ logN - 1 ≠ 0 := by
    have := pow_ne_of_outsideBase hz (specDomain logN (by omega24)) one_ne_zero
    rw [map_one, one_pow] at this
    exact sub_ne_zero.mpr this
  have hlen : ps.length = A.width := hlde.1.symm
  refine checkConstraints_of A pis o logN zeta alpha _ ?_
  rw [hrec, Challenge.toSpec_mul, toSpec_foldedConstraints, Challenge.toSpec_inv,
    Challenge.toSpec_sub, toSpec_extPowTwo, Challenge.toSpec_one, eval_qFold]
  have hmap : (A.constraints.map fun c ↦ Challenge.toSpec (c.eval {
      cur := fun i ↦ o.traceLocal.getD i 0
      next := fun i ↦ o.traceNext.getD i 0
      pub := fun i ↦ Ext.ofBase (pis.getD i 0)
      const := Ext.ofBase
      isFirstRow := (Ext.powTwo zeta logN - 1) * (zeta - 1)⁻¹
      isLastRow := (Ext.powTwo zeta logN - 1) * (zeta - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹
      isTransition := zeta - Ext.ofBase (twoAdicGen logN)⁻¹ })) =
      (A.constraints.map fun c ↦ aeval (Challenge.toSpec zeta)
        (quotientPoly logN (ps.getD · 0) pis c)).map (· * (Challenge.toSpec zeta ^ 2 ^ logN -
            1)) := by
    rw [List.map_map]
    refine List.map_congr_left fun c hc ↦ ?_
    rw [toSpec_eval_opened A logN P.logBlowup pis ext ps hlde hlen zeta hz o.traceLocal
      o.traceNext rfl rfl c (hin.cols c hc),
      constraintPoly_eq A logN (by omega24) trace pis _ hT hsat hin.cols c hc, map_mul]
    simp only [Function.comp_apply, zH, map_sub, map_pow, aeval_X, map_one]
    ring
  rw [hmap, horner_mul, mul_mul_inv_cancel_ext _ _ hzh]

/-- Every chunk of the honest quotient is an LDE of `d` polynomials. -/
theorem chunk_isLde (P : Params) (A : Air F) (logN : Nat) (qs : Array EF)
    (h24 : logN + P.logBlowup ≤ 24) (hlc : A.logQuotientChunks ≤ P.logBlowup) (c : Nat) :
    ∃ ps, CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup) (ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))) ps ∧
        ps.length = Challenge.d EF := by
  have hg := gen_ne_zero
  have hsh : (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹ : F) ≠ 0 := by
    rw [powF_eq]
    exact mul_ne_zero hg (inv_ne_zero (mul_ne_zero hg
      (pow_ne_zero _ (BaseField.twoAdicGen_ne_zero _ (by omega24)))))
  obtain ⟨ps, hlde, -⟩ := ldeRef_isLde logN P.logBlowup
    (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
    (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))
    (by rw [size_chunkValues, Nat.mul_comm]) h24 hsh
  exact ⟨ps, hlde, hlde.1.symm⟩

/-- The honest openings pass the verifier's shape check. -/
theorem honest_shape (P : Params) (A : Air F) (logN : Nat) (trace : Array F) (pis : List F)
    (alpha zeta : EF) :
    let ext := ldeRef logN P.logBlowup gen A.width trace
    let qs := quotientOfLde A pis logN A.logQuotientChunks ext alpha
    let lc := A.logQuotientChunks
    let chunks := (List.range (2 ^ lc)).map fun c ↦
      ldeRef logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) (Challenge.d EF)
        (chunkValues qs (2 ^ lc) c (2 ^ logN))
    let o : OpenedValues EF := ⟨Fri.openedAt P.logBlowup ext zeta,
      Fri.openedAt P.logBlowup ext (zeta * Ext.ofBase (twoAdicGen logN)),
      (chunks.map fun m ↦ Fri.openedAt P.logBlowup m zeta).toArray⟩
    (o.traceLocal.size == A.width && o.traceNext.size == A.width &&
      o.quotientChunks.size == 2 ^ lc && o.quotientChunks.all (·.size == Challenge.d EF)) =
      true := by
  intro ext qs lc chunks o
  have hs (m : Stark.Mat F) (z : EF) : (Fri.openedAt P.logBlowup m z).size = m.width := by
    rw [openedAt_eq, Array.size_ofFn]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hs ext zeta, hs ext _⟩, ?_⟩, ?_⟩
  · show (chunks.map fun m ↦ Fri.openedAt P.logBlowup m zeta).toArray.size = 2 ^ lc
    rw [List.size_toArray, List.length_map, List.length_map, List.length_range]
  · rw [Array.all_eq_true]
    intro i hi
    simp only [o, chunks, List.getElem_toArray, List.getElem_map, hs, beq_iff_eq]
    rfl

end Check

end CompStark.Stark
