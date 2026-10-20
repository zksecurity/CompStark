/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Defs
public import CompStark.Stark.Fast.Lde
public import CompStark.Stark.Fast.Vectors
public import CompStark.Stark.Fast.Openings
public import CompPoly.Univariate.NTTFast.Packed.BitReversal
public import CompPoly.Univariate.NTTFast.Permutation
public import Mathlib.LinearAlgebra.Lagrange

/-! # FRI's folds keep low degree

The pure facts behind FRI's completeness, over the Mathlib fields the Montgomery elements denote:

* `lagrange` evaluates the interpolant: through distinct points carrying the values of a
  polynomial of smaller degree, it is that polynomial's value (`toSpec_lagrange`).
* A group of `2 ^ la` entries of a low-degree vector `vs` sits on a coset of the subgroup of order
  `2 ^ la`, where `p = ∑ₖ Xᵏ pₖ(X ^ 2 ^ la)` agrees with the polynomial `∑ₖ Xᵏ pₖ(y)` of degree
  below `2 ^ la`, `y` the coset's `2 ^ la`-th power. `foldRow` interpolates it at `β`, giving
  `(∑ₖ βᵏ pₖ)(y)`: the folded vector is low degree (`lowDegree_foldRows`), and so is the arity-2
  fold `foldPairs`, which is `foldRow` with arity 2 (`foldPairs_getD`).
* The final polynomial is the inverse transform of the low coefficients' values, which Horner's
  rule evaluates back to the vector's entries (`horner_idft`).
-/

@[expose] public section
namespace CompStark.Complete
open CompStark.Stark CompStark.Fri Polynomial Montgomery.Native32

variable {EF : Type} [Challenge EF]

local notation "F" => KoalaBear.Fast.Field
local notation "K" => KoalaBear.Field
local notation "L" => Challenge.Spec EF

/-- A base element in the specification's extension. -/
abbrev emb (x : F) : L := algebraMap K L (FastField.toField x)

theorem toSpec_ofBase (x : F) : Challenge.toSpec (Ext.ofBase x : EF) = emb x :=
  Challenge.toSpec_ofBase x

theorem emb_mul (x y : F) : (emb (x * y) : L) = emb x * emb y := by
  rw [emb, toField_mul, map_mul]

theorem emb_pow (x : F) (n : Nat) : (emb (x ^ n) : L) = emb x ^ n := by
  rw [emb, toField_npow, map_pow]

theorem emb_injective : Function.Injective (emb : F → L) :=
  (algebraMap K L).injective.comp toField_injective

/-- The two-adic generator of order `2 ^ n`, `n ≤ 24`, is a primitive root. -/
theorem isPrimitiveRoot_twoAdicGen (n : Nat) (hn : n ≤ 24) :
    IsPrimitiveRoot (twoAdicGen n) (2 ^ n) := by
  have h := KoalaBear.isPrimitiveRoot_twoAdicGenerator ⟨n, by
    show n < 24 + 1; omega⟩
  rw [Fast.twoAdicGen_eq_table ⟨n, by omega⟩]
  refine IsPrimitiveRoot.of_map_of_injective (f := ringEquiv KoalaBear.fieldSize) ?_
    (RingEquiv.injective _)
  have e : (ringEquiv KoalaBear.fieldSize) (KoalaBear.Fast.twoAdicGenerators[n]'(by
      simp only [KoalaBear.Fast.twoAdicGenerators, List.length_cons, List.length_nil]; omega)) =
      KoalaBear.twoAdicGenerators[n]'(by
        simp only [KoalaBear.twoAdicGenerators, List.length_cons, List.length_nil]; omega) := by
    simp only [ringEquiv_apply, KoalaBear.Fast.twoAdicGenerators_eq_map, List.getElem_map,
      KoalaBear.Fast.ofField, toField_ofField]
  rw [e]
  exact h


/-! ### `lagrange` evaluates the interpolant -/

theorem toSpec_foldl_add (n : Nat) (f : Nat → EF) (a : EF) :
    Challenge.toSpec ((List.range n).foldl (fun acc k ↦ acc + f k) a) =
      Challenge.toSpec a + ∑ k ∈ Finset.range n, Challenge.toSpec (f k) := by
  induction n with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Challenge.toSpec_add,
      ih, Finset.sum_range_succ, add_assoc]

theorem toSpec_foldl_weight (n : Nat) (gx : Nat → F) (x : F) (c d : Nat → EF) (a : EF) :
    Challenge.toSpec ((List.range n).foldl (fun w k ↦ if gx k == x then w else w * c k * d k) a) =
      Challenge.toSpec a * ∏ k ∈ Finset.range n,
        if gx k = x then 1 else Challenge.toSpec (c k) * Challenge.toSpec (d k) := by
  induction n with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.prod_range_zero, mul_one]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.prod_range_succ, ← mul_assoc, ← ih]
    by_cases h : gx n = x
    · simp only [h, beq_self_eq_true, ite_true, mul_one]
    · simp only [beq_iff_eq, h, ite_false, Challenge.toSpec_mul, mul_assoc]

/-- `lagrange` through distinct points `gx k`, `k < n`, holding the values of `q` of degree below
`n`, is `q`'s value. -/
theorem toSpec_lagrange (n : Nat) (gx : Nat → F) (gy : Nat → EF) (z : EF) (q : L[X])
    (hinj : ∀ i < n, ∀ j < n, gx i = gx j → i = j) (hdeg : q.degree < n)
    (hq : ∀ i < n, Challenge.toSpec (gy i) = q.eval (emb (gx i))) :
    Challenge.toSpec (lagrange ((List.range n).map gx) ((List.range n).map gy) z) =
      q.eval (Challenge.toSpec z) := by
  unfold lagrange
  rw [List.zip_map']
  dsimp only
  split
  · rename_i x y hfind
    have hp := List.find?_some hfind
    obtain ⟨k, hk, hxy⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rw [beq_iff_eq] at hp
    rw [hp, toSpec_ofBase, hq k (List.mem_range.mp hk)]
  · simp only [List.foldl_map]
    rw [toSpec_foldl_add, Challenge.toSpec_zero, zero_add]
    simp only [Challenge.toSpec_mul]
    have hinj' : Set.InjOn (fun k ↦ (emb (gx k) : L)) (Finset.range n : Set Nat) :=
      fun i hi j hj h ↦ hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
        (emb_injective h)
    rw [Lagrange.eq_interpolate_of_eval_eq (r := fun k ↦ Challenge.toSpec (gy k)) hinj'
      (by rwa [Finset.card_range]) (fun i hi ↦ (hq i (Finset.mem_range.mp hi)).symm),
      Lagrange.interpolate_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [eval_mul, eval_C, Lagrange.basis, eval_prod]
    congr 1
    rw [toSpec_foldl_weight, Challenge.toSpec_one, one_mul, ← Finset.mul_prod_erase _ _ hk,
      ite_eq_left rfl,
      one_mul]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    obtain ⟨hjk, hj⟩ := Finset.mem_erase.mp hj
    rw [ite_eq_right (fun h ↦ hjk (hinj _ (Finset.mem_range.mp hj) _ (Finset.mem_range.mp hk) h)),
      Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C]
    simp only [Challenge.toSpec_sub, toSpec_ofBase, emb, toField_inv, toField_sub, map_inv₀,
        map_sub]
    ring

/-! ### Folding a polynomial -/

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (f : Nat → M) (N a : Nat) :
    ∑ i ∈ Finset.range (N * a), f i =
      ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range a, f (n * a + k) := by
  induction N with
  | zero => rw [Nat.zero_mul, Finset.sum_range_zero, Finset.sum_range_zero]
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- `p = ∑ₖ Xᵏ pₖ(X ^ a)`, `pₖ` the coefficients `n a + k`. -/
theorem eval_decimate (p : L[X]) (a N : Nat) (hN : p.natDegree < N * a) (x : L) :
    p.eval x = ∑ k ∈ Finset.range a, x ^ k *
      ∑ n ∈ Finset.range N, p.coeff (n * a + k) * (x ^ a) ^ n := by
  rw [eval_eq_sum_range' hN, sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [pow_add, ← pow_mul, Nat.mul_comm a n]
  ring

/-- The fold at `β` by `2 ^ la`: coefficient `n` is `∑ₖ βᵏ p[n 2 ^ la + k]`, for `n < N`. -/
noncomputable def foldPoly (la : Nat) (beta : L) (N : Nat) (p : L[X]) : L[X] :=
  ∑ n ∈ Finset.range N,
    C (∑ k ∈ Finset.range (2 ^ la), beta ^ k * p.coeff (n * 2 ^ la + k)) * X ^ n

/-- The polynomial of degree below `a` that agrees with `p` where `X ^ a = y`. -/
noncomputable def groupPoly (a N : Nat) (y : L) (p : L[X]) : L[X] :=
  ∑ k ∈ Finset.range a, C (∑ n ∈ Finset.range N, p.coeff (n * a + k) * y ^ n) * X ^ k

theorem degree_sum_C_mul_X_pow_lt (N : Nat) (c : Nat → L) :
    (∑ n ∈ Finset.range N, C (c n) * X ^ n).degree < (N : WithBot Nat) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [coeff_C_mul_X_pow, ite_eq_right (by have := Finset.mem_range.mp hn; omega)]

theorem eval_sum_C_mul_X_pow (N : Nat) (c : Nat → L) (x : L) :
    (∑ n ∈ Finset.range N, C (c n) * X ^ n).eval x = ∑ n ∈ Finset.range N, c n * x ^ n := by
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

theorem eval_groupPoly (p : L[X]) (a N : Nat) (hN : p.natDegree < N * a) (y x : L)
    (hx : x ^ a = y) : (groupPoly a N y p).eval x = p.eval x := by
  rw [groupPoly, eval_sum_C_mul_X_pow, eval_decimate p a N hN, hx]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

theorem eval_groupPoly_beta (p : L[X]) (la N : Nat) (y beta : L) :
    (groupPoly (2 ^ la) N y p).eval beta = (foldPoly la beta N p).eval y := by
  rw [groupPoly, foldPoly, eval_sum_C_mul_X_pow, eval_sum_C_mul_X_pow]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem degree_foldPoly (la : Nat) (beta : L) (N : Nat) (p : L[X]) :
    (foldPoly la beta N p).degree < (N : WithBot Nat) :=
  degree_sum_C_mul_X_pow_lt N _

theorem natDegree_lt_of_degree {p : L[X]} {n : Nat} (hp : p.degree < (n : WithBot Nat))
    (hn : 0 < n) : p.natDegree < n := by
  by_cases h0 : p = 0
  · rw [h0, natDegree_zero]; exact hn
  · exact (natDegree_lt_iff_degree_lt h0).mpr hp

/-! ### Bit reversal and the two-adic generators -/

open CompPoly.CPolynomial.NTT.Transform in
theorem reverseBits_concat (la m i k : Nat) (hk : k < 2 ^ la) :
    reverseBits (i * 2 ^ la + k) (m + la) = 2 ^ m * reverseBits k la + reverseBits i m := by
  rw [Fast.reverseBits_eq, Fast.reverseBits_eq, Fast.reverseBits_eq, Nat.mul_comm i]
  exact CompPoly.CPolynomial.NTTFast.Packed.bitRevNat_concat m la i k hk

theorem reverseBits_lt (i bits : Nat) : reverseBits i bits < 2 ^ bits := by
  rw [Fast.reverseBits_eq]; exact CompPoly.CPolynomial.NTT.Transform.bitRevNat_lt _ _

theorem reverseBits_reverseBits {i bits : Nat} (hi : i < 2 ^ bits) :
    reverseBits (reverseBits i bits) bits = i := by
  rw [Fast.reverseBits_eq, Fast.reverseBits_eq]
  exact CompPoly.CPolynomial.NTT.Transform.bitRevNat_involutive bits i hi

theorem reverseBits_injective {i j bits : Nat} (hi : i < 2 ^ bits) (hj : j < 2 ^ bits)
    (h : reverseBits i bits = reverseBits j bits) : i = j := by
  rw [← reverseBits_reverseBits hi, h, reverseBits_reverseBits hj]

theorem twoAdicGen_ne_zero' (n : Nat) (hn : n ≤ 24) (e : Nat) : twoAdicGen n ^ e ≠ 0 :=
  pow_ne_zero _ (twoAdicGen_ne_zero n hn)

/-- Entry `i 2 ^ la + k` of the domain of order `2 ^ (m + la)` in bit-reversed order is the
group point `start · g ^ bitrev k`, `start` entry `i` of the folded domain's square roots. -/
theorem twoAdicGen_pow_concat (la m i k : Nat) (hml : m + la ≤ 24) (hk : k < 2 ^ la) :
    twoAdicGen (m + la) ^ reverseBits (i * 2 ^ la + k) (m + la) =
      twoAdicGen (m + la) ^ reverseBits i m * twoAdicGen la ^ reverseBits k la := by
  rw [reverseBits_concat la m i k hk, pow_add, pow_mul, Nat.add_comm m la,
    Fast.twoAdicGen_pow la m (by omega), mul_comm]

theorem twoAdicGen_pow_pow (la m r : Nat) (hml : m + la ≤ 24) :
    (twoAdicGen (m + la) ^ r) ^ 2 ^ la = twoAdicGen m ^ r := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, Fast.twoAdicGen_pow m la hml]

/-! ### The fold of a low-degree vector -/

/-- A group's points `start · g ^ bitrev k` are distinct. -/
theorem groupPoints_injective (la : Nat) (start : F) (hla : la ≤ 24) (hs : start ≠ 0) :
    ∀ a < 2 ^ la, ∀ b < 2 ^ la, start * powF (twoAdicGen la) (reverseBits a la) =
      start * powF (twoAdicGen la) (reverseBits b la) → a = b := by
  intro a ha b hb h
  rw [Fast.powF_eq, Fast.powF_eq] at h
  exact reverseBits_injective ha hb ((isPrimitiveRoot_twoAdicGen la hla).pow_inj
    (reverseBits_lt _ _) (reverseBits_lt _ _) (mul_left_cancel₀ hs h))

/-- `foldRow` of entry `i`'s group of a vector of the values of `p`, degree below `2 ^ d`, on the
domain of order `2 ^ (m + la)` in bit-reversed order, is the fold's value at entry `i` of the
folded domain. -/
theorem toSpec_foldRow (vs : Array EF) (m la d : Nat) (beta : EF) (p : L[X])
    (hml : m + la ≤ 24) (hla : la ≤ d) (hd : p.degree < ((2 ^ d : Nat) : WithBot Nat))
    (hv : ∀ r < 2 ^ (m + la), Challenge.toSpec (vs.getD r 0) =
      p.eval (emb (twoAdicGen (m + la)) ^ reverseBits r (m + la)))
    (i : Nat) (hi : i < 2 ^ m) :
    Challenge.toSpec (foldRow i m la beta
        ((List.range (2 ^ la)).map fun k ↦ vs.getD (i * 2 ^ la + k) 0)) =
      (foldPoly la (Challenge.toSpec beta) (2 ^ (d - la)) p).eval
        (emb (twoAdicGen m) ^ reverseBits i m) := by
  have hg := isPrimitiveRoot_twoAdicGen la (by omega)
  have hN : p.natDegree < 2 ^ (d - la) * 2 ^ la := by
    rw [← pow_add, Nat.sub_add_cancel hla]
    exact natDegree_lt_of_degree hd (by positivity)
  set start := twoAdicGen (m + la) ^ reverseBits i m with hstart
  have hgx : ∀ k < 2 ^ la, start * powF (twoAdicGen la) (reverseBits k la) =
      twoAdicGen (m + la) ^ reverseBits (i * 2 ^ la + k) (m + la) := fun k hk ↦ by
    rw [Fast.powF_eq, twoAdicGen_pow_concat la m i k hml hk]
  unfold foldRow
  dsimp only
  rw [Fast.powF_eq]
  rw [toSpec_lagrange (2 ^ la) (fun k ↦ start * powF (twoAdicGen la) (reverseBits k la))
    (fun k ↦ vs.getD (i * 2 ^ la + k) 0) beta
    (groupPoly (2 ^ la) (2 ^ (d - la)) (emb start ^ 2 ^ la) p)]
  · rw [eval_groupPoly_beta, ← emb_pow, hstart, twoAdicGen_pow_pow la m _ hml, emb_pow]
  · exact groupPoints_injective la _ (by omega) (twoAdicGen_ne_zero' _ (by omega) _)
  · exact degree_sum_C_mul_X_pow_lt _ _
  · intro k hk
    have hr : i * 2 ^ la + k < 2 ^ (m + la) := by
      have : (i + 1) * 2 ^ la ≤ 2 ^ m * 2 ^ la := Nat.mul_le_mul_right _ hi
      rw [pow_add]; rw [Nat.succ_mul] at this; omega
    rw [hv _ hr, ← emb_pow, ← hgx k hk, eval_groupPoly p _ _ hN]
    simp only [← emb_pow]
    congr 1
    rw [mul_pow, Fast.powF_eq, ← pow_mul (twoAdicGen la), Nat.mul_comm (reverseBits k la),
      pow_mul, hg.pow_eq_one, one_pow, mul_one]

/-- The groups of a low-degree vector fold to a low-degree vector. -/
theorem lowDegree_foldRows (vs : Array EF) (m la d : Nat) (beta : EF)
    (hv : LowDegree (m + la) (d + la) vs) :
    LowDegree m d (Array.ofFn (n := 2 ^ m) fun i ↦ foldRow i m la beta
      ((List.range (2 ^ la)).map fun k ↦ vs.getD (i * 2 ^ la + k) 0)) := by
  obtain ⟨-, hml, p, hp, hpv⟩ := hv
  refine ⟨Array.size_ofFn, by omega, foldPoly la (Challenge.toSpec beta) (2 ^ d) p,
    degree_foldPoly _ _ _ _, fun i hi ↦ ?_⟩
  rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hi]
  have := toSpec_foldRow vs m la (d + la) beta p hml (by omega) hp hpv i hi
  rw [Nat.add_sub_cancel] at this
  exact this

theorem twoAdicGen_one : twoAdicGen 1 = -1 := by decide

/-- The arity-2 fold is `foldRow` with arity 2. -/
theorem foldPairs_getD (vs : Array EF) (beta : EF) (m : Nat) (hm : m < 24) (i : Nat)
    (hi : i < 2 ^ m) :
    (foldPairs vs beta m).getD i 0 =
      foldRow i m 1 beta ((List.range (2 ^ 1)).map fun k ↦ vs.getD (i * 2 ^ 1 + k) 0) := by
  set start := twoAdicGen (m + 1) ^ reverseBits i m with hstart
  have hs : start ≠ 0 := twoAdicGen_ne_zero' _ (by omega) _
  have hs' : (emb start : L) ≠ 0 := fun h ↦ hs (emb_injective (h.trans (map_zero _).symm |>.trans
    (by rw [emb, toField_zero])))
  set lo := Challenge.toSpec (vs.getD (2 * i) 0)
  set hi' := Challenge.toSpec (vs.getD (2 * i + 1) 0)
  have h2 : (2 : L) ≠ 0 := by
    have h : (2 : K) ≠ 0 := by decide
    rw [← map_ofNat (algebraMap K L) 2]; exact (_root_.map_ne_zero _).mpr h
  apply Challenge.toSpec_injective
  unfold foldRow
  dsimp only
  rw [Fast.powF_eq, ← hstart,
    toSpec_lagrange (2 ^ 1) (fun k ↦ start * powF (twoAdicGen 1) (reverseBits k 1))
    (fun k ↦ vs.getD (i * 2 ^ 1 + k) 0) beta
    (C ((lo + hi') / 2) + C ((lo - hi') / (2 * emb start)) * X)]
  · rw [foldPairs_eq vs beta m hm, CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hi]
    simp only [foldAt, twoX, Challenge.toSpec_add, Challenge.toSpec_mul, Challenge.toSpec_sub,
      toSpec_ofBase, eval_add, eval_C, eval_mul, eval_X]
    rw [cosetPoints_eq, Fast.bitRevPerm_getD m i hi, ← Fast.reverseBits_eq,
      CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ (by
        have := reverseBits_lt i m; rw [pow_succ]; omega)]
    simp only [emb, toField_inv, toField_mul, one_mul, map_inv₀, map_mul]
    have e2 : (algebraMap K L) (FastField.toField (2 : F)) = 2 := by
      rw [show (2 : F) = ((2 : Nat) : F) from (Nat.cast_ofNat).symm, toField_natCast,
        Nat.cast_ofNat, map_ofNat]
    have hs'' : (algebraMap K L) (FastField.toField start) ≠ 0 := hs'
    rw [e2, ← hstart]
    field_simp
    ring
  · exact groupPoints_injective 1 _ (by omega) hs
  · rw [pow_one, add_comm]; exact_mod_cast degree_linear_lt
  · intro k hk
    have e1 : powF (twoAdicGen 1) 1 = -1 := by rw [Fast.powF_eq, pow_one, twoAdicGen_one]
    have hs'' : (algebraMap K L) (FastField.toField start) ≠ 0 := hs'
    interval_cases k
    · rw [show i * 2 ^ 1 + 0 = 2 * i by ring, show reverseBits 0 1 = 0 from rfl, Fast.powF_eq,
        pow_zero, mul_one]
      show lo = _
      simp only [eval_add, eval_C, eval_mul, eval_X, emb]
      field_simp
      ring
    · rw [show i * 2 ^ 1 + 1 = 2 * i + 1 by ring, show reverseBits 1 1 = 1 from rfl, e1]
      show hi' = _
      simp only [eval_add, eval_C, eval_mul, eval_X, emb, mul_neg, mul_one, toField_neg,
        map_neg]
      field_simp
      ring

/-- Adding a multiple of a low-degree vector keeps low degree. -/
theorem lowDegree_addScaled (H D : Nat) (a b : Array EF) (x : EF) (ha : LowDegree H D a)
    (hb : LowDegree H D b) : LowDegree H D (Array.zipWith (fun u v ↦ u + x * v) a b) := by
  obtain ⟨hsa, hH, p, hp, hpa⟩ := ha
  obtain ⟨hsb, -, q, hq, hqb⟩ := hb
  have hs : (Array.zipWith (fun u v ↦ u + x * v) a b).size = 2 ^ H := by
    rw [Array.size_zipWith, hsa, hsb, Nat.min_self]
  refine ⟨hs, hH, p + C (Challenge.toSpec x) * q, ?_, fun r hr ↦ ?_⟩
  · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt hp (lt_of_le_of_lt (degree_mul_le _ _) ?_))
    refine lt_of_le_of_lt (add_le_add_left degree_C_le _) ?_
    rwa [zero_add]
  · rw [getD_lt _ r (by rw [hs]; exact hr), Array.getElem_zipWith, ← getD_lt a r (by omega),
      ← getD_lt b r (by omega), Challenge.toSpec_add, Challenge.toSpec_mul, hpa r hr, hqb r hr,
          eval_add,
      eval_mul, eval_C]

/-! ### The final polynomial -/

theorem reverseBitsGo_zero : ∀ b, reverseBitsGo b 0 0 = 0
  | 0 => rfl
  | b + 1 => by
    rw [reverseBitsGo, Nat.zero_div, Nat.zero_mod, Nat.zero_mul]
    exact reverseBitsGo_zero b

theorem reverseBits_zero (b : Nat) : reverseBits 0 b = 0 := reverseBitsGo_zero b

/-- Reversing `k < 2 ^ la` in `m + la` bits shifts its reversal in `la` bits up by `m`. -/
theorem reverseBits_low (la m k : Nat) (hk : k < 2 ^ la) :
    reverseBits k (m + la) = 2 ^ m * reverseBits k la := by
  have := reverseBits_concat la m 0 k hk
  rwa [Nat.zero_mul, Nat.zero_add, reverseBits_zero, Nat.add_zero] at this

/-- The point of entry `k < 2 ^ la` of the domain of order `2 ^ (m + la)`, bit-reversed. -/
theorem twoAdicGen_pow_low (la m k : Nat) (hml : m + la ≤ 24) (hk : k < 2 ^ la) :
    twoAdicGen (m + la) ^ reverseBits k (m + la) = twoAdicGen la ^ reverseBits k la := by
  rw [reverseBits_low la m k hk, pow_mul, Nat.add_comm m la, Fast.twoAdicGen_pow la m (by omega)]

theorem sum_roots (ζ : L) (n : Nat) (hζ : IsPrimitiveRoot ζ n) (m k : Nat) (hm : m < n)
    (hk : k < n) :
    ∑ j ∈ Finset.range n, (ζ ^ m * ζ⁻¹ ^ k) ^ j = if m = k then (n : L) else 0 := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  split_ifs with h
  · subst h
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ h0)]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hw : ζ ^ m * ζ⁻¹ ^ k ≠ 1 := by
      intro e
      rw [inv_pow] at e
      exact h (hζ.pow_inj hm hk ((mul_inv_eq_one₀ (pow_ne_zero _ h0)).mp e))
    rw [geom_sum_eq hw, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m, Nat.mul_comm k, pow_mul,
      pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow, one_pow, mul_one, sub_self, zero_div]

theorem isPrimitiveRoot_emb (n : Nat) (hn : n ≤ 24) :
    IsPrimitiveRoot (emb (twoAdicGen n) : L) (2 ^ n) :=
  (isPrimitiveRoot_twoAdicGen n hn).map_of_injective
    (f := (algebraMap K L).comp (ringEquiv KoalaBear.fieldSize).toRingHom)
    ((algebraMap K L).injective.comp (RingEquiv.injective _))

theorem two_pow_ne_zero (n : Nat) : ((2 ^ n : Nat) : L) ≠ 0 := by
  have h : (2 : K) ≠ 0 := by decide
  rw [Nat.cast_pow, Nat.cast_ofNat, ← map_ofNat (algebraMap K L) 2]
  exact pow_ne_zero _ ((_root_.map_ne_zero _).mpr h)

/-- The inverse transform of the values of `p`, degree below `n = 2 ^ lf`, at the powers of the
generator of order `n` gives `p`'s coefficients. -/
theorem toSpec_idft (lf : Nat) (hlf : lf ≤ 24) (vs : Array EF) (p : L[X])
    (hp : p.degree < ((2 ^ lf : Nat) : WithBot Nat))
    (hv : ∀ j < 2 ^ lf, Challenge.toSpec (vs.getD j 0) = p.eval (emb (twoAdicGen lf) ^ j))
    (k : Nat) (hk : k < 2 ^ lf) : Challenge.toSpec ((idft lf vs).getD k 0) = p.coeff k := by
  have hζ := isPrimitiveRoot_emb (EF := EF) lf hlf
  set ζ : L := emb (twoAdicGen lf)
  have hN := natDegree_lt_of_degree hp (by positivity)
  unfold idft
  dsimp only
  rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hk, Challenge.toSpec_mul,
    toSpec_foldl_add, Challenge.toSpec_zero, zero_add, toSpec_ofBase]
  have hinv : emb ((((2 ^ lf : Nat) : F))⁻¹) = (((2 ^ lf : Nat) : L))⁻¹ := by
    rw [emb, toField_inv, toField_natCast, map_inv₀, map_natCast]
  rw [hinv]
  have hterm : ∀ j ∈ Finset.range (2 ^ lf), Challenge.toSpec (Ext.ofBase
      (powF (twoAdicGen lf)⁻¹ (j * k)) * vs.getD j 0) =
      ∑ m ∈ Finset.range (2 ^ lf), p.coeff m * (ζ ^ m * ζ⁻¹ ^ k) ^ j := by
    intro j hj
    rw [Challenge.toSpec_mul, toSpec_ofBase, hv j (Finset.mem_range.mp hj), Fast.powF_eq, emb_pow,
      emb, toField_inv, map_inv₀, eval_eq_sum_range' hN, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    show ζ⁻¹ ^ (j * k) * (p.coeff m * ζ ^ (j * m)) = p.coeff m * (ζ ^ (m * j) * ζ⁻¹ ^ (k * j))
    rw [Nat.mul_comm m j, Nat.mul_comm k j]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun m hm ↦ by
    rw [sum_roots ζ _ hζ m k (Finset.mem_range.mp hm) hk]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' _ _ (fun m ↦ p.coeff m * ((2 ^ lf : Nat) : L)),
    ite_eq_left (Finset.mem_range.mpr hk), mul_comm, mul_assoc,
    mul_inv_cancel₀ (two_pow_ne_zero lf),
    mul_one]

theorem toList_getD {α : Type} (a : Array α) (k : Nat) (d : α) :
    a.toList.getD k d = a.getD k d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

theorem toSpec_horner_list (l : List EF) (x : EF) :
    Challenge.toSpec (l.foldr (fun c acc ↦ acc * x + c) 0) =
      ∑ k ∈ Finset.range l.length, Challenge.toSpec (l.getD k 0) * Challenge.toSpec x ^ k := by
  induction l with
  | nil => rw [List.foldr_nil, Challenge.toSpec_zero, List.length_nil, Finset.sum_range_zero]
  | cons c l ih =>
    rw [List.foldr_cons, Challenge.toSpec_add, Challenge.toSpec_mul, ih, List.length_cons,
      Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ, mul_assoc]

/-- The final polynomial, the inverse transform of the low entries of a vector of degree below
`2 ^ lf` on the domain of order `2 ^ (lb + lf)`, evaluates by Horner's rule at entry `idx`'s point
to the entry. -/
theorem horner_idft (fa : Array EF) (lb lf M idx : Nat) (hfa : LowDegree (lb + lf) lf fa)
    (hM : lb + lf ≤ M) (hM24 : M ≤ 24) (hidx : idx < 2 ^ (lb + lf)) :
    (idft lf (Array.ofFn (n := 2 ^ lf) fun i ↦ fa.getD (reverseBits i lf) 0)).foldr
      (fun c acc ↦ acc * Ext.ofBase (powF (twoAdicGen M) (reverseBits idx M)) + c) 0 =
      fa.getD idx 0 := by
  obtain ⟨-, hL, p, hp, hpv⟩ := hfa
  have hN := natDegree_lt_of_degree hp (by positivity)
  apply Challenge.toSpec_injective
  rw [← Array.foldr_toList, toSpec_horner_list, Array.length_toList,
    show (idft lf _).size = 2 ^ lf from Array.size_ofFn, hpv idx hidx, eval_eq_sum_range' hN]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk := Finset.mem_range.mp hk
  rw [toList_getD, toSpec_idft lf (by omega) _ p hp (fun j hj ↦ ?_) k hk]
  · congr 1
    rw [toSpec_ofBase, Fast.powF_eq, emb_pow, ← emb_pow,
      show M = (M - (lb + lf)) + (lb + lf) by omega,
      twoAdicGen_pow_low (lb + lf) (M - (lb + lf)) idx (by omega) hidx]
    exact (emb_pow (EF := EF) _ _).symm ▸ rfl
  · have hr := reverseBits_lt j lf
    rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hj,
      hpv _ (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega))), ← emb_pow,
      twoAdicGen_pow_low lf lb _ hL hr, reverseBits_reverseBits hj, emb_pow]

end CompStark.Complete
