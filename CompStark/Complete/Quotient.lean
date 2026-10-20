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

variable {EF : Type} [Challenge EF]

local notation "F" => KoalaBear.Fast.Field
local notation "K" => KoalaBear.Field
local notation "E" => Challenge.Spec EF

/-! ### The example AIRs fit -/

/-- The expression operators are the constructors. -/
theorem Expr.mul_eq (a b : Expr) : a * b = .mul a b := rfl
theorem Expr.sub_eq (a b : Expr) : a - b = .sub a b := rfl
theorem Expr.add_eq (a b : Expr) : a + b = .add a b := rfl

/-- Powers of two are powers of two. -/
theorem isPowerOfTwo_two_pow : ∀ k, (2 ^ k).isPowerOfTwo
  | 0 => Nat.isPowerOfTwo_one
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo (isPowerOfTwo_two_pow k)

/-- Plonky3's chunk count for a largest degree `d + 1`, `d = 2 ^ k`. -/
theorem logQuotientChunks_of (A : Air) (k : Nat) (h : max A.maxDegree 2 - 1 = 2 ^ k) :
    A.logQuotientChunks = k := by
  rw [Air.logQuotientChunks]
  simp only [h]
  rw [Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k), Nat.log2_two_pow]

/-- The Fibonacci AIR fits its single chunk for every trace length. -/
theorem fibonacci_degreeFits (logN : Nat) : fibonacci.DegreeFits logN := by
  have hlc : fibonacci.logQuotientChunks = 0 := logQuotientChunks_of _ 0 (by decide)
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [fibonacci, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hlc, Nat.add_zero]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Expr.sub_eq, Expr.add_eq, Expr.degBound] <;> omega

/-- The cube AIR's degree-3 transition fits its two chunks for every trace length. -/
theorem cube_degreeFits (logN : Nat) : cube.DegreeFits logN := by
  have hlc : cube.logQuotientChunks = 1 := logQuotientChunks_of _ 1 (by decide)
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [cube, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hlc, Nat.pow_succ]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Expr.sub_eq, Expr.add_eq, Expr.degBound] <;> omega

/-- The largest degree of a nonempty list of degree-3 constraints. -/
theorem foldl_max_degree (a : Nat) : ∀ l : List Expr, (∀ c ∈ l, c.degree = 3) → l ≠ [] →
    l.foldl (fun m c ↦ max m c.degree) a = max a 3
  | [], _, h => absurd rfl h
  | [c], hl, _ => by rw [List.foldl_cons, List.foldl_nil, hl c List.mem_cons_self]
  | c :: d :: l, hl, _ => by
    rw [List.foldl_cons, foldl_max_degree _ (d :: l) (fun e he ↦ hl e (List.mem_cons_of_mem _ he))
      (List.cons_ne_nil _ _), hl c List.mem_cons_self, Nat.max_assoc, Nat.max_self]

/-- The wide AIR's quotient has two chunks. -/
theorem wide_logQuotientChunks (w : Nat) (hw : 0 < w) : (wide w).logQuotientChunks = 1 := by
  have hmax : (wide w).maxDegree = 3 := by
    rw [Air.maxDegree, foldl_max_degree 0 _ (fun e he ↦ ?_)
      (by simp only [wide, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega)]
    · rfl
    · simp only [wide, List.mem_map, List.mem_range] at he
      obtain ⟨i, -, rfl⟩ := he
      rfl
  exact logQuotientChunks_of _ 1 (by rw [hmax]; rfl)

/-- The wide AIR fits its two chunks for every width and trace length. -/
theorem wide_degreeFits (w logN : Nat) : (wide w).DegreeFits logN := by
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [wide, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  rw [wide_logQuotientChunks w (by omega), Nat.pow_succ]
  simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
  omega

/-! ### Constraints under ring maps -/

/-- Evaluation commutes with a map that respects `+`, `-` and `*`, for expressions reading
columns below `w` of environments that agree there. -/
theorem Expr.eval_hom {R S : Type*} [Add R] [Sub R] [Mul R] [Add S] [Sub S] [Mul S] (f : R → S)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsub : ∀ a b, f (a - b) = f a - f b)
    (hmul : ∀ a b, f (a * b) = f a * f b) (w : Nat) (r : Expr.Env R) (s : Expr.Env S)
    (hcur : ∀ c < w, f (r.cur c) = s.cur c) (hnext : ∀ c < w, f (r.next c) = s.next c)
    (hpub : ∀ j, f (r.pub j) = s.pub j) (hconst : ∀ c, f (r.const c) = s.const c)
    (h1 : f r.isFirstRow = s.isFirstRow) (h2 : f r.isLastRow = s.isLastRow)
    (h3 : f r.isTransition = s.isTransition) :
    ∀ e : Expr, e.colsBelow w = true → f (e.eval r) = e.eval s
  | .cur c, h => hcur c (of_decide_eq_true h)
  | .next c, h => hnext c (of_decide_eq_true h)
  | .pub j, _ => hpub j
  | .const c, _ => hconst c
  | .isFirstRow, _ => h1
  | .isLastRow, _ => h2
  | .isTransition, _ => h3
  | .add a b, h => by
    simp only [Expr.colsBelow, Bool.and_eq_true] at h
    simp only [Expr.eval]
    rw [hadd, Expr.eval_hom f hadd hsub hmul w r s hcur hnext hpub hconst h1 h2 h3 a h.1,
      Expr.eval_hom f hadd hsub hmul w r s hcur hnext hpub hconst h1 h2 h3 b h.2]
  | .sub a b, h => by
    simp only [Expr.colsBelow, Bool.and_eq_true] at h
    simp only [Expr.eval]
    rw [hsub, Expr.eval_hom f hadd hsub hmul w r s hcur hnext hpub hconst h1 h2 h3 a h.1,
      Expr.eval_hom f hadd hsub hmul w r s hcur hnext hpub hconst h1 h2 h3 b h.2]
  | .mul a b, h => by
    simp only [Expr.colsBelow, Bool.and_eq_true] at h
    simp only [Expr.eval]
    rw [hmul, Expr.eval_hom f hadd hsub hmul w r s hcur hnext hpub hconst h1 h2 h3 a h.1,
      Expr.eval_hom f hadd hsub hmul w r s hcur hnext hpub hconst h1 h2 h3 b h.2]

/-- The degree of a constraint over polynomials is at most `degBound`. -/
theorem Expr.natDegree_eval (n : Nat) (env : Expr.Env K[X])
    (hcur : ∀ c, (env.cur c).natDegree ≤ n - 1) (hnext : ∀ c, (env.next c).natDegree ≤ n - 1)
    (hpub : ∀ j, (env.pub j).natDegree = 0) (hconst : ∀ c, (env.const c).natDegree = 0)
    (h1 : env.isFirstRow.natDegree ≤ n - 1) (h2 : env.isLastRow.natDegree ≤ n - 1)
    (h3 : env.isTransition.natDegree ≤ 1) : ∀ e : Expr, (e.eval env).natDegree ≤ e.degBound n
  | .cur c => hcur c
  | .next c => hnext c
  | .pub j => (hpub j).le
  | .const c => (hconst c).le
  | .isFirstRow => h1
  | .isLastRow => h2
  | .isTransition => h3
  | .add a b => (natDegree_add_le _ _).trans (max_le_max
      (Expr.natDegree_eval n env hcur hnext hpub hconst h1 h2 h3 a)
      (Expr.natDegree_eval n env hcur hnext hpub hconst h1 h2 h3 b))
  | .sub a b => (natDegree_sub_le _ _).trans (max_le_max
      (Expr.natDegree_eval n env hcur hnext hpub hconst h1 h2 h3 a)
      (Expr.natDegree_eval n env hcur hnext hpub hconst h1 h2 h3 b))
  | .mul a b => natDegree_mul_le.trans (Nat.add_le_add
      (Expr.natDegree_eval n env hcur hnext hpub hconst h1 h2 h3 a)
      (Expr.natDegree_eval n env hcur hnext hpub hconst h1 h2 h3 b))

/-! ### The constraints as polynomials -/

/-- `Z_H(X) / (X - 1) = 1 + X + … + X^(n-1)`. -/
noncomputable def firstSel (n : Nat) : K[X] := ∑ m ∈ Finset.range n, X ^ m

/-- `Z_H(X) / (X - ω⁻¹) = ω · (Z_H / (X - 1))(ω X)`. -/
noncomputable def lastSel (n : Nat) (w : K) : K[X] := C w * (firstSel n).comp (C w * X)

/-- The constraints' environment over the spec polynomials: the trace's column polynomials `T`,
shifted by `ω` for the next row, and the selectors. -/
noncomputable def polyEnv (n : Nat) (w : K) (T : Nat → K[X]) (pis : List F) :
    Expr.Env K[X] where
  cur := T
  next j := (T j).comp (C w * X)
  pub j := C (FastField.toField (pis.getD j 0))
  const c := C (FastField.toField c)
  isFirstRow := firstSel n
  isLastRow := lastSel n w
  isTransition := X - C w⁻¹

/-- `(X - 1) · Z_H / (X - 1) = Z_H`, at any point. -/
theorem aeval_firstSel {S : Type*} [CommRing S] [Algebra K S] (n : Nat) (y : S) :
    aeval y (firstSel n) * (y - 1) = y ^ n - 1 := by
  rw [firstSel, map_sum]
  simp only [map_pow, aeval_X]
  exact geom_sum_mul y n

/-- `(X - ω⁻¹) · Z_H / (X - ω⁻¹) = Z_H`, at any point, for `ωⁿ = 1`. -/
theorem aeval_lastSel {S : Type*} [CommRing S] [Algebra K S] (n : Nat) (w : K) (hw : w ≠ 0)
    (hwn : w ^ n = 1) (y : S) :
    aeval y (lastSel n w) * (y - algebraMap K S w⁻¹) = y ^ n - 1 := by
  have h := aeval_firstSel n (algebraMap K S w * y)
  rw [lastSel, map_mul, aeval_comp, map_mul, aeval_C, aeval_X]
  have hw' : algebraMap K S w * algebraMap K S w⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hw, map_one]
  calc algebraMap K S w * aeval (algebraMap K S w * y) (firstSel n) *
        (y - algebraMap K S w⁻¹)
      = aeval (algebraMap K S w * y) (firstSel n) * (algebraMap K S w * y - 1) := by
        rw [← hw']; ring
    _ = y ^ n - 1 := by rw [h, mul_pow, ← map_pow, hwn, map_one, one_mul]

/-- The first-row selector has degree below `n`. -/
theorem natDegree_firstSel (n : Nat) : (firstSel n).natDegree ≤ n - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun m hm ↦
    (natDegree_X_pow_le m).trans (by have := Finset.mem_range.mp hm; omega)

/-- Composing with `w X` keeps the degree bound. -/
theorem natDegree_comp_shift (p : K[X]) (w : K) : (p.comp (C w * X)).natDegree ≤ p.natDegree :=
  natDegree_comp_le.trans (by
    have := (natDegree_C_mul_le w (X : K[X])).trans natDegree_X_le
    calc p.natDegree * (C w * X).natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ this
      _ = p.natDegree := Nat.mul_one _)

/-- The last-row selector has degree below `n`. -/
theorem natDegree_lastSel (n : Nat) (w : K) : (lastSel n w).natDegree ≤ n - 1 :=
  (natDegree_C_mul_le _ _).trans ((natDegree_comp_shift _ _).trans (natDegree_firstSel n))

/-- The constraint `c` over the trace polynomials. -/
noncomputable def constraintPoly (n : Nat) (w : K) (T : Nat → K[X]) (pis : List F) (c : Expr) :
    K[X] :=
  c.eval (polyEnv n w T pis)

/-- A constraint polynomial has degree at most `degBound`. -/
theorem natDegree_constraintPoly (n : Nat) (w : K) (T : Nat → K[X]) (pis : List F) (c : Expr)
    (hT : ∀ j, (T j).natDegree ≤ n - 1) :
    (constraintPoly n w T pis c).natDegree ≤ c.degBound n :=
  Expr.natDegree_eval n (polyEnv n w T pis) hT (fun j ↦ (natDegree_comp_shift _ _).trans (hT j))
    (fun _ ↦ natDegree_C _) (fun _ ↦ natDegree_C _) (natDegree_firstSel n)
    (natDegree_lastSel n w) (natDegree_sub_le_of_le natDegree_X_le (natDegree_C _).le) c

/-! ### Two-adic roots of unity in the spec field -/

/-- `ω` of order `2 ^ k`, in the spec field. -/
noncomputable abbrev tw (k : Nat) : K := FastField.toField (twoAdicGen k)

/-- `ω ^ 2 ^ k = 1`. -/
theorem tw_pow (k : Nat) (hk : k ≤ 24) : tw k ^ 2 ^ k = 1 :=
  (isPrimitiveRoot_twoAdicGen k hk).pow_eq_one

/-- `ω ≠ 0`. -/
theorem tw_ne_zero (k : Nat) (hk : k ≤ 24) : tw k ≠ 0 :=
  (isPrimitiveRoot_twoAdicGen k hk).ne_zero (Nat.two_pow_pos k).ne'

/-- `ω_{n+b} ^ 2 ^ b = ω_n`. -/
theorem tw_pow_tw (n b : Nat) (h : n + b ≤ 24) : tw (n + b) ^ 2 ^ b = tw n := by
  rw [tw, tw, ← toField_npow, Fast.twoAdicGen_pow n b h]

/-- `x ^ 2 ^ k` by squaring. -/
def sqIter (x : K) : Nat → K
  | 0 => x
  | k + 1 => sqIter (x * x) k

/-- `sqIter` squares `k` times. -/
theorem sqIter_eq (x : K) : ∀ k, sqIter x k = x ^ 2 ^ k
  | 0 => (pow_one x).symm
  | k + 1 => by rw [sqIter, sqIter_eq _ k, ← sq, ← pow_mul, pow_succ']

/-- `g = 3` is not in the two-adic subgroup. -/
theorem gen_pow_ne_one : FastField.toField gen ^ 2 ^ 24 ≠ 1 := by
  rw [show FastField.toField gen = 3 by decide, ← sqIter_eq]
  decide

/-- A `2 ^ k`-th root of unity is a `2 ^ 24`-th one. -/
theorem root_pow_24 (y : K) (k : Nat) (hk : k ≤ 24) (hy : y ^ 2 ^ k = 1) : y ^ 2 ^ 24 = 1 := by
  rw [show 2 ^ 24 = 2 ^ k * 2 ^ (24 - k) by rw [← Nat.pow_add]; congr 1; omega, pow_mul, hy,
    one_pow]

/-- No point `g ωᵐ` of a coset of a two-adic subgroup is a two-adic root of unity. -/
theorem genPoint_pow_ne (k m : Nat) (hk : k ≤ 24) (j : Nat) (hj : j ≤ 24) :
    (FastField.toField gen * tw k ^ m) ^ 2 ^ j ≠ 1 := fun h ↦ by
  have := root_pow_24 _ j hj h
  rw [mul_pow, ← pow_mul, Nat.mul_comm m, pow_mul, root_pow_24 _ k hk (tw_pow k hk), one_pow,
    mul_one] at this
  exact gen_pow_ne_one this

/-- No point `g ωᵐ` is a two-adic root of unity. -/
theorem genPoint_ne (k m : Nat) (hk : k ≤ 24) (y : K) (j : Nat) (hj : j ≤ 24)
    (hy : y ^ 2 ^ j = 1) : FastField.toField gen * tw k ^ m ≠ y := fun h ↦
  genPoint_pow_ne k m hk j hj (by rw [h, hy])

/-! ### The constraints vanish on the trace domain -/

theorem eval_firstSel_mul (n : Nat) (y : K) : (firstSel n).eval y * (y - 1) = y ^ n - 1 := by
  rw [firstSel, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact geom_sum_mul y n

/-- The first-row selector is `n` at `1`. -/
theorem eval_firstSel_one (n : Nat) : (firstSel n).eval 1 = n := by
  simp only [firstSel, eval_finsetSum, eval_pow, eval_X, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]

/-- The first-row selector on `⟨ω⟩`. -/
theorem eval_firstSel_root (logN i : Nat) (h : logN ≤ 24) (hi : i < 2 ^ logN) :
    (firstSel (2 ^ logN)).eval (tw logN ^ i) = if i = 0 then ((2 ^ logN : Nat) : K) else 0 := by
  split
  · rename_i h0
    rw [h0, pow_zero, eval_firstSel_one]
  · rename_i h0
    have hp := isPrimitiveRoot_twoAdicGen logN h
    have h1 : tw logN ^ i - 1 ≠ 0 :=
      sub_ne_zero.mpr (hp.pow_ne_one_of_pos_of_lt h0 hi)
    have := eval_firstSel_mul (2 ^ logN) (tw logN ^ i)
    rw [← pow_mul, Nat.mul_comm, pow_mul, hp.pow_eq_one, one_pow, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right h1

/-- The trace polynomials `T` take the trace's values on `⟨ω⟩`. -/
def TraceOn (logN w : Nat) (trace : Array F) (T : Nat → K[X]) : Prop :=
  ∀ j < w, ∀ i < 2 ^ logN, (T j).eval (tw logN ^ i) = FastField.toField (trace.getD (i * w + j) 0)

/-- The constraints over the trace polynomials take the constraints' values on the trace's rows. -/
theorem eval_constraintPoly_root (A : Air) (logN : Nat) (h : logN ≤ 24) (trace : Array F)
    (pis : List F) (T : Nat → K[X]) (hT : TraceOn logN A.width trace T) (c : Expr)
    (hc : c.colsBelow A.width = true) (i : Nat) (hi : i < 2 ^ logN) :
    (constraintPoly (2 ^ logN) (tw logN) T pis c).eval (tw logN ^ i) =
      FastField.toField (c.eval (A.traceRow logN trace pis i)) := by
  have hp := isPrimitiveRoot_twoAdicGen logN h
  have hsucc : tw logN ^ (i + 1) = tw logN ^ ((i + 1) % 2 ^ logN) := by
    conv_lhs => rw [← Nat.mod_add_div (i + 1) (2 ^ logN)]
    rw [pow_add, pow_mul, hp.pow_eq_one, one_pow, mul_one]
  let envK : Expr.Env K := {
    cur := fun j ↦ FastField.toField ((A.traceRow logN trace pis i).cur j)
    next := fun j ↦ FastField.toField ((A.traceRow logN trace pis i).next j)
    pub := fun j ↦ FastField.toField ((A.traceRow logN trace pis i).pub j)
    const := FastField.toField
    isFirstRow := FastField.toField (A.traceRow logN trace pis i).isFirstRow
    isLastRow := FastField.toField (A.traceRow logN trace pis i).isLastRow
    isTransition := FastField.toField (A.traceRow logN trace pis i).isTransition }
  have hb := Expr.eval_hom FastField.toField toField_add toField_sub toField_mul A.width
    (A.traceRow logN trace pis i) envK (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) rfl rfl rfl c hc
  rw [hb, constraintPoly]
  refine Expr.eval_hom (eval (tw logN ^ i)) (fun _ _ ↦ eval_add) (fun a b ↦ eval_sub a b _)
    (fun _ _ ↦ eval_mul) A.width _ envK (fun j hj ↦ hT j hj i hi) (fun j hj ↦ ?_)
    (fun _ ↦ eval_C) (fun _ ↦ eval_C) ?_ ?_ ?_ c hc
  · have hm : (i + 1) % 2 ^ logN < 2 ^ logN := Nat.mod_lt _ (Nat.two_pow_pos _)
    change ((T j).comp (C (tw logN) * X)).eval (tw logN ^ i) =
      FastField.toField (trace.getD ((i + 1) % 2 ^ logN * A.width + j) 0)
    rw [eval_comp, eval_mul, eval_C, eval_X, ← hT j hj _ hm, ← pow_succ', hsucc]
  · change (firstSel (2 ^ logN)).eval (tw logN ^ i) =
      FastField.toField (if i = 0 then ((2 ^ logN : Nat) : F) else 0)
    rw [eval_firstSel_root logN i h hi, apply_ite FastField.toField, toField_natCast,
      toField_zero]
  · change (lastSel (2 ^ logN) (tw logN)).eval (tw logN ^ i) = FastField.toField
      (if i + 1 = 2 ^ logN then ((2 ^ logN : Nat) : F) * twoAdicGen logN else 0)
    have hm : (i + 1) % 2 ^ logN < 2 ^ logN := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [lastSel, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, ← pow_succ', hsucc,
      eval_firstSel_root logN _ h hm, apply_ite FastField.toField, toField_mul, toField_natCast,
      toField_zero]
    by_cases hl : i + 1 = 2 ^ logN
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl),
        ite_eq_left_of_eq_true _ _ (eq_true (by rw [hl, Nat.mod_self])), mul_comm]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl),
        ite_eq_right_of_eq_false _ _ (eq_false (by rw [Nat.mod_eq_of_lt (by omega)]; omega)),
        mul_zero]
  · change (X - C (tw logN)⁻¹).eval (tw logN ^ i) =
      FastField.toField (twoAdicGen logN ^ i - (twoAdicGen logN)⁻¹)
    rw [eval_sub, eval_X, eval_C, toField_sub, toField_npow, toField_inv]

/-- The trace domain's vanishing polynomial `Z_H = Xⁿ - 1`. -/
noncomputable abbrev zH (n : Nat) : K[X] := X ^ n - C 1

/-- A constraint that vanishes on the trace domain, divided by `Z_H`. -/
noncomputable def quotientPoly (logN : Nat) (T : Nat → K[X]) (pis : List F) (c : Expr) : K[X] :=
  constraintPoly (2 ^ logN) (tw logN) T pis c /ₘ zH (2 ^ logN)

/-- `Z_H` is monic. -/
theorem zH_monic (logN : Nat) : (zH (2 ^ logN)).Monic :=
  monic_X_pow_sub_C 1 (Nat.two_pow_pos logN).ne'

/-- A polynomial vanishing on `⟨ω⟩` is `Z_H` times its quotient. -/
theorem eq_zH_mul (logN : Nat) (h : logN ≤ 24) (p : K[X])
    (hp : ∀ i < 2 ^ logN, p.eval (tw logN ^ i) = 0) : p = zH (2 ^ logN) * (p /ₘ zH (2 ^ logN)) := by
  have hr : p %ₘ zH (2 ^ logN) = 0 := by
    have hpr := isPrimitiveRoot_twoAdicGen logN h
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.range (2 ^ logN))
      (v := fun i ↦ tw logN ^ i) (fun i hi j hj hij ↦ ?_) ?_ (fun i hi ↦ ?_)
    · exact hpr.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    · rw [Finset.card_range]
      have := degree_modByMonic_lt p (zH_monic logN)
      rwa [degree_X_pow_sub_C (Nat.two_pow_pos logN)] at this
    · have e := congrArg (eval (tw logN ^ i)) (modByMonic_add_div p (zH (2 ^ logN)))
      rw [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, ← pow_mul, Nat.mul_comm,
        pow_mul, hpr.pow_eq_one, one_pow, sub_self, zero_mul, add_zero,
        hp i (Finset.mem_range.mp hi)] at e
      exact e
  have := modByMonic_add_div p (zH (2 ^ logN))
  rw [hr, zero_add] at this
  exact this.symm

/-- The trace polynomials have degree below `n`. -/
def TraceDeg (logN : Nat) (T : Nat → K[X]) : Prop := ∀ j, (T j).natDegree ≤ 2 ^ logN - 1

/-- A satisfied constraint is `Z_H` times its quotient. -/
theorem constraintPoly_eq (A : Air) (logN : Nat) (h : logN ≤ 24) (trace : Array F)
    (pis : List F) (T : Nat → K[X]) (hT : TraceOn logN A.width trace T)
    (hsat : A.ConstraintsVanish logN trace pis) (hcols : A.ColsInWidth) (c : Expr)
    (hc : c ∈ A.constraints) :
    constraintPoly (2 ^ logN) (tw logN) T pis c = zH (2 ^ logN) * quotientPoly logN T pis c :=
  eq_zH_mul logN h _ fun i hi ↦ by
    rw [eval_constraintPoly_root A logN h trace pis T hT c (hcols c hc) i hi, hsat c hc i hi,
      toField_zero]

/-- A constraint's quotient has degree below `k n`. -/
theorem natDegree_quotientPoly (A : Air) (logN : Nat) (pis : List F) (T : Nat → K[X])
    (hTd : TraceDeg logN T) (hdeg : A.DegreeFits logN) (c : Expr) (hc : c ∈ A.constraints) :
    (quotientPoly logN T pis c).natDegree < 2 ^ (logN + A.logQuotientChunks) := by
  rw [quotientPoly, natDegree_divByMonic _ (zH_monic logN), natDegree_X_pow_sub_C]
  have h1 := natDegree_constraintPoly (2 ^ logN) (tw logN) T pis c hTd
  have h2 := hdeg c hc
  have h3 := Nat.two_pow_pos (logN + A.logQuotientChunks)
  omega

/-! ### Horner's rule -/

/-- `∑ₖ lₖ aᴷ⁻¹⁻ᵏ` by Horner's rule, `K` the length of `l`. -/
def horner {R : Type*} [Add R] [Mul R] [Zero R] (l : List R) (a : R) : R :=
  l.foldl (fun acc v ↦ acc * a + v) 0

/-- Horner's rule from an accumulator. -/
theorem foldl_horner {R : Type*} [CommRing R] (a : R) :
    ∀ (l : List R) (x : R), l.foldl (fun acc v ↦ acc * a + v) x = x * a ^ l.length + horner l a
  | [], x => by rw [List.foldl_nil, List.length_nil, pow_zero, mul_one, horner, List.foldl_nil,
      add_zero]
  | v :: l, x => by
    have h1 := foldl_horner a l (x * a + v)
    have h2 := foldl_horner a l (0 * a + v)
    simp only [horner, List.foldl_cons, List.length_cons] at h1 h2 ⊢
    rw [h1, h2, pow_succ]
    ring

/-- Ring maps commute with Horner's rule. -/
theorem horner_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : List R) (a : R) :
    f (horner l a) = horner (l.map f) (f a) := by
  suffices h : ∀ (l : List R) (x : R), f (l.foldl (fun acc v ↦ acc * a + v) x) =
      (l.map f).foldl (fun acc v ↦ acc * f a + v) (f x) by
    rw [horner, horner, h, map_zero]
  intro l
  induction l with
  | nil => intro x; rfl
  | cons v l ih => intro x; rw [List.foldl_cons, ih, map_add, map_mul]; rfl

/-- Horner's rule is linear: scaling every term scales the result. -/
theorem horner_mul {R : Type*} [CommRing R] (l : List R) (a s : R) :
    horner (l.map (· * s)) a = horner l a * s := by
  suffices h : ∀ (l : List R) (x : R), (l.map (· * s)).foldl (fun acc v ↦ acc * a + v) (x * s) =
      l.foldl (fun acc v ↦ acc * a + v) x * s by
    have := h l 0
    rwa [zero_mul] at this
  intro l
  induction l with
  | nil => intro x; rfl
  | cons v l ih =>
    intro x
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    ring

/-- Horner's rule is the sum of the terms weighted by descending powers. -/
theorem horner_eq_sum {R : Type*} [CommRing R] (a : R) : ∀ l : List R,
    horner l a = ((l.zip ((List.range l.length).map fun k ↦ a ^ (l.length - 1 - k))).map
      fun p ↦ p.1 * p.2).sum
  | [] => rfl
  | v :: l => by
    rw [horner, List.foldl_cons, foldl_horner, horner_eq_sum a l, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
      List.map_map]
    congr 2
    · ring_nf
    · have : (fun k ↦ a ^ (l.length + 1 - 1 - k)) ∘ Nat.succ =
          fun k ↦ a ^ (l.length - 1 - k) := by
        funext k
        simp only [Function.comp_apply]
        congr 1
        omega
      rw [this]

/-- Horner's rule in `C a` keeps polynomials below a degree. -/
theorem natDegree_horner {R : Type*} [CommRing R] (N : Nat) (a : R) :
    ∀ (l : List R[X]) (x : R[X]), x.natDegree < N → (∀ p ∈ l, p.natDegree < N) →
      (l.foldl (fun acc v ↦ acc * C a + v) x).natDegree < N
  | [], x, hx, _ => hx
  | v :: l, x, hx, hl => by
    rw [List.foldl_cons]
    refine natDegree_horner N a l _ ?_ (fun p hp ↦ hl p (List.mem_cons_of_mem _ hp))
    refine (natDegree_add_le _ _).trans_lt (max_lt ?_ (hl v List.mem_cons_self))
    exact (natDegree_mul_C_le _ _).trans_lt hx

/-! ### The folded quotient -/

/-- The quotient of the constraints folded by `α`: `∑_c α^(K-1-c) Q_c` over the extension. -/
noncomputable def qFold (A : Air) (logN : Nat) (T : Nat → K[X]) (pis : List F) (a : E) : E[X] :=
  horner (A.constraints.map fun c ↦ (quotientPoly logN T pis c).map (algebraMap K E)) (C a)

/-- The folded quotient has degree below `k n`. -/
theorem natDegree_qFold (A : Air) (logN : Nat) (pis : List F) (T : Nat → K[X])
    (hTd : TraceDeg logN T) (hdeg : A.DegreeFits logN) (a : E) :
    (qFold A logN T pis a).natDegree < 2 ^ (logN + A.logQuotientChunks) := by
  refine natDegree_horner _ a _ 0 (by rw [natDegree_zero]; exact Nat.two_pow_pos _)
    (fun p hp ↦ ?_)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact natDegree_map_le.trans_lt (natDegree_quotientPoly A logN pis T hTd hdeg c hc)

/-- The folded quotient at a point is Horner's rule over the quotients there. -/
theorem eval_qFold (A : Air) (logN : Nat) (T : Nat → K[X]) (pis : List F) (a y : E) :
    (qFold A logN T pis a).eval y =
      horner (A.constraints.map fun c ↦ aeval y (quotientPoly logN T pis c)) a := by
  rw [qFold, ← coe_evalRingHom, horner_map, coe_evalRingHom, eval_C, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ ↦ ?_
  simp only [Function.comp_apply, eval_map_algebraMap]

/-! ### The prover's quotient values -/

section QuotientValues

/-- `Ext.pow` is the power in the spec field. -/
theorem toSpec_extPow (x : EF) (n : Nat) :
    Challenge.toSpec (Ext.pow x n) = Challenge.toSpec x ^ n :=
  Ext.toSpec_pow x n

/-- `Ext.powTwo` is `x ^ 2 ^ k` in the spec field. -/
theorem toSpec_extPowTwo (x : EF) (k : Nat) :
    Challenge.toSpec (Ext.powTwo x k) = Challenge.toSpec x ^ 2 ^ k :=
  Ext.toSpec_powTwo x k

/-- An element of given coordinates in the spec field. -/
theorem toSpec_ofCoeffs_sum (l : List F) : Challenge.toSpec (Challenge.ofCoeffs l : EF) =
    ∑ e ∈ Finset.range (Challenge.d EF),
      CompPoly.Extension.Ext.gen ^ e * algebraMap K E (FastField.toField (l.getD e 0)) := by
  rw [Challenge.toSpec_eq_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [Challenge.toField_coeffs, Challenge.toSpec_ofCoeffs,
    CompPoly.Extension.Ext.coeffNat_of_lt _ (Finset.mem_range.mp he),
    CompPoly.Extension.Ext.coeff_ofFn]

/-- Entry `e < n` of a tabulated list. -/
theorem getD_map_range {α : Type} (f : Nat → α) (n e : Nat) (d : α) (he : e < n) :
    ((List.range n).map f).getD e d = f e := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact he),
    List.getElem_map, List.getElem_range]

/-- The accumulated weighted constraints of a row as a sum in the spec field. -/
theorem toSpec_rowAcc (ev : Expr → F) : ∀ (cw : List (Expr × List F)) (x : Nat → F),
    Challenge.toSpec (Challenge.ofCoeffs
      ((List.range (Challenge.d EF)).map fun j ↦ rowAcc cw ev j (x j)) : EF) =
      Challenge.toSpec (Challenge.ofCoeffs ((List.range (Challenge.d EF)).map x) : EF) +
        (cw.map fun a ↦ algebraMap K E (FastField.toField (ev a.1)) *
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
    rw [getD_map_range _ _ _ _ he, getD_map_range _ _ _ _ he, toField_add, toField_mul, map_add,
      map_mul]
    ring

/-- The weighted constraints' sum is Horner's rule in `α`. -/
theorem weighted_sum (A : Air) (alpha : EF) (g : Expr → E) :
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
theorem toSpec_quotientRow (A : Air) (pis : List F) (d l : Nat) (tq : Mat) (alpha : EF)
    (r : Nat) : Challenge.toSpec (quotientRow A pis d l tq alpha r) =
      algebraMap K E (FastField.toField ((batchInv (qZh d l)).getD (r % 2 ^ l) 0)) *
        horner (A.constraints.map fun c ↦ algebraMap K E (FastField.toField (c.eval
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
    rw [getD_map_range _ _ _ _ (Finset.mem_range.mp he), toField_zero, map_zero, mul_zero]
  rw [h0, zero_add]
  exact weighted_sum A alpha fun c ↦ algebraMap K E (FastField.toField (c.eval
    (rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r)))

/-- A batch inversion of nonzero elements, entry by entry. -/
theorem toField_batchInv (xs : Array F) (hx : ∀ x ∈ xs, FastField.toField x ≠ 0) (i : Nat)
    (hi : i < xs.size) :
    FastField.toField ((batchInv xs).getD i 0) = (FastField.toField (xs.getD i 0))⁻¹ := by
  rw [batchInv_eq FastField.toField toField_injective toField_mul toField_inv toField_one xs hx,
    Fast.getD_map_lt _ _ _ hi _ 0, toField_inv]

/-- The quotient domain's points. -/
theorem toField_qPoints (d l m : Nat) (hm : m < 2 ^ (d + l)) :
    FastField.toField ((qPoints d l).getD m 0) = FastField.toField gen * tw (d + l) ^ m := by
  rw [qPoints, cosetPoints_eq, getD_lt _ _ (by rw [Array.size_ofFn]; exact hm),
    Array.getElem_ofFn, toField_mul, toField_npow]

/-- `powF` is the power in the spec field. -/
theorem toField_powF (x : F) (n : Nat) :
    FastField.toField (powF x n) = FastField.toField x ^ n := by
  rw [Fast.powF_eq, toField_npow]

/-- `Z_H` on the quotient domain has period `k`. -/
theorem toField_qZh (d l r : Nat) (h : d + l ≤ 24) :
    FastField.toField ((qZh d l).getD (r % 2 ^ l) 0) =
      (FastField.toField gen * tw (d + l) ^ r) ^ 2 ^ d - 1 := by
  have hk : r % 2 ^ l < 2 ^ l := Nat.mod_lt _ (Nat.two_pow_pos l)
  rw [qZh, getD_lt _ _ (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn, toField_sub,
    toField_powF, toField_qPoints d l _ (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega)
      (by omega))), toField_one]
  congr 1
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  congr 1
  conv_rhs => rw [← Nat.mod_add_div r (2 ^ l)]
  rw [Nat.add_mul, pow_add, Nat.mul_comm (2 ^ l), Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm l,
    pow_mul' (tw (d + l)) (r / 2 ^ l), tw_pow (d + l) h, one_pow, mul_one]

/-- `Z_H` has no zero on the quotient domain. -/
theorem qZh_ne (d l : Nat) (h : d + l ≤ 24) : ∀ x ∈ qZh d l, FastField.toField x ≠ 0 := by
  intro x hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hx
  have hi : i.val < 2 ^ (d + l) :=
    lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  rw [toField_sub, toField_powF, toField_qPoints d l _ hi, toField_one, sub_ne_zero]
  exact genPoint_pow_ne _ _ h d (by omega)

/-- No quotient point is a two-adic root of unity `y`. -/
theorem points_sub_ne (d l : Nat) (h : d + l ≤ 24) (y : F) (j : Nat) (hj : j ≤ 24)
    (hy : FastField.toField y ^ 2 ^ j = 1) :
    ∀ x ∈ (qPoints d l).map (· - y), FastField.toField x ≠ 0 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hx
  rw [qPoints, cosetPoints_eq] at hp
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hp
  rw [toField_sub, toField_mul, toField_npow, sub_ne_zero]
  exact genPoint_ne _ _ h _ j hj hy

/-- The quotient domain's point `x_r = g ω_qʳ`. -/
noncomputable abbrev qpt (q r : Nat) : K := FastField.toField gen * tw q ^ r

/-- The prover's inverse of `Z_H` at a quotient point. -/
theorem toField_invZh (d l r : Nat) (h : d + l ≤ 24) :
    FastField.toField ((batchInv (qZh d l)).getD (r % 2 ^ l) 0) =
      (qpt (d + l) r ^ 2 ^ d - 1)⁻¹ := by
  have hk : r % 2 ^ l < (qZh d l).size := by
    rw [qZh, Array.size_ofFn]
    exact Nat.mod_lt _ (Nat.two_pow_pos l)
  rw [toField_batchInv _ (qZh_ne d l h) _ hk, toField_qZh d l r h]

/-- The prover's first-row selector at a quotient point is the polynomial's. -/
theorem toField_qFirst (d l r : Nat) (h : d + l ≤ 24) (hr : r < 2 ^ (d + l)) :
    FastField.toField ((qFirst d l).getD r 0) = (firstSel (2 ^ d)).eval (qpt (d + l) r) := by
  have hs : r < ((qPoints d l).map (· - 1)).size := by
    rw [Array.size_map, qPoints, size_cosetPoints]; exact hr
  rw [qFirst, getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn, toField_mul,
    toField_qZh d l r h, toField_batchInv _ (points_sub_ne d l h 1 0 (by omega)
      (by rw [toField_one, one_pow])) _ hs, Fast.getD_map_lt _ _ _ (by
        rw [Array.size_map] at hs; exact hs) _ 0, toField_sub, toField_qPoints d l r hr,
    toField_one]
  have hne : qpt (d + l) r - 1 ≠ 0 :=
    sub_ne_zero.mpr (genPoint_ne _ _ h 1 0 (by omega) (by rw [one_pow]))
  rw [← eval_firstSel_mul (2 ^ d), mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- The prover's last-row selector at a quotient point is the polynomial's. -/
theorem toField_qLast (d l r : Nat) (h : d + l ≤ 24) (hr : r < 2 ^ (d + l)) :
    FastField.toField ((qLast d l).getD r 0) =
      (lastSel (2 ^ d) (tw d)).eval (qpt (d + l) r) := by
  have hs : r < ((qPoints d l).map (· - (twoAdicGen d)⁻¹)).size := by
    rw [Array.size_map, qPoints, size_cosetPoints]; exact hr
  have hy : FastField.toField (twoAdicGen d)⁻¹ ^ 2 ^ d = 1 := by
    rw [toField_inv, inv_pow, tw_pow d (by omega), inv_one]
  rw [qLast, getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn, toField_mul,
    toField_qZh d l r h, toField_batchInv _ (points_sub_ne d l h _ d (by omega) hy) _ hs,
    Fast.getD_map_lt _ _ _ (by rw [Array.size_map] at hs; exact hs) _ 0, toField_sub,
    toField_qPoints d l r hr]
  have hne : qpt (d + l) r - FastField.toField (twoAdicGen d)⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (genPoint_ne _ _ h _ d (by omega) hy)
  have := aeval_lastSel (S := K) (2 ^ d) (tw d) (tw_ne_zero d (by omega)) (tw_pow d (by omega))
    (qpt (d + l) r)
  rw [coe_aeval_eq_eval, Algebra.algebraMap_self, RingHom.id_apply, ← toField_inv] at this
  rw [← this, mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- The prover's transition selector at a quotient point. -/
theorem toField_qTrans (d l r : Nat) (hr : r < 2 ^ (d + l)) :
    FastField.toField ((qTrans d l).getD r 0) = qpt (d + l) r - (tw d)⁻¹ := by
  rw [qTrans, Fast.getD_map_lt _ _ _ (by rw [qPoints, size_cosetPoints]; exact hr) _ 0,
    toField_sub, toField_qPoints d l r hr, toField_inv]

/-- `a ^ (n mod m) = a ^ n` for `a ^ m = 1`. -/
theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] (a : M) (n m : Nat) (h : a ^ m = 1) :
    a ^ (n % m) = a ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m]
  rw [pow_add, pow_mul, h, one_pow, mul_one]

/-- The constraints at a row of the quotient domain are the constraint polynomials at its
point. -/
theorem toField_rowEnv_eval (A : Air) (d l : Nat) (h : d + l ≤ 24) (tq : Mat) (pis : List F)
    (T : Nat → K[X])
    (hq : ∀ j < A.width, ∀ r < 2 ^ (d + l),
      FastField.toField (tq.values.getD (r * tq.width + j) 0) = (T j).eval (qpt (d + l) r))
    (c : Expr) (hc : c.colsBelow A.width = true) (r : Nat) (hr : r < 2 ^ (d + l)) :
    FastField.toField (c.eval
      (rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r)) =
      (constraintPoly (2 ^ d) (tw d) T pis c).eval (qpt (d + l) r) := by
  set env := rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r
  let envK : Expr.Env K := {
    cur := fun j ↦ FastField.toField (env.cur j)
    next := fun j ↦ FastField.toField (env.next j)
    pub := fun j ↦ FastField.toField (env.pub j)
    const := FastField.toField
    isFirstRow := FastField.toField env.isFirstRow
    isLastRow := FastField.toField env.isLastRow
    isTransition := FastField.toField env.isTransition }
  have hb := Expr.eval_hom FastField.toField toField_add toField_sub toField_mul A.width
    env envK (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl rfl c hc
  rw [hb, constraintPoly]
  refine (Expr.eval_hom (eval (qpt (d + l) r)) (fun _ _ ↦ eval_add) (fun a b ↦ eval_sub a b _)
    (fun _ _ ↦ eval_mul) A.width _ envK (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun _ ↦ eval_C)
    (fun _ ↦ eval_C) ?_ ?_ ?_ c hc).symm
  · change (T j).eval (qpt (d + l) r) = FastField.toField (tq.values.getD (r * tq.width + j) 0)
    rw [hq j hj r hr]
  · have hm : (r + 2 ^ l) % 2 ^ (d + l) < 2 ^ (d + l) := Nat.mod_lt _ (Nat.two_pow_pos _)
    change ((T j).comp (C (tw d) * X)).eval (qpt (d + l) r) = FastField.toField
      (tq.values.getD ((r + 2 ^ l) % 2 ^ (d + l) * tq.width + j) 0)
    rw [hq j hj _ hm, eval_comp, eval_mul, eval_C, eval_X, qpt, qpt,
      pow_mod_of_pow_eq_one _ _ _ (tw_pow (d + l) h), pow_add, tw_pow_tw d l h,
      mul_comm (tw d), mul_assoc]
  · exact (toField_qFirst d l r h hr).symm
  · exact (toField_qLast d l r h hr).symm
  · change (X - C (tw d)⁻¹).eval (qpt (d + l) r) = FastField.toField ((qTrans d l).getD r 0)
    rw [toField_qTrans d l r hr, eval_sub, eval_X, eval_C]

/-- The trace's extension read in bit-reversed row order is the trace on the quotient domain. -/
theorem permuteRows_lde (m : Stark.Mat) (ps : List K[X]) (b L e : Nat)
    (hm : CompStark.Mat.IsLde b (L + e) m ps) (r : Nat) (hr : r < 2 ^ L) (j : Nat)
    (hj : j < ps.length) :
    FastField.toField ((permuteRows m (bitRevPerm L)).getD (r * m.width + j) 0) =
      (ps.getD j 0).eval (qpt L r) := by
  obtain ⟨hw, -, -, -, h24, -, hval⟩ := hm
  have hr' := CompPoly.CPolynomial.NTT.Transform.bitRevNat_lt L r
  rw [Fast.permuteRows_getD m _ r j (by rw [Fast.size_bitRevPerm]; exact hr) (by omega),
    Fast.bitRevPerm_getD L r hr, hval _ (lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by omega)
      (by omega))) j hj, reverseBits_low L e r hr, pow_mul,
    tw_pow_tw L e h24]

/-- **The prover's quotient values are the folded quotient** on the quotient domain. -/
theorem toSpec_quotientOfLde (A : Air) (pis : List F) (logN b : Nat) (trace : Array F)
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
  have hq : ∀ j < A.width, ∀ r < 2 ^ (logN + lc), FastField.toField
      ((Mat.ofValues ext.width (2 ^ (logN + lc))
        (permuteRows ext (bitRevPerm (logN + lc)))).values.getD (r * ext.width + j) 0) =
      (ps.getD j 0).eval (qpt (logN + lc) r) := fun j hj r hr ↦
    permuteRows_lde ext ps b (logN + lc) (b - lc) hps' r hr j (by omega)
  have hlc24 : logN + lc ≤ 24 := by omega
  have hz : (qpt (logN + lc) r) ^ 2 ^ logN - 1 ≠ 0 :=
    sub_ne_zero.mpr (genPoint_pow_ne _ _ hlc24 logN (by omega))
  show Challenge.toSpec ((quotientValues A pis logN lc (Mat.ofValues ext.width (2 ^ (logN + lc))
    (permuteRows ext (bitRevPerm (logN + lc)))) alpha).getD r 0) = _
  rw [quotientValues_eq, getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn,
    toSpec_quotientRow, toField_invZh logN lc r hlc24, eval_qFold]
  have hmap : (A.constraints.map fun c ↦ algebraMap K E (FastField.toField (c.eval
      (rowEnv (Mat.ofValues ext.width (2 ^ (logN + lc)) (permuteRows ext (bitRevPerm (logN + lc))))
        (2 ^ (logN + lc)) (2 ^ lc) pis (qFirst logN lc) (qLast logN lc) (qTrans logN lc) r)))) =
      (A.constraints.map fun c ↦ aeval (algebraMap K E (qpt (logN + lc) r))
        (quotientPoly logN (ps.getD · 0) pis c)).map
        (· * algebraMap K E (qpt (logN + lc) r ^ 2 ^ logN - 1)) := by
    rw [List.map_map]
    refine List.map_congr_left fun c hc ↦ ?_
    rw [toField_rowEnv_eval A logN lc hlc24 _ pis _ hq c (hcols c hc) r hr,
      constraintPoly_eq A logN (by omega) trace pis _ hT hsat hcols c hc, eval_mul]
    simp only [Function.comp_apply]
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, ← map_mul, mul_comm]
    simp only [zH, eval_sub, eval_pow, eval_X, eval_C]
  rw [hmap, horner_mul, mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hz, map_one, mul_one]

end QuotientValues

/-! ### Recomposing the quotient from its chunks -/

section Recompose

/-- The vanishing polynomial `Z_D(y) = (y / s) ^ n - 1` of the coset `D = s · ⟨ω⟩`, `n = 2 ^ logN`,
at `y`. -/
noncomputable def vanish (logN : Nat) (s : K) (y : E) : E :=
  (y * algebraMap K E s⁻¹) ^ 2 ^ logN - 1

/-- The selector of chunk `c` at `y`: `∏_{d ≠ c} Z_{D_d}(y) / Z_{D_d}(s_c)`, `s_c = g ω_qᶜ`. -/
noncomputable def chunkSel (logN lc c : Nat) (y : E) : E :=
  ∏ d ∈ (Finset.range (2 ^ lc)).erase c, vanish logN (qpt (logN + lc) d) y *
    (vanish logN (qpt (logN + lc) d) (algebraMap K E (qpt (logN + lc) c)))⁻¹

variable (EF) in
/-- The chunk selector as a polynomial. -/
noncomputable def chunkSelPoly (logN lc c : Nat) : E[X] :=
  ∏ d ∈ (Finset.range (2 ^ lc)).erase c, ((X * C (algebraMap K E (qpt (logN + lc) d)⁻¹)) ^ 2 ^ logN
    - 1) * C (vanish logN (qpt (logN + lc) d) (algebraMap K E (qpt (logN + lc) c)))⁻¹

/-- The chunk selector polynomial evaluates to `chunkSel`. -/
theorem eval_chunkSelPoly (logN lc c : Nat) (y : E) :
    (chunkSelPoly EF logN lc c).eval y = chunkSel logN lc c y := by
  rw [chunkSelPoly, eval_prod]
  refine Finset.prod_congr rfl fun d _ ↦ ?_
  rw [eval_mul, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_C, eval_one]
  simp only [vanish]

/-- The chunk selector has degree at most `(k - 1) n`. -/
theorem natDegree_chunkSelPoly (logN lc c : Nat) (hc : c < 2 ^ lc) :
    (chunkSelPoly EF logN lc c).natDegree ≤ (2 ^ lc - 1) * 2 ^ logN := by
  refine (natDegree_prod_le _ _).trans ?_
  have hcard : ((Finset.range (2 ^ lc)).erase c).card = 2 ^ lc - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hc), Finset.card_range]
  rw [← hcard, ← smul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun d _ ↦ ?_
  refine (natDegree_mul_le).trans ?_
  rw [natDegree_C, Nat.add_zero]
  refine (natDegree_sub_le _ _).trans ?_
  rw [natDegree_one, Nat.max_zero]
  refine natDegree_pow_le.trans ?_
  have : (X * C (algebraMap K E (qpt (logN + lc) d)⁻¹)).natDegree ≤ 1 :=
    (natDegree_mul_C_le _ _).trans natDegree_X_le
  calc 2 ^ logN * (X * C (algebraMap K E (qpt (logN + lc) d)⁻¹)).natDegree ≤ 2 ^ logN * 1 :=
        Nat.mul_le_mul_left _ this
    _ = 2 ^ logN := Nat.mul_one _

/-- A degree bound from a `natDegree` bound. -/
theorem degree_lt_of_natDegree_lt'' {p : E[X]} {N : Nat} (h : p.natDegree < N) :
    p.degree < (N : WithBot Nat) :=
  degree_le_natDegree.trans_lt (by exact_mod_cast h)

/-- Quotient points are nonzero. -/
theorem qpt_ne_zero (q m : Nat) (h : q ≤ 24) : qpt q m ≠ 0 :=
  mul_ne_zero toField_gen_ne_zero (pow_ne_zero _ (tw_ne_zero q h))

/-- The point `r` of coset `c` is the quotient domain's point `c + k r`. -/
theorem qpt_coset (logN lc c r : Nat) (h : logN + lc ≤ 24) :
    qpt (logN + lc) c * tw logN ^ r = qpt (logN + lc) (c + 2 ^ lc * r) := by
  rw [qpt, qpt, pow_add, pow_mul, tw_pow_tw logN lc h, mul_assoc]

/-- `Z_{D_d}` takes the same value on all of `D_c`. -/
theorem vanish_coset (logN lc c d r : Nat) (h : logN + lc ≤ 24) :
    vanish logN (qpt (logN + lc) d) (algebraMap K E (qpt (logN + lc) c * tw logN ^ r)) =
      vanish logN (qpt (logN + lc) d) (algebraMap K E (qpt (logN + lc) c)) := by
  simp only [vanish, ← map_mul, ← map_pow]
  rw [mul_right_comm, mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, tw_pow logN (by omega), one_pow,
    mul_one]

/-- `Z_{D_c}(s_c) = 0`. -/
theorem vanish_self (logN lc c : Nat) (h : logN + lc ≤ 24) :
    vanish logN (qpt (logN + lc) c) (algebraMap K E (qpt (logN + lc) c)) = 0 := by
  rw [vanish, ← map_mul, mul_inv_cancel₀ (qpt_ne_zero _ c h), map_one, one_pow, sub_self]

/-- Distinct chunks' cosets are disjoint: `Z_{D_d}(s_c) ≠ 0`. -/
theorem vanish_ne_zero (logN lc c d : Nat) (h : logN + lc ≤ 24) (hc : c < 2 ^ lc)
    (hd : d < 2 ^ lc) (hcd : d ≠ c) :
    vanish logN (qpt (logN + lc) d) (algebraMap K E (qpt (logN + lc) c)) ≠ 0 := by
  rw [vanish, ← map_mul, ← map_pow, ← map_one (algebraMap K E), ← map_sub, ne_eq,
    map_eq_zero_iff _ (algebraMap K E).injective, sub_eq_zero]
  intro he
  have hp := isPrimitiveRoot_twoAdicGen (logN + lc) h
  have hp' : IsPrimitiveRoot (tw (logN + lc) ^ 2 ^ logN) (2 ^ lc) :=
    hp.pow (Nat.two_pow_pos _) (Nat.pow_add 2 logN lc)
  have hg := toField_gen_ne_zero
  have hw := tw_ne_zero (logN + lc) h
  rw [qpt, qpt, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hg, one_mul, mul_pow, inv_pow,
    ← pow_mul, ← pow_mul, Nat.mul_comm c, Nat.mul_comm d, pow_mul, pow_mul,
    mul_inv_eq_one₀ (pow_ne_zero _ (pow_ne_zero _ hw))] at he
  exact hcd (hp'.pow_inj hd hc he.symm)

/-- The chunk selector is `1` on its own coset and `0` on the others. -/
theorem chunkSel_coset (logN lc c c' r : Nat) (h : logN + lc ≤ 24) (hc : c < 2 ^ lc)
    (hc' : c' < 2 ^ lc) :
    chunkSel logN lc c (algebraMap K E (qpt (logN + lc) c' * tw logN ^ r)) =
      if c = c' then 1 else 0 := by
  rw [chunkSel]
  simp only [vanish_coset logN lc c' _ r h]
  by_cases hcc : c = c'
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hcc), ← hcc]
    refine Finset.prod_eq_one fun d hd ↦ ?_
    have hd' := Finset.mem_erase.mp hd
    have hne := vanish_ne_zero (EF := EF) logN lc c d h hc (Finset.mem_range.mp hd'.2) hd'.1
    exact CompPoly.Extension.Ext.mul_inv_cancel' hne
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hcc)]
    refine Finset.prod_eq_zero (i := c') (Finset.mem_erase.mpr ⟨Ne.symm hcc,
      Finset.mem_range.mpr hc'⟩) ?_
    rw [vanish_self logN lc c' h, zero_mul]

/-- **Recomposition**: chunks `q_c` of degree below `n` that agree with `Q`, of degree below
`k n`, on their cosets `s_c ⟨ω⟩` recompose to `Q` everywhere. -/
theorem sum_chunkSel (logN lc : Nat) (h : logN + lc ≤ 24) (Q : E[X])
    (hQ : Q.natDegree < 2 ^ (logN + lc)) (qc : Nat → E[X])
    (hqd : ∀ c < 2 ^ lc, (qc c).natDegree < 2 ^ logN)
    (hqa : ∀ c < 2 ^ lc, ∀ r < 2 ^ logN,
      (qc c).eval (algebraMap K E (qpt (logN + lc) c * tw logN ^ r)) =
        Q.eval (algebraMap K E (qpt (logN + lc) c * tw logN ^ r))) (y : E) :
    ∑ c ∈ Finset.range (2 ^ lc), chunkSel logN lc c y * (qc c).eval y = Q.eval y := by
  set P : E[X] := ∑ c ∈ Finset.range (2 ^ lc), chunkSelPoly EF logN lc c * qc c
  have hP : P = Q := by
    have hp := isPrimitiveRoot_twoAdicGen (logN + lc) h
    refine eq_of_degree_sub_lt_of_eval_index_eq (Finset.range (2 ^ (logN + lc)))
      (v := fun m ↦ algebraMap K E (qpt (logN + lc) m)) (fun i hi j hj hij ↦ ?_) ?_
      (fun m hm ↦ ?_)
    · have := (algebraMap K E).injective hij
      simp only [qpt] at this
      exact hp.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        (mul_left_cancel₀ toField_gen_ne_zero this)
    · rw [Finset.card_range]
      refine (degree_sub_le _ _).trans_lt (max_lt ?_ (degree_lt_of_natDegree_lt'' hQ))
      refine degree_lt_of_natDegree_lt'' ?_
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2 ^ (logN + lc) - 1)
        fun c hc ↦ ?_) (by have := Nat.two_pow_pos (logN + lc); omega)
      have hc := Finset.mem_range.mp hc
      refine natDegree_mul_le.trans ?_
      have h1 := natDegree_chunkSelPoly (EF := EF) logN lc c hc
      have h2 := hqd c hc
      have h3 : (2 ^ lc - 1) * 2 ^ logN + 2 ^ logN = 2 ^ (logN + lc) := by
        rw [Nat.pow_add, Nat.sub_one_mul, Nat.mul_comm]
        have := Nat.two_pow_pos lc
        have : 2 ^ logN ≤ 2 ^ logN * 2 ^ lc := Nat.le_mul_of_pos_right _ this
        omega
      omega
    · have hm := Finset.mem_range.mp hm
      have hk := Nat.two_pow_pos lc
      have hc' : m % 2 ^ lc < 2 ^ lc := Nat.mod_lt _ hk
      have hr : m / 2 ^ lc < 2 ^ logN := by
        rw [Nat.div_lt_iff_lt_mul hk, ← Nat.pow_add]; exact hm
      have hpt : qpt (logN + lc) m = qpt (logN + lc) (m % 2 ^ lc) * tw logN ^ (m / 2 ^ lc) := by
        rw [qpt_coset logN lc _ _ h, Nat.mod_add_div]
      rw [hpt, eval_finsetSum, Finset.sum_eq_single (m % 2 ^ lc) (fun c hc hne ↦ ?_)
        (fun hn ↦ absurd (Finset.mem_range.mpr hc') hn), eval_mul, eval_chunkSelPoly,
        chunkSel_coset logN lc _ _ _ h hc' hc', ite_eq_left_of_eq_true _ _ (eq_true rfl), one_mul,
        hqa _ hc' _ hr]
      rw [eval_mul, eval_chunkSelPoly, chunkSel_coset logN lc _ _ _ h (Finset.mem_range.mp hc) hc',
        ite_eq_right_of_eq_false _ _ (eq_false hne), zero_mul]
  rw [← hP, eval_finsetSum]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [eval_mul, eval_chunkSelPoly]

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
    Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he, Nat.zero_add]

/-- An extension element is the sum of its coordinates times the basis. -/
theorem toSpec_eq_basis (y : EF) : Challenge.toSpec y = ∑ e ∈ Finset.range (Challenge.d EF),
    Challenge.toSpec (Ext.basis e : EF) * algebraMap K E (FastField.toField (coordOf e y)) := by
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
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun e he ↦ ?_) (by omega)
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
      ∀ r < 2 ^ logN, (chunkPoly EF ps).eval (algebraMap K E (qpt (logN + lc) c * tw logN ^ r)) =
        Q.eval (algebraMap K E (qpt (logN + lc) c * tw logN ^ r)) := by
  have hg := toField_gen_ne_zero
  have hw : tw (logN + lc) ≠ 0 := tw_ne_zero _ (by omega)
  have hsh : FastField.toField (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹) ≠ 0 := by
    rw [toField_mul, toField_inv, toField_mul, toField_powF]
    exact mul_ne_zero hg (inv_ne_zero (mul_ne_zero hg (pow_ne_zero _ hw)))
  obtain ⟨ps, hlde, hval⟩ := ldeRef_isLde logN b (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹)
    (Challenge.d EF) (chunkValues qs (2 ^ lc) c (2 ^ logN)) (by rw [size_chunkValues, Nat.mul_comm])
    h24
    (fun h0 ↦ hsh (by rw [h0]; exact toField_zero))
  have hlen : ps.length = Challenge.d EF := hlde.1.symm
  have hpt : FastField.toField (gen * (gen * (gen * powF (twoAdicGen (logN + lc)) c)⁻¹)⁻¹) =
      qpt (logN + lc) c := by
    rw [toField_mul, toField_inv, toField_mul, toField_inv, toField_mul, toField_powF, qpt]
    field_simp
  refine ⟨ps, hlde, natDegree_chunkPoly ps _ (Nat.two_pow_pos _) fun e he ↦ ?_, fun r hr ↦ ?_⟩
  · have hmem : ps.getD e 0 ∈ ps := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have := hlde.2.2.2.2.2.1 _ hmem
    rw [Nat.add_sub_cancel] at this
    exact natDegree_lt_of_degree_lt' (Nat.two_pow_pos _) this
  · have hx : qpt (logN + lc) c * tw logN ^ r = qpt (logN + lc) (r * 2 ^ lc + c) := by
      rw [qpt_coset logN lc c r (by omega)]; congr 1; ring
    rw [eval_chunkPoly, hx, ← hqs _ (by rw [Nat.pow_add]; nlinarith [Nat.two_pow_pos lc]),
      toSpec_eq_basis, ← hx]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he := Finset.mem_range.mp he
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, ← hpt, hval e he r hr,
      chunkValues_getD _ _ _ _ _ _ hr he]

/-- A fold of additions in the spec field. -/
theorem toSpec_foldl_add {α : Type*} (f : α → EF) : ∀ (l : List α) (x : EF),
    Challenge.toSpec (l.foldl (fun acc a ↦ acc + f a) x) =
      Challenge.toSpec x + (l.map fun a ↦ Challenge.toSpec (f a)).sum
  | [], x => by rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | a :: l, x => by
    rw [List.foldl_cons, toSpec_foldl_add f l, Challenge.toSpec_add, List.map_cons, List.sum_cons,
      add_assoc]

/-- A fold of quotients in the spec field. -/
theorem toSpec_foldl_mul {α : Type*} (f g : α → EF) : ∀ (l : List α) (x : EF),
    Challenge.toSpec (l.foldl (fun acc a ↦ acc * f a * (g a)⁻¹) x) =
      Challenge.toSpec x * (l.map fun a ↦ Challenge.toSpec (f a) * (Challenge.toSpec (g a))⁻¹).prod
  | [], x => by rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | a :: l, x => by
    rw [List.foldl_cons, toSpec_foldl_mul f g l, Challenge.toSpec_mul, Challenge.toSpec_mul,
      Challenge.toSpec_inv, List.map_cons, List.prod_cons]
    simp only [mul_assoc]

/-- A list sum over `0, …, n - 1` is the `Finset` sum. -/
theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : Nat → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n,
      Finset.sum_range_succ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- The domain of chunk `i`. -/
abbrev chunkDomain (logN lc i : Nat) : Domain :=
  ⟨gen * powF (twoAdicGen (logN + lc)) i, logN⟩

/-- Chunk `i`'s shift is the quotient point `i`. -/
theorem toField_chunkShift (logN lc i : Nat) :
    FastField.toField (chunkDomain logN lc i).shift = qpt (logN + lc) i := by
  rw [toField_mul, toField_powF]

/-- The verifier's vanishing polynomial of chunk `i`'s coset. -/
theorem toSpec_vanishingAt (logN lc i : Nat) (p : EF) :
    Challenge.toSpec (vanishingAt (chunkDomain logN lc i) p) =
      vanish logN (qpt (logN + lc) i) (Challenge.toSpec p) := by
  rw [vanishingAt, Challenge.toSpec_sub, toSpec_extPowTwo, Challenge.toSpec_mul,
    Challenge.toSpec_ofBase,
    Challenge.toSpec_one, vanish, toField_inv, toField_chunkShift,
    CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- Chunk shifts are distinct. -/
theorem chunkShift_beq (logN lc i j : Nat) (h : logN + lc ≤ 24) (hi : i < 2 ^ lc)
    (hj : j < 2 ^ lc) :
    ((chunkDomain logN lc j).shift != (chunkDomain logN lc i).shift) = (j != i) := by
  by_cases hij : j = i
  · rw [hij]; simp only [bne_self_eq_false]
  · have hne : (chunkDomain logN lc j).shift ≠ (chunkDomain logN lc i).shift := fun he ↦ by
      have := congrArg FastField.toField he
      rw [toField_chunkShift, toField_chunkShift, qpt, qpt] at this
      have hp := isPrimitiveRoot_twoAdicGen (logN + lc) h
      have hk : 2 ^ lc ≤ 2 ^ (logN + lc) := Nat.pow_le_pow_right (by omega) (by omega)
      exact hij (hp.pow_inj (by omega) (by omega) (mul_left_cancel₀ toField_gen_ne_zero this))
    rw [bne_iff_ne.mpr hne, bne_iff_ne.mpr hij]

/-- The verifier's selector of chunk `i` is `chunkSel`. -/
theorem toSpec_selector (logN lc i : Nat) (h : logN + lc ≤ 24) (hi : i < 2 ^ lc) (z : EF) :
    Challenge.toSpec (((chunkDomains logN lc).filter fun dj ↦
      dj.shift != (chunkDomain logN lc i).shift).foldl
      (fun acc dj ↦ acc * vanishingAt dj z *
        (vanishingAt dj (Ext.ofBase (chunkDomain logN lc i).shift))⁻¹) 1) =
      chunkSel logN lc i (Challenge.toSpec z) := by
  have hds : chunkDomains logN lc = (List.range (2 ^ lc)).map (chunkDomain logN lc) := rfl
  have hf : (List.range (2 ^ lc)).filter (fun j ↦ (chunkDomain logN lc j).shift !=
      (chunkDomain logN lc i).shift) = (List.range (2 ^ lc)).filter (fun j ↦ j != i) :=
    List.filter_congr fun j hj ↦ chunkShift_beq logN lc i j h hi (List.mem_range.mp hj)
  rw [hds, List.filter_map]
  simp only [Function.comp_def]
  rw [hf, List.foldl_map, toSpec_foldl_mul, Challenge.toSpec_one, one_mul]
  have hnd : ((List.range (2 ^ lc)).filter (· != i)).Nodup := (List.nodup_range).filter _
  have hfs : ((List.range (2 ^ lc)).filter (· != i)).toFinset =
      (Finset.range (2 ^ lc)).erase i := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq,
      Finset.mem_erase, Finset.mem_range]
    exact And.comm
  rw [← List.prod_toFinset _ hnd, hfs, chunkSel]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [toSpec_vanishingAt, toSpec_vanishingAt, Challenge.toSpec_ofBase, toField_chunkShift,
    ← CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- The verifier's per-chunk sum of the `d` coordinates. -/
abbrev chunkInner (ch : Array EF) : EF :=
  (List.range (Challenge.d EF)).foldl (fun s e ↦ s + Ext.basis e * ch.getD e 0) 0

/-- **The verifier's recomposition** is `∑_c L_c(ζ) q_c(ζ)` with the chunks' values. -/
theorem toSpec_recompose (logN lc : Nat) (h : logN + lc ≤ 24) (chs : Nat → Array EF) (z : EF) :
    Challenge.toSpec (recompose (chunkDomains logN lc) ((List.range (2 ^ lc)).map chs) z) =
      ∑ c ∈ Finset.range (2 ^ lc),
        chunkSel logN lc c (Challenge.toSpec z) * Challenge.toSpec (chunkInner (chs c)) := by
  have hds : chunkDomains logN lc = (List.range (2 ^ lc)).map (chunkDomain logN lc) := rfl
  unfold recompose
  rw [hds, List.map_map]
  simp only [List.zip_map', List.foldl_map, Function.comp_apply]
  rw [toSpec_foldl_add, Challenge.toSpec_zero, zero_add, list_sum_range]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [Challenge.toSpec_mul, ← hds]
  exact congrArg (· * _) (toSpec_selector logN lc c h (Finset.mem_range.mp hc) z)

end Recompose

/-! ### The verifier's check -/

section Check

/-- The verifier's per-chunk sum in the spec field. -/
theorem toSpec_chunkInner (ch : Array EF) : Challenge.toSpec (chunkInner ch) =
    ∑ e ∈ Finset.range (Challenge.d EF),
      Challenge.toSpec (Ext.basis e : EF) * Challenge.toSpec (ch.getD e 0) := by
  rw [chunkInner, toSpec_foldl_add, Challenge.toSpec_zero, zero_add, ← list_sum_range]
  simp only [Challenge.toSpec_mul]

/-- An opened chunk's coordinates combine to its chunk polynomial at the point. -/
theorem toSpec_chunkInner_openedAt (b h : Nat) (m : Stark.Mat) (ps : List K[X]) (z : EF)
    (hm : CompStark.Mat.IsLde b h m ps) (h4 : ps.length = Challenge.d EF)
    (hz : Ext.OutsideBase z) :
    Challenge.toSpec (chunkInner (Fri.openedAt b m z)) =
      (chunkPoly EF ps).eval (Challenge.toSpec z) := by
  rw [toSpec_chunkInner, eval_chunkPoly]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [(openedAt_isLde b h m ps z hm hz).2 e (by rw [h4]; exact Finset.mem_range.mp he)]

/-- The verifier's folded constraints are Horner's rule in `α`. -/
theorem toSpec_foldedConstraints (A : Air) (env : Expr.Env EF) (alpha : EF) :
    Challenge.toSpec (foldedConstraints A env alpha) = horner
      (A.constraints.map fun c ↦ Challenge.toSpec (c.eval env)) (Challenge.toSpec alpha) := by
  suffices h : ∀ (l : List Expr) (x : EF), Challenge.toSpec (l.foldl (fun acc c ↦ acc * alpha +
      c.eval env) x) = (l.map fun c ↦ Challenge.toSpec (c.eval env)).foldl
        (fun acc v ↦ acc * Challenge.toSpec alpha + v) (Challenge.toSpec x) by
    rw [foldedConstraints, h, Challenge.toSpec_zero]
    rfl
  intro l
  induction l with
  | nil => intro x; rfl
  | cons c l ih =>
    intro x
    rw [List.foldl_cons, ih, Challenge.toSpec_add, Challenge.toSpec_mul]
    rfl

/-- `a * b * b⁻¹ = a` in the spec extension field. -/
theorem mul_mul_inv_cancel_ext (a b : E) (hb : b ≠ 0) : a * b * b⁻¹ = a := by
  rw [mul_assoc, CompPoly.Extension.Ext.mul_inv_cancel' hb, mul_one]

/-- The verifier's constraints at `ζ`, from the opened trace values, are the constraint
polynomials at `ζ`. -/
theorem toSpec_eval_opened (A : Air) (logN b : Nat) (pis : List F) (m : Stark.Mat)
    (ps : List K[X]) (hm : CompStark.Mat.IsLde b (logN + b) m ps)
    (hw : ps.length = A.width) (z : EF) (hz : Ext.OutsideBase z) (tl tn : Array EF)
    (htl : tl = Fri.openedAt b m z) (htn : tn = Fri.openedAt b m (z * Ext.ofBase (twoAdicGen logN)))
    (c : Expr) (hc : c.colsBelow A.width = true) :
    Challenge.toSpec (c.eval {
      cur := fun i ↦ tl.getD i 0
      next := fun i ↦ tn.getD i 0
      pub := fun i ↦ Ext.ofBase (pis.getD i 0)
      const := Ext.ofBase
      isFirstRow := (Ext.powTwo z logN - 1) * (z - 1)⁻¹
      isLastRow := (Ext.powTwo z logN - 1) * (z - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹
      isTransition := z - Ext.ofBase (twoAdicGen logN)⁻¹ }) =
      aeval (Challenge.toSpec z) (constraintPoly (2 ^ logN) (tw logN) (ps.getD · 0) pis c) := by
  have h24 : logN ≤ 24 := by have := hm.2.2.2.2.1; omega
  have hw0 : twoAdicGen logN ≠ 0 := twoAdicGen_ne_zero logN h24
  have hz' : Ext.OutsideBase (z * Ext.ofBase (twoAdicGen logN)) := outsideBase_mul_ofBase hz hw0
  have hO := (openedAt_isLde b (logN + b) m ps z hm hz).2
  have hO' := (openedAt_isLde b (logN + b) m ps _ hm hz').2
  have hone : Challenge.toSpec z - 1 ≠ 0 := by
    have := toSpec_ne_ofBase hz 1
    rwa [CompPoly.Extension.Ext.ofBase_one, ← sub_ne_zero] at this
  have hlast : Challenge.toSpec z - algebraMap K E (tw logN)⁻¹ ≠ 0 := by
    have := toSpec_ne_ofBase hz (tw logN)⁻¹
    rwa [← CompPoly.Extension.Ext.algebraMap_eq_ofBase, ← sub_ne_zero] at this
  subst htl htn
  set env : Expr.Env EF := {
      cur := fun i ↦ (Fri.openedAt b m z).getD i 0
      next := fun i ↦ (Fri.openedAt b m (z * Ext.ofBase (twoAdicGen logN))).getD i 0
      pub := fun i ↦ Ext.ofBase (pis.getD i 0)
      const := Ext.ofBase
      isFirstRow := (Ext.powTwo z logN - 1) * (z - 1)⁻¹
      isLastRow := (Ext.powTwo z logN - 1) * (z - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹
      isTransition := z - Ext.ofBase (twoAdicGen logN)⁻¹ } with henv
  let envE : Expr.Env E := {
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
  · change aeval (Challenge.toSpec z) ((ps.getD j 0).comp (C (tw logN) * X)) =
      Challenge.toSpec ((Fri.openedAt b m (z * Ext.ofBase (twoAdicGen logN))).getD j 0)
    rw [hO' j (by rw [hw]; exact hj), aeval_comp, map_mul, aeval_C, aeval_X, Challenge.toSpec_mul,
      Challenge.toSpec_ofBase, ← CompPoly.Extension.Ext.algebraMap_eq_ofBase, mul_comm]
  · change aeval (Challenge.toSpec z) (C (FastField.toField (pis.getD j 0))) =
      Challenge.toSpec (Ext.ofBase (pis.getD j 0))
    rw [aeval_C, Challenge.toSpec_ofBase, CompPoly.Extension.Ext.algebraMap_eq_ofBase]
  · change aeval (Challenge.toSpec z) (C (FastField.toField x)) = Challenge.toSpec (Ext.ofBase x)
    rw [aeval_C, Challenge.toSpec_ofBase, CompPoly.Extension.Ext.algebraMap_eq_ofBase]
  · change aeval (Challenge.toSpec z) (firstSel (2 ^ logN)) =
      Challenge.toSpec ((Ext.powTwo z logN - 1) * (z - 1)⁻¹)
    rw [Challenge.toSpec_mul, Challenge.toSpec_inv, Challenge.toSpec_sub, Challenge.toSpec_sub,
      toSpec_extPowTwo, Challenge.toSpec_one, ← aeval_firstSel, mul_mul_inv_cancel_ext _ _ hone]
  · change aeval (Challenge.toSpec z) (lastSel (2 ^ logN) (tw logN)) =
      Challenge.toSpec ((Ext.powTwo z logN - 1) * (z - Ext.ofBase (twoAdicGen logN)⁻¹)⁻¹)
    rw [Challenge.toSpec_mul, Challenge.toSpec_inv, Challenge.toSpec_sub, Challenge.toSpec_sub,
      toSpec_extPowTwo, Challenge.toSpec_one, Challenge.toSpec_ofBase, toField_inv,
      ← CompPoly.Extension.Ext.algebraMap_eq_ofBase,
      ← aeval_lastSel (2 ^ logN) (tw logN) (tw_ne_zero logN h24) (tw_pow logN h24),
      mul_mul_inv_cancel_ext _ _ hlast]
  · change aeval (Challenge.toSpec z) (X - C (tw logN)⁻¹) =
      Challenge.toSpec (z - Ext.ofBase (twoAdicGen logN)⁻¹)
    rw [map_sub, aeval_X, aeval_C, Challenge.toSpec_sub, Challenge.toSpec_ofBase, toField_inv,
      CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- The trace's extension is an LDE of polynomials that take the trace on `⟨ω⟩`. -/
theorem trace_lde (P : Params) (A : Air) (logN : Nat) (trace : Array F)
    (hin : Fits P A logN trace) :
    ∃ ps, CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup)
      (ldeRef logN P.logBlowup gen A.width trace) ps ∧
      TraceOn logN A.width trace (ps.getD · 0) ∧ TraceDeg logN (ps.getD · 0) := by
  obtain ⟨ps, hlde, hval⟩ := ldeRef_isLde logN P.logBlowup gen A.width trace hin.trace
    hin.twoAdic gen_ne_zero
  refine ⟨ps, hlde, fun j hj i hi ↦ ?_, fun j ↦ ?_⟩
  · have := hval j hj i hi
    rwa [mul_inv_cancel₀ gen_ne_zero, toField_one, one_mul] at this
  · by_cases hj : j < ps.length
    · have hmem : ps.getD j 0 ∈ ps := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
      have := hlde.2.2.2.2.2.1 _ hmem
      rw [Nat.add_sub_cancel] at this
      have := natDegree_lt_of_degree_lt' (Nat.two_pow_pos _) this
      show (ps.getD j 0).natDegree ≤ 2 ^ logN - 1
      omega
    · show (ps.getD j 0).natDegree ≤ 2 ^ logN - 1
      rw [List.getD_eq_default _ _ (by omega), natDegree_zero]
      exact Nat.zero_le _

/-- `checkConstraints` as a function. Rewriting with it, rather than unfolding the definition at
its arguments, keeps the kernel from evaluating the final `==` on symbolic extension elements. -/
theorem checkConstraints_eq_fun : checkConstraints = fun (A : Air) (pis : List F)
    (opened : OpenedValues EF) (degreeBits : Nat) (zeta alpha quotient : EF) ↦
  let gInv := Ext.ofBase (twoAdicGen degreeBits)⁻¹
  let zh := Ext.powTwo zeta degreeBits - 1
  let env : Expr.Env EF := {
    cur := fun i ↦ opened.traceLocal.getD i 0
    next := fun i ↦ opened.traceNext.getD i 0
    pub := fun i ↦ Ext.ofBase (pis.getD i 0)
    const := Ext.ofBase
    isFirstRow := zh * (zeta - 1)⁻¹
    isLastRow := zh * (zeta - gInv)⁻¹
    isTransition := zeta - gInv }
  foldedConstraints A env alpha * zh⁻¹ == quotient := rfl

/-- The check passes when the folded constraints over `Z_H(ζ)` equal the quotient in the spec
field. -/
theorem checkConstraints_of (A : Air) (pis : List F) (o : OpenedValues EF) (logN : Nat)
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
theorem checkConstraints_honest (P : Params) (A : Air) (logN : Nat) (trace : Array F)
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
      ∀ r < 2 ^ logN, (chunkPoly EF cps).eval (algebraMap K E (qpt (logN + lc) c * tw logN ^ r)) =
        Q.eval (algebraMap K E (qpt (logN + lc) c * tw logN ^ r)) := by
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
    have := pow_ne_of_outsideBase hz (specDomain logN (by omega)) one_ne_zero
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
      constraintPoly_eq A logN (by omega) trace pis _ hT hsat hin.cols c hc, map_mul]
    simp only [Function.comp_apply, zH, map_sub, map_pow, aeval_X, map_one]
    ring
  rw [hmap, horner_mul, mul_mul_inv_cancel_ext _ _ hzh]

/-- Every chunk of the honest quotient is an LDE of `d` polynomials. -/
theorem chunk_isLde (P : Params) (A : Air) (logN : Nat) (qs : Array EF)
    (h24 : logN + P.logBlowup ≤ 24) (hlc : A.logQuotientChunks ≤ P.logBlowup) (c : Nat) :
    ∃ ps, CompStark.Mat.IsLde P.logBlowup (logN + P.logBlowup) (ldeRef logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
      (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))) ps ∧
        ps.length = Challenge.d EF := by
  have hg := toField_gen_ne_zero
  have hsh : FastField.toField
      (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) ≠ 0 := by
    rw [toField_mul, toField_inv, toField_mul, toField_powF]
    exact mul_ne_zero hg (inv_ne_zero (mul_ne_zero hg (pow_ne_zero _ (tw_ne_zero _ (by omega)))))
  obtain ⟨ps, hlde, -⟩ := ldeRef_isLde logN P.logBlowup
    (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
    (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))
    (by rw [size_chunkValues, Nat.mul_comm]) h24 (fun h0 ↦ hsh (by rw [h0]; exact toField_zero))
  exact ⟨ps, hlde, hlde.1.symm⟩

/-- The honest openings pass the verifier's shape check. -/
theorem honest_shape (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F)
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
  have hs (m : Stark.Mat) (z : EF) : (Fri.openedAt P.logBlowup m z).size = m.width := by
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
