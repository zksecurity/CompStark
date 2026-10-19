/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Lde
public import CompStark.Stark.Fast.Quotient
public import CompStark.Stark.Prover
public import CompStark.Stark.Refines

/-! # The quotient and the out-of-domain check

The honest prover's openings pass the verifier's constraint check at `ζ`.

Over the spec field, let `T_j` be the trace's column polynomials (`ldeRef_isLde`) and `C_c` the
constraint `c` evaluated on them with the selector polynomials `Z_H(X) / (X - 1)`,
`Z_H(X) / (X - ω⁻¹)` and `X - ω⁻¹` (`polyEnv`). `Air.Satisfied` says `C_c` vanishes on the trace
domain `H = ⟨ω⟩`, so `C_c = Z_H Q_c`, and `Air.DegreeFits` bounds `Q_c` below `k n`, `k` the
number of chunks (`quotientPoly`). The folded quotient `Q = ∑_c α^(K-1-c) Q_c` is a polynomial
of degree below `k n`.

* The prover's quotient values are `Q` on the quotient domain `g · ⟨ω_q⟩`
  (`quotientOfLde_toSpec`): `quotientValues` evaluates the same constraints there, with the same
  selectors, divided by `Z_H`.
* Chunk `c` holds `Q` on the coset `s_c ⟨ω⟩`, `s_c = g ω_qᶜ`; its extension's four coordinate
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

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4
local notation "K" => KoalaBear.Field
local notation "E" => KoalaBear.Ext4

/-! ### Satisfaction and degree -/

/-- Row `i` of the trace domain `⟨ω⟩` of size `n = 2 ^ logN`: the trace's rows `i` and
`i + 1 mod n` and the selectors at `ωⁱ`. The first-row selector `Z_H(X) / (X - 1)` is `n` at `1`
and `0` elsewhere on `⟨ω⟩`, the last-row selector `Z_H(X) / (X - ω⁻¹)` is `n ω` at `ω⁻¹` (row
`n - 1`) and `0` elsewhere, the transition selector is `X - ω⁻¹`. -/
def Air.traceRow (A : Air) (logN : Nat) (trace : Array F) (pis : List F) (i : Nat) :
    Expr.Env F where
  cur c := trace.getD (i * A.width + c) 0
  next c := trace.getD ((i + 1) % 2 ^ logN * A.width + c) 0
  pub j := pis.getD j 0
  const c := c
  isFirstRow := if i = 0 then ((2 ^ logN : Nat) : F) else 0
  isLastRow := if i + 1 = 2 ^ logN then ((2 ^ logN : Nat) : F) * twoAdicGen logN else 0
  isTransition := twoAdicGen logN ^ i - (twoAdicGen logN)⁻¹

/-- Every constraint vanishes on every row of the trace domain `⟨ω⟩` of size `2 ^ logN`, with
Plonky3's selectors there: `Z_H(x) / (x - 1)`, `Z_H(x) / (x - ω⁻¹)` and `x - ω⁻¹`
(`Air.traceRow`). -/
def Air.Satisfied (A : Air) (logN : Nat) (trace : Array F) (pis : List F) : Prop :=
  ∀ c ∈ A.constraints, ∀ i < 2 ^ logN, c.eval (A.traceRow logN trace pis i) = 0

/-- A bound on the degree of a constraint as a polynomial on a trace domain of size `n`: the
columns and the first- and last-row selectors have degree `n - 1`, the transition selector `1`. -/
def Expr.degBound (n : Nat) : Expr → Nat
  | .cur _ | .next _ | .isFirstRow | .isLastRow => n - 1
  | .isTransition => 1
  | .pub _ | .const _ => 0
  | .add a b | .sub a b => max (a.degBound n) (b.degBound n)
  | .mul a b => a.degBound n + b.degBound n

/-- The constraints' degrees fit the quotient's chunks: every constraint, of degree at most
`degBound n`, is below `(k + 1) n` for `k = 2 ^ logQuotientChunks` chunks of size `n = 2 ^ logN`,
so that it divided by `Z_H` has degree below `k n`. Unlike Plonky3's `degree_multiple`, the
transition selector counts as degree `1`. -/
def Air.DegreeFits (A : Air) (logN : Nat) : Prop :=
  ∀ c ∈ A.constraints, c.degBound (2 ^ logN) < 2 ^ (logN + A.logQuotientChunks) + 2 ^ logN

/-! ### The example AIRs fit -/

theorem Expr.mul_eq (a b : Expr) : a * b = .mul a b := rfl
theorem Expr.sub_eq (a b : Expr) : a - b = .sub a b := rfl
theorem Expr.add_eq (a b : Expr) : a + b = .add a b := rfl

theorem isPowerOfTwo_two_pow : ∀ k, (2 ^ k).isPowerOfTwo
  | 0 => Nat.isPowerOfTwo_one
  | k + 1 => by rw [Nat.pow_succ]; exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo (isPowerOfTwo_two_pow k)

/-- Plonky3's chunk count for a largest degree `d + 1`, `d = 2 ^ k`. -/
theorem logQuotientChunks_of (A : Air) (k : Nat) (h : max A.maxDegree 2 - 1 = 2 ^ k) :
    A.logQuotientChunks = k := by
  rw [Air.logQuotientChunks]
  simp only [h]
  rw [Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k), Nat.log2_two_pow]

theorem fibonacci_degreeFits (logN : Nat) : fibonacci.DegreeFits logN := by
  have hlc : fibonacci.logQuotientChunks = 0 := logQuotientChunks_of _ 0 (by decide)
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [fibonacci, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hlc, Nat.add_zero]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Expr.sub_eq, Expr.add_eq, Expr.degBound] <;> omega

theorem cube_degreeFits (logN : Nat) : cube.DegreeFits logN := by
  have hlc : cube.logQuotientChunks = 1 := logQuotientChunks_of _ 1 (by decide)
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [cube, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hlc, Nat.pow_succ]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Expr.sub_eq, Expr.add_eq, Expr.degBound] <;> omega

theorem foldl_max_degree (a : Nat) : ∀ l : List Expr, (∀ c ∈ l, c.degree = 3) → l ≠ [] →
    l.foldl (fun m c ↦ max m c.degree) a = max a 3
  | [], _, h => absurd rfl h
  | [c], hl, _ => by rw [List.foldl_cons, List.foldl_nil, hl c List.mem_cons_self]
  | c :: d :: l, hl, _ => by
    rw [List.foldl_cons, foldl_max_degree _ (d :: l) (fun e he ↦ hl e (List.mem_cons_of_mem _ he))
      (List.cons_ne_nil _ _), hl c List.mem_cons_self, Nat.max_assoc, Nat.max_self]

theorem wide_degreeFits (w logN : Nat) : (wide w).DegreeFits logN := by
  have := Nat.two_pow_pos logN
  intro c hc
  simp only [wide, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have hmax : (wide w).maxDegree = 3 := by
    rw [Air.maxDegree, foldl_max_degree 0 _ (fun e he ↦ ?_)
      (by simp only [wide, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega)]
    · rfl
    · simp only [wide, List.mem_map, List.mem_range] at he
      obtain ⟨i, -, rfl⟩ := he
      rfl
  have hlc : (wide w).logQuotientChunks = 1 := logQuotientChunks_of _ 1 (by rw [hmax]; rfl)
  rw [hlc, Nat.pow_succ]
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

theorem aeval_firstSel {S : Type*} [CommRing S] [Algebra K S] (n : Nat) (y : S) :
    aeval y (firstSel n) * (y - 1) = y ^ n - 1 := by
  rw [firstSel, map_sum]
  simp only [map_pow, aeval_X]
  exact geom_sum_mul y n

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

theorem natDegree_firstSel (n : Nat) : (firstSel n).natDegree ≤ n - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun m hm ↦
    (natDegree_X_pow_le m).trans (by have := Finset.mem_range.mp hm; omega)

theorem natDegree_comp_shift (p : K[X]) (w : K) : (p.comp (C w * X)).natDegree ≤ p.natDegree :=
  natDegree_comp_le.trans (by
    have := (natDegree_C_mul_le w (X : K[X])).trans natDegree_X_le
    calc p.natDegree * (C w * X).natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ this
      _ = p.natDegree := Nat.mul_one _)

theorem natDegree_lastSel (n : Nat) (w : K) : (lastSel n w).natDegree ≤ n - 1 :=
  (natDegree_C_mul_le _ _).trans ((natDegree_comp_shift _ _).trans (natDegree_firstSel n))

/-- The constraint `c` over the trace polynomials. -/
noncomputable def constraintPoly (n : Nat) (w : K) (T : Nat → K[X]) (pis : List F) (c : Expr) :
    K[X] :=
  c.eval (polyEnv n w T pis)

theorem natDegree_constraintPoly (n : Nat) (w : K) (T : Nat → K[X]) (pis : List F) (c : Expr)
    (hT : ∀ j, (T j).natDegree ≤ n - 1) :
    (constraintPoly n w T pis c).natDegree ≤ c.degBound n :=
  Expr.natDegree_eval n (polyEnv n w T pis) hT (fun j ↦ (natDegree_comp_shift _ _).trans (hT j))
    (fun _ ↦ natDegree_C _) (fun _ ↦ natDegree_C _) (natDegree_firstSel n)
    (natDegree_lastSel n w) (natDegree_sub_le_of_le natDegree_X_le (natDegree_C _).le) c

/-! ### Two-adic roots of unity in the spec field -/

/-- `ω` of order `2 ^ k`, in the spec field. -/
noncomputable abbrev tw (k : Nat) : K := FastField.toField (twoAdicGen k)

theorem tw_pow (k : Nat) (hk : k ≤ 24) : tw k ^ 2 ^ k = 1 :=
  (isPrimitiveRoot_twoAdicGen k hk).pow_eq_one

theorem tw_ne_zero (k : Nat) (hk : k ≤ 24) : tw k ≠ 0 :=
  (isPrimitiveRoot_twoAdicGen k hk).ne_zero (Nat.two_pow_pos k).ne'

theorem tw_pow_tw (n b : Nat) (h : n + b ≤ 24) : tw (n + b) ^ 2 ^ b = tw n := by
  rw [tw, tw, ← toField_npow, Fast.twoAdicGen_pow n b h]

/-- `x ^ 2 ^ k` by squaring. -/
def sqIter (x : K) : Nat → K
  | 0 => x
  | k + 1 => sqIter (x * x) k

theorem sqIter_eq (x : K) : ∀ k, sqIter x k = x ^ 2 ^ k
  | 0 => (pow_one x).symm
  | k + 1 => by rw [sqIter, sqIter_eq _ k, ← sq, ← pow_mul, pow_succ']

/-- `g = 3` is not in the two-adic subgroup. -/
theorem gen_pow_ne_one : FastField.toField gen ^ 2 ^ 24 ≠ 1 := by
  rw [show FastField.toField gen = 3 by decide, ← sqIter_eq]
  decide

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

theorem genPoint_ne (k m : Nat) (hk : k ≤ 24) (y : K) (j : Nat) (hj : j ≤ 24)
    (hy : y ^ 2 ^ j = 1) : FastField.toField gen * tw k ^ m ≠ y := fun h ↦
  genPoint_pow_ne k m hk j hj (by rw [h, hy])

/-! ### The constraints vanish on the trace domain -/

theorem eval_firstSel_mul (n : Nat) (y : K) : (firstSel n).eval y * (y - 1) = y ^ n - 1 := by
  rw [firstSel, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact geom_sum_mul y n

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
        ite_eq_right_of_eq_false _ _ (eq_false (by rw [Nat.mod_eq_of_lt (by omega)]; omega)), mul_zero]
  · change (X - C (tw logN)⁻¹).eval (tw logN ^ i) =
      FastField.toField (twoAdicGen logN ^ i - (twoAdicGen logN)⁻¹)
    rw [eval_sub, eval_X, eval_C, toField_sub, toField_npow, toField_inv]

/-- The trace domain's vanishing polynomial `Z_H = Xⁿ - 1`. -/
noncomputable abbrev zH (n : Nat) : K[X] := X ^ n - C 1

/-- A constraint that vanishes on the trace domain, divided by `Z_H`. -/
noncomputable def quotientPoly (logN : Nat) (T : Nat → K[X]) (pis : List F) (c : Expr) : K[X] :=
  constraintPoly (2 ^ logN) (tw logN) T pis c /ₘ zH (2 ^ logN)

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
    (hsat : A.Satisfied logN trace pis) (hcols : A.ColsInWidth) (c : Expr)
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

theorem horner_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : List R) (a : R) :
    f (horner l a) = horner (l.map f) (f a) := by
  suffices h : ∀ (l : List R) (x : R), f (l.foldl (fun acc v ↦ acc * a + v) x) =
      (l.map f).foldl (fun acc v ↦ acc * f a + v) (f x) by
    rw [horner, horner, h, map_zero]
  intro l
  induction l with
  | nil => intro x; rfl
  | cons v l ih => intro x; rw [List.foldl_cons, ih, map_add, map_mul]; rfl

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

theorem natDegree_qFold (A : Air) (logN : Nat) (pis : List F) (T : Nat → K[X])
    (hTd : TraceDeg logN T) (hdeg : A.DegreeFits logN) (a : E) :
    (qFold A logN T pis a).natDegree < 2 ^ (logN + A.logQuotientChunks) := by
  refine natDegree_horner _ a _ 0 (by rw [natDegree_zero]; exact Nat.two_pow_pos _)
    (fun p hp ↦ ?_)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact natDegree_map_le.trans_lt (natDegree_quotientPoly A logN pis T hTd hdeg c hc)

theorem eval_qFold (A : Air) (logN : Nat) (T : Nat → K[X]) (pis : List F) (a y : E) :
    (qFold A logN T pis a).eval y =
      horner (A.constraints.map fun c ↦ aeval y (quotientPoly logN T pis c)) a := by
  rw [qFold, ← coe_evalRingHom, horner_map, coe_evalRingHom, eval_C, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ ↦ ?_
  simp only [Function.comp_apply, eval_map_algebraMap]

/-! ### The prover's quotient values -/

section QuotientValues
open KoalaBear.Fast (Ext4)

theorem toSpec_extPow (x : EF) (n : Nat) : Ext4.toSpec (Ext.pow x n) = Ext4.toSpec x ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases n with
    | zero => rw [Ext.pow, Ext4.toSpec_one, pow_zero]
    | succ k =>
      rw [Ext.pow]
      have h := Nat.div_add_mod (k + 1) 2
      split_ifs with hp
      · rw [Ext4.toSpec_mul, ih _ (by omega), Ext4.toSpec_mul, ← sq, ← pow_mul, ← pow_succ']
        exact congrArg (Ext4.toSpec x ^ ·) (by omega)
      · rw [ih _ (by omega), Ext4.toSpec_mul, ← sq, ← pow_mul]
        exact congrArg (Ext4.toSpec x ^ ·) (by omega)

theorem toSpec_extPowTwo (x : EF) : ∀ k, Ext4.toSpec (Ext.powTwo x k) = Ext4.toSpec x ^ 2 ^ k
  | 0 => by rw [Ext.powTwo, pow_zero, pow_one]
  | k + 1 => by
    rw [Ext.powTwo, toSpec_extPowTwo _ k, Ext4.toSpec_mul, ← sq, ← pow_mul, ← Nat.pow_succ']

/-- The extension element of four coordinates. -/
def ofCoeffs (l : List F) : EF := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0⟩

theorem ofCoeffs_coeffs (y : EF) : ofCoeffs (Ext.coeffs y) = y := rfl

theorem toSpec_rowAcc (ev : Expr → F) : ∀ (cw : List (Expr × List F)) (x0 x1 x2 x3 : F),
    Ext4.toSpec ⟨rowAcc cw ev 0 x0, rowAcc cw ev 1 x1, rowAcc cw ev 2 x2, rowAcc cw ev 3 x3⟩ =
      Ext4.toSpec ⟨x0, x1, x2, x3⟩ + (cw.map fun a ↦
        algebraMap K E (FastField.toField (ev a.1)) * Ext4.toSpec (ofCoeffs a.2)).sum
  | [], x0, x1, x2, x3 => by
    rw [List.map_nil, List.sum_nil, add_zero]
    rfl
  | a :: cw, x0, x1, x2, x3 => by
    simp only [Fast.rowAcc_cons]
    rw [toSpec_rowAcc ev cw, List.map_cons, List.sum_cons, ← add_assoc, ← Algebra.smul_def,
      ← Ext4.toSpec_smul, ← Ext4.toSpec_add]
    congr 2

/-- The weighted constraints' sum is Horner's rule in `α`. -/
theorem weighted_sum (A : Air) (alpha : EF) (g : Expr → E) :
    ((weighted A alpha).map fun a ↦ g a.1 * Ext4.toSpec (ofCoeffs a.2)).sum =
      horner (A.constraints.map g) (Ext4.toSpec alpha) := by
  rw [horner_eq_sum, List.length_map, weighted]
  have : (List.range A.constraints.length).map (fun k ↦ Ext4.toSpec alpha ^
      (A.constraints.length - 1 - k)) = ((List.range A.constraints.length).map fun k ↦
        Ext.coeffs (Ext.pow alpha (A.constraints.length - 1 - k))).map
          (fun l ↦ Ext4.toSpec (ofCoeffs l)) := by
    rw [List.map_map]
    refine List.map_congr_left fun k _ ↦ ?_
    simp only [Function.comp_apply]
    rw [ofCoeffs_coeffs, toSpec_extPow]
  rw [this, List.zip_map, List.map_map]
  congr 1

/-- The prover's quotient row in the spec field. -/
theorem toSpec_quotientRow (A : Air) (pis : List F) (d l : Nat) (tq : Mat) (alpha : EF)
    (r : Nat) : Ext4.toSpec (quotientRow A pis d l tq alpha r) =
      algebraMap K E (FastField.toField ((batchInv (qZh d l)).getD (r % 2 ^ l) 0)) *
        horner (A.constraints.map fun c ↦ algebraMap K E (FastField.toField (c.eval
          (rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r))))
          (Ext4.toSpec alpha) := by
  simp only [quotientRow]
  rw [Ext4.toSpec_smul, Algebra.smul_def]
  refine congrArg₂ (· * ·) rfl ?_
  refine (toSpec_rowAcc _ _ 0 0 0 0).trans ?_
  have h0 : Ext4.toSpec ⟨0, 0, 0, 0⟩ = 0 := Ext4.toSpec_zero
  rw [h0, zero_add]
  exact weighted_sum A alpha fun c ↦ algebraMap K E (FastField.toField (c.eval
    (rowEnv tq (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r)))

/-- A batch inversion of nonzero elements, entry by entry. -/
theorem toField_batchInv (xs : Array F) (hx : ∀ x ∈ xs, FastField.toField x ≠ 0) (i : Nat)
    (hi : i < xs.size) :
    FastField.toField ((batchInv xs).getD i 0) = (FastField.toField (xs.getD i 0))⁻¹ := by
  rw [batchInv_eq FastField.toField toField_injective toField_mul toField_inv toField_one xs hx,
    Fast.getD_map_lt _ _ _ hi _ 0, toField_inv]

theorem toField_qPoints (d l m : Nat) (hm : m < 2 ^ (d + l)) :
    FastField.toField ((qPoints d l).getD m 0) = FastField.toField gen * tw (d + l) ^ m := by
  rw [qPoints, cosetPoints_eq, getD_lt _ _ (by rw [Array.size_ofFn]; exact hm),
    Array.getElem_ofFn, toField_mul, toField_npow]

theorem toField_powF (x : F) (n : Nat) : FastField.toField (powF x n) = FastField.toField x ^ n := by
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

theorem qZh_ne (d l : Nat) (h : d + l ≤ 24) : ∀ x ∈ qZh d l, FastField.toField x ≠ 0 := by
  intro x hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hx
  have hi : i.val < 2 ^ (d + l) :=
    lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  rw [toField_sub, toField_powF, toField_qPoints d l _ hi, toField_one, sub_ne_zero]
  exact genPoint_pow_ne _ _ h d (by omega)

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

theorem toField_invZh (d l r : Nat) (h : d + l ≤ 24) (hr : r < 2 ^ (d + l)) :
    FastField.toField ((batchInv (qZh d l)).getD (r % 2 ^ l) 0) =
      (qpt (d + l) r ^ 2 ^ d - 1)⁻¹ := by
  have hk : r % 2 ^ l < (qZh d l).size := by
    rw [qZh, Array.size_ofFn]
    exact Nat.mod_lt _ (Nat.two_pow_pos l)
  rw [toField_batchInv _ (qZh_ne d l h) _ hk, toField_qZh d l r h]

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

theorem toField_qTrans (d l r : Nat) (hr : r < 2 ^ (d + l)) :
    FastField.toField ((qTrans d l).getD r 0) = qpt (d + l) r - (tw d)⁻¹ := by
  rw [qTrans, Fast.getD_map_lt _ _ _ (by rw [qPoints, size_cosetPoints]; exact hr) _ 0,
    toField_sub, toField_qPoints d l r hr, toField_inv]

end QuotientValues

end CompStark.Stark
