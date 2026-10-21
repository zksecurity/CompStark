/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Constraints
public import CompStark.Stark.Points
public import CompStark.Stark.Verifier

/-! # The verifier's constraint check in the spec field

The verifier recomposes the quotient at `ζ` from its chunks and checks the folded constraints
there (`recompose`, `checkConstraints`). In the spec field:

* `chunkSel`: the selector of chunk `c`, `∏_{d ≠ c} Z_{D_d}(y) / Z_{D_d}(s_c)` over the chunks'
  cosets `D_d = s_d ⟨ω⟩`, `s_d = g ω_qᵈ` the quotient points `qpt`. It is `1` on its own coset and
  `0` on the others (`chunkSel_coset`), so chunks that agree with a polynomial on their cosets
  recompose to it (`sum_chunkSel`).
* `toSpec_recompose`: the verifier's recomposition is `∑_c L_c(ζ) q_c(ζ)`.
* `toSpec_foldedConstraints`: the folded constraints are Horner's rule in `α`.

`vRounds` are the verifier's opening rounds of a proof.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "E" => Challenge.Spec EF

/-- The quotient domain's point `g ω_qʳ`, `ω_q` of order `2 ^ q`. -/
abbrev qpt (q r : Nat) : F := gen * twoAdicGen q ^ r

/-- `Ext.pow` is the power in the spec field. -/
theorem toSpec_extPow (x : EF) (n : Nat) :
    Challenge.toSpec (Ext.pow x n) = Challenge.toSpec x ^ n :=
  Ext.toSpec_pow x n

/-- `Ext.powTwo` is `x ^ 2 ^ k` in the spec field. -/
theorem toSpec_extPowTwo (x : EF) (k : Nat) :
    Challenge.toSpec (Ext.powTwo x k) = Challenge.toSpec x ^ 2 ^ k :=
  Ext.toSpec_powTwo x k

/-! ### The verifier's rounds -/

/-- The verifier's rounds of a proof: the trace opened at `ζ` and `ζ ω`, the quotient's chunks at
`ζ`. -/
def vRounds (proof : Proof F EF) (zeta : EF) : List (Round F EF) :=
  let o := proof.opened
  let traceDomain : Domain F := ⟨1, proof.degreeBits⟩
  [(proof.traceCommit, [(traceDomain, [(zeta, o.traceLocal.toList),
      (zeta * Ext.ofBase (twoAdicGen proof.degreeBits), o.traceNext.toList)])]),
    (proof.quotientCommit, o.quotientChunks.toList.map fun ch ↦
      (traceDomain, [(zeta, ch.toList)]))]

/-! ### Recomposing the quotient from its chunks -/

/-- The vanishing polynomial `Z_D(y) = (y / s) ^ n - 1` of the coset `D = s · ⟨ω⟩`, `n = 2 ^ logN`,
at `y`. -/
noncomputable def vanish (logN : Nat) (s : F) (y : E) : E :=
  (y * algebraMap F E s⁻¹) ^ 2 ^ logN - 1

/-- The selector of chunk `c` at `y`: `∏_{d ≠ c} Z_{D_d}(y) / Z_{D_d}(s_c)`, `s_c = g ω_qᶜ`. -/
noncomputable def chunkSel (logN lc c : Nat) (y : E) : E :=
  ∏ d ∈ (Finset.range (2 ^ lc)).erase c, vanish logN (qpt (logN + lc) d) y *
    (vanish logN (qpt (logN + lc) d) (algebraMap F E (qpt (logN + lc) c)))⁻¹

variable (EF) in
/-- The chunk selector as a polynomial. -/
noncomputable def chunkSelPoly (logN lc c : Nat) : E[X] :=
  ∏ d ∈ (Finset.range (2 ^ lc)).erase c, ((X * C (algebraMap F E (qpt (logN + lc) d)⁻¹)) ^ 2 ^ logN
    - 1) * C (vanish logN (qpt (logN + lc) d) (algebraMap F E (qpt (logN + lc) c)))⁻¹

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
  have : (X * C (algebraMap F E (qpt (logN + lc) d)⁻¹)).natDegree ≤ 1 :=
    (natDegree_mul_C_le _ _).trans natDegree_X_le
  calc 2 ^ logN * (X * C (algebraMap F E (qpt (logN + lc) d)⁻¹)).natDegree ≤ 2 ^ logN * 1 :=
        Nat.mul_le_mul_left _ this
    _ = 2 ^ logN := Nat.mul_one _

/-- A degree bound from a `natDegree` bound. -/
theorem degree_lt_of_natDegree_lt'' {p : E[X]} {N : Nat} (h : p.natDegree < N) :
    p.degree < (N : WithBot Nat) :=
  degree_le_natDegree.trans_lt (by exact_mod_cast h)

/-- Quotient points are nonzero. -/
theorem qpt_ne_zero (q m : Nat) (h : q ≤ twoAdicity F) : qpt (F := F) q m ≠ 0 :=
  mul_ne_zero BaseField.gen_ne_zero (pow_ne_zero _ (BaseField.twoAdicGen_ne_zero q h))

/-- The point `r` of coset `c` is the quotient domain's point `c + k r`. -/
theorem qpt_coset (logN lc c r : Nat) (h : logN + lc ≤ twoAdicity F) :
    qpt (F := F) (logN + lc) c * twoAdicGen logN ^ r = qpt (logN + lc) (c + 2 ^ lc * r) := by
  rw [qpt, qpt, pow_add, pow_mul, BaseField.twoAdicGen_pow logN lc h, mul_assoc]

/-- `Z_{D_d}` takes the same value on all of `D_c`. -/
theorem vanish_coset (logN lc c d r : Nat) (h : logN + lc ≤ twoAdicity F) :
    vanish logN (qpt (logN + lc) d) (algebraMap F E (qpt (logN + lc) c * twoAdicGen logN ^ r)) =
      vanish logN (qpt (logN + lc) d) (algebraMap F E (qpt (logN + lc) c)) := by
  simp only [vanish, ← map_mul, ← map_pow]
  rw [mul_right_comm, mul_pow, ← pow_mul, Nat.mul_comm, pow_mul,
      twoAdicGen_pow_self logN (by omega), one_pow,
    mul_one]

/-- `Z_{D_c}(s_c) = 0`. -/
theorem vanish_self (logN lc c : Nat) (h : logN + lc ≤ twoAdicity F) :
    vanish logN (qpt (logN + lc) c) (algebraMap F E (qpt (logN + lc) c)) = 0 := by
  rw [vanish, ← map_mul, mul_inv_cancel₀ (qpt_ne_zero _ c h), map_one, one_pow, sub_self]

/-- Distinct chunks' cosets are disjoint: `Z_{D_d}(s_c) ≠ 0`. -/
theorem vanish_ne_zero (logN lc c d : Nat) (h : logN + lc ≤ twoAdicity F) (hc : c < 2 ^ lc)
    (hd : d < 2 ^ lc) (hcd : d ≠ c) :
    vanish logN (qpt (logN + lc) d) (algebraMap F E (qpt (logN + lc) c)) ≠ 0 := by
  rw [vanish, ← map_mul, ← map_pow, ← map_one (algebraMap F E), ← map_sub, ne_eq,
    map_eq_zero_iff _ (algebraMap F E).injective, sub_eq_zero]
  intro he
  have hp := BaseField.isPrimitiveRoot_twoAdicGen (F := F) (logN + lc) h
  have hp' : IsPrimitiveRoot (twoAdicGen (logN + lc) ^ 2 ^ logN) (2 ^ lc) :=
    hp.pow (Nat.two_pow_pos _) (Nat.pow_add 2 logN lc)
  have hg := BaseField.gen_ne_zero (F := F)
  have hw := BaseField.twoAdicGen_ne_zero (F := F) (logN + lc) h
  rw [qpt, qpt, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hg, one_mul, mul_pow, inv_pow,
    ← pow_mul, ← pow_mul, Nat.mul_comm c, Nat.mul_comm d, pow_mul, pow_mul,
    mul_inv_eq_one₀ (pow_ne_zero _ (pow_ne_zero _ hw))] at he
  exact hcd (hp'.pow_inj hd hc he.symm)

/-- The chunk selector is `1` on its own coset and `0` on the others. -/
theorem chunkSel_coset (logN lc c c' r : Nat) (h : logN + lc ≤ twoAdicity F) (hc : c < 2 ^ lc)
    (hc' : c' < 2 ^ lc) :
    chunkSel logN lc c (algebraMap F E (qpt (logN + lc) c' * twoAdicGen logN ^ r)) =
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
theorem sum_chunkSel (logN lc : Nat) (h : logN + lc ≤ twoAdicity F) (Q : E[X])
    (hQ : Q.natDegree < 2 ^ (logN + lc)) (qc : Nat → E[X])
    (hqd : ∀ c < 2 ^ lc, (qc c).natDegree < 2 ^ logN)
    (hqa : ∀ c < 2 ^ lc, ∀ r < 2 ^ logN,
      (qc c).eval (algebraMap F E (qpt (logN + lc) c * twoAdicGen logN ^ r)) =
        Q.eval (algebraMap F E (qpt (logN + lc) c * twoAdicGen logN ^ r))) (y : E) :
    ∑ c ∈ Finset.range (2 ^ lc), chunkSel logN lc c y * (qc c).eval y = Q.eval y := by
  set P : E[X] := ∑ c ∈ Finset.range (2 ^ lc), chunkSelPoly EF logN lc c * qc c
  have hP : P = Q := by
    have hp := BaseField.isPrimitiveRoot_twoAdicGen (F := F) (logN + lc) h
    refine eq_of_degree_sub_lt_of_eval_index_eq (Finset.range (2 ^ (logN + lc)))
      (v := fun m ↦ algebraMap F E (qpt (logN + lc) m)) (fun i hi j hj hij ↦ ?_) ?_
      (fun m hm ↦ ?_)
    · have := (algebraMap F E).injective hij
      simp only [qpt] at this
      exact hp.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        (mul_left_cancel₀ BaseField.gen_ne_zero this)
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
      have hpt : qpt (F := F) (logN + lc) m =
          qpt (logN + lc) (m % 2 ^ lc) * twoAdicGen logN ^ (m / 2 ^ lc) := by
        rw [qpt_coset logN lc _ _ h, Nat.mod_add_div]
      rw [hpt, eval_finsetSum, Finset.sum_eq_single (m % 2 ^ lc) (fun c hc hne ↦ ?_)
        (fun hn ↦ absurd (Finset.mem_range.mpr hc') hn), eval_mul, eval_chunkSelPoly,
        chunkSel_coset logN lc _ _ _ h hc' hc', ite_eq_left_of_eq_true _ _ (eq_true rfl), one_mul,
        hqa _ hc' _ hr]
      rw [eval_mul, eval_chunkSelPoly, chunkSel_coset logN lc _ _ _ h (Finset.mem_range.mp hc) hc',
        ite_eq_right_of_eq_false _ _ (eq_false hne), zero_mul]
  rw [← hP, eval_finsetSum]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [eval_mul, eval_chunkSelPoly]

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
abbrev chunkDomain (logN lc i : Nat) : Domain F :=
  ⟨gen * powF (twoAdicGen (logN + lc)) i, logN⟩

/-- Chunk `i`'s shift is the quotient point `i`. -/
theorem chunkShift_eq (logN lc i : Nat) :
    (chunkDomain (F := F) logN lc i).shift = qpt (logN + lc) i := by
  rw [chunkDomain, powF_eq]

/-- The verifier's vanishing polynomial of chunk `i`'s coset. -/
theorem toSpec_vanishingAt (logN lc i : Nat) (p : EF) :
    Challenge.toSpec (vanishingAt (chunkDomain logN lc i) p) =
      vanish logN (qpt (logN + lc) i) (Challenge.toSpec p) := by
  rw [vanishingAt, Challenge.toSpec_sub, toSpec_extPowTwo, Challenge.toSpec_mul,
    Challenge.toSpec_ofBase,
    Challenge.toSpec_one, vanish, chunkShift_eq,
    CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- Chunk shifts are distinct. -/
theorem chunkShift_beq (logN lc i j : Nat) (h : logN + lc ≤ twoAdicity F) (hi : i < 2 ^ lc)
    (hj : j < 2 ^ lc) :
    ((chunkDomain (F := F) logN lc j).shift != (chunkDomain logN lc i).shift) = (j != i) := by
  by_cases hij : j = i
  · rw [hij]; simp only [bne_self_eq_false]
  · have hne : (chunkDomain (F := F) logN lc j).shift ≠ (chunkDomain logN lc i).shift :=
      fun he ↦ by
      have := he
      rw [chunkShift_eq, chunkShift_eq, qpt, qpt] at this
      have hp := BaseField.isPrimitiveRoot_twoAdicGen (F := F) (logN + lc) h
      have hk : 2 ^ lc ≤ 2 ^ (logN + lc) := Nat.pow_le_pow_right (by omega) (by omega)
      exact hij (hp.pow_inj (by omega) (by omega) (mul_left_cancel₀ BaseField.gen_ne_zero this))
    rw [bne_iff_ne.mpr hne, bne_iff_ne.mpr hij]

/-- The verifier's selector of chunk `i` is `chunkSel`. -/
theorem toSpec_selector (logN lc i : Nat) (h : logN + lc ≤ twoAdicity F) (hi : i < 2 ^ lc)
    (z : EF) :
    Challenge.toSpec (((chunkDomains logN lc).filter fun dj ↦
      dj.shift != (chunkDomain logN lc i).shift).foldl
      (fun acc dj ↦ acc * vanishingAt dj z *
        (vanishingAt dj (Ext.ofBase (chunkDomain logN lc i).shift))⁻¹) 1) =
      chunkSel logN lc i (Challenge.toSpec z) := by
  have hds : chunkDomains (F := F) logN lc = (List.range (2 ^ lc)).map (chunkDomain logN lc) :=
    rfl
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
  rw [toSpec_vanishingAt, toSpec_vanishingAt, Challenge.toSpec_ofBase, powF_eq,
    ← CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- The verifier's per-chunk sum of the `d` coordinates. -/
abbrev chunkInner (ch : Array EF) : EF :=
  (List.range (Challenge.d EF)).foldl (fun s e ↦ s + Ext.basis e * ch.getD e 0) 0

/-- **The verifier's recomposition** is `∑_c L_c(ζ) q_c(ζ)` with the chunks' values. -/
theorem toSpec_recompose (logN lc : Nat) (h : logN + lc ≤ twoAdicity F) (chs : Nat → Array EF)
    (z : EF) :
    Challenge.toSpec (recompose (chunkDomains logN lc) ((List.range (2 ^ lc)).map chs) z) =
      ∑ c ∈ Finset.range (2 ^ lc),
        chunkSel logN lc c (Challenge.toSpec z) * Challenge.toSpec (chunkInner (chs c)) := by
  have hds : chunkDomains (F := F) logN lc = (List.range (2 ^ lc)).map (chunkDomain logN lc) :=
    rfl
  unfold recompose
  rw [hds, List.map_map]
  simp only [List.zip_map', List.foldl_map, Function.comp_apply]
  rw [toSpec_foldl_add, Challenge.toSpec_zero, zero_add, list_sum_range]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [Challenge.toSpec_mul, ← hds]
  exact congrArg (· * _) (toSpec_selector logN lc c h (Finset.mem_range.mp hc) z)

/-! ### The verifier's check -/

/-- The verifier's per-chunk sum in the spec field. -/
theorem toSpec_chunkInner (ch : Array EF) : Challenge.toSpec (chunkInner ch) =
    ∑ e ∈ Finset.range (Challenge.d EF),
      Challenge.toSpec (Ext.basis e : EF) * Challenge.toSpec (ch.getD e 0) := by
  rw [chunkInner, toSpec_foldl_add, Challenge.toSpec_zero, zero_add, ← list_sum_range]
  simp only [Challenge.toSpec_mul]

/-- The verifier's folded constraints are Horner's rule in `α`. -/
theorem toSpec_foldedConstraints (A : Air F) (env : Expr.Env F EF) (alpha : EF) :
    Challenge.toSpec (foldedConstraints A env alpha) = horner
      (A.constraints.map fun c ↦ Challenge.toSpec (c.eval env)) (Challenge.toSpec alpha) := by
  suffices h : ∀ (l : List (Expr F)) (x : EF), Challenge.toSpec (l.foldl (fun acc c ↦ acc * alpha +
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

/-- `checkConstraints` as a function. Rewriting with it, rather than unfolding the definition at
its arguments, keeps the kernel from evaluating the final `==` on symbolic extension elements. -/
theorem checkConstraints_eq_fun : checkConstraints = fun (A : Air F) (pis : List F)
    (opened : OpenedValues EF) (degreeBits : Nat) (zeta alpha quotient : EF) ↦
  let gInv := Ext.ofBase (twoAdicGen degreeBits)⁻¹
  let zh := Ext.powTwo zeta degreeBits - 1
  let env : Expr.Env F EF := {
    cur := fun i ↦ opened.traceLocal.getD i 0
    next := fun i ↦ opened.traceNext.getD i 0
    pub := fun i ↦ Ext.ofBase (pis.getD i 0)
    const := Ext.ofBase
    isFirstRow := zh * (zeta - 1)⁻¹
    isLastRow := zh * (zeta - gInv)⁻¹
    isTransition := zeta - gInv }
  foldedConstraints A env alpha * zh⁻¹ == quotient := rfl

end CompStark.Stark
