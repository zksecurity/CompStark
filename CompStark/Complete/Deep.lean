/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Defs
public import CompStark.Complete.Merkle
public import CompStark.Complete.Lde
public import CompStark.Stark.Fast.Openings
public import CompStark.Stark.Fast.Lde
public import CompStark.Fri.Shapes
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.LinearCombination

/-! # The batched quotients of the DEEP opening

`Fri.reduce` sums, per height, `α^k (p(z) - p(x)) / (z - x)` over the committed columns `p` and
their opening points `z`, at every row `x = g · ω ^ bitrev r` of the extended domain.

* With true openings `p(z)`, each summand is the value at `x` of `(p(z) - p(X)) / (z - X)`, a
  polynomial of degree below `deg p` since `z` is a root of `p(z) - p(X)` (`eval_divPoly`,
  `degree_divPoly`). `z` outside the base field keeps `z - x` invertible, so the batch inversion
  computes true inverses. Composed with `X ↦ g X`, the batch is a polynomial in `ω ^ bitrev r` of
  degree below `2 ^ (h - b) - 1` for an LDE of height `2 ^ h` and blowup `2 ^ b`
  (`reduceStep_lowDeg`), so every batched quotient is low degree (`reduce_lowDegree`).
* The verifier recomputes the batched quotients at a query from the opened rows, column by column
  with the running power of `α`; the prover sums point by point with the batched row. Both are
  `∑ᵢ α ^ (k + i) (yᵢ - vᵢ) / (z - x)` (`toSpec_termStep`, `toSpec_foldl_column`), so the
  verifier's running sums are the prover's at the queried rows (`reduceQuery_honest`). At the
  blowup height the polynomials are constants and the quotients vanish.
-/

@[expose] public section
namespace CompStark
open CompStark.Stark CompStark.Fri Polynomial Montgomery.Native32
open CompStark.Stark.Fast (crow termStep termsStep yzOf powers)

variable {F : Type} [BaseField F]
variable {EF : Type} [Challenge F EF]
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F
local notation "K" => Challenge.Spec EF
local notation "ι" => algebraMap F (Challenge.Spec EF)

namespace Deep

/-! ### Arithmetic through `toSpec` -/

theorem toSpec_pow (x : EF) (n : Nat) :
    Challenge.toSpec (Ext.pow x n) = Challenge.toSpec x ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases n with
    | zero => rw [Ext.pow, pow_zero, Challenge.toSpec_one]
    | succ k =>
      rw [Ext.pow]
      have h := Nat.div_add_mod (k + 1) 2
      split_ifs with hp
      · rw [Challenge.toSpec_mul, ih _
          (by omega), Challenge.toSpec_mul, ← sq, ← pow_mul, ← pow_succ']
        exact congrArg (Challenge.toSpec x ^ ·) (by omega)
      · rw [ih _ (by omega), Challenge.toSpec_mul, ← sq, ← pow_mul]
        exact congrArg (Challenge.toSpec x ^ ·) (by omega)

theorem toSpec_ofBase (x : F) : Challenge.toSpec (Ext.ofBase x : EF) = ι (x) :=
  Challenge.toSpec_ofBase x

theorem toSpec_foldl_range (f : Nat → EF) (a : EF) (w : Nat) :
    Challenge.toSpec ((List.range w).foldl (fun s i ↦ s + f i) a) =
      Challenge.toSpec a + ∑ i ∈ Finset.range w, Challenge.toSpec (f i) := by
  induction w with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ w ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Challenge.toSpec_add,
      ih, Finset.sum_range_succ, add_assoc]

theorem powers_getD (alpha : EF) (w i : Nat) (hi : i < w) :
    (powers alpha w).getD i 0 = Ext.pow alpha i :=
  CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hi _

/-- A point's term at a row, through `toSpec`: `∑ᵢ α ^ (cnt + i) (yᵢ - vᵢ) / (z - x)`. -/
theorem toSpec_termStep (alpha z acc : EF) (V : Array F) (ys : Array EF) (w r cnt : Nat)
    (x : F) : Challenge.toSpec (termStep (crow V (powers alpha w) w r) x acc
      (z, yzOf (powers alpha w) w ys, Ext.pow alpha cnt)) =
      Challenge.toSpec acc + ∑ i ∈ Finset.range w, Challenge.toSpec alpha ^ (cnt + i) *
        (Challenge.toSpec (ys.getD i 0) - ι ((V.getD (r * w + i) 0))) *
        (Challenge.toSpec z - ι (x))⁻¹ := by
  rw [termStep, crow, ← List.range_eq_range', yzOf]
  dsimp only
  rw [Challenge.toSpec_add, Challenge.toSpec_mul, Challenge.toSpec_mul, Challenge.toSpec_sub,
      Challenge.toSpec_inv,
    Challenge.toSpec_sub, toSpec_ofBase, toSpec_pow, toSpec_foldl_range, toSpec_foldl_range,
    Challenge.toSpec_zero, zero_add, zero_add, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)
  rw [powers_getD _ _ _ (Finset.mem_range.mp hi), Challenge.toSpec_mul, Challenge.toSpec_smul,
    Algebra.smul_def, toSpec_pow, pow_add]
  ring

/-! ### Divided differences -/

/-- `(p(z) - p(X)) / (z - X)`. -/
noncomputable def divPoly (p : K[X]) (z : K) : K[X] := (p - C (p.eval z)) /ₘ (X - C z)

theorem eval_divPoly (p : K[X]) (z x : K) (hx : z - x ≠ 0) :
    (divPoly p z).eval x = (p.eval z - p.eval x) * (z - x)⁻¹ := by
  have h := (mul_divByMonic_eq_iff_isRoot (a := z) (p := p - C (p.eval z))).mpr (by
    rw [IsRoot.def, eval_sub, eval_C, sub_self])
  have e := congrArg (eval x) h
  rw [eval_mul, eval_sub, eval_X, eval_C, eval_sub, eval_C] at e
  rw [eq_mul_inv_iff_mul_eq₀ hx, divPoly]
  linear_combination (-1 : K) * e

theorem degree_lt_of_natDegree {p : K[X]} {n : Nat} (h : p ≠ 0 → p.natDegree < n) :
    p.degree < (n : WithBot Nat) := by
  by_cases hp : p = 0
  · rw [hp, degree_zero]; exact WithBot.bot_lt_coe n
  · exact (natDegree_lt_iff_degree_lt hp).mp (h hp)

theorem degree_divPoly (p : K[X]) (z : K) {n : Nat} (h : p.degree < (n : WithBot Nat)) :
    (divPoly p z).degree < ((n - 1 : Nat) : WithBot Nat) := by
  refine degree_lt_of_natDegree fun hD ↦ ?_
  have hf : p - C (p.eval z) ≠ 0 := fun h0 ↦ hD (by rw [divPoly, h0, zero_divByMonic])
  have hlt := natDegree_lt_natDegree hD (by
    rw [divPoly]
    exact degree_divByMonic_lt _ (X - C z) hf (by rw [degree_X_sub_C]; exact zero_lt_one))
  have hp : p ≠ 0 := fun h0 ↦ hf (by rw [h0, eval_zero, C_0, sub_zero])
  have hpn := (natDegree_lt_iff_degree_lt hp).mpr h
  have := natDegree_sub_le p (C (p.eval z))
  rw [natDegree_C, Nat.max_zero] at this
  omega

theorem degree_comp_lt {p : K[X]} (a : K) {n : Nat} (h : p.degree < (n : WithBot Nat)) :
    (p.comp (C a * X)).degree < (n : WithBot Nat) := by
  refine degree_lt_of_natDegree fun hc ↦ ?_
  have hp : p ≠ 0 := fun h0 ↦ hc (by rw [h0, zero_comp])
  have h1 := (natDegree_lt_iff_degree_lt hp).mpr h
  have h2 := (natDegree_comp_le (p := p) (q := C a * X)).trans
    (Nat.mul_le_mul_left _ ((natDegree_C_mul_le a X).trans natDegree_X_le))
  omega

/-- The polynomial in `X` whose value at `ω ^ bitrev r` is a point's term at row `r`: the divided
differences of the columns `ps` at `z`, at `g X`, batched by `α ^ (cnt + i)`. -/
noncomputable def pointPoly (a z g : K) (cnt : Nat) (ps : List F[X]) : K[X] :=
  ∑ i ∈ Finset.range ps.length, C (a ^ (cnt + i)) * (divPoly ((ps.getD i 0).map ι) z).comp (C g * X)

theorem eval_pointPoly (a z g y : K) (cnt : Nat) (ps : List F[X])
    (hy : z - g * y ≠ 0) :
    (pointPoly a z g cnt ps).eval y = ∑ i ∈ Finset.range ps.length, a ^ (cnt + i) *
      (((ps.getD i 0).map ι).eval z - ((ps.getD i 0).map ι).eval (g * y)) * (z - g * y)⁻¹ := by
  rw [pointPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, eval_divPoly _ _ _ hy, mul_assoc]

theorem degree_pointPoly (a z g : K) (cnt n : Nat) (ps : List F[X])
    (hps : ∀ p ∈ ps, p.degree < (n : WithBot Nat)) :
    (pointPoly a z g cnt ps).degree < ((n - 1 : Nat) : WithBot Nat) := by
  rw [← mem_degreeLT, pointPoly]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  rw [← smul_eq_C_mul]
  refine Submodule.smul_mem _ _ (mem_degreeLT.mpr (degree_comp_lt _ (degree_divPoly _ _ ?_)))
  have hi := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ hi]
  exact (degree_map_le).trans_lt (hps _ (List.getElem_mem hi))

/-! ### `reduceStep` row by row -/

/-- One point of a matrix of width `w` at a row with batched value `comp` and point `x`: the count
of columns so far and the running sum. -/
def ptStep (alpha : EF) (w : Nat) (comp : EF) (x : F) (s : Nat × EF)
    (p : EF × Array EF) : Nat × EF :=
  (s.1 + w, termStep comp x s.2 (p.1, yzOf (powers alpha w) w p.2, Ext.pow alpha s.1))

theorem foldl_ptStep (alpha : EF) (w : Nat) (comp : EF) (x : F) :
    ∀ (pts : List (EF × Array EF)) (c : Nat) (a : EF),
      pts.foldl (ptStep alpha w comp x) (c, a) =
        ((pts.foldl (termsStep alpha (powers alpha w) w) (c, [])).1,
          (pts.foldl (termsStep alpha (powers alpha w) w) (c, [])).2.foldl (termStep comp x) a)
  | [], _, _ => rfl
  | p :: pts, c, a => by
    rw [List.foldl_cons, List.foldl_cons, ptStep, foldl_ptStep alpha w comp x pts, termsStep,
      Fast.foldl_termsStep alpha _ w pts _ ([] ++ _)]
    simp only [List.nil_append, List.cons_append, List.foldl_cons]

/-- The running sums `reduceStep` starts a matrix from. -/
def startOf (red : List (Nat × Nat × Array EF)) (m : Mat F) : Nat × Array EF :=
  (red.lookup (Nat.log2 m.height)).getD (0, Array.replicate m.height 0)

theorem ofFn_getD_self {α : Type} (v : Array α) (d : α) (n : Nat) (h : v.size = n) :
    v = Array.ofFn (n := n) fun r ↦ v.getD r.val d := by
  subst h
  refine Array.ext (by rw [Array.size_ofFn]) fun i h1 h2 ↦ ?_
  rw [Array.getElem_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Option.getD_some]

/-- `reduceStep` row by row: every point in turn adds its term onto the running sum. -/
theorem reduceStep_eq (alpha : EF) (red : List (Nat × Nat × Array EF)) (m : Mat F)
    (pts : List (EF × Array EF)) (hpts : ∀ p ∈ pts, Ext.OutsideBase p.1)
    (hst : (startOf red m).2.size = m.height) (hxs : m.height ≤ 2 ^ Nat.log2 m.height) :
    reduceStep alpha red (m, pts) = (Nat.log2 m.height,
      (pts.foldl (termsStep alpha (powers alpha m.width) m.width) ((startOf red m).1, [])).1,
      Array.ofFn (n := m.height) fun r ↦ (pts.foldl (ptStep alpha m.width
        ((compress m (powers alpha m.width)).getD r.val 0)
        ((cosetPointsBitRev (gen : F) (Nat.log2 m.height)).getD r.val 0))
        ((startOf red m).1, (startOf red m).2.getD r.val 0)).2) ::
      red.filter (·.1 != Nat.log2 m.height) := by
  have hx : m.height ≤ (cosetPointsBitRev (gen : F) (Nat.log2 m.height)).size := by
    rw [Fast.size_cosetPointsBitRev]; exact hxs
  have e := Fast.foldl_accumulate alpha (powers alpha m.width) m.width m.height
    (compress m (powers alpha m.width)) _ hx pts hpts (startOf red m).1
    (fun r ↦ (startOf red m).2.getD r 0)
  rw [← ofFn_getD_self _ _ _ hst] at e
  unfold reduceStep
  dsimp only
  rw [show ((red.lookup (Nat.log2 m.height)).getD (0, Array.replicate m.height 0)) =
    startOf red m from rfl, e]
  congr 3
  refine congrArg Array.ofFn (funext fun r ↦ ?_)
  rw [foldl_ptStep]

/-! ### The batched quotients are low degree -/

/-- A committed matrix with its points and opened values, honest for blowup `2 ^ b` at height
`2 ^ h`: the extension of polynomials `ps`, opened outside the base field at their values. -/
def HonestItem (b h : Nat) (x : Mat F × List (EF × Array EF)) : Prop :=
  ∃ ps, Mat.IsLde b h x.1 ps ∧ ∀ y ∈ x.2, Ext.OutsideBase y.1 ∧ y.2.size = ps.length ∧
    ∀ j < ps.length, Challenge.toSpec (y.2.getD j 0) = aeval (Challenge.toSpec y.1) (ps.getD j 0)

/-- The values on `⟨ω⟩`, `ω` of order `2 ^ h`, in bit-reversed order, of a polynomial of degree
below `2 ^ (h - b) - 1`. -/
def LowDeg (b h : Nat) (v : Array EF) : Prop :=
  v.size = 2 ^ h ∧ ∃ p : K[X], p.degree < ((2 ^ (h - b) - 1 : Nat) : WithBot Nat) ∧
    ∀ r < 2 ^ h, Challenge.toSpec (v.getD r 0) =
      p.eval (ι ((twoAdicGen h)) ^ reverseBits r h)

/-- The running sums of `reduceStep`: distinct heights, each low degree. -/
def RedOk (b : Nat) (red : List (Nat × Nat × Array EF)) : Prop :=
  (red.map (·.1)).Nodup ∧ ∀ e ∈ red, b ≤ e.1 ∧ e.1 ≤ twoAdicity F ∧ LowDeg b e.1 e.2.2

/-- Stored row `r` of the coset `g · ⟨ω⟩` is `g ω ^ bitrev r`. -/
theorem cosetPointsBitRev_getD (h r : Nat) (hr : r < 2 ^ h) :
    (cosetPointsBitRev (gen : F) h).getD r 0 = gen * twoAdicGen h ^ reverseBits r h := by
  rw [Fast.cosetPointsBitRev_getD _ _ _ hr, cosetPoints_eq,
    CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _
      (CompPoly.CPolynomial.NTT.Transform.bitRevNat_lt h r), reverseBits_eq]

theorem compress_getD (m : Mat F) (ap : Array EF) (r : Nat) (hr : r < m.height) :
    (compress m ap).getD r 0 = crow m.values ap m.width r := by
  rw [Fast.compress_eq, CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hr]

theorem lookup_mem {α : Type} {red : List (Nat × α)} {h : Nat} {v : α}
    (hl : red.lookup h = some v) : (h, v) ∈ red := by
  obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
  rw [e]
  exact List.mem_append_right _ List.mem_cons_self

theorem startOf_lowDeg {b : Nat} {red : List (Nat × Nat × Array EF)} (hred : RedOk b red)
    {m : Mat F}
    {h : Nat} (hm : m.height = 2 ^ h) (hlog : Nat.log2 m.height = h) :
    LowDeg b h (startOf red m).2 := by
  unfold startOf
  rw [hlog]
  cases hl : red.lookup h with
  | none =>
    refine ⟨by rw [Option.getD_none, Array.size_replicate, hm], 0, by
      rw [degree_zero]; exact WithBot.bot_lt_coe _, fun r hr ↦ ?_⟩
    rw [Option.getD_none, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
      (by rw [Array.size_replicate, hm]; exact hr), Array.getElem_replicate, Option.getD_some,
      eval_zero]
    exact Challenge.toSpec_zero
  | some v =>
    rw [Option.getD_some]
    exact (hred.2 _ (lookup_mem hl)).2.2

/-- A point's term at row `r` of an honest matrix is the value of `pointPoly`. -/
theorem toSpec_ptStep {b h : Nat} {m : Mat F} {ps : List F[X]} (hm : Mat.IsLde b h m ps)
    (alpha a : EF) (c : Nat) (y : EF × Array EF) (hz : Ext.OutsideBase y.1)
    (hys : ∀ j < ps.length,
        Challenge.toSpec (y.2.getD j 0) = aeval (Challenge.toSpec y.1) (ps.getD j 0))
    (r : Nat) (hr : r < 2 ^ h) :
    Challenge.toSpec (ptStep alpha m.width ((compress m (powers alpha m.width)).getD r 0)
      ((cosetPointsBitRev (gen : F) h).getD r 0) (c, a) y).2 = Challenge.toSpec a +
      (pointPoly (Challenge.toSpec alpha) (Challenge.toSpec y.1) (ι (gen))
        c ps).eval
        (ι ((twoAdicGen h)) ^ reverseBits r h) := by
  obtain ⟨hw, hh, -, -, -, -, hv⟩ := hm
  have hne := sub_ofBase_ne_zero hz ((cosetPointsBitRev (gen : F) h).getD r 0)
  rw [Challenge.toSpec_sub, toSpec_ofBase, cosetPointsBitRev_getD h r hr,
    map_mul, map_pow] at hne
  rw [ptStep, compress_getD _ _ _ (by rw [hh]; exact hr), toSpec_termStep,
    cosetPointsBitRev_getD h r hr, map_mul, map_pow,
    eval_pointPoly _ _ _ _ _ _ hne, hw]
  rw [hw] at hv
  refine congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)
  have hi := Finset.mem_range.mp hi
  rw [hys i hi, hv r hr i hi, aeval_def, eval_map, eval_map, ← map_pow (algebraMap _ K),
    ← map_mul (algebraMap _ K), eval₂_hom]

/-- Accumulating honest points keeps the running sums low degree. -/
theorem foldl_ptStep_lowDeg {b h : Nat} {m : Mat F} {ps : List F[X]}
    (hm : Mat.IsLde b h m ps) (alpha : EF) :
    ∀ (pts : List (EF × Array EF)), (∀ y ∈ pts, Ext.OutsideBase y.1 ∧
      ∀ j < ps.length,
        Challenge.toSpec (y.2.getD j 0) = aeval (Challenge.toSpec y.1) (ps.getD j 0)) →
    ∀ (c : Nat) (f : Nat → EF) (p : K[X]), p.degree < ((2 ^ (h - b) - 1 : Nat) : WithBot Nat) →
      (∀ r < 2 ^ h, Challenge.toSpec (f r) =
        p.eval (ι ((twoAdicGen h)) ^ reverseBits r h)) →
      ∃ q : K[X], q.degree < ((2 ^ (h - b) - 1 : Nat) : WithBot Nat) ∧ ∀ r < 2 ^ h,
        Challenge.toSpec (pts.foldl (ptStep alpha m.width
          ((compress m (powers alpha m.width)).getD r 0) ((cosetPointsBitRev (gen : F) h).getD r 0))
          (c, f r)).2 = q.eval (ι ((twoAdicGen h)) ^ reverseBits r h)
  | [], _, _, _, p, hp, hf => ⟨p, hp, hf⟩
  | y :: pts, hpts, c, f, p, hp, hf => by
    obtain ⟨hz, hys⟩ := hpts y List.mem_cons_self
    have := foldl_ptStep_lowDeg hm alpha pts (fun y hy ↦ hpts y (List.mem_cons_of_mem _ hy))
      (c + m.width) (fun r ↦ (ptStep alpha m.width ((compress m (powers alpha m.width)).getD r 0)
        ((cosetPointsBitRev (gen : F) h).getD r 0) (c, f r) y).2)
      (p + pointPoly (Challenge.toSpec alpha) (Challenge.toSpec y.1)
        (ι (gen)) c ps)
      (by
        rw [← mem_degreeLT] at hp ⊢
        exact Submodule.add_mem _ hp (mem_degreeLT.mpr
          (degree_pointPoly _ _ _ _ _ _ hm.2.2.2.2.2.1)))
      (fun r hr ↦ by rw [toSpec_ptStep hm alpha _ c y hz hys r hr, hf r hr, eval_add])
    exact this

/-- One honest matrix keeps the running sums low degree. -/
theorem reduceStep_ok {b h : Nat} (alpha : EF) {red : List (Nat × Nat × Array EF)}
    (hred : RedOk b red) {it : Mat F × List (EF × Array EF)} (hit : HonestItem b h it) :
    RedOk b (reduceStep alpha red it) := by
  obtain ⟨ps, hm, hpts⟩ := hit
  have hh := hm.2.1
  have hlog : Nat.log2 it.1.height = h := by rw [hh, Nat.log2_two_pow]
  have hst := startOf_lowDeg hred hh hlog
  obtain ⟨hsz, p, hp, hf⟩ := hst
  rw [show it = (it.1, it.2) from rfl, reduceStep_eq alpha red it.1 it.2
    (fun y hy ↦ (hpts y hy).1) (by rw [hsz, hh]) (by rw [hlog, hh]), hlog]
  refine ⟨?_, fun e he ↦ ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem ↦ ?_, hred.1.sublist (List.filter_sublist.map _)⟩
    obtain ⟨e, he, hk⟩ := List.mem_map.mp hmem
    have := (List.mem_filter.mp he).2
    rw [hk] at this
    simp only [bne_self_eq_false, Bool.false_eq_true] at this
  · rcases List.mem_cons.mp he with rfl | he
    · refine ⟨hm.2.2.2.1, hm.2.2.2.2.1, by rw [Array.size_ofFn, hh], ?_⟩
      obtain ⟨q, hq, hv⟩ := foldl_ptStep_lowDeg hm alpha it.2
        (fun y hy ↦ ⟨(hpts y hy).1, (hpts y hy).2.2⟩) (startOf red it.1).1
        (fun r ↦ (startOf red it.1).2.getD r 0) p hp hf
      refine ⟨q, hq, fun r hr ↦ ?_⟩
      rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ (by rw [hh]; exact hr)]
      exact hv r hr
    · exact hred.2 e (List.mem_filter.mp he).1

theorem foldl_reduceStep_ok (b : Nat) (alpha : EF) :
    ∀ (items : List (Mat F × List (EF × Array EF))), (∀ x ∈ items, ∃ h, HonestItem b h x) →
      ∀ red, RedOk b red → RedOk b (items.foldl (reduceStep alpha) red)
  | [], _, _, hred => hred
  | it :: items, hitems, red, hred => by
    obtain ⟨h, hit⟩ := hitems it List.mem_cons_self
    exact foldl_reduceStep_ok b alpha items (fun x hx ↦ hitems x (List.mem_cons_of_mem _ hx)) _
      (reduceStep_ok alpha hred hit)

end Deep
open Deep

/-- The batched quotients of LDE matrices with true openings are low degree. -/
theorem reduce_lowDegree (b : Nat) (alpha : EF) (items : List (Mat F × List (EF × Array EF)))
    (hitems : ∀ x ∈ items, ∃ h ps, Mat.IsLde b h x.1 ps ∧ ∀ y ∈ x.2, Ext.OutsideBase y.1 ∧
      y.2.size = ps.length ∧ ∀ j < ps.length,
        Challenge.toSpec (y.2.getD j 0) = aeval (Challenge.toSpec y.1) (ps.getD j 0)) :
    ∀ x ∈ Fri.reduce alpha items, LowDegree x.1 (x.1 - b) x.2 := by
  intro x hx
  rw [reduce_eq] at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨-, h24, hsz, p, hp, hv⟩ := (foldl_reduceStep_ok b alpha items hitems []
    ⟨List.nodup_nil, fun _ h ↦ absurd h List.not_mem_nil⟩).2 e (List.mem_mergeSort.mp he)
  refine ⟨hsz, h24, p, hp.trans_le (WithBot.coe_le_coe.mpr (Nat.sub_le _ _)), hv⟩

namespace Deep

/-- The running sums have distinct heights `h`, each of `2 ^ h` values. -/
def RedShape (red : List (Nat × Nat × Array EF)) : Prop :=
  (red.map (·.1)).Nodup ∧ ∀ e ∈ red, e.2.2.size = 2 ^ e.1

theorem keys_reduceStep (alpha : EF) (red : List (Nat × Nat × Array EF))
    (it : Mat F × List (EF × Array EF)) (h : Nat) :
    h ∈ (reduceStep alpha red it).map (·.1) ↔ h = Nat.log2 it.1.height ∨ h ∈ red.map (·.1) := by
  simp only [reduceStep, List.map_cons, List.mem_cons, List.mem_map, List.mem_filter, bne_iff_ne,
    ne_eq]
  constructor
  · rintro (rfl | ⟨e, ⟨he, -⟩, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (rfl | ⟨e, he, rfl⟩)
    · exact Or.inl rfl
    · by_cases hk : e.1 = Nat.log2 it.1.height
      · exact Or.inl hk
      · exact Or.inr ⟨e, ⟨he, hk⟩, rfl⟩

theorem reduceStep_shape (alpha : EF) {red : List (Nat × Nat × Array EF)} (hred : RedShape red)
    {it : Mat F × List (EF × Array EF)} (hit : it.1.height = 2 ^ Nat.log2 it.1.height) :
    RedShape (reduceStep alpha red it) := by
  refine ⟨?_, fun e he ↦ ?_⟩
  · show (Nat.log2 it.1.height :: (red.filter (·.1 != Nat.log2 it.1.height)).map (·.1)).Nodup
    rw [List.nodup_cons]
    refine ⟨fun hmem ↦ ?_, hred.1.sublist (List.filter_sublist.map _)⟩
    obtain ⟨e, he, hk⟩ := List.mem_map.mp hmem
    have := (List.mem_filter.mp he).2
    rw [hk] at this
    simp only [bne_self_eq_false, Bool.false_eq_true] at this
  simp only [reduceStep, List.mem_cons, List.mem_filter] at he
  rcases he with rfl | ⟨he, -⟩
  · have hstart : (startOf red it.1).2.size = 2 ^ Nat.log2 it.1.height := by
      unfold startOf
      cases hl : red.lookup (Nat.log2 it.1.height) with
      | none => rw [Option.getD_none, Array.size_replicate, ← hit]
      | some v => rw [Option.getD_some]; exact hred.2 _ (lookup_mem hl)
    have hfold : ∀ (f : Nat × Array EF → EF × Array EF → Nat × Array EF),
        (∀ b p, (f b p).2.size = 2 ^ Nat.log2 it.1.height) → ∀ (pts : List (EF × Array EF))
        (b : Nat × Array EF), b.2.size = 2 ^ Nat.log2 it.1.height →
        (pts.foldl f b).2.size = 2 ^ Nat.log2 it.1.height := by
      intro f hf pts
      induction pts with
      | nil => intro b hb; exact hb
      | cons p pts ih => intro b _; rw [List.foldl_cons]; exact ih _ (hf b p)
    refine hfold _ (fun b p ↦ ?_) _ _ hstart
    rw [size_parChunks _ _ _ (fun _ _ ↦ size_accumulateRows ..)
      (by split <;> simp only [Nat.zero_lt_one, Nat.ofNat_pos, true_or]), ← hit]
  · exact hred.2 e he

theorem foldl_reduceStep_shape (alpha : EF) :
    ∀ (items : List (Mat F × List (EF × Array EF))),
      (∀ x ∈ items, x.1.height = 2 ^ Nat.log2 x.1.height) → ∀ red, RedShape red →
      RedShape (items.foldl (reduceStep alpha) red) ∧ ∀ h,
        (h ∈ (items.foldl (reduceStep alpha) red).map (·.1) ↔
          h ∈ red.map (·.1) ∨ ∃ x ∈ items, Nat.log2 x.1.height = h)
  | [], _, _, hred => ⟨hred, fun h ↦ by
      simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]⟩
  | it :: items, hitems, red, hred => by
    obtain ⟨h1, h2⟩ := foldl_reduceStep_shape alpha items
      (fun x hx ↦ hitems x (List.mem_cons_of_mem _ hx)) _
      (reduceStep_shape alpha hred (hitems it List.mem_cons_self))
    refine ⟨h1, fun h ↦ ?_⟩
    rw [List.foldl_cons, h2, keys_reduceStep]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | (h | h))
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h

end Deep

/-- The shape of the batched quotients: their heights are the distinct `log₂` heights of the
matrices, strictly decreasing, and the batched quotient of height `h` has `2 ^ h` values. -/
theorem reduce_heights (alpha : EF) (items : List (Mat F × List (EF × Array EF)))
    (hitems : ∀ x ∈ items, x.1.height = 2 ^ Nat.log2 x.1.height) :
    ((Fri.reduce alpha items).map (·.1)).Pairwise (· > ·) ∧
      (∀ h, h ∈ (Fri.reduce alpha items).map (·.1) ↔ ∃ x ∈ items, Nat.log2 x.1.height = h) ∧
      ∀ y ∈ Fri.reduce alpha items, y.2.size = 2 ^ y.1 := by
  obtain ⟨⟨hnd, hsz⟩, hkeys⟩ := foldl_reduceStep_shape alpha items hitems []
    ⟨List.nodup_nil, fun _ h ↦ absurd h List.not_mem_nil⟩
  rw [reduce_eq, List.map_map]
  set red := items.foldl (reduceStep alpha) []
  have hperm := List.mergeSort_perm red fun a b ↦ decide (b.1 ≤ a.1)
  refine ⟨?_, fun h ↦ ?_, fun y hy ↦ ?_⟩
  · have hs := List.pairwise_mergeSort (le := fun a b : Nat × Nat × Array EF ↦ decide (b.1 ≤ a.1))
      (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at h1 h2 ⊢; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) red
    have hn : ((red.mergeSort fun a b ↦ decide (b.1 ≤ a.1)).map (·.1)).Nodup :=
      (hperm.map _).nodup_iff.mpr hnd
    rw [List.Nodup, List.pairwise_map] at hn
    rw [List.pairwise_map]
    refine (hs.and hn).imp fun ⟨h1, h2⟩ ↦ ?_
    simp only [decide_eq_true_eq] at h1
    show _ > _
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  · show h ∈ (red.mergeSort _).map (·.1) ↔ _
    rw [(hperm.map _).mem_iff, hkeys]
    simp only [List.map_nil, List.not_mem_nil, false_or]
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    exact hsz e (hperm.mem_iff.mp he)

namespace Deep

/-! ### The verifier's loops -/

/-- A loop whose body, on states `Φ c`, yields `Φ (G c d)` runs the fold of `G`. -/
theorem forIn_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}
    (χ : δ → α) (Φ : γ → β) (G : γ → δ → γ) (Inv : γ → Prop) (f : α → β → m (ForInStep β)) :
    ∀ (l : List δ), (∀ d ∈ l, ∀ c, Inv c → f (χ d) (Φ c) = pure (.yield (Φ (G c d))) ∧
      Inv (G c d)) → ∀ c, Inv c → forIn (l.map χ) (Φ c) f = pure (Φ (l.foldl G c))
  | [], _, _, _ => rfl
  | d :: l, hf, c, hc => by
    obtain ⟨h1, h2⟩ := hf d List.mem_cons_self c hc
    rw [List.map_cons, List.forIn_cons, h1, pure_bind]
    exact forIn_map_eq χ Φ G Inv f l (fun d hd ↦ hf d (List.mem_cons_of_mem _ hd)) _ h2

/-- The verifier's column loop through `toSpec`: the running power of `α` and the sum
`∑ᵢ ap αⁱ (yᵢ - vᵢ) q`. -/
theorem toSpec_foldl_column (alpha q : EF) (ys : Nat → EF) (vs : Nat → F) (ap acc : EF)
    (w : Nat) : let r := (List.range w).foldl (fun s i ↦ (s.1 * alpha,
      s.2 + s.1 * (ys i - Ext.ofBase (vs i)) * q)) (ap, acc)
    Challenge.toSpec r.1 = Challenge.toSpec ap * Challenge.toSpec alpha ^ w ∧
      Challenge.toSpec r.2 = Challenge.toSpec acc + ∑ i ∈ Finset.range w, Challenge.toSpec ap *
        Challenge.toSpec alpha ^ i * (Challenge.toSpec (ys i) - ι ((vs i))) *
          Challenge.toSpec q := by
  induction w with
  | zero =>
    refine ⟨by rw [List.range_zero, List.foldl_nil, pow_zero, mul_one], ?_⟩
    rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ w ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h1 h2 ⊢
    refine ⟨by rw [Challenge.toSpec_mul, h1, pow_succ, mul_assoc], ?_⟩
    rw [Challenge.toSpec_add, h2, Finset.sum_range_succ, Challenge.toSpec_mul,
      Challenge.toSpec_mul, h1, Challenge.toSpec_sub, toSpec_ofBase, add_assoc]

/-- The running sums of `reduce` as the verifier keeps them at a query: the power of `α` for the
next column and the sum at the queried row of each height. -/
def atQuery (alpha : EF) (logMax index : Nat) (red : List (Nat × Nat × Array EF)) :
    List (Nat × EF × EF) :=
  red.map fun e ↦ (e.1, Ext.pow alpha e.2.1, e.2.2.getD (index >>> (logMax - e.1)) 0)

theorem lookup_atQuery (alpha : EF) (logMax index h : Nat) :
    ∀ red : List (Nat × Nat × Array EF), (atQuery alpha logMax index red).lookup h =
      (red.lookup h).map fun v ↦ (Ext.pow alpha v.1, v.2.getD (index >>> (logMax - h)) 0)
  | [] => rfl
  | e :: red => by
    rw [atQuery, List.map_cons, List.lookup_cons, List.lookup_cons]
    by_cases he : h = e.1
    · subst he
      simp only [beq_self_eq_true, Option.map_some]
    · have hb : (h == e.1) = false := beq_false_of_ne he
      simp only [hb]
      exact lookup_atQuery alpha logMax index h red

theorem shiftRight_lt {index logMax h : Nat} (hidx : index < 2 ^ logMax)
    (hh : h ≤ logMax) : index >>> (logMax - h) < 2 ^ h := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
    Nat.add_sub_cancel' hh]
  exact hidx

/-- At the blowup height the polynomials are constants: the batched quotient vanishes. -/
theorem blowup_zero {b : Nat} {red : List (Nat × Nat × Array EF)} (hred : RedOk b red) (alpha : EF)
    (logMax index : Nat) (hidx : index < 2 ^ logMax) (hb : b ≤ logMax)
    {v : EF × EF} (hl : (atQuery alpha logMax index red).lookup b = some v) : v.2 = 0 := by
  rw [lookup_atQuery] at hl
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨-, -, -, p, hp, hv⟩ := hred.2 _ (lookup_mem hu)
  rw [Nat.sub_self, Nat.pow_zero, Nat.sub_self, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
    degree_eq_bot] at hp
  apply Challenge.toSpec_injective
  rw [hv _ (shiftRight_lt hidx hb), hp, eval_zero, Challenge.toSpec_zero]

/-- The verifier's state for a point count and running sum. -/
def powPair (alpha : EF) (s : Nat × EF) : EF × EF := (Ext.pow alpha s.1, s.2)

theorem zip_toList (a : Array F) (b : Array EF) (w : Nat) (ha : a.size = w)
    (hb : b.size = w) : a.toList.zip b.toList = (List.range w).map fun j ↦
        (a.getD j 0, b.getD j 0) := by
  apply List.ext_getElem
  · simp only [List.length_zip, Array.length_toList, ha, hb, Nat.min_self, List.length_map,
      List.length_range]
  · intro j h1 h2
    simp only [List.length_zip, Array.length_toList, ha, hb, Nat.min_self] at h1
    simp only [List.getElem_zip, Array.getElem_toList, List.getElem_map, List.getElem_range,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show j < a.size by omega),
      Array.getElem?_eq_getElem (show j < b.size by omega), Option.getD_some]

theorem rowOf_getD (m : Mat F) (i j : Nat) (hj : j < m.width) :
    (rowOf m i).getD j 0 = m.values.getD (i * m.width + j) 0 :=
  CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hj _

theorem lookup_start (alpha : EF) (logMax index h : Nat) (red : List (Nat × Nat × Array EF))
    (m : Mat F) (hm : Nat.log2 m.height = h) :
    ((atQuery alpha logMax index red).lookup h).getD (1, 0) =
      powPair alpha ((startOf red m).1, (startOf red m).2.getD (index >>> (logMax - h)) 0) := by
  rw [lookup_atQuery, startOf, hm]
  cases red.lookup h with
  | none =>
    simp only [Option.map_none, Option.getD_none, powPair]
    refine Prod.ext (by rw [Ext.pow]) ?_
    show (0 : EF) = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  | some v => rfl

theorem atQuery_cons_filter (alpha : EF) (logMax index k : Nat) (e : Nat × Nat × Array EF)
    (red : List (Nat × Nat × Array EF)) :
    atQuery alpha logMax index (e :: red.filter (·.1 != k)) =
      (e.1, Ext.pow alpha e.2.1, e.2.2.getD (index >>> (logMax - e.1)) 0) ::
        (atQuery alpha logMax index red).filter (·.1 != k) := by
  rw [atQuery, atQuery, List.map_cons, List.filter_map]
  rfl

/-- One point of the verifier's loop is the prover's `ptStep` at the queried row. -/
theorem column_loop (alpha : EF) (m : Mat F) (i : Nat) (hi : i < m.height) (xv : F) (c : Nat)
    (a : EF) (y : EF × Array EF) :
    (List.range m.width).foldl (fun s j ↦ (s.1 * alpha, s.2 + s.1 *
      (y.2.getD j 0 - Ext.ofBase ((rowOf m i).getD j 0)) * (y.1 - Ext.ofBase xv)⁻¹))
      (Ext.pow alpha c, a) =
      powPair alpha (ptStep alpha m.width ((compress m (powers alpha m.width)).getD i 0) xv
        (c, a) y) := by
  obtain ⟨h1, h2⟩ := toSpec_foldl_column alpha (y.1 - Ext.ofBase xv)⁻¹ (y.2.getD · 0)
    (fun j ↦ (rowOf m i).getD j 0) (Ext.pow alpha c) a m.width
  refine Prod.ext (Challenge.toSpec_injective ?_) (Challenge.toSpec_injective ?_)
  · rw [h1, powPair, ptStep, toSpec_pow, toSpec_pow]
    exact (pow_add _ _ _).symm
  · rw [h2, powPair, ptStep, compress_getD _ _ _ hi, toSpec_termStep]
    refine congrArg _ (Finset.sum_congr rfl fun j hj ↦ ?_)
    rw [rowOf_getD _ _ _ (Finset.mem_range.mp hj), toSpec_pow, Challenge.toSpec_inv,
      Challenge.toSpec_sub, toSpec_ofBase, pow_add]

end Deep

/-- **The verifier's batched quotients at a query are the prover's**: every round commits matrices
of one height `2 ^ h` that are honest LDEs with true openings at points outside the base field, the
verifier's rounds are built as the STARK verifier builds them, and the rows are the prover's at the
query's row. -/
theorem reduceQuery_honest [Poseidon2Field F] (P : Params) (logMax index : Nat) (alpha : EF)
    (rounds : List (Committed F × List (Mat F × List (EF × Array EF))))
    (hidx : index < 2 ^ logMax)
    (hrounds : ∀ r ∈ rounds, r.2 ≠ [] ∧ r.1 = Committed.ofMats hashF compF (r.2.map (·.1)) ∧
      ∃ h ≤ logMax, ∀ x ∈ r.2, Deep.HonestItem P.logBlowup h x) :
    reduceQuery (poseidon2 F) P logMax index alpha
      (rounds.map fun r ↦ (r.1.openAt (index >>> (logMax - Nat.log2 r.1.maxHeight))).values.toList)
      (rounds.map fun r ↦ (r.1.root, r.2.map fun x ↦
        ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F), x.2.map fun y ↦ (y.1, y.2.toList)))) =
      pure ((Fri.reduce alpha (rounds.flatMap (·.2))).map fun y ↦
        (y.1, y.2.getD (index >>> (logMax - y.1)) 0)) := by
  have hb : rounds ≠ [] → P.logBlowup ≤ logMax := fun hne ↦ by
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hne', -, h, hh, hits⟩ := hrounds r hr
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne'
    obtain ⟨ps, hm, -⟩ := hits x hx
    exact hm.2.2.2.1.trans hh
  unfold reduceQuery
  rw [List.zip_map']
  simp only [List.forIn_pure_yield_eq_foldl]
  rw [show ([] : List (Nat × EF × EF)) = Deep.atQuery alpha logMax index [] from rfl]
  rw [Deep.forIn_map_eq _ (Deep.atQuery alpha logMax index)
    (fun red r ↦ r.2.foldl (reduceStep alpha) red) (Deep.RedOk P.logBlowup) _ rounds ?hf []
    ⟨List.nodup_nil, fun _ h ↦ absurd h List.not_mem_nil⟩, pure_bind]
  case hf =>
    intro r hr red hred
    obtain ⟨hne, hc, h, hh, hits⟩ := hrounds r hr
    obtain ⟨c, its⟩ := r
    dsimp only at hne hc hits ⊢
    subst hc
    have hH : ∀ x ∈ its, x.1.height = 2 ^ h ∧ x.1.values.size = x.1.width * x.1.height := by
      intro x hx
      obtain ⟨ps, hm, -⟩ := hits x hx
      exact ⟨hm.2.1, hm.2.2.1⟩
    have hlog : ∀ x ∈ its, Nat.log2 x.1.height - P.logBlowup + P.logBlowup = h := by
      intro x hx
      obtain ⟨ps, hm, -⟩ := hits x hx
      rw [hm.2.1, Nat.log2_two_pow, Nat.sub_add_cancel hm.2.2.2.1]
    have hne' : its.map (·.1) ≠ [] := by rwa [Ne, List.map_eq_nil_iff]
    have hms : ∀ m ∈ its.map (·.1), m.height = 2 ^ h ∧ m.values.size = m.width * m.height := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      exact hH x hx
    have hmx : (Committed.ofMats hashF compF (its.map (·.1))).maxHeight = 2 ^ h :=
      Fri.maxHeight_ofMats _ _ hne' fun m hm ↦ (hms m hm).1
    have hok := Deep.foldl_reduceStep_ok P.logBlowup alpha its (fun x hx ↦ ⟨h, hits x hx⟩) red
      hred
    refine ⟨?_, hok⟩
    rw [hmx]
    simp only [Nat.log2_two_pow, Fri.openAt_values _ h (fun m hm ↦ (hms m hm).1),
      List.toList_toArray, List.map_map, List.zip_map']
    rw [Deep.forIn_map_eq _ (Deep.atQuery alpha logMax index) (reduceStep alpha)
      (Deep.RedOk P.logBlowup) _ its ?hf2 red hred, pure_bind]
    case hf2 =>
      intro x hx red' hred'
      refine ⟨?_, Deep.reduceStep_ok alpha hred' (hits x hx)⟩
      have hl := hlog x hx
      obtain ⟨ps, hm, hpts⟩ := hits x hx
      obtain ⟨m, pts⟩ := x
      dsimp only at hl hm hpts ⊢
      have hlog2 : Nat.log2 m.height = h := by rw [hm.2.1, Nat.log2_two_pow]
      have hrow : (rowOf m (index >>> (logMax - h))).size = m.width := Array.size_ofFn
      simp only [Function.comp_apply, hl]
      rw [Deep.lookup_start alpha logMax index h red' m hlog2]
      have hi : index >>> (logMax - h) < m.height := by
        rw [hm.2.1]; exact Deep.shiftRight_lt hidx hh
      rw [Deep.forIn_map_eq _ (Deep.powPair alpha) (Deep.ptStep alpha m.width
        ((compress m (powers alpha m.width)).getD (index >>> (logMax - h)) 0)
        (gen * powF (twoAdicGen h) (reverseBits (index >>> (logMax - h)) h))) (fun _ ↦ True) _ pts
        ?hf3 _ trivial]
      case hf3 =>
        intro y hy s _
        refine ⟨?_, trivial⟩
        obtain ⟨c, a⟩ := s
        have hy2 : y.2.size = m.width := by rw [(hpts y hy).2.1, hm.1]
        have hz : y.1 - Ext.ofBase (gen * powF (twoAdicGen h) (reverseBits (index >>>
            (logMax - h)) h)) ≠ 0 := fun he ↦ toSpec_ne_ofBase (hpts y hy).1 _ (by
          have := congrArg Challenge.toSpec he
          rwa [Challenge.toSpec_sub, Challenge.toSpec_zero, sub_eq_zero,
            Challenge.toSpec_ofBase] at this)
        have hz' : (y.1 - Ext.ofBase (gen * powF (twoAdicGen h) (reverseBits (index >>>
            (logMax - h)) h)) != 0) = true := bne_iff_ne.mpr hz
        simp only [Array.length_toList, hy2, hrow, beq_self_eq_true, ensure, ↓reduceIte,
          pure_bind, hz', Deep.zip_toList _ _ m.width hrow hy2, List.foldl_map, Prod.mk.eta]
        rw [show Deep.powPair alpha (c, a) = (Ext.pow alpha c, a) from rfl, Deep.column_loop]
        rw [hm.2.1]
        exact Deep.shiftRight_lt hidx hh
      have hst := Deep.startOf_lowDeg hred' hm.2.1 hlog2
      rw [pure_bind, Deep.reduceStep_eq alpha red' m pts (fun y hy ↦ (hpts y hy).1)
        (by rw [hst.1, hm.2.1]) (by rw [hlog2, hm.2.1]), Deep.atQuery_cons_filter, hlog2,
        CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hi,
        Deep.cosetPointsBitRev_getD h _ (by rw [← hm.2.1]; exact hi), Deep.powPair,
        Deep.foldl_ptStep, Deep.foldl_ptStep, powF_eq]
  rw [← List.foldl_flatMap]
  have hok := Deep.foldl_reduceStep_ok P.logBlowup alpha (rounds.flatMap (·.2)) (fun x hx ↦ by
      obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨-, -, h, -, hits⟩ := hrounds r hr
      exact ⟨h, hits x hx⟩) [] ⟨List.nodup_nil, fun _ h ↦ absurd h List.not_mem_nil⟩
  have htail : ((Deep.atQuery alpha logMax index ((rounds.flatMap (·.2)).foldl (reduceStep alpha)
      [])).mergeSort (fun a b ↦ decide (b.1 ≤ a.1))).map (fun x ↦ (x.1, x.2.2)) =
      (Fri.reduce alpha (rounds.flatMap (·.2))).map fun y ↦
        (y.1, y.2.getD (index >>> (logMax - y.1)) 0) := by
    rw [reduce_eq, List.map_map, Deep.atQuery,
      ← List.map_mergeSort (l := List.foldl (reduceStep alpha) [] (rounds.flatMap Prod.snd))
        (f := fun e : Nat × Nat × Array EF ↦
          (e.1, Ext.pow alpha e.2.1, e.2.2.getD (index >>> (logMax - e.1)) 0))
        (r := fun a b ↦ decide (b.1 ≤ a.1)) (s := fun a b ↦ decide (b.1 ≤ a.1))
        (fun _ _ _ _ ↦ rfl), List.map_map]
    rfl
  split
  · rename_i v w hl
    have hne : rounds ≠ [] := by
      rintro rfl
      exact absurd hl (by simp only [List.flatMap_nil, List.foldl_nil]; exact nofun)
    have h0 : w = 0 := Deep.blowup_zero hok alpha logMax index hidx (hb hne) (v := (v, w)) hl
    simp only [h0, beq_self_eq_true, ensure, ↓reduceIte, pure_bind, htail]
  · exact congrArg pure htail

end CompStark
