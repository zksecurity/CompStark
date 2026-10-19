/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Defs
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
  verifier's running sums are the prover's at the queried rows (`openInput_honest`). At the
  blowup height the polynomials are constants and the quotients vanish.
-/

@[expose] public section
namespace CompStark
open CompStark.Stark CompStark.Fri Polynomial Montgomery.Native32
open CompStark.Stark.Fast (crow termStep termsStep yzOf powers)
open KoalaBear.Fast (Ext4)

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4
local notation "K" => KoalaBear.Ext4
local notation "ι" => algebraMap KoalaBear.Field KoalaBear.Ext4

namespace Deep

/-! ### Arithmetic through `toSpec` -/

theorem toSpec_pow (x : EF) (n : Nat) : Ext4.toSpec (Ext.pow x n) = Ext4.toSpec x ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases n with
    | zero => rw [Ext.pow, pow_zero, Ext4.toSpec_one]
    | succ k =>
      rw [Ext.pow]
      have h := Nat.div_add_mod (k + 1) 2
      split_ifs with hp
      · rw [Ext4.toSpec_mul, ih _ (by omega), Ext4.toSpec_mul, ← sq, ← pow_mul, ← pow_succ']
        exact congrArg (Ext4.toSpec x ^ ·) (by omega)
      · rw [ih _ (by omega), Ext4.toSpec_mul, ← sq, ← pow_mul]
        exact congrArg (Ext4.toSpec x ^ ·) (by omega)

theorem toSpec_ofBase (x : F) : Ext4.toSpec (Ext.ofBase x) = ι (FastField.toField x) :=
  Ext4.toSpec_ofBase x

theorem toSpec_foldl_range (f : Nat → EF) (a : EF) (w : Nat) :
    Ext4.toSpec ((List.range w).foldl (fun s i ↦ s + f i) a) =
      Ext4.toSpec a + ∑ i ∈ Finset.range w, Ext4.toSpec (f i) := by
  induction w with
  | zero => rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ w ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Ext4.toSpec_add, ih,
      Finset.sum_range_succ, add_assoc]

theorem powers_getD (alpha : EF) (w i : Nat) (hi : i < w) :
    (powers alpha w).getD i 0 = Ext.pow alpha i :=
  CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hi _

/-- A point's term at a row, through `toSpec`: `∑ᵢ α ^ (cnt + i) (yᵢ - vᵢ) / (z - x)`. -/
theorem toSpec_termStep (alpha z acc : EF) (V : Array F) (ys : Array EF) (w r cnt : Nat) (x : F) :
    Ext4.toSpec (termStep (crow V (powers alpha w) w r) x acc
      (z, yzOf (powers alpha w) w ys, Ext.pow alpha cnt)) =
      Ext4.toSpec acc + ∑ i ∈ Finset.range w, Ext4.toSpec alpha ^ (cnt + i) *
        (Ext4.toSpec (ys.getD i 0) - ι (FastField.toField (V.getD (r * w + i) 0))) *
        (Ext4.toSpec z - ι (FastField.toField x))⁻¹ := by
  rw [termStep, crow, ← List.range_eq_range', yzOf]
  dsimp only
  rw [Ext4.toSpec_add, Ext4.toSpec_mul, Ext4.toSpec_mul, Ext4.toSpec_sub, Ext4.toSpec_inv,
    Ext4.toSpec_sub, toSpec_ofBase, toSpec_pow, toSpec_foldl_range, toSpec_foldl_range,
    Ext4.toSpec_zero, zero_add, zero_add, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)
  rw [powers_getD _ _ _ (Finset.mem_range.mp hi), Ext4.toSpec_mul, Ext4.toSpec_smul,
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
noncomputable def pointPoly (a z g : K) (cnt : Nat) (ps : List KoalaBear.Field[X]) : K[X] :=
  ∑ i ∈ Finset.range ps.length, C (a ^ (cnt + i)) * (divPoly ((ps.getD i 0).map ι) z).comp (C g * X)

theorem eval_pointPoly (a z g y : K) (cnt : Nat) (ps : List KoalaBear.Field[X])
    (hy : z - g * y ≠ 0) :
    (pointPoly a z g cnt ps).eval y = ∑ i ∈ Finset.range ps.length, a ^ (cnt + i) *
      (((ps.getD i 0).map ι).eval z - ((ps.getD i 0).map ι).eval (g * y)) * (z - g * y)⁻¹ := by
  rw [pointPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, eval_divPoly _ _ _ hy, mul_assoc]

theorem degree_pointPoly (a z g : K) (cnt n : Nat) (ps : List KoalaBear.Field[X])
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
def ptStep (alpha : EF) (w : Nat) (comp : EF) (x : F) (s : Nat × EF) (p : EF × Array EF) :
    Nat × EF :=
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
def startOf (red : List (Nat × Nat × Array EF)) (m : Mat) : Nat × Array EF :=
  (red.lookup (Nat.log2 m.height)).getD (0, Array.replicate m.height 0)

theorem ofFn_getD_self {α : Type} (v : Array α) (d : α) (n : Nat) (h : v.size = n) :
    v = Array.ofFn (n := n) fun r ↦ v.getD r.val d := by
  subst h
  refine Array.ext (by rw [Array.size_ofFn]) fun i h1 h2 ↦ ?_
  rw [Array.getElem_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Option.getD_some]

/-- `reduceStep` row by row: every point in turn adds its term onto the running sum. -/
theorem reduceStep_eq (alpha : EF) (red : List (Nat × Nat × Array EF)) (m : Mat)
    (pts : List (EF × Array EF)) (hpts : ∀ p ∈ pts, Ext.OutsideBase p.1)
    (hst : (startOf red m).2.size = m.height) (hxs : m.height ≤ 2 ^ Nat.log2 m.height) :
    reduceStep alpha red (m, pts) = (Nat.log2 m.height,
      (pts.foldl (termsStep alpha (powers alpha m.width) m.width) ((startOf red m).1, [])).1,
      Array.ofFn (n := m.height) fun r ↦ (pts.foldl (ptStep alpha m.width
        ((compress m (powers alpha m.width)).getD r.val 0)
        ((cosetPointsBitRev gen (Nat.log2 m.height)).getD r.val 0))
        ((startOf red m).1, (startOf red m).2.getD r.val 0)).2) ::
      red.filter (·.1 != Nat.log2 m.height) := by
  have hx : m.height ≤ (cosetPointsBitRev gen (Nat.log2 m.height)).size := by
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
def HonestItem (b h : Nat) (x : Mat × List (EF × Array EF)) : Prop :=
  ∃ ps, Mat.IsLde b h x.1 ps ∧ ∀ y ∈ x.2, Ext.OutsideBase y.1 ∧ y.2.size = ps.length ∧
    ∀ j < ps.length, Ext4.toSpec (y.2.getD j 0) = aeval (Ext4.toSpec y.1) (ps.getD j 0)

/-- The values on `⟨ω⟩`, `ω` of order `2 ^ h`, in bit-reversed order, of a polynomial of degree
below `2 ^ (h - b) - 1`. -/
def LowDeg (b h : Nat) (v : Array EF) : Prop :=
  v.size = 2 ^ h ∧ ∃ p : K[X], p.degree < ((2 ^ (h - b) - 1 : Nat) : WithBot Nat) ∧
    ∀ r < 2 ^ h, Ext4.toSpec (v.getD r 0) =
      p.eval (ι (FastField.toField (twoAdicGen h)) ^ reverseBits r h)

/-- The running sums of `reduceStep`: distinct heights, each low degree. -/
def RedOk (b : Nat) (red : List (Nat × Nat × Array EF)) : Prop :=
  (red.map (·.1)).Nodup ∧ ∀ e ∈ red, b ≤ e.1 ∧ e.1 ≤ 24 ∧ LowDeg b e.1 e.2.2

/-- Stored row `r` of the coset `g · ⟨ω⟩` is `g ω ^ bitrev r`. -/
theorem cosetPointsBitRev_getD (h r : Nat) (hr : r < 2 ^ h) :
    (cosetPointsBitRev gen h).getD r 0 = gen * twoAdicGen h ^ reverseBits r h := by
  rw [Fast.cosetPointsBitRev_getD _ _ _ hr, cosetPoints_eq,
    CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _
      (CompPoly.CPolynomial.NTT.Transform.bitRevNat_lt h r), Fast.reverseBits_eq]

theorem compress_getD (m : Mat) (ap : Array EF) (r : Nat) (hr : r < m.height) :
    (compress m ap).getD r 0 = crow m.values ap m.width r := by
  rw [Fast.compress_eq, CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hr]

theorem lookup_mem {red : List (Nat × Nat × Array EF)} {h : Nat} {v : Nat × Array EF}
    (hl : red.lookup h = some v) : (h, v) ∈ red := by
  obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
  rw [e]
  exact List.mem_append_right _ List.mem_cons_self

theorem startOf_lowDeg {b : Nat} {red : List (Nat × Nat × Array EF)} (hred : RedOk b red) {m : Mat}
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
    exact Ext4.toSpec_zero
  | some v =>
    rw [Option.getD_some]
    exact (hred.2 _ (lookup_mem hl)).2.2

/-- A point's term at row `r` of an honest matrix is the value of `pointPoly`. -/
theorem toSpec_ptStep {b h : Nat} {m : Mat} {ps : List KoalaBear.Field[X]} (hm : Mat.IsLde b h m ps)
    (alpha a : EF) (c : Nat) (y : EF × Array EF) (hz : Ext.OutsideBase y.1)
    (hys : ∀ j < ps.length, Ext4.toSpec (y.2.getD j 0) = aeval (Ext4.toSpec y.1) (ps.getD j 0))
    (r : Nat) (hr : r < 2 ^ h) :
    Ext4.toSpec (ptStep alpha m.width ((compress m (powers alpha m.width)).getD r 0)
      ((cosetPointsBitRev gen h).getD r 0) (c, a) y).2 = Ext4.toSpec a +
      (pointPoly (Ext4.toSpec alpha) (Ext4.toSpec y.1) (ι (FastField.toField gen)) c ps).eval
        (ι (FastField.toField (twoAdicGen h)) ^ reverseBits r h) := by
  obtain ⟨hw, hh, -, -, -, -, hv⟩ := hm
  have hne := Fast.sub_ofBase_ne_zero hz ((cosetPointsBitRev gen h).getD r 0)
  rw [Ext4.toSpec_sub, toSpec_ofBase, cosetPointsBitRev_getD h r hr,
    toField_mul, toField_npow, map_mul, map_pow] at hne
  rw [ptStep, compress_getD _ _ _ (by rw [hh]; exact hr), toSpec_termStep,
    cosetPointsBitRev_getD h r hr, toField_mul, toField_npow, map_mul, map_pow,
    eval_pointPoly _ _ _ _ _ _ hne, hw]
  rw [hw] at hv
  refine congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)
  have hi := Finset.mem_range.mp hi
  rw [hys i hi, hv r hr i hi, aeval_def, eval_map, eval_map, ← map_pow, ← map_mul, eval₂_hom]

/-- Accumulating honest points keeps the running sums low degree. -/
theorem foldl_ptStep_lowDeg {b h : Nat} {m : Mat} {ps : List KoalaBear.Field[X]}
    (hm : Mat.IsLde b h m ps) (alpha : EF) :
    ∀ (pts : List (EF × Array EF)), (∀ y ∈ pts, Ext.OutsideBase y.1 ∧
      ∀ j < ps.length, Ext4.toSpec (y.2.getD j 0) = aeval (Ext4.toSpec y.1) (ps.getD j 0)) →
    ∀ (c : Nat) (f : Nat → EF) (p : K[X]), p.degree < ((2 ^ (h - b) - 1 : Nat) : WithBot Nat) →
      (∀ r < 2 ^ h, Ext4.toSpec (f r) =
        p.eval (ι (FastField.toField (twoAdicGen h)) ^ reverseBits r h)) →
      ∃ q : K[X], q.degree < ((2 ^ (h - b) - 1 : Nat) : WithBot Nat) ∧ ∀ r < 2 ^ h,
        Ext4.toSpec (pts.foldl (ptStep alpha m.width
          ((compress m (powers alpha m.width)).getD r 0) ((cosetPointsBitRev gen h).getD r 0))
          (c, f r)).2 = q.eval (ι (FastField.toField (twoAdicGen h)) ^ reverseBits r h)
  | [], _, _, _, p, hp, hf => ⟨p, hp, hf⟩
  | y :: pts, hpts, c, f, p, hp, hf => by
    obtain ⟨hz, hys⟩ := hpts y List.mem_cons_self
    have := foldl_ptStep_lowDeg hm alpha pts (fun y hy ↦ hpts y (List.mem_cons_of_mem _ hy))
      (c + m.width) (fun r ↦ (ptStep alpha m.width ((compress m (powers alpha m.width)).getD r 0)
        ((cosetPointsBitRev gen h).getD r 0) (c, f r) y).2)
      (p + pointPoly (Ext4.toSpec alpha) (Ext4.toSpec y.1) (ι (FastField.toField gen)) c ps)
      (by
        rw [← mem_degreeLT] at hp ⊢
        exact Submodule.add_mem _ hp (mem_degreeLT.mpr
          (degree_pointPoly _ _ _ _ _ _ hm.2.2.2.2.2.1)))
      (fun r hr ↦ by rw [toSpec_ptStep hm alpha _ c y hz hys r hr, hf r hr, eval_add])
    exact this

/-- One honest matrix keeps the running sums low degree. -/
theorem reduceStep_ok {b h : Nat} (alpha : EF) {red : List (Nat × Nat × Array EF)}
    (hred : RedOk b red) {it : Mat × List (EF × Array EF)} (hit : HonestItem b h it) :
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
    ∀ (items : List (Mat × List (EF × Array EF))), (∀ x ∈ items, ∃ h, HonestItem b h x) →
      ∀ red, RedOk b red → RedOk b (items.foldl (reduceStep alpha) red)
  | [], _, _, hred => hred
  | it :: items, hitems, red, hred => by
    obtain ⟨h, hit⟩ := hitems it List.mem_cons_self
    exact foldl_reduceStep_ok b alpha items (fun x hx ↦ hitems x (List.mem_cons_of_mem _ hx)) _
      (reduceStep_ok alpha hred hit)

end Deep
open Deep

/-- The batched quotients of LDE matrices with true openings are low degree. -/
theorem reduce_lowDegree (b : Nat) (alpha : EF) (items : List (Mat × List (EF × Array EF)))
    (hitems : ∀ x ∈ items, ∃ h ps, Mat.IsLde b h x.1 ps ∧ ∀ y ∈ x.2, Ext.OutsideBase y.1 ∧
      y.2.size = ps.length ∧ ∀ j < ps.length,
        Ext4.toSpec (y.2.getD j 0) = aeval (Ext4.toSpec y.1) (ps.getD j 0)) :
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
    (it : Mat × List (EF × Array EF)) (h : Nat) :
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
    {it : Mat × List (EF × Array EF)} (hit : it.1.height = 2 ^ Nat.log2 it.1.height) :
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
    ∀ (items : List (Mat × List (EF × Array EF))),
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
theorem reduce_heights (alpha : EF) (items : List (Mat × List (EF × Array EF)))
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

end CompStark
