/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Quotient
public import CompStark.Stark.Constraints

/-! # The fast LogUp quotient is the specification's

A block value (`XVal`) represents the values of an extension expression on a block of rows
(`XRel`): one value for all of them, base words, or planes. Every operation on block values
represents the operation on the values (`XRel.add`, `XRel.sub`, `XRel.mul`), so a block of an
extension expression evaluates to the expression's values there (`evalX_rel`). The constraints
accumulated with the powers of `α` are their Horner fold (`accumulate_rel`, `horner_eq_sum`), and
the rest follows the quotient's argument (`lookupQuotientWith_rel`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open Montgomery.Native32.Words
open CompPoly.Array (batchInv)
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial

open Montgomery.Native32

variable {p : ℕ} [Mont32Field p] {EF : Type} [FastExt p EF]

local notation "F" => FastField p

/-! ### Base elements -/

theorem ofBase_add (a b : F) :
    FastExt.ofBase (E := EF) a + FastExt.ofBase b = FastExt.ofBase (a + b) :=
  FastExt.toSpec_injective (by
    rw [FastExt.toSpec_add, FastExt.toSpec_ofBase, FastExt.toSpec_ofBase, FastExt.toSpec_ofBase]
    exact (map_add (CompPoly.Extension.Ext.ofBaseRingHom _) a b).symm)

theorem ofBase_sub (a b : F) :
    FastExt.ofBase (E := EF) a - FastExt.ofBase b = FastExt.ofBase (a - b) :=
  FastExt.toSpec_injective (by
    rw [FastExt.toSpec_sub, FastExt.toSpec_ofBase, FastExt.toSpec_ofBase, FastExt.toSpec_ofBase]
    exact (map_sub (CompPoly.Extension.Ext.ofBaseRingHom _) a b).symm)

theorem ofBase_mul (a b : F) :
    FastExt.ofBase (E := EF) a * FastExt.ofBase b = FastExt.ofBase (a * b) :=
  FastExt.toSpec_injective (by
    rw [FastExt.toSpec_mul, FastExt.toSpec_ofBase, FastExt.toSpec_ofBase, FastExt.toSpec_ofBase]
    exact (map_mul (CompPoly.Extension.Ext.ofBaseRingHom _) a b).symm)

/-! ### Block values -/

/-- A block value represents the values `f` on its `B` rows. -/
def XRel (B : Nat) : XVal p EF → (Nat → EF) → Prop
  | .const c, f => ∀ i < B, f i = c
  | .base w, f => ∃ g : Nat → F, w = encode (tab B g) ∧ ∀ i < B, f i = FastExt.ofBase (g i)
  | .ext v, f => ExtPlanes.Rel v (tab B f)

theorem XRel.congr {B : Nat} {x : XVal p EF} {f g : Nat → EF} (h : XRel B x f)
    (hfg : ∀ i < B, f i = g i) : XRel B x g := by
  cases x with
  | const c => exact fun i hi ↦ (hfg i hi).symm.trans (h i hi)
  | base w =>
    obtain ⟨g', hw, hg⟩ := h
    exact ⟨g', hw, fun i hi ↦ (hfg i hi).symm.trans (hg i hi)⟩
  | ext v => exact ExtPlanes.Rel.congr_tab h hfg

/-- The planes of a block value represent its values. -/
theorem XRel.planes {B : Nat} (hB : 4 * B < USize.size) {x : XVal p EF} {f : Nat → EF}
    (h : XRel B x f) : ExtPlanes.Rel (x.planes B) (tab B f) := by
  cases x with
  | const c =>
    refine ExtPlanes.rel_tab_iff.mpr ⟨rfl, fun k ↦ ?_⟩
    simp only [XVal.planes, XVal.rep, ExtPlanes.getElem_ofFn_fin]
    rw [replicateWord_tab hB]
    exact congrArg encode (tab_congr fun i hi ↦ by rw [h i hi])
  | base w =>
    obtain ⟨g, hw, hg⟩ := h
    refine ExtPlanes.rel_tab_iff.mpr ⟨rfl, fun k ↦ ?_⟩
    simp only [XVal.planes, ExtPlanes.getElem_ofFn_fin]
    split
    · rename_i hk
      rw [hw]
      exact congrArg encode (tab_congr fun i hi ↦ by
        rw [hg i hi, FastExt.coord_ofBase, ite_eq_left_of_eq_true _ _ (eq_true hk)])
    · rename_i hk
      rw [zeroWords_tab (p := p)]
      exact congrArg encode (tab_congr fun i hi ↦ by
        rw [hg i hi, FastExt.coord_ofBase, ite_eq_right_of_eq_false _ _ (eq_false hk)])
  | ext v => exact h

/-- Plane `0` mapped by `op`, the others kept. -/
theorem rv_mapPlane0 {B : Nat} {v : ExtPlanes p EF} {f h : Nat → EF} (op : ByteArray → ByteArray)
    (hv : ExtPlanes.Rel v (tab B f)) (k0 : Fin (FastExt.d p EF)) (hk0 : k0.val = 0)
    (h0 : op (encode (tab B fun i ↦ FastExt.coord (f i) k0)) =
      encode (tab B fun i ↦ FastExt.coord (h i) k0))
    (hk : ∀ i < B, ∀ k : Fin (FastExt.d p EF), k.val ≠ 0 →
      FastExt.coord (h i) k = FastExt.coord (f i) k) :
    ExtPlanes.Rel (mapPlane0 op v) (tab B h) := by
  obtain ⟨hn, hc⟩ := ExtPlanes.rel_tab_iff.mp hv
  refine ExtPlanes.rel_tab_iff.mpr ⟨hn, fun k ↦ ?_⟩
  simp only [mapPlane0, ExtPlanes.getElem_ofFn_fin]
  split
  · rename_i hk'
    obtain rfl : k = k0 := Fin.ext (by rw [hk', hk0])
    rw [hc]
    exact h0
  · rename_i hk'
    rw [hc]
    exact congrArg encode (tab_congr fun i hi ↦ (hk i hi k hk').symm)

/-- The coordinates of `a + x`, `x + a` and `a - x` for a base element `x`. -/
theorem coord_add_ofBase (a : EF) (x : F) (k : Fin (FastExt.d p EF)) :
    FastExt.coord (a + FastExt.ofBase x) k = FastExt.coord a k + if k.val = 0 then x else 0 := by
  rw [FastExt.coord_add, Pi.add_apply, FastExt.coord_ofBase]

theorem coord_ofBase_add (a : EF) (x : F) (k : Fin (FastExt.d p EF)) :
    FastExt.coord (FastExt.ofBase x + a) k = (if k.val = 0 then x else 0) + FastExt.coord a k := by
  rw [FastExt.coord_add, Pi.add_apply, FastExt.coord_ofBase]

theorem coord_sub_ofBase (a : EF) (x : F) (k : Fin (FastExt.d p EF)) :
    FastExt.coord (a - FastExt.ofBase x) k = FastExt.coord a k - if k.val = 0 then x else 0 := by
  rw [FastExt.coord_sub, Pi.sub_apply, FastExt.coord_ofBase]

/-- The zero coordinate. -/
def k0 : Fin (FastExt.d p EF) := ⟨0, (FastExt.params (p := p) (E := EF)).d_pos⟩

theorem XRel.add {B : Nat} (hB : 4 * B < USize.size) {x y : XVal p EF} {f g : Nat → EF}
    (hx : XRel B x f) (hy : XRel B y g) : XRel B (x.add B y) fun i ↦ f i + g i := by
  have generic : ExtPlanes.Rel ((x.planes B).add (y.planes B)) (tab B fun i ↦ f i + g i) :=
    ExtPlanes.add_rel hB (hx.planes hB) (hy.planes hB)
  cases x with
  | const a =>
    cases y with
    | const b => exact fun i hi ↦ by beta_reduce; rw [hx i hi, hy i hi]
    | base w => exact generic
    | ext v => exact generic
  | base w =>
    obtain ⟨g1, hw1, hg1⟩ := hx
    cases y with
    | const b => exact generic
    | base w' =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      refine ⟨fun i ↦ g1 i + g2 i, ?_, fun i hi ↦ by
        beta_reduce; rw [hg1 i hi, hg2 i hi, ofBase_add]⟩
      show Words.addWords p w w' B = _
      rw [hw1, hw2, addWords_tab hB]
    | ext v =>
      show ExtPlanes.Rel (mapPlane0 _ v) _
      rw [hw1]
      refine rv_mapPlane0 _ hy k0 rfl ?_ fun i hi k hk ↦ ?_
      · rw [addWords_tab hB]
        exact congrArg encode (tab_congr fun i hi ↦ by
          rw [hg1 i hi, coord_ofBase_add, ite_eq_left_of_eq_true _ _ (eq_true (show (k0 (p := p) (EF
              := EF) : ℕ) = 0 from rfl))])
      · rw [hg1 i hi, coord_ofBase_add, ite_eq_right_of_eq_false _ _ (eq_false hk), zero_add]
  | ext v =>
    cases y with
    | const b => exact generic
    | base w =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      show ExtPlanes.Rel (mapPlane0 _ v) _
      rw [hw2]
      refine rv_mapPlane0 _ hx k0 rfl ?_ fun i hi k hk ↦ ?_
      · rw [addWords_tab hB]
        exact congrArg encode (tab_congr fun i hi ↦ by
          rw [hg2 i hi, coord_add_ofBase, ite_eq_left_of_eq_true _ _ (eq_true (show (k0 (p := p) (EF
              := EF) : ℕ) = 0 from rfl))])
      · rw [hg2 i hi, coord_add_ofBase, ite_eq_right_of_eq_false _ _ (eq_false hk), add_zero]
    | ext v' => exact generic

theorem XRel.sub {B : Nat} (hB : 4 * B < USize.size) {x y : XVal p EF} {f g : Nat → EF}
    (hx : XRel B x f) (hy : XRel B y g) : XRel B (x.sub B y) fun i ↦ f i - g i := by
  have generic : ExtPlanes.Rel ((x.planes B).sub (y.planes B)) (tab B fun i ↦ f i - g i) :=
    ExtPlanes.sub_rel hB (hx.planes hB) (hy.planes hB)
  cases x with
  | const a =>
    cases y with
    | const b => exact fun i hi ↦ by beta_reduce; rw [hx i hi, hy i hi]
    | base w => exact generic
    | ext v => exact generic
  | base w =>
    cases y with
    | const b => exact generic
    | base w' =>
      obtain ⟨g1, hw1, hg1⟩ := hx
      obtain ⟨g2, hw2, hg2⟩ := hy
      refine ⟨fun i ↦ g1 i - g2 i, ?_, fun i hi ↦ by
        beta_reduce; rw [hg1 i hi, hg2 i hi, ofBase_sub]⟩
      show Words.subWords p w w' B = _
      rw [hw1, hw2, subWords_tab hB]
    | ext v => exact generic
  | ext v =>
    cases y with
    | const b => exact generic
    | base w =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      show ExtPlanes.Rel (mapPlane0 _ v) _
      rw [hw2]
      refine rv_mapPlane0 _ hx k0 rfl ?_ fun i hi k hk ↦ ?_
      · rw [subWords_tab hB]
        exact congrArg encode (tab_congr fun i hi ↦ by
          rw [hg2 i hi, coord_sub_ofBase, ite_eq_left_of_eq_true _ _ (eq_true (show (k0 (p := p) (EF
              := EF) : ℕ) = 0 from rfl))])
      · rw [hg2 i hi, coord_sub_ofBase, ite_eq_right_of_eq_false _ _ (eq_false hk), sub_zero]
    | ext v' => exact generic

/-- Base words times an extension scalar. -/
theorem rv_scaleBase [Mont32BaseField p] {B : Nat} (hB : 4 * B < USize.size) (g : Nat → F)
    (c : EF) : ExtPlanes.Rel (XVal.scaleBase B (encode (tab B g)) c)
      (tab B fun i ↦ FastExt.ofBase (g i) * c) := by
  refine ExtPlanes.rel_tab_iff.mpr ⟨rfl, fun k ↦ ?_⟩
  simp only [XVal.scaleBase, ExtPlanes.getElem_ofFn_fin]
  rw [zeroWords_tab (p := p), mulAddWords_tab hB]
  refine congrArg encode (tab_congr fun i _ ↦ ?_)
  rw [FastExt.coord_smul_ofBase, zero_add]

theorem XRel.mul [Mont32BaseField p] {B : Nat} (hB : 4 * B < USize.size) {x y : XVal p EF}
    {f g : Nat → EF} (hx : XRel B x f) (hy : XRel B y g) :
    XRel B (x.mul B y) fun i ↦ f i * g i := by
  cases x with
  | const a =>
    cases y with
    | const b => exact fun i hi ↦ by beta_reduce; rw [hx i hi, hy i hi]
    | base w =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      show ExtPlanes.Rel (XVal.scaleBase B w a) _
      rw [hw2]
      exact (rv_scaleBase hB g2 a).congr_tab fun i hi ↦ by
        rw [hx i hi, hg2 i hi, FastExt.mul_comm]
    | ext v =>
      show ExtPlanes.Rel (v.smul a) _
      exact (ExtPlanes.smul_rel hB a hy).congr_tab fun i hi ↦ by
        rw [hx i hi, FastExt.mul_comm]
  | base w =>
    obtain ⟨g1, hw1, hg1⟩ := hx
    cases y with
    | const b =>
      show ExtPlanes.Rel (XVal.scaleBase B w b) _
      rw [hw1]
      exact (rv_scaleBase hB g1 b).congr_tab fun i hi ↦ by rw [hg1 i hi, hy i hi]
    | base w' =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      refine ⟨fun i ↦ g1 i * g2 i, ?_, fun i hi ↦ by
        beta_reduce; rw [hg1 i hi, hg2 i hi, ofBase_mul]⟩
      show Words.mulWords p w w' B = _
      rw [hw1, hw2, mulWords_tab hB]
    | ext v =>
      show ExtPlanes.Rel (v.mulBase w) _
      rw [hw1]
      exact (ExtPlanes.mulBase_rel hB g1 hy).congr_tab fun i hi ↦ by
        rw [hg1 i hi, FastExt.mul_comm]
  | ext v =>
    cases y with
    | const b =>
      show ExtPlanes.Rel (v.smul b) _
      exact (ExtPlanes.smul_rel hB b hx).congr_tab fun i hi ↦ by rw [hy i hi]
    | base w =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      show ExtPlanes.Rel (v.mulBase w) _
      rw [hw2]
      exact (ExtPlanes.mulBase_rel hB g2 hx).congr_tab fun i hi ↦ by rw [hg2 i hi]
    | ext v' => exact ExtPlanes.mul_rel hB hx hy

/-! ### Horner's fold as weights -/

section Horner

/-- `∑ₖ xₖ a ^ (n - 1 - k)` of `n` values. -/
def hornerSum {R : Type*} [CommRing R] (a : R) : List R → R
  | [] => 0
  | x :: xs => x * a ^ xs.length + hornerSum a xs

variable {K : Type} [BaseField K] {E : Type} [Challenge K E]

theorem toSpec_foldl_horner' (alpha : E) : ∀ (xs : List E) (acc : E),
    Challenge.toSpec (xs.foldl (fun acc x ↦ acc * alpha + x) acc) =
      Challenge.toSpec acc * Challenge.toSpec alpha ^ xs.length +
        hornerSum (Challenge.toSpec alpha) (xs.map Challenge.toSpec)
  | [], acc => by simp only [List.foldl_nil, List.length_nil, pow_zero, mul_one, List.map_nil,
      hornerSum, add_zero]
  | x :: xs, acc => by
    rw [List.foldl_cons, toSpec_foldl_horner' alpha xs, Challenge.toSpec_add,
      Challenge.toSpec_mul, List.map_cons, hornerSum, List.length_cons, List.length_map, pow_succ]
    ring

theorem toSpec_foldl_weighted (alpha : E) : ∀ (xs : List E) (y : E),
    Challenge.toSpec ((xs.zip ((List.range xs.length).map fun k ↦
      Ext.pow alpha (xs.length - 1 - k))).foldl (fun y x ↦ y + x.1 * x.2) y) =
      Challenge.toSpec y + hornerSum (Challenge.toSpec alpha) (xs.map Challenge.toSpec)
  | [], y => by simp only [List.zip_nil_left, List.foldl_nil, List.map_nil, hornerSum, add_zero]
  | x :: xs, y => by
    have hr : (List.range (x :: xs).length).map (fun k ↦ Ext.pow alpha ((x :: xs).length - 1 - k))
        = Ext.pow alpha xs.length ::
          (List.range xs.length).map fun k ↦ Ext.pow alpha (xs.length - 1 - k) := by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun k hk ↦ ?_
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [hr, List.zip_cons_cons, List.foldl_cons, toSpec_foldl_weighted alpha xs,
      Challenge.toSpec_add, Challenge.toSpec_mul, Ext.toSpec_pow, List.map_cons, hornerSum,
      List.length_map]
    ring

/-- The values weighted by the powers `α ^ (n - 1 - k)` are their Horner fold. -/
theorem weighted_eq_horner (alpha : E) (xs : List E) :
    (xs.zip ((List.range xs.length).map fun k ↦ Ext.pow alpha (xs.length - 1 - k))).foldl
      (fun y x ↦ y + x.1 * x.2) 0 = xs.foldl (fun acc x ↦ acc * alpha + x) 0 := by
  refine Challenge.toSpec_injective ?_
  rw [toSpec_foldl_weighted, toSpec_foldl_horner', Challenge.toSpec_zero, MulZeroClass.zero_mul]

end Horner

/-! ### The specification row by row -/

/-- Coordinate `j` of products zipped with weights by index, accumulated. -/
theorem coord_foldl_zip {α : Type} (u : α → EF) (g : Nat → EF) (j : Nat) :
    ∀ (cs : List α) (n : Nat) (y : EF),
      coord j (((cs.map u).zip ((List.range' n cs.length).map g)).foldl
        (fun y x ↦ y + x.1 * x.2) y) =
        ((cs.zipIdx n).map fun (c, k) ↦ coord j (u c * g k)).foldl (· + ·) (coord j y)
  | [], _, _ => rfl
  | c :: cs, n, y => by
    rw [List.length_cons, List.range'_succ, List.map_cons, List.map_cons, List.zip_cons_cons,
      List.foldl_cons, List.zipIdx_cons, List.map_cons, List.foldl_cons, ← coord_add]
    exact coord_foldl_zip u g j cs (n + 1) _

/-- The fast extension element of a specification element. -/
abbrev toE (x : FastExt.Spec p EF) : EF := FastExt.ofSpec x

theorem toE_add (a b : FastExt.Spec p EF) : toE (a + b) = toE a + toE b :=
  FastExt.toSpec_injective (by
    simp only [toE, FastExt.toSpec_add, FastExt.toSpec_ofSpec])

theorem toE_sub (a b : FastExt.Spec p EF) : toE (a - b) = toE a - toE b :=
  FastExt.toSpec_injective (by
    simp only [toE, FastExt.toSpec_sub, FastExt.toSpec_ofSpec])

theorem toE_mul (a b : FastExt.Spec p EF) : toE (a * b) = toE a * toE b :=
  FastExt.toSpec_injective (by
    simp only [toE, FastExt.toSpec_mul, FastExt.toSpec_ofSpec])

theorem toE_ofFn (f : Fin (FastExt.d p EF) → F) :
    toE (CompPoly.Extension.Ext.ofFn f) = FastExt.ofCoords f :=
  FastExt.toSpec_injective (by rw [FastExt.toSpec_ofSpec, FastExt.toSpec_ofCoords])

theorem toE_ofBase (x : F) : toE (CompPoly.Extension.Ext.ofBase x) = FastExt.ofBase (E := EF) x :=
  FastExt.toSpec_injective (by rw [FastExt.toSpec_ofSpec, FastExt.toSpec_ofBase])

theorem eval_pubBelow (np : Nat) (env : Expr.Env F F) : ∀ e : Expr F,
    (Prog.Dag.pubBelow np e).eval env =
      e.eval { env with pub := fun j ↦ if j < np then env.pub j else env.const 0 }
  | .add a b => by
    simp only [Prog.Dag.pubBelow, Expr.eval, eval_pubBelow np env a, eval_pubBelow np env b]
  | .sub a b => by
    simp only [Prog.Dag.pubBelow, Expr.eval, eval_pubBelow np env a, eval_pubBelow np env b]
  | .mul a b => by
    simp only [Prog.Dag.pubBelow, Expr.eval, eval_pubBelow np env a, eval_pubBelow np env b]
  | .pub j => by
    simp only [Prog.Dag.pubBelow]
    by_cases h : j < np
    · simp only [h, ite_true, Expr.eval]
    · simp only [h, ite_false, Expr.eval]
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .periodic _ | .const _ | .isFirstRow
  | .isLastRow | .isTransition => rfl

section Spec
variable [Mont32BaseField p] [Mont32.AlgebraId EF]

/-- The base environment of row `r` of `lookupQuotientValues`. -/
def lqEnv (pis : List F) (d l : Nat) (tq pq : Mat F) (per : List (Array F)) (r : Nat) :
    Expr.Env F EF :=
  let r' := (r + 2 ^ l) % 2 ^ (d + l)
  let get (m : Mat F) (r c : Nat) : F := m.values.getD (r * m.width + c) 0
  { cur := fun c ↦ Ext.ofBase (get tq r c)
    next := fun c ↦ Ext.ofBase (get tq r' c)
    prepCur := fun c ↦ Ext.ofBase (get pq r c)
    prepNext := fun c ↦ Ext.ofBase (get pq r' c)
    periodic := fun j ↦ Ext.ofBase (periodicRow (per.getD j #[]) r)
    pub := fun j ↦ Ext.ofBase (pis.getD j 0)
    const := Ext.ofBase
    isFirstRow := Ext.ofBase ((qFirst d l : Array F).getD r 0)
    isLastRow := Ext.ofBase ((qLast d l : Array F).getD r 0)
    isTransition := Ext.ofBase ((qTrans d l : Array F).getD r 0) }

/-- The permutation rows, challenges and terminal of row `r` of `lookupQuotientValues`. -/
def lqAux (d l : Nat) (rq : Mat F) (chs : List EF) (terminal : EF) (r : Nat) :
    Lookup.ExtExpr.Env EF :=
  let r' := (r + 2 ^ l) % 2 ^ (d + l)
  let get (m : Mat F) (r c : Nat) : F := m.values.getD (r * m.width + c) 0
  let permAt (r c : Nat) : EF := Challenge.ofCoeffs ((List.range (Challenge.d EF)).map fun e ↦
    get rq r (c * Challenge.d EF + e))
  ⟨permAt r, permAt r', (chs.getD · 0), terminal⟩

/-- Row `r` of `lookupQuotientValues`. -/
theorem lookupQuotientValues_getD (ext : List (Lookup.ExtExpr F)) (pis : List F) (d l : Nat)
    (tq pq rq : Mat F) (per : List (Array F)) (chs : List EF) (terminal alpha : EF) (r : Nat)
    (hr : r < 2 ^ (d + l)) :
    (Lookup.lookupQuotientValues ext pis d l tq pq rq per chs terminal alpha).getD r 0 =
      Challenge.smul ((batchInv (qZh d l) : Array F).getD (r % 2 ^ l) 0)
        (ext.foldl (fun acc c ↦ acc * alpha + c.eval (lqEnv pis d l tq pq per r)
          (lqAux d l rq chs terminal r)) 0) := by
  unfold Lookup.lookupQuotientValues
  rw [getD_lt _ _ (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn]
  rfl


theorem coeffs_getD (x : EF) (j : Nat) : (Challenge.coeffs x).getD j 0 = coord j x := by
  rw [Mont32.coeffs_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn, coord]
  split
  · simp only [Option.getD_some]
  · simp only [Option.getD_none]

/-- The coordinates of extension elements laid out `d` by `d`. -/
theorem flatMap_coeffs_getD (xs : List EF) (q e : Nat) (he : e < FastExt.d p EF) :
    (xs.toArray.flatMap fun c ↦ (Challenge.coeffs c).toArray).getD (FastExt.d p EF * q + e) 0 =
      coord e (xs.getD q 0) := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, Array.toList_flatMap,
    List.toList_toArray]
  induction xs generalizing q with
  | nil =>
    simp only [List.flatMap_nil, List.getElem?_nil, Option.getD_none, List.getD_nil]
    exact (coord_zero e).symm
  | cons x xs ih =>
    have hl : (Challenge.coeffs x).toArray.toList.length = FastExt.d p EF := by
      rw [List.toList_toArray, Challenge.length_coeffs]; rfl
    rw [List.flatMap_cons]
    rcases q with _ | q
    · rw [List.getElem?_append_left (by rw [hl]; omega), List.getD_cons_zero, Nat.mul_zero,
        Nat.zero_add, List.toList_toArray, ← List.getD_eq_getElem?_getD, coeffs_getD]
    · rw [List.getElem?_append_right (by rw [hl, Nat.mul_succ]; omega), List.getD_cons_succ, hl,
        show FastExt.d p EF * (q + 1) + e - FastExt.d p EF = FastExt.d p EF * q + e by
          rw [Nat.mul_succ]; omega]
      exact ih q

/-- **The fast LogUp quotient is the specification's** on related extensions of the trace, the
preprocessed trace and the permutation trace, for extension constraints reading their columns, `k`
permutation columns of `d` coordinates. -/
theorem lookupQuotientWith_rel (kernels : List (Prog.GroupKernel p)) (A : Air F) (ext : List
    (Lookup.ExtExpr F)) (pis : List F)
    (d l : Nat) (chs : List EF) (terminal alpha : EF) (k : Nat) {tr : PMat} {s : Mat F}
    {prep : Option PMat} {ps : Option (Mat F)} {perm : PMat} {rs : Mat F}
    (h : RM tr s) (hs : MatOk s) (hh : 2 ^ (d + l) ≤ s.height) (hp : Option.Rel RM prep ps)
    (hps : ∀ q ∈ ps, MatOk q ∧ q.height = s.height) (hr : RM perm rs) (hrs : MatOk rs)
    (hrh : rs.height = s.height) (hk : k * FastExt.d p EF ≤ rs.width)
    (hc : ∀ c ∈ ext, c.colsBelow s.width s.width ((ps.map (·.width)).getD 0)
      ((ps.map (·.width)).getD 0) k) (hU : 4 * (2 ^ (d + l) * FastExt.d p EF) < USize.size) :
    QRel (lookupQuotientWith kernels (quotientTables (p := p) d l) A ext pis tr prep perm
      chs terminal alpha) (lookupQuotientOfLde A ext pis d l s ps rs chs terminal alpha) := by
  have hw := h.width
  have hrw := hr.width
  obtain ⟨hw0, -, hvs', hadd⟩ := hs
  obtain ⟨-, -, hrvs, hradd⟩ := hrs
  have hus : 4 * s.values.size < USize.size := by
    unfold Addressable at hadd
    rw [hvs']
    omega
  have hrus : 4 * rs.values.size < USize.size := by
    unfold Addressable at hradd
    rw [hrvs]
    omega
  have hpw : (ps.map (·.width)).getD 0 = (prepOrEmpty ps s.height).width := by cases ps <;> rfl
  have hpw' : (prep.map (·.width)).getD 0 = (prepOrEmpty ps s.height).width := by
    cases hp with
    | none => rfl
    | @some a q hr => exact hr.1
  have hpm : RowsOk (prepOrEmpty ps s.height) (prep.getD PMat.empty).rows ∧
      (prep.getD PMat.empty).toCols = (⟨colBlocks (prepOrEmpty ps s.height)
        (prep.getD PMat.empty).rows, (prepOrEmpty ps s.height).width,
        (prep.getD PMat.empty).rows⟩ : Prog.ColsF p).enc ∧
      ∀ r0 B, 0 < B → r0 + B ≤ s.height → (prep.getD PMat.empty).block r0 B =
        encode (blockT (prepOrEmpty ps s.height) r0 B) := by
    cases hp with
    | none =>
      refine ⟨⟨Nat.one_pos, Nat.mod_one _, by
        show 4 * 1 < USize.size; have := USize.le_size; omega⟩,
        empty_toCols s.height, fun r0 B _ _ ↦ ?_⟩
      show PMat.empty.block r0 B = encode (blockT (⟨0, s.height, #[]⟩ : Mat F) r0 B)
      rw [Array.eq_empty_of_size_eq_zero (xs := blockT _ r0 B) (by rw [size_blockT,
        Nat.zero_mul])]
      unfold PMat.block
      simp only [PMat.empty, Nat.zero_mul, Nat.mul_zero]
      split <;> rfl
    | @some a q hr =>
      obtain ⟨-, hqh⟩ := hps q rfl
      refine ⟨hr.rowsOk, toCols_rel hr, fun r0 B hB hrB ↦ block_rel hr r0 B hB (by
        show r0 + B ≤ q.height; rw [hqh]; exact hrB)⟩
  have hspv : (prepOrEmpty ps s.height).values.size =
      (prepOrEmpty ps s.height).width * s.height := by
    cases hp with
    | none => show (#[] : Array F).size = 0 * s.height; rw [Nat.zero_mul]; rfl
    | @some a q hr =>
      obtain ⟨⟨-, -, hq, -⟩, hqh⟩ := hps q rfl
      show q.values.size = q.width * s.height
      rw [hq, hqh]
  have husp : 4 * (prepOrEmpty ps s.height).values.size < USize.size := by
    cases hp with
    | none => show 4 * 0 < USize.size; have := USize.le_size; omega
    | @some a q hr =>
      obtain ⟨⟨-, -, hq, hqa⟩, -⟩ := hps q rfl
      unfold Addressable at hqa
      show 4 * q.values.size < USize.size
      rw [hq]
      omega
  have hpq : (ps.map fun m ↦ Mat.ofValues m.width (2 ^ (d + l))
        (permuteRows m (bitRevPerm (d + l)))).getD (Mat.ofValues 0 (2 ^ (d + l)) #[]) =
      Mat.ofValues (prepOrEmpty ps s.height).width (2 ^ (d + l))
        (permuteRows (prepOrEmpty ps s.height) (bitRevPerm (d + l))) := by
    cases ps with
    | none =>
      show Mat.ofValues 0 (2 ^ (d + l)) #[] = Mat.ofValues 0 (2 ^ (d + l)) (permuteRows _ _)
      rw [Array.eq_empty_of_size_eq_zero (xs := permuteRows _ _)
        (by rw [permuteRows_eq, Array.size_ofFn]; rfl)]
    | some q => rfl
  have hsph : (prepOrEmpty ps s.height).height = s.height := by
    cases ps with
    | none => rfl
    | some q => exact (hps q rfl).2
  generalize prepOrEmpty ps s.height = sp at hpw hpw' hpm hspv husp hpq hsph
  rw [hpw] at hc
  have hn : 2 ^ (d + l) ≤ s.values.size := by
    rw [hvs']; exact le_trans hh (Nat.le_mul_of_pos_left _ hw0)
  have hnU : 4 * 2 ^ (d + l) < USize.size := by omega
  have hsS : QShape d l s.height s := ⟨hvs', hh, hus⟩
  have hspS : QShape d l s.height sp := ⟨hspv, hh, husp⟩
  have hrsS : QShape d l s.height rs := ⟨by rw [hrvs, hrh], hh, hrus⟩
  let K := ext.length
  let np := pis.length
  let SC : Array F := pis.toArray ++ (terminal :: chs).toArray.flatMap fun c ↦
    (Challenge.coeffs c).toArray
  let dE := FastExt.d p EF
  have hd : 0 < dE := (FastExt.params (p := p) (E := EF)).d_pos
  let WT : Array F := Array.ofFn (n := dE * dE * K) fun i ↦
    (Ext.coeffs (FastExt.pow FastExt.gen (i.val / dE % dE) *
      Ext.pow alpha (K - 1 - i.val / (dE * dE)))).getD (i.val % dE) 0
  have hWT : extWeightCoords alpha K = WT := rfl
  unfold lookupQuotientOfLde
  dsimp only
  rw [hpq]
  unfold lookupQuotientWith
  rw [periodicWords_eq]
  generalize A.periodic.map (fun col ↦ periodicOnQuotient col d l) = pl
  let tq := Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l)))
  let pq := Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))
  let rq := Mat.ofValues rs.width (2 ^ (d + l)) (permuteRows rs (bitRevPerm (d + l)))
  let V (r : Nat) : EF := ext.foldl (fun acc c ↦ acc * alpha + c.eval (lqEnv pis d l tq pq pl r)
    (lqAux d l rq chs terminal r)) 0
  let Q (j e : Nat) : F := coord e (V ((bitRevPerm (d + l)).getD j 0))
  have hspec : Lookup.lookupQuotientValues ext pis d l tq pq rq pl chs terminal alpha =
      Array.ofFn (n := 2 ^ (d + l)) fun r ↦ Challenge.smul
        ((batchInv (qZh d l) : Array F).getD (r.val % 2 ^ l) 0) (V r.val) := by
    apply Array.ext (by rw [Lookup.lookupQuotientValues, Array.size_ofFn, Array.size_ofFn])
    intro r h1 h2
    rw [Array.size_ofFn] at h2
    rw [Array.getElem_ofFn, ← getD_lt _ _ (d := 0) h1]
    exact lookupQuotientValues_getD ext pis d l tq pq rq pl chs terminal alpha r h2
  dsimp only
  rw [hspec, hWT]
  refine (congrArg (QRel _) ?_).mp (quotientBlocks_rel d l _ _ (groupRun_eq kernels _) SC WT _ Q
    ?hblk hU)
  case hblk =>
    intro r0 hdvd hr0
    obtain ⟨hB0, -, -⟩ := tables_B (p := p) d l
    rw [tables_first, tables_last, tables_trans]
    generalize (quotientTables (p := p) d l).B = B at hdvd hr0 hB0 ⊢
    refine ⟨blockT s r0 B, 0, B, qLoads d l s sp rs tr.rows (prep.getD PMat.empty).rows
      perm.rows pl (quotientTables (p := p) d l).next r0 B, ?_, hsS.blockT hr0,
      qLoads_addr h.rowsOk hpm.1 hr.rowsOk hspS hrsS pl _ hr0 hnU, fun ins hins ↦ ?_,
      fun i hi st0 hst0 j hj ↦ ?_⟩
    · rw [block_rel h r0 B hB0 (by omega), hpm.2.2 r0 B hB0 (by omega), toCols_rel h,
        hpm.2.1, block_rel hr r0 B hB0 (by omega), toCols_rel hr]
      rfl
    · refine Prog.Instr.inRange_of (cq := (· < s.width))
        (lq := Prog.Src.Below s.width sp.width sp.width rs.width) (fun c hc ↦ ?_)
        (qLoads_inRange h.rowsOk hpm.1 hr.rowsOk hsS hspS hrsS rfl hsph hrh pl hr0)
        ins ((Prog.compileExt_run (FastExt.params EF) np ext ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0,
          fun _ _ ↦ 0⟩ ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2 ins hins)
        (Prog.compileExt_leafOk (FastExt.params EF) np ext s.width s.width sp.width sp.width k
          rs.width (by rw [Nat.mul_comm]; exact hk) hc ins hins)
      rw [size_blockT, Nat.zero_add]
      have := Nat.mul_le_mul_right B (show c + 1 ≤ s.width by exact hc)
      rw [Nat.succ_mul] at this; exact this
    · have hri : r0 + i < 2 ^ (d + l) := by omega
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := qLoads_env (FastExt.d p EF) d l s sp rs tr.rows
        (prep.getD PMat.empty).rows perm.rows h.rowsOk hpm.1 hh (by rw [hsph]; exact hh) pl pis
        SC WT r0 B i hi hri
      set ctx := Prog.blockCtx (FastExt.d p EF) (blockT s r0 B) 0 B
        (qLoads d l s sp rs tr.rows (prep.getD PMat.empty).rows perm.rows pl
          (quotientTables (p := p) d l).next r0 B) SC WT B i with hctx
      let R := (bitRevPerm (d + l)).getD (r0 + i) 0
      let u (c : Lookup.ExtExpr F) : EF := c.eval (lqEnv pis d l tq pq pl R)
        (lqAux d l rq chs terminal R)
      let g (k : Nat) : EF := Ext.pow alpha (K - 1 - k)
      -- The scalars: the public values, then the terminal's and the challenges' coordinates.
      have hsc (q e : Nat) (he : e < dE) : ctx.scalar (np + (dE * q + e)) =
          coord e ((terminal :: chs).getD q 0) := by
        show SC.getD (pis.length + (dE * q + e)) 0 = _
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by
          simp only [List.size_toArray]; omega), List.size_toArray, Nat.add_sub_cancel_left,
          ← Array.getD_eq_getD_getElem?]
        exact flatMap_coeffs_getD _ q e he
      have hscE (q : Nat) : toE (ctx.scalarsExt (FastExt.params EF) (np + dE * q)) =
          (terminal :: chs).getD q 0 := by
        refine (toE_ofFn _).trans (FastExt.ext fun i ↦ ?_)
        rw [FastExt.coord_ofCoords, Nat.add_assoc, hsc q i i.isLt, coord_fin]
      have hcd (c : Nat) (hc : c < k) (e : Nat) (he : e < dE) : dE * c + e < rs.width := by
        have h1 : dE * (c + 1) ≤ dE * k := Nat.mul_le_mul_left dE hc
        have h2 : dE * k = k * FastExt.d p EF := Nat.mul_comm _ _
        have h3 := hr.width
        rw [Nat.mul_succ] at h1
        omega
      -- The permutation columns of a stored row.
      have hpermAt (R' : Nat) (c : Nat) (x : Nat → F)
          (hx : ∀ e < dE, x (dE * c + e) = rq.values.getD (R' * rq.width + (c * dE + e)) 0) :
          toE (EF := EF) (CompPoly.Extension.Ext.ofFn fun j ↦ x ((FastExt.params EF).d * c + j)) =
            Challenge.ofCoeffs ((List.range (Challenge.d EF)).map fun e ↦
              rq.values.getD (R' * rq.width + (c * Challenge.d EF + e)) 0) := by
        rw [toE_ofFn, Mont32.ofCoeffs_eq, Mont32.d_eq]
        refine congrArg FastExt.ofCoords (funext fun j ↦ ?_)
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt,
          Option.map_some, Option.getD_some]
        exact hx j j.isLt
      have hu (c : Lookup.ExtExpr F) (hcm : c ∈ ext) :
          toE (c.eval (ctx.envQ (FastExt.params EF) np) (ctx.auxQ (FastExt.params EF) np)) =
            u c := by
        refine Lookup.ExtExpr.eval_hom toE toE_add toE_sub toE_mul s.width s.width sp.width
          sp.width k _ _ _ _ (fun e he ↦ ?_) (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun jj ↦ ?_) ?_ c
          (hc c hcm)
        · rw [Prog.Expr.eval_envQ, eval_pubBelow, toE_ofBase]
          have hb := Expr.eval_hom (R := F) (S := EF) FastExt.ofBase
            (fun a b ↦ (ofBase_add a b).symm) (fun a b ↦ (ofBase_sub a b).symm)
            (fun a b ↦ (ofBase_mul a b).symm) s.width s.width
            sp.width sp.width (rowEnv tq pq pl (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l)
              (qTrans d l) R) (lqEnv pis d l tq pq pl R) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
            (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl rfl
            e he
          rw [← hb]
          congr 1
          exact Expr.eval_hom (R := F) (S := F) id (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
            (fun _ _ ↦ rfl) s.width s.width sp.width sp.width
            { ctx.env with pub := fun j ↦ if j < np then ctx.env.pub j else ctx.env.const 0 }
            (rowEnv tq pq pl (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) R)
            e1 e2 e3 e4 e5
            (fun jj ↦ by
              show (if jj < np then SC.getD jj 0 else 0) = pis.getD jj 0
              by_cases hj : jj < np
              · rw [ite_eq_left hj, Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by
                  simp only [List.size_toArray]; exact hj), List.getElem?_toArray,
                  List.getD_eq_getElem?_getD]
              · rw [ite_eq_right hj, List.getD_eq_default _ _ (by omega)])
            (fun _ ↦ rfl) e6 e7 e8 e he
        · refine hpermAt R c (fun m ↦ ctx.src (.permCur m)) fun e he ↦ ?_
          show (blockT rs r0 B).getD ((dE * c + e) * B + i) 0 = _
          rw [blockT_getD rs r0 B _ i (hcd c hc e he) hi, show c * dE + e = dE * c + e by ring]
          exact (permuteRows_bitRev rs d l _ _ hri (hcd c hc e he)).symm
        · refine hpermAt ((R + 2 ^ l) % 2 ^ (d + l)) c (fun m ↦ ctx.src (.permNext m))
            fun e he ↦ ?_
          have hn : (quotientTables (p := p) d l).next.getD (r0 + i) 0 < 2 ^ (d + l) := by
            rw [tables_next _ _ _ hri]
            exact bitRevPerm_getD_lt _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
          show (⟨colBlocks rs perm.rows, rs.width, perm.rows⟩ : Prog.ColsF p).at
            ((quotientTables (p := p) d l).next.getD (r0 + i) 0) (dE * c + e) = _
          rw [colsF_at hr.rowsOk _ _ (by omega) (hcd c hc e he),
            show c * dE + e = dE * c + e by ring]
          exact (permuteRows_bitRev_next rs d l _ _ hri (hcd c hc e he)).symm
        · show toE (ctx.scalarsExt (FastExt.params EF) (np + dE * (jj + 1))) = chs.getD jj 0
          rw [hscE]
          rfl
        · show toE (ctx.scalarsExt (FastExt.params EF) np) = terminal
          rw [← Nat.add_zero np, ← Nat.mul_zero dE, hscE]
          rfl
      rw [(Prog.compileExt_run (FastExt.params EF) np ext ctx st0).1, hst0]
      dsimp only
      have hV : V R = ((ext.map u).zip ((List.range (ext.map u).length).map fun k ↦
          Ext.pow alpha ((ext.map u).length - 1 - k))).foldl (fun y x ↦ y + x.1 * x.2) 0 := by
        rw [weighted_eq_horner, List.foldl_map]
      show _ = coord j (V R)
      rw [hV, List.length_map, List.range_eq_range', coord_foldl_zip u g j ext 0 0, coord_zero]
      refine foldl_add_congr _ _ _ (fun a ha ↦ ?_) 0
      obtain ⟨c, kk⟩ := a
      have hcm : c ∈ ext := List.fst_mem_of_mem_zipIdx ha
      have hkk : kk < K := List.snd_lt_of_mem_zipIdx ha
      dsimp only
      have hv : c.eval (ctx.envQ (FastExt.params EF) np) (ctx.auxQ (FastExt.params EF) np) =
          FastExt.toSpec (u c) := by
        rw [← hu c hcm, FastExt.toSpec_ofSpec]
      have hw (e : Nat) (he : e < dE) :
          ctx.weight (dE * kk + e) j = coord j (FastExt.pow FastExt.gen e * g kk) := by
        show WT.getD (dE * (dE * kk + e) + j) 0 = _
        have hlt : dE * (dE * kk + e) + j < dE * dE * K := by
          have h1 := Nat.mul_le_mul_left dE (show dE * kk + e + 1 ≤ dE * K by
            have := Nat.mul_le_mul_left dE (show kk + 1 ≤ K from hkk)
            rw [Nat.mul_succ] at this; omega)
          rw [Nat.mul_succ, ← Nat.mul_assoc] at h1
          omega
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ hlt]
        have h1 : (dE * (dE * kk + e) + j) / dE = dE * kk + e := by
          rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.add_zero]
        have h2 : (dE * (dE * kk + e) + j) / (dE * dE) = kk := by
          rw [← Nat.div_div_eq_div_mul, h1, Nat.mul_add_div hd, Nat.div_eq_of_lt he,
            Nat.add_zero]
        have h3 : (dE * (dE * kk + e) + j) % dE = j := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
        have h4 : (dE * kk + e) % dE = e := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt he]
        simp only [h1, h2, h3, h4]
        exact coeffs_getD _ j
      unfold Prog.extTerm
      rw [hv, coord, dite_eq_left hj, FastExt.coord_mul_eq_sum,
        ← CompPoly.Extension.Ext.sum_range_eq_list_sum, ← Fin.sum_univ_eq_sum_range
          (fun i ↦ CompPoly.Extension.Ext.coeffNat (FastExt.toSpec (u c)) i *
            ctx.weight ((FastExt.params EF).d * kk + i) j)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [CompPoly.Extension.Ext.coeffNat_of_lt _ i.isLt, FastExt.coeff_toSpec, hw i i.isLt, coord,
        dite_eq_left hj]
  refine congrArg Array.ofFn (funext fun r ↦ ?_)
  simp only [Q, bitRevPerm_getD_getD _ _ r.isLt]
  show _ = FastExt.ofCoords fun i ↦ _ * FastExt.coord _ i
  refine congrArg FastExt.ofCoords (funext fun j ↦ ?_)
  rw [coord_fin]

end Spec

end CompStark.Stark.Fast
