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
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial

open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-! ### Tabulated values -/

/-- The values `f 0, …, f (B - 1)`. -/
def tab {α : Type} (B : Nat) (f : Nat → α) : Array α := Array.ofFn (n := B) fun i ↦ f i.val

theorem size_tab {α : Type} (B : Nat) (f : Nat → α) : (tab B f).size = B := Array.size_ofFn

theorem tab_congr {α : Type} {B : Nat} {f g : Nat → α} (h : ∀ i < B, f i = g i) :
    tab B f = tab B g :=
  congrArg Array.ofFn (funext fun i ↦ h i.val i.isLt)

theorem tab_zipWith {α β γ : Type} (B : Nat) (f : Nat → α) (g : Nat → β) (op : α → β → γ) :
    Array.zipWith op (tab B f) (tab B g) = tab B fun i ↦ op (f i) (g i) := by
  apply Array.ext (by simp only [Array.size_zipWith, tab, Array.size_ofFn, Nat.min_self])
  intro i h1 h2
  simp only [tab, Array.getElem_zipWith, Array.getElem_ofFn]

theorem tab_map {α β : Type} (B : Nat) (f : Nat → α) (g : α → β) :
    (tab B f).map g = tab B fun i ↦ g (f i) := by
  apply Array.ext (by simp only [Array.size_map, tab, Array.size_ofFn])
  intro i h1 h2
  simp only [tab, Array.getElem_map, Array.getElem_ofFn]

theorem replicate_tab (B : Nat) (c : F) : Array.replicate B c = tab B fun _ ↦ c := by
  apply Array.ext (by simp only [Array.size_replicate, tab, Array.size_ofFn])
  intro i h1 h2
  simp only [tab, Array.getElem_replicate, Array.getElem_ofFn]

theorem getElem_tab {α : Type} (B : Nat) (f : Nat → α) (i : Nat) (h : i < (tab B f).size) :
    (tab B f)[i] = f i := by
  simp only [tab, Array.getElem_ofFn]

theorem getD_tab {α : Type} (B : Nat) (f : Nat → α) (i : Nat) (h : i < B) (d : α) :
    (tab B f).getD i d = f i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [size_tab]; exact h),
    Option.getD_some]
  simp only [tab, Array.getElem_ofFn]

theorem zeroWords_tab (B : Nat) :
    CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B = encode (tab B fun _ ↦ (0 : F)) :=
  EVec.zeroWords_ofFn B

theorem addWords_tab {B : Nat} (hB : 4 * B < USize.size) (f g : Nat → F) :
    Words.addWords p (encode (tab B f)) (encode (tab B g)) B = encode (tab B fun i ↦ f i + g i) :=
  EVec.addWords_ofFn hB (fun i ↦ f i.val) (fun i ↦ g i.val)

theorem subWords_tab {B : Nat} (hB : 4 * B < USize.size) (f g : Nat → F) :
    Words.subWords p (encode (tab B f)) (encode (tab B g)) B = encode (tab B fun i ↦ f i - g i) :=
  EVec.subWords_ofFn hB (fun i ↦ f i.val) (fun i ↦ g i.val)

theorem mulWords_tab {B : Nat} (hB : 4 * B < USize.size) (f g : Nat → F) :
    Words.mulWords p (encode (tab B f)) (encode (tab B g)) B = encode (tab B fun i ↦ f i * g i) :=
  EVec.mulWords_ofFn hB (fun i ↦ f i.val) (fun i ↦ g i.val)

theorem mulAddWords_tab {B : Nat} (hB : 4 * B < USize.size) (f g : Nat → F) (c : F) :
    Words.mulAddWords p (encode (tab B f)) (encode (tab B g)) c.val B =
      encode (tab B fun i ↦ f i + g i * c) :=
  EVec.mulAddWords_ofFn hB (fun i ↦ f i.val) (fun i ↦ g i.val) c

theorem word_tab {B : Nat} (hB : 4 * B < USize.size) (f : Nat → F) (i : Nat) (hi : i < B) :
    word (encode (tab B f)) i = f i :=
  word_encode_ofFn B hB f i hi

theorem replicateWord_tab {B : Nat} (hB : 4 * B < USize.size) (c : F) :
    Words.replicateWord c.val B = encode (tab B fun _ ↦ c) := by
  rw [Words.replicateWord_encode _ _ hB, replicate_tab]

/-- Planes represent tabulated elements when they tabulate the coordinates. -/
theorem rv_tab_iff {B : Nat} {v : EVec p} {f : Nat → EF} :
    RV v (tab B f) ↔ v.n = B ∧ v.c0 = encode (tab B fun i ↦ (f i).c0) ∧
      v.c1 = encode (tab B fun i ↦ (f i).c1) ∧ v.c2 = encode (tab B fun i ↦ (f i).c2) ∧
      v.c3 = encode (tab B fun i ↦ (f i).c3) := by
  simp only [RV, size_tab, tab_map]

theorem RV.congr_tab {B : Nat} {v : EVec p} {f g : Nat → EF} (h : RV v (tab B f))
    (hfg : ∀ i < B, f i = g i) : RV v (tab B g) := by
  rw [← tab_congr hfg]; exact h

theorem ext4_mul_comm [Binomial4 p] (a b : EF) : a * b = b * a := by
  rw [EVec.mul_coords, EVec.mul_coords]
  congr 1 <;> ring

theorem ofBase_c0 (x : F) : (Ext4.ofBase x).c0 = x := rfl
theorem ofBase_c1 (x : F) : (Ext4.ofBase x).c1 = 0 := rfl
theorem ofBase_c2 (x : F) : (Ext4.ofBase x).c2 = 0 := rfl
theorem ofBase_c3 (x : F) : (Ext4.ofBase x).c3 = 0 := rfl

theorem ofBase_add (a b : F) : Ext4.ofBase a + Ext4.ofBase b = Ext4.ofBase (p := p) (a + b) := by
  show (⟨a + b, 0 + 0, 0 + 0, 0 + 0⟩ : EF) = ⟨a + b, 0, 0, 0⟩
  rw [add_zero]

theorem ofBase_sub (a b : F) : Ext4.ofBase a - Ext4.ofBase b = Ext4.ofBase (p := p) (a - b) := by
  show (⟨a - b, 0 - 0, 0 - 0, 0 - 0⟩ : EF) = ⟨a - b, 0, 0, 0⟩
  rw [sub_zero]

theorem ofBase_mul [Binomial4 p] (a b : F) :
    Ext4.ofBase a * Ext4.ofBase b = Ext4.ofBase (p := p) (a * b) := by
  rw [EVec.mul_coords]
  simp only [ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3]
  show (⟨_, _, _, _⟩ : EF) = ⟨a * b, 0, 0, 0⟩
  congr 1 <;> ring

/-! ### Block values -/

/-- A block value represents the values `f` on its `B` rows. -/
def XRel (B : Nat) : XVal p → (Nat → EF) → Prop
  | .const c, f => ∀ i < B, f i = c
  | .base w, f => ∃ g : Nat → F, w = encode (tab B g) ∧ ∀ i < B, f i = Ext4.ofBase (g i)
  | .ext v, f => RV v (tab B f)

theorem XRel.congr {B : Nat} {x : XVal p} {f g : Nat → EF} (h : XRel B x f)
    (hfg : ∀ i < B, f i = g i) : XRel B x g := by
  cases x with
  | const c => exact fun i hi ↦ (hfg i hi).symm.trans (h i hi)
  | base w =>
    obtain ⟨g', hw, hg⟩ := h
    exact ⟨g', hw, fun i hi ↦ (hfg i hi).symm.trans (hg i hi)⟩
  | ext v => exact RV.congr_tab h hfg

/-- The planes of a block value represent its values. -/
theorem XRel.planes {B : Nat} (hB : 4 * B < USize.size) {x : XVal p} {f : Nat → EF}
    (h : XRel B x f) : RV (x.planes B) (tab B f) := by
  cases x with
  | const c =>
    refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [XVal.planes, XVal.rep]
      rw [replicateWord_tab hB]
      exact congrArg encode (tab_congr fun i hi ↦ by rw [h i hi])
  | base w =>
    obtain ⟨g, hw, hg⟩ := h
    refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [XVal.planes, hw]
      exact congrArg encode (tab_congr fun i hi ↦ by rw [hg i hi]; rfl)
    all_goals
      rw [XVal.planes, zeroWords_tab (p := p)]
      exact congrArg encode (tab_congr fun i hi ↦ by rw [hg i hi]; rfl)
  | ext v => exact h

theorem XRel.planes_n {B : Nat} {x : XVal p} {f : Nat → EF} (h : XRel B x f) :
    (x.planes B).n = B := by
  cases x with
  | const c => rfl
  | base w => rfl
  | ext v => exact (rv_tab_iff.mp h).1

/-- Base words added to the constant coordinate of planes. -/
theorem rv_addC0 {B : Nat} (hB : 4 * B < USize.size) {v : EVec p} (f : Nat → EF) (g : Nat → F)
    (hv : RV v (tab B f)) :
    RV ⟨B, Words.addWords p v.c0 (encode (tab B g)) B, v.c1, v.c2, v.c3⟩
      (tab B fun i ↦ f i + Ext4.ofBase (g i)) := by
  obtain ⟨-, h0, h1, h2, h3⟩ := rv_tab_iff.mp hv
  refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show Words.addWords p v.c0 (encode (tab B g)) B = _
    rw [h0, addWords_tab hB]; rfl
  · show v.c1 = _
    rw [h1]; exact congrArg encode (tab_congr fun i _ ↦ (add_zero _).symm)
  · show v.c2 = _
    rw [h2]; exact congrArg encode (tab_congr fun i _ ↦ (add_zero _).symm)
  · show v.c3 = _
    rw [h3]; exact congrArg encode (tab_congr fun i _ ↦ (add_zero _).symm)

theorem rv_addC0' {B : Nat} (hB : 4 * B < USize.size) {v : EVec p} (f : Nat → EF) (g : Nat → F)
    (hv : RV v (tab B f)) :
    RV ⟨B, Words.addWords p (encode (tab B g)) v.c0 B, v.c1, v.c2, v.c3⟩
      (tab B fun i ↦ Ext4.ofBase (g i) + f i) := by
  obtain ⟨-, h0, h1, h2, h3⟩ := rv_tab_iff.mp hv
  refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show Words.addWords p (encode (tab B g)) v.c0 B = _
    rw [h0, addWords_tab hB]; rfl
  · show v.c1 = _
    rw [h1]; exact congrArg encode (tab_congr fun i _ ↦ (zero_add _).symm)
  · show v.c2 = _
    rw [h2]; exact congrArg encode (tab_congr fun i _ ↦ (zero_add _).symm)
  · show v.c3 = _
    rw [h3]; exact congrArg encode (tab_congr fun i _ ↦ (zero_add _).symm)

theorem rv_subC0 {B : Nat} (hB : 4 * B < USize.size) {v : EVec p} (f : Nat → EF) (g : Nat → F)
    (hv : RV v (tab B f)) :
    RV ⟨B, Words.subWords p v.c0 (encode (tab B g)) B, v.c1, v.c2, v.c3⟩
      (tab B fun i ↦ f i - Ext4.ofBase (g i)) := by
  obtain ⟨-, h0, h1, h2, h3⟩ := rv_tab_iff.mp hv
  refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show Words.subWords p v.c0 (encode (tab B g)) B = _
    rw [h0, subWords_tab hB]; rfl
  · show v.c1 = _
    rw [h1]; exact congrArg encode (tab_congr fun i _ ↦ (sub_zero _).symm)
  · show v.c2 = _
    rw [h2]; exact congrArg encode (tab_congr fun i _ ↦ (sub_zero _).symm)
  · show v.c3 = _
    rw [h3]; exact congrArg encode (tab_congr fun i _ ↦ (sub_zero _).symm)

theorem XRel.add {B : Nat} (hB : 4 * B < USize.size) {x y : XVal p} {f g : Nat → EF}
    (hx : XRel B x f) (hy : XRel B y g) : XRel B (x.add B y) fun i ↦ f i + g i := by
  have generic : RV ((x.planes B).add (y.planes B)) (tab B fun i ↦ f i + g i) := by
    have := EVec.add_rel (hx.planes hB) (hy.planes hB) (by rw [hx.planes_n, hy.planes_n])
      (by rw [size_tab]; exact hB)
    rwa [tab_zipWith] at this
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
      show RV ⟨B, Words.addWords p w v.c0 B, v.c1, v.c2, v.c3⟩ _
      rw [hw1]
      exact (rv_addC0' hB g g1 hy).congr_tab fun i hi ↦ by rw [hg1 i hi]
  | ext v =>
    cases y with
    | const b => exact generic
    | base w =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      show RV ⟨B, Words.addWords p v.c0 w B, v.c1, v.c2, v.c3⟩ _
      rw [hw2]
      exact (rv_addC0 hB f g2 hx).congr_tab fun i hi ↦ by rw [hg2 i hi]
    | ext v' => exact generic

theorem XRel.sub {B : Nat} (hB : 4 * B < USize.size) {x y : XVal p} {f g : Nat → EF}
    (hx : XRel B x f) (hy : XRel B y g) : XRel B (x.sub B y) fun i ↦ f i - g i := by
  have generic : RV ((x.planes B).sub (y.planes B)) (tab B fun i ↦ f i - g i) := by
    have := EVec.sub_rel (hx.planes hB) (hy.planes hB) (by rw [hx.planes_n, hy.planes_n])
      (by rw [size_tab]; exact hB)
    rwa [tab_zipWith] at this
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
      show RV ⟨B, Words.subWords p v.c0 w B, v.c1, v.c2, v.c3⟩ _
      rw [hw2]
      exact (rv_subC0 hB f g2 hx).congr_tab fun i hi ↦ by rw [hg2 i hi]
    | ext v' => exact generic

/-- Base words times an extension scalar. -/
theorem rv_scaleBase [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size) (g : Nat → F) (c : EF) :
    RV (XVal.scaleBase B (encode (tab B g)) c) (tab B fun i ↦ Ext4.ofBase (g i) * c) := by
  refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [XVal.scaleBase]
    rw [zeroWords_tab (p := p), mulAddWords_tab hB]
    refine congrArg encode (tab_congr fun i _ ↦ ?_)
    rw [EVec.mul_coords]
    simp only [ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3]
    ring

theorem XRel.mul [Mont32BaseField p] [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size)
    {x y : XVal p}
    {f g : Nat → EF} (hx : XRel B x f) (hy : XRel B y g) :
    XRel B (x.mul B y) fun i ↦ f i * g i := by
  have hBs : 4 * (tab B f).size < USize.size := by rw [size_tab]; exact hB
  cases x with
  | const a =>
    cases y with
    | const b => exact fun i hi ↦ by beta_reduce; rw [hx i hi, hy i hi]
    | base w =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      show RV (XVal.scaleBase B w a) _
      rw [hw2]
      exact (rv_scaleBase hB g2 a).congr_tab fun i hi ↦ by
        rw [hx i hi, hg2 i hi, ext4_mul_comm]
    | ext v =>
      show RV (v.smul a) _
      have := EVec.smul_rel a hy (by rw [size_tab]; exact hB)
      rw [tab_map] at this
      exact this.congr_tab fun i hi ↦ by rw [hx i hi, ext4_mul_comm]
  | base w =>
    obtain ⟨g1, hw1, hg1⟩ := hx
    cases y with
    | const b =>
      show RV (XVal.scaleBase B w b) _
      rw [hw1]
      exact (rv_scaleBase hB g1 b).congr_tab fun i hi ↦ by rw [hg1 i hi, hy i hi]
    | base w' =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      refine ⟨fun i ↦ g1 i * g2 i, ?_, fun i hi ↦ by
        beta_reduce; rw [hg1 i hi, hg2 i hi, ofBase_mul]⟩
      show Words.mulWords p w w' B = _
      rw [hw1, hw2, mulWords_tab hB]
    | ext v =>
      show RV (v.mulBase w) _
      rw [hw1]
      have := EVec.mulBase_rel (tab B g1) hy (by rw [size_tab, size_tab])
        (by rw [size_tab]; exact hB)
      rw [tab_zipWith] at this
      exact this.congr_tab fun i hi ↦ by rw [hg1 i hi, ext4_mul_comm]; rfl
  | ext v =>
    cases y with
    | const b =>
      show RV (v.smul b) _
      have := EVec.smul_rel b hx (by rw [size_tab]; exact hB)
      rw [tab_map] at this
      exact this.congr_tab fun i hi ↦ by rw [hy i hi]
    | base w =>
      obtain ⟨g2, hw2, hg2⟩ := hy
      show RV (v.mulBase w) _
      rw [hw2]
      have := EVec.mulBase_rel (tab B g2) hx (by rw [size_tab, size_tab])
        (by rw [size_tab]; exact hB)
      rw [tab_zipWith] at this
      exact this.congr_tab fun i hi ↦ by rw [hg2 i hi]; rfl
    | ext v' =>
      show RV (v.mul v') _
      have := EVec.mul_rel hx hy (by rw [(rv_tab_iff.mp hx).1, (rv_tab_iff.mp hy).1]) hBs
      rwa [tab_zipWith] at this

/-! ### Extension expressions on a block -/

theorem colsOf_empty (parts R : Nat) : colsOf (p := p) #[] 0 parts R = #[] :=
  Array.eq_empty_of_size_eq_zero (by rw [colsOf, Array.size_ofFn, Nat.zero_mul, Nat.mul_zero])

/-- `evalX` on a block of `B` stored rows from `r0` is the extension expression at those rows,
as `evalWords_eq` for its base expressions, with the permutation trace `rvals` of width `rw`
holding `k` columns of four coordinates, `G j` the environment of stored row `j` over the
extension (its base expressions those of `E j`) and `X j` its permutation rows, challenges and
terminal, which `cpl` and `tpl` tabulate. -/
theorem evalX_rel [Mont32BaseField p] [Binomial4 p] (vals pvals perVals rvals : Array F)
    (w pw np rw n parts R B : Nat) (next : Array Nat) (contiguous : Array (Option Nat))
    (pis : List F) (fA lA tA : Array F) (r0 : Nat) (cpl : Array (EVec p)) (tpl : EVec p)
    (chs : List EF) (terminal : EF) (E : Nat → Expr.Env F F) (G : Nat → Expr.Env F EF)
    (X : Nat → Lookup.ExtExpr.Env EF) (k : Nat) (hR : 0 < R) (hBR : B ∣ R) (hB0 : 0 < B)
    (hBr : B ∣ r0) (hr : r0 + B ≤ parts * R) (hv : parts * R * w ≤ vals.size)
    (hs : 4 * vals.size < USize.size) (hpv : parts * R * pw ≤ pvals.size)
    (hps : 4 * pvals.size < USize.size) (hrv : parts * R * rw ≤ rvals.size)
    (hrs : 4 * rvals.size < USize.size) (hpn : np * n ≤ perVals.size) (hrn : r0 + B ≤ n)
    (hBs : 4 * B < USize.size) (hnext : ∀ j < parts * R, next.getD j 0 < parts * R)
    (hcont : ∀ n0, contiguous.getD (r0 / B) none = some n0 →
      B ∣ n0 ∧ ∀ k < B, next.getD (r0 + k) 0 = n0 + k)
    (hf : r0 + B ≤ fA.size) (hl : r0 + B ≤ lA.size) (ht : r0 + B ≤ tA.size)
    (hEcur : ∀ j < parts * R, ∀ c < w, (E j).cur c = vals.getD (j * w + c) 0)
    (hEnext : ∀ j < parts * R, ∀ c < w, (E j).next c = vals.getD (next.getD j 0 * w + c) 0)
    (hEpcur : ∀ j < parts * R, ∀ c < pw, (E j).prepCur c = pvals.getD (j * pw + c) 0)
    (hEpnext : ∀ j < parts * R, ∀ c < pw,
      (E j).prepNext c = pvals.getD (next.getD j 0 * pw + c) 0)
    (hEper : ∀ j < parts * R, ∀ c,
      (E j).periodic c = if c < np then perVals.getD (c * n + j) 0 else 0)
    (hEpub : ∀ j i, (E j).pub i = pis.getD i 0) (hEconst : ∀ j x, (E j).const x = x)
    (hEf : ∀ j < parts * R, (E j).isFirstRow = fA.getD j 0)
    (hEl : ∀ j < parts * R, (E j).isLastRow = lA.getD j 0)
    (hEt : ∀ j < parts * R, (E j).isTransition = tA.getD j 0)
    (hG : ∀ j < parts * R, ∀ e : Expr F, e.colsBelow w w pw pw = true →
      e.eval (G j) = Ext4.ofBase (e.eval (E j)))
    (hk : k * 4 ≤ rw)
    (hXperm : ∀ j < parts * R, ∀ c < k, (X j).perm c =
      ⟨rvals.getD (j * rw + 4 * c) 0, rvals.getD (j * rw + (4 * c + 1)) 0,
        rvals.getD (j * rw + (4 * c + 2)) 0, rvals.getD (j * rw + (4 * c + 3)) 0⟩)
    (hXnext : ∀ j < parts * R, ∀ c < k, (X j).permNext c =
      ⟨rvals.getD (next.getD j 0 * rw + 4 * c) 0, rvals.getD (next.getD j 0 * rw + (4 * c + 1)) 0,
        rvals.getD (next.getD j 0 * rw + (4 * c + 2)) 0,
        rvals.getD (next.getD j 0 * rw + (4 * c + 3)) 0⟩)
    (hXch : ∀ j i, (X j).challenge i = chs.getD i 0) (hXt : ∀ j, (X j).terminal = terminal)
    (hcpl : ∀ i, RV (cpl.getD i (EVec.zeros B)) (tab B fun _ ↦ chs.getD i 0))
    (htpl : RV tpl (tab B fun _ ↦ terminal)) :
    ∀ e : Lookup.ExtExpr F, e.colsBelow w w pw pw k = true →
      XRel B (evalX (encode (colsOf vals w parts R)) (encode (colsOf pvals pw parts R))
        (encode perVals) (encode (colsOf rvals rw parts R)) w pw np rw n R B next contiguous pis
        (encode fA) (encode lA) (encode tA) cpl tpl r0 e)
        (fun i ↦ e.eval (G (r0 + i)) (X (r0 + i))) := by
  -- The permutation trace read as a trace of its own.
  let E' (j : Nat) : Expr.Env F F :=
    { cur := fun c ↦ rvals.getD (j * rw + c) 0
      next := fun c ↦ rvals.getD (next.getD j 0 * rw + c) 0
      prepCur := fun _ ↦ 0
      prepNext := fun _ ↦ 0
      periodic := fun _ ↦ 0
      pub := fun i ↦ ([] : List F).getD i 0
      const := id
      isFirstRow := fA.getD j 0
      isLastRow := lA.getD j 0
      isTransition := tA.getD j 0 }
  have hperm (e : Expr F) (he : e.colsBelow rw rw 0 0 = true) :
      evalWords (p := p) (encode (colsOf rvals rw parts R)) .empty .empty rw 0 0 n R B next
        contiguous [] (encode fA) (encode lA) (encode tA) r0 e =
      encode (tab B fun i ↦ e.eval (E' (r0 + i))) := by
    have := evalWords_eq rvals #[] #[] rw 0 0 n parts R B next contiguous [] fA lA tA r0 E' hR hBR
      hB0 hBr hr hrv hrs (by rw [Nat.mul_zero]; exact Nat.zero_le _)
      (by show 4 * 0 < USize.size; have := USize.le_size; omega)
      (by rw [Nat.zero_mul]; exact Nat.zero_le _) hrn hBs hnext hcont hf hl ht
      (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (fun _ _ c hc ↦ absurd hc (Nat.not_lt_zero c))
      (fun _ _ c hc ↦ absurd hc (Nat.not_lt_zero c)) (fun _ _ c ↦ by
        rw [ite_eq_right_iff.mpr fun h ↦ absurd h (Nat.not_lt_zero c)]) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) e he
    rwa [colsOf_empty, CompPoly.PackedRepr.encode_empty] at this
  have hrB : ∀ i < B, r0 + i < parts * R := fun i hi ↦ by omega
  intro e he
  induction e with
  | base e =>
    simp only [Lookup.ExtExpr.colsBelow] at he
    refine ⟨fun i ↦ e.eval (E (r0 + i)), ?_, fun i hi ↦ hG _ (hrB i hi) e he⟩
    show evalWords (p := p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e = _
    rw [evalWords_eq vals pvals perVals w pw np n parts R B next contiguous pis fA lA tA r0 E
      hR hBR hB0 hBr hr hv hs hpv hps hpn hrn hBs hnext hcont hf hl ht hEcur hEnext hEpcur hEpnext
      hEper hEpub hEconst hEf hEl hEt e he]
    rfl
  | perm c =>
    simp only [Lookup.ExtExpr.colsBelow, decide_eq_true_eq] at he
    have hc (j : Nat) (hj : j < 4) :
        ((Expr.cur (4 * c + j) : Expr F)).colsBelow rw rw 0 0 = true := by
      simp only [Expr.colsBelow, decide_eq_true_eq]; omega
    show RV ⟨B, _, _, _, _⟩ _
    refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [hperm _ (hc 0 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXperm _ (hrB i hi) c he]; rfl)
    · dsimp only
      rw [hperm _ (hc 1 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXperm _ (hrB i hi) c he]; rfl)
    · dsimp only
      rw [hperm _ (hc 2 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXperm _ (hrB i hi) c he]; rfl)
    · dsimp only
      rw [hperm _ (hc 3 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXperm _ (hrB i hi) c he]; rfl)
  | permNext c =>
    simp only [Lookup.ExtExpr.colsBelow, decide_eq_true_eq] at he
    have hc (j : Nat) (hj : j < 4) :
        ((Expr.next (4 * c + j) : Expr F)).colsBelow rw rw 0 0 = true := by
      simp only [Expr.colsBelow, decide_eq_true_eq]; omega
    show RV ⟨B, _, _, _, _⟩ _
    refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [hperm _ (hc 0 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXnext _ (hrB i hi) c he]; rfl)
    · dsimp only
      rw [hperm _ (hc 1 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXnext _ (hrB i hi) c he]; rfl)
    · dsimp only
      rw [hperm _ (hc 2 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXnext _ (hrB i hi) c he]; rfl)
    · dsimp only
      rw [hperm _ (hc 3 (by decide))]
      exact congrArg encode (tab_congr fun i hi ↦ by
        simp only [Lookup.ExtExpr.eval]; rw [hXnext _ (hrB i hi) c he]; rfl)
  | challenge i =>
    exact (hcpl i).congr_tab fun j _ ↦ (hXch _ i).symm
  | terminal => exact htpl.congr_tab fun j _ ↦ (hXt _).symm
  | add a b iha ihb =>
    simp only [Lookup.ExtExpr.colsBelow, Bool.and_eq_true] at he
    exact XRel.add hBs (iha he.1) (ihb he.2)
  | sub a b iha ihb =>
    simp only [Lookup.ExtExpr.colsBelow, Bool.and_eq_true] at he
    exact XRel.sub hBs (iha he.1) (ihb he.2)
  | mul a b iha ihb =>
    simp only [Lookup.ExtExpr.colsBelow, Bool.and_eq_true] at he
    exact XRel.mul hBs (iha he.1) (ihb he.2)

/-! ### Accumulating the constraints -/

/-- Four planes tabulating the coordinates of `Y`. -/
abbrev planesOf (B : Nat) (Y : Nat → EF) : Array ByteArray :=
  #[encode (tab B fun i ↦ (Y i).c0), encode (tab B fun i ↦ (Y i).c1),
    encode (tab B fun i ↦ (Y i).c2), encode (tab B fun i ↦ (Y i).c3)]

theorem mulAddInto_tab {B : Nat} (hB : 4 * B < USize.size) (f g : Nat → F) (c : F) :
    Words.mulAddInto p (encode (tab B f)) (encode (tab B g)) 0 c.val B =
      encode (tab B fun i ↦ f i + g i * c) := by
  have h := Words.mulAddInto_encode (tab B f) (tab B g) 0 c
    (by rw [size_tab, size_tab]; omega) (by rw [size_tab]; exact hB) (by rw [size_tab]; exact hB)
  rw [size_tab] at h
  rw [h]
  refine congrArg encode (?_ : tab B (fun k ↦ (tab B f).getD k 0 + (tab B g).getD (0 + k) 0 * c) =
    _)
  exact tab_congr fun i hi ↦ by rw [getD_tab _ _ _ hi, Nat.zero_add, getD_tab _ _ _ hi]

/-- Four multiply-adds into a tabulated plane. -/
theorem mulAddInto4_tab {B : Nat} (hB : 4 * B < USize.size) (y a b c d : Nat → F)
    (s0 s1 s2 s3 : F) :
    Words.mulAddInto p (Words.mulAddInto p (Words.mulAddInto p (Words.mulAddInto p
      (encode (tab B y)) (encode (tab B a)) 0 s0.val B) (encode (tab B b)) 0 s1.val B)
      (encode (tab B c)) 0 s2.val B) (encode (tab B d)) 0 s3.val B =
    encode (tab B fun i ↦ y i + a i * s0 + b i * s1 + c i * s2 + d i * s3) := by
  rw [mulAddInto_tab hB, mulAddInto_tab hB, mulAddInto_tab hB, mulAddInto_tab hB]

/-- Accumulating a block value with an extension weight `s` adds the values times `s`. -/
theorem accumulate_rel [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size) (Y : Nat → EF)
    {v : XVal p} {f : Nat → EF} (hv : XRel B v f) (s : EF) :
    accumulate B (planesOf B Y) v s (Binomial4.mulW s.c3, Binomial4.mulW s.c2,
      Binomial4.mulW s.c1) = planesOf B fun i ↦ Y i + f i * s := by
  have generic : ∀ e : EVec p, RV e (tab B f) →
      accumulate B (planesOf B Y) (.ext e) s (Binomial4.mulW s.c3, Binomial4.mulW s.c2,
        Binomial4.mulW s.c1) = planesOf B fun i ↦ Y i + f i * s := by
    intro e he
    obtain ⟨-, h0, h1, h2, h3⟩ := rv_tab_iff.mp he
    simp only [accumulate, XVal.planes, planesOf, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h0, h1, h2, h3, mulAddInto4_tab hB, mulAddInto4_tab hB, mulAddInto4_tab hB,
      mulAddInto4_tab hB]
    have e0 : (tab B fun i ↦ (Y i).c0 + (f i).c0 * s.c0 + (f i).c1 * Binomial4.mulW s.c3 +
        (f i).c2 * Binomial4.mulW s.c2 + (f i).c3 * Binomial4.mulW s.c1) =
        tab B fun i ↦ (Y i + f i * s).c0 := tab_congr fun i _ ↦ by
      rw [Norm.add_c0, Norm.mul_c0, Binomial4.mulW_eq, Binomial4.mulW_eq, Binomial4.mulW_eq]; ring
    have e1 : (tab B fun i ↦ (Y i).c1 + (f i).c0 * s.c1 + (f i).c1 * s.c0 +
        (f i).c2 * Binomial4.mulW s.c3 + (f i).c3 * Binomial4.mulW s.c2) =
        tab B fun i ↦ (Y i + f i * s).c1 := tab_congr fun i _ ↦ by
      rw [Norm.add_c1, Norm.mul_c1, Binomial4.mulW_eq, Binomial4.mulW_eq]; ring
    have e2 : (tab B fun i ↦ (Y i).c2 + (f i).c0 * s.c2 + (f i).c1 * s.c1 +
        (f i).c2 * s.c0 + (f i).c3 * Binomial4.mulW s.c3) =
        tab B fun i ↦ (Y i + f i * s).c2 := tab_congr fun i _ ↦ by
      rw [Norm.add_c2, Norm.mul_c2, Binomial4.mulW_eq]; ring
    have e3 : (tab B fun i ↦ (Y i).c3 + (f i).c0 * s.c3 + (f i).c1 * s.c2 +
        (f i).c2 * s.c1 + (f i).c3 * s.c0) =
        tab B fun i ↦ (Y i + f i * s).c3 := tab_congr fun i _ ↦ by
      rw [Norm.add_c3, Norm.mul_c3]; ring
    rw [e0, e1, e2, e3]
  cases v with
  | base x =>
    obtain ⟨g, hx, hg⟩ := hv
    simp only [accumulate, planesOf, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [hx, mulAddInto_tab hB, mulAddInto_tab hB, mulAddInto_tab hB, mulAddInto_tab hB]
    have e0 : (tab B fun i ↦ (Y i).c0 + g i * s.c0) = tab B fun i ↦ (Y i + f i * s).c0 :=
      tab_congr fun i hi ↦ by
        rw [hg i hi, Norm.add_c0, Norm.mul_c0, ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3]; ring
    have e1 : (tab B fun i ↦ (Y i).c1 + g i * s.c1) = tab B fun i ↦ (Y i + f i * s).c1 :=
      tab_congr fun i hi ↦ by
        rw [hg i hi, Norm.add_c1, Norm.mul_c1, ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3]; ring
    have e2 : (tab B fun i ↦ (Y i).c2 + g i * s.c2) = tab B fun i ↦ (Y i + f i * s).c2 :=
      tab_congr fun i hi ↦ by
        rw [hg i hi, Norm.add_c2, Norm.mul_c2, ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3]; ring
    have e3 : (tab B fun i ↦ (Y i).c3 + g i * s.c3) = tab B fun i ↦ (Y i + f i * s).c3 :=
      tab_congr fun i hi ↦ by
        rw [hg i hi, Norm.add_c3, Norm.mul_c3, ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3]; ring
    rw [e0, e1, e2, e3]
  | const c =>
    have := generic _ ((XRel.planes hB hv))
    simp only [accumulate] at this ⊢
    exact this
  | ext e => exact generic e hv

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

/-! ### All constraints on a block -/

theorem accumulate_fold [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size)
    (ev : Lookup.ExtExpr F → XVal p) (val : Lookup.ExtExpr F → Nat → EF) :
    ∀ (L : List (Lookup.ExtExpr F × EF × F × F × F)) (Y : Nat → EF),
      (∀ x ∈ L, x.2.2 = (Binomial4.mulW x.2.1.c3, Binomial4.mulW x.2.1.c2,
        Binomial4.mulW x.2.1.c1)) → (∀ x ∈ L, XRel B (ev x.1) (val x.1)) →
      L.foldl (fun acc x ↦ accumulate B acc (ev x.1) x.2.1 x.2.2) (planesOf B Y) =
        planesOf B fun i ↦ L.foldl (fun y x ↦ y + val x.1 i * x.2.1) (Y i)
  | [], Y, _, _ => rfl
  | x :: L, Y, hw, hv => by
    rw [List.foldl_cons, hw x List.mem_cons_self,
      accumulate_rel hB Y (hv x List.mem_cons_self) x.2.1]
    exact accumulate_fold hB ev val L _ (fun y hy ↦ hw y (List.mem_cons_of_mem _ hy))
      (fun y hy ↦ hv y (List.mem_cons_of_mem _ hy))

/-- The accumulated constraints on a block are their values folded by `α` in Horner's order. -/
theorem accumulateAll_eq [Mont32BaseField p] [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size)
    (alpha : EF) (ext : List (Lookup.ExtExpr F)) (ev : Lookup.ExtExpr F → XVal p)
    (val : Lookup.ExtExpr F → Nat → EF) (hv : ∀ c ∈ ext, XRel B (ev c) (val c)) :
    accumulateAll B ev (ext.zip (weightsOf alpha ext.length)) =
      planesOf B fun i ↦ ext.foldl (fun acc c ↦ acc * alpha + val c i) 0 := by
  have hz : (#[CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B,
      CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B,
      CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B,
      CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B] : Array ByteArray) =
      planesOf (p := p) B fun _ ↦ 0 := by
    rw [zeroWords_tab (p := p)]; rfl
  unfold accumulateAll
  dsimp only
  rw [hz, accumulate_fold hB ev val _ _ (fun x hx ↦ ?_) (fun x hx ↦ hv x.1 (List.of_mem_zip hx).1)]
  · congr 1
    funext i
    have e1 : ((ext.zip (weightsOf alpha ext.length)).foldl
        (fun y x ↦ y + val x.1 i * x.2.1) 0) =
        (((ext.map (val · i)).zip ((List.range (ext.map (val · i)).length).map fun k ↦
          Ext.pow alpha ((ext.map (val · i)).length - 1 - k))).foldl
          (fun y x ↦ y + x.1 * x.2) 0) := by
      rw [List.length_map, weightsOf, List.zip_map, List.foldl_map, List.zip_map_right,
        List.foldl_map]
      rfl
    rw [e1, weighted_eq_horner, List.foldl_map]
  · obtain ⟨-, h2⟩ := List.of_mem_zip hx
    obtain ⟨k, -, hk⟩ := List.mem_map.mp h2
    rw [← hk]

/-! ### The specification row by row -/

section Spec
variable [Mont32BaseField p] [Binomial4 p]

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


/-- **The fast LogUp quotient is the specification's** on related extensions of the trace, the
preprocessed trace and the permutation trace, for extension constraints reading their columns, `k`
permutation columns of four coordinates. -/
theorem lookupQuotientWith_rel (A : Air F) (ext : List (Lookup.ExtExpr F)) (pis : List F)
    (d l : Nat) (chs : List EF) (terminal alpha : EF) (k : Nat) {tr : PMat} {s : Mat F}
    {prep : Option PMat} {ps : Option (Mat F)} {perm : PMat} {rs : Mat F}
    (h : RM tr s) (hs : MatOk s) (hh : 2 ^ (d + l) ≤ s.height) (hp : Option.Rel RM prep ps)
    (hps : ∀ q ∈ ps, MatOk q ∧ q.height = s.height) (hr : RM perm rs) (hrs : MatOk rs)
    (hrh : rs.height = s.height) (hk : k * 4 ≤ rs.width)
    (hc : ∀ c ∈ ext, c.colsBelow s.width s.width ((ps.map (·.width)).getD 0)
      ((ps.map (·.width)).getD 0) k) :
    lookupQuotientWith (quotientTables (p := p) d l) A ext pis tr prep perm chs terminal alpha =
      lookupQuotientOfLde A ext pis d l s ps rs chs terminal alpha := by
  have hRM := h
  have hRr := hr
  obtain ⟨hw, hhe, hv⟩ := h
  obtain ⟨hrw, hrhe, hrv⟩ := hr
  obtain ⟨-, -, hvs', hadd⟩ := hs
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
  have hpcols (parts R : Nat)
      (hM : parts * R * (prepOrEmpty ps s.height).width ≤
        (prepOrEmpty ps s.height).values.size) :
      (prep.map (transposePieces · parts R)).getD ByteArray.empty =
        encode (colsOf (prepOrEmpty ps s.height).values (prepOrEmpty ps s.height).width parts
          R) := by
    cases hp with
    | none =>
      show ByteArray.empty = encode (colsOf #[] 0 parts R)
      rw [colsOf_empty]
      rfl
    | @some a q hr => exact transposePieces_rel hr parts R hM husp
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
  generalize prepOrEmpty ps s.height = sp at hpw hpw' hspv husp hpcols hpq
  rw [hpw] at hc
  have hn' := hh
  unfold lookupQuotientWith
  have hTd : (quotientTables (p := p) d l).degreeBits = d := rfl
  have hTl : (quotientTables (p := p) d l).logChunks = l := rfl
  have hTp : (quotientTables (p := p) d l).perm = bitRevPerm (d + l) := rfl
  have hTz : (quotientTables (p := p) d l).invZh = batchInv (qZh d l) := rfl
  have hTB : (quotientTables (p := p) d l).B =
      min (2 ^ (d + l) / (if 2 ^ (d + l) < 4096 then 1 else 16)) 256 := rfl
  have hcont := tables_contiguous (p := p) d l
  have hnext := tables_next (p := p) d l
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [hTd, hTl, hTp, hTz, tables_first, tables_last, tables_trans] at *
  rw [hv, hw, hrv, hrw] at *
  generalize quotientTables (p := p) d l = T at hcont hnext hTB ⊢
  have hpow : ∃ e, 2 ^ (d + l) / (if 2 ^ (d + l) < 4096 then 1 else 16) = 2 ^ e ∧
      (if 2 ^ (d + l) < 4096 then 1 else 16) * 2 ^ e = 2 ^ (d + l) := by
    split
    · exact ⟨d + l, Nat.div_one _, Nat.one_mul _⟩
    · rename_i hge
      have h12 : 12 ≤ d + l := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega : d + l < 12))
          (le_refl _))
      have h16 : 2 ^ (d + l) = 16 * 2 ^ (d + l - 4) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]
        congr 1
        omega
      refine ⟨d + l - 4, ?_, h16.symm⟩
      rw [h16, Nat.mul_div_cancel_left _ (by decide)]
  generalize (if 2 ^ (d + l) < 4096 then 1 else 16) = parts at hpow hTB ⊢
  obtain ⟨e, hRe, hpe⟩ := hpow
  rw [hRe] at hTB ⊢
  generalize T.B = B at hcont hTB ⊢
  have hparts : 0 < parts := Nat.pos_of_ne_zero fun h0 ↦ by
    rw [h0, Nat.zero_mul] at hpe; exact absurd hpe (Nat.two_pow_pos _).ne
  have hB0 : 0 < B := by rw [hTB]; exact Nat.lt_min.mpr ⟨Nat.two_pow_pos _, by decide⟩
  have hB256 : B ≤ 256 := by rw [hTB]; exact Nat.min_le_right _ _
  have hBR : B ∣ 2 ^ e := by
    rw [hTB]
    by_cases h8 : e ≤ 8
    · rw [Nat.min_eq_left (le_trans (Nat.pow_le_pow_right (by decide) h8) (le_refl (2 ^ 8)))]
    · rw [Nat.min_eq_right
        (le_trans (le_refl (2 ^ 8)) (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact Nat.pow_dvd_pow 2 (by omega)
  have hBn : B ∣ 2 ^ (d + l) := by rw [← hpe]; exact Dvd.dvd.mul_left hBR parts
  have hM : parts * 2 ^ e * s.width ≤ s.values.size := by
    rw [hpe, hvs', Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hn'
  have hMp : parts * 2 ^ e * sp.width ≤ sp.values.size := by
    rw [hpe, hspv, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hn'
  have hMr : parts * 2 ^ e * rs.width ≤ rs.values.size := by
    rw [hpe, hrvs, hrh, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hn'
  rw [transposePieces_rel hRM parts (2 ^ e) hM hus, hpcols parts (2 ^ e) hMp, hpw',
    transposePieces_rel hRr parts (2 ^ e) hMr hrus, NTTFast.Packed.Native.encodeFields_eq]
  unfold lookupQuotientOfLde
  dsimp only
  rw [hpq]
  generalize A.periodic.map (fun col ↦ periodicOnQuotient col d l) = pl
  obtain ⟨perVals, hPV⟩ : ∃ v, v = Array.ofFn (n := pl.toArray.size * 2 ^ (d + l)) fun k ↦
      periodicRow (pl.toArray.getD (k.val / 2 ^ (d + l)) #[])
        ((bitRevPerm (d + l)).getD (k.val % 2 ^ (d + l)) 0) := ⟨_, rfl⟩
  rw [← hPV]
  have hPVs : perVals.size = pl.toArray.size * 2 ^ (d + l) := by rw [hPV, Array.size_ofFn]
  have hPVget (c j : Nat) (hj : j < 2 ^ (d + l)) :
      periodicRow (pl.getD c #[]) ((bitRevPerm (d + l)).getD j 0) =
        if c < pl.toArray.size then perVals.getD (c * 2 ^ (d + l) + j) 0 else 0 := by
    split
    · rename_i hc
      have h1 := Nat.mul_le_mul_right (2 ^ (d + l)) (hc : c + 1 ≤ pl.toArray.size)
      rw [Nat.succ_mul] at h1
      have hd : (c * 2 ^ (d + l) + j) / 2 ^ (d + l) = c := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hj,
          Nat.zero_add]
      have hm : (c * 2 ^ (d + l) + j) % 2 ^ (d + l) = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have hpl : pl.toArray.getD c #[] = pl.getD c #[] := by
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
      rw [hPV, NTTFast.Packed.getD_ofFn_bounded _ _ (by omega), hd, hm, hpl]
    · rename_i hc
      rw [List.size_toArray] at hc
      rw [List.getD_eq_default _ _ (by omega)]
      simp only [periodicRow, Array.size_empty, Array.getD_eq_getD_getElem?,
        Array.getElem?_empty, Option.getD_none]
  -- The specification's values, row by row.
  let tq := Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l)))
  let pq := Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))
  let rq := Mat.ofValues rs.width (2 ^ (d + l)) (permuteRows rs (bitRevPerm (d + l)))
  let spec (r : Nat) : EF := Challenge.smul ((batchInv (qZh d l) : Array F).getD (r % 2 ^ l) 0)
    (ext.foldl (fun acc c ↦ acc * alpha + c.eval (lqEnv pis d l tq pq pl r)
      (lqAux d l rq chs terminal r)) 0)
  have hspec : Lookup.lookupQuotientValues ext pis d l tq pq rq pl chs terminal alpha =
      Array.ofFn (n := 2 ^ (d + l)) fun r ↦ spec r.val := by
    apply Array.ext (by rw [Lookup.lookupQuotientValues, Array.size_ofFn, Array.size_ofFn])
    intro r h1 h2
    rw [Array.size_ofFn] at h2
    rw [Array.getElem_ofFn, ← getD_lt _ _ (d := 0) h1]
    exact lookupQuotientValues_getD ext pis d l tq pq rq pl chs terminal alpha r h2
  rw [hspec]
  rw [parChunks_eq_blocks (2 ^ (d + l) / B) (min (2 ^ (d + l) / B) 16) B _
    (fun j ↦ spec ((bitRevPerm (d + l)).getD j 0)) ?_
    (Or.inl (Nat.lt_min.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Nat.two_pow_pos _) hBn) hB0,
      by decide⟩))]
  · show Array.map _ (bitRevPerm (d + l)) = _
    rw [Nat.div_mul_cancel hBn]
    apply Array.ext (by rw [Array.size_map, Array.size_ofFn, size_bitRevPerm])
    intro r h1 h2
    rw [Array.size_ofFn] at h2
    have hP := bitRevPerm_getD_lt (d + l) r h2
    have hPr : (bitRevPerm (d + l))[r]'(by rw [size_bitRevPerm]; exact h2) =
        (bitRevPerm (d + l)).getD r 0 := by
      rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by rw [size_bitRevPerm]; exact h2),
        Option.getD_some]
    rw [Array.getElem_map, Array.getElem_ofFn, hPr, NTTFast.Packed.getD_ofFn_bounded _ _ hP,
      bitRevPerm_getD_getD _ _ h2]
  intro s0 len hlen
  show List.foldl _ (Array.emptyWithCapacity (len * B)) _ = _
  simp only [Nat.add_sub_cancel_left]
  rw [CompStark.Stark.foldl_blocks, Array.emptyWithCapacity_eq, Array.empty_append]
  apply congrArg
  funext r
  have hr : r.val < len * B := r.isLt
  have hlen' : s0 + r.val / B < 2 ^ (d + l) / B := by
    have : r.val / B < len := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm B len]; exact hr)
    rcases hlen with hlen | hlen
    · omega
    · have h0 : len * B = 0 := by rw [hlen, Nat.zero_mul]
      omega
  rw [show s0 * B + r.val = (s0 + r.val / B) * B + r.val % B by
    rw [Nat.add_mul, Nat.add_assoc, Nat.div_add_mod']]
  generalize s0 + r.val / B = blk at hlen' ⊢
  have hi : r.val % B < B := Nat.mod_lt _ hB0
  generalize r.val % B = i at hi ⊢
  have hblkB : blk * B + B ≤ 2 ^ (d + l) := by
    have := Nat.mul_le_mul_right B (hlen' : blk + 1 ≤ 2 ^ (d + l) / B)
    rw [Nat.succ_mul, Nat.div_mul_cancel hBn] at this
    exact this
  have hsizeP : (bitRevPerm (d + l)).size = parts * 2 ^ e := by rw [size_bitRevPerm, hpe]
  have hBs : 4 * B < USize.size := by have := USize.le_size; omega
  let π (j : Nat) : Nat := (bitRevPerm (d + l)).getD j 0
  let E (j : Nat) : Expr.Env F F := rowEnv tq pq pl (2 ^ (d + l)) (2 ^ l) pis (qFirst d l)
    (qLast d l) (qTrans d l) (π j)
  let G (j : Nat) : Expr.Env F EF := lqEnv pis d l tq pq pl (π j)
  let X (j : Nat) : Lookup.ExtExpr.Env EF := lqAux d l rq chs terminal (π j)
  have hsel (sel : Array F) (j : Nat) (hj : j < parts * 2 ^ e) :
      sel.getD (π j) 0 = ((bitRevPerm (d + l)).map fun i ↦ sel.getD i 0).getD j 0 := by
    rw [getD_map_lt _ _ j (by rw [hsizeP]; exact hj) 0 0]
  have hrow (m : Mat F) (j c : Nat) (hj : j < 2 ^ (d + l)) (hc : c < m.width) :
      (permuteRows m (bitRevPerm (d + l))).getD (π j * m.width + c) 0 =
        m.values.getD (j * m.width + c) 0 := by
    rw [permuteRows_getD m _ _ c (by rw [size_bitRevPerm]; exact bitRevPerm_getD_lt _ _ hj) hc,
      bitRevPerm_getD_getD _ _ hj]
  have hrowN (m : Mat F) (j c : Nat) (hj : j < 2 ^ (d + l)) (hc : c < m.width) :
      (permuteRows m (bitRevPerm (d + l))).getD (((π j + 2 ^ l) % 2 ^ (d + l)) * m.width + c)
        0 = m.values.getD (T.next.getD j 0 * m.width + c) 0 := by
    rw [permuteRows_getD m _ _ c (by rw [size_bitRevPerm]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
      hc, hnext j hj]
  have hval : ∀ c ∈ ext, XRel B (evalX (encode (colsOf s.values s.width parts (2 ^ e)))
      (encode (colsOf sp.values sp.width parts (2 ^ e))) (encode perVals)
      (encode (colsOf rs.values rs.width parts (2 ^ e))) s.width sp.width pl.toArray.size
      rs.width (2 ^ (d + l)) (2 ^ e) B T.next T.contiguous pis
      (encode ((bitRevPerm (d + l)).map fun i ↦ (qFirst d l : Array F).getD i 0))
      (encode ((bitRevPerm (d + l)).map fun i ↦ (qLast d l : Array F).getD i 0))
      (encode ((bitRevPerm (d + l)).map fun i ↦ (qTrans d l : Array F).getD i 0))
      (chs.toArray.map fun c ↦ (XVal.const c).planes B) ((XVal.const terminal).planes B)
      (blk * B) c) (fun i ↦ c.eval (G (blk * B + i)) (X (blk * B + i))) := by
    intro c hcm
    refine evalX_rel s.values sp.values perVals rs.values s.width sp.width pl.toArray.size
      rs.width (2 ^ (d + l)) parts (2 ^ e) B T.next T.contiguous pis _ _ _ (blk * B) _ _ chs
      terminal E G X k (Nat.two_pow_pos e) hBR hB0 (Dvd.intro_left blk rfl)
      (by rw [hpe]; exact hblkB) hM hus hMp husp hMr hrus (by rw [hPVs]) hblkB hBs ?_ ?_
      (by rw [Array.size_map, hsizeP, hpe]; exact hblkB)
      (by rw [Array.size_map, hsizeP, hpe]; exact hblkB)
      (by rw [Array.size_map, hsizeP, hpe]; exact hblkB) ?_ ?_ ?_ ?_
      (fun j hj c ↦ hPVget c j (by rw [← hpe]; exact hj)) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun j hj ↦ hsel _ j hj) (fun j hj ↦ hsel _ j hj) (fun j hj ↦ hsel _ j hj)
      ?_ hk ?_ ?_ (fun _ _ ↦ rfl) (fun _ ↦ rfl) ?_ ?_ c (hc c hcm)
    · intro j hj
      rw [hpe] at hj ⊢
      rw [hnext j hj]
      exact bitRevPerm_getD_lt _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
    · intro n0 h0
      rw [Nat.mul_div_cancel _ hB0] at h0
      exact hcont blk n0 h0
    · intro j hj c hc
      rw [hpe] at hj
      exact hrow s j c hj hc
    · intro j hj c hc
      rw [hpe] at hj
      exact hrowN s j c hj hc
    · intro j hj c hc
      rw [hpe] at hj
      exact hrow sp j c hj hc
    · intro j hj c hc
      rw [hpe] at hj
      exact hrowN sp j c hj hc
    · intro j hj e he
      exact (Expr.eval_hom (Ext4.ofBase (p := p)) (fun a b ↦ (ofBase_add a b).symm)
        (fun a b ↦ (ofBase_sub a b).symm) (fun a b ↦ (ofBase_mul a b).symm) s.width s.width
        sp.width sp.width (E j) (G j) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl rfl e he).symm
    · intro j hj c hc
      rw [hpe] at hj
      have hb (e : Nat) (he : e < 4) : c * 4 + e < rs.width := by
        have : (c + 1) * 4 ≤ k * 4 := Nat.mul_le_mul_right 4 hc
        omega
      show (⟨(permuteRows rs (bitRevPerm (d + l))).getD (π j * rs.width + (c * 4 + 0)) 0,
        (permuteRows rs (bitRevPerm (d + l))).getD (π j * rs.width + (c * 4 + 1)) 0,
        (permuteRows rs (bitRevPerm (d + l))).getD (π j * rs.width + (c * 4 + 2)) 0,
        (permuteRows rs (bitRevPerm (d + l))).getD (π j * rs.width + (c * 4 + 3)) 0⟩ : EF) = _
      rw [hrow rs j _ hj (hb 0 (by decide)), hrow rs j _ hj (hb 1 (by decide)),
        hrow rs j _ hj (hb 2 (by decide)), hrow rs j _ hj (hb 3 (by decide)),
        Nat.mul_comm c 4, Nat.add_zero]
    · intro j hj c hc
      rw [hpe] at hj
      have hb (e : Nat) (he : e < 4) : c * 4 + e < rs.width := by
        have : (c + 1) * 4 ≤ k * 4 := Nat.mul_le_mul_right 4 hc
        omega
      show (⟨(permuteRows rs (bitRevPerm (d + l))).getD
          (((π j + 2 ^ l) % 2 ^ (d + l)) * rs.width + (c * 4 + 0)) 0,
        (permuteRows rs (bitRevPerm (d + l))).getD
          (((π j + 2 ^ l) % 2 ^ (d + l)) * rs.width + (c * 4 + 1)) 0,
        (permuteRows rs (bitRevPerm (d + l))).getD
          (((π j + 2 ^ l) % 2 ^ (d + l)) * rs.width + (c * 4 + 2)) 0,
        (permuteRows rs (bitRevPerm (d + l))).getD
          (((π j + 2 ^ l) % 2 ^ (d + l)) * rs.width + (c * 4 + 3)) 0⟩ : EF) = _
      rw [hrowN rs j _ hj (hb 0 (by decide)), hrowN rs j _ hj (hb 1 (by decide)),
        hrowN rs j _ hj (hb 2 (by decide)), hrowN rs j _ hj (hb 3 (by decide)),
        Nat.mul_comm c 4, Nat.add_zero]
    · intro i
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray]
      cases hci : chs[i]? with
      | none =>
        rw [Option.map_none, Option.getD_none, List.getD_eq_getElem?_getD, hci,
          Option.getD_none]
        have := EVec.zeros_rel (p := p) B
        rwa [show Array.replicate B (0 : EF) = tab B fun _ ↦ 0 from by
          apply Array.ext (by simp only [Array.size_replicate, size_tab])
          intro i h1 h2
          simp only [tab, Array.getElem_replicate, Array.getElem_ofFn]] at this
      | some x =>
        rw [Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD, hci, Option.getD_some]
        exact XRel.planes hBs (x := .const x) (fun _ _ ↦ rfl)
    · exact XRel.planes hBs (x := .const terminal) (fun _ _ ↦ rfl)
  rw [accumulateAll_eq hBs alpha ext _ _ hval]
  have hrd (Y : Nat → EF) : (⟨word (planesOf B Y)[0]! i, word (planesOf B Y)[1]! i,
      word (planesOf B Y)[2]! i, word (planesOf B Y)[3]! i⟩ : EF) = Y i := by
    simp only [planesOf]
    rw [(getElem!_lit4 _ _ _ _).1, (getElem!_lit4 _ _ _ _).2.1, (getElem!_lit4 _ _ _ _).2.2.1,
      (getElem!_lit4 _ _ _ _).2.2.2]
    rw [word_tab hBs _ i hi, word_tab hBs _ i hi, word_tab hBs _ i hi, word_tab hBs _ i hi]
  rw [hrd]
  rfl

end Spec

end CompStark.Stark.Fast
