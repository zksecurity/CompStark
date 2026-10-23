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

theorem replicate_tab (B : Nat) (c : F) : Array.replicate B c = tab B fun _ ↦ c := by
  apply Array.ext (by simp only [Array.size_replicate, tab, Array.size_ofFn])
  intro i h1 h2
  simp only [tab, Array.getElem_replicate, Array.getElem_ofFn]

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

/-- Coordinate `j` of an extension element. -/
def cj (x : EF) : Nat → F
  | 0 => x.c0
  | 1 => x.c1
  | 2 => x.c2
  | 3 => x.c3
  | _ => 0

theorem cj_add (a b : EF) (j : Nat) : cj (a + b) j = cj a j + cj b j := by
  rcases j with _ | _ | _ | _ | j
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (add_zero 0).symm

theorem cj_zero (j : Nat) : cj (0 : EF) j = 0 := by
  rcases j with _ | _ | _ | _ | j <;> rfl

/-- Coordinate `j` of a product: the first factor's coordinates times the second's shifted by
powers of `X` (`xPowMul`). -/
theorem cj_mul [Binomial4 p] (v s : EF) (j : Nat) (hj : j < 4) :
    cj (v * s) j = v.c0 * cj s j + v.c1 * cj (xPowMul 1 s) j + v.c2 * cj (xPowMul 2 s) j +
      v.c3 * cj (xPowMul 3 s) j := by
  have h1 : xPowMul 1 s = ⟨Binomial4.mulW s.c3, s.c0, s.c1, s.c2⟩ := rfl
  have h2 : xPowMul 2 s = ⟨Binomial4.mulW s.c2, Binomial4.mulW s.c3, s.c0, s.c1⟩ := rfl
  have h3 : xPowMul 3 s = ⟨Binomial4.mulW s.c1, Binomial4.mulW s.c2, Binomial4.mulW s.c3,
    s.c0⟩ := rfl
  rw [h1, h2, h3]
  rcases j with _ | _ | _ | _ | j
  · simp only [cj, Norm.mul_c0, Binomial4.mulW_eq]; ring
  · simp only [cj, Norm.mul_c1, Binomial4.mulW_eq]; ring
  · simp only [cj, Norm.mul_c2, Binomial4.mulW_eq]; ring
  · simp only [cj, Norm.mul_c3]
  · omega

/-- Coordinate `j` of products zipped with weights by index, accumulated. -/
theorem cj_foldl_zip [Binomial4 p] {α : Type} (u : α → EF) (g : Nat → EF) (j : Nat) :
    ∀ (cs : List α) (n : Nat) (y : EF),
      cj (((cs.map u).zip ((List.range' n cs.length).map g)).foldl
        (fun y x ↦ y + x.1 * x.2) y) j =
        ((cs.zipIdx n).map fun (c, k) ↦ cj (u c * g k) j).foldl (· + ·) (cj y j)
  | [], _, _ => rfl
  | c :: cs, n, y => by
    rw [List.length_cons, List.range'_succ, List.map_cons, List.map_cons, List.zip_cons_cons,
      List.foldl_cons, List.zipIdx_cons, List.map_cons, List.foldl_cons, ← cj_add]
    exact cj_foldl_zip u g j cs (n + 1) _

/-- The extension coordinates of `Prog`'s quadruples over `X⁴ = W`. -/
def toE [Binomial4 p] (x : Prog.Coords F (Binomial4.W (p := p))) : EF := ⟨x.c0, x.c1, x.c2, x.c3⟩

theorem toE_mul [Binomial4 p] (a b : Prog.Coords F (Binomial4.W (p := p))) :
    toE (a * b) = toE a * toE b := by
  apply Norm.ext <;> simp only [Norm.mul_c0, Norm.mul_c1, Norm.mul_c2, Norm.mul_c3] <;> rfl

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


theorem coeffs_getD (x : EF) (j : Nat) : (Challenge.coeffs x).getD j 0 = cj x j := by
  rcases j with _ | _ | _ | _ | j <;> rfl

/-- The coordinates of extension elements laid out four by four. -/
theorem flatMap_coeffs_getD (xs : List EF) (q e : Nat) (he : e < 4) :
    (xs.toArray.flatMap fun c ↦ (Challenge.coeffs c).toArray).getD (4 * q + e) 0 =
      cj (xs.getD q 0) e := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, Array.toList_flatMap]
  induction xs generalizing q with
  | nil =>
    simp only [List.flatMap_nil, List.getElem?_nil, Option.getD_none, List.getD_nil]
    exact (cj_zero e).symm
  | cons x xs ih =>
    rw [List.flatMap_cons, Mont32.coeffs_ext4]
    rcases q with _ | q
    · rw [List.getElem?_append_left (by simp only [List.length_cons, List.length_nil]; omega),
        List.getD_cons_zero]
      rcases e with _ | _ | _ | _ | e
      · rfl
      · rfl
      · rfl
      · rfl
      · omega
    · rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega),
        List.getD_cons_succ]
      simp only [List.length_cons, List.length_nil]
      rw [show 4 * (q + 1) + e - (0 + 1 + 1 + 1 + 1) = 4 * q + e by omega]
      exact ih q

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
  obtain ⟨hw, -, hv⟩ := h
  obtain ⟨hrw, -, hrv⟩ := hr
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
  have hpwords : (prep.map (·.words)).getD ByteArray.empty =
      encode (prepOrEmpty ps s.height).values := by
    cases hp with
    | none => rfl
    | @some a q hr => exact hr.2.2
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
  generalize prepOrEmpty ps s.height = sp at hpw hpw' hpwords hspv husp hpq
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
  let WT : Array F := Array.ofFn (n := 16 * K) fun i ↦
    (Challenge.coeffs (xPowMul (i.val / 4 % 4) (Ext.pow alpha (K - 1 - i.val / 16)))).getD
      (i.val % 4) 0
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
  let Q (j e : Nat) : F := cj (V ((bitRevPerm (d + l)).getD j 0)) e
  have hspec : Lookup.lookupQuotientValues ext pis d l tq pq rq pl chs terminal alpha =
      Array.ofFn (n := 2 ^ (d + l)) fun r ↦ Ext4.smul
        ((batchInv (qZh d l) : Array F).getD (r.val % 2 ^ l) 0) (V r.val) := by
    apply Array.ext (by rw [Lookup.lookupQuotientValues, Array.size_ofFn, Array.size_ofFn])
    intro r h1 h2
    rw [Array.size_ofFn] at h2
    rw [Array.getElem_ofFn, ← getD_lt _ _ (d := 0) h1]
    exact lookupQuotientValues_getD ext pis d l tq pq rq pl chs terminal alpha r h2
  rw [hspec, hpw', hpwords, hv, hw, hrv, hrw, hWT,
    quotientBlocks_eq d l _ SC WT _ Q ?hblk]
  case hblk =>
    intro r0 hdvd hr0
    obtain ⟨hB0, -, -⟩ := tables_B (p := p) d l
    rw [tables_first, tables_last, tables_trans]
    generalize (quotientTables (p := p) d l).B = B at hdvd hr0 hB0 ⊢
    refine ⟨blockT s r0 B, 0, B, qLoads d l s sp rs pl (quotientTables (p := p) d l).next r0 B,
      ?_, hsS.blockT hr0, qLoads_addr hsS hspS hrsS pl _ hr0 hnU, fun ins hins ↦ ?_,
      fun i hi st0 hst0 j hj ↦ ?_⟩
    · rw [transposeRows_blockT s r0 B (hsS.block hr0) hus,
        transposeRows_blockT sp r0 B (hspS.block hr0) husp,
        transposeRows_blockT rs r0 B (hrsS.block hr0) hrus]
      rfl
    · refine Prog.Instr.inRange_of (cq := (· < s.width))
        (lq := Prog.Src.Below s.width sp.width sp.width rs.width) (fun c hc ↦ ?_)
        (qLoads_inRange hsS hspS hrsS pl hr0)
        ins ((Prog.compileExt_run Binomial4.W np ext ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0,
          fun _ _ ↦ 0⟩ ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2 ins hins)
        (Prog.compileExt_leafOk Binomial4.W np ext s.width s.width sp.width sp.width k rs.width
          (by omega) hc ins hins)
      rw [size_blockT, Nat.zero_add]
      have := Nat.mul_le_mul_right B (show c + 1 ≤ s.width by exact hc)
      rw [Nat.succ_mul] at this; exact this
    · have hri : r0 + i < 2 ^ (d + l) := by omega
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := qLoads_env d l s sp rs pl pis SC WT r0 B i hi hri
      set ctx := Prog.blockCtx (blockT s r0 B) 0 B
        (qLoads d l s sp rs pl (quotientTables (p := p) d l).next r0 B) SC WT B i with hctx
      let R := (bitRevPerm (d + l)).getD (r0 + i) 0
      let u (c : Lookup.ExtExpr F) : EF := c.eval (lqEnv pis d l tq pq pl R)
        (lqAux d l rq chs terminal R)
      let g (k : Nat) : EF := Ext.pow alpha (K - 1 - k)
      -- The scalars: the public values, then the terminal's and the challenges' coordinates.
      have hsc (q e : Nat) (he : e < 4) : ctx.scalar (np + (4 * q + e)) =
          cj ((terminal :: chs).getD q 0) e := by
        show SC.getD (pis.length + (4 * q + e)) 0 = _
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by
          simp only [List.size_toArray]; omega), List.size_toArray, Nat.add_sub_cancel_left,
          ← Array.getD_eq_getD_getElem?]
        exact flatMap_coeffs_getD _ q e he
      have hsc4 (q : Nat) : toE (ctx.scalars4 Binomial4.W (np + 4 * q)) =
          (terminal :: chs).getD q 0 := by
        have h0 := hsc q 0 (by decide)
        have h1 := hsc q 1 (by decide)
        have h2 := hsc q 2 (by decide)
        have h3 := hsc q 3 (by decide)
        simp only [Nat.add_zero, ← Nat.add_assoc] at h0 h1 h2 h3
        simp only [toE, Prog.Ctx.scalars4, h0, h1, h2, h3]
        rfl
      -- The permutation columns of a stored row.
      have hpermAt (R' : Nat) (c : Nat) (hc : c < k) (x : Nat → F)
          (hx : ∀ e < 4, x (4 * c + e) = rq.values.getD (R' * rq.width + (c * 4 + e)) 0) :
          (⟨x (4 * c), x (4 * c + 1), x (4 * c + 2), x (4 * c + 3)⟩ : EF) =
            Challenge.ofCoeffs ((List.range (Challenge.d EF)).map fun e ↦
              rq.values.getD (R' * rq.width + (c * Challenge.d EF + e)) 0) := by
        rw [Mont32.ofCoeffs_ext4, Mont32.d_ext4]
        have h0 := hx 0 (by decide)
        have h1 := hx 1 (by decide)
        have h2 := hx 2 (by decide)
        have h3 := hx 3 (by decide)
        rw [Nat.add_zero] at h0
        rw [h0, h1, h2, h3]
        rfl
      have hu (c : Lookup.ExtExpr F) (hcm : c ∈ ext) :
          toE (c.eval (ctx.envQ Binomial4.W np) (ctx.auxQ Binomial4.W np)) = u c := by
        refine Lookup.ExtExpr.eval_hom toE (fun _ _ ↦ Norm.ext rfl rfl rfl rfl)
          (fun _ _ ↦ Norm.ext rfl rfl rfl rfl) toE_mul s.width s.width sp.width sp.width k _ _
          _ _ (fun e he ↦ ?_) (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun jj ↦ ?_) ?_ c (hc c hcm)
        · rw [Prog.Expr.eval_envQ, eval_pubBelow]
          show Ext4.ofBase _ = _
          have hb := Expr.eval_hom (R := F) (S := EF) Ext4.ofBase (fun a b ↦ (ofBase_add a b).symm)
            (fun a b ↦ (ofBase_sub a b).symm) (fun a b ↦ (ofBase_mul a b).symm) s.width s.width
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
        · refine hpermAt R c hc (fun m ↦ ctx.src (.permCur m)) fun e he ↦ ?_
          show (blockT rs r0 B).getD ((4 * c + e) * B + i) 0 = _
          rw [blockT_getD rs r0 B _ i (by omega) hi, show c * 4 + e = 4 * c + e by ring]
          exact (permuteRows_bitRev rs d l _ _ hri (by omega)).symm
        · refine hpermAt ((R + 2 ^ l) % 2 ^ (d + l)) c hc (fun m ↦ ctx.src (.permNext m))
            fun e he ↦ ?_
          show rs.values.getD ((quotientTables (p := p) d l).next.getD (r0 + i) 0 * rs.width +
            (4 * c + e)) 0 = _
          rw [show c * 4 + e = 4 * c + e by ring]
          exact (permuteRows_bitRev_next rs d l _ _ hri (by omega)).symm
        · show toE (ctx.scalars4 Binomial4.W (np + 4 * (jj + 1))) = chs.getD jj 0
          rw [hsc4]
          rfl
        · show toE (ctx.scalars4 Binomial4.W (np + 4 * 0)) = terminal
          rw [hsc4]
          rfl
      rw [(Prog.compileExt_run Binomial4.W np ext ctx st0).1, hst0]
      dsimp only
      have hV : V R = ((ext.map u).zip ((List.range (ext.map u).length).map fun k ↦
          Ext.pow alpha ((ext.map u).length - 1 - k))).foldl (fun y x ↦ y + x.1 * x.2) 0 := by
        rw [weighted_eq_horner, List.foldl_map]
      show _ = cj (V R) j
      rw [hV, List.length_map, List.range_eq_range', cj_foldl_zip u g j ext 0 0, cj_zero]
      refine foldl_add_congr _ _ _ (fun a ha ↦ ?_) 0
      obtain ⟨c, kk⟩ := a
      have hcm : c ∈ ext := List.fst_mem_of_mem_zipIdx ha
      have hkk : kk < K := List.snd_lt_of_mem_zipIdx ha
      dsimp only
      rw [cj_mul _ _ j hj, ← hu c hcm]
      have hw (e : Nat) (he : e < 4) : ctx.weight (4 * kk + e) j = cj (xPowMul e (g kk)) j := by
        show WT.getD (4 * (4 * kk + e) + j) 0 = _
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ (by omega)]
        have h1 : (4 * (4 * kk + e) + j) / 4 % 4 = e := by omega
        have h2 : (4 * (4 * kk + e) + j) / 16 = kk := by omega
        have h3 : (4 * (4 * kk + e) + j) % 4 = j := by omega
        simp only [h1, h2, h3]
        exact coeffs_getD _ j
      unfold Prog.extTerm
      rw [show 4 * kk = 4 * kk + 0 from rfl, hw 0 (by decide), hw 1 (by decide),
        hw 2 (by decide), hw 3 (by decide)]
      rfl
  refine congrArg Array.ofFn (funext fun r ↦ ?_)
  simp only [Q, bitRevPerm_getD_getD _ _ r.isLt]
  rfl

end Spec

end CompStark.Stark.Fast
