/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.LookupQuotient
public import CompStark.Stark.Fast.Lde

/-! # The fast permutation trace is the specification's

Inverses of planes follow `Ext4.inv` coordinate by coordinate, the norms inverted in one batch
with the zeros left zero (`invPlanes_rel`). So a block's fractions are the specification's
(`fractionsX_rel`), the rows written block by block are the permutation trace's rows with the
accumulator from the range's start (`writeBlock_rel`), and shifting it by the sums before the range
gives the permutation trace (`permutationWords_eq`, `permutationLdeWith_rel`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial
open CompPoly.CPolynomial.NTTFast.Packed (LdePlan)

open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-! ### Inverses -/

theorem val_eq_zero_iff (x : F) : x.val = 0 ↔ x = 0 :=
  ⟨fun h ↦ Subtype.ext h, fun h ↦ h ▸ rfl⟩

theorem read_tab {B : Nat} (hB : 4 * B < USize.size) (g : Nat → F) (k : Nat) (hk : k < B) :
    NTTFast.Packed.Native.read (encode (tab B g)) k = (g k).val := by
  rw [Words.read_encode _ _ (by rw [size_tab]; exact hB) (by rw [size_tab]; exact hk),
    getD_tab _ _ _ hk]

/-- Single words written in order give the tabulated values. -/
theorem foldl_write_tab {B : Nat} (f : Nat → F)
    (T : ByteArray → Nat → ByteArray)
    (hT : ∀ k < B, ∀ o : ByteArray, o = encode (Words.upto (tab B fun _ ↦ 0) f k) →
      T o k = encode (Words.upto (tab B fun _ ↦ 0) f (k + 1))) :
    (List.range' 0 B).foldl T (encode (tab B fun _ ↦ (0 : F))) = encode (tab B f) := by
  have h := Words.foldl_tail (tab B fun _ ↦ (0 : F)) f 0 B T fun k _ hk ↦ hT k (by omega) _ rfl
  rw [Words.upto_zero, Nat.zero_add, Words.upto_full _ _ _ (size_tab _ _)] at h
  exact h

theorem nonzeroWords_tab {B : Nat} (hB : 4 * B < USize.size) (g : Nat → F) :
    nonzeroWords (p := p) (encode (tab B g)) B =
      encode (tab B fun i ↦ if g i = 0 then 1 else g i) := by
  unfold nonzeroWords
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [zeroWords_tab (p := p)]
  refine foldl_write_tab _ _ fun k hk o ho ↦ ?_
  rw [ho, read_tab hB g k hk]
  have hw : (if (g k).val == 0 then (1 : F).val else (g k).val) =
      (if g k = 0 then (1 : F) else g k).val := by
    by_cases h0 : g k = 0
    · simp only [h0, ite_true]; rfl
    · have : ((g k).val == 0) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, val_eq_zero_iff]; exact h0
      simp only [this, h0, Bool.false_eq_true, ite_false]
  rw [hw]
  exact Words.write_upto _ _ k (by rw [size_tab]; exact hk) (by rw [size_tab]; exact hB)

theorem maskZeros_tab {B : Nat} (hB : 4 * B < USize.size) (g h : Nat → F) :
    maskZeros (encode (tab B g)) (encode (tab B h)) B =
      encode (tab B fun i ↦ if g i = 0 then 0 else h i) := by
  unfold maskZeros
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [zeroWords_tab (p := p)]
  refine foldl_write_tab _ _ fun k hk o ho ↦ ?_
  rw [ho, read_tab hB g k hk, read_tab hB h k hk]
  have hw : (if (g k).val == 0 then (0 : UInt32) else (h k).val) =
      (if g k = 0 then (0 : F) else h k).val := by
    by_cases h0 : g k = 0
    · simp only [h0, ite_true]; rfl
    · have : ((g k).val == 0) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, val_eq_zero_iff]; exact h0
      simp only [this, h0, Bool.false_eq_true, ite_false]
  rw [hw]
  exact Words.write_upto _ _ k (by rw [size_tab]; exact hk) (by rw [size_tab]; exact hB)

/-- The inverses of a block of words, zero for zero. -/
theorem invWords_tab {B : Nat} (hB : 4 * B < USize.size) (g : Nat → F) :
    invWords (p := p) (encode (tab B g)) B = encode (tab B fun i ↦ (g i)⁻¹) := by
  unfold invWords
  rw [nonzeroWords_tab hB g]
  have hinv := batchInvRange_encode (tab B fun i ↦ if g i = 0 then 1 else g i) 0 B
    (by rw [size_tab]; omega) (by rw [size_tab]; exact hB) fun k hk ↦ by
      rw [Nat.zero_add, getD_tab _ _ _ hk]
      split
      · exact one_ne_zero
      · assumption
  rw [hinv]
  have ht : (Array.ofFn (n := B) fun k ↦ ((tab B fun i ↦ if g i = 0 then 1 else g i).getD
      (0 + k.val) 0)⁻¹) = tab B fun i ↦ (if g i = 0 then 1 else g i)⁻¹ := by
    show tab B (fun k ↦ ((tab B fun i ↦ if g i = 0 then 1 else g i).getD (0 + k) 0)⁻¹) = _
    exact tab_congr fun i hi ↦ by rw [Nat.zero_add, getD_tab _ _ _ hi]
  rw [ht, maskZeros_tab hB]
  exact congrArg encode (tab_congr fun i _ ↦ by
    by_cases h0 : g i = 0
    · simp only [h0, ite_true, inv_zero]
    · simp only [h0, ite_false])

theorem scaleWords_tab {B : Nat} (hB : 4 * B < USize.size) (g : Nat → F) (c : F) :
    scaleWords (encode (tab B g)) c B = encode (tab B fun i ↦ g i * c) := by
  unfold scaleWords
  rw [zeroWords_tab (p := p), mulAddWords_tab hB]
  exact congrArg encode (tab_congr fun i _ ↦ zero_add _)

/-- **Inverses of planes**: `Ext4.inv` coordinate by coordinate, zero to zero. -/
theorem invPlanes_rel [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size) {v : EVec p}
    {f : Nat → EF} (hv : RV v (tab B f)) : RV (invPlanes v) (tab B fun i ↦ (f i)⁻¹) := by
  obtain ⟨hn, h0, h1, h2, h3⟩ := rv_tab_iff.mp hv
  unfold invPlanes
  simp only [hn, h0, h1, h2, h3, mulWords_tab hB, addWords_tab hB, subWords_tab hB,
    mulAddWords_tab hB, scaleWords_tab hB, invWords_tab hB]
  refine rv_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  · refine congrArg encode (tab_congr fun i _ ↦ ?_)
    first
      | show _ = (Ext4.inv (f i)).c0
      | show _ = (Ext4.inv (f i)).c1
      | show _ = (Ext4.inv (f i)).c2
      | show _ = (Ext4.inv (f i)).c3
    simp only [Ext4.inv, Ext4.g0, Ext4.g1, Ext4.norm, Binomial4.mulW_eq]
    ring

theorem ext4_add_zero (a : EF) : a + 0 = a := by
  show (⟨a.c0 + 0, a.c1 + 0, a.c2 + 0, a.c3 + 0⟩ : EF) = a
  simp only [add_zero]

theorem ext4_mul_ofBase_zero [Binomial4 p] (a : EF) : a * Ext4.ofBase 0 = 0 := by
  rw [EVec.mul_coords]
  simp only [ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3, MulZeroClass.mul_zero, add_zero]
  rfl

/-! ### Fractions -/

theorem length_fractionsX [Binomial4 p] {β E : Type} (B : Nat) (get : β → E → ByteArray)
    (v : β) (ts : List (List (List E × E))) (chs : List EF) (apl : Array (EVec p)) :
    (fractionsX B get v ts chs apl).length = ts.length := by
  rw [fractionsX, List.length_map, List.length_zipIdx]


section Fractions
variable [Mont32BaseField p] [Binomial4 p]

theorem combineX_fold {B : Nat} (hB : 4 * B < USize.size) (b : EF) :
    ∀ (ws : List ByteArray) (vs : List (Nat → F)),
      List.Forall₂ (fun w v ↦ w = encode (tab B v)) ws vs →
      ∀ (acc : XVal p) (f : Nat → EF), XRel B acc f →
      XRel B (ws.foldl (fun acc y ↦ (XVal.base y).add B (acc.mul B (.const b))) acc)
        (fun i ↦ (vs.map (· i)).foldl (fun acc y ↦ Ext.ofBase y + acc * b) (f i))
  | [], [], .nil, _, _, h => h
  | w :: ws, v :: vs, .cons hw hs, acc, f, h => by
    rw [List.foldl_cons]
    refine combineX_fold hB b ws vs hs _ _ (XRel.add hB (x := .base w) (f := fun i ↦
      Ext4.ofBase (v i)) ⟨v, hw, fun _ _ ↦ rfl⟩ (XRel.mul hB h (y := .const b)
        (g := fun _ ↦ b) fun _ _ ↦ rfl))

/-- `combineX` is `combine` on every row of the block. -/
theorem combineX_rel {B : Nat} (hB : 4 * B < USize.size) (b : EF) (ws : List ByteArray)
    (vs : List (Nat → F)) (h : List.Forall₂ (fun w v ↦ w = encode (tab B v)) ws vs) :
    XRel B (combineX B b ws) fun i ↦ Lookup.combine b (vs.map (· i)) := by
  cases h with
  | nil => exact fun _ _ ↦ rfl
  | cons hw hs =>
    exact combineX_fold hB b _ _ hs _ _ ⟨_, hw, fun _ _ ↦ rfl⟩

theorem fractionX_fold {E : Type} {B : Nat} (hB : 4 * B < USize.size) (ev : E → ByteArray)
    (val : E → Nat → F) (a b : EF) (apl : EVec p) (hapl : RV apl (tab B fun _ ↦ a)) :
    ∀ xs : List (List E × E),
      (∀ x ∈ xs, (∀ e ∈ x.1, ev e = encode (tab B (val e))) ∧
        ev x.2 = encode (tab B (val x.2))) →
      ∀ (z : EVec p) (S : Nat → EF), RV z (tab B S) →
      RV (xs.foldl (fun s (t, m) ↦
          let den := (XVal.ext apl).sub B (combineX B b (t.map ev))
          s.add ((invPlanes (den.planes B)).mulBase (ev m))) z)
        (tab B fun i ↦ xs.foldl (fun s (t, m) ↦
          let mv := val m i
          if mv = 0 then s
          else s + Challenge.smul mv (a - Lookup.combine b (t.map (val · i)))⁻¹) (S i))
  | [], _, z, S, hz => hz
  | (t, m) :: xs, hev, z, S, hz => by
    obtain ⟨ht, hm⟩ := hev (t, m) List.mem_cons_self
    simp only [List.foldl_cons]
    refine fractionX_fold hB ev val a b apl hapl xs
      (fun x hx ↦ hev x (List.mem_cons_of_mem _ hx)) _ _ ?_
    have hcomb := combineX_rel hB b (t.map ev) (t.map val)
      (by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact List.forall₂_same.mpr fun e he ↦ ht e he)
    have hden := XRel.sub hB (x := .ext apl) (f := fun _ ↦ a) hapl hcomb
    have hinv := invPlanes_rel hB (hden.planes hB)
    have hmb := EVec.mulBase_rel (tab B (val m)) hinv
      (by rw [size_tab, size_tab]) (by rw [size_tab]; exact hB)
    rw [← hm, tab_zipWith] at hmb
    have hadd := EVec.add_rel hz hmb (by rw [(rv_tab_iff.mp hz).1, (rv_tab_iff.mp hmb).1])
      (by rw [size_tab]; exact hB)
    rw [tab_zipWith] at hadd
    refine hadd.congr_tab fun i _ ↦ ?_
    by_cases h0 : val m i = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), h0]
      show S i + _ * Ext4.ofBase 0 = S i
      rw [ext4_mul_ofBase_zero, ext4_add_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      show _ = S i + Ext4.smul _ _
      rw [Norm.smul_eq_ofBase_mul, ext4_mul_comm (Ext4.ofBase _)]
      simp only [List.map_map]
      rfl

/-- The fraction of the tuples `t` with the values `val`, a tuple of multiplicity `0` adding
nothing (`Lookup.fraction`). -/
def fracOf {E : Type} (val : E → F) (a b : EF) (t : List (List E × E)) : EF :=
  t.foldl (fun s (tv, m) ↦
    let mv := val m
    if mv = 0 then s else s + Challenge.smul mv (a - Lookup.combine b (tv.map val))⁻¹) 0

/-- A lookup's fraction on a block of rows, `ev` its expressions' values there. -/
theorem fractionX_rel {E : Type} {B : Nat} (hB : 4 * B < USize.size) (ev : E → ByteArray)
    (val : E → Nat → F) (t : List (List E × E)) (a b : EF) (apl : EVec p)
    (hapl : RV apl (tab B fun _ ↦ a))
    (hev : ∀ x ∈ t, (∀ e ∈ x.1, ev e = encode (tab B (val e))) ∧
      ev x.2 = encode (tab B (val x.2))) :
    RV (t.foldl (fun s (t, m) ↦
        let den := (XVal.ext apl).sub B (combineX B b (t.map ev))
        s.add ((invPlanes (den.planes B)).mulBase (ev m))) (EVec.zeros B))
      (tab B fun i ↦ fracOf (val · i) a b t) := by
  have hz : RV (EVec.zeros (p := p) B) (tab B fun _ ↦ 0) := by
    have := EVec.zeros_rel (p := p) B
    rwa [show Array.replicate B (0 : EF) = tab B fun _ ↦ 0 from by
      apply Array.ext (by simp only [Array.size_replicate, size_tab])
      intro i h1 h2
      simp only [tab, Array.getElem_replicate, Array.getElem_ofFn]] at this
  exact fractionX_fold hB ev val a b apl hapl t hev _ _ hz

/-- Lookup `c`'s fraction planes on a block. -/
theorem fractionsX_getD {β E : Type} {B : Nat} (hB : 4 * B < USize.size)
    (get : β → E → ByteArray) (v : β)
    (val : E → Nat → F) (ts : List (List (List E × E))) (chs : List EF)
    (apl : Array (EVec p))
    (hapl : ∀ c < ts.length, RV (apl.getD c (EVec.zeros B)) (tab B fun _ ↦ chs.getD (2 * c) 0))
    (hev : ∀ t ∈ ts, ∀ x ∈ t, (∀ e ∈ x.1, get v e = encode (tab B (val e))) ∧
      get v x.2 = encode (tab B (val x.2))) (c : Nat) (hc : c < ts.length) :
    RV ((fractionsX B get v ts chs apl).toArray.getD c (EVec.zeros B))
      (tab B fun i ↦ fracOf (val · i) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) ts[c]) := by
  have hc' : c < (fractionsX B get v ts chs apl).length := by rw [length_fractionsX]; exact hc
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hc',
    Option.getD_some]
  simp only [fractionsX, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  exact fractionX_rel hB (get v) val ts[c] _ _ _ (hapl c hc) (hev _ (List.getElem_mem hc))

end Fractions

/-! ### Writing the rows -/

theorem write_upto' (O : Array F) (f : Nat → F) (k : Nat) (x : UInt32) (hx : x = (f k).val)
    (hk : k < O.size) (hs : 4 * O.size < USize.size) :
    NTTFast.Packed.Native.write (encode (Words.upto O f k)) k x =
      encode (Words.upto O f (k + 1)) := by
  rw [hx]; exact Words.write_upto O f k hk hs

/-- A row written at `o`: the accumulator's four coordinates, then four per lookup. -/
theorem writeRow_rel (O : Array F) (f : Nat → F) (o : Nat) (fs : Array (EVec p)) (acc : EF)
    (i : Nat) (hO : o + (fs.size + 1) * 4 ≤ O.size) (hs : 4 * O.size < USize.size)
    (hacc : f o = acc.c0 ∧ f (o + 1) = acc.c1 ∧ f (o + 2) = acc.c2 ∧ f (o + 3) = acc.c3)
    (hfs : ∀ c < fs.size,
      NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c0 i = (f (o + 4 * (c + 1))).val ∧
      NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c1 i =
        (f (o + 4 * (c + 1) + 1)).val ∧
      NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c2 i =
        (f (o + 4 * (c + 1) + 2)).val ∧
      NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c3 i =
        (f (o + 4 * (c + 1) + 3)).val) :
    writeRow (encode (Words.upto O f o)) o fs acc i =
      encode (Words.upto O f (o + (fs.size + 1) * 4)) := by
  unfold writeRow
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind]
  obtain ⟨a0, a1, a2, a3⟩ := hacc
  rw [write_upto' O f o _ (by rw [a0]) (by omega) hs,
    write_upto' O f (o + 1) _ (by rw [a1]) (by omega) hs,
    write_upto' O f (o + 1 + 1) _ (by rw [show o + 1 + 1 = o + 2 by omega, a2]) (by omega) hs,
    write_upto' O f (o + 1 + 1 + 1) _ (by rw [show o + 1 + 1 + 1 = o + 3 by omega, a3])
      (by omega) hs]
  suffices h : ∀ m ≤ fs.size, (List.range' 0 m).foldl (fun out c ↦
      NTTFast.Packed.Native.write (NTTFast.Packed.Native.write (NTTFast.Packed.Native.write
        (NTTFast.Packed.Native.write out (o + 4 * (c + 1))
          (NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c0 i))
        (o + 4 * (c + 1) + 1) (NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c1 i))
        (o + 4 * (c + 1) + 2) (NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c2 i))
        (o + 4 * (c + 1) + 3) (NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c3 i))
      (encode (Words.upto O f (o + 1 + 1 + 1 + 1))) = encode (Words.upto O f (o + 4 * (m + 1))) by
    rw [h fs.size le_rfl, Nat.mul_comm 4 (fs.size + 1)]
    rfl
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range'_concat, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      Nat.zero_add, Nat.one_mul]
    obtain ⟨b0, b1, b2, b3⟩ := hfs m (by omega)
    have hb : o + 4 * (m + 1 + 1) ≤ O.size := by
      have : o + 4 * (m + 1 + 1) ≤ o + (fs.size + 1) * 4 := by
        have : m + 1 ≤ fs.size := hm
        nlinarith
      omega
    rw [write_upto' O f _ _ b0 (by omega) hs,
      write_upto' O f _ _ (by rw [b1]) (by omega) hs,
      write_upto' O f _ _ (by rw [show o + 4 * (m + 1) + 1 + 1 = o + 4 * (m + 1) + 2 by omega, b2])
        (by omega) hs,
      write_upto' O f _ _ (by
        rw [show o + 4 * (m + 1) + 1 + 1 + 1 = o + 4 * (m + 1) + 3 by omega, b3]) (by omega) hs,
      show o + 4 * (m + 1) + 1 + 1 + 1 + 1 = o + 4 * (m + 1 + 1) by omega]

/-- The reads of a row: the fractions' coordinates at row `i` are `f`'s from word `o`. -/
def RowReads (f : Nat → F) (o : Nat) (fs : Array (EVec p)) (i : Nat) : Prop :=
  ∀ c < fs.size,
    NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c0 i = (f (o + 4 * (c + 1))).val ∧
    NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c1 i = (f (o + 4 * (c + 1) + 1)).val ∧
    NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c2 i = (f (o + 4 * (c + 1) + 2)).val ∧
    NTTFast.Packed.Native.read (fs.getD c (EVec.zeros 0)).c3 i = (f (o + 4 * (c + 1) + 3)).val

/-- A block written from row `r`, the accumulators `accs` row by row. -/
theorem writeBlock_rel (O : Array F) (f : Nat → F) (r : Nat) (fs : Array (EVec p)) (acc : EF)
    (B W : Nat) (accs : Nat → EF) (hW : W = (fs.size + 1) * 4) (hO : (r + B) * W ≤ O.size)
    (hs : 4 * O.size < USize.size) (hacc0 : accs 0 = acc)
    (hstep : ∀ i < B, accs (i + 1) = fs.foldl (fun a v ↦ a + v.get i) (accs i))
    (hacc : ∀ i < B, f ((r + i) * W) = (accs i).c0 ∧ f ((r + i) * W + 1) = (accs i).c1 ∧
      f ((r + i) * W + 2) = (accs i).c2 ∧ f ((r + i) * W + 3) = (accs i).c3)
    (hreads : ∀ i < B, RowReads f ((r + i) * W) fs i) :
    writeBlock (encode (Words.upto O f (r * W))) r fs acc B W =
      (encode (Words.upto O f ((r + B) * W)), accs B) := by
  unfold writeBlock
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind]
  suffices h : ∀ m ≤ B, (List.range' 0 m).foldl (fun st i ↦
      (writeRow st.1 ((r + i) * W) fs st.2 i, fs.foldl (fun a v ↦ a + v.get i) st.2))
      (encode (Words.upto O f (r * W)), acc) =
      (encode (Words.upto O f ((r + m) * W)), accs m) by
    rw [h B le_rfl]
    rfl
  intro m hm
  induction m with
  | zero => rw [hacc0]; rfl
  | succ m ih =>
    rw [List.range'_concat, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      Nat.zero_add, Nat.one_mul]
    dsimp only
    rw [writeRow_rel O f _ fs (accs m) m (by subst hW; nlinarith) hs (hacc m (by omega))
      (hreads m (by omega)), hstep m (by omega), hW]
    congr 3
    ring

/-! ### Shifting the accumulator -/

/-- Coordinate `e` of an extension element. -/
def coord4 (s : EF) : Nat → F
  | 0 => s.c0
  | 1 => s.c1
  | 2 => s.c2
  | _ => s.c3

/-- `O` with the accumulator columns of its first `i` rows of `W` words shifted by `s`. -/
def shiftedTo (O : Array F) (W : Nat) (s : EF) (i : Nat) : Array F :=
  Array.ofFn (n := O.size) fun k ↦
    if k.val < i * W ∧ k.val % W < 4 then O.getD k 0 + coord4 s (k.val % W) else O.getD k 0

theorem write_add (X : Array F) (k : Nat) (c : F) (hk : k < X.size)
    (hs : 4 * X.size < USize.size) :
    NTTFast.Packed.Native.write (encode X) k
        (NTTFast.Packed.add p (NTTFast.Packed.Native.read (encode X) k) c.val) =
      encode (X.setIfInBounds k (X.getD k 0 + c)) := by
  rw [Words.read_encode X k hs hk, NTTFast.Packed.add_val]
  exact NTTFast.Packed.Native.write_encode X k
    (by rw [CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]; omega) hk _

theorem size_shiftedTo (O : Array F) (W : Nat) (s : EF) (i : Nat) :
    (shiftedTo O W s i).size = O.size := Array.size_ofFn

theorem getD_shiftedTo (O : Array F) (W : Nat) (s : EF) (i k : Nat) (hk : k < O.size) :
    (shiftedTo O W s i).getD k 0 =
      if k < i * W ∧ k % W < 4 then O.getD k 0 + coord4 s (k % W) else O.getD k 0 := by
  rw [shiftedTo, NTTFast.Packed.getD_ofFn_bounded _ _ hk]

theorem ite_of_not {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  split
  · contradiction
  · rfl

theorem shiftRow_eq (X : Array F) (o : Nat) (s : EF) (ho : o + 4 ≤ X.size)
    (hs : 4 * X.size < USize.size) :
    shiftRow (encode X) o s = encode ((((X.setIfInBounds o (X.getD o 0 + s.c0)).setIfInBounds
      (o + 1) (X.getD (o + 1) 0 + s.c1)).setIfInBounds (o + 2)
        (X.getD (o + 2) 0 + s.c2)).setIfInBounds (o + 3) (X.getD (o + 3) 0 + s.c3)) := by
  unfold shiftRow
  dsimp only
  have hz (Y : Array F) (k : Nat) (x : F) : (Y.setIfInBounds k x).size = Y.size :=
    Array.size_setIfInBounds
  rw [write_add X o s.c0 (by omega) hs]
  rw [write_add _ (o + 1) s.c1 (by rw [hz]; omega) (by rw [hz]; exact hs),
    NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by omega), ite_of_not (by omega)]
  rw [write_add _ (o + 2) s.c2 (by rw [hz, hz]; omega) (by rw [hz, hz]; exact hs),
    NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by rw [hz]; omega), ite_of_not (by omega),
    NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by omega), ite_of_not (by omega)]
  rw [write_add _ (o + 3) s.c3 (by rw [hz, hz, hz]; omega) (by rw [hz, hz, hz]; exact hs),
    NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by rw [hz, hz]; omega), ite_of_not (by omega),
    NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by rw [hz]; omega), ite_of_not (by omega),
    NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by omega), ite_of_not (by omega)]

theorem mod_of_block (m W e : Nat) (he : e < W) : (m * W + e) % W = e := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

/-- Shifting the accumulator columns of `rows` rows. -/
theorem shiftAccumulator_eq (O : Array F) (rows W : Nat) (s : EF) (hW : 4 ≤ W)
    (hO : rows * W ≤ O.size) (hs : 4 * O.size < USize.size) :
    shiftAccumulator (encode O) rows W s = encode (shiftedTo O W s rows) := by
  unfold shiftAccumulator
  suffices h : ∀ m ≤ rows, (List.range m).foldl (fun out i ↦ shiftRow out (i * W) s)
      (encode O) = encode (shiftedTo O W s m) from h rows le_rfl
  intro m hm
  induction m with
  | zero =>
    rw [List.range_zero, List.foldl_nil]
    congr 1
    apply NTTFast.Packed.array_eq_of_getD _ _ 0 (by rw [size_shiftedTo])
    intro k
    by_cases hk : k < O.size
    · rw [getD_shiftedTo _ _ _ _ _ hk, Nat.zero_mul, ite_of_not (by omega)]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega),
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_shiftedTo]; omega)]
  | succ m ih =>
    have hmW : (m + 1) * W ≤ O.size := le_trans (Nat.mul_le_mul_right W hm) hO
    have hmw : m * W + 4 ≤ O.size := by rw [Nat.succ_mul] at hmW; omega
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      shiftRow_eq _ _ _ (by rw [size_shiftedTo]; exact hmw) (by rw [size_shiftedTo]; exact hs)]
    congr 1
    apply NTTFast.Packed.array_eq_of_getD _ _ 0 (by
      simp only [Array.size_setIfInBounds, size_shiftedTo])
    intro k
    have hz (Y : Array F) (j : Nat) (x : F) : (Y.setIfInBounds j x).size = Y.size :=
      Array.size_setIfInBounds
    rw [NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by
        simp only [Array.size_setIfInBounds, size_shiftedTo]; omega),
      NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by
        simp only [Array.size_setIfInBounds, size_shiftedTo]; omega),
      NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by
        simp only [Array.size_setIfInBounds, size_shiftedTo]; omega),
      NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by
        simp only [size_shiftedTo]; omega)]
    have hX (j : Nat) (hj : m * W ≤ j) (hjs : j < O.size) :
        (shiftedTo O W s m).getD j 0 = O.getD j 0 := by
      rw [getD_shiftedTo _ _ _ _ _ hjs, ite_of_not (by omega)]
    by_cases hk : k < O.size
    · rw [getD_shiftedTo O W s (m + 1) k hk]
      have hblk (e : Nat) (he : e < 4) : m * W + e < (m + 1) * W ∧ (m * W + e) % W < 4 :=
        ⟨by rw [Nat.succ_mul]; omega, by rw [mod_of_block m W e (by omega)]; exact he⟩
      by_cases h3 : k = m * W + 3
      · subst h3
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hX _ (by omega) hk,
          ite_eq_left_of_eq_true _ _ (eq_true (hblk 3 (by decide))), mod_of_block m W 3 (by omega)]
        rfl
      rw [ite_of_not h3]
      by_cases h2 : k = m * W + 2
      · subst h2
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hX _ (by omega) hk,
          ite_eq_left_of_eq_true _ _ (eq_true (hblk 2 (by decide))), mod_of_block m W 2 (by omega)]
        rfl
      rw [ite_of_not h2]
      by_cases h1 : k = m * W + 1
      · subst h1
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hX _ (by omega) hk,
          ite_eq_left_of_eq_true _ _ (eq_true (hblk 1 (by decide))), mod_of_block m W 1 (by omega)]
        rfl
      rw [ite_of_not h1]
      by_cases h0 : k = m * W
      · subst h0
        have h00 := hblk 0 (by decide)
        rw [Nat.add_zero] at h00
        have hm0 : m * W % W = 0 := Nat.mul_mod_left m W
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hX _ (by omega) hk,
          ite_eq_left_of_eq_true _ _ (eq_true h00), hm0]
        rfl
      rw [ite_of_not h0, getD_shiftedTo _ _ _ _ _ hk]
      by_cases hlt : k < m * W
      · have hlt' : k < (m + 1) * W := by rw [Nat.succ_mul]; omega
        simp only [hlt, hlt', true_and]
      · have hcond : ¬(k < (m + 1) * W ∧ k % W < 4) := by
          rintro ⟨hk1, hk2⟩
          have hq : k / W = m := Nat.div_eq_of_lt_le (by omega) hk1
          have := Nat.div_add_mod k W
          rw [hq] at this
          rw [Nat.mul_comm] at this
          omega
        rw [ite_of_not hcond, ite_of_not (by omega)]
    · rw [ite_of_not (by omega), ite_of_not (by omega), ite_of_not (by omega),
        ite_of_not (by omega)]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_shiftedTo]; omega),
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_shiftedTo]; omega)]

/-! ### The specification's permutation trace in closed form -/


/-- The accumulator before row `i`: every earlier row's fractions summed in order. -/
def specAcc (frs : Nat → List EF) (i : Nat) : EF :=
  (List.range i).foldl (fun acc r ↦ (frs r).foldl (· + ·) acc) 0

/-- Entry `k` of the permutation trace of `L` lookups with the rows' fractions `frs`. -/
def specEntry (frs : Nat → List EF) (L k : Nat) : EF :=
  if k % (L + 1) = 0 then specAcc frs (k / (L + 1))
  else (frs (k / (L + 1))).getD (k % (L + 1) - 1) 0

theorem permutationTrace_eq [Mont32BaseField p] [Binomial4 p] (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (chs : List EF) :
    Lookup.permutationTrace A ls logN t pis chs =
      (tab (2 ^ logN * (ls.length + 1))
        (specEntry (Lookup.rowFractions A ls logN t pis chs) ls.length),
        specAcc (Lookup.rowFractions A ls logN t pis chs) (2 ^ logN)) := by
  unfold Lookup.permutationTrace
  generalize hfrs : Lookup.rowFractions A ls logN t pis chs = frs
  have hlen : ∀ i, (frs i).length = ls.length := fun i ↦ by
    rw [← hfrs, Lookup.rowFractions, List.length_map, List.length_zipIdx]
  suffices h : ∀ m, (List.range m).foldl (fun (out, acc) i ↦
      ((out.push acc) ++ (frs i).toArray, (frs i).foldl (· + ·) acc)) (#[], 0) =
      (tab (m * (ls.length + 1)) (specEntry frs ls.length), specAcc frs m) from h _
  intro m
  induction m with
  | zero =>
    rw [List.range_zero, List.foldl_nil]
    refine Prod.ext ?_ rfl
    exact (Array.eq_empty_of_size_eq_zero (by rw [size_tab, Nat.zero_mul])).symm
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    dsimp only
    refine Prod.ext ?_ ?_
    · apply Array.ext (by
        simp only [Array.size_append, Array.size_push, size_tab, List.size_toArray, hlen]
        ring)
      intro k h1 h2
      rw [size_tab] at h2
      have hk' : k / (ls.length + 1) ≤ m := by
        apply Nat.lt_succ_iff.mp
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
      rw [getElem_tab]
      by_cases hlt : k < m * (ls.length + 1)
      · rw [Array.getElem_append_left (by rw [Array.size_push, size_tab]; omega),
          Array.getElem_push_lt (by rw [size_tab]; exact hlt), getElem_tab]
      · have hq : k / (ls.length + 1) = m := by
          apply Nat.le_antisymm hk'
          exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
        by_cases heq : k = m * (ls.length + 1)
        · subst heq
          rw [Array.getElem_append_left (by rw [Array.size_push, size_tab]; omega)]
          rw [Array.getElem_push, dite_eq_right_iff.mpr fun h ↦ absurd h (by rw [size_tab]; omega)]
          simp only [specEntry, Nat.mul_mod_left, ite_true,
            Nat.mul_div_cancel _ (Nat.succ_pos _)]
        · rw [Array.getElem_append_right (by rw [Array.size_push, size_tab]; omega)]
          simp only [List.getElem_toArray, Array.size_push, size_tab]
          have hr : k % (ls.length + 1) = k - m * (ls.length + 1) := by
            rw [Nat.mod_def, hq, Nat.mul_comm]
          have hr0 : k % (ls.length + 1) ≠ 0 := by omega
          have h2' : k < m * (ls.length + 1) + (ls.length + 1) := by
            rw [Nat.succ_mul] at h2; exact h2
          simp only [specEntry, hr0, ite_false, hq]
          rw [hr, List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
          simp only [Nat.sub_sub]
    · show (frs m).foldl (· + ·) (specAcc frs m) = specAcc frs (m + 1)
      rw [specAcc, specAcc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]


theorem tab_succ {α : Type} (N : Nat) (g : Nat → α) : tab (N + 1) g = (tab N g).push (g N) := by
  apply Array.ext (by rw [Array.size_push, size_tab, size_tab])
  intro k h1 h2
  rw [getElem_tab, Array.getElem_push]
  split
  · rw [getElem_tab]
  · rw [size_tab] at h1; rw [size_tab] at *; congr 1; omega

/-- A tabulated array of extension elements in base coordinates. -/
theorem flatten_tab [Mont32BaseField p] [Binomial4 p] (N : Nat) (g : Nat → EF) :
    Lookup.flatten (tab N g) = tab (N * 4) fun idx ↦ coord4 (g (idx / 4)) (idx % 4) := by
  induction N with
  | zero =>
    rw [Array.eq_empty_of_size_eq_zero (size_tab 0 g), Nat.zero_mul,
      Array.eq_empty_of_size_eq_zero (size_tab 0 _)]
    rfl
  | succ N ih =>
    rw [tab_succ, Lookup.flatten, Array.flatMap_push, ← Lookup.flatten, ih]
    apply Array.ext (by
      simp only [Array.size_append, size_tab, List.size_toArray, Mont32.coeffs_ext4,
        List.length_cons, List.length_nil]
      ring)
    intro k h1 h2
    have h2' : k < N * 4 + 4 := by rw [size_tab] at h2; omega
    rw [getElem_tab]
    by_cases hk : k < N * 4
    · rw [Array.getElem_append_left (by rw [size_tab]; exact hk), getElem_tab]
    · rw [Array.getElem_append_right (by rw [size_tab]; omega)]
      simp only [size_tab, Mont32.coeffs_ext4, List.getElem_toArray]
      have hq : k / 4 = N := by omega
      have hm : k % 4 = k - N * 4 := by omega
      rw [hq, hm]
      have : k - N * 4 = 0 ∨ k - N * 4 = 1 ∨ k - N * 4 = 2 ∨ k - N * 4 = 3 := by omega
      rcases this with h | h | h | h <;> simp only [h] <;> rfl


/-! ### A range of blocks -/

theorem get_tab {B : Nat} (hB : 4 * B < USize.size) {v : EVec p} {f : Nat → EF}
    (hv : RV v (tab B f)) (i : Nat) (hi : i < B) : v.get i = f i := by
  obtain ⟨-, h0, h1, h2, h3⟩ := rv_tab_iff.mp hv
  simp only [EVec.get, EVec.ofW, h0, h1, h2, h3, read_tab hB _ i hi,
    NTTFast.Packed.ofWord_val]

/-- The accumulator `i` rows into a range of rows from row `R0`, from `0`. -/
def localAcc (frs : Nat → List EF) (R0 i : Nat) : EF :=
  (List.range i).foldl (fun acc r ↦ (frs (R0 + r)).foldl (· + ·) acc) 0

/-- Word `j` of a range of rows from row `R0`, `W` words per row, with the accumulator from `0`. -/
def rangeVal (frs : Nat → List EF) (R0 W j : Nat) : F :=
  if j % W < 4 then coord4 (localAcc frs R0 (j / W)) (j % W)
  else coord4 ((frs (R0 + j / W)).getD (j % W / 4 - 1) 0) (j % W % 4)

theorem localAcc_succ (frs : Nat → List EF) (R0 i : Nat) :
    localAcc frs R0 (i + 1) = (frs (R0 + i)).foldl (· + ·) (localAcc frs R0 i) := by
  rw [localAcc, localAcc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem div_mod_row (W row e : Nat) (he : e < W) :
    (row * W + e) / W = row ∧ (row * W + e) % W = e :=
  ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he, Nat.zero_add],
    mod_of_block row W e he⟩

/-- **A range of blocks**: its rows of the permutation trace, the accumulator from `0`, and the
sum of their fractions. -/
theorem rangeRows_eq [Mont32BaseField p] [Binomial4 p] {β E : Type} (blk : Nat → β)
    (get : β → E → ByteArray)
    (ts : List (List (List E × E)))
    (chs : List EF) (B W b0 nb : Nat) (val : E → Nat → F) (frs : Nat → List EF)
    (hW : W = (ts.length + 1) * 4) (hB : 4 * B < USize.size)
    (hsz : 4 * (nb * B * W) < USize.size)
    (hfrs : ∀ r, frs r = ts.zipIdx.map fun (t, c) ↦
      fracOf (val · r) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) t)
    (hev : ∀ j < nb, ∀ t ∈ ts, ∀ x ∈ t,
      (∀ e ∈ x.1,
        get (blk ((b0 + j) * B)) e = encode (tab B fun i ↦ val e ((b0 + j) * B + i))) ∧
      get (blk ((b0 + j) * B)) x.2 = encode (tab B fun i ↦ val x.2 ((b0 + j) * B + i))) :
    rangeRows blk get ts chs B W b0 nb =
      (encode (tab (nb * B * W) (rangeVal frs (b0 * B) W)), localAcc frs (b0 * B) (nb * B)) := by
  unfold rangeRows
  dsimp only
  have hW4 : 4 ≤ W := by rw [hW]; omega
  have hapl : ∀ c < ts.length, RV
      (((Array.range ts.length).map fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B).getD c
        (EVec.zeros B)) (tab B fun _ ↦ chs.getD (2 * c) 0) := by
    intro c hc
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hc, ite_true, Option.map_some, Option.getD_some]
    exact XRel.planes hB (x := .const _) (fun _ _ ↦ rfl)
  generalize (Array.range ts.length).map (fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B) =
    apl at hapl
  let Z : Array F := tab (nb * B * W) fun _ ↦ 0
  have hZ : CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (nb * B * W) =
      encode (Words.upto Z (rangeVal frs (b0 * B) W) (0 * B * W)) := by
    rw [Nat.zero_mul, Nat.zero_mul, Words.upto_zero, zeroWords_tab (p := p)]
  have hZs : 4 * Z.size < USize.size := by rw [size_tab]; exact hsz
  rw [hZ]
  suffices h : ∀ m ≤ nb, (List.range m).foldl (fun st j ↦
      writeBlock st.1 (j * B) (fractionsX B get (blk ((b0 + j) * B)) ts chs apl).toArray st.2 B W)
      (encode (Words.upto Z (rangeVal frs (b0 * B) W) (0 * B * W)), 0) =
      (encode (Words.upto Z (rangeVal frs (b0 * B) W) (m * B * W)),
        localAcc frs (b0 * B) (m * B)) by
    rw [h nb le_rfl, Words.upto_full _ _ _ (size_tab _ _)]
    rfl
  intro m hm
  induction m with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.zero_mul]
    rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    dsimp only
    have hfs (c : Nat) (hc : c < ts.length) := fractionsX_getD hB get (blk ((b0 + m) * B))
      (fun e i ↦ val e ((b0 + m) * B + i)) ts chs apl hapl (hev m (by omega)) c hc
    have hsize : (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).toArray.size = ts.length := by
      rw [List.size_toArray, length_fractionsX]
    have hrow (i : Nat) (hi : i < B) : (frs ((b0 + m) * B + i)) =
        (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).map (·.get i) := by
      apply List.ext_getElem (by rw [List.length_map, length_fractionsX, hfrs, List.length_map,
        List.length_zipIdx])
      intro c h1 h2
      have hc : c < ts.length := by rwa [hfrs, List.length_map, List.length_zipIdx] at h1
      rw [List.getElem_map]
      have := hfs c hc
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some] at this
      rw [get_tab hB this i hi]
      simp only [hfrs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hx := writeBlock_rel Z (rangeVal frs (b0 * B) W) (m * B)
      (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).toArray (localAcc frs (b0 * B) (m * B)) B W
      (fun i ↦ localAcc frs (b0 * B) (m * B + i)) (by rw [hsize, hW])
      (by
        rw [size_tab]
        have := Nat.mul_le_mul_right (B * W) hm
        calc (m * B + B) * W = (m + 1) * (B * W) := by ring
          _ ≤ nb * (B * W) := this
          _ = nb * B * W := by ring)
      hZs rfl (fun i hi ↦ by
        rw [show m * B + (i + 1) = (m * B + i) + 1 by omega, localAcc_succ, List.foldl_toArray,
          show b0 * B + (m * B + i) = (b0 + m) * B + i by ring, hrow i hi, List.foldl_map])
      (fun i hi ↦ by
        obtain ⟨hq0, hr0⟩ := div_mod_row W (m * B + i) 0 (by omega)
        obtain ⟨hq1, hr1⟩ := div_mod_row W (m * B + i) 1 (by omega)
        obtain ⟨hq2, hr2⟩ := div_mod_row W (m * B + i) 2 (by omega)
        obtain ⟨hq3, hr3⟩ := div_mod_row W (m * B + i) 3 (by omega)
        rw [Nat.add_zero] at hq0 hr0
        simp only [rangeVal, hq0, hr0, hq1, hr1, hq2, hr2, hq3, hr3]
        exact ⟨rfl, rfl, rfl, rfl⟩) (fun i hi c hc ↦ by
        rw [hsize] at hc
        have := hfs c hc
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some] at this
        obtain ⟨-, h0, h1, h2, h3⟩ := rv_tab_iff.mp this
        have hfsc : (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).toArray.getD c (EVec.zeros 0) =
            (fractionsX B get (blk ((b0 + m) * B)) ts chs apl)[c]'(by
              rw [length_fractionsX]; exact hc) := by
          rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
            List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some]
        have hcW : 4 * (c + 1) + 3 < W := by rw [hW]; omega
        obtain ⟨hq0, hr0⟩ := div_mod_row W (m * B + i) (4 * (c + 1)) (by omega)
        obtain ⟨hq1, hr1⟩ := div_mod_row W (m * B + i) (4 * (c + 1) + 1) (by omega)
        obtain ⟨hq2, hr2⟩ := div_mod_row W (m * B + i) (4 * (c + 1) + 2) (by omega)
        obtain ⟨hq3, hr3⟩ := div_mod_row W (m * B + i) (4 * (c + 1) + 3) (by omega)
        rw [← Nat.add_assoc] at hq1 hr1 hq2 hr2 hq3 hr3
        have hfr : (frs (b0 * B + (m * B + i))).getD c 0 = fracOf
            (val · ((b0 + m) * B + i)) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) ts[c] := by
          rw [show b0 * B + (m * B + i) = (b0 + m) * B + i by ring, hfrs,
            List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_zipIdx]; exact hc)]
          simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
        have e0 : 4 * (c + 1) / 4 - 1 = c ∧ 4 * (c + 1) % 4 = 0 := by omega
        have e1 : (4 * (c + 1) + 1) / 4 - 1 = c ∧ (4 * (c + 1) + 1) % 4 = 1 := by omega
        have e2 : (4 * (c + 1) + 2) / 4 - 1 = c ∧ (4 * (c + 1) + 2) % 4 = 2 := by omega
        have e3 : (4 * (c + 1) + 3) / 4 - 1 = c ∧ (4 * (c + 1) + 3) % 4 = 3 := by omega
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
        · simp only [hfsc, rangeVal, h0, h1, h2, h3, hq0, hr0, hq1, hr1, hq2, hr2, hq3, hr3,
            read_tab hB _ i hi, e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
          rw [ite_of_not (by omega), hfr]
          rfl)
    rw [show (m + 1) * B * W = (m * B + B) * W by ring, show (m + 1) * B = m * B + B by ring,
      show m * B * W = m * B * W from rfl] at *
    rw [show m * B * W = (m * B) * W from rfl] at hx ⊢
    exact hx


/-! ### The whole permutation trace -/

theorem ext4_add_assoc (a b c : EF) : a + b + c = a + (b + c) := by
  apply Norm.ext <;> simp only [Norm.add_c0, Norm.add_c1, Norm.add_c2, Norm.add_c3, add_assoc]

theorem foldl_add_shift (s : EF) : ∀ (xs : List EF) (a : EF),
    xs.foldl (· + ·) (s + a) = s + xs.foldl (· + ·) a
  | [], _ => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, List.foldl_cons, ext4_add_assoc, foldl_add_shift s xs]

/-- The accumulator before row `R0 + i` is the one before row `R0` plus the range's. -/
theorem specAcc_add (frs : Nat → List EF) (R0 i : Nat) :
    specAcc frs (R0 + i) = specAcc frs R0 + localAcc frs R0 i := by
  unfold specAcc localAcc
  rw [List.range_add, List.foldl_append, List.foldl_map]
  generalize (List.range R0).foldl (fun acc r ↦ (frs r).foldl (· + ·) acc) 0 = s
  suffices h : ∀ (l : List Nat) (a : EF), l.foldl (fun acc r ↦ (frs (R0 + r)).foldl (· + ·) acc)
      (s + a) = s + l.foldl (fun acc r ↦ (frs (R0 + r)).foldl (· + ·) acc) a by
    rw [← h, ext4_add_zero]
  intro l
  induction l with
  | nil => intro a; rfl
  | cons r l ih => intro a; rw [List.foldl_cons, List.foldl_cons, foldl_add_shift, ih]

theorem coord4_add (a b : EF) (e : Nat) : coord4 (a + b) e = coord4 a e + coord4 b e := by
  match e with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The generation's shape of `2 ^ logN` rows: pieces of `2 ^ e` rows, blocks of `B` rows, and
tasks dividing the blocks. -/
theorem genShape (logN : Nat) : ∃ e, 2 ^ logN / (if 2 ^ logN < 4096 then 1 else 16) = 2 ^ e ∧
    (if 2 ^ logN < 4096 then 1 else 16) * 2 ^ e = 2 ^ logN ∧
    min (2 ^ e) 256 ∣ 2 ^ e ∧ 0 < min (2 ^ e) 256 ∧
    2 ^ logN / min (2 ^ e) 256 * min (2 ^ e) 256 = 2 ^ logN ∧
    (if 2 ^ logN / min (2 ^ e) 256 < 16 then 1 else 16) ∣ 2 ^ logN / min (2 ^ e) 256 := by
  have hpow : ∃ e, 2 ^ logN / (if 2 ^ logN < 4096 then 1 else 16) = 2 ^ e ∧
      (if 2 ^ logN < 4096 then 1 else 16) * 2 ^ e = 2 ^ logN := by
    split
    · exact ⟨logN, Nat.div_one _, Nat.one_mul _⟩
    · rename_i hge
      have h12 : 12 ≤ logN := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega : logN < 12))
          (le_refl _))
      have h16 : 2 ^ logN = 16 * 2 ^ (logN - 4) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]
        congr 1
        omega
      refine ⟨logN - 4, ?_, h16.symm⟩
      rw [h16, Nat.mul_div_cancel_left _ (by decide)]
  obtain ⟨e, h1, h2⟩ := hpow
  refine ⟨e, h1, h2, ?_⟩
  -- `B = 2 ^ b` for `b = min e 8`.
  have hB : min (2 ^ e) 256 = 2 ^ (min e 8) := by
    rcases Nat.le_total e 8 with h | h
    · rw [Nat.min_eq_left h, Nat.min_eq_left (le_trans (Nat.pow_le_pow_right (by decide) h)
        (le_refl (2 ^ 8)))]
    · rw [Nat.min_eq_right h, Nat.min_eq_right (le_trans (le_refl (2 ^ 8))
        (Nat.pow_le_pow_right (by decide) h))]
  rw [hB]
  have hle : min e 8 ≤ logN := by
    have : 2 ^ e ≤ 2 ^ logN := by rw [← h2]; exact Nat.le_mul_of_pos_left _ (by split <;> omega)
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp this
    omega
  have hdiv : 2 ^ logN / 2 ^ (min e 8) = 2 ^ (logN - min e 8) := Nat.pow_div hle (by decide)
  refine ⟨Nat.pow_dvd_pow 2 (Nat.min_le_left e 8), Nat.two_pow_pos _, ?_, ?_⟩
  · rw [hdiv, ← Nat.pow_add]; congr 1; omega
  · rw [hdiv]
    split
    · exact Nat.one_dvd _
    · rename_i hge
      have h4 : 4 ≤ logN - min e 8 := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega :
          logN - min e 8 < 4)) (le_refl _))
      exact (Nat.pow_dvd_pow 2 h4 : 2 ^ 4 ∣ _)

/-- Word `R0 W + j` of rows of `W = 4 (L + 1)` words: entry `(R0 + j / W, j % W / 4)` of the
trace, coordinate `j % W % 4`. -/
theorem idx_decomp (L R0 j : Nat) :
    (R0 * ((L + 1) * 4) + j) / 4 / (L + 1) = R0 + j / ((L + 1) * 4) ∧
    (R0 * ((L + 1) * 4) + j) / 4 % (L + 1) = j % ((L + 1) * 4) / 4 ∧
    (R0 * ((L + 1) * 4) + j) % 4 = j % ((L + 1) * 4) % 4 := by
  have hW : 0 < (L + 1) * 4 := by omega
  have hj := Nat.div_add_mod j ((L + 1) * 4)
  have hr := Nat.mod_lt j hW
  generalize j / ((L + 1) * 4) = q at hj
  generalize j % ((L + 1) * 4) = r at hj hr
  subst hj
  have e1 : R0 * ((L + 1) * 4) + ((L + 1) * 4 * q + r) = r + (R0 + q) * (L + 1) * 4 := by ring
  have hr4 : r / 4 < L + 1 := by omega
  rw [e1, Nat.add_mul_div_right _ _ (by decide), Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt hr4, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr4,
    Nat.add_mul_mod_self_right]
  exact ⟨rfl, rfl, rfl⟩

/-- Consecutive tabulated ranges of `S` values. -/
theorem foldl_tab_ranges {α : Type} (g : Nat → α) (S : Nat) : ∀ K : Nat,
    (List.range K).foldl (fun acc k ↦ acc ++ tab S fun j ↦ g (k * S + j)) #[] = tab (K * S) g
  | 0 => (Array.eq_empty_of_size_eq_zero (by rw [size_tab, Nat.zero_mul])).symm
  | K + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_tab_ranges g S K, List.foldl_cons,
      List.foldl_nil]
    have := CompStark.Stark.ofFn_append g (K * S) S
    rw [show K * S + S = (K + 1) * S by ring] at this
    exact this

/-- The words of the permutation trace with entries `specEntry frs L`. -/
abbrev specWord (frs : Nat → List EF) (L idx : Nat) : F :=
  coord4 (specEntry frs L (idx / 4)) (idx % 4)

/-- A range's rows shifted by the accumulator before it are the permutation trace's. -/
theorem shifted_rangeVal (frs : Nat → List EF) (L R0 rows : Nat) :
    shiftedTo (tab (rows * ((L + 1) * 4)) (rangeVal frs R0 ((L + 1) * 4))) ((L + 1) * 4)
        (specAcc frs R0) rows =
      tab (rows * ((L + 1) * 4)) fun j ↦ specWord frs L (R0 * ((L + 1) * 4) + j) := by
  apply NTTFast.Packed.array_eq_of_getD _ _ 0 (by rw [size_shiftedTo, size_tab, size_tab])
  intro j
  by_cases hj : j < rows * ((L + 1) * 4)
  · rw [getD_shiftedTo _ _ _ _ _ (by rw [size_tab]; exact hj), getD_tab _ _ _ hj,
      getD_tab _ _ _ hj]
    obtain ⟨h1, h2, h3⟩ := idx_decomp L R0 j
    simp only [specWord, specEntry, h1, h2, h3, rangeVal]
    by_cases hc : j % ((L + 1) * 4) < 4
    · have h0 : j % ((L + 1) * 4) / 4 = 0 := Nat.div_eq_of_lt hc
      have h4 : j % ((L + 1) * 4) % 4 = j % ((L + 1) * 4) := Nat.mod_eq_of_lt hc
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hj, hc⟩), ite_eq_left_of_eq_true _ _ (eq_true hc),
        ite_eq_left_of_eq_true _ _ (eq_true h0), h4, specAcc_add, coord4_add, add_comm]
    · have h0 : j % ((L + 1) * 4) / 4 ≠ 0 := by omega
      rw [ite_of_not (fun h ↦ hc h.2), ite_of_not hc, ite_of_not h0]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [size_shiftedTo, size_tab]; omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [size_tab]; omega)]

/-- **The parallel ranges of blocks** give the permutation trace's words and its terminal. -/
theorem assembleRanges_eq [Mont32BaseField p] [Binomial4 p] {β E : Type}
    (blk : Nat → β) (get : β → E → ByteArray) (ts : List (List (List E × E)))
    (chs : List EF) (B blocks : Nat) (val : E → Nat → F) (frs : Nat → List EF)
    (hB : 4 * B < USize.size) (hsz : 4 * (blocks * B * ((ts.length + 1) * 4)) < USize.size)
    (hdiv : (if blocks < 16 then 1 else 16) ∣ blocks)
    (hfrs : ∀ r, frs r = ts.zipIdx.map fun (t, c) ↦
      fracOf (val · r) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) t)
    (hev : ∀ j < blocks, ∀ t ∈ ts, ∀ x ∈ t,
      (∀ e ∈ x.1, get (blk (j * B)) e = encode (tab B fun i ↦ val e (j * B + i))) ∧
      get (blk (j * B)) x.2 = encode (tab B fun i ↦ val x.2 (j * B + i))) :
    assembleRanges blk get ts chs B ((ts.length + 1) * 4) blocks =
      (encode (tab (blocks * B * ((ts.length + 1) * 4)) (specWord frs ts.length)),
        specAcc frs (blocks * B)) := by
  unfold assembleRanges
  dsimp only
  have htpos : 0 < (if blocks < 16 then 1 else 16) := by split <;> omega
  generalize (if blocks < 16 then 1 else 16) = tasks at hdiv htpos ⊢
  generalize hW : (ts.length + 1) * 4 = W at hsz ⊢
  obtain ⟨size, rfl⟩ := hdiv
  have ht0 := htpos
  have hsize : tasks * size / tasks = size := Nat.mul_div_cancel_left size ht0
  rw [hsize]
  have hcount (k : Nat) (hk : k < tasks) :
      (if k + 1 = tasks then tasks * size - k * size else size) = size := by
    split
    · rename_i h; rw [← h, Nat.succ_mul]; omega
    · rfl
  -- Every range.
  have hrange (k : Nat) (hk : k < tasks) :
      rangeRows blk get ts chs B W (k * size) (if k + 1 = tasks then tasks * size - k * size else size)
        = (encode (tab (size * B * W) (rangeVal frs (k * size * B) W)),
          localAcc frs (k * size * B) (size * B)) := by
    rw [hcount k hk]
    refine rangeRows_eq blk get ts chs B W (k * size) size val frs hW.symm hB ?_ hfrs fun j hj ↦ ?_
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right W
        (Nat.mul_le_mul_right B (Nat.le_mul_of_pos_left size ht0)))) hsz
    · exact hev (k * size + j) (by nlinarith)
  -- The accumulators before the ranges, and the terminal.
  have hstarts : (Array.map (fun k ↦ Task.spawn fun _ ↦ rangeRows blk get ts chs B W (k * size)
      (if k + 1 = tasks then tasks * size - k * size else size)) (Array.range tasks)).foldl
      (fun (acc : Array EF × EF) t ↦ (acc.1.push acc.2, acc.2 + t.get.2)) (#[], 0) =
      (tab tasks fun k ↦ specAcc frs (k * size * B), specAcc frs (tasks * size * B)) := by
    rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
    suffices h : ∀ m ≤ tasks, (List.range m).foldl (fun (acc : Array EF × EF) k ↦
        (acc.1.push acc.2, acc.2 + (Task.spawn fun _ ↦ rangeRows blk get ts chs B W (k * size)
          (if k + 1 = tasks then tasks * size - k * size else size)).get.2)) (#[], 0) =
        (tab m fun k ↦ specAcc frs (k * size * B), specAcc frs (m * size * B)) from h tasks le_rfl
    intro m hm
    induction m with
    | zero =>
      rw [List.range_zero, List.foldl_nil, Array.eq_empty_of_size_eq_zero (size_tab 0 _),
        Nat.zero_mul, Nat.zero_mul]
      rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        get_spawn, hrange m (by omega), tab_succ, ← specAcc_add]
      congr 2
      ring
  rw [hstarts]
  refine Prod.ext ?_ rfl
  dsimp only
  rw [foldl_tasks tasks _ (fun k ↦ tab (size * B * W) fun j ↦
      specWord frs ts.length (k * (size * B * W) + j)) fun k hk ↦ ?_,
    foldl_tab_ranges (specWord frs ts.length) (size * B * W) tasks,
    show tasks * (size * B * W) = tasks * size * B * W by ring]
  have hget : ((Array.range tasks).map fun k ↦ Task.spawn fun _ ↦ rangeRows blk get ts chs B W
      (k * size) (if k + 1 = tasks then tasks * size - k * size else size)).getD k
      (Task.pure (ByteArray.empty, 0)) = Task.spawn fun _ ↦ rangeRows blk get ts chs B W (k * size)
        (if k + 1 = tasks then tasks * size - k * size else size) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hk, ite_true, Option.map_some, Option.getD_some]
  rw [hget, get_spawn, hrange k hk, getD_tab _ _ _ hk, hcount k hk]
  subst hW
  rw [shiftAccumulator_eq _ _ _ _ (by omega) (by rw [size_tab, Nat.mul_assoc])
    (by rw [size_tab]; exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right B (Nat.le_mul_of_pos_left size ht0)))) hsz),
    show size * B * ((ts.length + 1) * 4) = (size * B) * ((ts.length + 1) * 4) from rfl,
    shifted_rangeVal]
  refine congrArg encode (tab_congr fun j _ ↦ ?_)
  congr 1
  ring

/-! ### Lookups' tuples as indices -/

/-- A lookup's tuples' expressions in order: every tuple's elements, then its multiplicity. -/
abbrev flatL {α : Type} (l : List (List α × α)) : List α := l.flatMap fun (t, m) ↦ t ++ [m]

/-- A lookup's tuples as indices from `k` (`indexLookup`) name its expressions in order, through
`k + n` for its `n` expressions. -/
theorem indexLookup_spec {α β : Type} (f : Nat → β) (h : α → β) :
    ∀ (l : List (List α × α)) (k : Nat),
      (∀ j (hj : j < (flatL l).length), f (k + j) = h (flatL l)[j]) →
      (indexLookup l k).2 = k + (flatL l).length ∧
      (indexLookup l k).1.map (fun x ↦ (x.1.map f, f x.2)) = l.map (fun x ↦ (x.1.map h, h x.2)) ∧
      ∀ x ∈ (indexLookup l k).1, (∀ e ∈ x.1, k ≤ e ∧ e < k + (flatL l).length) ∧
        k ≤ x.2 ∧ x.2 < k + (flatL l).length
  | [], k, _ => ⟨rfl, rfl, fun x hx ↦ absurd hx List.not_mem_nil⟩
  | (t, m) :: l, k, hf => by
    have hfl : flatL ((t, m) :: l) = t ++ [m] ++ flatL l := by
      simp only [flatL, List.flatMap_cons]
    have hlen : (flatL ((t, m) :: l)).length = t.length + 1 + (flatL l).length := by
      rw [hfl, List.length_append, List.length_append, List.length_singleton]
    obtain ⟨ih1, ih2, ih3⟩ := indexLookup_spec f h l (k + t.length + 1) fun j hj ↦ by
      have := hf (t.length + 1 + j) (by rw [hlen]; omega)
      rw [show k + (t.length + 1 + j) = k + t.length + 1 + j by omega] at this
      rw [this]
      congr 1
      simp only [hfl]
      rw [List.getElem_append_right (by
        simp only [List.length_append, List.length_singleton]; omega)]
      congr 1
      simp only [List.length_append, List.length_singleton]
      omega
    simp only [indexLookup]
    refine ⟨by rw [ih1, hlen]; omega, ?_, ?_⟩
    · rw [List.map_cons, List.map_cons, ih2]
      congr 2
      · apply List.ext_getElem (by simp only [List.length_map, List.length_range'])
        intro j h1 h2
        rw [List.length_map, List.length_range'] at h1
        rw [List.getElem_map, List.getElem_map, List.getElem_range', Nat.one_mul,
          hf j (by rw [hlen]; omega)]
        congr 1
        simp only [hfl]
        rw [List.getElem_append_left (by
            simp only [List.length_append, List.length_singleton]; omega),
          List.getElem_append_left (by omega)]
      · have := hf t.length (by rw [hlen]; omega)
        rw [this]
        congr 1
        simp only [hfl]
        rw [List.getElem_append_left (by
            simp only [List.length_append, List.length_singleton]; omega),
          List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_singleton]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨fun e he ↦ ?_, by omega, by rw [hlen]; omega⟩
        rw [List.mem_range'_1] at he
        rw [hlen]; omega
      · obtain ⟨h1, h2, h3⟩ := ih3 x hx
        exact ⟨fun e he ↦ by have := h1 e he; rw [hlen]; omega, by omega, by rw [hlen]; omega⟩

/-- Lookups' tuples as indices from `k` (`indexTuples`) name their expressions in order. -/
theorem indexTuples_spec {α β : Type} (f : Nat → β) (h : α → β) :
    ∀ (ls : List (List (List α × α))) (k : Nat),
      (∀ j (hj : j < (flatTuples ls).length), f (k + j) = h (flatTuples ls)[j]) →
      (indexTuples ls k).map (·.map fun x ↦ (x.1.map f, f x.2)) =
        ls.map (·.map fun x ↦ (x.1.map h, h x.2)) ∧
      ∀ t ∈ indexTuples ls k, ∀ x ∈ t, (∀ e ∈ x.1, k ≤ e ∧ e < k + (flatTuples ls).length) ∧
        k ≤ x.2 ∧ x.2 < k + (flatTuples ls).length
  | [], k, _ => ⟨rfl, fun t ht ↦ absurd ht List.not_mem_nil⟩
  | l :: ls, k, hf => by
    have hft : flatTuples (l :: ls) = flatL l ++ flatTuples ls := by
      simp only [flatTuples, List.flatMap_cons]
    have hlen : (flatTuples (l :: ls)).length = (flatL l).length + (flatTuples ls).length := by
      rw [hft, List.length_append]
    obtain ⟨l1, l2, l3⟩ := indexLookup_spec f h l k fun j hj ↦ by
      rw [hf j (by rw [hlen]; omega)]
      congr 1
      simp only [hft]
      rw [List.getElem_append_left hj]
    obtain ⟨t2, t3⟩ := indexTuples_spec f h ls (indexLookup l k).2 fun j hj ↦ by
      rw [l1, Nat.add_assoc, hf _ (by rw [hlen]; omega)]
      congr 1
      simp only [hft]
      rw [List.getElem_append_right (by omega)]
      congr 1
      omega
    simp only [indexTuples]
    refine ⟨by rw [List.map_cons, List.map_cons, l2, t2], fun t ht x hx ↦ ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · obtain ⟨h1, h2, h3⟩ := l3 x hx
      exact ⟨fun e he ↦ by have := h1 e he; rw [hlen]; omega, h2, by rw [hlen]; omega⟩
    · obtain ⟨h1, h2, h3⟩ := t3 t ht x hx
      rw [l1] at h1 h2 h3
      exact ⟨fun e he ↦ by have := h1 e he; rw [hlen]; omega, by omega, by rw [hlen]; omega⟩

theorem length_indexTuples {α : Type} :
    ∀ (ls : List (List (List α × α))) (k : Nat), (indexTuples ls k).length = ls.length
  | [], _ => rfl
  | _ :: ls, _ => by simp only [indexTuples, List.length_cons, length_indexTuples ls]

/-- `fracOf` reads its tuples' values only. -/
theorem fracOf_map [Mont32BaseField p] [Binomial4 p] {E : Type} (val : E → F) (a b : EF)
    (t : List (List E × E)) : fracOf val a b t =
      fracOf id a b (t.map fun x ↦ (x.1.map val, val x.2)) := by
  simp only [fracOf, List.foldl_map, List.map_id]
  rfl

/-- The columns of an encoded row-major matrix, in one block. -/
theorem rowMajorCols_eq (M : Array F) (w n : Nat) (hn : 0 < n) (hM : M.size = n * w)
    (hs : 4 * M.size < USize.size) :
    rowMajorCols (encode M) w n = (⟨colBlocks ⟨w, n, M⟩ n, w, n⟩ : Prog.ColsF p).enc := by
  unfold rowMajorCols Prog.ColsF.enc
  dsimp only
  rw [transposeRows_encode M w 0 n (by rw [Nat.zero_add, hM]) hs]
  congr 1
  apply Array.ext (by rw [Array.size_map, Array.size_range, Array.size_map, size_colBlocks,
    Nat.div_self hn, Nat.one_mul])
  intro j h1 h2
  rw [Array.size_map, Array.size_range] at h1
  simp only [Array.getElem_map, Array.getElem_range, colBlocks, Array.getElem_ofFn]
  rw [extract_encode]
  congr 1
  apply Array.ext (by rw [Array.size_extract, Array.size_ofFn, Array.size_ofFn]
                      have := Nat.mul_le_mul_right n (show j + 1 ≤ w by omega)
                      rw [Nat.succ_mul] at this; omega)
  intro k k1 k2
  rw [Array.size_ofFn] at k2
  have hlt : j * n + k < w * n := by
    have := Nat.mul_le_mul_right n (show j + 1 ≤ w by omega)
    rw [Nat.succ_mul] at this; omega
  rw [Array.getElem_extract, Array.getElem_ofFn, Array.getElem_ofFn]
  dsimp only
  have e1 : (j * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k2]
  have e2 : (j * n + k) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt k2, Nat.zero_add]
  have e3 : j / w = 0 := Nat.div_eq_of_lt h1
  have e4 : j % w = j := Nat.mod_eq_of_lt h1
  simp only [e1, e2, e3, e4, Nat.zero_mul, Nat.zero_add]

/-- **The fast permutation trace is the specification's**, in base coordinates as packed words,
with its terminal. -/
theorem permutationWords_eq [Mont32BaseField p] [Binomial4 p] (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat)
    (trace : Array F) (pis : List F) (chs : List EF)
    (htr : trace.size = 2 ^ logN * A.width)
    (hpre : A.preprocessed.size = 2 ^ logN * A.preprocessedWidth) (hw : 0 < A.width)
    (hls : ∀ l ∈ ls, l.ColsBelow A.width A.preprocessedWidth)
    (hmem : Addressable (2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * 4))) :
    permutationWords A ls logN trace pis chs =
      (encode (permutationOf A ls logN trace pis chs).1,
        (permutationOf A ls logN trace pis chs).2) := by
  generalize hfrs : Lookup.rowFractions A ls logN trace pis chs = frs
  have hspec : permutationOf A ls logN trace pis chs =
      (tab (2 ^ logN * (ls.length + 1) * 4) fun idx ↦
        coord4 (specEntry frs ls.length (idx / 4)) (idx % 4), specAcc frs (2 ^ logN)) := by
    unfold permutationOf
    dsimp only
    rw [permutationTrace_eq, flatten_tab, hfrs]
  rw [hspec]
  unfold permutationWords
  dsimp only
  obtain ⟨e, hRe, -, -, hB0, hnB, htasks⟩ := genShape logN
  rw [← hRe] at hB0 hnB htasks
  set B := min (2 ^ logN / (if 2 ^ logN < 4096 then 1 else 16)) 256 with hBdef
  set blocks := 2 ^ logN / B with hbl
  have hBs : 4 * B < USize.size := blockSize_lt _
  have hsz : 4 * (blocks * B * ((ls.length + 1) * 4)) < USize.size := by
    rw [hnB]; unfold Addressable at hmem; nlinarith
  let tups := ls.map Stark.Lookup.tuples
  let flat := flatTuples tups
  let genRow := Lookup.generationRow A logN trace pis
  let val (k r : Nat) : F := (flat.getD k (.const 0)).eval (genRow r)
  have hlen : (indexTuples tups 0).length = ls.length := by
    rw [length_indexTuples, List.length_map]
  conv_lhs => rw [show ls.length = (indexTuples tups 0).length from hlen.symm]
  rw [assembleRanges_eq _ _ (indexTuples tups 0) chs B blocks val frs hBs (by rw [hlen]; exact hsz)
    htasks (fun r ↦ ?hfrs) ?hev, hnB, hlen]
  case hfrs =>
    rw [← hfrs]
    unfold Lookup.rowFractions
    obtain ⟨hmap, -⟩ := indexTuples_spec (fun k ↦ val k r) (fun e ↦ e.eval (genRow r)) tups 0
      fun j hj ↦ by
        show (flat.getD (0 + j) (.const 0)).eval _ = _
        rw [Nat.zero_add, List.getD_eq_getElem _ _ hj]
    have hl1 : (ls.zipIdx.map fun (l, c) ↦ Lookup.fraction (genRow r) (chs.getD (2 * c) 0)
        (chs.getD (2 * c + 1) 0) l).length = ls.length := by
      rw [List.length_map, List.length_zipIdx]
    apply List.ext_getElem (by rw [hl1, List.length_map, List.length_zipIdx, hlen])
    intro c h1 h2
    rw [hl1] at h1
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hc : c < (indexTuples tups 0).length := by rw [hlen]; exact h1
    have hm := List.getElem_of_eq hmap (by rw [List.length_map]; exact hc)
    rw [List.getElem_map, List.getElem_map] at hm
    rw [fracOf_map, hm]
    show fracOf (fun e ↦ e.eval (genRow r)) _ _ ls[c].tuples = _
    rw [fracOf_map]
    simp only [tups, List.getElem_map]
  case hev =>
    intro j hj t ht x hx
    have hjB : j * B + B ≤ 2 ^ logN := by
      have := Nat.mul_le_mul_right B (show j + 1 ≤ blocks from hj)
      rw [Nat.succ_mul, hnB] at this; exact this
    have hn : 4 * 2 ^ logN < USize.size := by
      unfold Addressable at hmem
      have : 2 ^ logN ≤ 2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * 4) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hus : 4 * trace.size < USize.size := by
      unfold Addressable at hmem; rw [htr]; nlinarith
    have husp : 4 * A.preprocessed.size < USize.size := by
      unfold Addressable at hmem; rw [hpre]; nlinarith
    -- The expressions read the columns below the widths.
    have hflat : ∀ ex ∈ flat, ex.colsBelow A.width A.width A.preprocessedWidth
        A.preprocessedWidth = true := by
      intro ex hex
      simp only [flat, tups, flatTuples, List.mem_flatMap, List.mem_map] at hex
      obtain ⟨_, ⟨l, hl, rfl⟩, y, hy, hey⟩ := hex
      rcases List.mem_append.mp hey with hey | hey
      · exact ((hls l hl) y hy).1 ex hey
      · rw [List.mem_singleton.mp hey]; exact ((hls l hl) y hy).2
    let n := 2 ^ logN
    let mt : Mat F := ⟨A.width, n, trace⟩
    let mp : Mat F := ⟨A.preprocessedWidth, n, A.preprocessed⟩
    let r0 := j * B
    let FS : Array F := Array.ofFn (n := n) fun i ↦ if (i.val == 0) = true then 1 else 0
    let LS : Array F := Array.ofFn (n := n) fun i ↦ if (i.val + 1 == n) = true then 1 else 0
    let TS : Array F := Array.ofFn (n := n) fun i ↦ if decide (i.val + 1 < n) = true then 1 else 0
    let L : Prog.LoadsF p := ⟨⟨colBlocks mt n, A.width, n⟩,
      ⟨colBlocks mp n, A.preprocessedWidth, n⟩, blockT mp r0 B, ⟨#[], 0, 1⟩, #[], r0,
      Array.ofFn (n := n) fun i ↦ (i.val + 1) % n,
      seqRows (Array.ofFn (n := n) fun i ↦ (i.val + 1) % n) r0 B, #[], FS, LS, TS⟩
    have hRn (m : Mat F) (hm : m.height = n) : RowsOk m n :=
      ⟨Nat.two_pow_pos _, by rw [hm, Nat.mod_self], hn⟩
    have hmt : (r0 + B) * A.width ≤ trace.size := by
      rw [htr]; exact Nat.mul_le_mul_right _ hjB
    have hmp : (r0 + B) * A.preprocessedWidth ≤ A.preprocessed.size := by
      rw [hpre]; exact Nat.mul_le_mul_right _ hjB
    have hnext (k : Nat) (hk : k < B) :
        (Array.ofFn (n := n) fun i ↦ (i.val + 1) % n).getD (r0 + k) 0 < n := by
      rw [NTTFast.Packed.getD_ofFn_bounded _ _ (by omega)]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hrow (m : Mat F) (hm : m.values.size = n * m.width) {r c : Nat} (hr : r < n)
        (hc : c < m.width) : r * m.width + c < m.values.size := by
      have := Nat.mul_le_mul_right m.width (show r + 1 ≤ n by omega)
      rw [Nat.succ_mul] at this; rw [hm]; omega
    have hcolB (m : Mat F) (c : Nat) (hc : c < m.width) : c * B + B ≤ (blockT m r0 B).size := by
      rw [size_blockT]
      have := Nat.mul_le_mul_right B (show c + 1 ≤ m.width by omega)
      rw [Nat.succ_mul] at this; omega
    have hpB : A.preprocessedWidth * B ≤ A.preprocessed.size := by
      refine le_trans ?_ hmp
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    have htB : A.width * B ≤ trace.size := by
      refine le_trans ?_ hmt
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    have hL : L.Addr := ⟨colsF_addr (hRn mt rfl), colsF_addr (hRn mp rfl), by
        show 4 * (blockT mp r0 B).size < USize.size
        rw [size_blockT]
        show 4 * (A.preprocessedWidth * B) < USize.size
        omega,
      fun a ha ↦ absurd ha (Array.not_mem_empty a), by show 4 * 0 < USize.size; omega,
      fun c hc ↦ absurd hc (Array.not_mem_empty c),
      by show 4 * FS.size < USize.size; rw [Array.size_ofFn]; exact hn,
      by show 4 * LS.size < USize.size; rw [Array.size_ofFn]; exact hn,
      by show 4 * TS.size < USize.size; rw [Array.size_ofFn]; exact hn⟩
    have hVs : 4 * (blockT mt r0 B).size < USize.size := by
      rw [size_blockT]
      show 4 * (A.width * B) < USize.size
      omega
    let prog := Prog.compileOuts flat
    have hlo := Prog.compileOuts_leafOk flat A.width A.width A.preprocessedWidth
      A.preprocessedWidth 0 hflat
    have hcq (c : Nat) (hc : c < A.width) : 0 + c * B + B ≤ (blockT mt r0 B).size := by
      rw [Nat.zero_add]; exact hcolB mt c hc
    have hlq : ∀ src, Prog.Src.Below A.width A.preprocessedWidth A.preprocessedWidth 0 src →
        L.InRange B src := by
      intro src hsrc
      cases src with
      | next c => exact ⟨fun k hk ↦ colsF_has (hRn mt rfl) _ c (hnext k hk) hsrc, seqRows_spec⟩
      | prepCur c => exact hcolB mp c hsrc
      | prepNext c =>
        exact ⟨fun k hk ↦ colsF_has (hRn mp rfl) _ c (hnext k hk) hsrc, seqRows_spec⟩
      | permCur c => exact absurd hsrc (Nat.not_lt_zero c)
      | permNext c => exact absurd hsrc (Nat.not_lt_zero c)
      | periodic j => exact fun h ↦ absurd h (Nat.not_lt_zero j)
      | isFirstRow => show r0 + B ≤ FS.size; rw [Array.size_ofFn]; exact hjB
      | isLastRow => show r0 + B ≤ LS.size; rw [Array.size_ofFn]; exact hjB
      | isTransition => show r0 + B ≤ TS.size; rw [Array.size_ofFn]; exact hjB
    have hcode : ∀ ins ∈ prog.code, ins.InRange (blockT mt r0 B) 0 B L B prog.regs :=
      fun ins hins ↦ Prog.Instr.inRange_of (cq := (· < A.width))
        (lq := Prog.Src.Below A.width A.preprocessedWidth A.preprocessedWidth 0) hcq hlq ins
        ((Prog.compileOuts_run flat ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ _ ↦ 0⟩
          ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2.2 ins hins) (hlo.1 ins hins)
    obtain ⟨hosz, -, -⟩ := Prog.compileOuts_run flat ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0,
      fun _ _ ↦ 0⟩ ⟨fun _ ↦ 0, fun _ ↦ 0⟩
    have hout : ∀ o ∈ prog.outs, o.InRange (blockT mt r0 B) 0 B B prog.regs := by
      intro o ho
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp ho
      have hg : prog.outs[k] = prog.outs.getD k (.reg 0) := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
      have hreg := ((Prog.compileOuts_run flat ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ _ ↦ 0⟩
        ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2.1 k (by rw [← hosz]; exact hk)).2
      have hleaf := hlo.2 _ ho
      rw [← hg] at hreg
      generalize prog.outs[k] = o at hreg hleaf ⊢
      cases o with
      | reg r => exact hreg
      | cur c => exact hcq c hleaf
      | const x => trivial
    have key : ∀ (vb : ByteArray) (Lc : Prog.Loads) (h0 : (NTTFast.Packed.Native.zeroWords
        B).size = 4 * B), vb = encode (blockT mt r0 B) → Lc = L.enc → ∀ k < flat.length,
        (Prog.outWords p prog.outs ⟨vb, 0, B⟩
          (Prog.runBlock p prog.code ⟨vb, 0, B⟩ Lc pis.toArray #[] B hBs
            (Array.replicate (4 + prog.regs) ⟨NTTFast.Packed.Native.zeroWords B, h0⟩)) B).getD k
          ByteArray.empty = encode (tab B fun i ↦ val k (r0 + i)) := by
      intro vb Lc h0 hvb hLc k hk
      subst hvb hLc
      have hrel := Prog.runBlock_rel prog.code (blockT mt r0 B) 0 B L pis.toArray #[] B prog.regs
        (4 * B) hBs _ _ (Prog.blockRel_zeros B prog.regs h0) (by exact hVs) hL hcode
      rw [Prog.outWords_rel prog.outs (blockT mt r0 B) 0 B L pis.toArray #[] _ _ hrel hBs hout,
        Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem (by rw [hosz]; exact hk), Option.map_some, Option.getD_some]
      refine congrArg encode (tab_congr fun i hi ↦ ?_)
      have hg : prog.outs[k]'(by rw [hosz]; exact hk) = prog.outs.getD k (.reg 0) := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem, Option.getD_some]
      rw [hg, ((Prog.compileOuts_run flat (Prog.blockCtx (blockT mt r0 B) 0 B L pis.toArray #[]
        B i) ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2.1 k hk).1]
      show _ = (flat.getD k (.const 0)).eval (genRow (r0 + i))
      rw [List.getD_eq_getElem _ _ hk]
      have hri : r0 + i < n := by omega
      refine Expr.eval_hom (R := F) (S := F) id (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        A.width A.width A.preprocessedWidth A.preprocessedWidth
        (Prog.blockCtx (blockT mt r0 B) 0 B L pis.toArray #[] B i).env (genRow (r0 + i))
        (fun c hc ↦ ?_)
        (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun jj ↦ ?_) (fun jj ↦ ?_)
        (fun _ ↦ rfl) ?_ ?_ ?_ _ (hflat _ (List.getElem_mem hk))
      · show (blockT mt r0 B).getD (0 + c * B + i) 0 = trace.getD ((r0 + i) * A.width + c) 0
        rw [Nat.zero_add]
        exact blockT_getD mt r0 B c i hc hi
      · show (⟨colBlocks mt n, A.width, n⟩ : Prog.ColsF p).at
          ((Array.ofFn (n := n) fun i ↦ (i.val + 1) % n).getD (r0 + i) 0) c =
          trace.getD ((r0 + i + 1) % 2 ^ logN * A.width + c) 0
        rw [colsF_at (hRn mt rfl) _ c (hnext i hi) hc, NTTFast.Packed.getD_ofFn_bounded _ _ hri]
      · show (blockT mp r0 B).getD (c * B + i) 0 =
          A.preprocessed.getD ((r0 + i) * A.preprocessedWidth + c) 0
        exact blockT_getD mp r0 B c i hc hi
      · show (⟨colBlocks mp n, A.preprocessedWidth, n⟩ : Prog.ColsF p).at
          ((Array.ofFn (n := n) fun i ↦ (i.val + 1) % n).getD (r0 + i) 0) c =
          A.preprocessed.getD ((r0 + i + 1) % 2 ^ logN * A.preprocessedWidth + c) 0
        rw [colsF_at (hRn mp rfl) _ c (hnext i hi) hc, NTTFast.Packed.getD_ofFn_bounded _ _ hri]
      · show ((#[] : Array (Array F)).getD jj #[]).getD (r0 + i) 0 = 0
        simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_nil,
          Option.getD_none]
      · show pis.toArray.getD jj 0 = pis.getD jj 0
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
      · show FS.getD (r0 + i) 0 = if r0 + i = 0 then 1 else 0
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ hri]
        simp only [beq_iff_eq]
      · show LS.getD (r0 + i) 0 = if r0 + i + 1 = 2 ^ logN then 1 else 0
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ hri]
        simp only [beq_iff_eq, n]
      · show TS.getD (r0 + i) 0 = if r0 + i + 1 < 2 ^ logN then 1 else 0
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ hri]
        simp only [decide_eq_true_eq, n]
    obtain ⟨-, hidx⟩ := indexTuples_spec (fun k ↦ flat.getD k (.const 0)) id tups 0
      fun jj hj' ↦ by rw [Nat.zero_add, List.getD_eq_getElem _ _ hj']; rfl
    obtain ⟨h1, -, h2⟩ := hidx t ht x hx
    have hvb : NTTFast.Packed.Native.transposeRows (NTTFast.Packed.Native.encodeFields trace)
        A.width 0 A.width r0 B = encode (blockT mt r0 B) := by
      rw [NTTFast.Packed.Native.encodeFields_eq]
      exact transposeRows_encode trace A.width r0 B hmt hus
    have hLc : (⟨rowMajorCols (NTTFast.Packed.Native.encodeFields trace) A.width n,
        rowMajorCols (NTTFast.Packed.Native.encodeFields A.preprocessed) A.preprocessedWidth n,
        NTTFast.Packed.Native.transposeRows (NTTFast.Packed.Native.encodeFields A.preprocessed)
          A.preprocessedWidth 0 A.preprocessedWidth r0 B, PMat.empty.toCols, ByteArray.empty, r0,
        Array.ofFn (n := n) fun i ↦ (i.val + 1) % n,
        seqRows (Array.ofFn (n := n) fun i ↦ (i.val + 1) % n) r0 B, #[],
        NTTFast.Packed.Native.encodeFields FS, NTTFast.Packed.Native.encodeFields LS,
        NTTFast.Packed.Native.encodeFields TS⟩ : Prog.Loads) = L.enc := by
      rw [NTTFast.Packed.Native.encodeFields_eq, NTTFast.Packed.Native.encodeFields_eq,
        transposeRows_encode A.preprocessed A.preprocessedWidth r0 B hmp husp,
        NTTFast.Packed.Native.encodeFields_eq, NTTFast.Packed.Native.encodeFields_eq,
        NTTFast.Packed.Native.encodeFields_eq,
        rowMajorCols_eq trace A.width n (Nat.two_pow_pos _) (by rw [htr]) hus,
        rowMajorCols_eq A.preprocessed A.preprocessedWidth n (Nat.two_pow_pos _) (by rw [hpre])
          husp]
      simp only [L, Prog.LoadsF.enc, mp, mt, blockT, CompPoly.PackedRepr.encode_empty,
        PMat.empty, PMat.toCols, List.map_toArray, List.map_nil, Prog.ColsF.enc]
    exact ⟨fun e he ↦ key _ _ _ hvb hLc e (by
        have := (h1 e he).2; simpa only [Nat.zero_add] using this),
      key _ _ _ hvb hLc x.2 (by simpa only [Nat.zero_add] using h2)⟩
  rw [show 2 ^ logN * (ls.length + 1) * 4 = 2 ^ logN * ((ls.length + 1) * 4) by ring]

/-- **The fast extension of the permutation trace is the specification's**, and so is its
terminal. -/
theorem permutationLdeWith_rel [Mont32BaseField p] [Binomial4 p]
    (plans : List (Nat × Nat × F × LdePlan p))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2) (bits : Nat) (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (t : Array F) (pis : List F) (chs : List EF)
    (hok : PermutationOk EF A ls logN bits t) :
    RM (permutationLdeWith plans bits A ls logN t pis chs).1
        (permutationLdeOf bits A ls logN t pis chs).1 ∧
      (permutationLdeWith plans bits A ls logN t pis chs).2 =
        (permutationLdeOf bits A ls logN t pis chs).2 := by
  have hmem : Addressable (2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * 4)) := by
    have := hok.mem
    unfold Addressable at this ⊢
    rw [Mont32.d_ext4] at this
    have : 2 ^ logN ≤ 2 ^ (logN + bits) := Nat.pow_le_pow_right (by decide) (by omega)
    nlinarith
  have hw := permutationWords_eq A ls logN t pis chs hok.trace hok.preprocessed hok.width
    hok.lookups hmem
  have hsize : (permutationOf A ls logN t pis chs).1.size =
      2 ^ logN * ((ls.length + 1) * 4) := by
    unfold permutationOf
    dsimp only
    rw [permutationTrace_eq, flatten_tab, size_tab]
    ring
  unfold permutationLdeWith permutationLdeOf
  rw [hw]
  dsimp only
  refine ⟨ldeWordsWith_one_rel plans hplans logN bits gen _ _ hsize hok.twoAdic ?_, rfl⟩
  have := hok.mem
  unfold Addressable at this ⊢
  rw [Mont32.d_ext4] at this
  have := Nat.mul_le_mul_left (2 ^ (logN + bits))
    (Nat.le_add_left ((ls.length + 1) * 4) (A.width + A.preprocessedWidth))
  omega


end CompStark.Stark.Fast
