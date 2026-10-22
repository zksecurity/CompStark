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
open CompPoly.CPolynomial.NTTFast.Packed (LdePlan PackedCosetLde)

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

theorem length_fractionsX [Binomial4 p] (B : Nat) (ev : Expr F → ByteArray)
    (ls : List (Stark.Lookup F))
    (chs : List EF) (apl : Array (EVec p)) : (fractionsX B ev ls chs apl).length = ls.length := by
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

theorem fractionX_fold {B : Nat} (hB : 4 * B < USize.size) (ev : Expr F → ByteArray)
    (env : Nat → Expr.Env F F) (a b : EF) (apl : EVec p) (hapl : RV apl (tab B fun _ ↦ a)) :
    ∀ xs : List (List (Expr F) × Expr F),
      (∀ x ∈ xs, (∀ e ∈ x.1, ev e = encode (tab B fun i ↦ e.eval (env i))) ∧
        ev x.2 = encode (tab B fun i ↦ x.2.eval (env i))) →
      ∀ (z : EVec p) (S : Nat → EF), RV z (tab B S) →
      RV (xs.foldl (fun s (t, m) ↦
          let den := (XVal.ext apl).sub B (combineX B b (t.map ev))
          s.add ((invPlanes (den.planes B)).mulBase (ev m))) z)
        (tab B fun i ↦ xs.foldl (fun s (t, m) ↦
          let mv := m.eval (env i)
          if mv = 0 then s
          else s + Challenge.smul mv (a - Lookup.combine b (t.map (·.eval (env i))))⁻¹) (S i))
  | [], _, z, S, hz => hz
  | (t, m) :: xs, hev, z, S, hz => by
    obtain ⟨ht, hm⟩ := hev (t, m) List.mem_cons_self
    simp only [List.foldl_cons]
    refine fractionX_fold hB ev env a b apl hapl xs
      (fun x hx ↦ hev x (List.mem_cons_of_mem _ hx)) _ _ ?_
    have hcomb := combineX_rel hB b (t.map ev) (t.map fun e i ↦ e.eval (env i))
      (by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact List.forall₂_same.mpr fun e he ↦ ht e he)
    have hden := XRel.sub hB (x := .ext apl) (f := fun _ ↦ a) hapl hcomb
    have hinv := invPlanes_rel hB (hden.planes hB)
    have hmb := EVec.mulBase_rel (tab B fun i ↦ m.eval (env i)) hinv
      (by rw [size_tab, size_tab]) (by rw [size_tab]; exact hB)
    rw [← hm, tab_zipWith] at hmb
    have hadd := EVec.add_rel hz hmb (by rw [(rv_tab_iff.mp hz).1, (rv_tab_iff.mp hmb).1])
      (by rw [size_tab]; exact hB)
    rw [tab_zipWith] at hadd
    refine hadd.congr_tab fun i _ ↦ ?_
    by_cases h0 : m.eval (env i) = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), h0]
      show S i + _ * Ext4.ofBase 0 = S i
      rw [ext4_mul_ofBase_zero, ext4_add_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      show _ = S i + Ext4.smul _ _
      rw [Norm.smul_eq_ofBase_mul, ext4_mul_comm (Ext4.ofBase _)]
      simp only [List.map_map]
      rfl

/-- A lookup's fraction on a block of rows, `ev` its expressions' values there. -/
theorem fractionX_rel {B : Nat} (hB : 4 * B < USize.size) (ev : Expr F → ByteArray)
    (env : Nat → Expr.Env F F) (l : Stark.Lookup F) (a b : EF) (apl : EVec p)
    (hapl : RV apl (tab B fun _ ↦ a))
    (hev : ∀ x ∈ l.tuples, (∀ e ∈ x.1, ev e = encode (tab B fun i ↦ e.eval (env i))) ∧
      ev x.2 = encode (tab B fun i ↦ x.2.eval (env i))) :
    RV (l.tuples.foldl (fun s (t, m) ↦
        let den := (XVal.ext apl).sub B (combineX B b (t.map ev))
        s.add ((invPlanes (den.planes B)).mulBase (ev m))) (EVec.zeros B))
      (tab B fun i ↦ Lookup.fraction (env i) a b l) := by
  have hz : RV (EVec.zeros (p := p) B) (tab B fun _ ↦ 0) := by
    have := EVec.zeros_rel (p := p) B
    rwa [show Array.replicate B (0 : EF) = tab B fun _ ↦ 0 from by
      apply Array.ext (by simp only [Array.size_replicate, size_tab])
      intro i h1 h2
      simp only [tab, Array.getElem_replicate, Array.getElem_ofFn]] at this
  exact fractionX_fold hB ev env a b apl hapl l.tuples hev _ _ hz

/-- Lookup `c`'s fraction planes on a block. -/
theorem fractionsX_getD {B : Nat} (hB : 4 * B < USize.size) (ev : Expr F → ByteArray)
    (env : Nat → Expr.Env F F) (ls : List (Stark.Lookup F)) (chs : List EF)
    (apl : Array (EVec p))
    (hapl : ∀ c < ls.length, RV (apl.getD c (EVec.zeros B)) (tab B fun _ ↦ chs.getD (2 * c) 0))
    (hev : ∀ l ∈ ls, ∀ x ∈ l.tuples, (∀ e ∈ x.1, ev e = encode (tab B fun i ↦ e.eval (env i))) ∧
      ev x.2 = encode (tab B fun i ↦ x.2.eval (env i))) (c : Nat) (hc : c < ls.length) :
    RV ((fractionsX B ev ls chs apl).toArray.getD c (EVec.zeros B))
      (tab B fun i ↦ Lookup.fraction (env i) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0)
        ls[c]) := by
  have hc' : c < (fractionsX B ev ls chs apl).length := by rw [length_fractionsX]; exact hc
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hc',
    Option.getD_some]
  simp only [fractionsX, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  exact fractionX_rel hB ev env ls[c] _ _ _ (hapl c hc) (hev _ (List.getElem_mem hc))

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
theorem rangeRows_eq [Mont32BaseField p] [Binomial4 p] (ev : Nat → Expr F → ByteArray)
    (ls : List (Stark.Lookup F))
    (chs : List EF) (B W b0 nb : Nat) (env : Nat → Expr.Env F F) (frs : Nat → List EF)
    (hW : W = (ls.length + 1) * 4) (hB : 4 * B < USize.size)
    (hsz : 4 * (nb * B * W) < USize.size)
    (hfrs : ∀ r, frs r = ls.zipIdx.map fun (l, c) ↦
      Lookup.fraction (env r) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) l)
    (hev : ∀ j < nb, ∀ l ∈ ls, ∀ x ∈ l.tuples,
      (∀ e ∈ x.1, ev ((b0 + j) * B) e = encode (tab B fun i ↦ e.eval (env ((b0 + j) * B + i)))) ∧
      ev ((b0 + j) * B) x.2 = encode (tab B fun i ↦ x.2.eval (env ((b0 + j) * B + i)))) :
    rangeRows ev ls chs B W b0 nb =
      (encode (tab (nb * B * W) (rangeVal frs (b0 * B) W)), localAcc frs (b0 * B) (nb * B)) := by
  unfold rangeRows
  dsimp only
  have hW4 : 4 ≤ W := by rw [hW]; omega
  have hapl : ∀ c < ls.length, RV
      (((Array.range ls.length).map fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B).getD c
        (EVec.zeros B)) (tab B fun _ ↦ chs.getD (2 * c) 0) := by
    intro c hc
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hc, ite_true, Option.map_some, Option.getD_some]
    exact XRel.planes hB (x := .const _) (fun _ _ ↦ rfl)
  generalize (Array.range ls.length).map (fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B) =
    apl at hapl
  let Z : Array F := tab (nb * B * W) fun _ ↦ 0
  have hZ : CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (nb * B * W) =
      encode (Words.upto Z (rangeVal frs (b0 * B) W) (0 * B * W)) := by
    rw [Nat.zero_mul, Nat.zero_mul, Words.upto_zero, zeroWords_tab (p := p)]
  have hZs : 4 * Z.size < USize.size := by rw [size_tab]; exact hsz
  rw [hZ]
  suffices h : ∀ m ≤ nb, (List.range m).foldl (fun st j ↦
      writeBlock st.1 (j * B) (fractionsX B (ev ((b0 + j) * B)) ls chs apl).toArray st.2 B W)
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
    have hfs (c : Nat) (hc : c < ls.length) := fractionsX_getD hB (ev ((b0 + m) * B))
      (fun i ↦ env ((b0 + m) * B + i)) ls chs apl hapl (hev m (by omega)) c hc
    have hsize : (fractionsX B (ev ((b0 + m) * B)) ls chs apl).toArray.size = ls.length := by
      rw [List.size_toArray, length_fractionsX]
    have hrow (i : Nat) (hi : i < B) : (frs ((b0 + m) * B + i)) =
        (fractionsX B (ev ((b0 + m) * B)) ls chs apl).map (·.get i) := by
      apply List.ext_getElem (by rw [List.length_map, length_fractionsX, hfrs, List.length_map,
        List.length_zipIdx])
      intro c h1 h2
      have hc : c < ls.length := by rwa [hfrs, List.length_map, List.length_zipIdx] at h1
      rw [List.getElem_map]
      have := hfs c hc
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some] at this
      rw [get_tab hB this i hi]
      simp only [hfrs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hx := writeBlock_rel Z (rangeVal frs (b0 * B) W) (m * B)
      (fractionsX B (ev ((b0 + m) * B)) ls chs apl).toArray (localAcc frs (b0 * B) (m * B)) B W
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
        have hfsc : (fractionsX B (ev ((b0 + m) * B)) ls chs apl).toArray.getD c (EVec.zeros 0) =
            (fractionsX B (ev ((b0 + m) * B)) ls chs apl)[c]'(by
              rw [length_fractionsX]; exact hc) := by
          rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
            List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some]
        have hcW : 4 * (c + 1) + 3 < W := by rw [hW]; omega
        obtain ⟨hq0, hr0⟩ := div_mod_row W (m * B + i) (4 * (c + 1)) (by omega)
        obtain ⟨hq1, hr1⟩ := div_mod_row W (m * B + i) (4 * (c + 1) + 1) (by omega)
        obtain ⟨hq2, hr2⟩ := div_mod_row W (m * B + i) (4 * (c + 1) + 2) (by omega)
        obtain ⟨hq3, hr3⟩ := div_mod_row W (m * B + i) (4 * (c + 1) + 3) (by omega)
        rw [← Nat.add_assoc] at hq1 hr1 hq2 hr2 hq3 hr3
        have hfr : (frs (b0 * B + (m * B + i))).getD c 0 = Lookup.fraction
            (env ((b0 + m) * B + i)) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) ls[c] := by
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
theorem assembleRanges_eq [Mont32BaseField p] [Binomial4 p] (ev : Nat → Expr F → ByteArray)
    (ls : List (Stark.Lookup F))
    (chs : List EF) (B blocks : Nat) (env : Nat → Expr.Env F F) (frs : Nat → List EF)
    (hB : 4 * B < USize.size) (hsz : 4 * (blocks * B * ((ls.length + 1) * 4)) < USize.size)
    (hdiv : (if blocks < 16 then 1 else 16) ∣ blocks)
    (hfrs : ∀ r, frs r = ls.zipIdx.map fun (l, c) ↦
      Lookup.fraction (env r) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) l)
    (hev : ∀ j < blocks, ∀ l ∈ ls, ∀ x ∈ l.tuples,
      (∀ e ∈ x.1, ev (j * B) e = encode (tab B fun i ↦ e.eval (env (j * B + i)))) ∧
      ev (j * B) x.2 = encode (tab B fun i ↦ x.2.eval (env (j * B + i)))) :
    assembleRanges ev ls chs B ((ls.length + 1) * 4) blocks =
      (encode (tab (blocks * B * ((ls.length + 1) * 4)) (specWord frs ls.length)),
        specAcc frs (blocks * B)) := by
  unfold assembleRanges
  dsimp only
  have htpos : 0 < (if blocks < 16 then 1 else 16) := by split <;> omega
  generalize (if blocks < 16 then 1 else 16) = tasks at hdiv htpos ⊢
  generalize hW : (ls.length + 1) * 4 = W at hsz ⊢
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
      rangeRows ev ls chs B W (k * size) (if k + 1 = tasks then tasks * size - k * size else size)
        = (encode (tab (size * B * W) (rangeVal frs (k * size * B) W)),
          localAcc frs (k * size * B) (size * B)) := by
    rw [hcount k hk]
    refine rangeRows_eq ev ls chs B W (k * size) size env frs hW.symm hB ?_ hfrs fun j hj ↦ ?_
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right W
        (Nat.mul_le_mul_right B (Nat.le_mul_of_pos_left size ht0)))) hsz
    · exact hev (k * size + j) (by nlinarith)
  -- The accumulators before the ranges, and the terminal.
  have hstarts : (Array.map (fun k ↦ Task.spawn fun _ ↦ rangeRows ev ls chs B W (k * size)
      (if k + 1 = tasks then tasks * size - k * size else size)) (Array.range tasks)).foldl
      (fun (acc : Array EF × EF) t ↦ (acc.1.push acc.2, acc.2 + t.get.2)) (#[], 0) =
      (tab tasks fun k ↦ specAcc frs (k * size * B), specAcc frs (tasks * size * B)) := by
    rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
    suffices h : ∀ m ≤ tasks, (List.range m).foldl (fun (acc : Array EF × EF) k ↦
        (acc.1.push acc.2, acc.2 + (Task.spawn fun _ ↦ rangeRows ev ls chs B W (k * size)
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
      specWord frs ls.length (k * (size * B * W) + j)) fun k hk ↦ ?_,
    foldl_tab_ranges (specWord frs ls.length) (size * B * W) tasks,
    show tasks * (size * B * W) = tasks * size * B * W by ring]
  have hget : ((Array.range tasks).map fun k ↦ Task.spawn fun _ ↦ rangeRows ev ls chs B W
      (k * size) (if k + 1 = tasks then tasks * size - k * size else size)).getD k
      (Task.pure (ByteArray.empty, 0)) = Task.spawn fun _ ↦ rangeRows ev ls chs B W (k * size)
        (if k + 1 = tasks then tasks * size - k * size else size) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hk, ite_true, Option.map_some, Option.getD_some]
  rw [hget, get_spawn, hrange k hk, getD_tab _ _ _ hk, hcount k hk]
  subst hW
  rw [shiftAccumulator_eq _ _ _ _ (by omega) (by rw [size_tab, Nat.mul_assoc])
    (by rw [size_tab]; exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right B (Nat.le_mul_of_pos_left size ht0)))) hsz),
    show size * B * ((ls.length + 1) * 4) = (size * B) * ((ls.length + 1) * 4) from rfl,
    shifted_rangeVal]
  refine congrArg encode (tab_congr fun j _ ↦ ?_)
  congr 1
  ring

/-- The generation's evaluation of a base expression on the block from row `r0`. -/
theorem genEval_eq [Mont32BaseField p] (A : Air F) (logN : Nat) (trace : Array F)
    (pis : List F) (parts e B blocks : Nat)
    (hpe : parts * 2 ^ e = 2 ^ logN) (hBR : B ∣ 2 ^ e) (hB0 : 0 < B)
    (hBs : 4 * B < USize.size)
    (htr : trace.size = 2 ^ logN * A.width)
    (hpre : A.preprocessed.size = 2 ^ logN * A.preprocessedWidth)
    (hmem : Addressable (2 ^ logN * (A.width + A.preprocessedWidth)))
    (r0 : Nat) (hr0 : B ∣ r0) (hr : r0 + B ≤ 2 ^ logN) (ex : Expr F)
    (hex : ex.colsBelow A.width A.width A.preprocessedWidth A.preprocessedWidth = true) :
    evalWords (p := p) (transposePieces ⟨A.width, 2 ^ logN,
        NTTFast.Packed.Native.encodeFields trace⟩ parts (2 ^ e))
      (transposePieces ⟨A.preprocessedWidth, 2 ^ logN,
        NTTFast.Packed.Native.encodeFields A.preprocessed⟩ parts (2 ^ e))
      ByteArray.empty A.width A.preprocessedWidth 0 (2 ^ logN) (2 ^ e) B
      (Array.ofFn (n := 2 ^ logN) fun i ↦ (i.val + 1) % 2 ^ logN) (Array.replicate blocks none) pis
      (NTTFast.Packed.Native.encodeFields (Array.ofFn (n := 2 ^ logN) fun i ↦
        if (i.val == 0) = true then (1 : F) else 0))
      (NTTFast.Packed.Native.encodeFields (Array.ofFn (n := 2 ^ logN) fun i ↦
        if (i.val + 1 == 2 ^ logN) = true then (1 : F) else 0))
      (NTTFast.Packed.Native.encodeFields (Array.ofFn (n := 2 ^ logN) fun i ↦
        if decide (i.val + 1 < 2 ^ logN) = true then (1 : F) else 0)) r0 ex =
      encode (tab B fun i ↦ ex.eval (Lookup.generationRow A logN trace pis (r0 + i))) := by
  have hR : 0 < 2 ^ e := Nat.two_pow_pos e
  have hus : 4 * trace.size < USize.size := by
    unfold Addressable at hmem; rw [htr]; nlinarith
  have husp : 4 * A.preprocessed.size < USize.size := by
    unfold Addressable at hmem; rw [hpre]; nlinarith
  have hc := transposePieces_rel (p := p) (m := ⟨A.width, 2 ^ logN,
    NTTFast.Packed.Native.encodeFields trace⟩) (s := ⟨A.width, 2 ^ logN, trace⟩)
    ⟨rfl, rfl, NTTFast.Packed.Native.encodeFields_eq trace⟩ parts (2 ^ e)
    (by show parts * 2 ^ e * A.width ≤ trace.size; rw [hpe, htr]) hus
  have hpc := transposePieces_rel (p := p) (m := ⟨A.preprocessedWidth, 2 ^ logN,
    NTTFast.Packed.Native.encodeFields A.preprocessed⟩)
    (s := ⟨A.preprocessedWidth, 2 ^ logN, A.preprocessed⟩)
    ⟨rfl, rfl, NTTFast.Packed.Native.encodeFields_eq _⟩ parts (2 ^ e)
    (by show parts * 2 ^ e * A.preprocessedWidth ≤ A.preprocessed.size; rw [hpe, hpre]) husp
  rw [hc, hpc, NTTFast.Packed.Native.encodeFields_eq, NTTFast.Packed.Native.encodeFields_eq,
    NTTFast.Packed.Native.encodeFields_eq]
  have := evalWords_eq trace A.preprocessed #[] A.width A.preprocessedWidth 0 (2 ^ logN) parts
    (2 ^ e) B (Array.ofFn (n := 2 ^ logN) fun i ↦ (i.val + 1) % 2 ^ logN)
    (Array.replicate blocks none) pis
    (Array.ofFn (n := 2 ^ logN) fun i ↦ if (i.val == 0) = true then (1 : F) else 0)
    (Array.ofFn (n := 2 ^ logN) fun i ↦ if (i.val + 1 == 2 ^ logN) = true then (1 : F) else 0)
    (Array.ofFn (n := 2 ^ logN) fun i ↦
      if decide (i.val + 1 < 2 ^ logN) = true then (1 : F) else 0) r0
    (Lookup.generationRow A logN trace pis) hR hBR hB0 hr0 (by rw [hpe]; exact hr)
    (by rw [hpe, htr, Nat.mul_comm]) hus (by rw [hpe, hpre, Nat.mul_comm]) husp
    (by rw [Nat.zero_mul]; exact Nat.zero_le _) hr hBs ?_ ?_ (by rw [Array.size_ofFn]; exact hr)
    (by rw [Array.size_ofFn]; exact hr) (by rw [Array.size_ofFn]; exact hr)
    (fun _ _ _ _ ↦ rfl) ?_ (fun _ _ _ _ ↦ rfl) ?_
    (fun _ _ c ↦ (ite_eq_right_iff.mpr fun h ↦ absurd h (Nat.not_lt_zero c)).symm)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) ?_ ?_ ?_ ex hex
  · rw [CompPoly.PackedRepr.encode_empty] at this
    exact this
  · intro j hj
    rw [hpe] at hj ⊢
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · intro n0 h0
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h0
    split at h0 <;> simp only [Option.getD_some, Option.getD_none, reduceCtorEq] at h0
  · intro j hj c _
    rw [hpe] at hj
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj]
    rfl
  · intro j hj c _
    rw [hpe] at hj
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj]
    rfl
  · intro j hj
    rw [hpe] at hj
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj]
    simp only [Lookup.generationRow, beq_iff_eq]
  · intro j hj
    rw [hpe] at hj
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj]
    simp only [Lookup.generationRow, beq_iff_eq]
  · intro j hj
    rw [hpe] at hj
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj]
    simp only [Lookup.generationRow, decide_eq_true_eq]

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
  obtain ⟨e, hRe, hpe, hBR, hB0, hnB, htasks⟩ := genShape logN
  generalize (if 2 ^ logN < 4096 then 1 else 16) = parts at hRe hpe ⊢
  rw [hRe]
  generalize hB : min (2 ^ e) 256 = B at hBR hB0 hnB htasks ⊢
  generalize hbl : 2 ^ logN / B = blocks at hnB htasks ⊢
  have hB256 : B ≤ 256 := by rw [← hB]; exact Nat.min_le_right _ _
  have hBs : 4 * B < USize.size := by have := USize.le_size; omega
  have hsz : 4 * (blocks * B * ((ls.length + 1) * 4)) < USize.size := by
    rw [hnB]; unfold Addressable at hmem; nlinarith
  have hpw : Addressable (2 ^ logN * (A.width + A.preprocessedWidth)) := by
    unfold Addressable at hmem ⊢; nlinarith
  rw [assembleRanges_eq _ ls chs B blocks (Lookup.generationRow A logN trace pis) frs hBs hsz
    htasks (fun r ↦ by rw [← hfrs]; rfl) fun j hj l hl x hx ↦ ?_, hnB]
  · rw [show 2 ^ logN * (ls.length + 1) * 4 = 2 ^ logN * ((ls.length + 1) * 4) by ring]
  · have hjB : j * B + B ≤ 2 ^ logN := by
      rw [← hnB]; have := Nat.mul_le_mul_right B (hj : j + 1 ≤ blocks); rw [Nat.succ_mul] at this
      exact this
    have hcols := hls l hl x hx
    exact ⟨fun ex hex ↦ genEval_eq A logN trace pis parts e B blocks hpe hBR hB0 hBs htr hpre hpw
      (j * B) (Dvd.intro_left j rfl) hjB ex (hcols.1 ex hex),
      genEval_eq A logN trace pis parts e B blocks hpe hBR hB0 hBs htr hpre hpw (j * B)
        (Dvd.intro_left j rfl) hjB x.2 hcols.2⟩


/-- **The fast extension of the permutation trace is the specification's**, and so is its
terminal. -/
theorem permutationLdeWith_rel [Mont32BaseField p] [Binomial4 p] [PackedCosetLde p]
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
  refine ⟨ldeWordsWith_rel plans hplans logN bits gen _ _ hsize hok.twoAdic ?_, rfl⟩
  have := hok.mem
  unfold Addressable at this ⊢
  rw [Mont32.d_ext4] at this
  have := Nat.mul_le_mul_left (2 ^ (logN + bits))
    (Nat.le_add_left ((ls.length + 1) * 4) (A.width + A.preprocessedWidth))
  omega


end CompStark.Stark.Fast
