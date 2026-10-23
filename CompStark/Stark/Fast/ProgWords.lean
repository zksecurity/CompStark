/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgWords
public import CompStark.Stark.ProgCompile
public import CompStark.Stark.Fast.WordsLemmas

/-! # Programs on blocks of packed words compute the field's values

On encoded field arrays, a pass of `B` words overwrites a range of the registers (`updR`) with the
operation on its operands' words, sixteen words or one word at a time (`passBin_encode`,
`passWord_encode`), or adds its operand times four weights to the accumulator planes
(`passAcc_encode`). So an instruction on a block of `B` rows is the instruction on each row's
values (`execBlock_rel`, on the rows' values `blockCtx`), and so is a program (`runBlock_rel`):
the packed run simulates `B` runs on the field.
-/

@[expose] public section
namespace CompStark.Stark.Fast

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

theorem getElem_tab {α : Type} (B : Nat) (f : Nat → α) (i : Nat) (h : i < (tab B f).size) :
    (tab B f)[i] = f i := by
  simp only [tab, Array.getElem_ofFn]

theorem getD_tab {α : Type} (B : Nat) (f : Nat → α) (i : Nat) (h : i < B) (d : α) :
    (tab B f).getD i d = f i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [size_tab]; exact h),
    Option.getD_some]
  simp only [tab, Array.getElem_ofFn]

end CompStark.Stark.Fast

namespace CompStark.Stark.Prog
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul add_val sub_val mul_val
  size_encode_fields splice getD_splice size_splice lit16 getD_lit16 size_lit16
  array_eq_of_getD getD_ofFn_bounded)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write write16U zeroWords)
open CompStark.Poseidon2.Packed (Fits)
open CompStark.Words (rd rd_encode read_encode)
open Montgomery.Native32
open CompStark.Stark.Fast (tab size_tab tab_congr getD_tab)

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

/-! ### Ranges of an array overwritten -/

/-- Entry `idx` of `updR`. -/
def updF (X : Array F) (od m : Nat) (G : Nat → F) (idx : Nat) : F :=
  if od ≤ idx ∧ idx < od + m then G (idx - od) else X.getD idx 0

/-- `X` with its entries `od, …, od + m - 1` replaced by `G 0, …, G (m - 1)`. -/
def updR (X : Array F) (od m : Nat) (G : Nat → F) : Array F :=
  Array.ofFn (n := X.size) fun idx ↦ updF X od m G idx.val

@[simp] theorem size_updR (X : Array F) (od m : Nat) (G : Nat → F) :
    (updR X od m G).size = X.size := Array.size_ofFn

theorem getD_updR (X : Array F) (od m : Nat) (G : Nat → F) (idx : Nat) :
    (updR X od m G).getD idx 0 =
      if idx < X.size ∧ od ≤ idx ∧ idx < od + m then G (idx - od) else X.getD idx 0 := by
  unfold updR
  rw [Words.getD_ofFn X.size (updF X od m G)]
  by_cases h : idx < X.size
  · simp only [h, true_and, ite_true, updF]
  · simp only [h, false_and, ite_false]
    exact (Words.getD_eq_zero X idx (by omega)).symm

theorem updR_congr {X : Array F} {od m : Nat} {G G' : Nat → F} (h : ∀ k < m, G k = G' k) :
    updR X od m G = updR X od m G' := by
  unfold updR updF
  refine congrArg Array.ofFn (funext fun idx ↦ ?_)
  split
  · rename_i hi; rw [h _ (by omega)]
  · rfl

theorem updR_zero (X : Array F) (od : Nat) (G : Nat → F) : updR X od 0 G = X := by
  apply array_eq_of_getD _ _ 0 (size_updR ..)
  intro idx
  rw [getD_updR]
  split
  · omega
  · rfl

/-- Sixteen more entries overwritten. -/
theorem splice_updR (X : Array F) (od m : Nat) (G : Nat → F) (h : od + m + 16 ≤ X.size) :
    splice (updR X od m G) (od + m) (lit16 fun t ↦ G (m + t)) = updR X od (m + 16) G := by
  apply array_eq_of_getD _ _ 0 (by rw [size_splice _ _ _ (by rw [size_updR, size_lit16]; omega),
    size_updR, size_updR])
  intro idx
  rw [getD_splice _ _ _ (by rw [size_updR, size_lit16]; omega), getD_updR, getD_updR, size_lit16]
  by_cases h1 : idx < od + m
  · simp only [h1, ite_true]
    by_cases h2 : od ≤ idx
    · simp only [show idx < X.size by omega, h2, true_and, ite_true,
        show idx < od + (m + 16) by omega]
    · simp only [h2, false_and, and_false, ite_false]
  · by_cases h2 : idx < od + m + 16
    · simp only [h1, h2, ite_false, ite_true, show idx < X.size by omega, true_and,
        show od ≤ idx by omega, show idx < od + (m + 16) by omega]
      rw [getD_lit16 _ _ (by omega)]
      congr 1
      omega
    · simp only [h1, h2, ite_false, show ¬(od ≤ idx ∧ idx < od + (m + 16)) by omega, and_false]

/-- One more entry overwritten. -/
theorem set_updR (X : Array F) (od m : Nat) (G : Nat → F) (h : od + m < X.size) :
    (updR X od m G).setIfInBounds (od + m) (G m) = updR X od (m + 1) G := by
  apply array_eq_of_getD _ _ 0 (by simp only [Array.size_setIfInBounds, size_updR])
  intro idx
  rw [CompPoly.CPolynomial.NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by rw [size_updR]; omega),
    getD_updR, getD_updR]
  by_cases hi : idx = od + m
  · subst hi
    simp only [ite_true, h, Nat.le_add_right, true_and, show od + m < od + (m + 1) by omega,
      Nat.add_sub_cancel_left]
  · simp only [hi, ite_false]
    by_cases h1 : idx < X.size ∧ od ≤ idx ∧ idx < od + m
    · simp only [h1, and_self, ite_true, show idx < od + (m + 1) by omega]
    · simp only [h1, ite_false, show ¬(idx < X.size ∧ od ≤ idx ∧ idx < od + (m + 1)) by omega]

/-! ### Reads -/

/-- A checked read of an encoded array in range. -/
theorem read_encode' (a : Array F) (i : Nat) (hs : 4 * a.size < USize.size) (hi : i < a.size) :
    read (encode a) i = (a.getD i 0).val :=
  read_encode a i hs hi

/-- A sixteen-word kernel on words of encoded arrays: the operation on their entries. -/
theorem lanes16_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (x y : (k : Nat) → k ≤ 15 → UInt32)
    (xv yv : Nat → F) (hx : ∀ k hk, x k hk = (xv k).val) (hy : ∀ k hk, y k hk = (yv k).val)
    (Y : Array F) (io : USize) (hs : 4 * Y.size < USize.size) (hi : io.toNat + 16 ≤ Y.size) :
    lanes16 f x y (encode Y) io =
      encode (splice Y io.toNat (lit16 fun t ↦ g (xv t) (yv t))) := by
  unfold lanes16
  simp only [hx, hy, hf]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact hs) hi]
  rfl

/-- Word `j` of an operand's buffer: the registers' `Y` if `inR`, else `E`. -/
def pick (inR : Bool) (Y E : Array F) (j : Nat) : F := if inR then Y.getD j 0 else E.getD j 0

/-- The sixteen-word kernels on encoded arrays. -/
theorem k16RR_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Y : Array F) (io ia ib : USize)
    (hs : 4 * Y.size < USize.size) (hi : io.toNat + 16 ≤ Y.size) (ha hb) :
    k16RR f (encode Y) io ia ib ha hb = encode (splice Y io.toNat (lit16 fun t ↦
      g (Y.getD (ia.toNat + t) 0) (Y.getD (ib.toNat + t) 0))) :=
  lanes16_encode f g hf _ _ _ _ (fun _ hk ↦ rd_encode Y _ _ _ hk)
    (fun _ hk ↦ rd_encode Y _ _ _ hk) Y io hs hi

theorem k16RX_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Y E : Array F) (io ia ib : USize)
    (hs : 4 * Y.size < USize.size) (hi : io.toNat + 16 ≤ Y.size) (ha hb) :
    k16RX f (encode Y) (encode E) io ia ib ha hb = encode (splice Y io.toNat (lit16 fun t ↦
      g (Y.getD (ia.toNat + t) 0) (E.getD (ib.toNat + t) 0))) :=
  lanes16_encode f g hf _ _ _ _ (fun _ hk ↦ rd_encode Y _ _ _ hk)
    (fun _ hk ↦ rd_encode E _ _ _ hk) Y io hs hi

theorem k16XR_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Y E : Array F) (io ia ib : USize)
    (hs : 4 * Y.size < USize.size) (hi : io.toNat + 16 ≤ Y.size) (ha hb) :
    k16XR f (encode Y) (encode E) io ia ib ha hb = encode (splice Y io.toNat (lit16 fun t ↦
      g (E.getD (ia.toNat + t) 0) (Y.getD (ib.toNat + t) 0))) :=
  lanes16_encode f g hf _ _ _ _ (fun _ hk ↦ rd_encode E _ _ _ hk)
    (fun _ hk ↦ rd_encode Y _ _ _ hk) Y io hs hi

theorem k16XX_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Y Ea Eb : Array F) (io ia ib : USize)
    (hs : 4 * Y.size < USize.size) (hi : io.toNat + 16 ≤ Y.size) (ha hb) :
    k16XX f (encode Y) (encode Ea) (encode Eb) io ia ib ha hb = encode (splice Y io.toNat
      (lit16 fun t ↦ g (Ea.getD (ia.toNat + t) 0) (Eb.getD (ib.toNat + t) 0))) :=
  lanes16_encode f g hf _ _ _ _ (fun _ hk ↦ rd_encode Ea _ _ _ hk)
    (fun _ hk ↦ rd_encode Eb _ _ _ hk) Y io hs hi

theorem k16RW_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Y : Array F) (io ia : USize) (c : F)
    (hs : 4 * Y.size < USize.size) (hi : io.toNat + 16 ≤ Y.size) (ha) :
    k16RW f (encode Y) io ia c.val ha =
      encode (splice Y io.toNat (lit16 fun t ↦ g (Y.getD (ia.toNat + t) 0) c)) :=
  lanes16_encode f g hf _ _ _ (fun _ ↦ c) (fun _ hk ↦ rd_encode Y _ _ _ hk)
    (fun _ _ ↦ rfl) Y io hs hi

theorem k16XW_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Y E : Array F) (io ia : USize) (c : F)
    (hs : 4 * Y.size < USize.size) (hi : io.toNat + 16 ≤ Y.size) (ha) :
    k16XW f (encode Y) (encode E) io ia c.val ha =
      encode (splice Y io.toNat (lit16 fun t ↦ g (E.getD (ia.toNat + t) 0) c)) :=
  lanes16_encode f g hf _ _ _ (fun _ ↦ c) (fun _ hk ↦ rd_encode E _ _ _ hk)
    (fun _ _ ↦ rfl) Y io hs hi

theorem lit16_congr {φ ψ : Nat → F} (h : ∀ t < 16, φ t = ψ t) : lit16 φ = lit16 ψ := by
  unfold lit16
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
    h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
    h 15 (by decide)]

/-- An operand's buffer apart from the destination's `B` words: in the registers, its words are
the destination's or lie outside them. -/
def Apart (inR : Bool) (oa od B : Nat) : Prop :=
  inR = true → oa = od ∨ oa + B ≤ od ∨ od + B ≤ oa

/-- An operand apart from the destination reads its original words while the destination's first
`m` are overwritten, at words from its `m`-th on. -/
theorem pick_updR {inR : Bool} {oa od B : Nat} (h : Apart inR oa od B) (X E : Array F)
    (m : Nat) (G : Nat → F) (k : Nat) (hk : m ≤ k) (hkB : k < B) :
    pick inR (updR X od m G) E (oa + k) = pick inR X E (oa + k) := by
  unfold pick
  split
  · rename_i hr
    rw [getD_updR]
    have := h hr
    rw [ite_eq_right_iff.mpr fun h' ↦ absurd h' (by omega)]
  · rfl

theorem groupsBin_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Ea Eb X : Array F) (ra rb : Bool) (S : Nat)
    (hS : S < USize.size) (hEa : (encode Ea).size < USize.size)
    (hEb : (encode Eb).size < USize.size) (hSX : S = 4 * X.size)
    (od oa ob B : Nat) (haA : Apart ra oa od B) (hbA : Apart rb ob od B)
    (G : Nat → F) (hG : ∀ k, G k = g (pick ra X Ea (oa + k)) (pick rb X Eb (ob + k))) :
    ∀ n m, m + 16 * n ≤ B → ∀ out hout hd ha hb, out = encode (updR X od m G) →
      groupsBin f (encode Ea) (encode Eb) ra rb S hS hEa hEb n (od + m) (oa + m) (ob + m) out
        hout hd ha hb =
        encode (updR X od (m + 16 * n) G) := by
  intro n
  induction n with
  | zero => intro m _ out _ _ _ _ h; subst h; rfl
  | succ n ih =>
    intro m hm out hout hd ha hb hout'
    subst hout'
    have hs : 4 * (updR X od m G).size < USize.size := by rw [size_updR]; omega
    have hi : od + m + 16 ≤ (updR X od m G).size := by rw [size_updR]; omega
    have hlit (ra' rb' : Bool) (hra : ra' = ra) (hrb : rb' = rb) :
        (lit16 fun t ↦ g (pick ra' (updR X od m G) Ea (oa + m + t))
          (pick rb' (updR X od m G) Eb (ob + m + t))) = lit16 fun t ↦ G (m + t) := by
      subst hra hrb
      refine lit16_congr fun t ht ↦ ?_
      rw [Nat.add_assoc, Nat.add_assoc, pick_updR haA X Ea m G _ (by omega) (by omega),
        pick_updR hbA X Eb m G _ (by omega) (by omega), hG]
    have hnext : ∀ out' (h' : out'.size = S) hd' ha' hb',
        out' = encode (splice (updR X od m G) (od + m) (lit16 fun t ↦ G (m + t))) →
        groupsBin f (encode Ea) (encode Eb) ra rb S hS hEa hEb n (od + m + 16) (oa + m + 16)
          (ob + m + 16) out' h' hd' ha' hb' = encode (updR X od (m + 16 * (n + 1)) G) := by
      intro out' h' hd' ha' hb' e
      rw [splice_updR X od m G (by omega)] at e
      have := ih (m + 16) (by omega) out' h' (by omega) (by omega) (by omega) e
      rw [show m + 16 + 16 * n = m + 16 * (n + 1) by ring] at this
      simp only [Nat.add_assoc] at this ⊢
      exact this
    rw [groupsBin]
    dsimp only
    split
    · rename_i hra
      split
      · rename_i hrb
        apply hnext
        rw [k16RR_encode f g hf _ _ _ _ hs (by simp only [USize.toNat_ofNatLT]; exact hi)]
        simp only [USize.toNat_ofNatLT]
        rw [← hlit true true hra.symm hrb.symm]
        rfl
      · rename_i hrb
        apply hnext
        rw [k16RX_encode f g hf _ Eb _ _ _ hs (by simp only [USize.toNat_ofNatLT]; exact hi)]
        simp only [USize.toNat_ofNatLT]
        rw [← hlit true false hra.symm (Bool.eq_false_iff.mpr hrb).symm]
        rfl
    · rename_i hra
      split
      · rename_i hrb
        apply hnext
        rw [k16XR_encode f g hf _ Ea _ _ _ hs (by simp only [USize.toNat_ofNatLT]; exact hi)]
        simp only [USize.toNat_ofNatLT]
        rw [← hlit false true (Bool.eq_false_iff.mpr hra).symm hrb.symm]
        rfl
      · rename_i hrb
        apply hnext
        rw [k16XX_encode f g hf _ Ea Eb _ _ _ hs (by simp only [USize.toNat_ofNatLT]; exact hi)]
        simp only [USize.toNat_ofNatLT]
        rw [← hlit false false (Bool.eq_false_iff.mpr hra).symm
          (Bool.eq_false_iff.mpr hrb).symm]
        rfl

/-- A read of an operand's buffer in range. -/
theorem read_pick (inR : Bool) (Y E : Array F) (j : Nat) (hY : 4 * Y.size < USize.size)
    (hE : 4 * E.size < USize.size) (hj : j < if inR then Y.size else E.size) :
    (if inR then read (encode Y) j else read (encode E) j) = (pick inR Y E j).val := by
  unfold pick
  split
  · rename_i h; simp only [h, ite_true] at hj; exact read_encode Y j hY hj
  · rename_i h; simp only [h, Bool.false_eq_true, ite_false] at hj; exact read_encode E j hE hj

theorem tailBin_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Ea Eb X : Array F) (ra rb : Bool)
    (hX : 4 * X.size < USize.size) (hEas : 4 * Ea.size < USize.size)
    (hEbs : 4 * Eb.size < USize.size)
    (od oa ob B : Nat) (hB : od + B ≤ X.size) (haA : Apart ra oa od B) (hbA : Apart rb ob od B)
    (hai : oa + B ≤ if ra then X.size else Ea.size)
    (hbi : ob + B ≤ if rb then X.size else Eb.size)
    (G : Nat → F) (hG : ∀ k, G k = g (pick ra X Ea (oa + k)) (pick rb X Eb (ob + k))) :
    ∀ n k, k + n ≤ B →
      tailBin f (encode Ea) (encode Eb) ra rb od oa ob k n (encode (updR X od k G)) =
        encode (updR X od (k + n) G) := by
  intro n
  induction n with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k hk
    rw [tailBin]
    have hs : 4 * (updR X od k G).size < USize.size := by rw [size_updR]; exact hX
    have hra := read_pick ra (updR X od k G) Ea (oa + k) hs hEas (by
      rw [size_updR]; cases ra <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hai ⊢ <;>
        omega)
    have hrb := read_pick rb (updR X od k G) Eb (ob + k) hs hEbs (by
      rw [size_updR]; cases rb <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hbi ⊢ <;>
        omega)
    rw [hra, hrb, pick_updR haA X Ea k G _ (Nat.le_refl _) (by omega),
      pick_updR hbA X Eb k G _ (Nat.le_refl _) (by omega), hf, ← hG,
      CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _
        (by rw [size_encode_fields]; exact hs) (by rw [size_updR]; omega),
      set_updR X od k G (by omega), ih (k + 1) (by omega)]
    rw [Nat.add_assoc, Nat.add_comm 1 n]

/-- **A pass of an operation** on two operands apart from the destination overwrites the
destination's `B` words with the operation on the operands' words. -/
theorem passBin_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (Ea Eb X : Array F) (S : Nat)
    (hS : S < USize.size) (hEa : (encode Ea).size < USize.size)
    (hEb : (encode Eb).size < USize.size) (hSX : S = 4 * X.size)
    (od : Nat) (ra : Bool) (oa : Nat) (rb : Bool) (ob B : Nat) (hB : od + B ≤ X.size)
    (haA : Apart ra oa od B) (hbA : Apart rb ob od B)
    (hai : oa + B ≤ if ra then X.size else Ea.size)
    (hbi : ob + B ≤ if rb then X.size else Eb.size)
    (out : ByteArray) (hr : out.size = S) (ho : out = encode X) :
    passBin f (encode Ea) (encode Eb) S hS hEa hEb od ra oa rb ob B out hr =
      encode (updR X od B fun k ↦ g (pick ra X Ea (oa + k)) (pick rb X Eb (ob + k))) := by
  subst ho
  have hEas : 4 * Ea.size < USize.size := by rw [size_encode_fields] at hEa; exact hEa
  have hEbs : 4 * Eb.size < USize.size := by rw [size_encode_fields] at hEb; exact hEb
  have hX : 4 * X.size < USize.size := by omega
  have ht := tailBin_encode f g hf Ea Eb X ra rb hX hEas hEbs od oa ob B hB haA hbA hai hbi _
    fun _ ↦ rfl
  unfold passBin
  dsimp only
  split
  · rename_i h
    have hg := groupsBin_encode f g hf Ea Eb X ra rb S hS hEa hEb hSX od oa ob B haA hbA _
      (fun _ ↦ rfl) (B / 16) 0 (by omega) (encode X) hr (by simpa only [Nat.add_zero] using h.1)
      (by simpa only [Nat.add_zero] using h.2.1) (by simpa only [Nat.add_zero] using h.2.2)
      (by rw [updR_zero])
    simp only [Nat.add_zero, Nat.zero_add] at hg
    rw [hg, ht (B - 16 * (B / 16)) (16 * (B / 16)) (by omega)]
    congr 2
    omega
  · rw [← updR_zero X od (fun k ↦ g (pick ra X Ea (oa + k)) (pick rb X Eb (ob + k))), ht B 0
      (by omega), Nat.zero_add, updR_zero]

theorem groupsWord_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (E X : Array F) (ra : Bool) (c : F) (S : Nat)
    (hS : S < USize.size) (hE : (encode E).size < USize.size) (hSX : S = 4 * X.size)
    (od oa B : Nat) (haA : Apart ra oa od B)
    (G : Nat → F) (hG : ∀ k, G k = g (pick ra X E (oa + k)) c) :
    ∀ n m, m + 16 * n ≤ B → ∀ out hout hd ha, out = encode (updR X od m G) →
      groupsWord f (encode E) ra c.val S hS hE n (od + m) (oa + m) out hout hd ha =
        encode (updR X od (m + 16 * n) G) := by
  intro n
  induction n with
  | zero => intro m _ out _ _ _ h; subst h; rfl
  | succ n ih =>
    intro m hm out hout hd ha hout'
    subst hout'
    have hs : 4 * (updR X od m G).size < USize.size := by rw [size_updR]; omega
    have hi : od + m + 16 ≤ (updR X od m G).size := by rw [size_updR]; omega
    have hlit (ra' : Bool) (hra : ra' = ra) :
        (lit16 fun t ↦ g (pick ra' (updR X od m G) E (oa + m + t)) c) =
          lit16 fun t ↦ G (m + t) := by
      subst hra
      refine lit16_congr fun t ht ↦ ?_
      rw [Nat.add_assoc, pick_updR haA X E m G _ (by omega) (by omega), hG]
    have hnext : ∀ out' (h' : out'.size = S) hd' ha',
        out' = encode (splice (updR X od m G) (od + m) (lit16 fun t ↦ G (m + t))) →
        groupsWord f (encode E) ra c.val S hS hE n (od + m + 16) (oa + m + 16) out' h' hd' ha' =
          encode (updR X od (m + 16 * (n + 1)) G) := by
      intro out' h' hd' ha' e
      rw [splice_updR X od m G (by omega)] at e
      have := ih (m + 16) (by omega) out' h' (by omega) (by omega) e
      rw [show m + 16 + 16 * n = m + 16 * (n + 1) by ring] at this
      simp only [Nat.add_assoc] at this ⊢
      exact this
    rw [groupsWord]
    dsimp only
    split
    · rename_i hra
      apply hnext
      rw [k16RW_encode f g hf _ _ _ c hs (by simp only [USize.toNat_ofNatLT]; exact hi)]
      simp only [USize.toNat_ofNatLT]
      rw [← hlit true hra.symm]
      rfl
    · rename_i hra
      apply hnext
      rw [k16XW_encode f g hf _ E _ _ c hs (by simp only [USize.toNat_ofNatLT]; exact hi)]
      simp only [USize.toNat_ofNatLT]
      rw [← hlit false (Bool.eq_false_iff.mpr hra).symm]
      rfl

theorem tailWord_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (E X : Array F) (ra : Bool) (c : F)
    (hX : 4 * X.size < USize.size) (hEs : 4 * E.size < USize.size)
    (od oa B : Nat) (hB : od + B ≤ X.size) (haA : Apart ra oa od B)
    (hai : oa + B ≤ if ra then X.size else E.size)
    (G : Nat → F) (hG : ∀ k, G k = g (pick ra X E (oa + k)) c) :
    ∀ n k, k + n ≤ B →
      tailWord f (encode E) ra c.val od oa k n (encode (updR X od k G)) =
        encode (updR X od (k + n) G) := by
  intro n
  induction n with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k hk
    rw [tailWord]
    have hs : 4 * (updR X od k G).size < USize.size := by rw [size_updR]; exact hX
    have hra := read_pick ra (updR X od k G) E (oa + k) hs hEs (by
      rw [size_updR]; cases ra <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hai ⊢ <;>
        omega)
    rw [hra, pick_updR haA X E k G _ (Nat.le_refl _) (by omega), hf, ← hG,
      CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _
        (by rw [size_encode_fields]; exact hs) (by rw [size_updR]; omega),
      set_updR X od k G (by omega), ih (k + 1) (by omega)]
    rw [Nat.add_assoc, Nat.add_comm 1 n]

/-- **A pass of an operation** on an operand apart from the destination and a word overwrites the
destination's `B` words with the operation on the operand's words and the word. -/
theorem passWord_encode (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (E X : Array F) (S : Nat)
    (hS : S < USize.size) (hE : (encode E).size < USize.size) (hSX : S = 4 * X.size)
    (od : Nat) (ra : Bool) (oa : Nat) (c : F) (B : Nat) (hB : od + B ≤ X.size)
    (haA : Apart ra oa od B) (hai : oa + B ≤ if ra then X.size else E.size)
    (out : ByteArray) (hr : out.size = S) (ho : out = encode X) :
    passWord f (encode E) S hS hE od ra oa c.val B out hr =
      encode (updR X od B fun k ↦ g (pick ra X E (oa + k)) c) := by
  subst ho
  have hEs : 4 * E.size < USize.size := by rw [size_encode_fields] at hE; exact hE
  have hX : 4 * X.size < USize.size := by omega
  have ht := tailWord_encode f g hf E X ra c hX hEs od oa B hB haA hai _ fun _ ↦ rfl
  unfold passWord
  dsimp only
  split
  · rename_i h
    have hg := groupsWord_encode f g hf E X ra c S hS hE hSX od oa B haA _
      (fun _ ↦ rfl) (B / 16) 0 (by omega) (encode X) hr (by simpa only [Nat.add_zero] using h.1)
      (by simpa only [Nat.add_zero] using h.2) (by rw [updR_zero])
    simp only [Nat.add_zero, Nat.zero_add] at hg
    rw [hg, ht (B - 16 * (B / 16)) (16 * (B / 16)) (by omega)]
    congr 2
    omega
  · rw [← updR_zero X od (fun k ↦ g (pick ra X E (oa + k)) c), ht B 0 (by omega), Nat.zero_add,
      updR_zero]


theorem updR_full (X : Array F) (B : Nat) (hX : X.size = B) (G : Nat → F) :
    updR X 0 B G = tab B G := by
  apply array_eq_of_getD _ _ 0 (by rw [size_updR, size_tab, hX])
  intro idx
  rw [getD_updR]
  by_cases h : idx < B
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, Nat.zero_le _, by omega⟩),
      getD_tab _ _ _ h, Nat.sub_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Words.getD_eq_zero X idx (by omega),
      Words.getD_eq_zero (tab B G) idx (by rw [size_tab]; omega)]

/-! ### Passes on a register's buffer -/

/-- An operand's value on row `k` of a pass: a constant, or its word `o + k` of its buffer, the
destination's `X` itself if `self`, else `E`. -/
def Opd.rd (self : Bool) (X E : Array F) (o : Nat) (a : Opd F) (k : Nat) : F :=
  match a with
  | .const x => x
  | _ => pick self X E (o + k)

/-- A non-constant operand of a pass lies in its buffer, apart from the destination. -/
def Opd.Placed (self : Bool) (X E : Array F) (o B : Nat) (a : Opd F) : Prop :=
  (∀ x, a ≠ .const x) → Apart self o 0 B ∧ o + B ≤ if self then X.size else E.size

theorem fillWord_tab (X : Array F) (B S : Nat) (hS : S < USize.size) (hX : X.size = B)
    (hSX : S = 4 * B) (c : F) (out : ByteArray) (hr : out.size = S) (ho : out = encode X) :
    fillWord S hS out hr c.val B = encode (tab B fun _ ↦ c) := by
  unfold fillWord
  have h := passWord_encode (fun _ c ↦ c) (fun _ c ↦ c) (fun _ _ ↦ rfl) #[] X S hS
    (by simp only [CompPoly.PackedRepr.encode_empty, ByteArray.size_empty]; omega) (by omega) 0
    true 0 c B (by omega) (fun _ ↦ Or.inl rfl) (by simp only [ite_true]; omega) out hr ho
  rw [updR_full X B hX] at h
  exact h

theorem copyWords_tab (X A : Array F) (B S : Nat) (hS : S < USize.size) (hX : X.size = B)
    (hSX : S = 4 * B) (hA : 4 * A.size < USize.size) (o : Nat) (hoA : o + B ≤ A.size)
    (out : ByteArray) (hr : out.size = S) (ho : out = encode X) :
    copyWords S hS out hr (encode A) o B = encode (tab B fun k ↦ A.getD (o + k) 0) := by
  unfold copyWords
  rw [dite_eq_left (by rw [size_encode_fields]; exact hA)]
  rw [passBin_encode (fun x _ ↦ x) (fun x _ ↦ x) (fun _ _ ↦ rfl) A A X S hS _ _ (by omega) 0 false
    o false o B (by omega) (fun h ↦ absurd h (by simp only [Bool.false_eq_true,
      not_false_eq_true])) (fun h ↦ absurd h (by simp only [Bool.false_eq_true,
      not_false_eq_true])) (by simp only [Bool.false_eq_true, ite_false]; exact hoA)
    (by simp only [Bool.false_eq_true, ite_false]; exact hoA) out hr ho, updR_full X B hX]
  rfl

/-- The values of columns in blocks of rows (`Cols`): column `c` of block `b` is `C[b w + c]`. -/
structure ColsF (p : ℕ) [Mont32Field p] where
  C : Array (Array (FastField p))
  width : Nat
  rows : Nat

/-- The packed columns. -/
def ColsF.enc (m : ColsF p) : Cols := ⟨m.C.map encode, m.width, m.rows⟩

/-- The column of entry `(r, c)`. -/
abbrev ColsF.col (m : ColsF p) (r c : Nat) : Array F := m.C.getD (r / m.rows * m.width + c) #[]

/-- Entry `(r, c)`. -/
def ColsF.at (m : ColsF p) (r c : Nat) : F := (m.col r c).getD (r % m.rows) 0

/-- Entry `(r, c)` lies in its column. -/
def ColsF.Has (m : ColsF p) (r c : Nat) : Prop := r % m.rows < (m.col r c).size

/-- The columns are addressable by machine words. -/
def ColsF.Addr (m : ColsF p) : Prop := ∀ a ∈ m.C, 4 * a.size < USize.size

theorem ColsF.at_enc (m : ColsF p) (h : m.Addr) (r c : Nat) (hrc : m.Has r c) :
    m.enc.at r c = (m.at r c).val := by
  unfold Cols.at ColsF.enc ColsF.at
  dsimp only
  have hcol : (m.C.map encode).getD (r / m.rows * m.width + c) .empty = encode (m.col r c) := by
    unfold ColsF.col
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases m.C[r / m.rows * m.width + c]? with
    | none => rfl
    | some a => rfl
  rw [hcol]
  have hA : 4 * (m.col r c).size < USize.size := by
    unfold ColsF.col
    rw [Array.getD_eq_getD_getElem?]
    cases e : m.C[r / m.rows * m.width + c]? with
    | none => show 4 * 0 < USize.size; have := USize.le_size; omega
    | some a => exact h a (Array.mem_of_getElem? e)
  exact read_encode' _ _ hA hrc

theorem nextInto_encode (M : ColsF p) (X : Array F) (c : Nat) (next : Array Nat) (r0 B : Nat)
    (hX : 4 * X.size < USize.size) (hM : M.Addr) (hB : B ≤ X.size)
    (hin : ∀ k < B, M.Has (next.getD (r0 + k) 0) c) :
    ∀ n k, k + n ≤ B →
      nextInto M.enc c next r0 k n
        (encode (updR X 0 k fun k ↦ M.at (next.getD (r0 + k) 0) c)) =
        encode (updR X 0 (k + n) fun k ↦ M.at (next.getD (r0 + k) 0) c) := by
  intro n
  induction n with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k hk
    have hset := set_updR X 0 k (fun k ↦ M.at (next.getD (r0 + k) 0) c) (by omega)
    rw [Nat.zero_add] at hset
    rw [nextInto, M.at_enc hM _ c (hin k (by omega)),
      CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _
        (by rw [size_encode_fields, size_updR]; exact hX) (by rw [size_updR]; omega),
      hset, ih (k + 1) (by omega), Nat.add_assoc, Nat.add_comm 1 n]

/-- The values a block's loads hold (`Loads`): the trace, the preprocessed trace and the
permutation trace as columns, the block's rows of the last two transposed, the next rows, the
periodic columns and the selectors. -/
structure LoadsF (p : ℕ) [Mont32Field p] where
  M : ColsF p
  P : ColsF p
  PT : Array (FastField p)
  Q : ColsF p
  QT : Array (FastField p)
  r0 : Nat
  next : Array Nat
  nseq : Bool
  PER : Array (Array (FastField p))
  FS : Array (FastField p)
  LS : Array (FastField p)
  TS : Array (FastField p)

/-- The packed loads. -/
def LoadsF.enc (L : LoadsF p) : Loads :=
  ⟨L.M.enc, L.P.enc, encode L.PT, L.Q.enc, encode L.QT, L.r0, L.next, L.nseq,
    L.PER.map encode, encode L.FS, encode L.LS, encode L.TS⟩

/-- A loaded column on row `i` of a block of `B` rows. -/
def LoadsF.src (L : LoadsF p) (B i : Nat) : Src → F
  | .next c => L.M.at (L.next.getD (L.r0 + i) 0) c
  | .prepCur c => L.PT.getD (c * B + i) 0
  | .prepNext c => L.P.at (L.next.getD (L.r0 + i) 0) c
  | .permCur c => L.QT.getD (c * B + i) 0
  | .permNext c => L.Q.at (L.next.getD (L.r0 + i) 0) c
  | .periodic j => (L.PER.getD j #[]).getD (L.r0 + i) 0
  | .isFirstRow => L.FS.getD (L.r0 + i) 0
  | .isLastRow => L.LS.getD (L.r0 + i) 0
  | .isTransition => L.TS.getD (L.r0 + i) 0

/-- If the block's next rows are said to be consecutive, they are. -/
def LoadsF.Seq (L : LoadsF p) (B : Nat) : Prop :=
  L.nseq = true → ∀ k < B, L.next.getD (L.r0 + k) 0 = L.next.getD L.r0 0 + k

/-- A loaded column's words lie in their arrays on the block's `B` rows. -/
def LoadsF.InRange (L : LoadsF p) (B : Nat) : Src → Prop
  | .next c => (∀ k < B, L.M.Has (L.next.getD (L.r0 + k) 0) c) ∧ L.Seq B
  | .prepCur c => c * B + B ≤ L.PT.size
  | .prepNext c => (∀ k < B, L.P.Has (L.next.getD (L.r0 + k) 0) c) ∧ L.Seq B
  | .permCur c => c * B + B ≤ L.QT.size
  | .permNext c => (∀ k < B, L.Q.Has (L.next.getD (L.r0 + k) 0) c) ∧ L.Seq B
  | .periodic j => j < L.PER.size → L.r0 + B ≤ (L.PER.getD j #[]).size
  | .isFirstRow => L.r0 + B ≤ L.FS.size
  | .isLastRow => L.r0 + B ≤ L.LS.size
  | .isTransition => L.r0 + B ≤ L.TS.size

/-- The loads' arrays are addressable by machine words. -/
def LoadsF.Addr (L : LoadsF p) : Prop :=
  L.M.Addr ∧ L.P.Addr ∧ 4 * L.PT.size < USize.size ∧
    L.Q.Addr ∧ 4 * L.QT.size < USize.size ∧
    (∀ c ∈ L.PER, 4 * c.size < USize.size) ∧
    4 * L.FS.size < USize.size ∧ 4 * L.LS.size < USize.size ∧ 4 * L.TS.size < USize.size

theorem loadSrc_tab (X : Array F) (B S : Nat) (hS : S < USize.size) (hX : X.size = B)
    (hSX : S = 4 * B) (L : LoadsF p) (hL : L.Addr) (s : Src) (hs : L.InRange B s)
    (out : ByteArray) (hr : out.size = S) (ho : out = encode X) :
    loadSrc S hS out hr L.enc B s = encode (tab B fun k ↦ L.src B k s) := by
  have hXs : 4 * X.size < USize.size := by omega
  obtain ⟨hM, hP, hPT, hQ, hQT, hPER, hFS, hLS, hTS⟩ := hL
  have hnext (M : ColsF p) (c : Nat) (hM : M.Addr)
      (hin : ∀ k < B, M.Has (L.next.getD (L.r0 + k) 0) c) :
      nextInto M.enc c L.next L.r0 0 B out =
        encode (tab B fun k ↦ M.at (L.next.getD (L.r0 + k) 0) c) := by
    have := nextInto_encode M X c L.next L.r0 B hXs hM (by omega) hin B 0 (by omega)
    rw [updR_zero, Nat.zero_add, updR_full X B hX] at this
    rw [ho]
    exact this
  cases s with
  | next c => exact hnext L.M c hM hs.1
  | prepCur c => exact copyWords_tab X L.PT B S hS hX hSX hPT (c * B) hs out hr ho
  | prepNext c => exact hnext L.P c hP hs.1
  | permCur c => exact copyWords_tab X L.QT B S hS hX hSX hQT (c * B) hs out hr ho
  | permNext c => exact hnext L.Q c hQ hs.1
  | periodic j =>
    simp only [loadSrc, LoadsF.enc, LoadsF.src, Array.getElem?_map]
    by_cases hj : j < L.PER.size
    · rw [Array.getElem?_eq_getElem hj, Option.map_some]
      have hc := hs hj
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some] at hc
      dsimp only
      rw [copyWords_tab X L.PER[j] B S hS hX hSX (hPER _ (Array.getElem_mem hj)) L.r0 hc out hr ho,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
    · rw [Array.getElem?_eq_none (by omega), Option.map_none]
      dsimp only
      rw [show (0 : UInt32) = (0 : F).val from rfl, fillWord_tab X B S hS hX hSX 0 out hr ho,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
      refine congrArg encode (tab_congr fun k _ ↦ ?_)
      simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_nil,
        Option.getD_none]
  | isFirstRow => exact copyWords_tab X L.FS B S hS hX hSX hFS L.r0 hs out hr ho
  | isLastRow => exact copyWords_tab X L.LS B S hS hX hSX hLS L.r0 hs out hr ho
  | isTransition => exact copyWords_tab X L.TS B S hS hX hSX hTS L.r0 hs out hr ho

theorem Op.word_val (o : Op) (x y : F) : Op.word p o x.val y.val = (o.eval x y).val := by
  cases o
  · exact add_val x y
  · exact sub_val x y
  · exact mul_val x y

theorem constPass_tab (X Ea : Array F) (B S : Nat) (hS : S < USize.size) (hX : X.size = B)
    (hSX : S = 4 * B) (o : Op) (ea : ByteArray) (hEa : ea.size < USize.size)
    (hea : ea = encode Ea) (ra : Bool) (oa : Nat) (haA : Apart ra oa 0 B)
    (hai : oa + B ≤ if ra then X.size else Ea.size) (c : F) (out : ByteArray)
    (hr : out.size = S) (ho : out = encode X) :
    constPass p o ea S hS hEa ra oa c B out hr =
      encode (tab B fun k ↦ o.eval (pick ra X Ea (oa + k)) c) := by
  subst hea
  have hpw (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
      (hf : ∀ x y : F, f x.val y.val = (g x y).val) :
      passWord f (encode Ea) S hS hEa 0 ra oa c.val B out hr =
        encode (tab B fun k ↦ g (pick ra X Ea (oa + k)) c) := by
    rw [passWord_encode f g hf Ea X S hS hEa (by omega) 0 ra oa c B (by omega) haA hai out hr ho,
      updR_full X B hX]
  unfold constPass
  cases o with
  | mul =>
    dsimp only
    split
    · rename_i h2
      rw [passBin_encode (add p) (· + ·) add_val Ea Ea X S hS hEa hEa (by omega) 0 _ _ _ _ B
        (by omega) haA haA hai hai out hr ho, updR_full X B hX]
      refine congrArg encode (tab_congr fun k _ ↦ ?_)
      rw [h2]
      show _ = _ * 2
      rw [mul_two]
    · exact hpw (mul p) (· * ·) mul_val
  | add => exact hpw (add p) (· + ·) add_val
  | sub => exact hpw (sub p) (· - ·) sub_val

theorem binPass_tab (X Ea Eb : Array F) (B S : Nat) (hS : S < USize.size) (hX : X.size = B)
    (hSX : S = 4 * B) (o : Op) (d : Nat) (a b : Opd F) (ea eb : ByteArray)
    (hEa : ea.size < USize.size) (hEb : eb.size < USize.size) (hea : ea = encode Ea)
    (heb : eb = encode Eb) (oa ob : Nat) (hpa : a.Placed (a.isReg (4 + d)) X Ea oa B)
    (hpb : b.Placed (b.isReg (4 + d)) X Eb ob B) (out : ByteArray) (hr : out.size = S)
    (ho : out = encode X) :
    binPass p o d a b ea eb S hS hEa hEb oa ob B out hr = encode (tab B fun k ↦
      o.eval (a.rd (a.isReg (4 + d)) X Ea oa k) (b.rd (b.isReg (4 + d)) X Eb ob k)) := by
  subst hea heb
  have hbin (ha : ∀ x, a ≠ .const x) (hb : ∀ x, b ≠ .const x) :
      passBin (Op.word p o) (encode Ea) (encode Eb) S hS hEa hEb 0 (a.isReg (4 + d)) oa
        (b.isReg (4 + d)) ob B out hr = encode (tab B fun k ↦
          o.eval (a.rd (a.isReg (4 + d)) X Ea oa k) (b.rd (b.isReg (4 + d)) X Eb ob k)) := by
    rw [passBin_encode (Op.word p o) o.eval (Op.word_val o) Ea Eb X S hS hEa hEb (by omega) 0 _ _
      _ _ B (by omega) (hpa ha).1 (hpb hb).1 (hpa ha).2 (hpb hb).2 out hr ho, updR_full X B hX]
    refine congrArg encode (tab_congr fun k _ ↦ ?_)
    cases a with
    | const x => exact absurd rfl (ha x)
    | _ =>
      cases b with
      | const y => exact absurd rfl (hb y)
      | _ => rfl
  have hca (y : F) (ha : ∀ x, a ≠ .const x) :
      constPass p o (encode Ea) S hS hEa (a.isReg (4 + d)) oa y B out hr = encode (tab B fun k ↦
        o.eval (a.rd (a.isReg (4 + d)) X Ea oa k) y) := by
    rw [constPass_tab X Ea B S hS hX hSX o _ hEa rfl _ oa (hpa ha).1 (hpa ha).2 y out hr ho]
    refine congrArg encode (tab_congr fun k _ ↦ ?_)
    cases a with
    | const x => exact absurd rfl (ha x)
    | _ => rfl
  have hcb (x : F) (o' : Op) (hb : ∀ y, b ≠ .const y) (hc : ∀ u v : F, o.eval v u = o'.eval u v) :
      constPass p o' (encode Eb) S hS hEb (b.isReg (4 + d)) ob x B out hr = encode (tab B fun k ↦
        o.eval x (b.rd (b.isReg (4 + d)) X Eb ob k)) := by
    rw [constPass_tab X Eb B S hS hX hSX o' _ hEb rfl _ ob (hpb hb).1 (hpb hb).2 x out hr ho]
    refine congrArg encode (tab_congr fun k _ ↦ ?_)
    rw [hc]
    cases b with
    | const y => exact absurd rfl (hb y)
    | _ => rfl
  have hsub (x : F) (hb : ∀ y, b ≠ .const y) :
      passWord (fun x c ↦ sub p c x) (encode Eb) S hS hEb 0 (b.isReg (4 + d)) ob x.val B out hr =
        encode (tab B fun k ↦ Op.sub.eval x (b.rd (b.isReg (4 + d)) X Eb ob k)) := by
    rw [passWord_encode (fun x c ↦ sub p c x) (fun u c ↦ c - u) (fun u c ↦ sub_val c u) Eb X S hS
      hEb (by omega) 0 _ ob x B (by omega) (hpb hb).1 (hpb hb).2 out hr ho, updR_full X B hX]
    refine congrArg encode (tab_congr fun k _ ↦ ?_)
    cases b with
    | const y => exact absurd rfl (hb y)
    | _ => rfl
  have nr (r : Nat) : ∀ x : F, Opd.reg r ≠ .const x := fun _ ↦ by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  have nc (c : Nat) : ∀ x : F, Opd.cur c ≠ .const x := fun _ ↦ by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  have hcomm (o : Op) (ho : o ≠ .sub) : ∀ u v : F, o.eval v u = o.eval u v := by
    intro u v
    cases o with
    | add => exact add_comm v u
    | mul => exact mul_comm v u
    | sub => exact absurd rfl ho
  cases a with
  | const x =>
    cases b with
    | const y =>
      show fillWord S hS out hr (Op.word p o x.val y.val) B = _
      rw [Op.word_val, fillWord_tab X B S hS hX hSX _ out hr ho]
      rfl
    | reg r =>
      cases o with
      | sub => exact hsub x (nr r)
      | add => exact hcb x .add (nr r) (hcomm .add (by decide))
      | mul => exact hcb x .mul (nr r) (hcomm .mul (by decide))
    | cur c =>
      cases o with
      | sub => exact hsub x (nc c)
      | add => exact hcb x .add (nc c) (hcomm .add (by decide))
      | mul => exact hcb x .mul (nc c) (hcomm .mul (by decide))
  | reg r =>
    cases b with
    | const y => exact hca y (nr r)
    | reg r' => exact hbin (nr r) (nr r')
    | cur c => exact hbin (nr r) (nc c)
  | cur c =>
    cases b with
    | const y => exact hca y (nc c)
    | reg r' => exact hbin (nc c) (nr r')
    | cur c' => exact hbin (nc c) (nc c')

theorem accPass_tab (X Ea : Array F) (B S : Nat) (hS : S < USize.size) (hX : X.size = B)
    (hSX : S = 4 * B) (a : Opd F) (ea : ByteArray) (hEa : ea.size < USize.size)
    (hea : ea = encode Ea) (oa : Nat) (hpa : a.Placed false X Ea oa B) (W : F)
    (out : ByteArray) (hr : out.size = S) (ho : out = encode X) :
    accPass p a ea S hS hEa oa W.val B out hr =
      encode (tab B fun k ↦ X.getD k 0 + a.rd false X Ea oa k * W) := by
  subst hea
  have hf : ∀ x y : F, add p x.val (mul p y.val W.val) = (x + y * W).val := fun x y ↦ by
    rw [mul_val, add_val]
  unfold accPass
  split
  · rename_i c
    rw [passWord_encode (fun x c ↦ add p x (mul p c W.val)) (fun x c ↦ x + c * W) hf Ea X S hS
      hEa (by omega) 0 true 0 c B (by omega) (fun _ ↦ Or.inl rfl) (by simp only [ite_true]; omega)
      out hr ho, updR_full X B hX]
    simp only [pick, ite_true, Nat.zero_add, Opd.rd]
  · rename_i hc
    have hc' : ∀ x, a ≠ .const x := fun x e ↦ hc x e
    rw [passBin_encode (fun x y ↦ add p x (mul p y W.val)) (fun x y ↦ x + y * W) hf Ea Ea X S hS
      hEa hEa (by omega) 0 true 0 false oa B (by omega) (fun _ ↦ Or.inl rfl) (hpa hc').1
      (by simp only [ite_true]; omega) (hpa hc').2 out hr ho, updR_full X B hX]
    refine congrArg encode (tab_congr fun k _ ↦ ?_)
    cases a with
    | const x => exact absurd rfl (hc' x)
    | _ => simp only [pick, ite_true, Nat.zero_add, Opd.rd]

/-! ### Instructions on a block of rows -/

/-- Row `i` of a block of `B` rows as a program reads it: the trace's current rows in `V` (column
`c` from word `cb + c · cs`), the loads, the scalars and the weights' coordinates. -/
def blockCtx (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) (B i : Nat) : Ctx F :=
  ⟨fun c ↦ V.getD (cb + c * cs + i) 0, L.src B i, fun k ↦ SC.getD k 0,
    fun w j ↦ WT.getD (4 * w + j) 0⟩

/-- Buffer `s` of a row's state: accumulator `s` below four, register `s - 4` from four. -/
def St.slot (st : St F) (s : Nat) : F := if s < 4 then st.acc s else st.reg (s - 4)

/-- A row's state with buffer `s` set to `x`. -/
def St.setSlot (st : St F) (s : Nat) (x : F) : St F :=
  if s < 4 then { st with acc := Function.update st.acc s x }
  else { st with reg := Function.update st.reg (s - 4) x }

theorem St.slot_setSlot (st : St F) (s t : Nat) (x : F) :
    (st.setSlot s x).slot t = if t = s then x else st.slot t := by
  unfold St.setSlot St.slot
  by_cases hs : s < 4 <;> by_cases ht : t < 4
  · simp only [hs, ht, ite_true, Function.update_apply]
  · simp only [hs, ht, ite_true, ite_false, show t ≠ s by omega]
  · simp only [hs, ht, ite_true, ite_false, show t ≠ s by omega]
  · simp only [hs, ht, ite_false, Function.update_apply]
    by_cases e : t = s
    · simp only [e, ite_true]
    · simp only [e, ite_false, show t - 4 ≠ s - 4 by omega]

/-- The registers hold `B` rows' run states: buffer `s` the rows' `s`-th (`St.slot`). -/
def BlockRel {S : Nat} (B nregs : Nat) (regs : Regs S) (sts : Nat → St F) : Prop :=
  regs.size = 4 + nregs ∧ ∀ s < 4 + nregs, regBuf regs s = encode (tab B fun i ↦ (sts i).slot s)

theorem regBuf_getElem {S : Nat} (regs : Regs S) (i : Nat) (hi : i < regs.size) :
    regBuf regs i = regs[i].1 := by
  unfold regBuf
  rw [Array.getElem?_eq_getElem hi]

theorem size_modReg {S : Nat} (regs : Regs S) (i : Nat)
    (f : (b : ByteArray) → b.size = S → ByteArray) (hf) : (modReg regs i f hf).size = regs.size :=
  Array.size_modify

theorem regBuf_modReg {S : Nat} (regs : Regs S) (i : Nat) (hi : i < regs.size)
    (f : (b : ByteArray) → b.size = S → ByteArray) (hf) (s : Nat) :
    regBuf (modReg regs i f hf) s = if s = i then f regs[i].1 regs[i].2 else regBuf regs s := by
  unfold regBuf modReg
  rw [Array.getElem?_modify]
  by_cases e : s = i
  · subst e
    simp only [ite_true, Array.getElem?_eq_getElem hi, Option.map_some]
  · simp only [Ne.symm e, e, ite_false]

theorem BlockRel.congr {S B nregs : Nat} {regs : Regs S} {sts sts' : Nat → St F}
    (h : BlockRel B nregs regs sts)
    (e : ∀ i < B, ∀ s < 4 + nregs, (sts i).slot s = (sts' i).slot s) :
    BlockRel B nregs regs sts' :=
  ⟨h.1, fun s hs ↦ by rw [h.2 s hs, tab_congr fun i hi ↦ e i hi s hs]⟩

theorem BlockRel.size_eq {S B nregs : Nat} {regs : Regs S} {sts : Nat → St F}
    (h : BlockRel B nregs regs sts) : S = 4 * B := by
  have h0 := h.2 0 (by omega)
  have hl : 0 < regs.size := by rw [h.1]; omega
  rw [regBuf_getElem regs 0 hl] at h0
  have := regs[0].2
  rw [h0, size_encode_fields, size_tab] at this
  exact this.symm

/-- Overwriting buffer `s` with the rows' `G` sets every row's `s`-th. -/
theorem BlockRel.set {S B nregs : Nat} {regs : Regs S} {sts : Nat → St F}
    (h : BlockRel B nregs regs sts) (s : Nat) (hs : s < 4 + nregs)
    (f : (b : ByteArray) → b.size = S → ByteArray) (hf) (G : Nat → F)
    (hG : ∀ b hb, b = encode (tab B fun i ↦ (sts i).slot s) → f b hb = encode (tab B G)) :
    BlockRel B nregs (modReg regs s f hf) fun i ↦ (sts i).setSlot s (G i) := by
  have hsl : s < regs.size := by rw [h.1]; exact hs
  refine ⟨by rw [size_modReg, h.1], fun t ht ↦ ?_⟩
  rw [regBuf_modReg regs s hsl]
  split
  · rename_i e
    subst e
    rw [hG _ _ (by rw [← regBuf_getElem regs t hsl]; exact h.2 t ht)]
    refine congrArg encode (tab_congr fun i _ ↦ ?_)
    rw [St.slot_setSlot, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · rename_i e
    rw [h.2 t ht]
    refine congrArg encode (tab_congr fun i _ ↦ ?_)
    rw [St.slot_setSlot, ite_eq_right_of_eq_false _ _ (eq_false e)]

/-- An operand's words lie in their buffer: a register below `nregs`, a column in the view. -/
def Opd.InRange (V : Array F) (cb cs B nregs : Nat) : Opd F → Prop
  | .reg r => r < nregs
  | .cur c => cb + c * cs + B ≤ V.size
  | .const _ => True

/-- An instruction's registers are below `nregs` and its operands and loads in range. -/
def Instr.InRange (V : Array F) (cb cs : Nat) (L : LoadsF p) (B nregs : Nat) :
    Instr F → Prop
  | .load d s => d < nregs ∧ L.InRange B s
  | .scalar d _ => d < nregs
  | .bin _ d a b => d < nregs ∧ a.InRange V cb cs B nregs ∧ b.InRange V cb cs B nregs
  | .acc a _ => a.InRange V cb cs B nregs

/-- The array an operand of an instruction writing buffer `t` reads besides that buffer
(`Opd.buf`): another register's rows, or the view's. -/
def Opd.arr (t B : Nat) (V : Array F) (sts : Nat → St F) : Opd F → Array F
  | .reg r => if 4 + r == t then #[] else tab B fun i ↦ (sts i).reg r
  | _ => V

theorem Opd.buf_eq {S B nregs : Nat} {regs : Regs S} {sts : Nat → St F} {V : Array F}
    {cb cs : Nat} (h : BlockRel B nregs regs sts) (a : Opd F) (ha : a.InRange V cb cs B nregs)
    (t : Nat) : a.buf t regs ⟨encode V, cb, cs⟩ = encode (a.arr t B V sts) := by
  cases a with
  | reg r =>
    simp only [Opd.buf, Opd.arr]
    split
    · rfl
    · rw [h.2 (4 + r) (by simp only [Opd.InRange] at ha; omega)]
      refine congrArg encode (tab_congr fun i _ ↦ ?_)
      simp only [St.slot, show ¬4 + r < 4 by omega, ite_false, Nat.add_sub_cancel_left]
  | cur c => rfl
  | const x => rfl

/-- An operand in range of an instruction writing buffer `t` reads every row's value. -/
theorem Opd.rd_arr {V : Array F} {cb cs : Nat} {L : LoadsF p} {SC WT : Array F} {B : Nat}
    {sts : Nat → St F} (a : Opd F) (t : Nat) (self : Bool) (hself : self = true → self = a.isReg t)
    (hsf : self = false → a.isReg t = false) (k : Nat) (hk : k < B) :
    a.rd self (tab B fun i ↦ (sts i).slot t) (a.arr t B V sts) (a.off ⟨encode V, cb, cs⟩) k =
      a.val (blockCtx V cb cs L SC WT B k) (sts k) := by
  cases a with
  | reg r =>
    simp only [Opd.rd, Opd.off, Opd.arr, Opd.val, pick, Nat.zero_add]
    by_cases e : (4 + r == t) = true
    · have hs : self = true := by
        cases self
        · have := hsf rfl; simp only [Opd.isReg] at this; rw [this] at e; exact absurd e (by decide)
        · rfl
      rw [hs, ite_eq_left rfl, getD_tab _ _ _ hk]
      have := beq_iff_eq.mp e
      subst this
      simp only [St.slot, show ¬4 + r < 4 by omega, ite_false, Nat.add_sub_cancel_left]
    · have hs : self = false := by
        cases self
        · rfl
        · have := hself rfl; simp only [Opd.isReg] at this; rw [← this] at e; exact absurd rfl e
      rw [hs, ite_eq_right (by decide), ite_eq_right e, getD_tab _ _ _ hk]
  | cur c =>
    simp only [Opd.rd, Opd.off, Opd.arr, Opd.val, pick, blockCtx]
    cases self
    · rfl
    · have := hself rfl; simp only [Opd.isReg] at this; exact absurd this (by decide)
  | const x => rfl

/-- An operand in range of an instruction writing buffer `t` is placed in its buffer. -/
theorem Opd.placed_arr {V : Array F} {cb cs B nregs : Nat} {sts : Nat → St F} (a : Opd F)
    (ha : a.InRange V cb cs B nregs) (t : Nat) (self : Bool)
    (hself : self = true → self = a.isReg t) (hsf : self = false → a.isReg t = false) :
    a.Placed self (tab B fun i ↦ (sts i).slot t) (a.arr t B V sts) (a.off ⟨encode V, cb, cs⟩)
      B := by
  intro hc
  cases a with
  | reg r =>
    simp only [Opd.off]
    refine ⟨fun _ ↦ Or.inl rfl, ?_⟩
    cases self
    · have := hsf rfl
      simp only [Opd.isReg] at this
      simp only [Bool.false_eq_true, ite_false, Opd.arr, this, size_tab, Nat.zero_add, le_refl]
    · simp only [ite_true, size_tab, Nat.zero_add, le_refl]
  | cur c =>
    cases self
    · exact ⟨fun h ↦ absurd h (by decide), by
        simpa only [Opd.off, Bool.false_eq_true, ite_false, Opd.arr, Opd.InRange] using ha⟩
    · have := hself rfl; simp only [Opd.isReg] at this; exact absurd this (by decide)
  | const x => exact absurd rfl (hc x)

theorem Opd.size_arr {V : Array F} {B : Nat} {sts : Nat → St F} (hB : 4 * B < USize.size)
    (hV : 4 * V.size < USize.size) (a : Opd F) (t : Nat) :
    4 * (a.arr t B V sts).size < USize.size := by
  cases a with
  | reg r =>
    simp only [Opd.arr]
    split
    · simp only [List.size_toArray, List.length_nil, Nat.mul_zero]; omega
    · rw [size_tab]; exact hB
  | cur c => exact hV
  | const x => exact hV


theorem St.setSlot_reg (st : St F) (d : Nat) (x : F) :
    st.setSlot (4 + d) x = { st with reg := Function.update st.reg d x } := by
  simp only [St.setSlot, show ¬4 + d < 4 by omega, ite_false, Nat.add_sub_cancel_left]

theorem BlockRel.congr' {S B nregs : Nat} {regs : Regs S} {sts sts' : Nat → St F}
    (h : BlockRel B nregs regs sts) (e : ∀ i < B, sts i = sts' i) : BlockRel B nregs regs sts' :=
  h.congr fun i hi _ _ ↦ by rw [e i hi]

theorem Opd.rd_false (X X' E : Array F) (o : Nat) (a : Opd F) (k : Nat) :
    a.rd false X E o k = a.rd false X' E o k := by
  cases a <;> rfl

/-- One accumulator's pass: accumulator `j` of every row plus the operand times `W`. -/
theorem BlockRel.accStep {S B nregs : Nat} {regs : Regs S} {sts : Nat → St F}
    (h : BlockRel B nregs regs sts) (hS : S < USize.size) (j : Nat) (hj : j < 4) (a : Opd F)
    (Ea : Array F) (ea : ByteArray) (hEa : ea.size < USize.size) (hea : ea = encode Ea)
    (oa : Nat) (hpa : ∀ X, a.Placed false X Ea oa B) (W : F) (wv : UInt32) (hw : wv = W.val)
    (A : Nat → F) (hA : ∀ X, ∀ k < B, a.rd false X Ea oa k = A k) :
    BlockRel B nregs (modReg regs j (fun r h ↦ accPass p a ea S hS hEa oa wv B r h)
      (fun _ _ ↦ size_accPass ..)) fun i ↦ (sts i).setSlot j ((sts i).slot j + A i * W) := by
  subst hw
  refine h.set j (by omega) _ _ _ fun b hb e ↦ ?_
  rw [accPass_tab (tab B fun i ↦ (sts i).slot j) Ea B S hS (size_tab ..) h.size_eq a ea hEa hea
    oa (hpa _) W b hb e]
  exact congrArg encode (tab_congr fun k hk ↦ by rw [getD_tab _ _ _ hk, hA _ k hk])

/-- **An instruction on a block** of `B` rows in range is the instruction on every row's values
(`blockCtx`). -/
theorem execBlock_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F)
    (B nregs S : Nat) (hS : S < USize.size) (hE : (encode V).size < USize.size) (regs : Regs S)
    (sts : Nat → St F) (h : BlockRel B nregs regs sts) (hL : L.Addr)
    (ins : Instr F)
    (hin : ins.InRange V cb cs L B nregs) :
    BlockRel B nregs (execBlock p ⟨encode V, cb, cs⟩ L.enc SC WT B S hS hE regs ins) fun i ↦
      ins.exec (fieldMachine (blockCtx V cb cs L SC WT B i)) (sts i) := by
  have hSX := h.size_eq
  have hB : 4 * B < USize.size := by omega
  have hV : 4 * V.size < USize.size := by rw [size_encode_fields] at hE; exact hE
  have hX (t : Nat) : (tab B fun i ↦ (sts i).slot t).size = B := size_tab ..
  cases ins with
  | load d src =>
    obtain ⟨hd, hs⟩ := hin
    refine (h.set (4 + d) (by omega) _ (fun _ _ ↦ size_loadSrc ..) (fun k ↦ L.src B k src)
      fun b hb e ↦
      loadSrc_tab _ B S hS (hX _) hSX L hL src hs b hb e).congr' fun i _ ↦ ?_
    rw [St.setSlot_reg, exec_load]
    rfl
  | scalar d k =>
    have hd : d < nregs := hin
    refine (h.set (4 + d) (by omega) _ (fun _ _ ↦ size_fillWord ..) (fun _ ↦ SC.getD k 0)
      fun b hb e ↦ ?_).congr' fun i _ ↦ ?_
    · exact fillWord_tab _ B S hS (hX _) hSX _ b hb e
    · rw [St.setSlot_reg, exec_scalar]
      rfl
  | bin o d a b =>
    obtain ⟨hd, ha, hb⟩ := hin
    refine (h.set (4 + d) (by omega) _ (fun _ _ ↦ size_binPass ..) (fun k ↦ o.eval
      (a.val (blockCtx V cb cs L SC WT B k) (sts k))
      (b.val (blockCtx V cb cs L SC WT B k) (sts k))) fun b' hb' e ↦ ?_).congr' fun i _ ↦ ?_
    · rw [binPass_tab _ (a.arr (4 + d) B V sts) (b.arr (4 + d) B V sts) B S hS (hX _) hSX o d a b
        _ _ _ _ (Opd.buf_eq h a ha _) (Opd.buf_eq h b hb _) _ _
        (Opd.placed_arr a ha _ _ (fun _ ↦ rfl) id) (Opd.placed_arr b hb _ _ (fun _ ↦ rfl) id)
        b' hb' e]
      exact congrArg encode (tab_congr fun k hk ↦ by
        rw [Opd.rd_arr a (4 + d) _ (fun _ ↦ rfl) id k hk,
          Opd.rd_arr b (4 + d) _ (fun _ ↦ rfl) id k hk])
    · rw [St.setSlot_reg, exec_bin]
  | acc a w =>
    have ha : a.InRange V cb cs B nregs := hin
    have hsf : a.isReg 0 = false := by
      cases a with
      | reg r => exact beq_eq_false_iff_ne.mpr (by omega)
      | _ => rfl
    have hpa (X : Array F) : a.Placed false X (a.arr 0 B V sts) (a.off ⟨encode V, cb, cs⟩) B :=
      fun hc ↦ by
        have := Opd.placed_arr (sts := sts) a ha 0 false (fun h ↦ absurd h (by decide))
          (fun _ ↦ hsf) hc
        simpa only [Bool.false_eq_true, ite_false] using this
    have hA (X : Array F) (k : Nat) (hk : k < B) :
        a.rd false X (a.arr 0 B V sts) (a.off ⟨encode V, cb, cs⟩) k =
          a.val (blockCtx V cb cs L SC WT B k) (sts k) := by
      rw [Opd.rd_false X (tab B fun i ↦ (sts i).slot 0)]
      exact Opd.rd_arr a 0 false (fun h ↦ absurd h (by decide)) (fun _ ↦ hsf) k hk
    have hw (j : Nat) : (WT.getD (4 * w + j) 0).val = (WT.getD (4 * w + j) 0).val := rfl
    have hea := Opd.buf_eq h a ha 0
    have hEa := size_opdBuf 0 regs ⟨encode V, cb, cs⟩ a hS hE
    have h0 := h.accStep hS 0 (by decide) a _ _ hEa hea _ hpa _ _ (hw 0) _ fun X k hk ↦ hA X k hk
    have h1 := h0.accStep hS 1 (by decide) a _ _ hEa hea _ hpa _ _ (hw 1) _ fun X k hk ↦ hA X k hk
    have h2 := h1.accStep hS 2 (by decide) a _ _ hEa hea _ hpa _ _ (hw 2) _ fun X k hk ↦ hA X k hk
    have h3 := h2.accStep hS 3 (by decide) a _ _ hEa hea _ hpa _ _ (hw 3) _ fun X k hk ↦ hA X k hk
    refine h3.congr fun i _ s _ ↦ ?_
    rw [exec_acc]
    simp only [St.slot_setSlot]
    by_cases s3 : s = 3
    · subst s3; simp only [St.slot, ite_true, show (3 : Nat) ≠ 2 by decide,
        show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide, ite_false, show 3 < 4 by decide]
      rfl
    by_cases s2 : s = 2
    · subst s2; simp only [St.slot, ite_true, show (2 : Nat) ≠ 3 by decide,
        show (2 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 0 by decide, ite_false, show 2 < 4 by decide]
      rfl
    by_cases s1 : s = 1
    · subst s1; simp only [St.slot, ite_true, show (1 : Nat) ≠ 3 by decide,
        show (1 : Nat) ≠ 2 by decide, show (1 : Nat) ≠ 0 by decide, ite_false, show 1 < 4 by decide]
      rfl
    by_cases s0 : s = 0
    · subst s0; simp only [St.slot, ite_true, show (0 : Nat) ≠ 3 by decide,
        show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 1 by decide, ite_false, show 0 < 4 by decide]
      rfl
    simp only [s0, s1, s2, s3, ite_false, St.slot, show ¬s < 4 by omega]

/-- **A program on a block** of `B` rows in range runs the program on every row's values
(`blockCtx`). -/
theorem runBlock_rel (code : Array (Instr F)) (V : Array F) (cb cs : Nat) (L : LoadsF p)
    (SC WT : Array F) (B nregs S : Nat) (hS : S < USize.size) (regs : Regs S)
    (sts : Nat → St F) (h : BlockRel B nregs regs sts) (hV : 4 * V.size < USize.size)
    (hL : L.Addr)
    (hcode : ∀ ins ∈ code, ins.InRange V cb cs L B nregs) :
    BlockRel B nregs (runBlock p code ⟨encode V, cb, cs⟩ L.enc SC WT B hS regs)
      fun i ↦ run (fieldMachine (blockCtx V cb cs L SC WT B i)) code (sts i) := by
  have hE : (encode V).size < USize.size := by rw [size_encode_fields]; exact hV
  unfold runBlock
  rw [dite_eq_left hE]
  simp only [run, ← Array.foldl_toList]
  have hcode' : ∀ ins ∈ code.toList, ins.InRange V cb cs L B nregs := fun i hi ↦
    hcode i (Array.mem_toList_iff.mp hi)
  generalize code.toList = l at hcode'
  induction l generalizing regs sts with
  | nil => exact h
  | cons ins l ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (execBlock_rel V cb cs L SC WT B nregs S hS hE regs sts h hL ins
      (hcode' ins List.mem_cons_self)) fun i hi ↦ hcode' i (List.mem_cons_of_mem _ hi)

/-- Clearing the accumulators clears every row's. -/
theorem clearAcc_rel {S B nregs : Nat} (hS : S < USize.size) (regs : Regs S)
    (sts : Nat → St F) (h : BlockRel B nregs regs sts) :
    BlockRel B nregs (clearAcc hS B regs) fun i ↦ { sts i with acc := fun _ ↦ 0 } := by
  have hSX := h.size_eq
  have hz {regs : Regs S} {sts : Nat → St F} (h : BlockRel B nregs regs sts) (j : Nat)
      (hj : j < 4) : BlockRel B nregs (modReg regs j (fun r h ↦ fillWord S hS r h 0 B)
        (fun _ _ ↦ size_fillWord ..)) fun i ↦ (sts i).setSlot j 0 :=
    h.set j (by omega) _ _ _ fun b hb e ↦ fillWord_tab _ B S hS (size_tab ..) hSX 0 b hb e
  refine (hz (hz (hz (hz h 0 (by decide)) 1 (by decide)) 2 (by decide)) 3 (by decide)).congr
    fun i _ s _ ↦ ?_
  simp only [St.slot_setSlot]
  by_cases s4 : s < 4
  · have : s = 3 ∨ s = 2 ∨ s = 1 ∨ s = 0 := by omega
    rcases this with e | e | e | e <;> subst e <;>
      simp only [St.slot, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceLT]
  · simp only [show s ≠ 3 by omega, show s ≠ 2 by omega, show s ≠ 1 by omega,
      show s ≠ 0 by omega, ite_false, St.slot, s4]

/-- Zero registers hold zero run states. -/
theorem blockRel_zeros (B nregs : Nat) (h : (zeroWords B).size = 4 * B) :
    BlockRel B nregs (Array.replicate (4 + nregs) ⟨zeroWords B, h⟩ : Regs (4 * B))
      fun _ ↦ (⟨fun _ ↦ 0, fun _ ↦ 0⟩ : St F) := by
  refine ⟨Array.size_replicate .., fun s hs ↦ ?_⟩
  rw [regBuf_getElem _ _ (by rw [Array.size_replicate]; exact hs)]
  simp only [Array.getElem_replicate]
  rw [Words.zeroWords_eq (p := p)]
  refine congrArg encode (Array.ext (by simp only [Array.size_replicate, size_tab])
    fun i h1 h2 ↦ ?_)
  simp only [Array.getElem_replicate, tab, Array.getElem_ofFn, St.slot]
  split <;> rfl

/-- The registers of a block of `B` rows are encoded run states. -/
def Encoded {S : Nat} (B nregs : Nat) (regs : Regs S) : Prop :=
  ∃ sts : Nat → St F, BlockRel B nregs regs sts

/-- **A program accumulating every row** on a block of `B` rows, from cleared accumulators and any
encoded registers: the accumulators hold its rows' accumulations. -/
theorem runBlock_acc (code : Array (Instr F)) (nregs : Nat) (V : Array F) (cb cs : Nat)
    (L : LoadsF p) (SC WT : Array F) (B S : Nat) (hS : S < USize.size) (regs : Regs S)
    (h : Encoded (p := p) B nregs regs) (hV : 4 * V.size < USize.size) (hL : L.Addr)
    (hcode : ∀ ins ∈ code, ins.InRange V cb cs L B nregs) (Q : Nat → Nat → F)
    (hQ : ∀ i < B, ∀ st0 : St F, st0.acc = (fun _ ↦ 0) → ∀ j < 4,
      (run (fieldMachine (blockCtx V cb cs L SC WT B i)) code st0).acc j = Q i j) :
    let regs' := runBlock p code ⟨encode V, cb, cs⟩ L.enc SC WT B hS
      (clearAcc hS B regs)
    Encoded (p := p) B nregs regs' ∧ ∀ j < 4, regBuf regs' j = encode (tab B fun i ↦ Q i j) := by
  obtain ⟨sts, h⟩ := h
  have h' := runBlock_rel code V cb cs L SC WT B nregs S hS _ _ (clearAcc_rel hS regs sts h) hV hL
    hcode
  refine ⟨⟨_, h'⟩, fun j hj ↦ ?_⟩
  rw [h'.2 j (by omega)]
  refine congrArg encode (tab_congr fun i hi ↦ ?_)
  simp only [St.slot, hj, ite_true]
  exact hQ i hi _ rfl j hj

theorem wordsAt_encode (A : Array F) (o B : Nat) :
    wordsAt (encode A) o B = encode (A.extract o (o + B)) := by
  unfold wordsAt ByteArray.extract
  have := CompPoly.PackedRepr.copySlice_encode A #[] o B
  simp only [CompPoly.PackedRepr.encode_empty, ByteArray.size_empty, Array.empty_append] at this
  rw [show 4 * (o + B) - 4 * o = 4 * B by omega]
  exact this

theorem extract_tab (f : Nat → F) (o B N : Nat) (h : o + B ≤ N) :
    (tab N f).extract o (o + B) = tab B fun i ↦ f (o + i) := by
  apply Array.ext (by simp only [Array.size_extract, size_tab]; omega)
  intro i h1 h2
  simp only [Array.getElem_extract, tab, Array.getElem_ofFn]

/-- **The outputs' words** on a block after its run: every row's values. -/
theorem outWords_rel {S B nregs : Nat} (outs : Array (Opd F)) (V : Array F) (cb cs : Nat)
    (L : LoadsF p) (SC WT : Array F) (regs : Regs S) (sts : Nat → St F)
    (h : BlockRel B nregs regs sts) (hB : 4 * B < USize.size)
    (hout : ∀ o ∈ outs, o.InRange V cb cs B nregs) :
    outWords p outs ⟨encode V, cb, cs⟩ regs B = outs.map fun o ↦
      encode (tab B fun i ↦ o.val (blockCtx V cb cs L SC WT B i) (sts i)) := by
  unfold outWords
  refine Array.map_congr_left fun o ho ↦ ?_
  have hin := hout o ho
  cases o with
  | reg r =>
    simp only [Opd.InRange] at hin
    show wordsAt (regBuf regs (4 + r)) 0 B = _
    rw [h.2 (4 + r) (by omega), wordsAt_encode, extract_tab _ 0 B B (by omega)]
    refine congrArg encode (tab_congr fun i _ ↦ ?_)
    simp only [St.slot, show ¬4 + r < 4 by omega, ite_false, Nat.add_sub_cancel_left,
      Nat.zero_add, Opd.val]
  | cur c =>
    simp only [Opd.InRange] at hin
    show wordsAt (encode V) (cb + c * cs) B = _
    rw [wordsAt_encode]
    refine congrArg encode (Array.ext (by simp only [Array.size_extract, size_tab]; omega)
      fun i h1 h2 ↦ ?_)
    simp only [Array.getElem_extract, tab, Array.getElem_ofFn, Opd.val, blockCtx]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by
      simp only [Array.size_extract] at h1; omega), Option.getD_some]
  | const x =>
    show Words.replicateWord x.val B = _
    rw [Words.replicateWord_encode _ _ hB]
    refine congrArg encode (Array.ext (by simp only [Array.size_replicate, size_tab])
      fun i h1 h2 ↦ ?_)
    simp only [Array.getElem_replicate, tab, Array.getElem_ofFn]
    rfl

/-- An instruction with registers below `nregs` and leaves in range is in range. -/
theorem Instr.inRange_of {V : Array F} {cb cs : Nat} {L : LoadsF p} {B nregs : Nat}
    {cq : Nat → Prop} {lq : Src → Prop} (hc : ∀ c, cq c → cb + c * cs + B ≤ V.size)
    (hl : ∀ s, lq s → L.InRange B s) (ins : Instr F) (hreg : ins.RegsLt nregs)
    (hleaf : ins.LeafOk cq lq) : ins.InRange V cb cs L B nregs := by
  have hopd (a : Opd F) (h1 : a.RegsLt nregs) (h2 : a.LeafOk cq) :
      a.InRange V cb cs B nregs := by
    cases a with
    | reg r => exact h1
    | cur c => exact hc c h2
    | const x => trivial
  cases ins with
  | load d s => exact ⟨hreg, hl s hleaf⟩
  | scalar d k => exact hreg
  | bin o d a b => exact ⟨hreg.1, hopd a hreg.2.1 hleaf.1, hopd b hreg.2.2 hleaf.2⟩
  | acc a w => exact hopd a hreg hleaf

end CompStark.Stark.Prog
