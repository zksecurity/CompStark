/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgGroup
public import CompStark.Stark.Fast.ProgWords

/-! # Programs on groups of rows compute the field's values

On encoded field arrays, a kernel of the group machine (`CompStark/Stark/ProgGroup.lean`) overwrites
a range of the state, sixteen words at a time, with the operation on its operands' words, its
operands' windows checked once (`pass_upd`, `lanes_upd`), or adds an operand times the weights to
the accumulators (`accS_upd` and its kin). So an instruction on a group of `B` rows is the
instruction on each row's values (`execGroup_rel`, on the rows' values `blockCtx`), and so is a
program (`runGroup_rel`): the group machine simulates `B` runs on the field.
-/

@[expose] public section
namespace CompStark.Stark.Prog
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul add_val sub_val mul_val reduceOnce_eq sub_eq
  size_encode_fields splice getD_splice size_splice lit16 getD_lit16 size_lit16
  array_eq_of_getD)
open CompPoly.CPolynomial.NTTFast.Packed.Native (Buf read write16U toNat_usize_le
  usize_add_toNat_of_le)
open Montgomery.Native32
open Montgomery.Native32.Words (tab size_tab tab_congr getD_tab)

variable {p : ℕ} [P : Mont32Field p] {na : Nat}

local notation "F" => FastField p

/-! ### Machine words -/

theorem toUSize_toNat {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n :=
  USize.toNat_ofNat_of_lt' h

theorem usize_add_toNat {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, hsz, Nat.mod_eq_of_lt h]

theorem usize_mul_toNat {x y : USize} (h : x.toNat * y.toNat < USize.size) :
    (x * y).toNat = x.toNat * y.toNat := by
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_mul, hsz, Nat.mod_eq_of_lt h]

theorem usize_size_le : 4294967296 ≤ USize.size := USize.le_size

theorem usize_numeral (n : Nat) (h : n < 4294967296) : (OfNat.ofNat n : USize).toNat = n := by
  rw [USize.toNat_ofNat]; exact Nat.mod_eq_of_lt (lt_of_lt_of_le h usize_size_le)

/-- A store in the window of a buffer that fits machine indices is the checked store. -/
theorem st16_eq (s : ByteArray) (i : USize) (h : Win s i) (hs : s.size < USize.size)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    st16 s i h v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      write16U s i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 := by
  have hb := win_bytes h
  have h64 : (4 * (16 : UInt8).toNat).toUSize.toNat = 64 :=
    toUSize_toNat (Nat.lt_of_lt_of_le (by decide) usize_size_le)
  have hu : s.usize.toNat = s.size := by rw [ByteArray.usize, toUSize_toNat hs]
  have hn : (i * 4 + (4 * (16 : UInt8).toNat).toUSize).toNat = (i * 4).toNat + 64 := by
    rw [usize_add_toNat (by rw [h64]; omega), h64]
  have c1 : i * 4 ≤ i * 4 + (4 * (16 : UInt8).toNat).toUSize :=
    USize.le_iff_toNat_le.mpr (by rw [hn]; omega)
  have c2 : i * 4 + (4 * (16 : UInt8).toNat).toUSize ≤ s.usize :=
    USize.le_iff_toNat_le.mpr (by rw [hn, hu]; omega)
  unfold st16 write16U CompPoly.CPolynomial.NTTFast.Packed.Native.storeWords
  rw [dite_eq_right (by decide), dite_eq_left ⟨c1, c2⟩]
  rfl

/-- A word read from an encoded array is its element. -/
theorem ld_encode (Y : Array F) (i : USize) (h : Win (encode Y) i) (k : Nat) (hk : k ≤ 15) :
    ld (encode Y) i h k hk = (Y.getD (i.toNat + k) 0).val := by
  unfold ld
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.ugetUInt32LE_eq, (win_off h k hk).1,
    CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val,
    CompPoly.PackedRepr.getUInt32LE!_encode,
    CompPoly.CPolynomial.NTTFast.Packed.getD_map_val]

/-! ### Montgomery multiplication -/

/-- `mulM` is `mul`: the quotient's word product is the low word of the 64-bit product. -/
theorem mulM_eq (x y : UInt32) : mulM p x y = mul p x y := by
  have hlow : (x.toUInt64 * y.toUInt64).toUInt32 = x * y := by
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
      UInt32.toNat_mul, Nat.mod_mod_of_dvd _ (by decide)]
  simp only [mulM, CompPoly.CPolynomial.NTTFast.Packed.mul, hlow]

/-- `mulM` is the carrier's verified multiplication. -/
theorem mulM_val (x y : F) : mulM p x.val y.val = (x * y).val := by
  rw [mulM_eq, mul_val]

theorem Op.wordG_val (o : Op) (x y : F) : Op.wordG p o x.val y.val = (o.eval x y).val := by
  cases o
  · exact add_val x y
  · exact sub_val x y
  · exact mulM_val x y

/-! ### Passes over a group -/

theorem usize16 (m : Nat) (h : 16 * (m + 1) < USize.size) :
    (16 * m).toUSize + 16 = (16 * (m + 1)).toUSize := by
  apply USize.toNat_inj.mp
  have h16 : (16 : USize).toNat = 16 := usize_numeral 16 (by decide)
  rw [usize_add_toNat (by rw [h16, toUSize_toNat (by omega)]; omega), h16, toUSize_toNat (by omega),
    toUSize_toNat h]
  ring

/-- **A pass over a group**: steps taking a buffer of `n` bytes through `Z 0, Z 1, …, Z nm`. -/
theorem groupsW_states {n : Nat} (nm : Nat) (hnm : 16 * nm < USize.size)
    (step : Buf n → (o : USize) → o.toNat + 16 ≤ 16 * nm → Buf n) (Z : Nat → ByteArray)
    (hZ : ∀ m, (Z m).size = n)
    (hstep : ∀ m < nm, ∀ ho, (step ⟨Z m, hZ m⟩ (16 * m).toUSize ho).1 = Z (m + 1))
    (s0 : Buf n) (h0 : s0.1 = Z 0) : (runW nm hnm step s0).1 = Z nm := by
  suffices h : ∀ j m (o : USize), o.toNat = 16 * m → m + j = nm → ∀ ho,
      (groupsW nm hnm step j ⟨Z m, hZ m⟩ o ho).1 = Z nm by
    obtain ⟨v, hv⟩ := s0
    dsimp only at h0
    subst h0
    exact h nm 0 0 (by rw [USize.toNat_zero]) (Nat.zero_add _) _
  intro j
  induction j with
  | zero =>
    intro m o _ hm _
    rw [Nat.add_zero] at hm
    subst hm
    rfl
  | succ j ih =>
    intro m o hom hmj ho
    have hm : m < nm := by omega
    obtain rfl : o = (16 * m).toUSize :=
      USize.toNat_inj.mp (by rw [hom, toUSize_toNat (by omega)])
    rw [groupsW, show step ⟨Z m, hZ m⟩ (16 * m).toUSize (by omega) = ⟨Z (m + 1), hZ (m + 1)⟩ from
      Subtype.ext (hstep m hm _)]
    exact ih (m + 1) _ (by rw [usize16 m (by omega), toUSize_toNat (by omega)]) (by omega) _

/-- Sixteen lanes of `f` on the operands' words: the next sixteen of `updR`. -/
theorem lanes_upd (f : UInt32 → UInt32 → UInt32) (X : Array F) (od m : Nat) (G : Nat → F)
    (x y : (k : Nat) → k ≤ 15 → UInt32) (xv yv : Nat → F) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val)
    (hx : ∀ k hk, x k hk = (xv k).val) (hy : ∀ k hk, y k hk = (yv k).val)
    (hG : ∀ t < 16, g (xv t) (yv t) = G (m + t)) (d : USize) (hd : d.toNat = od + m)
    (hX : 4 * X.size < USize.size) (hr : od + m + 16 ≤ X.size) :
    lanes16 f x y (encode (updR X od m G)) d = encode (updR X od (m + 16) G) := by
  rw [lanes16_encode f g hf x y xv yv hx hy _ d (by rw [size_updR]; exact hX)
    (by rw [size_updR, hd]; exact hr), hd, lit16_congr hG, splice_updR X od m G hr]

/-- **A pass over a group of `16 nm` rows** writing `updR`: every step sixteen lanes of `f` on
operands holding `xv`, `yv`. -/
theorem pass_upd {n : Nat} (nm : Nat)
    (step : Buf n → (o : USize) → o.toNat + 16 ≤ 16 * nm → Buf n) (f : UInt32 → UInt32 → UInt32)
    (g : F → F → F) (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (od : Nat)
    (G : Nat → F) (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
    (hrd : od + 16 * nm ≤ X.size) (xv yv : Nat → F) (hG : ∀ k < 16 * nm, G k = g (xv k) (yv k))
    (hn : (encode X).size = n) (hnm : 16 * nm < USize.size)
    (hstep : ∀ m < nm, ∃ x y : (k : Nat) → k ≤ 15 → UInt32,
      (∀ k hk, x k hk = (xv (16 * m + k)).val) ∧ (∀ k hk, y k hk = (yv (16 * m + k)).val) ∧
        ∀ hs ho, (step ⟨encode (updR X od (16 * m) G), hs⟩ (16 * m).toUSize ho).1 =
          lanes16 f x y (encode (updR X od (16 * m) G)) (d + (16 * m).toUSize)) :
    (runW nm hnm step ⟨encode X, hn⟩).1 = encode (updR X od (16 * nm) G) := by
  have hZ (m : Nat) : (encode (updR X od (16 * m) G)).size = n := by
    rw [size_encode_fields, size_updR, ← size_encode_fields, hn]
  refine groupsW_states nm hnm step (fun m ↦ encode (updR X od (16 * m) G)) hZ (fun m hm ho ↦ ?_)
    _ (by simp only [Nat.mul_zero, updR_zero])
  obtain ⟨x, y, hx, hy, e⟩ := hstep m hm
  rw [e, show 16 * (m + 1) = 16 * m + 16 by ring]
  refine lanes_upd f X od (16 * m) G x y (fun k ↦ xv (16 * m + k)) (fun k ↦ yv (16 * m + k)) g
    hf hx hy (fun t ht ↦ (hG _ (by omega)).symm) _ ?_ hX (by omega)
  rw [usize_add_toNat (by rw [toUSize_toNat (by omega)]; omega), toUSize_toNat (by omega), hd]

/-- The windows of `nm` groups from word `a` of an encoded array. -/
theorem wins_encode (Y : Array F) (nm oa : Nat) (a : USize) (ha : a.toNat = oa)
    (hY : 4 * Y.size < USize.size) (hra : oa + 16 * nm ≤ Y.size) :
    Wins (encode Y).size a nm :=
  ⟨by rw [size_encode_fields, ha]; omega, by rw [size_encode_fields]; exact hY⟩

/-- An offset `16 m` past word `a` of a group. -/
theorem off_toNat {a : USize} {oa m n : Nat} (ha : a.toNat = oa) (h : oa + 16 * m + 16 ≤ n)
    (hn : 4 * n < USize.size) : (a + (16 * m).toUSize).toNat = oa + 16 * m := by
  rw [usize_add_toNat (by rw [toUSize_toNat (by omega)]; omega), toUSize_toNat (by omega), ha]

/-- A word of the state while the destination's first `16 m` are written: an operand apart from
them reads its original word. -/
theorem ldS_upd (X : Array F) (od oa m nm : Nat) (G : Nat → F) (a : USize) (ha : a.toNat = oa)
    (hX : 4 * X.size < USize.size) (hra : oa + 16 * nm ≤ X.size) (hm : m < nm)
    (hA : Apart true oa od (16 * nm)) (h : Win (encode (updR X od (16 * m) G))
      (a + (16 * m).toUSize)) (k : Nat) (hk : k ≤ 15) :
    ld (encode (updR X od (16 * m) G)) (a + (16 * m).toUSize) h k hk =
      (X.getD (oa + (16 * m + k)) 0).val := by
  rw [ld_encode, off_toNat ha (show oa + 16 * m + 16 ≤ X.size by omega) hX, Nat.add_assoc]
  have := pick_updR hA X X (16 * m) G (16 * m + k) (by omega) (by omega)
  simp only [pick, ite_true] at this
  rw [this]

/-- A word of another buffer. -/
theorem ldE_val (E : Array F) (oa m : Nat) (a : USize) (ha : a.toNat = oa)
    (hE : 4 * E.size < USize.size) (hm : oa + 16 * m + 16 ≤ E.size)
    (h : Win (encode E) (a + (16 * m).toUSize)) (k : Nat) (hk : k ≤ 15) :
    ld (encode E) (a + (16 * m).toUSize) h k hk = (E.getD (oa + (16 * m + k)) 0).val := by
  rw [ld_encode, off_toNat ha hm hE, Nat.add_assoc]

/-- The windows of a state's and another buffer's words in range. -/
theorem winS (X : Array F) (od oa m nm : Nat) (G : Nat → F) (a : USize) (ha : a.toNat = oa)
    (hX : 4 * X.size < USize.size) (hra : oa + 16 * nm ≤ X.size) (hm : m < nm) :
    4 * ((a + (16 * m).toUSize).toNat + 16) ≤ (encode (updR X od (16 * m) G)).size ∧
      (encode (updR X od (16 * m) G)).size < USize.size := by
  rw [size_encode_fields, size_updR, off_toNat ha (show oa + 16 * m + 16 ≤ X.size by omega) hX]
  omega

theorem winE (E : Array F) (oa m : Nat) (a : USize) (ha : a.toNat = oa)
    (hE : 4 * E.size < USize.size) (hm : oa + 16 * m + 16 ≤ E.size) :
    4 * ((a + (16 * m).toUSize).toNat + 16) ≤ (encode E).size ∧ (encode E).size < USize.size := by
  rw [size_encode_fields, off_toNat ha hm hE]
  omega

theorem winS' (X : Array F) (od oa m nm : Nat) (G : Nat → F) (a : USize) (ha : a.toNat = oa)
    (hX : 4 * X.size < USize.size) (hra : oa + 16 * nm ≤ X.size) (hm : m < nm) :
    Win (encode (updR X od (16 * m) G)) (a + (16 * m).toUSize) :=
  have h := winS X od oa m nm G a ha hX hra hm
  ⟨h.1, Nat.lt_of_le_of_lt h.1 h.2⟩

theorem winE' (E : Array F) (oa m : Nat) (a : USize) (ha : a.toNat = oa)
    (hE : 4 * E.size < USize.size) (hm : oa + 16 * m + 16 ≤ E.size) :
    Win (encode E) (a + (16 * m).toUSize) :=
  have h := winE E oa m a ha hE hm
  ⟨h.1, Nat.lt_of_le_of_lt h.1 h.2⟩

/-! ### The kernels' passes -/

theorem groupsSS_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (oa ob : Nat) (a b : USize)
    (ha : a.toNat = oa) (hb : b.toNat = ob) (hra : oa + 16 * nm ≤ X.size)
    (hrb : ob + 16 * nm ≤ X.size) (hAa : Apart true oa od (16 * nm))
    (hAb : Apart true ob od (16 * nm))
    (hG : ∀ k < 16 * nm, G k = g (X.getD (oa + k) 0) (X.getD (ob + k) 0)) :
    kSS f nm (encode X) d a b = encode (updR X od (16 * nm) G) := by
  unfold kSS
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode X nm oa a ha hX hra),
      (wins_encode X nm ob b hb hX hrb)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd _ _ hG rfl _ fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk,
      fun k hk ↦ ld _ _ (winS' X od ob m nm G b hb hX hrb hm) k hk,
      fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk,
      fun k hk ↦ ldS_upd X od ob m nm G b hb hX hrb hm hAb _ k hk, ?_⟩
  intro hs ho
  unfold stepSS
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl

theorem groupsSE_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size)
        (oa ob : Nat) (a b : USize)
    (ha : a.toNat = oa) (hb : b.toNat = ob) (hra : oa + 16 * nm ≤ X.size)
    (hrb : ob + 16 * nm ≤ E.size) (hAa : Apart true oa od (16 * nm))
    (hG : ∀ k < 16 * nm, G k = g (X.getD (oa + k) 0) (E.getD (ob + k) 0)) :
    kSE f nm (encode X) (encode E) d a b = encode (updR X od (16 * nm) G) := by
  unfold kSE
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode X nm oa a ha hX hra),
      (wins_encode E nm ob b hb hE hrb)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd _ _ hG rfl _ fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk,
      fun k hk ↦ ld _ _ (winE' E ob m b hb hE (by omega)) k hk,
      fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk,
      fun k hk ↦ ldE_val E ob m b hb hE (by omega) _ k hk, ?_⟩
  intro hs ho
  unfold stepSE
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl

theorem groupsES_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size)
        (oa ob : Nat) (a b : USize)
    (ha : a.toNat = oa) (hb : b.toNat = ob) (hra : oa + 16 * nm ≤ E.size)
    (hrb : ob + 16 * nm ≤ X.size) (hAb : Apart true ob od (16 * nm))
    (hG : ∀ k < 16 * nm, G k = g (E.getD (oa + k) 0) (X.getD (ob + k) 0)) :
    kES f nm (encode X) (encode E) d a b = encode (updR X od (16 * nm) G) := by
  unfold kES
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode E nm oa a ha hE hra),
      (wins_encode X nm ob b hb hX hrb)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd _ _ hG rfl _ fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk,
      fun k hk ↦ ld _ _ (winS' X od ob m nm G b hb hX hrb hm) k hk,
      fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk,
      fun k hk ↦ ldS_upd X od ob m nm G b hb hX hrb hm hAb _ k hk, ?_⟩
  intro hs ho
  unfold stepES
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl

theorem groupsEE_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size)
        (oa ob : Nat) (a b : USize)
    (ha : a.toNat = oa) (hb : b.toNat = ob) (hra : oa + 16 * nm ≤ E.size)
    (hrb : ob + 16 * nm ≤ E.size)
    (hG : ∀ k < 16 * nm, G k = g (E.getD (oa + k) 0) (E.getD (ob + k) 0)) :
    kEE f nm (encode X) (encode E) d a b = encode (updR X od (16 * nm) G) := by
  unfold kEE
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode E nm oa a ha hE hra),
      (wins_encode E nm ob b hb hE hrb)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd _ _ hG rfl _ fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk,
      fun k hk ↦ ld _ _ (winE' E ob m b hb hE (by omega)) k hk,
      fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk,
      fun k hk ↦ ldE_val E ob m b hb hE (by omega) _ k hk, ?_⟩
  intro hs ho
  unfold stepEE
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl

theorem groupsSW_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (oa : Nat) (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ X.size)
    (hAa : Apart true oa od (16 * nm)) (c : F) (hG : ∀ k < 16 * nm, G k = g (X.getD (oa + k) 0) c) :
    kSW f nm (encode X) d a c.val = encode (updR X od (16 * nm) G) := by
  unfold kSW
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode X nm oa a ha hX hra)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd _ (fun _ ↦ c) hG rfl _ fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk, fun _ _ ↦ c.val,
      fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk, fun _ _ ↦ rfl, ?_⟩
  intro hs ho
  unfold stepSW
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl

theorem groupsEW_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size) (oa : Nat)
        (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ E.size) (c : F)
    (hG : ∀ k < 16 * nm, G k = g (E.getD (oa + k) 0) c) :
    kEW f nm (encode X) (encode E) d a c.val = encode (updR X od (16 * nm) G) := by
  unfold kEW
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode E nm oa a ha hE hra)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd _ (fun _ ↦ c) hG rfl _ fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk, fun _ _ ↦ c.val,
      fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk, fun _ _ ↦ rfl, ?_⟩
  intro hs ho
  unfold stepEW
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl

theorem groupsWS_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (oa : Nat) (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ X.size)
    (hAa : Apart true oa od (16 * nm)) (c : F) (hG : ∀ k < 16 * nm, G k = g c (X.getD (oa + k) 0)) :
    kWS f nm (encode X) d a c.val = encode (updR X od (16 * nm) G) := by
  unfold kWS
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode X nm oa a ha hX hra)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd (fun _ ↦ c) _ hG rfl _ fun m hm ↦ ?_
  refine ⟨fun _ _ ↦ c.val, fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk,
      fun _ _ ↦ rfl, fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk, ?_⟩
  intro hs ho
  unfold stepWS
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl

theorem groupsWE_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size) (oa : Nat)
        (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ E.size) (c : F)
    (hG : ∀ k < 16 * nm, G k = g c (E.getD (oa + k) 0)) :
    kWE f nm (encode X) (encode E) d a c.val = encode (updR X od (16 * nm) G) := by
  unfold kWE
  rw [dite_eq_left_of_eq_true (eq_true
    ⟨(wins_encode X nm od d hd hX hrd), (wins_encode E nm oa a ha hE hra)⟩)]
  refine pass_upd nm _ f g hf X od G d hd hX hrd (fun _ ↦ c) _ hG rfl _ fun m hm ↦ ?_
  refine ⟨fun _ _ ↦ c.val, fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk,
      fun _ _ ↦ rfl, fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk, ?_⟩
  intro hs ho
  unfold stepWE
  dsimp only
  rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
  rfl


/-! ### Accumulations -/

/-- Word `idx` of `accUpd`. -/
def accF (na : Nat) (X : Array F) (B m c : Nat) (A W : Nat → F) (idx : Nat) : F :=
  if idx < na * B ∧ (idx % B < 16 * m ∨ (idx / B < c ∧ idx % B < 16 * m + 16))
  then X.getD idx 0 + A (idx % B) * W (idx / B) else X.getD idx 0

/-- The state with the `na` accumulators of `B` rows, words `0, …, na B - 1`, plus `A i` times the
weights `W j`: of rows `i < 16 m`, and of rows `i < 16 m + 16` of accumulators `j < c`. -/
def accUpd (na : Nat) (X : Array F) (B m c : Nat) (A W : Nat → F) : Array F :=
  Array.ofFn (n := X.size) fun idx ↦ accF na X B m c A W idx.val

theorem getD_accUpd (X : Array F) (B m c : Nat) (A W : Nat → F) (idx : Nat) :
    (accUpd na X B m c A W).getD idx 0 = if idx < X.size ∧ idx < na * B ∧
      (idx % B < 16 * m ∨ (idx / B < c ∧ idx % B < 16 * m + 16))
    then X.getD idx 0 + A (idx % B) * W (idx / B) else X.getD idx 0 := by
  unfold accUpd
  rw [Words.getD_ofFn X.size]
  by_cases h : idx < X.size
  · simp only [h, true_and, ite_true, accF]
  · simp only [h, false_and, ite_false]
    exact (Words.getD_eq_zero X idx (by omega)).symm

@[simp] theorem size_accUpd (X : Array F) (B m c : Nat) (A W : Nat → F) :
    (accUpd na X B m c A W).size = X.size := Array.size_ofFn

/-- The chunk of rows `16 m, …, 16 m + 15` of accumulator `j`. -/
def chunkP (j m : Nat) (j' i : Nat) : Bool := j' == j && (16 * m ≤ i && i < 16 * m + 16)

/-- Word `idx` of `accP`. -/
def accPF (na : Nat) (X : Array F) (B : Nat) (P : Nat → Nat → Bool) (A W : Nat → F) (idx : Nat) :
    F :=
  if idx < na * B ∧ P (idx / B) (idx % B) = true
  then X.getD idx 0 + A (idx % B) * W (idx / B) else X.getD idx 0

/-- The state with the `na` accumulators of `B` rows, words `0, …, na B - 1`, plus `A i` times the
weights `W j` at the rows `i` of the accumulators `j` where `P j i`. -/
def accP (na : Nat) (X : Array F) (B : Nat) (P : Nat → Nat → Bool) (A W : Nat → F) : Array F :=
  Array.ofFn (n := X.size) fun idx ↦ accPF na X B P A W idx.val

@[simp] theorem size_accP (X : Array F) (B : Nat) (P : Nat → Nat → Bool) (A W : Nat → F) :
    (accP na X B P A W).size = X.size := Array.size_ofFn

theorem getD_accP (X : Array F) (B : Nat) (P : Nat → Nat → Bool) (A W : Nat → F) (idx : Nat) :
    (accP na X B P A W).getD idx 0 = if idx < X.size ∧ idx < na * B ∧ P (idx / B) (idx % B) = true
    then X.getD idx 0 + A (idx % B) * W (idx / B) else X.getD idx 0 := by
  unfold accP
  rw [Words.getD_ofFn X.size]
  by_cases h : idx < X.size
  · simp only [h, true_and, ite_true, accPF]
  · simp only [h, false_and, ite_false]
    exact (Words.getD_eq_zero X idx (by omega)).symm

/-- Rows and accumulators of a group: `idx < na B` is row `idx % B` of accumulator `idx / B`. -/
theorem div_mod_lt {B idx : Nat} (hi : idx < na * B) : idx / B < na ∧ idx % B < B := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.mul_zero] at hi; omega
    · exact h0
  exact ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi), Nat.mod_lt _ hB⟩

theorem accP_congr (X : Array F) (B : Nat) (P Q : Nat → Nat → Bool) (A W : Nat → F)
    (h : ∀ j < na, ∀ i < B, P j i = Q j i) : accP na X B P A W = accP na X B Q A W := by
  apply array_eq_of_getD _ _ 0 (by simp only [size_accP])
  intro idx
  rw [getD_accP, getD_accP]
  by_cases hi : idx < na * B
  · obtain ⟨h1, h2⟩ := div_mod_lt hi
    rw [h _ h1 _ h2]
  · simp only [hi, false_and, and_false, ite_false]

/-- No accumulation is the state. -/
theorem accP_none (X : Array F) (B : Nat) (P : Nat → Nat → Bool) (A W : Nat → F)
    (h : ∀ j < na, ∀ i < B, P j i = false) : accP na X B P A W = X := by
  apply array_eq_of_getD _ _ 0 (by simp only [size_accP])
  intro idx
  rw [getD_accP]
  by_cases hi : idx < na * B
  · obtain ⟨h1, h2⟩ := div_mod_lt hi
    rw [h _ h1 _ h2]
    simp only [Bool.false_eq_true, and_false, ite_false]
  · simp only [hi, false_and, and_false, ite_false]

/-- Every accumulator's every row is `accUpd`'s complete accumulation. -/
theorem accP_all (X : Array F) (nm : Nat) (A W : Nat → F) :
    accP na X (16 * nm) (fun _ _ ↦ true) A W = accUpd na X (16 * nm) nm 0 A W := by
  apply array_eq_of_getD _ _ 0 (by simp only [size_accP, size_accUpd])
  intro idx
  rw [getD_accP, getD_accUpd]
  by_cases hi : idx < na * (16 * nm)
  · have h2 := (div_mod_lt hi).2
    simp only [hi, h2, true_or, and_true]
  · simp only [hi, false_and, and_false, ite_false]

/-- Sixteen rows more of accumulator `j`. -/
theorem splice_accP (X : Array F) (B m j : Nat) (P : Nat → Nat → Bool) (A W : Nat → F)
    (hj : j < na) (hm : 16 * m + 16 ≤ B) (hX : na * B ≤ X.size) :
    splice (accP na X B P A W) (j * B + 16 * m) (lit16 fun t ↦
        X.getD (j * B + 16 * m + t) 0 + A (16 * m + t) * W j) =
      accP na X B (fun j' i ↦ P j' i || chunkP j m j' i) A W := by
  have hB : 0 < B := by omega
  have hjB : j * B + B ≤ na * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  have hs : j * B + 16 * m + (lit16 fun t ↦
      X.getD (j * B + 16 * m + t) 0 + A (16 * m + t) * W j).size ≤ (accP na X B P A W).size := by
    rw [size_lit16, size_accP]
    omega
  apply array_eq_of_getD _ _ 0 (by rw [size_splice _ _ _ hs, size_accP, size_accP])
  intro idx
  have hdm := Nat.div_add_mod idx B
  have hlt := Nat.mod_lt idx hB
  have hcomm : B * (idx / B) = idx / B * B := Nat.mul_comm _ _
  rw [getD_splice _ _ _ hs, size_lit16, getD_accP, getD_accP]
  by_cases hin : j * B + 16 * m ≤ idx ∧ idx < j * B + 16 * m + 16
  · have hq : idx / B = j := Nat.div_eq_of_lt_le (by omega)
      (by rw [Nat.add_mul, Nat.one_mul]; omega)
    have hr : idx % B = 16 * m + (idx - (j * B + 16 * m)) := by
      rw [hq] at hcomm hdm
      omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _
      (eq_true (by omega)), getD_lit16 _ _ (by omega), ite_eq_left_of_eq_true _ _ (eq_true
        ⟨by omega, by omega, by simp only [chunkP, hq, hr, beq_self_eq_true, Bool.true_and,
          Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]; right; omega⟩), hq, hr,
      show j * B + 16 * m + (idx - (j * B + 16 * m)) = idx by omega]
  · have e : (P (idx / B) (idx % B) || chunkP j m (idx / B) (idx % B)) = P (idx / B) (idx % B) := by
      have hc : chunkP j m (idx / B) (idx % B) = false := by
        simp only [chunkP, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
            decide_eq_false_iff_not,
          Nat.not_le, Nat.not_lt]
        by_cases q : idx / B = j
        · rw [q] at hcomm hdm
          right
          omega
        · left; exact q
      rw [hc, Bool.or_false]
    rw [e]
    by_cases h1 : idx < j * B + 16 * m
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- Sixteen rows more of accumulator `j`, by the lanes of the accumulation. -/
theorem lanesAcc_upd (X : Array F) (B m j : Nat) (P : Nat → Nat → Bool) (A W : Nat → F)
    (hj : j < na) (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size) (hB : na * B ≤ X.size)
    (hP : ∀ t < 16, P j (16 * m + t) = false) (o : USize) (ho : o.toNat = j * B + 16 * m)
    (h : Win (encode (accP na X B P A W)) o) (wj : UInt32)
    (hw : wj = (W j).val) (y : (k : Nat) → k ≤ 15 → UInt32)
    (hy : ∀ k hk, y k hk = (A (16 * m + k)).val) :
    lanes16 (fun acc x ↦ add p acc (mulM p x wj)) (fun k hk ↦ ld _ o h k hk) y
        (encode (accP na X B P A W)) o =
      encode (accP na X B (fun j' i ↦ P j' i || chunkP j m j' i) A W) := by
  subst hw
  have hjB : j * B + B ≤ na * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  rw [lanes16_encode (fun acc x ↦ add p acc (mulM p x (W j).val)) (fun acc x ↦ acc + x * W j)
    (fun x y ↦ by rw [mulM_val, add_val]) _ y (fun k ↦ X.getD (j * B + 16 * m + k) 0)
    (fun k ↦ A (16 * m + k)) (fun k hk ↦ ?_) hy _ o (by rw [size_accP]; exact hX)
    (by rw [size_accP, ho]; omega), ho]
  · rw [← splice_accP X B m j P A W hj hm (by omega)]
  · have hB0 : 0 < B := by omega
    have hq : (j * B + 16 * m + k) / B = j :=
      Nat.div_eq_of_lt_le (by rw [Nat.add_assoc]; exact Nat.le_add_right _ _)
        (by rw [Nat.add_mul, Nat.one_mul]; omega)
    have hr : (j * B + 16 * m + k) % B = 16 * m + k := by
      rw [show j * B + 16 * m + k = (16 * m + k) + B * j by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    rw [ld_encode, ho, getD_accP, hq, hr, hP k (by omega)]
    simp only [Bool.false_eq_true, and_false, ite_false]

/-- An accumulator's offset in a group of `B` rows. -/
theorem accOff_toNat {q : USize} {j B m : Nat} (hq : q.toNat = j * B) (hj : j < na)
    (hm : 16 * m + 16 ≤ B) (hB : 4 * (na * B) < USize.size) :
    (q + (16 * m).toUSize).toNat = j * B + 16 * m := by
  have hjB : j * B + B ≤ na * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  rw [usize_add_toNat (by rw [hq, toUSize_toNat (by omega)]; omega), hq,
    toUSize_toNat (by omega)]

variable (p) in
theorem stepAccS_upd (X : Array F) (B m j : Nat) (P : Nat → Nat → Bool) (A W : Nat → F)
    (hj : j < na) (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size) (hB : na * B ≤ X.size)
    (hP : ∀ t < 16, P j (16 * m + t) = false) (q a : USize) (hq : q.toNat = j * B) (oa : Nat)
    (ha : a.toNat = oa) (hoa : na * B ≤ oa) (hra : oa + B ≤ X.size)
    (hA : ∀ k < B, A k = X.getD (oa + k) 0) (wj : UInt32) (hw : wj = (W j).val) {n nm : Nat}
    (hwj : Wins n q nm) (hwa : Wins n a nm) (hsn : (encode (accP na X B P A W)).size = n)
    (ho : ((16 * m).toUSize).toNat + 16 ≤ 16 * nm) :
    (stepAccS p q a wj hwj hwa ⟨encode (accP na X B P A W), hsn⟩ (16 * m).toUSize ho).1 =
      encode (accP na X B (fun j' i ↦ P j' i || chunkP j m j' i) A W) := by
  have hs : (encode (accP na X B P A W)).size = 4 * X.size := by
    rw [size_encode_fields, size_accP]
  have hoff := accOff_toNat hq hj hm (by omega)
  have hjB : j * B + B ≤ na * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  have hoa' : (a + (16 * m).toUSize).toNat = oa + 16 * m :=
    off_toNat (n := X.size) ha (by omega) hX
  unfold stepAccS
  dsimp only
  rw [st16_eq _ _ _ (by rw [hs]; exact hX)]
  refine lanesAcc_upd X B m j P A W hj hm hX hB hP _ hoff _ wj hw _ fun k hk ↦ ?_
  rw [ld_encode, hoa', getD_accP, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hA _
      (by omega), Nat.add_assoc]

variable (p) in
theorem stepAccE_upd (X E : Array F) (B m j : Nat) (P : Nat → Nat → Bool) (A W : Nat → F)
    (hj : j < na) (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size)
    (hE : 4 * E.size < USize.size) (hB : na * B ≤ X.size)
    (hP : ∀ t < 16, P j (16 * m + t) = false) (q a : USize) (hq : q.toNat = j * B) (oa : Nat)
    (ha : a.toNat = oa) (hra : oa + B ≤ E.size) (hA : ∀ k < B, A k = E.getD (oa + k) 0)
    (wj : UInt32) (hw : wj = (W j).val) {n nm : Nat} (hwj : Wins n q nm)
    (hwa : Wins (encode E).size a nm) (hsn : (encode (accP na X B P A W)).size = n)
    (ho : ((16 * m).toUSize).toNat + 16 ≤ 16 * nm) :
    (stepAccE p q (encode E) a wj hwj hwa ⟨encode (accP na X B P A W), hsn⟩
      (16 * m).toUSize ho).1 = encode (accP na X B (fun j' i ↦ P j' i || chunkP j m j' i) A W) := by
  have hs : (encode (accP na X B P A W)).size = 4 * X.size := by
    rw [size_encode_fields, size_accP]
  have hoff := accOff_toNat hq hj hm (by omega)
  have hoa' : (a + (16 * m).toUSize).toNat = oa + 16 * m :=
    off_toNat (n := E.size) ha (by omega) hE
  unfold stepAccE
  dsimp only
  rw [st16_eq _ _ _ (by rw [hs]; exact hX)]
  refine lanesAcc_upd X B m j P A W hj hm hX hB hP _ hoff _ wj hw _ fun k hk ↦ ?_
  rw [ld_encode, hoa', hA _ (by omega), Nat.add_assoc]

variable (p) in
theorem stepAccW_upd (X : Array F) (B m j : Nat) (P : Nat → Nat → Bool) (W : Nat → F)
    (hj : j < na) (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size) (hB : na * B ≤ X.size)
    (hP : ∀ t < 16, P j (16 * m + t) = false) (q : USize) (hq : q.toNat = j * B) (c : F)
    (wj : UInt32) (hw : wj = (W j).val) {n nm : Nat} (hwj : Wins n q nm)
    (hsn : (encode (accP na X B P (fun _ ↦ c) W)).size = n)
    (ho : ((16 * m).toUSize).toNat + 16 ≤ 16 * nm) :
    (stepAccW p q c.val wj hwj ⟨encode (accP na X B P (fun _ ↦ c) W), hsn⟩
      (16 * m).toUSize ho).1 =
      encode (accP na X B (fun j' i ↦ P j' i || chunkP j m j' i) (fun _ ↦ c) W) := by
  have hs : (encode (accP na X B P (fun _ ↦ c) W)).size = 4 * X.size := by
    rw [size_encode_fields, size_accP]
  have hoff := accOff_toNat hq hj hm (by omega)
  unfold stepAccW
  dsimp only
  rw [st16_eq _ _ _ (by rw [hs]; exact hX)]
  exact lanesAcc_upd X B m j P _ W hj hm hX hB hP _ hoff _ wj hw (fun _ _ ↦ c.val) fun _ _ ↦ rfl

/-- An accumulation's weights' words. -/
def WtsOk (na : Nat) (wts : Array UInt32) (w : Nat) (W : Nat → F) : Prop :=
  ∀ j < na, wts.getD (na * w + j) 0 = (W j).val

/-- Accumulators `j, …, j + g - 1` of a pass: the accumulators before `j` complete, rows before
`16 m` of the pass's, and rows before `16 m + 16` of the first `c` of them. -/
def passP (j g m c : Nat) (j' i : Nat) : Bool :=
  decide (j' < j ∨ (j ≤ j' ∧ j' < j + g ∧ (i < 16 * m ∨ (j' < j + c ∧ i < 16 * m + 16))))

theorem passP_step (j g m c : Nat) (hc : c < g) (B : Nat) :
    ∀ j' < na, ∀ i < B, (passP j g m c j' i || chunkP (j + c) m j' i) = passP j g m (c + 1) j' i :=
  fun j' _ i _ ↦ by
    rw [Bool.eq_iff_iff]
    simp only [passP, chunkP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega

theorem passP_free (j g m c : Nat) :
    ∀ t < 16, passP j g m c (j + c) (16 * m + t) = false := fun t _ ↦ by
  simp only [passP, decide_eq_false_iff_not]
  omega

theorem passP_init (j g : Nat) (B : Nat) :
    ∀ j' < na, ∀ i < B, decide (j' < j) = passP j g 0 0 j' i := fun j' _ i _ ↦ by
  simp only [passP]
  exact decide_eq_decide.mpr (by omega)

theorem passP_next (j g m : Nat) (B : Nat) :
    ∀ j' < na, ∀ i < B, passP j g m g j' i = passP j g (m + 1) 0 j' i := fun j' _ i _ ↦ by
  simp only [passP]
  exact decide_eq_decide.mpr (by omega)

theorem passP_done (j g nm : Nat) :
    ∀ j' < na, ∀ i < 16 * nm, passP j g nm 0 j' i = decide (j' < j + g) := fun j' _ i _ ↦ by
  simp only [passP]
  exact decide_eq_decide.mpr (by omega)

/-- The offset of accumulator `j < na` of a group of `16 nm` rows. -/
theorem accOff (nm j : Nat) (rb : USize) (hrb : rb.toNat = 16 * nm) (hj : j < na)
    (hs : 4 * (na * (16 * nm)) < USize.size) : (j.toUSize * rb).toNat = j * (16 * nm) := by
  rcases Nat.eq_zero_or_pos nm with h0 | h0
  · subst h0
    rw [USize.toNat_mul, hrb]
    simp
  · have hjB : j * (16 * nm) < na * (16 * nm) := Nat.mul_lt_mul_of_pos_right hj (by omega)
    have hjl : j ≤ j * (16 * nm) := Nat.le_mul_of_pos_right j (by omega)
    have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    rw [USize.toNat_mul, toUSize_toNat (by omega), hrb, hsz, Nat.mod_eq_of_lt (by omega)]

variable (p) in
/-- A step of a register's accumulation pass. -/
theorem stepAccS_pass (X : Array F) (nm j g m c : Nat) (A W : Nat → F) (hc : c < g)
    (hjc : j + c < na) (hm : m < nm) (hX : 4 * X.size < USize.size)
    (hB : na * (16 * nm) ≤ X.size) (q a : USize) (hq : q.toNat = (j + c) * (16 * nm)) (oa : Nat)
    (ha : a.toNat = oa) (hoa : na * (16 * nm) ≤ oa) (hra : oa + 16 * nm ≤ X.size)
    (hA : ∀ k < 16 * nm, A k = X.getD (oa + k) 0) (w : UInt32) (hw : w = (W (j + c)).val)
    {n : Nat} (hwq : Wins n q nm) (hwa : Wins n a nm)
    (hsn : (encode (accP na X (16 * nm) (passP j g m c) A W)).size = n)
    (ho : ((16 * m).toUSize).toNat + 16 ≤ 16 * nm) :
    stepAccS p q a w hwq hwa ⟨encode (accP na X (16 * nm) (passP j g m c) A W), hsn⟩
      (16 * m).toUSize ho = ⟨encode (accP na X (16 * nm) (passP j g m (c + 1)) A W),
        by rw [size_encode_fields, size_accP]; rw [size_encode_fields, size_accP] at hsn
           exact hsn⟩ := by
  apply Subtype.ext
  rw [stepAccS_upd p X (16 * nm) m (j + c) _ A W hjc (by omega) hX hB
    (passP_free j g m c) q a hq oa ha hoa hra hA w hw hwq hwa hsn ho]
  exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_step j g m c hc _))

variable (p) in
/-- **A register's accumulation passes** from accumulator `j`. -/
theorem accPassesS_upd (X : Array F) (nm : Nat) (A W : Nat → F) (hX : 4 * X.size < USize.size)
    (hB : na * (16 * nm) ≤ X.size) (hnm : 16 * nm < USize.size) (rb a : USize)
    (hrb : rb.toNat = 16 * nm) (oa : Nat) (ha : a.toNat = oa) (hoa : na * (16 * nm) ≤ oa)
    (hra : oa + 16 * nm ≤ X.size) (hA : ∀ k < 16 * nm, A k = X.getD (oa + k) 0)
    (wts : Array UInt32) (base : Nat) (hw : ∀ j < na, wts.getD (base + j) 0 = (W j).val)
    (hj : ∀ j < na, Wins (encode X).size (j.toUSize * rb) nm)
    (hwa : Wins (encode X).size a nm) :
    ∀ k j (hk : j + k = na) (s : Buf (encode X).size),
      s.1 = encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j)) A W) →
      (accPassesS p nm hnm rb a wts base na hj hwa k j hk s).1 =
        encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < na)) A W) := by
  have hsz (j g m c : Nat) : (encode (accP na X (16 * nm) (passP j g m c) A W)).size =
      (encode X).size := by rw [size_encode_fields, size_accP, size_encode_fields]
  have hs4 : 4 * (na * (16 * nm)) < USize.size := by omega
  have hoff (j : Nat) (hc : j < na) : (j.toUSize * rb).toNat = j * (16 * nm) :=
    accOff nm j rb hrb hc hs4
  -- One pass of a single accumulator `j`.
  have single (j : Nat) (hj1 : j < na) (s : Buf (encode X).size)
      (hs : s.1 = encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j)) A W)) :
      (runW nm hnm (stepAccS p (j.toUSize * rb) a (wts.getD (base + j) 0) (hj j hj1) hwa) s).1 =
        encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j + 1)) A W) := by
    rw [groupsW_states nm hnm _ (fun m ↦ encode (accP na X (16 * nm) (passP j 1 m 0) A W))
      (fun m ↦ hsz j 1 m 0) (fun m hm ho ↦ ?_) s (by
        rw [hs]; exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_init j 1 _)))]
    · exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_done j 1 nm))
    · rw [stepAccS_pass p X nm j 1 m 0 A W (by decide) (by omega) hm hX hB _ a
          (by rw [Nat.add_zero]; exact hoff j hj1) oa ha hoa hra hA _
          (by rw [Nat.add_zero, hw j hj1])]
      exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_next j 1 m _))
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro j hk s hs
  match k, ih, hk with
  | 0, _, hk =>
    obtain rfl : j = na := by omega
    rw [accPassesS]
    exact hs
  | 1, ih, hk | 2, ih, hk | 3, ih, hk =>
    rw [accPassesS]
    exact ih _ (by omega) (j + 1) (by omega) _ (single j (by omega) s hs)
  | k + 4, ih, hk =>
    have hw' (c : Nat) (hc : j + c < na) : wts.getD (base + j + c) 0 = (W (j + c)).val := by
      rw [Nat.add_assoc]; exact hw _ hc
    rw [accPassesS]
    refine ih k (by omega) (j + 4) (by omega) _ ?_
    rw [groupsW_states nm hnm _ (fun m ↦ encode (accP na X (16 * nm) (passP j 4 m 0) A W))
      (fun m ↦ hsz j 4 m 0) (fun m hm ho ↦ ?_) s (by
        rw [hs]; exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_init j 4 _)))]
    · exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_done j 4 nm))
    · rw [stepAccS_pass p X nm j 4 m 0 A W (by decide) (by omega) hm hX hB _ a
          (by rw [Nat.add_zero]; exact hoff j (by omega)) oa ha hoa hra hA _
          (by rw [Nat.add_zero, hw j (by omega)]),
        stepAccS_pass p X nm j 4 m 1 A W (by decide) (by omega) hm hX hB _ a
          (hoff (j + 1) (by omega)) oa ha hoa hra hA _ (hw' 1 (by omega)),
        stepAccS_pass p X nm j 4 m 2 A W (by decide) (by omega) hm hX hB _ a
          (hoff (j + 2) (by omega)) oa ha hoa hra hA _ (hw' 2 (by omega)),
        stepAccS_pass p X nm j 4 m 3 A W (by decide) (by omega) hm hX hB _ a
          (hoff (j + 3) (by omega)) oa ha hoa hra hA _ (hw' 3 (by omega))]
      exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_next j 4 m _))

/-- **An accumulation of a register** on a group of `16 nm` rows. -/
theorem accS_upd (X : Array F) (nm : Nat) (A W : Nat → F) (hX : 4 * X.size < USize.size)
    (hB : na * (16 * nm) ≤ X.size) (rb a : USize) (hrb : rb.toNat = 16 * nm) (oa : Nat)
    (ha : a.toNat = oa) (hoa : na * (16 * nm) ≤ oa) (hra : oa + 16 * nm ≤ X.size)
    (hA : ∀ k < 16 * nm, A k = X.getD (oa + k) 0) (wts : Array UInt32) (w : Nat)
    (hw : WtsOk na wts w W) :
    accS p na nm rb (encode X) a wts w = encode (accUpd na X (16 * nm) nm 0 A W) := by
  have hwa := wins_encode X nm oa a ha hX hra
  have hnm : 16 * nm < USize.size := by
    rw [size_encode_fields] at hwa; have := hwa.2; omega
  have hfit : AccsFit (encode X).size na rb nm :=
    ⟨hrb, by rw [size_encode_fields, hrb]; omega, by rw [size_encode_fields]; omega⟩
  unfold accS
  rw [dite_eq_left_of_eq_true (eq_true ⟨hnm, hfit, hwa⟩), ← accP_all,
    accPassesS_upd p X nm A W hX hB hnm rb a hrb oa ha hoa hra hA wts (na * w) hw _ hwa na 0
      (Nat.zero_add na) _ (by
        rw [accP_none _ _ _ _ _ fun j' _ _ _ ↦ by simp only [Nat.not_lt_zero, decide_false]])]
  exact congrArg encode (accP_congr _ _ _ _ _ _ fun j' hj' _ _ ↦ by simp only [hj', decide_true])

variable (p) in
/-- A step of another buffer's accumulation pass. -/
theorem stepAccE_pass (X E : Array F) (nm j g m c : Nat) (A W : Nat → F) (hc : c < g)
    (hjc : j + c < na) (hm : m < nm) (hX : 4 * X.size < USize.size)
    (hE : 4 * E.size < USize.size) (hB : na * (16 * nm) ≤ X.size) (q a : USize)
    (hq : q.toNat = (j + c) * (16 * nm)) (oa : Nat) (ha : a.toNat = oa)
    (hra : oa + 16 * nm ≤ E.size) (hA : ∀ k < 16 * nm, A k = E.getD (oa + k) 0) (w : UInt32)
    (hw : w = (W (j + c)).val) {n : Nat} (hwq : Wins n q nm) (hwa : Wins (encode E).size a nm)
    (hsn : (encode (accP na X (16 * nm) (passP j g m c) A W)).size = n)
    (ho : ((16 * m).toUSize).toNat + 16 ≤ 16 * nm) :
    stepAccE p q (encode E) a w hwq hwa ⟨encode (accP na X (16 * nm) (passP j g m c) A W), hsn⟩
      (16 * m).toUSize ho = ⟨encode (accP na X (16 * nm) (passP j g m (c + 1)) A W),
        by rw [size_encode_fields, size_accP]; rw [size_encode_fields, size_accP] at hsn
           exact hsn⟩ := by
  apply Subtype.ext
  rw [stepAccE_upd p X E (16 * nm) m (j + c) _ A W hjc (by omega) hX hE hB
    (passP_free j g m c) q a hq oa ha hra hA w hw hwq hwa hsn ho]
  exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_step j g m c hc _))

variable (p) in
/-- **Another buffer's accumulation passes** from accumulator `j`. -/
theorem accPassesE_upd (X E : Array F) (nm : Nat) (A W : Nat → F) (hX : 4 * X.size < USize.size)
    (hE : 4 * E.size < USize.size) (hB : na * (16 * nm) ≤ X.size) (hnm : 16 * nm < USize.size)
    (rb a : USize) (hrb : rb.toNat = 16 * nm) (oa : Nat) (ha : a.toNat = oa)
    (hra : oa + 16 * nm ≤ E.size) (hA : ∀ k < 16 * nm, A k = E.getD (oa + k) 0)
    (wts : Array UInt32) (base : Nat) (hw : ∀ j < na, wts.getD (base + j) 0 = (W j).val)
    (hj : ∀ j < na, Wins (encode X).size (j.toUSize * rb) nm)
    (hwa : Wins (encode E).size a nm) :
    ∀ k j (hk : j + k = na) (s : Buf (encode X).size),
      s.1 = encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j)) A W) →
      (accPassesE p nm hnm rb (encode E) a wts base na hj hwa k j hk s).1 =
        encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < na)) A W) := by
  have hsz (j g m c : Nat) : (encode (accP na X (16 * nm) (passP j g m c) A W)).size =
      (encode X).size := by rw [size_encode_fields, size_accP, size_encode_fields]
  have hs4 : 4 * (na * (16 * nm)) < USize.size := by omega
  have hoff (j : Nat) (hc : j < na) : (j.toUSize * rb).toNat = j * (16 * nm) :=
    accOff nm j rb hrb hc hs4
  -- One pass of a single accumulator `j`.
  have single (j : Nat) (hj1 : j < na) (s : Buf (encode X).size)
      (hs : s.1 = encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j)) A W)) :
      (runW nm hnm (stepAccE p (j.toUSize * rb) (encode E) a (wts.getD (base + j) 0) (hj j hj1) hwa)
        s).1 =
        encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j + 1)) A W) := by
    rw [groupsW_states nm hnm _ (fun m ↦ encode (accP na X (16 * nm) (passP j 1 m 0) A W))
      (fun m ↦ hsz j 1 m 0) (fun m hm ho ↦ ?_) s (by
        rw [hs]; exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_init j 1 _)))]
    · exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_done j 1 nm))
    · rw [stepAccE_pass p X E nm j 1 m 0 A W (by decide) (by omega) hm hX hE hB _ a
          (by rw [Nat.add_zero]; exact hoff j hj1) oa ha hra hA _
          (by rw [Nat.add_zero, hw j hj1])]
      exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_next j 1 m _))
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro j hk s hs
  match k, ih, hk with
  | 0, _, hk =>
    obtain rfl : j = na := by omega
    rw [accPassesE]
    exact hs
  | 1, ih, hk | 2, ih, hk | 3, ih, hk =>
    rw [accPassesE]
    exact ih _ (by omega) (j + 1) (by omega) _ (single j (by omega) s hs)
  | k + 4, ih, hk =>
    have hw' (c : Nat) (hc : j + c < na) : wts.getD (base + j + c) 0 = (W (j + c)).val := by
      rw [Nat.add_assoc]; exact hw _ hc
    rw [accPassesE]
    refine ih k (by omega) (j + 4) (by omega) _ ?_
    rw [groupsW_states nm hnm _ (fun m ↦ encode (accP na X (16 * nm) (passP j 4 m 0) A W))
      (fun m ↦ hsz j 4 m 0) (fun m hm ho ↦ ?_) s (by
        rw [hs]; exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_init j 4 _)))]
    · exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_done j 4 nm))
    · rw [stepAccE_pass p X E nm j 4 m 0 A W (by decide) (by omega) hm hX hE hB _ a
          (by rw [Nat.add_zero]; exact hoff j (by omega)) oa ha hra hA _
          (by rw [Nat.add_zero, hw j (by omega)]),
        stepAccE_pass p X E nm j 4 m 1 A W (by decide) (by omega) hm hX hE hB _ a
          (hoff (j + 1) (by omega)) oa ha hra hA _ (hw' 1 (by omega)),
        stepAccE_pass p X E nm j 4 m 2 A W (by decide) (by omega) hm hX hE hB _ a
          (hoff (j + 2) (by omega)) oa ha hra hA _ (hw' 2 (by omega)),
        stepAccE_pass p X E nm j 4 m 3 A W (by decide) (by omega) hm hX hE hB _ a
          (hoff (j + 3) (by omega)) oa ha hra hA _ (hw' 3 (by omega))]
      exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_next j 4 m _))

/-- **An accumulation of another buffer's words** on a group of `16 nm` rows. -/
theorem accE_upd (X E : Array F) (nm : Nat) (A W : Nat → F) (hX : 4 * X.size < USize.size)
    (hE : 4 * E.size < USize.size) (hB : na * (16 * nm) ≤ X.size) (rb a : USize)
    (hrb : rb.toNat = 16 * nm) (oa : Nat) (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ E.size)
    (hA : ∀ k < 16 * nm, A k = E.getD (oa + k) 0) (wts : Array UInt32) (w : Nat)
    (hw : WtsOk na wts w W) :
    accE p na nm rb (encode X) (encode E) a wts w = encode (accUpd na X (16 * nm) nm 0 A W) := by
  have hwa := wins_encode E nm oa a ha hE hra
  have hnm : 16 * nm < USize.size := by
    rw [size_encode_fields] at hwa; have := hwa.2; omega
  have hfit : AccsFit (encode X).size na rb nm :=
    ⟨hrb, by rw [size_encode_fields, hrb]; omega, by rw [size_encode_fields]; omega⟩
  unfold accE
  rw [dite_eq_left_of_eq_true (eq_true ⟨hnm, hfit, hwa⟩), ← accP_all,
    accPassesE_upd p X E nm A W hX hE hB hnm rb a hrb oa ha hra hA wts (na * w) hw _ hwa na 0
      (Nat.zero_add na) _ (by
        rw [accP_none _ _ _ _ _ fun j' _ _ _ ↦ by simp only [Nat.not_lt_zero, decide_false]])]
  exact congrArg encode (accP_congr _ _ _ _ _ _ fun j' hj' _ _ ↦ by simp only [hj', decide_true])

variable (p) in
/-- A step of a constant's accumulation pass. -/
theorem stepAccW_pass (X : Array F) (nm j g m c : Nat) (cv : F) (W : Nat → F) (hc : c < g)
    (hjc : j + c < na) (hm : m < nm) (hX : 4 * X.size < USize.size)
    (hB : na * (16 * nm) ≤ X.size) (q : USize) (hq : q.toNat = (j + c) * (16 * nm))
    (w : UInt32) (hw : w = (W (j + c)).val) {n : Nat} (hwq : Wins n q nm)
    (hsn : (encode (accP na X (16 * nm) (passP j g m c) (fun _ ↦ cv) W)).size = n)
    (ho : ((16 * m).toUSize).toNat + 16 ≤ 16 * nm) :
    stepAccW p q cv.val w hwq ⟨encode (accP na X (16 * nm) (passP j g m c) (fun _ ↦ cv) W), hsn⟩
      (16 * m).toUSize ho = ⟨encode (accP na X (16 * nm) (passP j g m (c + 1)) (fun _ ↦ cv) W),
        by rw [size_encode_fields, size_accP]; rw [size_encode_fields, size_accP] at hsn
           exact hsn⟩ := by
  apply Subtype.ext
  rw [stepAccW_upd p X (16 * nm) m (j + c) _ W hjc (by omega) hX hB
    (passP_free j g m c) q hq cv w hw hwq hsn ho]
  exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_step j g m c hc _))

variable (p) in
/-- **A constant's accumulation passes** from accumulator `j`. -/
theorem accPassesW_upd (X : Array F) (nm : Nat) (cv : F) (W : Nat → F)
    (hX : 4 * X.size < USize.size) (hB : na * (16 * nm) ≤ X.size) (hnm : 16 * nm < USize.size)
    (rb : USize) (hrb : rb.toNat = 16 * nm) (wts : Array UInt32) (base : Nat)
    (hw : ∀ j < na, wts.getD (base + j) 0 = (W j).val)
    (hj : ∀ j < na, Wins (encode X).size (j.toUSize * rb) nm) :
    ∀ k j (hk : j + k = na) (s : Buf (encode X).size),
      s.1 = encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j)) (fun _ ↦ cv) W) →
      (accPassesW p nm hnm rb cv.val wts base na hj k j hk s).1 =
        encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < na)) (fun _ ↦ cv) W) := by
  have hsz (j g m c : Nat) : (encode (accP na X (16 * nm) (passP j g m c) (fun _ ↦ cv) W)).size =
      (encode X).size := by rw [size_encode_fields, size_accP, size_encode_fields]
  have hs4 : 4 * (na * (16 * nm)) < USize.size := by omega
  have hoff (j : Nat) (hc : j < na) : (j.toUSize * rb).toNat = j * (16 * nm) :=
    accOff nm j rb hrb hc hs4
  -- One pass of a single accumulator `j`.
  have single (j : Nat) (hj1 : j < na) (s : Buf (encode X).size)
      (hs : s.1 = encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j)) (fun _ ↦ cv) W)) :
      (runW nm hnm (stepAccW p (j.toUSize * rb) cv.val (wts.getD (base + j) 0) (hj j hj1)) s).1 =
        encode (accP na X (16 * nm) (fun j' _ ↦ decide (j' < j + 1)) (fun _ ↦ cv) W) := by
    rw [groupsW_states nm hnm _ (fun m ↦ encode (accP na X (16 * nm) (passP j 1 m 0)
      (fun _ ↦ cv) W))
      (fun m ↦ hsz j 1 m 0) (fun m hm ho ↦ ?_) s (by
        rw [hs]; exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_init j 1 _)))]
    · exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_done j 1 nm))
    · rw [stepAccW_pass p X nm j 1 m 0 cv W (by decide) (by omega) hm hX hB _
          (by rw [Nat.add_zero]; exact hoff j hj1) _
          (by rw [Nat.add_zero, hw j hj1])]
      exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_next j 1 m _))
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro j hk s hs
  match k, ih, hk with
  | 0, _, hk =>
    obtain rfl : j = na := by omega
    rw [accPassesW]
    exact hs
  | 1, ih, hk | 2, ih, hk | 3, ih, hk =>
    rw [accPassesW]
    exact ih _ (by omega) (j + 1) (by omega) _ (single j (by omega) s hs)
  | k + 4, ih, hk =>
    have hw' (c : Nat) (hc : j + c < na) : wts.getD (base + j + c) 0 = (W (j + c)).val := by
      rw [Nat.add_assoc]; exact hw _ hc
    rw [accPassesW]
    refine ih k (by omega) (j + 4) (by omega) _ ?_
    rw [groupsW_states nm hnm _ (fun m ↦ encode (accP na X (16 * nm) (passP j 4 m 0)
      (fun _ ↦ cv) W))
      (fun m ↦ hsz j 4 m 0) (fun m hm ho ↦ ?_) s (by
        rw [hs]; exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_init j 4 _)))]
    · exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_done j 4 nm))
    · rw [stepAccW_pass p X nm j 4 m 0 cv W (by decide) (by omega) hm hX hB _
          (by rw [Nat.add_zero]; exact hoff j (by omega)) _
          (by rw [Nat.add_zero, hw j (by omega)]),
        stepAccW_pass p X nm j 4 m 1 cv W (by decide) (by omega) hm hX hB _
          (hoff (j + 1) (by omega)) _ (hw' 1 (by omega)),
        stepAccW_pass p X nm j 4 m 2 cv W (by decide) (by omega) hm hX hB _
          (hoff (j + 2) (by omega)) _ (hw' 2 (by omega)),
        stepAccW_pass p X nm j 4 m 3 cv W (by decide) (by omega) hm hX hB _
          (hoff (j + 3) (by omega)) _ (hw' 3 (by omega))]
      exact congrArg encode (accP_congr _ _ _ _ _ _ (passP_next j 4 m _))

/-- **An accumulation of a constant** on a group of `16 nm` rows. -/
theorem accW_upd (X : Array F) (nm : Nat) (W : Nat → F) (hX : 4 * X.size < USize.size)
    (hB : na * (16 * nm) ≤ X.size) (rb : USize) (hrb : rb.toNat = 16 * nm)
    (hnm : 16 * nm < USize.size) (c : F) (wts : Array UInt32) (w : Nat) (hw : WtsOk na wts w W) :
    accW p na nm rb (encode X) c.val wts w =
      encode (accUpd na X (16 * nm) nm 0 (fun _ ↦ c) W) := by
  have hfit : AccsFit (encode X).size na rb nm :=
    ⟨hrb, by rw [size_encode_fields, hrb]; omega, by rw [size_encode_fields]; omega⟩
  unfold accW
  rw [dite_eq_left_of_eq_true (eq_true ⟨hnm, hfit⟩), ← accP_all,
    accPassesW_upd p X nm c W hX hB hnm rb hrb wts (na * w) hw _ na 0 (Nat.zero_add na) _ (by
      rw [accP_none _ _ _ _ _ fun j' _ _ _ ↦ by simp only [Nat.not_lt_zero, decide_false]])]
  exact congrArg encode (accP_congr _ _ _ _ _ _ fun j' hj' _ _ ↦ by simp only [hj', decide_true])

/-! ### Fills, copies and gathers -/

theorem fill_upd (X : Array F) (nm od : Nat) (d : USize) (hd : d.toNat = od)
    (hX : 4 * X.size < USize.size) (hrd : od + 16 * nm ≤ X.size) (c : F) :
    fill nm (encode X) d c.val = encode (updR X od (16 * nm) fun _ ↦ c) := by
  unfold fill
  rw [dite_eq_left_of_eq_true (eq_true (wins_encode X nm od d hd hX hrd))]
  exact pass_upd nm _ (fun x _ ↦ x) (fun x _ ↦ x) (fun _ _ ↦ rfl) X od _ d hd hX hrd (fun _ ↦ c)
    (fun _ ↦ c) (fun _ _ ↦ rfl) rfl _ fun m hm ↦ ⟨fun _ _ ↦ c.val, fun _ _ ↦ c.val, fun _ _ ↦ rfl,
      fun _ _ ↦ rfl, fun hs ho ↦ by
        unfold stepW
        dsimp only
        rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
        rfl⟩

theorem copy_upd (X E : Array F) (nm od oa : Nat) (d a : USize) (hd : d.toNat = od)
    (ha : a.toNat = oa) (hX : 4 * X.size < USize.size) (hE : 4 * E.size < USize.size)
    (hrd : od + 16 * nm ≤ X.size) (hra : oa + 16 * nm ≤ E.size) :
    copy nm (encode X) (encode E) d a = encode (updR X od (16 * nm) fun k ↦ E.getD (oa + k) 0) :=
  groupsEW_upd (fun x _ ↦ x) (fun x _ ↦ x) (fun _ _ ↦ rfl) X nm od _ d hd hX hrd E hE oa a ha
    hra 0 fun _ _ ↦ rfl

theorem div_mod_add {n0 k R : Nat} (hk : n0 % R + k < R) :
    (n0 + k) / R = n0 / R ∧ (n0 + k) % R = n0 % R + k := by
  have hR : 0 < R := by omega
  have e : n0 + k = (n0 % R + k) + n0 / R * R := by have := Nat.div_add_mod' n0 R; omega
  rw [e, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hk, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  exact ⟨rfl, rfl⟩

/-- Entry `n0 + k` of columns in blocks, for rows within the block of `n0`. -/
theorem ColsF.at_add (M : ColsF p) (n0 k c : Nat) (hk : n0 % M.rows + k < M.rows) :
    M.at (n0 + k) c = (M.col n0 c).getD (n0 % M.rows + k) 0 := by
  obtain ⟨h1, h2⟩ := div_mod_add hk
  unfold ColsF.at ColsF.col
  rw [h1, h2]

theorem gather_upd (X : Array F) (M : ColsF p) (nm od c r0 : Nat) (next : Array Nat)
    (nseq : Bool) (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size) (hM : M.Addr)
    (hrd : od + 16 * nm ≤ X.size) (hr : ∀ k < 16 * nm, M.Has (next.getD (r0 + k) 0) c)
    (hseq : nseq = true → ∀ k < 16 * nm, next.getD (r0 + k) 0 = next.getD r0 0 + k) :
    gather nm (encode X) d M.enc c next r0 nseq =
      encode (updR X od (16 * nm) fun k ↦ M.at (next.getD (r0 + k) 0) c) := by
  unfold gather
  dsimp only
  split
  · rename_i hc
    obtain ⟨hs, hblk⟩ := hc
    have hseq := hseq hs
    have hR : M.enc.rows = M.rows := rfl
    have hw : M.enc.width = M.width := rfl
    rw [hR] at hblk
    rw [hR, hw]
    generalize hn0 : next.getD r0 0 = n0 at hblk hseq
    by_cases hnm : nm = 0
    · subst hnm
      unfold kEW
      split <;> simp only [runW, groupsW, Nat.mul_zero, updR_zero]
    have hcol : M.enc.cols.getD (n0 / M.rows * M.width + c) .empty = encode (M.col n0 c) := by
      unfold ColsF.enc ColsF.col
      dsimp only
      generalize n0 / M.rows * M.width + c = i
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases M.C[i]? with
      | none => exact CompPoly.PackedRepr.encode_empty.symm
      | some a => rfl
    have hlast := hr (16 * nm - 1) (by omega)
    rw [hseq _ (by omega)] at hlast
    obtain ⟨h1, h2⟩ := div_mod_add (show n0 % M.rows + (16 * nm - 1) < M.rows by omega)
    have hsz : n0 % M.rows + 16 * nm ≤ (M.col n0 c).size := by
      unfold ColsF.Has ColsF.col at hlast
      rw [h1, h2] at hlast
      unfold ColsF.col
      omega
    have hE : 4 * (M.col n0 c).size < USize.size := by
      unfold ColsF.col
      rw [Array.getD_eq_getD_getElem?]
      cases e : M.C[n0 / M.rows * M.width + c]? with
      | none => show 4 * 0 < USize.size; have := USize.le_size; omega
      | some a => exact hM a (Array.mem_of_getElem? e)
    rw [hcol]
    have e := copy_upd X (M.col n0 c) nm od (n0 % M.rows) d (n0 % M.rows).toUSize hd
      (toUSize_toNat (by omega)) hX hE hrd hsz
    unfold copy at e
    rw [e]
    congr 1
    apply updR_congr
    intro k hk
    rw [hseq k hk, ColsF.at_add M _ k c (by omega)]
  · rw [dite_eq_left_of_eq_true (eq_true (wins_encode X nm od d hd hX hrd))]
    exact pass_upd nm _ (fun x _ ↦ x) (fun x _ ↦ x) (fun _ _ ↦ rfl) X od _ d hd hX hrd
      (fun k ↦ M.at (next.getD (r0 + k) 0) c) (fun _ ↦ 0) (fun _ _ ↦ rfl) rfl _ fun m hm ↦
        ⟨fun k _ ↦ M.enc.at (next.getD (r0 + (16 * m).toUSize.toNat + k) 0) c,
          fun _ _ ↦ 0, fun k hk ↦ by
            have h1 := hr (16 * m + k) (by omega)
            rw [toUSize_toNat (by omega)]
            dsimp only
            rw [Nat.add_assoc, M.at_enc hM _ c h1], fun _ _ ↦ rfl, fun hs ho ↦ by
          unfold stepGather
          dsimp only
          rw [st16_eq _ _ _ (by rw [size_encode_fields, size_updR]; exact hX)]
          rfl⟩

theorem copyPer_upd (X : Array F) (PER : Array (Array F)) (nm od j oa : Nat) (d a : USize)
    (hd : d.toNat = od) (ha : j < PER.size → a.toNat = oa) (hX : 4 * X.size < USize.size)
    (hP : ∀ c ∈ PER, 4 * c.size < USize.size) (hrd : od + 16 * nm ≤ X.size)
    (hra : j < PER.size → oa + 16 * nm ≤ (PER.getD j #[]).size) :
    copyPer nm (encode X) (PER.map encode) j d a =
      encode (updR X od (16 * nm) fun k ↦ (PER.getD j #[]).getD (oa + k) 0) := by
  unfold copyPer
  by_cases hj : j < PER.size
  · have hc : PER.getD j #[] = PER[j] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hj, Option.map_some]
    dsimp only
    rw [hc] at hra ⊢
    exact copy_upd X _ nm od oa d a hd (ha hj) hX (hP _ (Array.getElem_mem hj)) hrd (hra hj)
  · rw [Array.getElem?_map, Array.getElem?_eq_none (by omega), Option.map_none]
    dsimp only
    have hc : PER.getD j #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    rw [hc]
    exact fill_upd X nm od d hd hX hrd 0

/-! ### The group machine on the rows' values -/

/-- The words of `B` rows' run states: slot `s` (`St.slot`) of row `i` at word `B s + i`. -/
def gtab (na B nregs : Nat) (sts : Nat → St F) : Array F :=
  tab (B * (na + nregs)) fun idx ↦ (sts (idx % B)).slot na (idx / B)

/-- A group's state holds `B` rows' run states. -/
def GroupRel (B nregs : Nat) (st : ByteArray) (sts : Nat → St F) : Prop :=
  st = encode (gtab na B nregs sts)

theorem size_gtab (B nregs : Nat) (sts : Nat → St F) :
    (gtab na B nregs sts).size = B * (na + nregs) := size_tab ..

/-- Slot `t` of every row set: its words overwritten. -/
theorem updR_gtab (B nregs t : Nat) (sts : Nat → St F) (H : Nat → F) :
    updR (gtab na B nregs sts) (B * t) B H = gtab na B nregs fun i ↦ (sts i).setSlot na t (H i) :=
        by
  apply array_eq_of_getD _ _ 0 (by rw [size_updR, size_gtab, size_gtab])
  intro idx
  rw [getD_updR, size_gtab]
  unfold gtab
  by_cases hi : idx < B * (na + nregs)
  · rw [getD_tab _ _ _ hi, getD_tab _ _ _ hi, St.slot_setSlot]
    have hB : 0 < B := Nat.pos_of_ne_zero fun h ↦ by subst h; simp only [Nat.zero_mul] at hi; omega
    have hdm := Nat.div_add_mod idx B
    have hlt := Nat.mod_lt idx hB
    by_cases hr : B * t ≤ idx ∧ idx < B * t + B
    · have hq : idx / B = t := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hr.1)
        (by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; exact hr.2)
      rw [hq] at hdm
      simp only [hi, hr, and_self, ite_true, hq]
      congr 1
      omega
    · simp only [hi, hr, and_false, ite_false]
      have : idx / B ≠ t := fun hq ↦ by
        rw [hq] at hdm
        exact hr ⟨by omega, by omega⟩
      simp only [this, ite_false]
  · rw [Words.getD_eq_zero _ _ (by rw [size_tab]; omega),
      Words.getD_eq_zero _ _ (by rw [size_tab]; omega)]
    simp only [hi, false_and, ite_false]

/-- The accumulators of every row plus `A i` times the weights `W j`. -/
theorem accUpd_gtab (nm nregs : Nat) (sts : Nat → St F) (A W : Nat → F) :
    accUpd na (gtab na (16 * nm) nregs sts) (16 * nm) nm 0 A W = gtab na (16 * nm) nregs fun i ↦
      { sts i with acc := fun j ↦ (sts i).acc j + A i * W j } := by
  apply array_eq_of_getD _ _ 0 (by rw [size_accUpd, size_gtab, size_gtab])
  intro idx
  rw [getD_accUpd, size_gtab]
  unfold gtab
  by_cases hi : idx < 16 * nm * (na + nregs)
  · rw [getD_tab _ _ _ hi, getD_tab _ _ _ hi]
    have hB : 0 < 16 * nm := Nat.pos_of_ne_zero fun h ↦ by
      rw [h, Nat.zero_mul] at hi; omega
    have hlt := Nat.mod_lt idx hB
    by_cases h4 : idx < na * (16 * nm)
    · have hq : idx / (16 * nm) < na := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h4)
      simp only [hi, h4, hlt, true_or, and_self, ite_true, St.slot, hq]
    · have hq : ¬idx / (16 * nm) < na := fun hq ↦ h4 (by
        have := Nat.div_add_mod idx (16 * nm)
        have : idx / (16 * nm) * (16 * nm) + (16 * nm) ≤ na * (16 * nm) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hq
        have h3 : 16 * nm * (idx / (16 * nm)) = idx / (16 * nm) * (16 * nm) := Nat.mul_comm _ _
        omega)
      simp only [hi, h4, false_and, and_false, ite_false, St.slot, hq]
  · rw [Words.getD_eq_zero _ _ (by rw [size_tab]; omega),
      Words.getD_eq_zero _ _ (by rw [size_tab]; omega)]
    simp only [hi, false_and, ite_false]

/-! ### Instructions on a group -/

variable (p) in
theorem binG_SS (env : GroupEnv) (o : Op) (d : Nat) (x y : Nat) (s : ByteArray) :
    binG p env o d (.reg x) (.reg y) s =
      kSS (Op.wordG p o) env.nm s (regOff env d) (regOff env x) (regOff env y) := by
  cases o <;> rfl

variable (p) in
theorem binG_SE (env : GroupEnv) (o : Op) (d : Nat) (x y : Nat) (s : ByteArray) :
    binG p env o d (.reg x) (.cur y) s =
      kSE (Op.wordG p o) env.nm s env.view (regOff env d) (regOff env x) (colOff env y) := by
  cases o <;> rfl

variable (p) in
theorem binG_ES (env : GroupEnv) (o : Op) (d : Nat) (x y : Nat) (s : ByteArray) :
    binG p env o d (.cur x) (.reg y) s =
      kES (Op.wordG p o) env.nm s env.view (regOff env d) (colOff env x) (regOff env y) := by
  cases o <;> rfl

variable (p) in
theorem binG_EE (env : GroupEnv) (o : Op) (d : Nat) (x y : Nat) (s : ByteArray) :
    binG p env o d (.cur x) (.cur y) s =
      kEE (Op.wordG p o) env.nm s env.view (regOff env d) (colOff env x) (colOff env y) := by
  cases o <;> rfl

variable (p) in
theorem binG_SW (env : GroupEnv) (o : Op) (d : Nat) (x : Nat) (y : F) (s : ByteArray) :
    binG p env o d (.reg x) (.const y) s =
      kSW (Op.wordG p o) env.nm s (regOff env d) (regOff env x) y.val := by
  cases o <;> rfl

variable (p) in
theorem binG_EW (env : GroupEnv) (o : Op) (d : Nat) (x : Nat) (y : F) (s : ByteArray) :
    binG p env o d (.cur x) (.const y) s =
      kEW (Op.wordG p o) env.nm s env.view (regOff env d) (colOff env x) y.val := by
  cases o <;> rfl

variable (p) in
theorem binG_WS (env : GroupEnv) (o : Op) (d : Nat) (x : F) (y : Nat) (s : ByteArray) :
    binG p env o d (.const x) (.reg y) s =
      kWS (Op.wordG p o) env.nm s (regOff env d) (regOff env y) x.val := by
  cases o <;> rfl

variable (p) in
theorem binG_WE (env : GroupEnv) (o : Op) (d : Nat) (x : F) (y : Nat) (s : ByteArray) :
    binG p env o d (.const x) (.cur y) s =
      kWE (Op.wordG p o) env.nm s env.view (regOff env d) (colOff env y) x.val := by
  cases o <;> rfl

variable (p) in
theorem binG_WW (env : GroupEnv) (o : Op) (d : Nat) (x y : F) (s : ByteArray) :
    binG p env o d (.const x) (.const y) s = fill env.nm s (regOff env d)
        (Op.wordG p o x.val y.val) := by
  cases o <;> rfl

theorem regOff_toNat (B nregs r : Nat) (v : View) (L : Loads) (scal wts : Array UInt32)
    (hr : r < nregs) (hst : 4 * (B * (na + nregs)) < USize.size) :
    (regOff (blockEnv na B v L scal wts) r).toNat = B * (na + r) := by
  simp only [regOff, blockEnv]
  rcases Nat.eq_zero_or_pos B with h0 | h0
  · subst h0
    rw [USize.toNat_mul]
    simp
  · have h4 : B * (na + r) ≤ B * (na + nregs) := Nat.mul_le_mul_left B (by omega)
    have h5 : na + r ≤ B * (na + r) := Nat.le_mul_of_pos_left _ h0
    have h6 : B ≤ B * (na + nregs) := Nat.le_mul_of_pos_right B (by omega)
    have e1 : (na + r).toUSize.toNat = na + r := toUSize_toNat (by omega)
    have e2 : B.toUSize.toNat = B := toUSize_toNat (by omega)
    rw [usize_mul_toNat (by rw [e1, e2, Nat.mul_comm]; omega), e1, e2, Nat.mul_comm]

theorem colOff_toNat (B : Nat) (V : Array F) (cb cs c : Nat) (L : Loads) (scal wts : Array UInt32)
    (hc : cb + c * cs + B ≤ V.size) (hV : 4 * V.size < USize.size) :
    (colOff (blockEnv na B ⟨encode V, cb, cs⟩ L scal wts) c).toNat = cb + c * cs := by
  simp only [colOff, blockEnv]
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · subst h0
    have : (0 : Nat).toUSize * cs.toUSize = 0 := by
      apply USize.toNat_inj.mp; rw [USize.toNat_mul]; simp
    rw [this, usize_add_toNat (by rw [toUSize_toNat (by omega)]; simp; omega),
      toUSize_toNat (by omega)]
    simp
  · have hcs : cs ≤ c * cs := Nat.le_mul_of_pos_left cs h0
    have hc' : c ≤ c * cs ∨ cs = 0 := by
      rcases Nat.eq_zero_or_pos cs with h | h
      · exact Or.inr h
      · exact Or.inl (Nat.le_mul_of_pos_right c h)
    rcases hc' with hc' | hc'
    · rw [usize_add_toNat (by rw [toUSize_toNat (by omega), usize_mul_toNat (by
        rw [toUSize_toNat (by omega), toUSize_toNat (by omega)]; omega), toUSize_toNat (by omega),
        toUSize_toNat (by omega)]; omega), usize_mul_toNat (by
        rw [toUSize_toNat (by omega), toUSize_toNat (by omega)]; omega), toUSize_toNat (by omega),
        toUSize_toNat (by omega), toUSize_toNat (by omega)]
    · subst hc'
      have : c.toUSize * (0 : Nat).toUSize = 0 := by
        apply USize.toNat_inj.mp; rw [USize.toNat_mul]; simp
      rw [this, usize_add_toNat (by rw [toUSize_toNat (by omega)]; simp; omega),
        toUSize_toNat (by omega)]
      simp

theorem toUSize_toNat_of_le {n m : Nat} (h : n ≤ m) (hm : 4 * m < USize.size) :
    n.toUSize.toNat = n := toUSize_toNat (by omega)

theorem tcolOff_toNat (B c : Nat) (v : View) (L : Loads) (scal wts : Array UInt32) (n : Nat)
    (hc : c * B + B ≤ n) (hn : 4 * n < USize.size) :
    (tcolOff (blockEnv na B v L scal wts) c).toNat = c * B := by
  simp only [tcolOff, blockEnv]
  rcases Nat.eq_zero_or_pos B with h0 | h0
  · subst h0
    rw [usize_add_toNat (by rw [USize.toNat_mul]; simp), USize.toNat_mul]
    simp
  rcases Nat.eq_zero_or_pos c with c0 | c0
  · subst c0
    rw [usize_add_toNat (by rw [USize.toNat_mul]; simp), USize.toNat_mul]
    simp
  have h1 : c ≤ c * B := Nat.le_mul_of_pos_right c h0
  have h2 : B ≤ c * B := Nat.le_mul_of_pos_left B c0
  have e1 : c.toUSize.toNat = c := toUSize_toNat (by omega)
  have e2 : B.toUSize.toNat = B := toUSize_toNat (by omega)
  have e0 : (0 : USize).toNat = 0 := usize_numeral 0 (by decide)
  rw [usize_add_toNat (by rw [e0, usize_mul_toNat (by rw [e1, e2]; omega), e1, e2]; omega), e0,
    usize_mul_toNat (by rw [e1, e2]; omega), e1, e2, Nat.zero_add]

/-- Word `B s + k` of `B` rows' run states: slot `s` of row `k`. -/
theorem getD_gtab (B nregs : Nat) (sts : Nat → St F) (s k : Nat) (hs : s < na + nregs)
    (hk : k < B) : (gtab na B nregs sts).getD (B * s + k) 0 = (sts k).slot na s := by
  have hlt : B * s + k < B * (na + nregs) := by
    have : B * s + B ≤ B * (na + nregs) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left B (by omega)
    omega
  unfold gtab
  rw [getD_tab _ _ _ hlt]
  have hq : (B * s + k) / B = s := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk,
      Nat.zero_add]
  have hr : (B * s + k) % B = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  rw [hq, hr]

/-- Two registers' words are the same or apart. -/
theorem apart_regs (B x d : Nat) : Apart true (B * (na + x)) (B * (na + d)) B := fun _ ↦ by
  rcases Nat.lt_trichotomy x d with h | h | h
  · right; left
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left B (by omega)
  · left; rw [h]
  · right; right
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left B (by omega)

theorem scalAt_blockEnv (B : Nat) (v : View) (L : Loads) (SC : Array F) (wts : Array UInt32)
    (i : Nat) : scalAt (blockEnv na B v L (SC.map (·.val)) wts) i = (SC.getD i 0).val :=
  CompPoly.CPolynomial.NTTFast.Packed.getD_map_val SC i

theorem wtsOk_blockCtx (WT : Array F) (w : Nat) :
    WtsOk na (WT.map (·.val)) w fun j ↦ WT.getD (na * w + j) 0 := fun _ _ ↦
  CompPoly.CPolynomial.NTTFast.Packed.getD_map_val WT _

/-- The group of a block of `16 nm` rows: the block's view and loads, the scalars and weights. -/
abbrev groupOf (na nm : Nat) (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) :
    GroupEnv :=
  blockEnv na (16 * nm) ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val)) (WT.map (·.val))

theorem groupOf_nm (nm : Nat) (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) :
    (groupOf na nm V cb cs L SC WT).nm = nm := Nat.mul_div_cancel_left nm (by decide)

theorem groupOf_rb (nm : Nat) (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F)
    (h : 16 * nm < USize.size) : (groupOf na nm V cb cs L SC WT).rb.toNat = 16 * nm :=
  toUSize_toNat h

/-- **A load on a group** of `16 nm` rows in range is the load on every row's values. -/
theorem loadG_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) (nm nregs : Nat)
    (hst : 4 * (16 * nm * (na + nregs)) < USize.size) (hL : L.Addr) (sts : Nat → St F) (d : Nat)
    (src : Src) (hd : d < nregs) (hs : L.InRange (16 * nm) src) :
    loadG (groupOf na nm V cb cs L SC WT) d src (encode (gtab na (16 * nm) nregs sts)) =
      encode (gtab na (16 * nm) nregs fun i ↦ (sts i).setSlot na (na + d) (L.src (16 * nm) i src))
          := by
  obtain ⟨hM, hP, hPT, hQ, hQT, hPER, hFS, hLS, hTS⟩ := hL
  have hX : 4 * (gtab na (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
  have hrd : 16 * nm * (na + d) + 16 * nm ≤ (gtab na (16 * nm) nregs sts).size := by
    rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hro := regOff_toNat (16 * nm) nregs d ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val))
    (WT.map (·.val)) hd hst
  rw [← updR_gtab _ _ _ _ _]
  have hnm := groupOf_nm (na := na) nm V cb cs L SC WT
  cases src <;> simp only [LoadsF.InRange] at hs
  case next c =>
    simp only [loadG, hnm]
    exact gather_upd _ L.M nm _ c L.r0 L.next L.nseq _ hro hX hM hrd hs.1 hs.2
  case prepCur c =>
    simp only [loadG, hnm]
    exact copy_upd _ L.PT nm _ (c * (16 * nm)) _ _ hro (tcolOff_toNat _ c _ _ _ _ L.PT.size hs hPT)
      hX hPT hrd hs
  case prepNext c =>
    simp only [loadG, hnm]
    exact gather_upd _ L.P nm _ c L.r0 L.next L.nseq _ hro hX hP hrd hs.1 hs.2
  case permCur c =>
    simp only [loadG, hnm]
    exact copy_upd _ L.QT nm _ (c * (16 * nm)) _ _ hro (tcolOff_toNat _ c _ _ _ _ L.QT.size hs hQT)
      hX hQT hrd hs
  case permNext c =>
    simp only [loadG, hnm]
    exact gather_upd _ L.Q nm _ c L.r0 L.next L.nseq _ hro hX hQ hrd hs.1 hs.2
  case periodic j =>
    simp only [loadG, hnm]
    by_cases hj : j < L.PER.size
    · have hr := hs hj
      have hc : (L.PER.getD j #[]) ∈ L.PER := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
        exact Array.getElem_mem hj
      exact copyPer_upd _ L.PER nm _ j L.r0 _ _ hro
        (fun _ ↦ toUSize_toNat_of_le (show L.r0 ≤ (L.PER.getD j #[]).size by omega) (hPER _ hc))
        hX hPER hrd fun _ ↦ hr
    · exact copyPer_upd _ L.PER nm _ j L.r0 _ _ hro (fun h ↦ absurd h hj) hX hPER hrd
        fun h ↦ absurd h hj
  case isFirstRow =>
    simp only [loadG, hnm]
    exact copy_upd _ L.FS nm _ L.r0 _ _ hro (toUSize_toNat_of_le (n := L.r0) (m := L.FS.size)
        (by omega) hFS) hX hFS hrd hs
  case isLastRow =>
    simp only [loadG, hnm]
    exact copy_upd _ L.LS nm _ L.r0 _ _ hro (toUSize_toNat_of_le (n := L.r0) (m := L.LS.size)
        (by omega) hLS) hX hLS hrd hs
  case isTransition =>
    simp only [loadG, hnm]
    exact copy_upd _ L.TS nm _ L.r0 _ _ hro (toUSize_toNat_of_le (n := L.r0) (m := L.TS.size)
        (by omega) hTS) hX hTS hrd hs

theorem getD_gtab_reg (B nregs : Nat) (sts : Nat → St F) (r k : Nat) (hr : r < nregs)
    (hk : k < B) : (gtab na B nregs sts).getD (B * (na + r) + k) 0 = (sts k).reg r := by
  rw [getD_gtab _ _ _ _ _ (by omega) hk]
  simp only [St.slot, show ¬na + r < na by omega, ite_false, Nat.add_sub_cancel_left]

/-- **An operation on a group** of `16 nm` rows in range is the operation on every row's values. -/
theorem binG_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) (nm nregs : Nat)
    (hst : 4 * (16 * nm * (na + nregs)) < USize.size) (hV : 4 * V.size < USize.size)
    (sts : Nat → St F) (o : Op) (d : Nat) (a b : Opd F) (hd : d < nregs)
    (ha : a.InRange V cb cs (16 * nm) nregs) (hb : b.InRange V cb cs (16 * nm) nregs) :
    binG p (groupOf na nm V cb cs L SC WT) o d a b (encode (gtab na (16 * nm) nregs sts)) =
      encode (gtab na (16 * nm) nregs fun i ↦ (sts i).setSlot na (na + d)
        (o.eval (a.val (blockCtx na V cb cs L SC WT (16 * nm) i) (sts i))
          (b.val (blockCtx na V cb cs L SC WT (16 * nm) i) (sts i)))) := by
  have hX : 4 * (gtab na (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
  have hrd : ∀ r < nregs, 16 * nm * (na + r) + 16 * nm ≤ (gtab na (16 * nm) nregs sts).size := by
    intro r hr
    rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hro (r : Nat) (hr : r < nregs) := regOff_toNat (16 * nm) nregs r ⟨encode V, cb, cs⟩ L.enc
    (SC.map (·.val)) (WT.map (·.val)) hr hst
  have hco (c : Nat) (hc : cb + c * cs + 16 * nm ≤ V.size) := colOff_toNat (na := na) (16 * nm) V cb
      cs c
    L.enc (SC.map (·.val)) (WT.map (·.val)) hc hV
  have hnm := groupOf_nm (na := na) nm V cb cs L SC WT
  have hw := Op.wordG_val (p := p) o
  rw [← updR_gtab _ _ _ _ _]
  cases a with
  | reg x =>
    have hx : x < nregs := ha
    cases b with
    | reg y =>
      have hy : y < nregs := hb
      rw [binG_SS, hnm]
      exact groupsSS_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) _ _ _ _ (hro x hx)
        (hro y hy) (hrd x hx) (hrd y hy) (apart_regs _ _ _) (apart_regs _ _ _) fun k hk ↦ by
          rw [getD_gtab_reg _ _ _ _ _ hx hk, getD_gtab_reg _ _ _ _ _ hy hk]; rfl
    | cur y =>
      have hy : cb + y * cs + 16 * nm ≤ V.size := hb
      rw [binG_SE, hnm]
      exact groupsSE_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) V hV _ _ _ _ (hro x hx)
        (hco y hy) (hrd x hx) hy (apart_regs _ _ _) fun k hk ↦ by
          rw [getD_gtab_reg _ _ _ _ _ hx hk]; rfl
    | const y =>
      rw [binG_SW, hnm]
      exact groupsSW_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) _ _ (hro x hx) (hrd x hx)
        (apart_regs _ _ _) y fun k hk ↦ by rw [getD_gtab_reg _ _ _ _ _ hx hk]; rfl
  | cur x =>
    have hx : cb + x * cs + 16 * nm ≤ V.size := ha
    cases b with
    | reg y =>
      have hy : y < nregs := hb
      rw [binG_ES, hnm]
      exact groupsES_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) V hV _ _ _ _ (hco x hx)
        (hro y hy) hx (hrd y hy) (apart_regs _ _ _) fun k hk ↦ by
          rw [getD_gtab_reg _ _ _ _ _ hy hk]; rfl
    | cur y =>
      have hy : cb + y * cs + 16 * nm ≤ V.size := hb
      rw [binG_EE, hnm]
      exact groupsEE_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) V hV _ _ _ _ (hco x hx)
        (hco y hy) hx hy fun k hk ↦ rfl
    | const y =>
      rw [binG_EW, hnm]
      exact groupsEW_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) V hV _ _ (hco x hx) hx y
        fun k hk ↦ rfl
  | const x =>
    cases b with
    | reg y =>
      have hy : y < nregs := hb
      rw [binG_WS, hnm]
      exact groupsWS_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) _ _ (hro y hy) (hrd y hy)
        (apart_regs _ _ _) x fun k hk ↦ by rw [getD_gtab_reg _ _ _ _ _ hy hk]; rfl
    | cur y =>
      have hy : cb + y * cs + 16 * nm ≤ V.size := hb
      rw [binG_WE, hnm]
      exact groupsWE_upd _ o.eval hw _ nm _ _ _ (hro d hd) hX (hrd d hd) V hV _ _ (hco y hy) hy x
        fun k hk ↦ rfl
    | const y =>
      rw [binG_WW, hnm, hw]
      exact fill_upd _ nm _ _ (hro d hd) hX (hrd d hd) _

/-- **An accumulation on a group** of `16 nm` rows in range is the accumulation on every row's
values. -/
theorem accG_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) (nm nregs : Nat)
    (hna : 0 < na) (hst : 4 * (16 * nm * (na + nregs)) < USize.size) (hV : 4 * V.size < USize.size)
    (sts : Nat → St F) (a : Opd F) (w : Nat) (ha : a.InRange V cb cs (16 * nm) nregs) :
    accG p (groupOf na nm V cb cs L SC WT) a w (encode (gtab na (16 * nm) nregs sts)) =
      encode (gtab na (16 * nm) nregs fun i ↦
        (Instr.acc a w).exec (fieldMachine (blockCtx na V cb cs L SC WT (16 * nm) i)) (sts i)) := by
  have hX : 4 * (gtab na (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
  have hB : na * (16 * nm) ≤ (gtab na (16 * nm) nregs sts).size := by
    rw [size_gtab, Nat.mul_comm na]; exact Nat.mul_le_mul_left _ (by omega)
  have h16 : 16 * nm < USize.size := by
    have : 16 * nm ≤ 16 * nm * (na + nregs) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnm := groupOf_nm (na := na) nm V cb cs L SC WT
  have hrb := groupOf_rb (na := na) nm V cb cs L SC WT h16
  have hwt := wtsOk_blockCtx (na := na) WT w
  have e : (fun i ↦ (Instr.acc a w).exec (fieldMachine (blockCtx na V cb cs L SC WT (16 * nm) i))
      (sts i)) = fun i ↦ ⟨(sts i).reg, fun j ↦ (sts i).acc j +
        a.val (blockCtx na V cb cs L SC WT (16 * nm) i) (sts i) * WT.getD (na * w + j) 0⟩ :=
    funext fun _ ↦ rfl
  rw [e, ← accUpd_gtab]
  cases a with
  | reg r =>
    have hr : r < nregs := ha
    have hro := regOff_toNat (16 * nm) nregs r ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val))
      (WT.map (·.val)) hr hst
    have h4 : na * (16 * nm) ≤ 16 * nm * (na + r) := by
      rw [Nat.mul_comm na]; exact Nat.mul_le_mul_left _ (by omega)
    have h5 : 16 * nm * (na + r) + 16 * nm ≤ (gtab na (16 * nm) nregs sts).size := by
      rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    simp only [accG, hnm]
    exact accS_upd _ nm _ _ hX hB _ _ hrb _ hro h4 h5
      (fun k hk ↦ (getD_gtab_reg _ _ _ _ _ hr hk).symm) _ _ hwt
  | cur c =>
    have hc : cb + c * cs + 16 * nm ≤ V.size := ha
    simp only [accG, hnm]
    exact accE_upd _ V nm _ _ hX hV hB _ _ hrb _ (colOff_toNat (na := na) (16 * nm) V cb cs c L.enc
      (SC.map (·.val)) (WT.map (·.val)) hc hV) hc (fun k hk ↦ rfl) _ _ hwt
  | const c =>
    simp only [accG, hnm]
    exact accW_upd _ nm _ hX hB _ hrb h16 c _ _ hwt

/-- **An instruction on a group** of `16 nm` rows in range is the instruction on every row's
values (`blockCtx`). -/
theorem execGroup_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F)
    (nm nregs : Nat) (hna : 0 < na) (hst : 4 * (16 * nm * (na + nregs)) < USize.size)
    (hV : 4 * V.size < USize.size) (hL : L.Addr) (sts : Nat → St F) (ins : Instr F)
    (hin : ins.InRange V cb cs L (16 * nm) nregs) :
    ins.exec (groupMachine p (groupOf na nm V cb cs L SC WT)) (encode (gtab na (16 * nm) nregs sts))
        =
      encode (gtab na (16 * nm) nregs fun i ↦
        ins.exec (fieldMachine (blockCtx na V cb cs L SC WT (16 * nm) i)) (sts i)) := by
  cases ins with
  | load d src =>
    obtain ⟨hd, hs⟩ := hin
    refine (loadG_rel V cb cs L SC WT nm nregs hst hL sts d src hd hs).trans ?_
    refine congrArg (fun f ↦ encode (gtab na (16 * nm) nregs f)) (funext fun i ↦ ?_)
    rw [St.setSlot_reg, exec_load]
    rfl
  | scalar d k =>
    have hd : d < nregs := hin
    have hX : 4 * (gtab na (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
    show fill _ _ _ _ = _
    rw [groupOf_nm, scalAt_blockEnv, fill_upd _ nm _ _ (regOff_toNat (16 * nm) nregs d
      ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val)) (WT.map (·.val)) hd hst) hX (by
        rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)),
      updR_gtab _ _ _ _ _]
    refine congrArg (fun f ↦ encode (gtab na (16 * nm) nregs f)) (funext fun i ↦ ?_)
    rw [St.setSlot_reg, exec_scalar]
    rfl
  | bin o d a b =>
    obtain ⟨hd, ha, hb⟩ := hin
    refine (binG_rel V cb cs L SC WT nm nregs hst hV sts o d a b hd ha hb).trans ?_
    refine congrArg (fun f ↦ encode (gtab na (16 * nm) nregs f)) (funext fun i ↦ ?_)
    rw [St.setSlot_reg, exec_bin]
  | acc a w => exact accG_rel V cb cs L SC WT nm nregs hna hst hV sts a w hin

/-- **A program on a group** of `16 nm` rows in range runs the program on every row's values. -/
theorem runGroup_rel (code : Array (Instr F)) (V : Array F) (cb cs : Nat) (L : LoadsF p)
    (SC WT : Array F) (nm nregs : Nat) (hna : 0 < na)
    (hst : 4 * (16 * nm * (na + nregs)) < USize.size)
    (hV : 4 * V.size < USize.size) (hL : L.Addr) (sts : Nat → St F)
    (hcode : ∀ ins ∈ code, ins.InRange V cb cs L (16 * nm) nregs) :
    run (groupMachine p (groupOf na nm V cb cs L SC WT)) code (encode (gtab na (16 * nm) nregs sts))
        =
      encode (gtab na (16 * nm) nregs fun i ↦
        run (fieldMachine (blockCtx na V cb cs L SC WT (16 * nm) i)) code (sts i)) := by
  simp only [run, ← Array.foldl_toList]
  have hcode' : ∀ ins ∈ code.toList, ins.InRange V cb cs L (16 * nm) nregs := fun i hi ↦
    hcode i (Array.mem_toList_iff.mp hi)
  generalize code.toList = l at hcode'
  induction l generalizing sts with
  | nil => rfl
  | cons ins l ih =>
    simp only [List.foldl_cons]
    rw [execGroup_rel V cb cs L SC WT nm nregs hna hst hV hL sts ins (hcode' ins
        List.mem_cons_self)]
    exact ih _ fun i hi ↦ hcode' i (List.mem_cons_of_mem _ hi)

/-- A group's state whose words are encoded run states. -/
def GEncoded (na B nregs : Nat) (st : ByteArray) : Prop :=
  ∃ sts : Nat → St F, st = encode (gtab na B nregs sts)

theorem clearAccs_rel (nm nregs : Nat) (hst : 4 * (16 * nm * (na + nregs)) < USize.size)
    (sts : Nat → St F) :
    clearAccs na (16 * nm) (encode (gtab na (16 * nm) nregs sts)) = encode (gtab na (16 * nm) nregs
      fun i ↦ ⟨(sts i).reg, fun _ ↦ 0⟩) := by
  have hnm : 16 * nm / 16 = nm := Nat.mul_div_cancel_left nm (by decide)
  have key : ∀ M ≤ na, (List.range M).foldl (fun st j ↦ fill (16 * nm / 16) st
      (j * (16 * nm)).toUSize 0) (encode (gtab na (16 * nm) nregs sts)) =
      encode (gtab na (16 * nm) nregs fun i ↦
        ⟨(sts i).reg, fun j ↦ if j < M then 0 else (sts i).acc j⟩) := by
    intro M hM
    induction M with
    | zero =>
      refine congrArg encode (tab_congr fun idx _ ↦ ?_)
      simp only [St.slot, Nat.not_lt_zero, ite_false]
    | succ M ih =>
      have hMB : 16 * nm * M + 16 * nm ≤ 16 * nm * (na + nregs) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil, hnm,
        show (0 : UInt32) = (0 : F).val from rfl, fill_upd _ nm (16 * nm * M) _ (by
          rw [toUSize_toNat (by rw [Nat.mul_comm]; omega), Nat.mul_comm])
        (by rw [size_gtab]; exact hst) (by rw [size_gtab]; omega), updR_gtab _ _ _ _ _]
      refine congrArg encode (tab_congr fun idx _ ↦ ?_)
      rw [St.slot_setSlot]
      generalize idx / (16 * nm) = q
      by_cases e : q = M
      · subst e; simp only [ite_true, St.slot, show q < na by omega, show q < q + 1 by omega]
      · simp only [e, ite_false, St.slot]
        split
        · by_cases hq : q < M
          · simp only [hq, show q < M + 1 by omega, ite_true]
          · simp only [hq, show ¬q < M + 1 by omega, ite_false]
        · rfl
  unfold clearAccs
  rw [key na le_rfl]
  refine congrArg encode (tab_congr fun idx _ ↦ ?_)
  simp only [St.slot]
  split
  · simp only [*]
  · rfl

/-- **A program accumulating every row** on a group of `B` rows (`B` a multiple of sixteen), from
cleared accumulators and any encoded registers: the accumulators hold its rows' accumulations. -/
theorem groupBlock_acc (code : Array (Instr F)) (nregs : Nat) (V : Array F) (cb cs : Nat)
    (L : LoadsF p) (SC WT : Array F) (B : Nat) (hB : B % 16 = 0) (hna : 0 < na)
    (hst : 4 * (B * (na + nregs)) < USize.size) (hV : 4 * V.size < USize.size) (hL : L.Addr)
    (hcode : ∀ ins ∈ code, ins.InRange V cb cs L B nregs) (Q : Nat → Nat → F)
    (hQ : ∀ i < B, ∀ st0 : St F, st0.acc = (fun _ ↦ 0) → ∀ j < na,
      (run (fieldMachine (blockCtx na V cb cs L SC WT B i)) code st0).acc j = Q i j)
    (st : ByteArray) (h : GEncoded (p := p) na B nregs st) :
    let st' := run (groupMachine p (blockEnv na B ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val))
      (WT.map (·.val)))) code (clearAccs na B st)
    GEncoded (p := p) na B nregs st' ∧ ∀ j < na, ∀ i < B, read st' (B * j + i) = (Q i j).val := by
  obtain ⟨nm, rfl⟩ : ∃ nm, B = 16 * nm := ⟨B / 16, by omega⟩
  obtain ⟨sts, rfl⟩ := h
  dsimp only
  rw [clearAccs_rel nm nregs hst sts]
  have e := runGroup_rel code V cb cs L SC WT nm nregs hna hst hV hL
    (fun i ↦ ⟨(sts i).reg, fun _ ↦ 0⟩) hcode
  simp only [groupOf] at e
  rw [e]
  refine ⟨⟨_, rfl⟩, fun j hj i hi ↦ ?_⟩
  rw [Words.read_encode _ _ (by rw [size_gtab]; exact hst) (by
      rw [size_gtab]
      have : 16 * nm * j + 16 * nm ≤ 16 * nm * (na + nregs) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega),
    getD_gtab _ _ _ _ _ (by omega) hi]
  simp only [St.slot, hj, ite_true]
  rw [hQ i hi _ rfl j hj]

theorem gEncoded_zeros (B nregs : Nat) :
    GEncoded (p := p) na B nregs (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords
      (B * (na + nregs))) := by
  refine ⟨fun _ ↦ ⟨fun _ ↦ 0, fun _ ↦ 0⟩, ?_⟩
  rw [Words.zeroWords_eq (p := p)]
  refine congrArg encode (Array.ext (by rw [Array.size_replicate, size_gtab]) fun i h1 h2 ↦ ?_)
  simp only [Array.getElem_replicate, gtab, tab, Array.getElem_ofFn, St.slot]
  split <;> rfl

end CompStark.Stark.Prog
