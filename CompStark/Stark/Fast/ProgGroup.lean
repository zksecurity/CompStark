/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgGroup
public import CompStark.Stark.Fast.ProgWords

/-! # Programs on groups of rows compute the field's values

On encoded field arrays, a kernel of the group machine (`CompStark/Stark/ProgGroup.lean`) overwrites
a range of the state, sixteen words at a time, with the operation on its operands' words
(`groups_upd`, `lanes_upd`), or adds an operand times four weights to the four accumulators
(`accS_upd` and its kin). So an instruction on a group of `B` rows is the instruction on each row's
values (`execGroup_rel`, on the rows' values `blockCtx`), and so is a program (`runGroup_rel`): the
group machine simulates `B` runs on the field.
-/

@[expose] public section
namespace CompStark.Stark.Prog
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul add_val sub_val mul_val reduceOnce_eq sub_eq
  size_encode_fields splice getD_splice size_splice lit16 getD_lit16 size_lit16
  array_eq_of_getD)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write16U toNat_usize_le
  usize_add_toNat_of_le)
open Montgomery.Native32
open CompStark.Stark.Fast (tab size_tab tab_congr getD_tab)

variable {p : ℕ} [P : Mont32Field p]

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

/-- Sixteen words from word `i` of a buffer that fits machine indices are in its window. -/
theorem withWin_pos {α : Type} (b : ByteArray) (i : USize) (d : α) (k : Win b i → α)
    (h1 : 4 * (i.toNat + 16) ≤ b.size) (h2 : b.size < USize.size) :
    withWin b i d k = k ⟨h1, Nat.lt_of_le_of_lt h1 h2⟩ := by
  unfold withWin
  have h16 : (16 : USize).toNat = 16 := usize_numeral 16 (by decide)
  have hi : (i + 16).toNat = i.toNat + 16 := by
    rw [usize_add_toNat (by rw [h16]; omega), h16]
  have hu : b.usize.toNat = b.size := by
    rw [ByteArray.usize, toUSize_toNat h2]
  have h6 : (2 : USize).toNat % System.Platform.numBits = 2 := by
    rw [usize_numeral 2 (by decide)]; rcases System.Platform.numBits_eq with e | e <;> rw [e]
  have c1 : i ≤ i + (16 : USize) := USize.le_iff_toNat_le.mpr (by rw [hi]; omega)
  have c2 : i + (16 : USize) ≤ b.usize >>> (2 : USize) := by
    apply USize.le_iff_toNat_le.mpr
    rw [hi, USize.toNat_shiftRight, h6, Nat.shiftRight_eq_div_pow, hu]
    omega
  rw [dite_eq_left ⟨c1, c2⟩]

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

/-- The Montgomery quotients `q₁ = L n` of `mul` and `q₂ = L (-n)` of `mulM`, with `n m ≡ -1`
modulo `2 ^ 32`: `L + q₁ m ≡ 0` and `q₁ + q₂ ≡ 0`. -/
theorem mont_quotients (L n m : Nat) (hn : n < 2 ^ 32) (hnp : n * m % 2 ^ 32 = 2 ^ 32 - 1) :
    (L + L * n % 2 ^ 32 * m) % 2 ^ 32 = 0 ∧
      (L * n % 2 ^ 32 + L * ((2 ^ 32 - n) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = 0 := by
  constructor
  · have h1 : L * n % 2 ^ 32 * m ≡ L * (2 ^ 32 - 1) [MOD 2 ^ 32] := by
      rw [show L * (2 ^ 32 - 1) = L * ((n * m) % 2 ^ 32) by rw [hnp]]
      refine Nat.ModEq.trans (Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)) ?_
      rw [Nat.mul_assoc]
      exact Nat.ModEq.mul_left _ (Nat.mod_modEq _ _).symm
    have h2 := Nat.ModEq.add_left L h1
    have h3 : L + L * (2 ^ 32 - 1) = L * 2 ^ 32 := by
      have h4 : L ≤ L * 2 ^ 32 := Nat.le_mul_of_pos_right L (by decide)
      rw [Nat.mul_sub, Nat.mul_one]
      omega
    rw [h3] at h2
    rw [h2, Nat.mul_mod_left]
  · have h1 : L * n % 2 ^ 32 + L * ((2 ^ 32 - n) % 2 ^ 32) % 2 ^ 32 ≡
        L * n + L * (2 ^ 32 - n) [MOD 2 ^ 32] :=
      Nat.ModEq.add (Nat.mod_modEq _ _)
        (Nat.ModEq.trans (Nat.mod_modEq _ _) (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)))
    rw [← Nat.mul_add, Nat.add_sub_cancel' hn.le] at h1
    rw [h1, Nat.mul_mod_left]

/-- `mulM` is `mul` on canonical residues. -/
theorem mulM_eq (x y : UInt32) (hx : x.toNat < p) (hy : y.toNat < p) :
    mulM p x y = mul p x y := by
  have hp31 := P.modulus_lt_two_pow_31
  have hp32 := P.modulus32_toNat
  have hp64 := P.modulus64_toNat
  have hp2 := P.two_lt_modulus
  have hnp := P.montgomeryNegInv_mul_modulus_mod_two_pow_32
  have hn := P.montgomeryNegInv.toNat_lt
  set n := P.montgomeryNegInv.toNat with hn_def
  have hz : x.toNat * y.toNat < p * 2 ^ 32 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx hy.le (by omega))
      (Nat.mul_le_mul_left _ (by omega))
  set z := x.toNat * y.toNat with hz_def
  have hz64 : (x.toUInt64 * y.toUInt64).toNat = z := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (by omega)
  set L := z % 2 ^ 32 with hL
  set q1 := L * n % 2 ^ 32 with hq1
  set q2 := L * ((2 ^ 32 - n) % 2 ^ 32) % 2 ^ 32 with hq2
  obtain ⟨c1, c2⟩ := mont_quotients L n p hn hnp
  rw [← hq1, ← hq2] at c2
  rw [← hq1] at c1
  have hq1R : q1 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hq2R : q2 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hq1p : q1 * p < 2 ^ 32 * p := Nat.mul_lt_mul_of_pos_right hq1R (by omega)
  -- `mul`
  have hA : (mul p x y).toNat = if (z + q1 * p) / 2 ^ 32 < p then (z + q1 * p) / 2 ^ 32
      else (z + q1 * p) / 2 ^ 32 - p := by
    have hS : (((x.toUInt64 * y.toUInt64 + ((x.toUInt64 * y.toUInt64).toUInt32 *
        P.montgomeryNegInv).toUInt64 * P.modulus64) >>> 32).toUInt32).toNat =
        (z + q1 * p) / 2 ^ 32 := by
      have e32 : (32 : UInt64).toNat % 64 = 32 := rfl
      have hz' : x.toNat * y.toNat % 2 ^ 64 = z := Nat.mod_eq_of_lt (by omega)
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_add,
        UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, e32, hz', hp64, ← hL]
      rw [Nat.mod_eq_of_lt (show q1 * p < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show z + q1 * p < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    rw [CompPoly.CPolynomial.NTTFast.Packed.mul, reduceOnce_eq]
    split
    · rename_i h
      rw [UInt32.lt_iff_toNat_lt, hS, hp32] at h
      rw [hS, ite_eq_left h]
    · rename_i h
      rw [UInt32.lt_iff_toNat_lt, hS, hp32] at h
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hS, hp32]; omega)), hS,
        hp32, ite_eq_right h]
  -- `mulM`
  have hB : (mulM p x y).toNat = if (q2 * p) / 2 ^ 32 ≤ z / 2 ^ 32 then
      z / 2 ^ 32 - (q2 * p) / 2 ^ 32 else z / 2 ^ 32 + p - (q2 * p) / 2 ^ 32 := by
    have hq2p : q2 * p < 2 ^ 32 * p := Nat.mul_lt_mul_of_pos_right hq2R (by omega)
    have hH : ((x.toUInt64 * y.toUInt64) >>> 32).toUInt32.toNat = z / 2 ^ 32 := by
      have e32 : (32 : UInt64).toNat % 64 = 32 := rfl
      rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hz64, e32, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have hH2 : ((((x.toUInt64 * y.toUInt64).toUInt32 * (0 - P.montgomeryNegInv)).toUInt64 *
        P.modulus64) >>> 32).toUInt32.toNat = q2 * p / 2 ^ 32 := by
      have e32 : (32 : UInt64).toNat % 64 = 32 := rfl
      have hz' : x.toNat * y.toNat % 2 ^ 64 = z := Nat.mod_eq_of_lt (by omega)
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_mul,
        UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt32.toNat_sub, UInt32.toNat_zero, Nat.add_zero,
        e32, hz', hp64, ← hL, ← hn_def, ← hq2]
      rw [Nat.mod_eq_of_lt (show q2 * p < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    unfold mulM
    dsimp only
    rw [sub_eq _ _ (by rw [hH]; omega) (by rw [hH2]; omega)]
    split
    · rename_i h
      rw [UInt32.le_iff_toNat_le, hH, hH2] at h
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hH, hH2]; omega)), hH,
        hH2, ite_eq_left h]
    · rename_i h
      rw [UInt32.le_iff_toNat_le, hH, hH2] at h
      have hs : (((x.toUInt64 * y.toUInt64) >>> 32).toUInt32 + P.modulus32).toNat =
          z / 2 ^ 32 + p := by
        rw [UInt32.toNat_add, hH, hp32]; exact Nat.mod_eq_of_lt (by omega)
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hs, hH2]; omega)), hs,
        hH2, ite_eq_right h]
  apply UInt32.toNat_inj.mp
  rw [hA, hB]
  have hzL : z = z / 2 ^ 32 * 2 ^ 32 + L := by omega
  rcases Nat.eq_zero_or_pos q1 with h0 | h0
  · have hq20 : q2 = 0 := by omega
    have hL0 : L = 0 := by rw [h0, Nat.zero_mul, Nat.add_zero] at c1; omega
    rw [h0, hq20, Nat.zero_mul, Nat.add_zero, Nat.zero_div]
    split <;> split <;> omega
  · have hq2' : q2 = 2 ^ 32 - q1 := by omega
    have hQ2 : q2 * p = 2 ^ 32 * p - q1 * p := by rw [hq2', Nat.sub_mul]
    have hp1 : p ≤ q1 * p := Nat.le_mul_of_pos_left p h0
    rw [hQ2]
    split <;> split <;> omega

/-- `mulM` is the carrier's verified multiplication. -/
theorem mulM_val (x y : F) : mulM p x.val y.val = (x * y).val := by
  rw [mulM_eq _ _ x.property y.property, mul_val]

theorem Op.wordG_val (o : Op) (x y : F) : Op.wordG p o x.val y.val = (o.eval x y).val := by
  cases o
  · exact add_val x y
  · exact sub_val x y
  · exact mulM_val x y

/-! ### Passes over a group -/

/-- `groups` from offset `16 m` runs the steps of offsets `16 m, …, 16 (m + j - 1)`. -/
theorem groups_succ (step : ByteArray → USize → ByteArray) (j : Nat) (s : ByteArray) (o : USize) :
    groups step (j + 1) s o = groups step j (step s o) (o + 16) := rfl

theorem usize16 (m : Nat) (h : 16 * (m + 1) < USize.size) :
    (16 * m).toUSize + 16 = (16 * (m + 1)).toUSize := by
  apply USize.toNat_inj.mp
  have h16 : (16 : USize).toNat = 16 := usize_numeral 16 (by decide)
  rw [usize_add_toNat (by rw [h16, toUSize_toNat (by omega)]; omega), h16, toUSize_toNat (by omega),
    toUSize_toNat h]
  ring

/-- **A pass over a group**: steps taking the state through `Z 0, Z 1, …, Z nm`. -/
theorem groups_states (step : ByteArray → USize → ByteArray) (nm : Nat) (Z : Nat → ByteArray)
    (hnm : 16 * nm < USize.size)
    (hstep : ∀ m < nm, step (Z m) (16 * m).toUSize = Z (m + 1)) :
    groups step nm (Z 0) 0 = Z nm := by
  suffices h : ∀ j m, m + j = nm → groups step j (Z m) (16 * m).toUSize = Z nm by
    have e : (16 * 0 : Nat).toUSize = 0 := rfl
    have := h nm 0 (by omega)
    rwa [e] at this
  intro j
  induction j with
  | zero => intro m hm; subst hm; rfl
  | succ j ih =>
    intro m hm
    rw [groups_succ, hstep m (by omega), usize16 m (by omega)]
    exact ih (m + 1) (by omega)

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
theorem pass_upd (step : ByteArray → USize → ByteArray) (f : UInt32 → UInt32 → UInt32)
    (g : F → F → F) (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat)
    (G : Nat → F) (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
    (hrd : od + 16 * nm ≤ X.size) (xv yv : Nat → F) (hG : ∀ k < 16 * nm, G k = g (xv k) (yv k))
    (hstep : ∀ m < nm, ∃ x y : (k : Nat) → k ≤ 15 → UInt32,
      (∀ k hk, x k hk = (xv (16 * m + k)).val) ∧ (∀ k hk, y k hk = (yv (16 * m + k)).val) ∧
        step (encode (updR X od (16 * m) G)) (16 * m).toUSize =
          lanes16 f x y (encode (updR X od (16 * m) G)) (d + (16 * m).toUSize)) :
    groups step nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  have h := groups_states step nm (fun m ↦ encode (updR X od (16 * m) G)) (by omega) fun m hm ↦ by
    obtain ⟨x, y, hx, hy, e⟩ := hstep m hm
    rw [e, show 16 * (m + 1) = 16 * m + 16 by ring]
    refine lanes_upd f X od (16 * m) G x y (fun k ↦ xv (16 * m + k)) (fun k ↦ yv (16 * m + k)) g
      hf hx hy (fun t ht ↦ (hG _ (by omega)).symm) _ ?_ hX (by omega)
    rw [usize_add_toNat (by rw [toUSize_toNat (by omega)]; omega), toUSize_toNat (by omega), hd]
  simpa only [Nat.mul_zero, updR_zero] using h

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
    groups (stepSS f d a b) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd _ _ hG fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk,
      fun k hk ↦ ld _ _ (winS' X od ob m nm G b hb hX hrb hm) k hk,
      fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk,
      fun k hk ↦ ldS_upd X od ob m nm G b hb hX hrb hm hAb _ k hk, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepSS
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winS X od oa m nm G a ha hX hra hm).1
    (winS X od oa m nm G a ha hX hra hm).2, withWin_pos _ _ _ _
    (winS X od ob m nm G b hb hX hrb hm).1 (winS X od ob m nm G b hb hX hrb hm).2]
  rw [st16_eq _ _ _ hw.2]
  rfl

theorem groupsSE_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size)
        (oa ob : Nat) (a b : USize)
    (ha : a.toNat = oa) (hb : b.toNat = ob) (hra : oa + 16 * nm ≤ X.size)
    (hrb : ob + 16 * nm ≤ E.size) (hAa : Apart true oa od (16 * nm))
    (hG : ∀ k < 16 * nm, G k = g (X.getD (oa + k) 0) (E.getD (ob + k) 0)) :
    groups (stepSE f (encode E) d a b) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd _ _ hG fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk,
      fun k hk ↦ ld _ _ (winE' E ob m b hb hE (by omega)) k hk,
      fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk,
      fun k hk ↦ ldE_val E ob m b hb hE (by omega) _ k hk, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepSE
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winS X od oa m nm G a ha hX hra hm).1
    (winS X od oa m nm G a ha hX hra hm).2, withWin_pos _ _ _ _
    (winE E ob m b hb hE (by omega)).1 (winE E ob m b hb hE (by omega)).2]
  rw [st16_eq _ _ _ hw.2]
  rfl

theorem groupsES_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size)
        (oa ob : Nat) (a b : USize)
    (ha : a.toNat = oa) (hb : b.toNat = ob) (hra : oa + 16 * nm ≤ E.size)
    (hrb : ob + 16 * nm ≤ X.size) (hAb : Apart true ob od (16 * nm))
    (hG : ∀ k < 16 * nm, G k = g (E.getD (oa + k) 0) (X.getD (ob + k) 0)) :
    groups (stepES f (encode E) d a b) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd _ _ hG fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk,
      fun k hk ↦ ld _ _ (winS' X od ob m nm G b hb hX hrb hm) k hk,
      fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk,
      fun k hk ↦ ldS_upd X od ob m nm G b hb hX hrb hm hAb _ k hk, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepES
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winE E oa m a ha hE (by omega)).1
    (winE E oa m a ha hE (by omega)).2, withWin_pos _ _ _ _
    (winS X od ob m nm G b hb hX hrb hm).1 (winS X od ob m nm G b hb hX hrb hm).2]
  rw [st16_eq _ _ _ hw.2]
  rfl

theorem groupsEE_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size)
        (oa ob : Nat) (a b : USize)
    (ha : a.toNat = oa) (hb : b.toNat = ob) (hra : oa + 16 * nm ≤ E.size)
    (hrb : ob + 16 * nm ≤ E.size)
    (hG : ∀ k < 16 * nm, G k = g (E.getD (oa + k) 0) (E.getD (ob + k) 0)) :
    groups (stepEE f (encode E) d a b) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd _ _ hG fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk,
      fun k hk ↦ ld _ _ (winE' E ob m b hb hE (by omega)) k hk,
      fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk,
      fun k hk ↦ ldE_val E ob m b hb hE (by omega) _ k hk, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepEE
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winE E oa m a ha hE (by omega)).1
    (winE E oa m a ha hE (by omega)).2, withWin_pos _ _ _ _
    (winE E ob m b hb hE (by omega)).1 (winE E ob m b hb hE (by omega)).2]
  rw [st16_eq _ _ _ hw.2]
  rfl

theorem groupsSW_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (oa : Nat) (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ X.size)
    (hAa : Apart true oa od (16 * nm)) (c : F) (hG : ∀ k < 16 * nm, G k = g (X.getD (oa + k) 0) c) :
    groups (stepSW f d a c.val) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd _ (fun _ ↦ c) hG fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk, fun _ _ ↦ c.val,
      fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk, fun _ _ ↦ rfl, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepSW
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winS X od oa m nm G a ha hX hra hm).1
    (winS X od oa m nm G a ha hX hra hm).2]
  rw [st16_eq _ _ _ hw.2]
  rfl

theorem groupsEW_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size) (oa : Nat)
        (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ E.size) (c : F)
    (hG : ∀ k < 16 * nm, G k = g (E.getD (oa + k) 0) c) :
    groups (stepEW f (encode E) d a c.val) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd _ (fun _ ↦ c) hG fun m hm ↦ ?_
  refine ⟨fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk, fun _ _ ↦ c.val,
      fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk, fun _ _ ↦ rfl, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepEW
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winE E oa m a ha hE (by omega)).1
    (winE E oa m a ha hE (by omega)).2]
  rw [st16_eq _ _ _ hw.2]
  rfl

theorem groupsWS_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (oa : Nat) (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ X.size)
    (hAa : Apart true oa od (16 * nm)) (c : F) (hG : ∀ k < 16 * nm, G k = g c (X.getD (oa + k) 0)) :
    groups (stepWS f d a c.val) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd (fun _ ↦ c) _ hG fun m hm ↦ ?_
  refine ⟨fun _ _ ↦ c.val, fun k hk ↦ ld _ _ (winS' X od oa m nm G a ha hX hra hm) k hk,
      fun _ _ ↦ rfl, fun k hk ↦ ldS_upd X od oa m nm G a ha hX hra hm hAa _ k hk, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepWS
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winS X od oa m nm G a ha hX hra hm).1
    (winS X od oa m nm G a ha hX hra hm).2]
  rw [st16_eq _ _ _ hw.2]
  rfl

theorem groupsWE_upd (f : UInt32 → UInt32 → UInt32) (g : F → F → F)
    (hf : ∀ x y : F, f x.val y.val = (g x y).val) (X : Array F) (nm od : Nat) (G : Nat → F)
    (d : USize) (hd : d.toNat = od) (hX : 4 * X.size < USize.size)
        (hrd : od + 16 * nm ≤ X.size) (E : Array F) (hE : 4 * E.size < USize.size) (oa : Nat)
        (a : USize)
    (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ E.size) (c : F)
    (hG : ∀ k < 16 * nm, G k = g c (E.getD (oa + k) 0)) :
    groups (stepWE f (encode E) d a c.val) nm (encode X) 0 = encode (updR X od (16 * nm) G) := by
  refine pass_upd _ f g hf X nm od G d hd hX hrd (fun _ ↦ c) _ hG fun m hm ↦ ?_
  refine ⟨fun _ _ ↦ c.val, fun k hk ↦ ld _ _ (winE' E oa m a ha hE (by omega)) k hk,
      fun _ _ ↦ rfl, fun k hk ↦ ldE_val E oa m a ha hE (by omega) _ k hk, ?_⟩
  have hw := winS X od od m nm G d hd hX hrd hm
  unfold stepWE
  rw [withWin_pos _ _ _ _ hw.1 hw.2, withWin_pos _ _ _ _ (winE E oa m a ha hE (by omega)).1
    (winE E oa m a ha hE (by omega)).2]
  rw [st16_eq _ _ _ hw.2]
  rfl


/-! ### Accumulations -/

/-- Word `idx` of `accUpd`. -/
def accF (X : Array F) (B m c : Nat) (A W : Nat → F) (idx : Nat) : F :=
  if idx < 4 * B ∧ (idx % B < 16 * m ∨ (idx / B < c ∧ idx % B < 16 * m + 16))
  then X.getD idx 0 + A (idx % B) * W (idx / B) else X.getD idx 0

/-- The state with the four accumulators of `B` rows, words `0, …, 4 B - 1`, plus `A i` times the
weights `W j`: of rows `i < 16 m`, and of rows `i < 16 m + 16` of accumulators `j < c`. -/
def accUpd (X : Array F) (B m c : Nat) (A W : Nat → F) : Array F :=
  Array.ofFn (n := X.size) fun idx ↦ accF X B m c A W idx.val

theorem getD_accUpd (X : Array F) (B m c : Nat) (A W : Nat → F) (idx : Nat) :
    (accUpd X B m c A W).getD idx 0 = if idx < X.size ∧ idx < 4 * B ∧
      (idx % B < 16 * m ∨ (idx / B < c ∧ idx % B < 16 * m + 16))
    then X.getD idx 0 + A (idx % B) * W (idx / B) else X.getD idx 0 := by
  unfold accUpd
  rw [Words.getD_ofFn X.size]
  by_cases h : idx < X.size
  · simp only [h, true_and, ite_true, accF]
  · simp only [h, false_and, ite_false]
    exact (Words.getD_eq_zero X idx (by omega)).symm

@[simp] theorem size_accUpd (X : Array F) (B m c : Nat) (A W : Nat → F) :
    (accUpd X B m c A W).size = X.size := Array.size_ofFn

theorem accUpd_zero (X : Array F) (B : Nat) (A W : Nat → F) : accUpd X B 0 0 A W = X := by
  apply array_eq_of_getD _ _ 0 (size_accUpd ..)
  intro idx
  rw [getD_accUpd]
  simp only [Nat.mul_zero, Nat.not_lt_zero, false_and, false_or, and_false, ite_false]

theorem accUpd_next (X : Array F) (B m : Nat) (A W : Nat → F) :
    accUpd X B m 4 A W = accUpd X B (m + 1) 0 A W := by
  apply array_eq_of_getD _ _ 0 (by simp only [size_accUpd])
  intro idx
  rw [getD_accUpd, getD_accUpd]
  by_cases h : idx < X.size ∧ idx < 4 * B
  · have h4 : idx / B < 4 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hlt := Nat.mod_lt idx (show 0 < B by omega)
    have e : (idx % B < 16 * m ∨ (idx / B < 4 ∧ idx % B < 16 * m + 16)) ↔
        (idx % B < 16 * (m + 1) ∨ (idx / B < 0 ∧ idx % B < 16 * (m + 1) + 16)) := by
      constructor
      · rintro (a | ⟨-, b⟩) <;> left <;> omega
      · rintro (a | ⟨b, -⟩)
        · by_cases c : idx % B < 16 * m
          · exact Or.inl c
          · exact Or.inr ⟨h4, by omega⟩
        · exact absurd b (Nat.not_lt_zero _)
    simp only [h, true_and, e]
  · simp only [show ¬(idx < X.size ∧ idx < 4 * B ∧ _) from fun h' ↦ h ⟨h'.1, h'.2.1⟩, ite_false]

/-- Sixteen rows more of accumulator `j`. -/
theorem splice_accUpd (X : Array F) (B m j : Nat) (A W : Nat → F) (hj : j < 4)
    (hm : 16 * m + 16 ≤ B) (hX : 4 * B ≤ X.size) :
    splice (accUpd X B m j A W) (j * B + 16 * m) (lit16 fun t ↦
        X.getD (j * B + 16 * m + t) 0 + A (16 * m + t) * W j) = accUpd X B m (j + 1) A W := by
  have hB : 0 < B := by omega
  have hjB : j * B + B ≤ 4 * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  have hs : j * B + 16 * m + (lit16 fun t ↦
      X.getD (j * B + 16 * m + t) 0 + A (16 * m + t) * W j).size ≤ (accUpd X B m j A W).size := by
    rw [size_lit16, size_accUpd]
    omega
  apply array_eq_of_getD _ _ 0 (by rw [size_splice _ _ _ hs, size_accUpd, size_accUpd])
  intro idx
  have hdm := Nat.div_add_mod idx B
  have hlt := Nat.mod_lt idx hB
  have hcomm : B * (idx / B) = idx / B * B := Nat.mul_comm _ _
  rw [getD_splice _ _ _ hs, size_lit16, getD_accUpd, getD_accUpd]
  by_cases h1 : idx < j * B + 16 * m
  · have e : (idx % B < 16 * m ∨ (idx / B < j ∧ idx % B < 16 * m + 16)) ↔
        (idx % B < 16 * m ∨ (idx / B < j + 1 ∧ idx % B < 16 * m + 16)) := by
      constructor
      · rintro (a | ⟨b, c⟩)
        · exact Or.inl a
        · exact Or.inr ⟨by omega, c⟩
      · rintro (a | ⟨b, c⟩)
        · exact Or.inl a
        · by_cases q : idx / B = j
          · left
            rw [q] at hcomm hdm
            have : j * B ≤ idx := by rw [← hcomm]; omega
            omega
          · exact Or.inr ⟨by omega, c⟩
    simp only [h1, ite_true, e]
  · by_cases h2 : idx < j * B + 16 * m + 16
    · have hq : idx / B = j := Nat.div_eq_of_lt_le (by omega)
        (by rw [Nat.add_mul, Nat.one_mul]; omega)
      have hr : idx % B = 16 * m + (idx - (j * B + 16 * m)) := by
        rw [hq] at hcomm hdm
        omega
      simp only [h1, h2, ite_false, ite_true]
      rw [getD_lit16 _ _ (by omega), ite_eq_left ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩,
        hq, hr, show j * B + 16 * m + (idx - (j * B + 16 * m)) = idx by omega]
    · have e : (idx % B < 16 * m ∨ (idx / B < j ∧ idx % B < 16 * m + 16)) ↔
          (idx % B < 16 * m ∨ (idx / B < j + 1 ∧ idx % B < 16 * m + 16)) := by
        constructor
        · rintro (a | ⟨b, c⟩)
          · exact Or.inl a
          · exact Or.inr ⟨by omega, c⟩
        · rintro (a | ⟨b, c⟩)
          · exact Or.inl a
          · by_cases q : idx / B = j
            · exfalso
              rw [q] at hcomm hdm
              omega
            · exact Or.inr ⟨by omega, c⟩
      simp only [h1, h2, ite_false, e]

/-- Sixteen rows more of accumulator `j`, by the lanes of the accumulation. -/
theorem lanesAcc_upd (X : Array F) (B m j : Nat) (A W : Nat → F) (hj : j < 4)
    (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size) (hB : 4 * B ≤ X.size) (o : USize)
    (ho : o.toNat = j * B + 16 * m) (h : Win (encode (accUpd X B m j A W)) o) (wj : UInt32)
    (hw : wj = (W j).val) (y : (k : Nat) → k ≤ 15 → UInt32)
    (hy : ∀ k hk, y k hk = (A (16 * m + k)).val) :
    lanes16 (fun acc x ↦ add p acc (mulM p x wj)) (fun k hk ↦ ld _ o h k hk) y
        (encode (accUpd X B m j A W)) o = encode (accUpd X B m (j + 1) A W) := by
  subst hw
  have hjB : j * B + B ≤ 4 * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  rw [lanes16_encode (fun acc x ↦ add p acc (mulM p x (W j).val)) (fun acc x ↦ acc + x * W j)
    (fun x y ↦ by rw [mulM_val, add_val]) _ y (fun k ↦ X.getD (j * B + 16 * m + k) 0)
    (fun k ↦ A (16 * m + k)) (fun k hk ↦ ?_) hy _ o (by rw [size_accUpd]; exact hX)
    (by rw [size_accUpd, ho]; omega), ho]
  · rw [← splice_accUpd X B m j A W hj hm (by omega)]
  · have hB0 : 0 < B := by omega
    have hq : (j * B + 16 * m + k) / B = j :=
      Nat.div_eq_of_lt_le (by rw [Nat.add_assoc]; exact Nat.le_add_right _ _)
        (by rw [Nat.add_mul, Nat.one_mul]; omega)
    have hr : (j * B + 16 * m + k) % B = 16 * m + k := by
      rw [show j * B + 16 * m + k = (16 * m + k) + B * j by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    rw [ld_encode, ho, getD_accUpd, hq, hr, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- An accumulator's offset in a group of `B` rows. -/
theorem accOff_toNat {jj rb : USize} {j B m : Nat} (hjj : jj.toNat = j) (hrb : rb.toNat = B)
    (hj : j < 4) (hm : 16 * m + 16 ≤ B) (hB : 4 * (4 * B) < USize.size) :
    (jj * rb + (16 * m).toUSize).toNat = j * B + 16 * m := by
  have hjB : j * B + B ≤ 4 * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  have hmul : (jj * rb).toNat = j * B := by
    rw [usize_mul_toNat (by rw [hjj, hrb]; omega), hjj, hrb]
  rw [usize_add_toNat (by rw [hmul, toUSize_toNat (by omega)]; omega), hmul,
    toUSize_toNat (by omega)]

variable (p) in
theorem stepAccS_upd (X : Array F) (B m j : Nat) (A W : Nat → F) (hj : j < 4)
    (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size) (hB : 4 * B ≤ X.size) (jj rb a : USize)
    (hjj : jj.toNat = j) (hrb : rb.toNat = B) (oa : Nat) (ha : a.toNat = oa) (hoa : 4 * B ≤ oa)
    (hra : oa + B ≤ X.size) (hA : ∀ k < B, A k = X.getD (oa + k) 0) (wj : UInt32)
    (hw : wj = (W j).val) :
    stepAccS p rb jj a wj (encode (accUpd X B m j A W)) (16 * m).toUSize =
      encode (accUpd X B m (j + 1) A W) := by
  have hs : (encode (accUpd X B m j A W)).size = 4 * X.size := by
    rw [size_encode_fields, size_accUpd]
  have ho := accOff_toNat hjj hrb hj hm (by omega)
  have hjB : j * B + B ≤ 4 * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  have hoa' : (a + (16 * m).toUSize).toNat = oa + 16 * m :=
    off_toNat (n := X.size) ha (by omega) hX
  unfold stepAccS
  rw [withWin_pos _ _ _ _ (by rw [hs, ho]; omega) (by rw [hs]; exact hX),
    withWin_pos _ _ _ _ (by rw [hs, hoa']; omega) (by rw [hs]; exact hX)]
  rw [st16_eq _ _ _ (by rw [hs]; exact hX)]
  refine lanesAcc_upd X B m j A W hj hm hX hB _ ho _ wj hw _ fun k hk ↦ ?_
  rw [ld_encode, hoa', getD_accUpd, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hA _
      (by omega), Nat.add_assoc]

variable (p) in
theorem stepAccE_upd (X E : Array F) (B m j : Nat) (A W : Nat → F) (hj : j < 4)
    (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size) (hE : 4 * E.size < USize.size)
    (hB : 4 * B ≤ X.size) (jj rb a : USize) (hjj : jj.toNat = j) (hrb : rb.toNat = B) (oa : Nat)
    (ha : a.toNat = oa) (hra : oa + B ≤ E.size) (hA : ∀ k < B, A k = E.getD (oa + k) 0)
    (wj : UInt32) (hw : wj = (W j).val) :
    stepAccE p rb jj (encode E) a wj (encode (accUpd X B m j A W)) (16 * m).toUSize =
      encode (accUpd X B m (j + 1) A W) := by
  have hs : (encode (accUpd X B m j A W)).size = 4 * X.size := by
    rw [size_encode_fields, size_accUpd]
  have ho := accOff_toNat hjj hrb hj hm (by omega)
  have hjB : j * B + B ≤ 4 * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  have hoa' : (a + (16 * m).toUSize).toNat = oa + 16 * m :=
    off_toNat (n := E.size) ha (by omega) hE
  unfold stepAccE
  rw [withWin_pos _ _ _ _ (by rw [hs, ho]; omega) (by rw [hs]; exact hX),
    withWin_pos _ _ _ _ (by rw [size_encode_fields, hoa']; omega)
      (by rw [size_encode_fields]; exact hE)]
  rw [st16_eq _ _ _ (by rw [hs]; exact hX)]
  refine lanesAcc_upd X B m j A W hj hm hX hB _ ho _ wj hw _ fun k hk ↦ ?_
  rw [ld_encode, hoa', hA _ (by omega), Nat.add_assoc]

variable (p) in
theorem stepAccW_upd (X : Array F) (B m j : Nat) (W : Nat → F) (hj : j < 4)
    (hm : 16 * m + 16 ≤ B) (hX : 4 * X.size < USize.size) (hB : 4 * B ≤ X.size) (jj rb : USize)
    (hjj : jj.toNat = j) (hrb : rb.toNat = B) (c : F) (wj : UInt32) (hw : wj = (W j).val) :
    stepAccW p rb jj c.val wj (encode (accUpd X B m j (fun _ ↦ c) W)) (16 * m).toUSize =
      encode (accUpd X B m (j + 1) (fun _ ↦ c) W) := by
  have hs : (encode (accUpd X B m j (fun _ ↦ c) W)).size = 4 * X.size := by
    rw [size_encode_fields, size_accUpd]
  have ho := accOff_toNat hjj hrb hj hm (by omega)
  have hjB : j * B + B ≤ 4 * B := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right B (by omega)
  unfold stepAccW
  rw [withWin_pos _ _ _ _ (by rw [hs, ho]; omega) (by rw [hs]; exact hX)]
  rw [st16_eq _ _ _ (by rw [hs]; exact hX)]
  exact lanesAcc_upd X B m j _ W hj hm hX hB _ ho _ wj hw (fun _ _ ↦ c.val) fun _ _ ↦ rfl

/-- The four coordinates' steps of an accumulation, from `accUpd … m 0` to `accUpd … (m + 1) 0`. -/
theorem acc4_steps (st : Nat → ByteArray → ByteArray) (X : Array F) (B m : Nat)
    (A W : Nat → F)
    (h : ∀ j < 4, st j (encode (accUpd X B m j A W)) = encode (accUpd X B m (j + 1) A W)) :
    st 3 (st 2 (st 1 (st 0 (encode (accUpd X B m 0 A W))))) =
      encode (accUpd X B (m + 1) 0 A W) := by
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    accUpd_next X B m A W]

/-- An accumulation's weights' words. -/
def WtsOk (wts : Array UInt32) (w : Nat) (W : Nat → F) : Prop :=
  ∀ j < 4, wts.getD (4 * w + j) 0 = (W j).val

theorem usize_lits : (0 : USize).toNat = 0 ∧ (1 : USize).toNat = 1 ∧ (2 : USize).toNat = 2 ∧
    (3 : USize).toNat = 3 :=
  ⟨usize_numeral 0 (by decide), usize_numeral 1 (by decide), usize_numeral 2 (by decide),
    usize_numeral 3 (by decide)⟩

/-- **An accumulation of a register** on a group of `16 nm` rows. -/
theorem accS_upd (X : Array F) (nm : Nat) (A W : Nat → F) (hX : 4 * X.size < USize.size)
    (hB : 4 * (16 * nm) ≤ X.size) (rb a : USize) (hrb : rb.toNat = 16 * nm) (oa : Nat)
    (ha : a.toNat = oa) (hoa : 4 * (16 * nm) ≤ oa) (hra : oa + 16 * nm ≤ X.size)
    (hA : ∀ k < 16 * nm, A k = X.getD (oa + k) 0) (wts : Array UInt32) (w : Nat)
    (hw : WtsOk wts w W) :
    accS p nm rb (encode X) a wts w = encode (accUpd X (16 * nm) nm 0 A W) := by
  obtain ⟨u0, u1, u2, u3⟩ := usize_lits
  have h := groups_states (stepAcc4S p rb a (wts.getD (4 * w) 0)
    (wts.getD (4 * w + 1) 0) (wts.getD (4 * w + 2) 0) (wts.getD (4 * w + 3) 0)) nm
    (fun m ↦ encode (accUpd X (16 * nm) m 0 A W)) (by omega) fun m hm ↦
      acc4_steps (fun j s ↦ stepAccS p rb j.toUSize a (wts.getD (4 * w + j) 0) s
        (16 * m).toUSize) X (16 * nm) m A W fun j hj ↦
        stepAccS_upd p X (16 * nm) m j A W hj (by omega) hX hB _ rb a
          (toUSize_toNat (by have := usize_size_le; omega)) hrb oa ha hoa hra hA _ (hw j hj)
  simpa only [accS, accUpd_zero] using h

/-- **An accumulation of another buffer's words** on a group of `16 nm` rows. -/
theorem accE_upd (X E : Array F) (nm : Nat) (A W : Nat → F) (hX : 4 * X.size < USize.size)
    (hE : 4 * E.size < USize.size) (hB : 4 * (16 * nm) ≤ X.size) (rb a : USize)
    (hrb : rb.toNat = 16 * nm) (oa : Nat) (ha : a.toNat = oa) (hra : oa + 16 * nm ≤ E.size)
    (hA : ∀ k < 16 * nm, A k = E.getD (oa + k) 0) (wts : Array UInt32) (w : Nat)
    (hw : WtsOk wts w W) :
    accE p nm rb (encode X) (encode E) a wts w = encode (accUpd X (16 * nm) nm 0 A W) := by
  have h := groups_states (stepAcc4E p rb (encode E) a (wts.getD (4 * w) 0)
    (wts.getD (4 * w + 1) 0) (wts.getD (4 * w + 2) 0) (wts.getD (4 * w + 3) 0)) nm
    (fun m ↦ encode (accUpd X (16 * nm) m 0 A W)) (by omega) fun m hm ↦
      acc4_steps (fun j s ↦ stepAccE p rb j.toUSize (encode E) a (wts.getD (4 * w + j) 0) s
        (16 * m).toUSize) X (16 * nm) m A W fun j hj ↦
        stepAccE_upd p X E (16 * nm) m j A W hj (by omega) hX hE hB _ rb a
          (toUSize_toNat (by have := usize_size_le; omega)) hrb oa ha hra hA _ (hw j hj)
  simpa only [accE, accUpd_zero] using h

/-- **An accumulation of a constant** on a group of `16 nm` rows. -/
theorem accW_upd (X : Array F) (nm : Nat) (W : Nat → F) (hX : 4 * X.size < USize.size)
    (hB : 4 * (16 * nm) ≤ X.size) (rb : USize) (hrb : rb.toNat = 16 * nm) (c : F)
    (wts : Array UInt32) (w : Nat) (hw : WtsOk wts w W) :
    accW p nm rb (encode X) c.val wts w = encode (accUpd X (16 * nm) nm 0 (fun _ ↦ c) W) := by
  have h := groups_states (stepAcc4W p rb c.val (wts.getD (4 * w) 0)
    (wts.getD (4 * w + 1) 0) (wts.getD (4 * w + 2) 0) (wts.getD (4 * w + 3) 0)) nm
    (fun m ↦ encode (accUpd X (16 * nm) m 0 (fun _ ↦ c) W)) (by omega) fun m hm ↦
      acc4_steps (fun j s ↦ stepAccW p rb j.toUSize c.val (wts.getD (4 * w + j) 0) s
        (16 * m).toUSize) X (16 * nm) m _ W fun j hj ↦
        stepAccW_upd p X (16 * nm) m j W hj (by omega) hX hB _ rb
          (toUSize_toNat (by have := usize_size_le; omega)) hrb c _ (hw j hj)
  simpa only [accW, accUpd_zero] using h

/-! ### Fills, copies and gathers -/

theorem fill_upd (X : Array F) (nm od : Nat) (d : USize) (hd : d.toNat = od)
    (hX : 4 * X.size < USize.size) (hrd : od + 16 * nm ≤ X.size) (c : F) :
    fill nm (encode X) d c.val = encode (updR X od (16 * nm) fun _ ↦ c) :=
  pass_upd _ (fun x _ ↦ x) (fun x _ ↦ x) (fun _ _ ↦ rfl) X nm od _ d hd hX hrd (fun _ ↦ c)
    (fun _ ↦ c) (fun _ _ ↦ rfl) fun m hm ↦ ⟨fun _ _ ↦ c.val, fun _ _ ↦ c.val, fun _ _ ↦ rfl,
      fun _ _ ↦ rfl, by
        have hw := winS X od od m nm (fun _ ↦ c) d hd hX hrd hm
        unfold stepW
        rw [withWin_pos _ _ _ _ hw.1 hw.2, st16_eq _ _ _ hw.2]
        rfl⟩

theorem copy_upd (X E : Array F) (nm od oa : Nat) (d a : USize) (hd : d.toNat = od)
    (ha : a.toNat = oa) (hX : 4 * X.size < USize.size) (hE : 4 * E.size < USize.size)
    (hrd : od + 16 * nm ≤ X.size) (hra : oa + 16 * nm ≤ E.size) :
    copy nm (encode X) (encode E) d a = encode (updR X od (16 * nm) fun k ↦ E.getD (oa + k) 0) :=
  groupsEW_upd (fun x _ ↦ x) (fun x _ ↦ x) (fun _ _ ↦ rfl) X nm od _ d hd hX hrd E hE oa a ha
    hra 0 fun _ _ ↦ rfl

theorem gather_upd (X M : Array F) (nm od w c r0 : Nat) (next : Array Nat) (d : USize)
    (hd : d.toNat = od) (hX : 4 * X.size < USize.size) (hM : 4 * M.size < USize.size)
    (hrd : od + 16 * nm ≤ X.size) (hr : ∀ k < 16 * nm, next.getD (r0 + k) 0 * w + c < M.size) :
    gather nm (encode X) d (encode M) w c next r0 =
      encode (updR X od (16 * nm) fun k ↦ M.getD (next.getD (r0 + k) 0 * w + c) 0) :=
  pass_upd _ (fun x _ ↦ x) (fun x _ ↦ x) (fun _ _ ↦ rfl) X nm od _ d hd hX hrd
    (fun k ↦ M.getD (next.getD (r0 + k) 0 * w + c) 0) (fun _ ↦ 0) (fun _ _ ↦ rfl) fun m hm ↦
      ⟨fun k _ ↦ read (encode M) (next.getD (r0 + (16 * m).toUSize.toNat + k) 0 * w + c),
        fun _ _ ↦ 0, fun k hk ↦ by
          have h1 := hr (16 * m + k) (by omega)
          rw [toUSize_toNat (by omega)]
          dsimp only
          rw [Nat.add_assoc, Words.read_encode M _ hM h1], fun _ _ ↦ rfl, by
        have hw := winS X od od m nm (fun k ↦ M.getD (next.getD (r0 + k) 0 * w + c) 0) d hd hX
          hrd hm
        unfold stepGather
        rw [withWin_pos _ _ _ _ hw.1 hw.2, st16_eq _ _ _ hw.2]
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
def gtab (B nregs : Nat) (sts : Nat → St F) : Array F :=
  tab (B * (4 + nregs)) fun idx ↦ (sts (idx % B)).slot (idx / B)

/-- A group's state holds `B` rows' run states. -/
def GroupRel (B nregs : Nat) (st : ByteArray) (sts : Nat → St F) : Prop :=
  st = encode (gtab B nregs sts)

theorem size_gtab (B nregs : Nat) (sts : Nat → St F) :
    (gtab B nregs sts).size = B * (4 + nregs) := size_tab ..

/-- Slot `t` of every row set: its words overwritten. -/
theorem updR_gtab (B nregs t : Nat) (sts : Nat → St F) (H : Nat → F) :
    updR (gtab B nregs sts) (B * t) B H = gtab B nregs fun i ↦ (sts i).setSlot t (H i) := by
  apply array_eq_of_getD _ _ 0 (by rw [size_updR, size_gtab, size_gtab])
  intro idx
  rw [getD_updR, size_gtab]
  unfold gtab
  by_cases hi : idx < B * (4 + nregs)
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
    accUpd (gtab (16 * nm) nregs sts) (16 * nm) nm 0 A W = gtab (16 * nm) nregs fun i ↦
      { sts i with acc := fun j ↦ (sts i).acc j + A i * W j } := by
  apply array_eq_of_getD _ _ 0 (by rw [size_accUpd, size_gtab, size_gtab])
  intro idx
  rw [getD_accUpd, size_gtab]
  unfold gtab
  by_cases hi : idx < 16 * nm * (4 + nregs)
  · rw [getD_tab _ _ _ hi, getD_tab _ _ _ hi]
    have hB : 0 < 16 * nm := Nat.pos_of_ne_zero fun h ↦ by
      rw [h, Nat.zero_mul] at hi; omega
    have hlt := Nat.mod_lt idx hB
    by_cases h4 : idx < 4 * (16 * nm)
    · have hq : idx / (16 * nm) < 4 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h4)
      simp only [hi, h4, hlt, true_or, and_self, ite_true, St.slot, hq]
    · have hq : ¬idx / (16 * nm) < 4 := fun hq ↦ h4 (by
        have := Nat.div_add_mod idx (16 * nm)
        have : idx / (16 * nm) * (16 * nm) + (16 * nm) ≤ 4 * (16 * nm) := by
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
      groups (stepSS (Op.wordG p o) (regOff env d) (regOff env x) (regOff env y)) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_SE (env : GroupEnv) (o : Op) (d : Nat) (x y : Nat) (s : ByteArray) :
    binG p env o d (.reg x) (.cur y) s =
      groups (stepSE (Op.wordG p o) env.view (regOff env d) (regOff env x)
          (colOff env y)) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_ES (env : GroupEnv) (o : Op) (d : Nat) (x y : Nat) (s : ByteArray) :
    binG p env o d (.cur x) (.reg y) s =
      groups (stepES (Op.wordG p o) env.view (regOff env d) (colOff env x)
          (regOff env y)) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_EE (env : GroupEnv) (o : Op) (d : Nat) (x y : Nat) (s : ByteArray) :
    binG p env o d (.cur x) (.cur y) s =
      groups (stepEE (Op.wordG p o) env.view (regOff env d) (colOff env x)
          (colOff env y)) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_SW (env : GroupEnv) (o : Op) (d : Nat) (x : Nat) (y : F) (s : ByteArray) :
    binG p env o d (.reg x) (.const y) s =
      groups (stepSW (Op.wordG p o) (regOff env d) (regOff env x) y.val) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_EW (env : GroupEnv) (o : Op) (d : Nat) (x : Nat) (y : F) (s : ByteArray) :
    binG p env o d (.cur x) (.const y) s =
      groups (stepEW (Op.wordG p o) env.view (regOff env d) (colOff env x) y.val) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_WS (env : GroupEnv) (o : Op) (d : Nat) (x : F) (y : Nat) (s : ByteArray) :
    binG p env o d (.const x) (.reg y) s =
      groups (stepWS (Op.wordG p o) (regOff env d) (regOff env y) x.val) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_WE (env : GroupEnv) (o : Op) (d : Nat) (x : F) (y : Nat) (s : ByteArray) :
    binG p env o d (.const x) (.cur y) s =
      groups (stepWE (Op.wordG p o) env.view (regOff env d) (colOff env y) x.val) env.nm s 0 := by
  cases o <;> rfl

variable (p) in
theorem binG_WW (env : GroupEnv) (o : Op) (d : Nat) (x y : F) (s : ByteArray) :
    binG p env o d (.const x) (.const y) s = fill env.nm s (regOff env d)
        (Op.wordG p o x.val y.val) := by
  cases o <;> rfl

theorem regOff_toNat (B nregs r : Nat) (v : View) (L : Loads) (scal wts : Array UInt32)
    (hr : r < nregs) (hst : 4 * (B * (4 + nregs)) < USize.size) :
    (regOff (blockEnv B v L scal wts) r).toNat = B * (4 + r) := by
  simp only [regOff, blockEnv]
  rcases Nat.eq_zero_or_pos B with h0 | h0
  · subst h0
    rw [USize.toNat_mul]
    simp
  · have h4 : B * (4 + r) ≤ B * (4 + nregs) := Nat.mul_le_mul_left B (by omega)
    have h5 : 4 + r ≤ B * (4 + r) := Nat.le_mul_of_pos_left _ h0
    have h6 : B ≤ B * (4 + r) := Nat.le_mul_of_pos_right B (by omega)
    have e1 : (4 + r).toUSize.toNat = 4 + r := toUSize_toNat (by omega)
    have e2 : B.toUSize.toNat = B := toUSize_toNat (by omega)
    rw [usize_mul_toNat (by rw [e1, e2, Nat.mul_comm]; omega), e1, e2, Nat.mul_comm]

theorem colOff_toNat (B : Nat) (V : Array F) (cb cs c : Nat) (L : Loads) (scal wts : Array UInt32)
    (hc : cb + c * cs + B ≤ V.size) (hV : 4 * V.size < USize.size) :
    (colOff (blockEnv B ⟨encode V, cb, cs⟩ L scal wts) c).toNat = cb + c * cs := by
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
    (tcolOff (blockEnv B v L scal wts) c).toNat = c * B := by
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
theorem getD_gtab (B nregs : Nat) (sts : Nat → St F) (s k : Nat) (hs : s < 4 + nregs)
    (hk : k < B) : (gtab B nregs sts).getD (B * s + k) 0 = (sts k).slot s := by
  have hlt : B * s + k < B * (4 + nregs) := by
    have : B * s + B ≤ B * (4 + nregs) := by
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
theorem apart_regs (B x d : Nat) : Apart true (B * (4 + x)) (B * (4 + d)) B := fun _ ↦ by
  rcases Nat.lt_trichotomy x d with h | h | h
  · right; left
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left B (by omega)
  · left; rw [h]
  · right; right
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left B (by omega)

theorem scalAt_blockEnv (B : Nat) (v : View) (L : Loads) (SC : Array F) (wts : Array UInt32)
    (i : Nat) : scalAt (blockEnv B v L (SC.map (·.val)) wts) i = (SC.getD i 0).val :=
  CompPoly.CPolynomial.NTTFast.Packed.getD_map_val SC i

theorem wtsOk_blockCtx (WT : Array F) (w : Nat) :
    WtsOk (WT.map (·.val)) w fun j ↦ WT.getD (4 * w + j) 0 := fun _ _ ↦
  CompPoly.CPolynomial.NTTFast.Packed.getD_map_val WT _

/-- The group of a block of `16 nm` rows: the block's view and loads, the scalars and weights. -/
abbrev groupOf (nm : Nat) (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) :
    GroupEnv :=
  blockEnv (16 * nm) ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val)) (WT.map (·.val))

theorem groupOf_nm (nm : Nat) (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) :
    (groupOf nm V cb cs L SC WT).nm = nm := Nat.mul_div_cancel_left nm (by decide)

theorem groupOf_rb (nm : Nat) (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F)
    (h : 16 * nm < USize.size) : (groupOf nm V cb cs L SC WT).rb.toNat = 16 * nm :=
  toUSize_toNat h

/-- **A load on a group** of `16 nm` rows in range is the load on every row's values. -/
theorem loadG_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) (nm nregs : Nat)
    (hst : 4 * (16 * nm * (4 + nregs)) < USize.size) (hL : L.Addr) (sts : Nat → St F) (d : Nat)
    (src : Src) (hd : d < nregs) (hs : L.InRange (16 * nm) src) :
    loadG (groupOf nm V cb cs L SC WT) d src (encode (gtab (16 * nm) nregs sts)) =
      encode (gtab (16 * nm) nregs fun i ↦ (sts i).setSlot (4 + d) (L.src (16 * nm) i src)) := by
  obtain ⟨hM, hP, hPT, hQ, hQT, hPER, hFS, hLS, hTS⟩ := hL
  have hX : 4 * (gtab (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
  have hrd : 16 * nm * (4 + d) + 16 * nm ≤ (gtab (16 * nm) nregs sts).size := by
    rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hro := regOff_toNat (16 * nm) nregs d ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val))
    (WT.map (·.val)) hd hst
  rw [← updR_gtab _ _ _ _ _]
  have hnm := groupOf_nm nm V cb cs L SC WT
  cases src <;> simp only [LoadsF.InRange] at hs
  case next c =>
    simp only [loadG, hnm]
    exact gather_upd _ L.M nm _ L.w c L.r0 L.next _ hro hX hM hrd hs
  case prepCur c =>
    simp only [loadG, hnm]
    exact copy_upd _ L.PT nm _ (c * (16 * nm)) _ _ hro (tcolOff_toNat _ c _ _ _ _ L.PT.size hs hPT)
      hX hPT hrd hs
  case prepNext c =>
    simp only [loadG, hnm]
    exact gather_upd _ L.P nm _ L.pw c L.r0 L.next _ hro hX hP hrd hs
  case permCur c =>
    simp only [loadG, hnm]
    exact copy_upd _ L.QT nm _ (c * (16 * nm)) _ _ hro (tcolOff_toNat _ c _ _ _ _ L.QT.size hs hQT)
      hX hQT hrd hs
  case permNext c =>
    simp only [loadG, hnm]
    exact gather_upd _ L.Q nm _ L.rw c L.r0 L.next _ hro hX hQ hrd hs
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
    (hk : k < B) : (gtab B nregs sts).getD (B * (4 + r) + k) 0 = (sts k).reg r := by
  rw [getD_gtab _ _ _ _ _ (by omega) hk]
  simp only [St.slot, show ¬4 + r < 4 by omega, ite_false, Nat.add_sub_cancel_left]

/-- **An operation on a group** of `16 nm` rows in range is the operation on every row's values. -/
theorem binG_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F) (nm nregs : Nat)
    (hst : 4 * (16 * nm * (4 + nregs)) < USize.size) (hV : 4 * V.size < USize.size)
    (sts : Nat → St F) (o : Op) (d : Nat) (a b : Opd F) (hd : d < nregs)
    (ha : a.InRange V cb cs (16 * nm) nregs) (hb : b.InRange V cb cs (16 * nm) nregs) :
    binG p (groupOf nm V cb cs L SC WT) o d a b (encode (gtab (16 * nm) nregs sts)) =
      encode (gtab (16 * nm) nregs fun i ↦ (sts i).setSlot (4 + d)
        (o.eval (a.val (blockCtx V cb cs L SC WT (16 * nm) i) (sts i))
          (b.val (blockCtx V cb cs L SC WT (16 * nm) i) (sts i)))) := by
  have hX : 4 * (gtab (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
  have hrd : ∀ r < nregs, 16 * nm * (4 + r) + 16 * nm ≤ (gtab (16 * nm) nregs sts).size := by
    intro r hr
    rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hro (r : Nat) (hr : r < nregs) := regOff_toNat (16 * nm) nregs r ⟨encode V, cb, cs⟩ L.enc
    (SC.map (·.val)) (WT.map (·.val)) hr hst
  have hco (c : Nat) (hc : cb + c * cs + 16 * nm ≤ V.size) := colOff_toNat (16 * nm) V cb cs c
    L.enc (SC.map (·.val)) (WT.map (·.val)) hc hV
  have hnm := groupOf_nm nm V cb cs L SC WT
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
    (hst : 4 * (16 * nm * (4 + nregs)) < USize.size) (hV : 4 * V.size < USize.size)
    (sts : Nat → St F) (a : Opd F) (w : Nat) (ha : a.InRange V cb cs (16 * nm) nregs) :
    accG p (groupOf nm V cb cs L SC WT) a w (encode (gtab (16 * nm) nregs sts)) =
      encode (gtab (16 * nm) nregs fun i ↦
        (Instr.acc a w).exec (fieldMachine (blockCtx V cb cs L SC WT (16 * nm) i)) (sts i)) := by
  have hX : 4 * (gtab (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
  have hB : 4 * (16 * nm) ≤ (gtab (16 * nm) nregs sts).size := by
    rw [size_gtab, Nat.mul_comm 4]; exact Nat.mul_le_mul_left _ (by omega)
  have hnm := groupOf_nm nm V cb cs L SC WT
  have hrb := groupOf_rb nm V cb cs L SC WT (by omega)
  have hwt := wtsOk_blockCtx WT w
  have e : (fun i ↦ (Instr.acc a w).exec (fieldMachine (blockCtx V cb cs L SC WT (16 * nm) i))
      (sts i)) = fun i ↦ ⟨(sts i).reg, fun j ↦ (sts i).acc j +
        a.val (blockCtx V cb cs L SC WT (16 * nm) i) (sts i) * WT.getD (4 * w + j) 0⟩ :=
    funext fun _ ↦ rfl
  rw [e, ← accUpd_gtab]
  cases a with
  | reg r =>
    have hr : r < nregs := ha
    have hro := regOff_toNat (16 * nm) nregs r ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val))
      (WT.map (·.val)) hr hst
    have h4 : 4 * (16 * nm) ≤ 16 * nm * (4 + r) := by
      rw [Nat.mul_comm 4]; exact Nat.mul_le_mul_left _ (by omega)
    have h5 : 16 * nm * (4 + r) + 16 * nm ≤ (gtab (16 * nm) nregs sts).size := by
      rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    simp only [accG, hnm]
    exact accS_upd _ nm _ _ hX hB _ _ hrb _ hro h4 h5
      (fun k hk ↦ (getD_gtab_reg _ _ _ _ _ hr hk).symm) _ _ hwt
  | cur c =>
    have hc : cb + c * cs + 16 * nm ≤ V.size := ha
    simp only [accG, hnm]
    exact accE_upd _ V nm _ _ hX hV hB _ _ hrb _ (colOff_toNat (16 * nm) V cb cs c L.enc
      (SC.map (·.val)) (WT.map (·.val)) hc hV) hc (fun k hk ↦ rfl) _ _ hwt
  | const c =>
    simp only [accG, hnm]
    exact accW_upd _ nm _ hX hB _ hrb c _ _ hwt

/-- **An instruction on a group** of `16 nm` rows in range is the instruction on every row's
values (`blockCtx`). -/
theorem execGroup_rel (V : Array F) (cb cs : Nat) (L : LoadsF p) (SC WT : Array F)
    (nm nregs : Nat) (hst : 4 * (16 * nm * (4 + nregs)) < USize.size)
    (hV : 4 * V.size < USize.size) (hL : L.Addr) (sts : Nat → St F) (ins : Instr F)
    (hin : ins.InRange V cb cs L (16 * nm) nregs) :
    ins.exec (groupMachine p (groupOf nm V cb cs L SC WT)) (encode (gtab (16 * nm) nregs sts)) =
      encode (gtab (16 * nm) nregs fun i ↦
        ins.exec (fieldMachine (blockCtx V cb cs L SC WT (16 * nm) i)) (sts i)) := by
  cases ins with
  | load d src =>
    obtain ⟨hd, hs⟩ := hin
    refine (loadG_rel V cb cs L SC WT nm nregs hst hL sts d src hd hs).trans ?_
    refine congrArg (fun f ↦ encode (gtab (16 * nm) nregs f)) (funext fun i ↦ ?_)
    rw [St.setSlot_reg, exec_load]
    rfl
  | scalar d k =>
    have hd : d < nregs := hin
    have hX : 4 * (gtab (16 * nm) nregs sts).size < USize.size := by rw [size_gtab]; exact hst
    show fill _ _ _ _ = _
    rw [groupOf_nm, scalAt_blockEnv, fill_upd _ nm _ _ (regOff_toNat (16 * nm) nregs d
      ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val)) (WT.map (·.val)) hd hst) hX (by
        rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)),
      updR_gtab _ _ _ _ _]
    refine congrArg (fun f ↦ encode (gtab (16 * nm) nregs f)) (funext fun i ↦ ?_)
    rw [St.setSlot_reg, exec_scalar]
    rfl
  | bin o d a b =>
    obtain ⟨hd, ha, hb⟩ := hin
    refine (binG_rel V cb cs L SC WT nm nregs hst hV sts o d a b hd ha hb).trans ?_
    refine congrArg (fun f ↦ encode (gtab (16 * nm) nregs f)) (funext fun i ↦ ?_)
    rw [St.setSlot_reg, exec_bin]
  | acc a w => exact accG_rel V cb cs L SC WT nm nregs hst hV sts a w hin

/-- **A program on a group** of `16 nm` rows in range runs the program on every row's values. -/
theorem runGroup_rel (code : Array (Instr F)) (V : Array F) (cb cs : Nat) (L : LoadsF p)
    (SC WT : Array F) (nm nregs : Nat) (hst : 4 * (16 * nm * (4 + nregs)) < USize.size)
    (hV : 4 * V.size < USize.size) (hL : L.Addr) (sts : Nat → St F)
    (hcode : ∀ ins ∈ code, ins.InRange V cb cs L (16 * nm) nregs) :
    run (groupMachine p (groupOf nm V cb cs L SC WT)) code (encode (gtab (16 * nm) nregs sts)) =
      encode (gtab (16 * nm) nregs fun i ↦
        run (fieldMachine (blockCtx V cb cs L SC WT (16 * nm) i)) code (sts i)) := by
  simp only [run, ← Array.foldl_toList]
  have hcode' : ∀ ins ∈ code.toList, ins.InRange V cb cs L (16 * nm) nregs := fun i hi ↦
    hcode i (Array.mem_toList_iff.mp hi)
  generalize code.toList = l at hcode'
  induction l generalizing sts with
  | nil => rfl
  | cons ins l ih =>
    simp only [List.foldl_cons]
    rw [execGroup_rel V cb cs L SC WT nm nregs hst hV hL sts ins (hcode' ins List.mem_cons_self)]
    exact ih _ fun i hi ↦ hcode' i (List.mem_cons_of_mem _ hi)

/-- A group's state whose words are encoded run states. -/
def GEncoded (B nregs : Nat) (st : ByteArray) : Prop :=
  ∃ sts : Nat → St F, st = encode (gtab B nregs sts)

theorem clearAccs_rel (nm nregs : Nat) (hst : 4 * (16 * nm * (4 + nregs)) < USize.size)
    (sts : Nat → St F) :
    clearAccs (16 * nm) (encode (gtab (16 * nm) nregs sts)) = encode (gtab (16 * nm) nregs
      fun i ↦ ⟨(sts i).reg, fun _ ↦ 0⟩) := by
  have hnm : 16 * nm / 16 = nm := Nat.mul_div_cancel_left nm (by decide)
  have hz (sts : Nat → St F) (j : Nat) (hj : j < 4) (u : USize) (hu : u.toNat = 16 * nm * j) :
      fill nm (encode (gtab (16 * nm) nregs sts)) u 0 =
        encode (gtab (16 * nm) nregs fun i ↦ (sts i).setSlot j 0) := by
    rw [show (0 : UInt32) = (0 : F).val from rfl, fill_upd _ nm _ _ hu
        (by rw [size_gtab]; exact hst)
      (by rw [size_gtab, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)),
      updR_gtab _ _ _ _ _]
  have hB : 16 * nm < USize.size := by
    have : 16 * nm ≤ 16 * nm * (4 + nregs) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h3 : 3 * (16 * nm) < USize.size := by
    have : 3 * (16 * nm) ≤ 16 * nm * (4 + nregs) := by
      rw [Nat.mul_comm 3]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  unfold clearAccs
  rw [hnm, hz _ 0 (by decide) 0 (by rw [usize_numeral 0 (by decide)]; ring),
    hz _ 1 (by decide) _ (by rw [toUSize_toNat hB]; ring),
    hz _ 2 (by decide) _ (by rw [toUSize_toNat (by omega)]; ring),
    hz _ 3 (by decide) _ (by rw [toUSize_toNat h3]; ring)]
  refine congrArg encode (tab_congr fun idx _ ↦ ?_)
  simp only [St.slot_setSlot]
  generalize idx / (16 * nm) = q
  by_cases h4 : q < 4
  · have : q = 3 ∨ q = 2 ∨ q = 1 ∨ q = 0 := by omega
    rcases this with e | e | e | e <;> simp only [e, St.slot] <;> rfl
  · simp only [show q ≠ 3 by omega, show q ≠ 2 by omega, show q ≠ 1 by omega,
      show q ≠ 0 by omega, ite_false, St.slot, h4]

/-- **A program accumulating every row** on a group of `B` rows (`B` a multiple of sixteen), from
cleared accumulators and any encoded registers: the accumulators hold its rows' accumulations. -/
theorem groupBlock_acc (code : Array (Instr F)) (nregs : Nat) (V : Array F) (cb cs : Nat)
    (L : LoadsF p) (SC WT : Array F) (B : Nat) (hB : B % 16 = 0)
    (hst : 4 * (B * (4 + nregs)) < USize.size) (hV : 4 * V.size < USize.size) (hL : L.Addr)
    (hcode : ∀ ins ∈ code, ins.InRange V cb cs L B nregs) (Q : Nat → Nat → F)
    (hQ : ∀ i < B, ∀ st0 : St F, st0.acc = (fun _ ↦ 0) → ∀ j < 4,
      (run (fieldMachine (blockCtx V cb cs L SC WT B i)) code st0).acc j = Q i j)
    (st : ByteArray) (h : GEncoded (p := p) B nregs st) :
    let st' := run (groupMachine p (blockEnv B ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val))
      (WT.map (·.val)))) code (clearAccs B st)
    GEncoded (p := p) B nregs st' ∧ ∀ j < 4, ∀ i < B, read st' (B * j + i) = (Q i j).val := by
  obtain ⟨nm, rfl⟩ : ∃ nm, B = 16 * nm := ⟨B / 16, by omega⟩
  obtain ⟨sts, rfl⟩ := h
  dsimp only
  rw [clearAccs_rel nm nregs hst sts]
  have e := runGroup_rel code V cb cs L SC WT nm nregs hst hV hL (fun i ↦ ⟨(sts i).reg, fun _ ↦ 0⟩)
    hcode
  simp only [groupOf] at e
  rw [e]
  refine ⟨⟨_, rfl⟩, fun j hj i hi ↦ ?_⟩
  rw [Words.read_encode _ _ (by rw [size_gtab]; exact hst) (by
      rw [size_gtab]
      have : 16 * nm * j + 16 * nm ≤ 16 * nm * (4 + nregs) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega),
    getD_gtab _ _ _ _ _ (by omega) hi]
  simp only [St.slot, hj, ite_true]
  rw [hQ i hi _ rfl j hj]

theorem gEncoded_zeros (B nregs : Nat) :
    GEncoded (p := p) B nregs (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords
      (B * (4 + nregs))) := by
  refine ⟨fun _ ↦ ⟨fun _ ↦ 0, fun _ ↦ 0⟩, ?_⟩
  rw [Words.zeroWords_eq (p := p)]
  refine congrArg encode (Array.ext (by rw [Array.size_replicate, size_gtab]) fun i h1 h2 ↦ ?_)
  simp only [Array.getElem_replicate, gtab, tab, Array.getElem_ofFn, St.slot]
  split <;> rfl

end CompStark.Stark.Prog
