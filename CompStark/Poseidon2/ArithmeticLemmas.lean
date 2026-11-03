/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Arithmetic
import CompPoly.Fields.Montgomery.Basic

/-! # Field semantics of the packed word arithmetic -/

@[expose] public section
namespace CompStark.Poseidon2
open Montgomery.Native32 Montgomery.Native32.FastField

variable {p : ℕ} [P : Mont32Field p]

local notation "F" => FastField p

variable (p) in
/-- `1 / 2` in the Montgomery field, named so that statements share one term. -/
def half : F := 2⁻¹

theorem modulus32_toNat' : P.modulus32.toNat = p := Mont32Field.modulus32_toNat

theorem lt_two_pow_31 : p < 2 ^ 31 := Mont32Field.modulus_lt_two_pow_31

theorem modulus_odd : p % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · have h2 := P.two_lt_modulus
    rcases P.prime.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
  · exact h

/-- Two words below `p` are equal if they agree in `ZMod p`. -/
theorem word_eq_of_cast {u v : UInt32} (hu : u.toNat < p) (hv : v.toNat < p)
    (h : (u.toNat : ZMod p) = (v.toNat : ZMod p)) : u = v :=
  UInt32.toNat_inj.mp (Montgomery.natCast_inj_of_lt h hu hv)

/-- Halving a canonical Montgomery word halves the field element. -/
theorem halve_val (x : F) : halve p x.val = (x * half p).val := by
  unfold half
  have hx : x.val.toNat < p := x.property
  have hp31 := lt_two_pow_31 (p := p)
  have hodd := modulus_odd (p := p)
  have hc : ((P.modulus32 >>> 1) + 1).toNat = p / 2 + 1 := by
    simp only [UInt32.toNat_add, UInt32.toNat_shiftRight, modulus32_toNat', UInt32.reduceToNat,
      Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
    omega
  have hs : (x.val >>> 1).toNat = x.val.toNat / 2 := by
    simp only [UInt32.toNat_shiftRight, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow,
      Nat.reduceMod, Nat.reducePow]
  have ha : (x.val &&& (1 : UInt32)).toNat = x.val.toNat % 2 := by
    simp only [UInt32.toNat_and, UInt32.reduceToNat, Nat.and_one_is_mod]
  -- The word of the half, as a natural number.
  have hh : (halve p x.val).toNat = x.val.toNat / 2 + x.val.toNat % 2 * (p / 2 + 1) := by
    unfold halve
    rw [UInt32.toNat_add, UInt32.toNat_mul, hs, ha, hc]
    rcases Nat.mod_two_eq_zero_or_one x.val.toNat with h | h <;> rw [h] <;> omega
  have hlt : (halve p x.val).toNat < p := by
    rw [hh]
    rcases Nat.mod_two_eq_zero_or_one x.val.toNat with h | h <;> rw [h] <;> omega
  apply word_eq_of_cast hlt (x * 2⁻¹).property
  -- Both words cast to `x · 2⁻¹ · 2 ^ 32`.
  have hc2 : ((halve p x.val).toNat : ZMod p) * 2 = (x.val.toNat : ZMod _) := by
    rw [hh]
    have : (x.val.toNat / 2 + x.val.toNat % 2 * (p / 2 + 1)) * 2 =
        x.val.toNat + x.val.toNat % 2 * p := by
      rcases Nat.mod_two_eq_zero_or_one x.val.toNat with h | h <;> rw [h] <;> omega
    have e : (((x.val.toNat / 2 + x.val.toNat % 2 * (p / 2 + 1) : Nat) : ZMod p)) * 2 =
        (((x.val.toNat / 2 + x.val.toNat % 2 * (p / 2 + 1)) * 2 : Nat) : ZMod _) := by
      push_cast; ring
    rw [e, this, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
  have h2 : (2 : ZMod p) ≠ 0 := Mont32Field.two_ne_zero
  have h2' : toField (2 : F) = 2 := by
    simpa using toField_natCast (modulus := p) 2
  have hhalf : ((halve p x.val).toNat : ZMod p) = (x.val.toNat : ZMod _) * 2⁻¹ := by
    rw [← hc2, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  rw [val_toNat_cast (x * 2⁻¹), toField_mul, toField_inv, h2', hhalf, val_toNat_cast x]
  ring

/-- The word of `x · 2 ^ (-n)`: canonical, and `2 ^ n` times it is `x` modulo `p`. -/
theorem mulInvPow2_toNat (n : Nat) (K : UInt32) (hn : n < 32) (hK : K.toNat * 2 ^ n + 1 = p)
    (w : UInt32) (hw : w.toNat < p) :
    (mulInvPow2 p n.toUInt32 K w).toNat < p ∧
      ((mulInvPow2 p n.toUInt32 K w).toNat * 2 ^ n) % p = w.toNat % p := by
  have hp31 := lt_two_pow_31 (p := p)
  have hnu : n.toUInt32.toNat = n := UInt32.toNat_ofNat_of_lt' (by unfold UInt32.size; omega)
  have hq0 : 0 < 2 ^ n := Nat.two_pow_pos n
  generalize ha : w.toNat = a at hw
  have hpow : (1 <<< n.toUInt32 : UInt32).toNat = 2 ^ n := by
    have : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
    simp only [UInt32.toNat_shiftLeft, hnu, UInt32.reduceToNat, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt hn]
    omega
  set q := 2 ^ n
  set k := K.toNat
  have hlo : a % q < q := Nat.mod_lt _ hq0
  -- `T = K · lo` is below `K · 2 ^ n = p - 1`, and `T · q = (p - 1) · lo`.
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.zero_mul] at hK
      have := P.two_lt_modulus
      omega
    · exact h
  have hT : a % q * k < p - 1 := by
    have := Nat.mul_le_mul_right k (show a % q + 1 ≤ q by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q k] at this
    generalize a % q * k = T at this ⊢
    generalize k * q = M at this hK
    omega
  have hTb : a % q * k < 4294967296 := by omega
  have hTq : a % q * k * q = (p - 1) * (a % q) := by
    rw [show a % q * k * q = k * q * (a % q) by ring]
    congr 1
    omega
  have hD : (w / (1 <<< n.toUInt32)).toNat = a / q := by rw [UInt32.toNat_div, hpow, ha]
  have hM : (w % (1 <<< n.toUInt32) * K).toNat = a % q * k := by
    rw [UInt32.toNat_mul, UInt32.toNat_mod, hpow, ha]
    exact Nat.mod_eq_of_lt hTb
  have hhi : a / q < p := lt_of_le_of_lt (Nat.div_le_self a q) hw
  have hdm : q * (a / q) + a % q = a := Nat.div_add_mod a q
  unfold mulInvPow2
  dsimp only
  generalize hd : w / (1 <<< n.toUInt32) - w % (1 <<< n.toUInt32) * K = d
  have hdv : d.toNat = (4294967296 - a % q * k + a / q) % 4294967296 := by
    rw [← hd, UInt32.toNat_sub, hD, hM]
  have he : (d + P.modulus32).toNat = (d.toNat + p) % 4294967296 := by
    simp only [UInt32.toNat_add, modulus32_toNat']
  -- The products as atoms: `q (a / q) + lo = a`, `lo k q = (p - 1) lo`.
  have hAq : a / q * q + a % q = a := by rw [Nat.mul_comm]; exact hdm
  have hpL : (p - 1) * (a % q) + a % q = p * (a % q) := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  by_cases hle : a % q * k ≤ a / q
  · -- No wrap: the result is `hi - T`, and `(hi - T) q + p lo = a`.
    have hd' : d.toNat = a / q - a % q * k := by rw [hdv]; omega
    have hne : ¬ d + P.modulus32 < d := by
      rw [UInt32.lt_iff_toNat_lt, he, hd']; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne), hd']
    refine ⟨by omega, ?_⟩
    have hv := Nat.mul_le_mul_right q hle
    have key : (a / q - a % q * k) * q + p * (a % q) = a := by
      rw [Nat.sub_mul]
      generalize a / q * q = u at hAq hv
      generalize a % q * k * q = v at hTq hv
      generalize (p - 1) * (a % q) = w at hTq hpL
      generalize p * (a % q) = z at hpL ⊢
      omega
    have := congrArg (· % p) key
    simp only [Nat.add_mul_mod_self_left] at this
    exact this
  · -- Wrap: the result is `hi + p - T`, and `(hi + p - T) q + p lo = a + p q`.
    have hd' : d.toNat = 4294967296 - a % q * k + a / q := by rw [hdv]; omega
    have hlt : d + P.modulus32 < d := by
      rw [UInt32.lt_iff_toNat_lt, he, hd']; omega
    have he' : (d + P.modulus32).toNat = a / q + p - a % q * k := by
      rw [he, hd']; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), he']
    refine ⟨by omega, ?_⟩
    have hv : a % q * k * q ≤ p * q := by
      rw [hTq, Nat.mul_comm p q]
      exact le_trans (Nat.mul_le_mul_left _ (Nat.le_of_lt hlo)) (by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega))
    have key : (a / q + p - a % q * k) * q + p * (a % q) = a + p * q := by
      rw [Nat.sub_mul, Nat.add_mul, Nat.mul_comm p q]
      rw [Nat.mul_comm p q] at hv
      generalize a / q * q = u at hAq
      generalize a % q * k * q = v at hTq hv
      generalize (p - 1) * (a % q) = w at hTq hpL
      generalize p * (a % q) = z at hpL ⊢
      generalize q * p = y at hv ⊢
      omega
    have := congrArg (· % p) key
    simp only [Nat.add_mul_mod_self_left, Nat.mul_comm p q, Nat.add_mul_mod_self_right] at this
    exact this

variable (p) in
/-- `2 ^ (-n)` in the Montgomery field. -/
def invPow2 (n : Nat) : F := (2 ^ n)⁻¹

/-- Multiplying a canonical Montgomery word by `2 ^ (-n)` with `mulInvPow2` multiplies the field
element. -/
theorem mulInvPow2_val (n K : UInt32) (hn : n.toNat < 32) (hK : K.toNat * 2 ^ n.toNat + 1 = p)
    (x : F) : mulInvPow2 p n K x.val = (x * invPow2 p n.toNat).val := by
  have hx : x.val.toNat < p := x.property
  have hkk : n.toNat.toUInt32 = n := UInt32.ofNat_toNat
  obtain ⟨hlt, hmod⟩ := mulInvPow2_toNat n.toNat K hn hK x.val hx
  rw [hkk] at hlt hmod
  apply word_eq_of_cast hlt (x * invPow2 p n.toNat).property
  have h2 : ((2 : ZMod p) ^ n.toNat) ≠ 0 := pow_ne_zero _ Mont32Field.two_ne_zero
  have hc : ((mulInvPow2 p n K x.val).toNat : ZMod p) * 2 ^ n.toNat =
      (x.val.toNat : ZMod _) := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ p).mpr hmod
    push_cast at this
    exact this
  have h2' : toField ((2 : F) ^ n.toNat) = 2 ^ n.toNat := by
    rw [toField_npow]
    congr 1
    simpa using toField_natCast (modulus := p) 2
  have hw : ((mulInvPow2 p n K x.val).toNat : ZMod p) =
      (x.val.toNat : ZMod _) * (2 ^ n.toNat)⁻¹ := by
    rw [← hc, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  rw [invPow2, val_toNat_cast (x * ((2 : F) ^ n.toNat)⁻¹), toField_mul, toField_inv, h2', hw,
    val_toNat_cast x]
  ring

/-- Below `2 p`, the sign reduction is the conditional subtraction of `p`. -/
theorem reduceSign_eq (u : UInt32) (h : u.toNat < 2 * p) :
    reduceSign p u = conditionalSubtract P.modulus32 u := by
  have hp31 := lt_two_pow_31 (p := p)
  have h2 := P.two_lt_modulus
  unfold reduceSign conditionalSubtract
  dsimp only
  have hd : (u - P.modulus32).toNat = (u.toNat + 4294967296 - p) % 4294967296 := by
    simp only [UInt32.toNat_sub, modulus32_toNat']
    omega
  by_cases hu : u < P.modulus32
  · -- `u - p` wraps: its sign bit is set and `p` is added back.
    rw [UInt32.lt_iff_toNat_lt, modulus32_toNat'] at hu
    have hs : (u - P.modulus32) >>> 31 = 1 := by
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_shiftRight, hd, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow,
        Nat.reduceMod, Nat.reducePow]
      omega
    rw [hs, show ((0 : UInt32) - 1) &&& P.modulus32 = P.modulus32 by
        rw [UInt32.zero_sub, UInt32.neg_one_and],
      UInt32.sub_add_cancel,
      ite_eq_left (by rw [UInt32.lt_iff_toNat_lt, modulus32_toNat']; exact hu)]
  · -- `u - p` is below `2 ^ 31`: its sign bit is clear.
    rw [UInt32.lt_iff_toNat_lt, modulus32_toNat'] at hu
    have hs : (u - P.modulus32) >>> 31 = 0 := by
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_shiftRight, hd, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow,
        Nat.reduceMod, Nat.reducePow]
      omega
    rw [hs, show ((0 : UInt32) - 0) &&& P.modulus32 = 0 by
        rw [UInt32.sub_zero, UInt32.zero_and], UInt32.add_zero,
      ite_eq_right (by rw [UInt32.lt_iff_toNat_lt, modulus32_toNat']; exact hu)]

/-- The lazy product is the native Montgomery quotient. -/
theorem mulLazy_eq (x y : UInt32) :
    mulLazy p x y = reduceQuotient P.montgomeryNegInv P.modulus64 (x.toUInt64 * y.toUInt64) := rfl

/-- The lazy product of words `x, y` with `x · y < p · 2 ^ 32`: below `2 p`, and `x · y · 2 ^ (-32)`
modulo `p`. -/
theorem mulLazy_toNat (x y : UInt32) (h : x.toNat * y.toNat < p * 2 ^ 32) :
    (mulLazy p x y).toNat < 2 * p ∧
      ((mulLazy p x y).toNat : ZMod p) =
        (x.toNat * y.toNat : ZMod _) * ((2 ^ 32 : ℕ) : ZMod p)⁻¹ := by
  have hp31 := lt_two_pow_31 (p := p)
  have h2 := P.two_lt_modulus
  have h64 : P.modulus64.toNat = p := Mont32Field.modulus64_toNat
  have hxy : (x.toUInt64 * y.toUInt64).toNat = x.toNat * y.toNat := by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (by omega)
  have hq := reduceQuotient_toNat (negInv := P.montgomeryNegInv) (p64 := P.modulus64)
    (x := x.toUInt64 * y.toUInt64) (by omega) (by omega) (by rw [hxy, h64]; exact h)
  rw [mulLazy_eq, hq, hxy, h64]
  refine ⟨Montgomery.reduceNatQuotient_lt_two_mul _ _ _ _ (by decide) (by omega) h, ?_⟩
  have : Fact p.Prime := ⟨P.prime⟩
  exact Montgomery.reduceNatQuotient_cast (2 ^ 32) p _ (by decide)
    P.montgomeryNegInv_mul_modulus_mod_two_pow_32 Mont32Field.two_pow_32_ne_zero
    (x.toNat * y.toNat)

/-- `mulLazy` of canonical words `x < p` and `y < 2 p`. -/
theorem mulLazy_bound {x y : UInt32} (hx : x.toNat < p) (hy : y.toNat < 2 * p) :
    x.toNat * y.toNat < p * 2 ^ 32 := by
  have hp31 := lt_two_pow_31 (p := p)
  calc x.toNat * y.toNat ≤ x.toNat * (2 * p) := Nat.mul_le_mul_left _ (by omega)
    _ < p * 2 ^ 32 := by nlinarith

/-- The lazy product of words `x < p`, `y < 2 p` is the field product, unreduced below `2 p`. -/
theorem mulLazy_spec {x y : UInt32} (hx : x.toNat < p) (hy : y.toNat < 2 * p) :
    (mulLazy p x y).toNat < 2 * p ∧
      ((mulLazy p x y).toNat : ZMod p) =
        (x.toNat * y.toNat : ZMod _) * ((2 ^ 32 : ℕ) : ZMod p)⁻¹ :=
  mulLazy_toNat x y (mulLazy_bound hx hy)

/-- The sign-reduced product of words `x < p`, `y < 2 p` is canonical. -/
theorem mulSign_lt {x y : UInt32} (hx : x.toNat < p) (hy : y.toNat < 2 * p) :
    (mulSign p x y).toNat < p := by
  have hr := (mulLazy_spec hx hy).1
  rw [mulSign, reduceSign_eq _ hr, conditionalSubtract]
  split <;> rename_i hu
  · rw [UInt32.lt_iff_toNat_lt, modulus32_toNat'] at hu; exact hu
  · rw [UInt32.lt_iff_toNat_lt, modulus32_toNat'] at hu
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, modulus32_toNat']; omega),
      modulus32_toNat']
    omega

/-- A word `u < 2 p`, reduced by sign, is `u` modulo `p` and canonical. -/
theorem reduceSign_cast {u : UInt32} (hu : u.toNat < 2 * p) :
    (reduceSign p u).toNat < p ∧ ((reduceSign p u).toNat : ZMod p) = (u.toNat : ZMod p) := by
  rw [reduceSign_eq _ hu, conditionalSubtract]
  split <;> rename_i h
  · rw [UInt32.lt_iff_toNat_lt, modulus32_toNat'] at h; exact ⟨h, rfl⟩
  · rw [UInt32.lt_iff_toNat_lt, modulus32_toNat'] at h
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, modulus32_toNat']; omega),
      modulus32_toNat']
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, sub_zero]

/-- A word `u < p` whose cast is `toField a · 2 ^ 32` is `a`'s word. -/
theorem eq_val_of_cast {u : UInt32} (a : F) (hu : u.toNat < p)
    (h : (u.toNat : ZMod p) = toField a * ((2 ^ 32 : ℕ) : ZMod p)) : u = a.val :=
  word_eq_of_cast hu a.property (by rw [h, val_toNat_cast a])

/-- The Montgomery product of the words of `a` and `b`, cast. -/
theorem cast_mulLazy (a b : F) (u : UInt32) (hu : (u.toNat : ZMod p) = toField b *
    ((2 ^ 32 : ℕ) : ZMod p)) (hb : u.toNat < 2 * p) :
    ((mulLazy p a.val u).toNat : ZMod p) = toField (a * b) * ((2 ^ 32 : ℕ) : ZMod p) := by
  have hR := Mont32Field.two_pow_32_ne_zero (modulus := p)
  rw [(mulLazy_spec a.property hb).2, Nat.cast_mul, hu, val_toNat_cast a, toField_mul]
  field_simp

/-- The cube of a canonical Montgomery word, canonical, is the field cube. -/
theorem cubeSign_val (a : F) : cubeSign p a.val = (a ^ 3).val := by
  have ha : a.val.toNat < p := a.property
  obtain ⟨hq, -⟩ := mulLazy_spec ha (by omega : a.val.toNat < 2 * p)
  have hsq : ((mulLazy p a.val a.val).toNat : ZMod p) = toField (a * a) * ((2 ^ 32 : ℕ) : ZMod p) :=
    cast_mulLazy a a a.val (val_toNat_cast a) (by omega)
  have hcu := cast_mulLazy a (a * a) _ hsq hq
  -- `mulLazy` is commutative in its words.
  have hcomm : mulLazy p (mulLazy p a.val a.val) a.val =
      mulLazy p a.val (mulLazy p a.val a.val) := by
    simp only [mulLazy, UInt64.mul_comm]
  obtain ⟨hlt, hc⟩ := reduceSign_cast (mulLazy_spec ha hq).1
  rw [cubeSign, mulSign, hcomm, show (a ^ 3) = a * (a * a) by ring]
  exact eq_val_of_cast _ hlt (by rw [hc]; exact hcu)

/-- The lazy cube of a canonical word is below `2 p`. -/
theorem cubeLazy_lt (a : F) : (cubeLazy p a.val).toNat < 2 * p := by
  have ha : a.val.toNat < p := a.property
  have hq := (mulLazy_spec ha (by omega : a.val.toNat < 2 * p)).1
  rw [cubeLazy, show mulLazy p (mulLazy p a.val a.val) a.val = mulLazy p a.val
    (mulLazy p a.val a.val) by simp only [mulLazy, UInt64.mul_comm]]
  exact (mulLazy_spec ha hq).1

/-- Reducing a word below `2 p` once is reducing it by sign. -/
theorem reduceOnce_eq_reduceSign {u : UInt32} (hu : u.toNat < 2 * p) :
    CompPoly.CPolynomial.NTTFast.Packed.reduceOnce p u = reduceSign p u := by
  rw [reduceSign_eq _ hu, CompPoly.CPolynomial.NTTFast.Packed.reduceOnce_eq]
  rfl

/-- Reducing the lazy cube of a canonical word once gives the field cube. -/
theorem reduceOnce_cubeLazy (a : F) :
    CompPoly.CPolynomial.NTTFast.Packed.reduceOnce p (cubeLazy p a.val) = (a ^ 3).val := by
  rw [reduceOnce_eq_reduceSign (cubeLazy_lt a), ← cubeSign_val]
  rfl

/-- The seventh power of a canonical Montgomery word, canonical, is the field power. -/
theorem pow7Sign_val (a : F) : pow7Sign p a.val = (a ^ 7).val := by
  have ha : a.val.toNat < p := a.property
  have ha2 : a.val.toNat < 2 * p := by omega
  -- `x2 = a ^ 2`, canonical.
  have hx2 : mulSign p a.val a.val = (a * a).val := by
    obtain ⟨hlt, hc⟩ := reduceSign_cast (mulLazy_spec ha ha2).1
    exact eq_val_of_cast _ hlt (by
      rw [mulSign, hc]; exact cast_mulLazy a a a.val (val_toNat_cast a) ha2)
  have hx3 : mulSign p (a * a).val a.val = (a * a * a).val := by
    obtain ⟨hlt, hc⟩ := reduceSign_cast (mulLazy_spec (a * a).property ha2).1
    exact eq_val_of_cast _ hlt (by
      rw [mulSign, hc]; exact cast_mulLazy (a * a) a a.val (val_toNat_cast a) ha2)
  have h4 := mulLazy_spec (a * a).property (by have := (a * a).property; omega :
    (a * a).val.toNat < 2 * p)
  have h4c : ((mulLazy p (a * a).val (a * a).val).toNat : ZMod p) =
      toField (a * a * (a * a)) * ((2 ^ 32 : ℕ) : ZMod p) :=
    cast_mulLazy (a * a) (a * a) _ (val_toNat_cast _) (by have := (a * a).property; omega)
  have h7 := mulLazy_spec (a * a * a).property h4.1
  obtain ⟨hlt, hc⟩ := reduceSign_cast h7.1
  unfold pow7Sign
  dsimp only
  rw [hx2, hx3, show a ^ 7 = a * a * a * (a * a * (a * a)) by ring]
  exact eq_val_of_cast _ hlt (by
    rw [mulSign, hc]; exact cast_mulLazy (a * a * a) (a * a * (a * a)) _ h4c h4.1)

/-- The lazy seventh power of a canonical word is below `2 p`. -/
theorem pow7Lazy_lt (a : F) : (pow7Lazy p a.val).toNat < 2 * p := by
  have ha : a.val.toNat < p := a.property
  have ha2 : a.val.toNat < 2 * p := by omega
  have hx2 := mulSign_lt ha ha2
  have h4 := (mulLazy_spec hx2 (by omega : (mulSign p a.val a.val).toNat < 2 * p)).1
  exact (mulLazy_spec (mulSign_lt hx2 ha2) h4).1

/-- Reducing the lazy seventh power of a canonical word once gives the field power. -/
theorem reduceOnce_pow7Lazy (a : F) :
    CompPoly.CPolynomial.NTTFast.Packed.reduceOnce p (pow7Lazy p a.val) = (a ^ 7).val := by
  rw [reduceOnce_eq_reduceSign (pow7Lazy_lt a), ← pow7Sign_val]
  rfl

/-- Reducing a canonical word once leaves it. -/
theorem reduceOnce_val (x : F) :
    CompPoly.CPolynomial.NTTFast.Packed.reduceOnce p x.val = x.val := by
  rw [CompPoly.CPolynomial.NTTFast.Packed.reduceOnce_eq]
  exact ite_eq_left (by rw [UInt32.lt_iff_toNat_lt, modulus32_toNat']; exact x.property)

end CompStark.Poseidon2
