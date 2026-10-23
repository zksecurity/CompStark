/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgWords

/-! # Programs on groups of rows

A program (`Prog`) runs on a group of `16 · nm` rows at once (`groupMachine`): the state is one
buffer holding the four accumulators and the registers, `16 · nm` Montgomery words each, and every
instruction is one kernel over the group's words, sixteen words at a time. An accumulation adds an
operand times the weight's four words to the four accumulators in one pass.

The trace's current rows and the transposed preprocessed and permutation traces are read where
they are: column `c` of the group at words `cb + c · cs` and `tcb + c · tcs`.
-/

@[expose] public section
namespace CompStark.Stark.Prog
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read putWords size_putWords toNat_usize_le
  usize_add_toNat_of_le)
open Montgomery.Native32 (Mont32Field FastField)

/-- What a program reads on a group of `16 · nm` rows, whose registers are `rb` words apart: the
trace's current rows (column `c` at words `cb + c · cs` of `view`), the loads (`L`; the transposed
traces' column `c` at words `tcb + c · tcs`, the periodic columns and selectors from word `sb`),
and the scalars' and the weights' words. -/
structure GroupEnv where
  nm : Nat
  rb : USize
  view : ByteArray
  cb : USize
  cs : USize
  L : Loads
  tcb : USize
  tcs : USize
  sb : USize
  scal : Array UInt32
  wts : Array UInt32

/-- Sixteen words from word `i` fit `b`: the words read by `ld`. -/
abbrev Win (b : ByteArray) (i : USize) : Prop := 4 * (i.toNat + 16) ≤ b.size ∧
  4 * (i.toNat + 16) < USize.size

theorem usize_lit (n : Nat) (h : n < 4294967296) : (n.toUSize).toNat = n :=
  USize.toNat_ofNat_of_lt' (lt_of_lt_of_le h USize.le_size)

/-- `k` with a proof that sixteen words from word `i` fit `b`, or `d`. -/
@[inline] def withWin {α : Type} (b : @& ByteArray) (i : USize) (d : α) (k : Win b i → α) : α :=
  if h : i ≤ i + (16 : USize) ∧ i + (16 : USize) ≤ b.usize >>> (2 : USize) then
    k (by
      have h1 := usize_add_toNat_of_le i 16 h.1
      have h2 := USize.le_iff_toNat_le.mp h.2
      have h3 := toNat_usize_le b
      have h4 : (16 : USize).toNat = 16 := usize_lit 16 (by decide)
      have h5 := b.usize.toNat_lt_size
      have h6 : (2 : USize).toNat % System.Platform.numBits = 2 := by
        have h7 : (2 : USize).toNat = 2 := usize_lit 2 (by decide)
        rw [h7]; rcases System.Platform.numBits_eq with e | e <;> rw [e]
      rw [h1, h4, USize.toNat_shiftRight, h6, Nat.shiftRight_eq_div_pow] at h2
      omega)
  else d

theorem win_off {b : ByteArray} {i : USize} (h : Win b i) (k : Nat) (hk : k ≤ 15) :
    ((i + k.toUSize) * 4).toNat = 4 * (i.toNat + k) ∧ 4 * (i.toNat + k) + 4 ≤ b.size := by
  obtain ⟨h1, h2⟩ := h
  have hk' : k.toUSize.toNat = k := usize_lit _ (by omega)
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have h4 : (4 : USize).toNat = 4 := usize_lit 4 (by decide)
  have e1 : (i.toNat + k) % USize.size = i.toNat + k := Nat.mod_eq_of_lt (by omega)
  have e2 : (i.toNat + k) * 4 % USize.size = (i.toNat + k) * 4 := Nat.mod_eq_of_lt (by omega)
  rw [USize.toNat_mul, USize.toNat_add, hk', h4, hsz, e1, e2]
  omega

/-- Word `k` of the sixteen from word `i`. -/
@[inline] def ld (b : @& ByteArray) (i : USize) (h : Win b i) (k : Nat)
    (hk : k ≤ 15 := by decide) : UInt32 :=
  b.ugetUInt32LE ((i + k.toUSize) * 4) (by rw [(win_off h k hk).1]; exact (win_off h k hk).2)

theorem win_bytes {b : ByteArray} {i : USize} (h : Win b i) :
    (i * 4).toNat + 4 * 16 ≤ b.size ∧ (i * 4).toNat + 4 * 16 < USize.size := by
  obtain ⟨h1, h2⟩ := h
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have h4 : (4 : USize).toNat = 4 := usize_lit 4 (by decide)
  rw [USize.toNat_mul, h4, hsz, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Sixteen words stored from word `i`, in the window. -/
@[inline] def st16 (s : ByteArray) (i : USize) (h : Win s i)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) : ByteArray :=
  putWords ⟨s, rfl⟩ (i * 4) 16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 (win_bytes h)

/-- `step s off` on the offsets `off, off + 16, …, off + 16 (j - 1)`. -/
@[specialize] def groups
    (step : ByteArray → USize → ByteArray) : Nat → ByteArray → USize → ByteArray
  | 0, s, _ => s
  | j + 1, s, off => groups step j (step s off) (off + 16)

/-! ### Kernels

A kernel runs sixteen words at a time, every sixteen `lanes16` on the operands' words as the state
holds them at that time, spelled out. -/

@[inline] def stepSS (f : UInt32 → UInt32 → UInt32) (d a b : USize) (s : ByteArray) (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin s (a + o) s fun ha ↦ withWin s (b + o) s fun hb ↦
    st16 s (d + o) hd
      (f (ld s (a + o) ha 0) (ld s (b + o) hb 0)) (f (ld s (a + o) ha 1) (ld s (b + o) hb 1))
      (f (ld s (a + o) ha 2) (ld s (b + o) hb 2)) (f (ld s (a + o) ha 3) (ld s (b + o) hb 3))
      (f (ld s (a + o) ha 4) (ld s (b + o) hb 4)) (f (ld s (a + o) ha 5) (ld s (b + o) hb 5))
      (f (ld s (a + o) ha 6) (ld s (b + o) hb 6)) (f (ld s (a + o) ha 7) (ld s (b + o) hb 7))
      (f (ld s (a + o) ha 8) (ld s (b + o) hb 8)) (f (ld s (a + o) ha 9) (ld s (b + o) hb 9))
      (f (ld s (a + o) ha 10) (ld s (b + o) hb 10)) (f (ld s (a + o) ha 11) (ld s (b + o) hb 11))
      (f (ld s (a + o) ha 12) (ld s (b + o) hb 12)) (f (ld s (a + o) ha 13) (ld s (b + o) hb 13))
      (f (ld s (a + o) ha 14) (ld s (b + o) hb 14)) (f (ld s (a + o) ha 15) (ld s (b + o) hb 15))

@[inline] def stepSE (f : UInt32 → UInt32 → UInt32) (e : @& ByteArray) (d a b : USize)
    (s : ByteArray) (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin s (a + o) s fun ha ↦ withWin e (b + o) s fun hb ↦
    st16 s (d + o) hd
      (f (ld s (a + o) ha 0) (ld e (b + o) hb 0)) (f (ld s (a + o) ha 1) (ld e (b + o) hb 1))
      (f (ld s (a + o) ha 2) (ld e (b + o) hb 2)) (f (ld s (a + o) ha 3) (ld e (b + o) hb 3))
      (f (ld s (a + o) ha 4) (ld e (b + o) hb 4)) (f (ld s (a + o) ha 5) (ld e (b + o) hb 5))
      (f (ld s (a + o) ha 6) (ld e (b + o) hb 6)) (f (ld s (a + o) ha 7) (ld e (b + o) hb 7))
      (f (ld s (a + o) ha 8) (ld e (b + o) hb 8)) (f (ld s (a + o) ha 9) (ld e (b + o) hb 9))
      (f (ld s (a + o) ha 10) (ld e (b + o) hb 10)) (f (ld s (a + o) ha 11) (ld e (b + o) hb 11))
      (f (ld s (a + o) ha 12) (ld e (b + o) hb 12)) (f (ld s (a + o) ha 13) (ld e (b + o) hb 13))
      (f (ld s (a + o) ha 14) (ld e (b + o) hb 14)) (f (ld s (a + o) ha 15) (ld e (b + o) hb 15))

@[inline] def stepES (f : UInt32 → UInt32 → UInt32) (e : @& ByteArray) (d a b : USize)
    (s : ByteArray) (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin e (a + o) s fun ha ↦ withWin s (b + o) s fun hb ↦
    st16 s (d + o) hd
      (f (ld e (a + o) ha 0) (ld s (b + o) hb 0)) (f (ld e (a + o) ha 1) (ld s (b + o) hb 1))
      (f (ld e (a + o) ha 2) (ld s (b + o) hb 2)) (f (ld e (a + o) ha 3) (ld s (b + o) hb 3))
      (f (ld e (a + o) ha 4) (ld s (b + o) hb 4)) (f (ld e (a + o) ha 5) (ld s (b + o) hb 5))
      (f (ld e (a + o) ha 6) (ld s (b + o) hb 6)) (f (ld e (a + o) ha 7) (ld s (b + o) hb 7))
      (f (ld e (a + o) ha 8) (ld s (b + o) hb 8)) (f (ld e (a + o) ha 9) (ld s (b + o) hb 9))
      (f (ld e (a + o) ha 10) (ld s (b + o) hb 10)) (f (ld e (a + o) ha 11) (ld s (b + o) hb 11))
      (f (ld e (a + o) ha 12) (ld s (b + o) hb 12)) (f (ld e (a + o) ha 13) (ld s (b + o) hb 13))
      (f (ld e (a + o) ha 14) (ld s (b + o) hb 14)) (f (ld e (a + o) ha 15) (ld s (b + o) hb 15))

@[inline] def stepEE (f : UInt32 → UInt32 → UInt32) (e : @& ByteArray) (d a b : USize)
    (s : ByteArray) (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin e (a + o) s fun ha ↦ withWin e (b + o) s fun hb ↦
    st16 s (d + o) hd
      (f (ld e (a + o) ha 0) (ld e (b + o) hb 0)) (f (ld e (a + o) ha 1) (ld e (b + o) hb 1))
      (f (ld e (a + o) ha 2) (ld e (b + o) hb 2)) (f (ld e (a + o) ha 3) (ld e (b + o) hb 3))
      (f (ld e (a + o) ha 4) (ld e (b + o) hb 4)) (f (ld e (a + o) ha 5) (ld e (b + o) hb 5))
      (f (ld e (a + o) ha 6) (ld e (b + o) hb 6)) (f (ld e (a + o) ha 7) (ld e (b + o) hb 7))
      (f (ld e (a + o) ha 8) (ld e (b + o) hb 8)) (f (ld e (a + o) ha 9) (ld e (b + o) hb 9))
      (f (ld e (a + o) ha 10) (ld e (b + o) hb 10)) (f (ld e (a + o) ha 11) (ld e (b + o) hb 11))
      (f (ld e (a + o) ha 12) (ld e (b + o) hb 12)) (f (ld e (a + o) ha 13) (ld e (b + o) hb 13))
      (f (ld e (a + o) ha 14) (ld e (b + o) hb 14)) (f (ld e (a + o) ha 15) (ld e (b + o) hb 15))

@[inline] def stepSW (f : UInt32 → UInt32 → UInt32) (d a : USize) (c : UInt32) (s : ByteArray)
    (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin s (a + o) s fun ha ↦
    st16 s (d + o) hd
      (f (ld s (a + o) ha 0) c) (f (ld s (a + o) ha 1) c) (f (ld s (a + o) ha 2) c)
      (f (ld s (a + o) ha 3) c) (f (ld s (a + o) ha 4) c) (f (ld s (a + o) ha 5) c)
      (f (ld s (a + o) ha 6) c) (f (ld s (a + o) ha 7) c) (f (ld s (a + o) ha 8) c)
      (f (ld s (a + o) ha 9) c) (f (ld s (a + o) ha 10) c) (f (ld s (a + o) ha 11) c)
      (f (ld s (a + o) ha 12) c) (f (ld s (a + o) ha 13) c) (f (ld s (a + o) ha 14) c)
      (f (ld s (a + o) ha 15) c)

@[inline] def stepEW (f : UInt32 → UInt32 → UInt32) (e : @& ByteArray) (d a : USize)
    (c : UInt32) (s : ByteArray) (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin e (a + o) s fun ha ↦
    st16 s (d + o) hd
      (f (ld e (a + o) ha 0) c) (f (ld e (a + o) ha 1) c) (f (ld e (a + o) ha 2) c)
      (f (ld e (a + o) ha 3) c) (f (ld e (a + o) ha 4) c) (f (ld e (a + o) ha 5) c)
      (f (ld e (a + o) ha 6) c) (f (ld e (a + o) ha 7) c) (f (ld e (a + o) ha 8) c)
      (f (ld e (a + o) ha 9) c) (f (ld e (a + o) ha 10) c) (f (ld e (a + o) ha 11) c)
      (f (ld e (a + o) ha 12) c) (f (ld e (a + o) ha 13) c) (f (ld e (a + o) ha 14) c)
      (f (ld e (a + o) ha 15) c)

@[inline] def stepWS (f : UInt32 → UInt32 → UInt32) (d a : USize) (c : UInt32) (s : ByteArray)
    (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin s (a + o) s fun ha ↦
    st16 s (d + o) hd
      (f c (ld s (a + o) ha 0)) (f c (ld s (a + o) ha 1)) (f c (ld s (a + o) ha 2))
      (f c (ld s (a + o) ha 3)) (f c (ld s (a + o) ha 4)) (f c (ld s (a + o) ha 5))
      (f c (ld s (a + o) ha 6)) (f c (ld s (a + o) ha 7)) (f c (ld s (a + o) ha 8))
      (f c (ld s (a + o) ha 9)) (f c (ld s (a + o) ha 10)) (f c (ld s (a + o) ha 11))
      (f c (ld s (a + o) ha 12)) (f c (ld s (a + o) ha 13)) (f c (ld s (a + o) ha 14))
      (f c (ld s (a + o) ha 15))

@[inline] def stepWE (f : UInt32 → UInt32 → UInt32) (e : @& ByteArray) (d a : USize)
    (c : UInt32) (s : ByteArray) (o : USize) :
    ByteArray :=
  withWin s (d + o) s fun hd ↦ withWin e (a + o) s fun ha ↦
    st16 s (d + o) hd
      (f c (ld e (a + o) ha 0)) (f c (ld e (a + o) ha 1)) (f c (ld e (a + o) ha 2))
      (f c (ld e (a + o) ha 3)) (f c (ld e (a + o) ha 4)) (f c (ld e (a + o) ha 5))
      (f c (ld e (a + o) ha 6)) (f c (ld e (a + o) ha 7)) (f c (ld e (a + o) ha 8))
      (f c (ld e (a + o) ha 9)) (f c (ld e (a + o) ha 10)) (f c (ld e (a + o) ha 11))
      (f c (ld e (a + o) ha 12)) (f c (ld e (a + o) ha 13)) (f c (ld e (a + o) ha 14))
      (f c (ld e (a + o) ha 15))

/-- Sixteen copies of `c` into `d + o`. -/
@[inline] def stepW (d : USize) (c : UInt32) (s : ByteArray) (o : USize) : ByteArray :=
  withWin s (d + o) s fun hd ↦ st16 s (d + o) hd
  (c) (c) (c) (c) (c) (c) (c) (c) (c) (c) (c) (c) (c) (c) (c) (c)

/-- `B = 16 nm` copies of `c` into word `d`. -/
@[inline] def fill (nm : Nat) (s : ByteArray) (d : USize) (c : UInt32) : ByteArray :=
  groups (stepW d c) nm s 0

/-- `B = 16 nm` words from word `a` of `e` into word `d`. -/
@[inline] def copy (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize) : ByteArray :=
  groups (stepEW (fun x _ ↦ x) e d a 0) nm s 0

/-- Column `c` of a row-major matrix of width `w` at the rows `next[r0 + o + k]` into `d + o`. -/
@[inline] def stepGather (m : @& ByteArray) (w c : Nat) (next : @& Array Nat) (r0 : Nat) (d : USize)
    (s : ByteArray) (o : USize) : ByteArray :=
  withWin s (d + o) s fun hd ↦ st16 s (d + o) hd
  (read m (next.getD (r0 + o.toNat + 0) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 1) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 2) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 3) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 4) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 5) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 6) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 7) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 8) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 9) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 10) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 11) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 12) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 13) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 14) 0 * w + c))
  (read m (next.getD (r0 + o.toNat + 15) 0 * w + c))

/-- Column `c` of a row-major matrix of width `w` at the rows `next[r0 + k]` into word `d`. -/
@[inline] def gather (nm : Nat) (s : ByteArray) (d : USize) (m : @& ByteArray) (w c : Nat)
    (next : @& Array Nat) (r0 : Nat) : ByteArray :=
  groups (stepGather m w c next r0 d) nm s 0

variable (p : ℕ) [Mont32Field p]

/-- Multiply canonical Montgomery residues with the positive Montgomery quotient `q`: the high words
of `x y` and of `q p` subtracted (`sub`), which vectorizes to word multiplications and a minimum. -/
@[inline] def mulM (x y : UInt32) : UInt32 :=
  let z := x.toUInt64 * y.toUInt64
  let q := z.toUInt32 * (0 - Mont32Field.montgomeryNegInv (modulus := p))
  sub p (z >>> 32).toUInt32 ((q.toUInt64 * Mont32Field.modulus64 (modulus := p)) >>> 32).toUInt32

/-- The operation on words of the group kernels. -/
@[inline] def Op.wordG : Op → UInt32 → UInt32 → UInt32
  | .add => CompPoly.CPolynomial.NTTFast.Packed.add p
  | .sub => CompPoly.CPolynomial.NTTFast.Packed.sub p
  | .mul => mulM p

/-- Sixteen words of accumulator `j` (word `j · rb`) plus the operand's words times `w`. -/
@[inline] def stepAccS (rb j : USize) (a : USize) (w : UInt32) (s : ByteArray)
    (o : USize) : ByteArray :=
  withWin s (j * rb + o) s fun h ↦ withWin s (a + o) s fun ha ↦
    st16 s (j * rb + o) h
      (add p (ld s (j * rb + o) h 0) (mulM p (ld s (a + o) ha 0) w))
      (add p (ld s (j * rb + o) h 1) (mulM p (ld s (a + o) ha 1) w))
      (add p (ld s (j * rb + o) h 2) (mulM p (ld s (a + o) ha 2) w))
      (add p (ld s (j * rb + o) h 3) (mulM p (ld s (a + o) ha 3) w))
      (add p (ld s (j * rb + o) h 4) (mulM p (ld s (a + o) ha 4) w))
      (add p (ld s (j * rb + o) h 5) (mulM p (ld s (a + o) ha 5) w))
      (add p (ld s (j * rb + o) h 6) (mulM p (ld s (a + o) ha 6) w))
      (add p (ld s (j * rb + o) h 7) (mulM p (ld s (a + o) ha 7) w))
      (add p (ld s (j * rb + o) h 8) (mulM p (ld s (a + o) ha 8) w))
      (add p (ld s (j * rb + o) h 9) (mulM p (ld s (a + o) ha 9) w))
      (add p (ld s (j * rb + o) h 10) (mulM p (ld s (a + o) ha 10) w))
      (add p (ld s (j * rb + o) h 11) (mulM p (ld s (a + o) ha 11) w))
      (add p (ld s (j * rb + o) h 12) (mulM p (ld s (a + o) ha 12) w))
      (add p (ld s (j * rb + o) h 13) (mulM p (ld s (a + o) ha 13) w))
      (add p (ld s (j * rb + o) h 14) (mulM p (ld s (a + o) ha 14) w))
      (add p (ld s (j * rb + o) h 15) (mulM p (ld s (a + o) ha 15) w))

/-- Sixteen words of the four accumulators plus the operand's words times the weights `w`'s. -/
@[inline] def stepAcc4S (rb : USize) (a : USize) (w0 w1 w2 w3 : UInt32) (s : ByteArray)
    (o : USize) : ByteArray :=
  let s := stepAccS p rb 0 a w0 s o
  let s := stepAccS p rb 1 a w1 s o
  let s := stepAccS p rb 2 a w2 s o
  stepAccS p rb 3 a w3 s o

/-- The accumulators plus the operand's words times the weights `w`'s four words. -/
@[inline] def accS (nm : Nat) (rb : USize) (s : ByteArray) (a : USize) (wts : @& Array UInt32)
    (w : Nat) : ByteArray :=
  groups (stepAcc4S p rb a (wts.getD (4 * w) 0) (wts.getD (4 * w + 1) 0)
    (wts.getD (4 * w + 2) 0) (wts.getD (4 * w + 3) 0)) nm s 0

/-- Sixteen words of accumulator `j` (word `j · rb`) plus the operand's words times `w`. -/
@[inline] def stepAccE (rb j : USize) (e : @& ByteArray) (a : USize) (w : UInt32)
    (s : ByteArray) (o : USize) : ByteArray :=
  withWin s (j * rb + o) s fun h ↦ withWin e (a + o) s fun ha ↦
    st16 s (j * rb + o) h
      (add p (ld s (j * rb + o) h 0) (mulM p (ld e (a + o) ha 0) w))
      (add p (ld s (j * rb + o) h 1) (mulM p (ld e (a + o) ha 1) w))
      (add p (ld s (j * rb + o) h 2) (mulM p (ld e (a + o) ha 2) w))
      (add p (ld s (j * rb + o) h 3) (mulM p (ld e (a + o) ha 3) w))
      (add p (ld s (j * rb + o) h 4) (mulM p (ld e (a + o) ha 4) w))
      (add p (ld s (j * rb + o) h 5) (mulM p (ld e (a + o) ha 5) w))
      (add p (ld s (j * rb + o) h 6) (mulM p (ld e (a + o) ha 6) w))
      (add p (ld s (j * rb + o) h 7) (mulM p (ld e (a + o) ha 7) w))
      (add p (ld s (j * rb + o) h 8) (mulM p (ld e (a + o) ha 8) w))
      (add p (ld s (j * rb + o) h 9) (mulM p (ld e (a + o) ha 9) w))
      (add p (ld s (j * rb + o) h 10) (mulM p (ld e (a + o) ha 10) w))
      (add p (ld s (j * rb + o) h 11) (mulM p (ld e (a + o) ha 11) w))
      (add p (ld s (j * rb + o) h 12) (mulM p (ld e (a + o) ha 12) w))
      (add p (ld s (j * rb + o) h 13) (mulM p (ld e (a + o) ha 13) w))
      (add p (ld s (j * rb + o) h 14) (mulM p (ld e (a + o) ha 14) w))
      (add p (ld s (j * rb + o) h 15) (mulM p (ld e (a + o) ha 15) w))

/-- Sixteen words of the four accumulators plus the operand's words times the weights `w`'s. -/
@[inline] def stepAcc4E (rb : USize) (e : @& ByteArray) (a : USize) (w0 w1 w2 w3 : UInt32)
    (s : ByteArray)
    (o : USize) : ByteArray :=
  let s := stepAccE p rb 0 e a w0 s o
  let s := stepAccE p rb 1 e a w1 s o
  let s := stepAccE p rb 2 e a w2 s o
  stepAccE p rb 3 e a w3 s o

/-- The accumulators plus the operand's words times the weights `w`'s four words. -/
@[inline] def accE (nm : Nat) (rb : USize) (s : ByteArray) (e : @& ByteArray) (a : USize)
    (wts : @& Array UInt32)
    (w : Nat) : ByteArray :=
  groups (stepAcc4E p rb e a (wts.getD (4 * w) 0) (wts.getD (4 * w + 1) 0)
    (wts.getD (4 * w + 2) 0) (wts.getD (4 * w + 3) 0)) nm s 0

/-- Sixteen words of accumulator `j` (word `j · rb`) plus the operand's words times `w`. -/
@[inline] def stepAccW (rb j : USize) (c : UInt32) (w : UInt32) (s : ByteArray)
    (o : USize) : ByteArray :=
  withWin s (j * rb + o) s fun h ↦ 
    st16 s (j * rb + o) h
      (add p (ld s (j * rb + o) h 0) (mulM p (c) w)) (add p (ld s (j * rb + o) h 1) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 2) (mulM p (c) w)) (add p (ld s (j * rb + o) h 3) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 4) (mulM p (c) w)) (add p (ld s (j * rb + o) h 5) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 6) (mulM p (c) w)) (add p (ld s (j * rb + o) h 7) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 8) (mulM p (c) w)) (add p (ld s (j * rb + o) h 9) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 10) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 11) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 12) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 13) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 14) (mulM p (c) w))
      (add p (ld s (j * rb + o) h 15) (mulM p (c) w))

/-- Sixteen words of the four accumulators plus the operand's words times the weights `w`'s. -/
@[inline] def stepAcc4W (rb : USize) (c : UInt32) (w0 w1 w2 w3 : UInt32) (s : ByteArray)
    (o : USize) : ByteArray :=
  let s := stepAccW p rb 0 c w0 s o
  let s := stepAccW p rb 1 c w1 s o
  let s := stepAccW p rb 2 c w2 s o
  stepAccW p rb 3 c w3 s o

/-- The accumulators plus the operand's words times the weights `w`'s four words. -/
@[inline] def accW (nm : Nat) (rb : USize) (s : ByteArray) (c : UInt32) (wts : @& Array UInt32)
    (w : Nat) : ByteArray :=
  groups (stepAcc4W p rb c (wts.getD (4 * w) 0) (wts.getD (4 * w + 1) 0)
    (wts.getD (4 * w + 2) 0) (wts.getD (4 * w + 3) 0)) nm s 0

@[inline] def addSS (nm : Nat) (s : ByteArray) (d a b : USize) : ByteArray :=
  groups (stepSS (add p) d a b) nm s 0
@[inline] def addSE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepSE (add p) e d a b) nm s 0
@[inline] def addES (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepES (add p) e d a b) nm s 0
@[inline] def addEE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepEE (add p) e d a b) nm s 0
@[inline] def addSW (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
  groups (stepSW (add p) d a c) nm s 0
@[inline] def addEW (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
    (c : UInt32) : ByteArray :=
  groups (stepEW (add p) e d a c) nm s 0
@[inline] def addWS (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
  groups (stepWS (add p) d a c) nm s 0
@[inline] def addWE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
    (c : UInt32) : ByteArray :=
  groups (stepWE (add p) e d a c) nm s 0
@[inline] def subSS (nm : Nat) (s : ByteArray) (d a b : USize) : ByteArray :=
  groups (stepSS (sub p) d a b) nm s 0
@[inline] def subSE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepSE (sub p) e d a b) nm s 0
@[inline] def subES (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepES (sub p) e d a b) nm s 0
@[inline] def subEE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepEE (sub p) e d a b) nm s 0
@[inline] def subSW (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
  groups (stepSW (sub p) d a c) nm s 0
@[inline] def subEW (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
    (c : UInt32) : ByteArray :=
  groups (stepEW (sub p) e d a c) nm s 0
@[inline] def subWS (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
  groups (stepWS (sub p) d a c) nm s 0
@[inline] def subWE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
    (c : UInt32) : ByteArray :=
  groups (stepWE (sub p) e d a c) nm s 0
@[inline] def mulSS (nm : Nat) (s : ByteArray) (d a b : USize) : ByteArray :=
  groups (stepSS (mulM p) d a b) nm s 0
@[inline] def mulSE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepSE (mulM p) e d a b) nm s 0
@[inline] def mulES (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepES (mulM p) e d a b) nm s 0
@[inline] def mulEE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a b : USize) : ByteArray :=
  groups (stepEE (mulM p) e d a b) nm s 0
@[inline] def mulSW (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
  groups (stepSW (mulM p) d a c) nm s 0
@[inline] def mulEW (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
    (c : UInt32) : ByteArray :=
  groups (stepEW (mulM p) e d a c) nm s 0
@[inline] def mulWS (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
  groups (stepWS (mulM p) d a c) nm s 0
@[inline] def mulWE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
    (c : UInt32) : ByteArray :=
  groups (stepWE (mulM p) e d a c) nm s 0

/-- The periodic column `j` from word `a` into word `d`, zero if there is none. -/
@[noinline] def copyPer (nm : Nat) (s : ByteArray) (per : @& Array ByteArray) (j : Nat)
    (d a : USize) : ByteArray :=
  match per[j]? with
  | some c => copy nm s c d a
  | none => fill nm s d 0

/-- Scalar `i`'s word. -/
@[noinline] def scalAt (env : @& GroupEnv) (i : Nat) : UInt32 := env.scal.getD i 0

/-- Byte offset of register `r`, after the four accumulators. -/
@[inline] def regOff (env : @& GroupEnv) (r : Nat) : USize := (4 + r).toUSize * env.rb

/-- Byte offset of column `c` of the group's current rows. -/
@[inline] def colOff (env : @& GroupEnv) (c : Nat) : USize := env.cb + c.toUSize * env.cs

/-- Byte offset of column `c` of the group's transposed rows. -/
@[inline] def tcolOff (env : @& GroupEnv) (c : Nat) : USize := env.tcb + c.toUSize * env.tcs

/-- An operation on two operands of a group into register `d`. -/
@[inline] def binG (env : @& GroupEnv) (o : Op) (d : Nat) (a b : Opd (FastField p))
    (s : ByteArray) : ByteArray :=
  match o, a, b with
  | .add, .reg x, .reg y => addSS p env.nm s (regOff env d) (regOff env x) (regOff env y)
  | .add, .reg x, .cur y => addSE p env.nm s env.view (regOff env d) (regOff env x) (colOff env y)
  | .add, .cur x, .reg y => addES p env.nm s env.view (regOff env d) (colOff env x) (regOff env y)
  | .add, .cur x, .cur y => addEE p env.nm s env.view (regOff env d) (colOff env x) (colOff env y)
  | .add, .reg x, .const y => addSW p env.nm s (regOff env d) (regOff env x) y.val
  | .add, .cur x, .const y => addEW p env.nm s env.view (regOff env d) (colOff env x) y.val
  | .add, .const x, .reg y => addWS p env.nm s (regOff env d) (regOff env y) x.val
  | .add, .const x, .cur y => addWE p env.nm s env.view (regOff env d) (colOff env y) x.val
  | .sub, .reg x, .reg y => subSS p env.nm s (regOff env d) (regOff env x) (regOff env y)
  | .sub, .reg x, .cur y => subSE p env.nm s env.view (regOff env d) (regOff env x) (colOff env y)
  | .sub, .cur x, .reg y => subES p env.nm s env.view (regOff env d) (colOff env x) (regOff env y)
  | .sub, .cur x, .cur y => subEE p env.nm s env.view (regOff env d) (colOff env x) (colOff env y)
  | .sub, .reg x, .const y => subSW p env.nm s (regOff env d) (regOff env x) y.val
  | .sub, .cur x, .const y => subEW p env.nm s env.view (regOff env d) (colOff env x) y.val
  | .sub, .const x, .reg y => subWS p env.nm s (regOff env d) (regOff env y) x.val
  | .sub, .const x, .cur y => subWE p env.nm s env.view (regOff env d) (colOff env y) x.val
  | .mul, .reg x, .reg y => mulSS p env.nm s (regOff env d) (regOff env x) (regOff env y)
  | .mul, .reg x, .cur y => mulSE p env.nm s env.view (regOff env d) (regOff env x) (colOff env y)
  | .mul, .cur x, .reg y => mulES p env.nm s env.view (regOff env d) (colOff env x) (regOff env y)
  | .mul, .cur x, .cur y => mulEE p env.nm s env.view (regOff env d) (colOff env x) (colOff env y)
  | .mul, .reg x, .const y => mulSW p env.nm s (regOff env d) (regOff env x) y.val
  | .mul, .cur x, .const y => mulEW p env.nm s env.view (regOff env d) (colOff env x) y.val
  | .mul, .const x, .reg y => mulWS p env.nm s (regOff env d) (regOff env y) x.val
  | .mul, .const x, .cur y => mulWE p env.nm s env.view (regOff env d) (colOff env y) x.val
  | o, .const x, .const y => fill env.nm s (regOff env d) (Op.wordG p o x.val y.val)

/-- A loaded column into register `d`. -/
@[inline] def loadG (env : @& GroupEnv) (d : Nat) (src : Src) (s : ByteArray) : ByteArray :=
  match src with
  | .next c => gather env.nm s (regOff env d) env.L.main env.L.w c env.L.next env.L.r0
  | .prepCur c => copy env.nm s env.L.prepT (regOff env d) (tcolOff env c)
  | .prepNext c => gather env.nm s (regOff env d) env.L.prep env.L.pw c env.L.next env.L.r0
  | .permCur c => copy env.nm s env.L.permT (regOff env d) (tcolOff env c)
  | .permNext c => gather env.nm s (regOff env d) env.L.perm env.L.rw c env.L.next env.L.r0
  | .periodic j => copyPer env.nm s env.L.per j (regOff env d) env.sb
  | .isFirstRow => copy env.nm s env.L.first (regOff env d) env.sb
  | .isLastRow => copy env.nm s env.L.last (regOff env d) env.sb
  | .isTransition => copy env.nm s env.L.trans (regOff env d) env.sb

/-- An accumulation of an operand of a group with weight `w`. -/
@[inline] def accG (env : @& GroupEnv) (a : Opd (FastField p)) (w : Nat) (s : ByteArray) :
    ByteArray :=
  match a with
  | .reg r => accS p env.nm env.rb s (regOff env r) env.wts w
  | .cur c => accE p env.nm env.rb s env.view (colOff env c) env.wts w
  | .const c => accW p env.nm env.rb s c.val env.wts w

/-- A program on a group of rows: the state is the group's buffer. -/
@[inline] def groupMachine (env : @& GroupEnv) : Machine (FastField p) ByteArray where
  load d src s := loadG env d src s
  scalar d i s := fill env.nm s (regOff env d) (scalAt env i)
  bin o d a b s := binG p env o d a b s
  acc a w s := accG p env a w s

/-- The four accumulators of a group of `B` rows cleared. -/
@[inline] def clearAccs (B : Nat) (st : ByteArray) : ByteArray :=
  fill (B / 16) (fill (B / 16) (fill (B / 16) (fill (B / 16) st 0 0) B.toUSize 0)
    (2 * B).toUSize 0) (3 * B).toUSize 0

/-- The group of a block of `B` rows, `B` a multiple of sixteen: the block's view and loads, the
transposed traces' columns `B` words apart, and the scalars' and the weights' words. -/
@[inline] def blockEnv (B : Nat) (v : View) (L : Loads) (scal wts : Array UInt32) : GroupEnv :=
  ⟨B / 16, B.toUSize, v.buf, v.cb.toUSize, v.cs.toUSize, L, 0, B.toUSize, L.r0.toUSize, scal, wts⟩

/-- A program's code on groups of rows, run by `run`: straight-line code generated for the
program, or the program interpreted. -/
structure GroupKernel (p : ℕ) [Mont32Field p] where
  code : Array (Instr (FastField p))
  run : GroupEnv → ByteArray → ByteArray
  run_eq : ∀ env s, run env s = Prog.run (groupMachine p env) code s

/-- Chunks of code run one after another. -/
def runChunks {σ : Type} (fs : List (σ → σ)) (s : σ) : σ := fs.foldl (fun s f ↦ f s) s

theorem runChunks_eq {F σ : Type} (M : Machine F σ) :
    ∀ (cs : List (List (Instr F))) (fs : List (σ → σ)),
      List.Forall₂ (fun c f ↦ ∀ s, f s = c.foldl (fun s i ↦ i.exec M s) s) cs fs →
      ∀ s, runChunks fs s = Prog.run M cs.flatten.toArray s
  | [], [], .nil, s => by
    simp only [runChunks, List.foldl_nil, List.flatten_nil, Prog.run, List.foldl_toArray']
  | c :: cs, f :: fs, .cons h t, s => by
    have ih := runChunks_eq M cs fs t (f s)
    simp only [runChunks, List.foldl_cons, Prog.run, List.foldl_toArray'] at ih ⊢
    rw [ih, h, List.flatten_cons, List.foldl_append]

end CompStark.Stark.Prog

