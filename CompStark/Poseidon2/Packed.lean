/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.Montgomery.Native32Words
public import CompPoly.Univariate.NTTFast.Packed.Native
public import CompStark.Poseidon2.Basic

/-! # Packed Poseidon2 groups

Poseidon2 runs on eight states at once. The states are Montgomery words in a `ByteArray`; the group
of width `t` at word `i` holds coordinate `j` of state `l` at word `i + 8 j + l`, so every round
is eight-lane straight-line code that the C compiler vectorizes. This module has the buffers, their
bounds and the packed constants the round kernels (`PackedKernels`) work on.
-/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open Montgomery.Native32.Words (Fits Fits.mono Fits.of_size inBounds)
open Montgomery.Native32 (Mont32Field FastField)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset putWords size_putWords wordOffset_toNat
  encodeFields usize_numeral)

/-- The group at `i` fits the buffer. -/
abbrev GroupFits (b : ByteArray) (i : USize) : Prop := Fits b i 127

theorem storeBounds16 {b : ByteArray} {i : USize} (h : GroupFits b i) (k : USize)
    (hk : k.toNat ≤ 120) : ((i + k) * 4).toNat + 4 * 8 ≤ b.size ∧
      ((i + k) * 4).toNat + 4 * 8 < USize.size := by
  rw [wordOffset_toNat _ _ (by omega)]
  omega

/-- Words `i + k, …, i + k + 7` of a buffer of size `n`, overwritten without a branch. -/
@[inline] def store8 {n : Nat} (st : { x : ByteArray // x.size = n }) (i k : USize)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32)
    (h : ((i + k) * 4).toNat + 4 * 8 ≤ n ∧ ((i + k) * 4).toNat + 4 * 8 < USize.size) :
    { x : ByteArray // x.size = n } :=
  ⟨putWords st ((i + k) * 4) 8 v0 v1 v2 v3 v4 v5 v6 v7 0 0 0 0 0 0 0 0 h, size_putWords ..⟩

/-- Words `i, …, i + 7` written back unchanged. The result is exclusive, so a kernel that starts
from it lets the compiler drop the exclusivity checks of its stores and interleave its loads with
them. -/
@[inline] def touch8 (b : ByteArray) (i : USize) (h : Fits b i 7) :
    { x : ByteArray // x.size = b.size } :=
  store8 ⟨b, rfl⟩ i 0
    (readUOffset b i 0 (inBounds h 0 (by simp only [USize.reduceToNat]; decide)))
    (readUOffset b i 1 (inBounds h 1 (by simp only [USize.reduceToNat]; decide)))
    (readUOffset b i 2 (inBounds h 2 (by simp only [USize.reduceToNat]; decide)))
    (readUOffset b i 3 (inBounds h 3 (by simp only [USize.reduceToNat]; decide)))
    (readUOffset b i 4 (inBounds h 4 (by simp only [USize.reduceToNat]; decide)))
    (readUOffset b i 5 (inBounds h 5 (by simp only [USize.reduceToNat]; decide)))
    (readUOffset b i 6 (inBounds h 6 (by simp only [USize.reduceToNat]; decide)))
    (readUOffset b i 7 (inBounds h 7 (by simp only [USize.reduceToNat]; decide)))
    (by rw [wordOffset_toNat _ _ (by simp only [USize.toNat_zero]; omega)]
        simp only [USize.toNat_zero]; omega)

/-- A buffer of `n` bytes. -/
abbrev Buf (n : Nat) : Type := { x : ByteArray // x.size = n }

/-- A kernel's output on a buffer of `n` bytes, as a buffer of `n` bytes. -/
@[inline] def Buf.of {n : Nat} (b : Buf n) (x : { y : ByteArray // y.size = b.1.size }) : Buf n :=
  ⟨x.1, x.2.trans b.2⟩

/-- The width-16 group at `i` fits buffers of `n` bytes. -/
abbrev Room16 (n : Nat) (i : USize) : Prop := 4 * (i.toNat + 127) + 3 < n ∧ n < USize.size

theorem Room16.fits {n : Nat} {i : USize} (h : Room16 n i) (b : Buf n) : GroupFits b.1 i := by
  unfold GroupFits Fits
  rw [b.2]
  exact h

/-- The constants of a width-16 instance as packed Montgomery words: the rows of the initial and
terminal full rounds, and the partial rounds' constants. -/
structure Packed16 where
  initial : ByteArray
  internal : Array UInt32
  terminal : ByteArray

/-- Pack the constants of a width-16 instance over the Montgomery field. -/
def Packed16.ofParams {p : ℕ} [Mont32Field p] (P : Params (FastField p) 16) : Packed16 where
  initial := encodeFields (P.initial.foldl (fun acc c ↦ acc ++ c.toArray) #[])
  internal := (P.internal.map Subtype.val).toArray
  terminal := encodeFields (P.terminal.foldl (fun acc c ↦ acc ++ c.toArray) #[])

/-- Four rows of sixteen constants fit `rc`. -/
abbrev Rows16 (rc : ByteArray) : Prop := 4 * 64 ≤ rc.size ∧ rc.size < USize.size

theorem lt_four_toNat {k : USize} (hk : k < 4) : k.toNat < 4 := by
  rw [USize.lt_iff_toNat_lt, usize_numeral 4 (by decide)] at hk
  exact hk

/-- Row `k < 4` of `rc` fits it. -/
theorem Rows16.fits {rc : ByteArray} (h : Rows16 rc) (k : USize) (hk : k < 4) :
    Fits rc (16 * k) 15 := by
  have hk' := lt_four_toNat hk
  have e : (16 * k).toNat = 16 * k.toNat := by
    have := USize.le_size
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    rw [USize.toNat_mul, usize_numeral 16 (by decide), hsize]
    exact Nat.mod_eq_of_lt (by omega)
  unfold Fits
  rw [e]
  omega

/-- The constants of `K` fit their buffers. -/
abbrev Packed16.Fits (K : Packed16) : Prop := Rows16 K.initial ∧ Rows16 K.terminal

/-- The width-24 group at `i` fits the buffer. -/
abbrev GroupFits24 (b : ByteArray) (i : USize) : Prop := Fits b i 191

theorem storeBounds24 {b : ByteArray} {i : USize} (h : GroupFits24 b i) (k : USize)
    (hk : k.toNat ≤ 184) : ((i + k) * 4).toNat + 4 * 8 ≤ b.size ∧
      ((i + k) * 4).toNat + 4 * 8 < USize.size := by
  rw [wordOffset_toNat _ _ (by omega)]
  omega

/-- The width-24 group at `i` fits buffers of `n` bytes. -/
abbrev Room24 (n : Nat) (i : USize) : Prop := 4 * (i.toNat + 191) + 3 < n ∧ n < USize.size

theorem Room24.fits {n : Nat} {i : USize} (h : Room24 n i) (b : Buf n) : GroupFits24 b.1 i := by
  unfold GroupFits24 Fits
  rw [b.2]
  exact h

/-- Four rows of twenty-four constants fit `rc`. -/
abbrev Rows24 (rc : ByteArray) : Prop := 4 * 96 ≤ rc.size ∧ rc.size < USize.size

/-- Row `k < 4` of `rc` fits it. -/
theorem Rows24.fits {rc : ByteArray} (h : Rows24 rc) (k : USize) (hk : k < 4) :
    Fits rc (24 * k) 23 := by
  have hk' := lt_four_toNat hk
  have e : (24 * k).toNat = 24 * k.toNat := by
    have := USize.le_size
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    rw [USize.toNat_mul, usize_numeral 24 (by decide), hsize]
    exact Nat.mod_eq_of_lt (by omega)
  unfold Fits
  rw [e]
  omega

/-- The constants of a width-24 instance as packed Montgomery words. -/
structure Packed24 where
  initial : ByteArray
  internal : Array UInt32
  terminal : ByteArray

/-- Pack the constants of a width-24 instance over the Montgomery field. -/
def Packed24.ofParams {p : ℕ} [Mont32Field p] (P : Params (FastField p) 24) : Packed24 where
  initial := encodeFields (P.initial.foldl (fun acc c ↦ acc ++ c.toArray) #[])
  internal := (P.internal.map Subtype.val).toArray
  terminal := encodeFields (P.terminal.foldl (fun acc c ↦ acc ++ c.toArray) #[])

/-- The constants of `K` fit their buffers. -/
abbrev Packed24.Fits (K : Packed24) : Prop := Rows24 K.initial ∧ Rows24 K.terminal

end CompStark.Poseidon2.Packed
