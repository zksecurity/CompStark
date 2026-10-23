/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Native
public import CompStark.Poseidon2.KoalaBear
import CompStark.Poseidon2.Unrolled
public import CompStark.Poseidon2.Arithmetic

/-! # Packed Poseidon2

Width-16 Poseidon2 on eight states at once. The states are Montgomery words in a `ByteArray`;
the group at word `i` holds coordinate `j` of state `l` at word `i + 8 j + l`, so every round
is eight-lane straight-line code that the C compiler vectorizes.
-/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul reduceOnce)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset putWords size_putWords wordOffset_toNat
  encodeFields usize_numeral)

/-- Words `i, …, i + n` of `b` fit, and `b` fits machine indices. -/
abbrev Fits (b : ByteArray) (i : USize) (n : Nat) : Prop :=
  4 * (i.toNat + n) + 3 < b.size ∧ b.size < USize.size

/-- The group at `i` fits the buffer. -/
abbrev GroupFits (b : ByteArray) (i : USize) : Prop := Fits b i 127

theorem inBounds {b : ByteArray} {i : USize} {n : Nat} (h : Fits b i n) (k : USize)
    (hk : k.toNat ≤ n) : 4 * (i.toNat + k.toNat) + 3 < b.size ∧ b.size < USize.size :=
  ⟨by omega, h.2⟩

theorem storeBounds16 {b : ByteArray} {i : USize} (h : GroupFits b i) (k : USize)
    (hk : k.toNat ≤ 120) : ((i + k) * 4).toNat + 4 * 8 ≤ b.size ∧
      ((i + k) * 4).toNat + 4 * 8 < USize.size := by
  rw [wordOffset_toNat _ _ (by omega)]
  omega

theorem Fits.mono {b : ByteArray} {i : USize} {m n : Nat} (h : Fits b i n) (hm : m ≤ n) :
    Fits b i m :=
  ⟨by omega, h.2⟩

theorem Fits.of_size {b b' : ByteArray} {i : USize} {n : Nat} (hs : b'.size = b.size)
    (h : Fits b i n) : Fits b' i n := by
  unfold Fits at *
  rw [hs]
  exact h

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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A partial round with constant `c` and internal diagonal `d` on the eight states at `i`. -/
@[noinline] def partial16 (c : UInt32) (d : @& ByteArray) (b : ByteArray) (i : USize)
    (hb : GroupFits b i) (hd : Fits d 0 15) : { x : ByteArray // x.size = b.size } :=
  p2_partial% 16 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The constant additions and S-boxes of a full round on the eight states at `i`. -/
@[noinline] def sbox16 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize)
    (hb : GroupFits b i) (hr : Fits rc r 15) : { x : ByteArray // x.size = b.size } :=
  p2_sbox% 16 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- `mat4` on every block of four coordinates of the eight states at `i`, words below `2 p`. -/
@[noinline] def mat4x16 (b : ByteArray) (i : USize) (hb : GroupFits b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mat4% 16 8

set_option maxRecDepth 16384 in
/-- The block-sum mixing of the external matrix on the eight states at `i`. -/
@[noinline] def mix16 (b : ByteArray) (i : USize) (hb : GroupFits b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mix% 16 8

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

/-- The external matrix on the eight states at `i`, as two passes. -/
@[inline] def external16 {n : Nat} (b : Buf n) (i : USize) (h : Room16 n i) : Buf n :=
  let b := b.of (mat4x16 b.1 i (h.fits b))
  b.of (mix16 b.1 i (h.fits b))

/-- A width-16 instance as packed Montgomery words. -/
structure Packed16 where
  initial : ByteArray
  internal : Array UInt32
  terminal : ByteArray
  diagonal : ByteArray

/-- Pack the constants of a width-16 instance over the Montgomery field. -/
def Packed16.ofParams (P : Params KoalaBear.Fast.Field 16) : Packed16 where
  initial := encodeFields (P.initial.foldl (fun acc c ↦ acc ++ c.toArray) #[])
  internal := (P.internal.map Subtype.val).toArray
  terminal := encodeFields (P.terminal.foldl (fun acc c ↦ acc ++ c.toArray) #[])
  diagonal := encodeFields P.diagonal.toArray

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

/-- Full rounds `k, …, 3` with the constant rows of `rc`, by recursion so the loop allocates
nothing. -/
def fullRoundsGo {n : Nat} (rc : @& ByteArray) (hr : Rows16 rc) (i : USize) (h : Room16 n i)
    (k : USize) (b : Buf n) : Buf n :=
  if hk : k < 4 then
    let b := b.of (sbox16 rc (16 * k) b.1 i (h.fits b) (hr.fits k hk))
    fullRoundsGo rc hr i h (k + 1) (external16 b i h)
  else b
termination_by 4 - k.toNat
decreasing_by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The partial rounds with the constants `k, …` of `K`. -/
def partialRoundsGo {n : Nat} (K : @& Packed16) (hd : Fits K.diagonal 0 15) (i : USize)
    (h : Room16 n i) (k : Nat) (b : Buf n) : Buf n :=
  if hk : k < K.internal.size then
    partialRoundsGo K hd i h (k + 1) (b.of (partial16 K.internal[k] K.diagonal b.1 i (h.fits b) hd))
  else b
termination_by K.internal.size - k

/-- The constants of `K` fit their buffers. -/
abbrev Packed16.Fits (K : Packed16) : Prop :=
  Rows16 K.initial ∧ Rows16 K.terminal ∧ Poseidon2.Packed.Fits K.diagonal 0 15

/-- The permutation of the eight states at `i`. -/
def permute16 (K : @& Packed16) (b : ByteArray) (i : USize) : ByteArray :=
  if h : GroupFits b i ∧ K.Fits then
    let s : Buf b.size := ⟨b, rfl⟩
    let s := external16 s i h.1
    let s := fullRoundsGo K.initial h.2.1 i h.1 0 s
    let s := partialRoundsGo K h.2.2.2 i h.1 0 s
    (fullRoundsGo K.terminal h.2.2.1 i h.1 0 s).1
  else b

end CompStark.Poseidon2.Packed
