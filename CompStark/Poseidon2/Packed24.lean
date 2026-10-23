/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Packed
import CompStark.Poseidon2.Unrolled

/-! # Packed width-24 Poseidon2

The width-24 permutation on eight states at once, with the round kernels of `Packed` generated at
width 24: coordinate `j` of state `l` of the group at word `i` is word `i + 8 j + l`. The first
nine diagonal entries of the internal matrix are those of width 16; the rest are products.
-/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul reduceOnce)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset putWords size_putWords wordOffset_toNat
  encodeFields usize_numeral)

/-- The width-24 group at `i` fits the buffer. -/
abbrev GroupFits24 (b : ByteArray) (i : USize) : Prop := Fits b i 191

theorem storeBounds24 {b : ByteArray} {i : USize} (h : GroupFits24 b i) (k : USize)
    (hk : k.toNat ≤ 184) : ((i + k) * 4).toNat + 4 * 8 ≤ b.size ∧
      ((i + k) * 4).toNat + 4 * 8 < USize.size := by
  rw [wordOffset_toNat _ _ (by omega)]
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A width-24 partial round with constant `c` and internal diagonal `d`. -/
@[noinline] def partial24 (c : UInt32) (d : @& ByteArray) (b : ByteArray) (i : USize)
    (hb : GroupFits24 b i) (hd : Fits d 0 23) : { x : ByteArray // x.size = b.size } :=
  p2_partial% 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The constant additions and S-boxes of a width-24 full round. -/
@[noinline] def sbox24 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize)
    (hb : GroupFits24 b i) (hr : Fits rc r 23) : { x : ByteArray // x.size = b.size } :=
  p2_sbox% 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- `mat4` on every block of four coordinates of a width-24 group, words below `2 p`. -/
@[noinline] def mat4x24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mat4% 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The block-sum mixing of the width-24 external matrix. -/
@[noinline] def mix24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) :
    { x : ByteArray // x.size = b.size } :=
  p2_mix% 24 8

/-- The width-24 group at `i` fits buffers of `n` bytes. -/
abbrev Room24 (n : Nat) (i : USize) : Prop := 4 * (i.toNat + 191) + 3 < n ∧ n < USize.size

theorem Room24.fits {n : Nat} {i : USize} (h : Room24 n i) (b : Buf n) : GroupFits24 b.1 i := by
  unfold GroupFits24 Fits
  rw [b.2]
  exact h

/-- The width-24 external matrix, as two passes. -/
@[inline] def external24 {n : Nat} (b : Buf n) (i : USize) (h : Room24 n i) : Buf n :=
  let b := b.of (mat4x24 b.1 i (h.fits b))
  b.of (mix24 b.1 i (h.fits b))

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

/-- Width-24 full rounds `k, …, 3` with the constant rows of `rc`, by recursion so the loop
allocates nothing. -/
def fullRounds24Go {n : Nat} (rc : @& ByteArray) (hr : Rows24 rc) (i : USize) (h : Room24 n i)
    (k : USize) (b : Buf n) : Buf n :=
  if hk : k < 4 then
    let b := b.of (sbox24 rc (24 * k) b.1 i (h.fits b) (hr.fits k hk))
    fullRounds24Go rc hr i h (k + 1) (external24 b i h)
  else b
termination_by 4 - k.toNat
decreasing_by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A width-24 instance as packed Montgomery words. -/
structure Packed24 where
  initial : ByteArray
  internal : Array UInt32
  terminal : ByteArray
  diagonal : ByteArray

/-- Pack the constants of a width-24 instance over the Montgomery field. -/
def Packed24.ofParams (P : Params KoalaBear.Fast.Field 24) : Packed24 where
  initial := encodeFields (P.initial.foldl (fun acc c ↦ acc ++ c.toArray) #[])
  internal := (P.internal.map Subtype.val).toArray
  terminal := encodeFields (P.terminal.foldl (fun acc c ↦ acc ++ c.toArray) #[])
  diagonal := encodeFields P.diagonal.toArray

/-- The width-24 partial rounds with the constants `k, …` of `K`. -/
def partialRounds24Go {n : Nat} (K : @& Packed24) (hd : Fits K.diagonal 0 23) (i : USize)
    (h : Room24 n i) (k : Nat) (b : Buf n) : Buf n :=
  if hk : k < K.internal.size then
    partialRounds24Go K hd i h (k + 1)
      (b.of (partial24 K.internal[k] K.diagonal b.1 i (h.fits b) hd))
  else b
termination_by K.internal.size - k

/-- The constants of `K` fit their buffers. -/
abbrev Packed24.Fits (K : Packed24) : Prop :=
  Rows24 K.initial ∧ Rows24 K.terminal ∧ Poseidon2.Packed.Fits K.diagonal 0 23

/-- The width-24 permutation of the eight states at `i`. -/
def permute24 (K : @& Packed24) (b : ByteArray) (i : USize) : ByteArray :=
  if h : GroupFits24 b i ∧ K.Fits then
    let s : Buf b.size := ⟨b, rfl⟩
    let s := external24 s i h.1
    let s := fullRounds24Go K.initial h.2.1 i h.1 0 s
    let s := partialRounds24Go K h.2.2.2 i h.1 0 s
    (fullRounds24Go K.terminal h.2.2.1 i h.1 0 s).1
  else b

end CompStark.Poseidon2.Packed
