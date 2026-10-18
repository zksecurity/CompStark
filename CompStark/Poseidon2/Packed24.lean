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
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset putWords size_putWords wordOffset_toNat
  encodeFields)

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
    (hb : GroupFits24 b i) (hd : Fits d 0 23) : ByteArray :=
  p2_partial% 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The constant additions and S-boxes of a width-24 full round. -/
@[noinline] def sbox24 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize)
    (hb : GroupFits24 b i) (hr : Fits rc r 23) : ByteArray :=
  p2_sbox% 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- `mat4` on every block of four coordinates of a width-24 group. -/
@[noinline] def mat4x24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) : ByteArray :=
  p2_mat4% 24 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The block-sum mixing of the width-24 external matrix. -/
@[noinline] def mix24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) : ByteArray :=
  p2_mix% 24 8

/-- The width-24 external matrix, as two passes. -/
def external24 (b : ByteArray) (i : USize) : ByteArray :=
  let b := if h : GroupFits24 b i then mat4x24 b i h else b
  if h : GroupFits24 b i then mix24 b i h else b

/-- Width-24 full rounds `r, …, r + n - 1` of `rc`, by recursion so the loop allocates nothing. -/
def fullRounds24Go (rc : @& ByteArray) (i : USize) : Nat → Nat → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, r, b =>
    fullRounds24Go rc i n (r + 1)
      (if h : GroupFits24 b i ∧ 4 * (24 * r + 23) + 3 < rc.size ∧ rc.size < USize.size then
        let b := sbox24 rc (USize.ofNatLT (24 * r) (by omega)) b i h.1
          (by simp only [Fits, USize.toNat_ofNatLT]; exact h.2)
        external24 b i
      else b)

/-- Width-24 full rounds with the constant rows `0, …, rounds - 1` of `rc`. -/
def fullRounds24 (rc : @& ByteArray) (rounds : Nat) (b : ByteArray) (i : USize) : ByteArray :=
  fullRounds24Go rc i rounds 0 b

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

/-- The width-24 partial rounds. -/
def partialRounds24 (K : @& Packed24) (b : ByteArray) (i : USize) : ByteArray :=
  K.internal.foldl (fun b c ↦
    if h : GroupFits24 b i ∧ Fits K.diagonal 0 23 then
      partial24 c K.diagonal b i h.1 h.2
    else b) b

/-- The width-24 permutation of the eight states at `i`. -/
def permute24 (K : @& Packed24) (b : ByteArray) (i : USize) : ByteArray :=
  let b := external24 b i
  let b := fullRounds24 K.initial 4 b i
  let b := partialRounds24 K b i
  fullRounds24 K.terminal 4 b i

end CompStark.Poseidon2.Packed
