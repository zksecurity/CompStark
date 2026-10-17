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
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset putWords size_putWords wordOffset_toNat
  encodeFields)

/-- Words `i, …, i + n` of `b` fit, and `b` fits machine indices. -/
abbrev Fits (b : ByteArray) (i : USize) (n : Nat) : Prop :=
  4 * (i.toNat + n) + 3 < b.size ∧ b.size < USize.size

/-- The group at `i` fits the buffer. -/
abbrev GroupFits (b : ByteArray) (i : USize) : Prop := Fits b i 127

theorem inBounds {b : ByteArray} {i : USize} {n : Nat} (h : Fits b i n) (k : USize)
    (hk : k.toNat ≤ n) : 4 * (i.toNat + k.toNat) + 3 < b.size ∧ b.size < USize.size :=
  ⟨by omega, h.2⟩

theorem storeBounds {b : ByteArray} {i : USize} (h : GroupFits b i) (k : USize)
    (hk : k.toNat ≤ 120) : ((i + k) * 4).toNat + 4 * 8 ≤ b.size ∧
      ((i + k) * 4).toNat + 4 * 8 < USize.size := by
  rw [wordOffset_toNat _ _ (by omega)]
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The initial external matrix on the eight states at `i`. -/
@[noinline] def linear16 (b : ByteArray) (i : USize) (hb : GroupFits b i) : ByteArray :=
  p2_linear% 16 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A full round with constants `r, …, r + 15` of `rc` on the eight states at `i`. -/
@[noinline] def full16 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize)
    (hb : GroupFits b i) (hr : Fits rc r 15) : ByteArray :=
  p2_full% 16 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A partial round with constant `c` and internal diagonal `d` on the eight states at `i`. -/
@[noinline] def partial16 (c : UInt32) (d : @& ByteArray) (b : ByteArray) (i : USize)
    (hb : GroupFits b i) (hd : Fits d 0 15) : ByteArray :=
  p2_partial% 16 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The constant additions and S-boxes of a full round on the eight states at `i`. -/
@[noinline] def sbox16 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize)
    (hb : GroupFits b i) (hr : Fits rc r 15) : ByteArray :=
  p2_sbox% 16 8

set_option maxRecDepth 16384 in
/-- `mat4` on every block of four coordinates of the eight states at `i`. -/
@[noinline] def mat4x16 (b : ByteArray) (i : USize) (hb : GroupFits b i) : ByteArray :=
  p2_mat4% 16 8

set_option maxRecDepth 16384 in
/-- The block-sum mixing of the external matrix on the eight states at `i`. -/
@[noinline] def mix16 (b : ByteArray) (i : USize) (hb : GroupFits b i) : ByteArray :=
  p2_mix% 16 8

/-- The external matrix on the eight states at `i`, as two passes. -/
def external16 (b : ByteArray) (i : USize) : ByteArray :=
  let b := if h : GroupFits b i then mat4x16 b i h else b
  if h : GroupFits b i then mix16 b i h else b

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

/-- Full rounds with the constant rows `0, …, rounds - 1` of `rc`. -/
def fullRounds (rc : @& ByteArray) (rounds : Nat) (b : ByteArray) (i : USize) : ByteArray :=
  (List.range rounds).foldl (fun b r ↦
    if h : GroupFits b i ∧ 4 * (16 * r + 15) + 3 < rc.size ∧ rc.size < USize.size then
      let b := sbox16 rc (USize.ofNatLT (16 * r) (by omega)) b i h.1
        (by simp only [Fits, USize.toNat_ofNatLT]; exact h.2)
      external16 b i
    else b) b

/-- The partial rounds. -/
def partialRounds (K : @& Packed16) (b : ByteArray) (i : USize) : ByteArray :=
  K.internal.foldl (fun b c ↦
    if h : GroupFits b i ∧ Fits K.diagonal 0 15 then
      partial16 c K.diagonal b i h.1 h.2
    else b) b

/-- The permutation of the eight states at `i`. -/
def permute16 (K : @& Packed16) (b : ByteArray) (i : USize) : ByteArray :=
  let b := external16 b i
  let b := fullRounds K.initial 4 b i
  let b := partialRounds K b i
  fullRounds K.terminal 4 b i

end CompStark.Poseidon2.Packed
