/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.PackedLanes

/-! # Packed Poseidon2 over a Montgomery field

`PackedKernels p` gives the round kernels of Poseidon2 over `FastField p` on groups of eight
states of widths 16 and 24, each with the model of `PackedLanes` it computes. A field instantiates
the kernels that `Unrolled` generates for its shape (modulus, S-box degree, internal diagonals).
`permute16` and `permute24` run Plonky3's round structure on them: the external matrix, four full
rounds, the partial rounds and four full rounds, each full round part one call on the whole group
and the partial rounds one loop.
-/

@[expose] public section
namespace CompStark.Poseidon2.Packed
open Montgomery.Native32 (Mont32Field FastField)
open Montgomery.Native32.Words (Fits)
open CompPoly.PackedRepr (encode)

/-- The partial rounds with the constants `k, …` of `C`, each by the kernel `f`. A field's loop
(`PackedKernels.partials16`) is this loop on its kernel, compiled with the kernel inlined, so a
round makes no call. -/
@[specialize] def partialsLoop16
    (f : UInt32 → (b : ByteArray) → (i : USize) → GroupFits b i →
      { x : ByteArray // x.size = b.size })
    {n : Nat} (C : @& Packed16) (i : USize) (h : Room16 n i) (k : Nat) (b : Buf n) : Buf n :=
  if hk : k < C.internal.size then
    partialsLoop16 f C i h (k + 1) (b.of (f C.internal[k] b.1 i (h.fits b)))
  else b
termination_by C.internal.size - k

/-- The width-24 partial rounds with the constants `k, …` of `C`, each by the kernel `f`. -/
@[specialize] def partialsLoop24
    (f : UInt32 → (b : ByteArray) → (i : USize) → GroupFits24 b i →
      { x : ByteArray // x.size = b.size })
    {n : Nat} (C : @& Packed24) (i : USize) (h : Room24 n i) (k : Nat) (b : Buf n) : Buf n :=
  if hk : k < C.internal.size then
    partialsLoop24 f C i h (k + 1) (b.of (f C.internal[k] b.1 i (h.fits b)))
  else b
termination_by C.internal.size - k

/-- The packed round kernels of Poseidon2 over `FastField p` at widths 16 and 24, with their
models: the S-boxes of a full round (left below `2 p` by `lazyPow`), `mat4` on every block of four
and the block-sum mixing of the external matrix, and the partial round, whose lanes are the
specification's partial rounds for the field's S-box degree and internal diagonals. -/
class PackedKernels (p : ℕ) [Mont32Field p] where
  /-- The S-box degree. -/
  degree : Nat
  /-- The diagonal of the width-16 internal matrix. -/
  diagonal16 : Vector (FastField p) 16
  /-- The diagonal of the width-24 internal matrix. -/
  diagonal24 : Vector (FastField p) 24
  /-- The S-box of a full round on a canonical word, below `2 p`. -/
  lazyPow : UInt32 → UInt32
  lazyPow_lt (a : FastField p) : (lazyPow a.val).toNat < 2 * p
  reduceOnce_lazyPow (a : FastField p) :
    CompPoly.CPolynomial.NTTFast.Packed.reduceOnce p (lazyPow a.val) = (a ^ degree).val
  sbox16 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize) (hb : GroupFits b i)
    (hr : Fits rc r 15) : { x : ByteArray // x.size = b.size }
  mat4x16 (b : ByteArray) (i : USize) (hb : GroupFits b i) : { x : ByteArray // x.size = b.size }
  mix16 (b : ByteArray) (i : USize) (hb : GroupFits b i) : { x : ByteArray // x.size = b.size }
  partial16 (c : UInt32) (b : ByteArray) (i : USize) (hb : GroupFits b i) :
    { x : ByteArray // x.size = b.size }
  /-- The partial rounds of `C`: `partialsLoop16` on `partial16`. -/
  partials16 {n : Nat} (C : @& Packed16) (i : USize) (h : Room16 n i) (b : Buf n) : Buf n
  partials16_eq {n : Nat} (C : Packed16) (i : USize) (h : Room16 n i) (b : Buf n) :
    partials16 C i h b = partialsLoop16 partial16 C i h 0 b
  sbox24 (rc : @& ByteArray) (r : USize) (b : ByteArray) (i : USize) (hb : GroupFits24 b i)
    (hr : Fits rc r 23) : { x : ByteArray // x.size = b.size }
  mat4x24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) :
    { x : ByteArray // x.size = b.size }
  mix24 (b : ByteArray) (i : USize) (hb : GroupFits24 b i) : { x : ByteArray // x.size = b.size }
  partial24 (c : UInt32) (b : ByteArray) (i : USize) (hb : GroupFits24 b i) :
    { x : ByteArray // x.size = b.size }
  /-- The width-24 partial rounds of `C`: `partialsLoop24` on `partial24`. -/
  partials24 {n : Nat} (C : @& Packed24) (i : USize) (h : Room24 n i) (b : Buf n) : Buf n
  partials24_eq {n : Nat} (C : Packed24) (i : USize) (h : Room24 n i) (b : Buf n) :
    partials24 C i h b = partialsLoop24 partial24 C i h 0 b
  sbox16_encode (rc W : Array (FastField p)) (r i : USize) (hb) (hr) :
    (sbox16 (encode rc) r (encode W) i hb hr).1 =
      encode (sboxWords lazyPow coords16 rc W r.toNat i.toNat)
  mat4x16_encodeWords (U : Array UInt32) (i : USize) (hb)
    (hU : ∀ k, (U.getD k 0).toNat < 2 * p) :
    (mat4x16 (encode U) i hb).1 = encode (mat4Words p coords16 U i.toNat)
  mix16_encode (W : Array (FastField p)) (i : USize) (hb) :
    (mix16 (encode W) i hb).1 = encode (mixModel coords16 [4, 8, 12] W i.toNat)
  partial16_spec (P : Params (FastField p) 16) (hd : P.degree = degree)
    (hD : P.diagonal = diagonal16) (c : FastField p) (W : Array (FastField p)) (i : USize) (hb)
    (hW : i.toNat + 8 * 16 ≤ W.size) :
    ∃ W', (partial16 c.val (encode W) i hb).1 = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane 16 W' i.toNat l = partialRound P (lane 16 W i.toNat l) c) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 16 ≤ k) → W'.getD k 0 = W.getD k 0
  sbox24_encode (rc W : Array (FastField p)) (r i : USize) (hb) (hr) :
    (sbox24 (encode rc) r (encode W) i hb hr).1 =
      encode (sboxWords lazyPow coords24 rc W r.toNat i.toNat)
  mat4x24_encodeWords (U : Array UInt32) (i : USize) (hb)
    (hU : ∀ k, (U.getD k 0).toNat < 2 * p) :
    (mat4x24 (encode U) i hb).1 = encode (mat4Words p coords24 U i.toNat)
  mix24_encode (W : Array (FastField p)) (i : USize) (hb) :
    (mix24 (encode W) i hb).1 = encode (mixModel coords24 [4, 8, 12, 16, 20] W i.toNat)
  partial24_spec (P : Params (FastField p) 24) (hd : P.degree = degree)
    (hD : P.diagonal = diagonal24) (c : FastField p) (W : Array (FastField p)) (i : USize) (hb)
    (hW : i.toNat + 8 * 24 ≤ W.size) :
    ∃ W', (partial24 c.val (encode W) i hb).1 = encode W' ∧ W'.size = W.size ∧
      (∀ l < 8, lane 24 W' i.toNat l = partialRound P (lane 24 W i.toNat l) c) ∧
      ∀ k, (k < i.toNat ∨ i.toNat + 8 * 24 ≤ k) → W'.getD k 0 = W.getD k 0

variable (p : ℕ) [Mont32Field p] [K : PackedKernels p]

/-! ### Width 16 -/

/-- The external matrix on the eight states at `i`, as two passes. -/
@[inline] def external16 {n : Nat} (b : Buf n) (i : USize) (h : Room16 n i) : Buf n :=
  let b := b.of (K.mat4x16 b.1 i (h.fits b))
  b.of (K.mix16 b.1 i (h.fits b))

/-- Full rounds `k, …, 3` with the constant rows of `rc`, by recursion so the loop allocates
nothing. -/
@[specialize] def fullRoundsGo {n : Nat} (rc : @& ByteArray) (hr : Rows16 rc) (i : USize)
    (h : Room16 n i) (k : USize) (b : Buf n) : Buf n :=
  if hk : k < 4 then
    let b := b.of (K.sbox16 rc (16 * k) b.1 i (h.fits b) (hr.fits k hk))
    fullRoundsGo rc hr i h (k + 1) (external16 p b i h)
  else b
termination_by 4 - k.toNat
decreasing_by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The width-16 permutation of the eight states at `i`. -/
@[specialize] def permute16 (C : @& Packed16) (b : ByteArray) (i : USize) : ByteArray :=
  if h : GroupFits b i ∧ C.Fits then
    let s : Buf b.size := ⟨b, rfl⟩
    let s := external16 p s i h.1
    let s := fullRoundsGo p C.initial h.2.1 i h.1 0 s
    let s := K.partials16 C i h.1 s
    (fullRoundsGo p C.terminal h.2.2 i h.1 0 s).1
  else b

/-! ### Width 24 -/

/-- The width-24 external matrix, as two passes. -/
@[inline] def external24 {n : Nat} (b : Buf n) (i : USize) (h : Room24 n i) : Buf n :=
  let b := b.of (K.mat4x24 b.1 i (h.fits b))
  b.of (K.mix24 b.1 i (h.fits b))

/-- Width-24 full rounds `k, …, 3` with the constant rows of `rc`, by recursion so the loop
allocates nothing. -/
@[specialize] def fullRounds24Go {n : Nat} (rc : @& ByteArray) (hr : Rows24 rc) (i : USize)
    (h : Room24 n i) (k : USize) (b : Buf n) : Buf n :=
  if hk : k < 4 then
    let b := b.of (K.sbox24 rc (24 * k) b.1 i (h.fits b) (hr.fits k hk))
    fullRounds24Go rc hr i h (k + 1) (external24 p b i h)
  else b
termination_by 4 - k.toNat
decreasing_by
  have hk' := lt_four_toNat hk
  have := USize.le_size
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The width-24 permutation of the eight states at `i`. -/
@[specialize] def permute24 (C : @& Packed24) (b : ByteArray) (i : USize) : ByteArray :=
  if h : GroupFits24 b i ∧ C.Fits then
    let s : Buf b.size := ⟨b, rfl⟩
    let s := external24 p s i h.1
    let s := fullRounds24Go p C.initial h.2.1 i h.1 0 s
    let s := K.partials24 C i h.1 s
    (fullRounds24Go p C.terminal h.2.2 i h.1 0 s).1
  else b

end CompStark.Poseidon2.Packed
