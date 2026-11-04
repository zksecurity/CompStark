/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.FoldWords
public import CompStark.Poseidon2.ArithmeticLemmas
public import CompPoly.Fields.Montgomery.Native32WordsCorrectness

/-! # Correctness of the fold's word kernels

On encoded arrays, `halves` gives the halved sums of the pairs and `diffs` their differences times
the base vector (`halves_encode`, `diffs_encode`).
-/

@[expose] public section
namespace CompStark.Fri.FoldWords
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast
open CompPoly.CPolynomial.NTTFast.Packed (add_val sub_val mul_val size_encode_fields splice lit16)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write write16U zeroWords readUOffset)
open Montgomery.Native32 (Mont32Field FastField)
open Montgomery.Native32.Words (Fits tab upto read_encode zeroWords_eq foldl_blocks foldl_tail
  upto_full splice_upto write_upto dite_pure_yield size_upto)
open CompStark.Poseidon2 (halve half halve_val)

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

theorem rd32_encode (a : Array F) (j : USize) (k : Nat) (h : Fits (encode a) j 31) (hk : k ≤ 31) :
    rd32 (encode a) j k h hk = (a.getD (j.toNat + k) 0).val := by
  rw [rd32, CompPoly.CPolynomial.NTTFast.Packed.Native.readUOffset_encode,
    USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]

/-- `half16` splices the halved sums of sixteen pairs. -/
theorem half16_encode (b o : Array F) (j i : USize) (hb) (hi : i.toNat + 16 ≤ o.size)
    (ho : 4 * o.size < USize.size) :
    half16 p (encode b) j i (encode o) hb = encode (splice o i.toNat (lit16 fun t ↦
      (b.getD (j.toNat + 2 * t) 0 + b.getD (j.toNat + 2 * t + 1) 0) * half p)) := by
  unfold half16
  simp only [rd32_encode, add_val, halve_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- `diff16` splices the differences of sixteen pairs times sixteen words. -/
theorem diff16_encode (b c o : Array F) (j k i : USize) (hb hc) (hi : i.toNat + 16 ≤ o.size)
    (ho : 4 * o.size < USize.size) :
    diff16 p (encode b) (encode c) j k i (encode o) hb hc = encode (splice o i.toNat (lit16 fun t ↦
      (b.getD (j.toNat + 2 * t) 0 - b.getD (j.toNat + 2 * t + 1) 0) * c.getD (k.toNat + t) 0)) := by
  unfold diff16
  simp only [rd32_encode, Montgomery.Native32.Words.rd_encode, sub_val, mul_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- The halved sums of pairs `r0, …, r0 + len - 1`. -/
theorem halves_encode (A : Array F) (r0 len : Nat) (hA : 2 * (r0 + len) ≤ A.size)
    (hs : 4 * A.size < USize.size) :
    halves p (encode A) r0 len = encode (tab len fun i ↦
      (A.getD (2 * (r0 + i)) 0 + A.getD (2 * (r0 + i) + 1) 0) * half p) := by
  unfold halves
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, pure_bind, dite_pure_yield, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hn : 4 * len < USize.size := by omega
  have hsA : (encode A).size = 4 * A.size := size_encode_fields A
  let f (i : Nat) : F := (A.getD (2 * (r0 + i)) 0 + A.getD (2 * (r0 + i) + 1) 0) * half p
  rw [zeroWords_eq (p := p), foldl_blocks (Array.replicate len 0) f (len / 16) _ (fun m hm ↦ by
    have h16 : 16 * m + 16 ≤ len := by omega
    have hi16 : (USize.ofNatLT (16 * m) (by omega)).toNat + 16 ≤
        (upto (Array.replicate len (0 : F)) f (16 * m)).size := by
      simp only [USize.toNat_ofNatLT, size_upto, Array.size_replicate]; omega
    have ho16 : 4 * (upto (Array.replicate len (0 : F)) f (16 * m)).size < USize.size := by
      simp only [size_upto, Array.size_replicate]; omega
    rw [dite_eq_left_of_eq_true (eq_true ⟨by omega, by omega⟩),
      half16_encode _ _ _ _ _ hi16 ho16]
    simp only [USize.toNat_ofNatLT]
    refine congrArg encode ((congrArg _ (Montgomery.Native32.Words.lit16_congr _ _
      fun t ht ↦ ?_)).trans (splice_upto _ f _ (by rw [Array.size_replicate]; omega)))
    show _ = f (16 * m + t)
    simp only [f]
    rw [show 2 * (r0 + 16 * m) + 2 * t = 2 * (r0 + (16 * m + t)) by omega]),
    foldl_tail _ f _ _ _ (fun k _ hk ↦ by
      rw [read_encode A _ hs (by omega), read_encode A _ hs (by omega), add_val, halve_val]
      exact write_upto _ f k (by rw [Array.size_replicate]; omega)
        (by rw [Array.size_replicate]; omega)),
    Nat.add_sub_cancel' (Nat.mul_div_le len 16), upto_full _ f _ (Array.size_replicate ..)]
  rfl

/-- The differences of pairs `r0, …, r0 + len - 1` times the words `r0, …` of `C`. -/
theorem diffs_encode (A C : Array F) (r0 len : Nat) (hA : 2 * (r0 + len) ≤ A.size)
    (hC : r0 + len ≤ C.size) (hs : 4 * A.size < USize.size) (hsC : 4 * C.size < USize.size) :
    diffs p (encode A) (encode C) r0 len = encode (tab len fun i ↦
      (A.getD (2 * (r0 + i)) 0 - A.getD (2 * (r0 + i) + 1) 0) * C.getD (r0 + i) 0) := by
  unfold diffs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, pure_bind, dite_pure_yield, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hn : 4 * len < USize.size := by omega
  have hsA : (encode A).size = 4 * A.size := size_encode_fields A
  have hsC' : (encode C).size = 4 * C.size := size_encode_fields C
  let f (i : Nat) : F := (A.getD (2 * (r0 + i)) 0 - A.getD (2 * (r0 + i) + 1) 0) * C.getD (r0 + i) 0
  rw [zeroWords_eq (p := p), foldl_blocks (Array.replicate len 0) f (len / 16) _ (fun m hm ↦ by
    have h16 : 16 * m + 16 ≤ len := by omega
    have hi16 : (USize.ofNatLT (16 * m) (by omega)).toNat + 16 ≤
        (upto (Array.replicate len (0 : F)) f (16 * m)).size := by
      simp only [USize.toNat_ofNatLT, size_upto, Array.size_replicate]; omega
    have ho16 : 4 * (upto (Array.replicate len (0 : F)) f (16 * m)).size < USize.size := by
      simp only [size_upto, Array.size_replicate]; omega
    rw [dite_eq_left_of_eq_true (eq_true ⟨by omega, by omega, by omega, by omega⟩),
      diff16_encode _ _ _ _ _ _ _ _ hi16 ho16]
    simp only [USize.toNat_ofNatLT]
    refine congrArg encode ((congrArg _ (Montgomery.Native32.Words.lit16_congr _ _
      fun t ht ↦ ?_)).trans (splice_upto _ f _ (by rw [Array.size_replicate]; omega)))
    show _ = f (16 * m + t)
    simp only [f]
    rw [show 2 * (r0 + 16 * m) + 2 * t = 2 * (r0 + (16 * m + t)) by omega,
      show r0 + 16 * m + t = r0 + (16 * m + t) by omega]),
    foldl_tail _ f _ _ _ (fun k _ hk ↦ by
      rw [read_encode A _ hs (by omega), read_encode A _ hs (by omega),
        read_encode C _ hsC (by omega), sub_val, mul_val]
      exact write_upto _ f k (by rw [Array.size_replicate]; omega)
        (by rw [Array.size_replicate]; omega)),
    Nat.add_sub_cancel' (Nat.mul_div_le len 16), upto_full _ f _ (Array.size_replicate ..)]
  rfl

end CompStark.Fri.FoldWords
