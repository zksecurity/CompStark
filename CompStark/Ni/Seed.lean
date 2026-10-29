/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Verifier
public import Mathlib.Data.Nat.Digits.Defs

/-! # The STARK's domain separator fixes the trace length

The challenger observes the STARK's domain separator (`starkSeedOf`) first, the trace's log length
among its numbers. Its length does not depend on the trace length (`length_starkSeedOf`): the
interaction pattern is the same, and the instance label has one number per field. It tells the
trace lengths apart (`starkSeedOf_inj`) when the challenger reads its bytes in chunks of at
least one byte, `p ≥ 2 ^ 8`, and the lengths fit the label's eight bytes, below `2 ^ 64`: the
chunks' values are below `p`, so they are the chunks' little-endian numbers, which give the bytes
back, and the label's first number is the trace's log length in eight big-endian bytes.
-/

@[expose] public section
namespace CompStark.DomainSeparator

/-! ### Lengths -/

theorem length_bigEndian (k n : Nat) : (bigEndian k n).length = k := by
  simp only [bigEndian, List.length_map, List.length_reverse, List.length_range]

theorem length_chunks_go (k : Nat) :
    ∀ (fuel : Nat) (bs bs' : List UInt8), bs.length = bs'.length →
      (chunks.go k fuel bs).length = (chunks.go k fuel bs').length
  | 0, _, _, _ => by simp only [chunks.go]
  | _ + 1, [], [], _ => rfl
  | _ + 1, [], _ :: _, h => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | _ + 1, _ :: _, [], h => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | fuel + 1, b :: bs, b' :: bs', h => by
    simp only [chunks.go, List.length_cons]
    exact congrArg (· + 1) (length_chunks_go k fuel _ _ (by
      simp only [List.length_drop, List.length_cons] at h ⊢; omega))

theorem length_toElems (F : Type) [BaseField F] {bs bs' : List UInt8}
    (h : bs.length = bs'.length) : (toElems F bs).length = (toElems F bs').length := by
  simp only [toElems, List.length_cons, List.length_map, chunks, h]
  exact congrArg (· + 1) (length_chunks_go _ _ _ _ h)

theorem length_label (inst : List Nat) :
    (inst.flatMap fun n ↦ bigEndian 4 8 ++ bigEndian 8 n).length = 12 * inst.length := by
  induction inst with
  | nil => rfl
  | cons n inst ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_append, length_bigEndian,
      length_bigEndian, List.length_cons]
    ring

theorem length_seedBytes (version : Nat) (name : String) (steps : List Step) {inst inst' : List Nat}
    (h : inst.length = inst'.length) :
    (seedBytes version name steps inst).length = (seedBytes version name steps inst').length := by
  simp only [seedBytes, List.length_append, length_label, h, length_bigEndian]

variable {F : Type} [BaseField F] (EF : Type) [Challenge F EF]

/-- The STARK's domain separator has one length at every trace length. -/
theorem length_starkSeedOf (P : Fri.Params) (A : Stark.Air F) (n m : Nat) :
    (Stark.starkSeedOf EF P A n).length = (Stark.starkSeedOf EF P A m).length := by
  unfold Stark.starkSeedOf starkSeed
  exact length_toElems F (length_seedBytes _ _ _ rfl)

/-! ### Decoding -/

/-- The little-endian number of bytes, as `toElems` reads a chunk, is `Nat.ofDigits 256`. -/
theorem foldl_zipIdx_eq (c : List UInt8) (s acc : Nat) :
    (c.zipIdx s).foldl (fun acc (b, i) ↦ acc + b.toNat * 256 ^ i) acc =
      acc + 256 ^ s * Nat.ofDigits 256 (c.map UInt8.toNat) := by
  induction c generalizing s acc with
  | nil => simp only [List.zipIdx_nil, List.foldl_nil, List.map_nil, Nat.ofDigits_nil,
      Nat.mul_zero, Nat.add_zero]
  | cons b c ih =>
    rw [List.zipIdx_cons, List.foldl_cons, ih, List.map_cons, Nat.ofDigits_cons]
    push_cast
    ring

theorem ofDigits_inj {b : Nat} :
    ∀ (L L' : List Nat), L.length = L'.length → (∀ x ∈ L, x < b) → (∀ x ∈ L', x < b) →
      Nat.ofDigits b L = Nat.ofDigits b L' → L = L'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | _ :: _, [], h, _, _, _ => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | a :: L, a' :: L', h, w, w', he => by
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons] at he
    have ha := w a List.mem_cons_self
    have ha' := w' a' List.mem_cons_self
    have h1 : a = a' := by
      have := congrArg (· % b) he
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
      exact this
    subst h1
    have hpos : 0 < b := by omega
    have h2 : Nat.ofDigits b L = Nat.ofDigits b L' :=
      Nat.eq_of_mul_eq_mul_left hpos (by omega)
    rw [ofDigits_inj L L' (by simp only [List.length_cons] at h; omega)
      (fun x hx ↦ w x (List.mem_cons_of_mem _ hx)) (fun x hx ↦ w' x (List.mem_cons_of_mem _ hx)) h2]

theorem map_toNat_inj {c c' : List UInt8} (h : c.map UInt8.toNat = c'.map UInt8.toNat) :
    c = c' :=
  List.map_injective_iff.mpr (fun _ _ h ↦ UInt8.toNat_inj.mp h) h

/-- Chunks of at most `k ≥ 1` bytes give the bytes back. -/
theorem flatten_chunks_go (k : Nat) (hk : 1 ≤ k) :
    ∀ (fuel : Nat) (bs : List UInt8), bs.length ≤ fuel → (chunks.go k fuel bs).flatten = bs
  | 0, bs, h => by simp only [chunks.go, List.flatten_nil]; exact (List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp h)).symm
  | _ + 1, [], _ => rfl
  | fuel + 1, b :: bs, h => by
    have hlen : (List.drop k (b :: bs)).length ≤ fuel := by
      simp only [List.length_drop, List.length_cons] at h ⊢; omega
    simp only [chunks.go, List.flatten_cons]
    rw [flatten_chunks_go k hk fuel _ hlen, List.take_append_drop]

theorem chunks_go_mem_length (k : Nat) :
    ∀ (fuel : Nat) (bs : List UInt8), ∀ c ∈ chunks.go k fuel bs, c.length ≤ k
  | 0, _, c, hc => by simp only [chunks.go, List.not_mem_nil] at hc
  | _ + 1, [], c, hc => by simp only [chunks.go, List.not_mem_nil] at hc
  | fuel + 1, b :: bs, c, hc => by
    simp only [chunks.go, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact List.length_take_le _ _
    · exact chunks_go_mem_length k fuel _ c hc

theorem natCast_inj {a b : Nat} (ha : a < Nat.card F) (hb : b < Nat.card F)
    (h : (a : F) = (b : F)) : a = b := by
  have hc : CharP F (Nat.card F) := BaseField.ringChar_eq_card (F := F) ▸ ringChar.charP F
  have := (CharP.natCast_eq_natCast F (Nat.card F)).mp h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- The value of a chunk of at most `k` bytes. -/
abbrev chunkValue (c : List UInt8) : Nat :=
  c.zipIdx.foldl (fun acc (b, i) ↦ acc + b.toNat * 256 ^ i) 0

theorem chunkValue_eq (c : List UInt8) : chunkValue c = Nat.ofDigits 256 (c.map UInt8.toNat) := by
  rw [chunkValue, foldl_zipIdx_eq, Nat.zero_add, Nat.pow_zero, Nat.one_mul]

theorem chunkValue_lt (c : List UInt8) : chunkValue c < 256 ^ c.length := by
  rw [chunkValue_eq, ← List.length_map (f := UInt8.toNat)]
  exact Nat.ofDigits_lt_base_pow_length (by norm_num) fun x hx ↦ by
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact y.toNat_lt

theorem chunks_go_inj (k : Nat) (hkp : 256 ^ k ≤ Nat.card F) :
    ∀ (fuel : Nat) (bs bs' : List UInt8), bs.length = bs'.length →
      (chunks.go k fuel bs).map (fun c ↦ ((chunkValue c : Nat) : F)) =
        (chunks.go k fuel bs').map (fun c ↦ ((chunkValue c : Nat) : F)) →
      chunks.go k fuel bs = chunks.go k fuel bs'
  | 0, _, _, _, _ => by simp only [chunks.go]
  | _ + 1, [], [], _, _ => rfl
  | _ + 1, [], _ :: _, h, _ => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | _ + 1, _ :: _, [], h, _ => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | fuel + 1, b :: bs, b' :: bs', h, he => by
    simp only [chunks.go, List.map_cons, List.cons.injEq] at he ⊢
    have hlen : ((b :: bs).take k).length = ((b' :: bs').take k).length := by
      simp only [List.length_take, h]
    have hlt (c : List UInt8) (hc : c.length ≤ k) : chunkValue c < Nat.card F :=
      lt_of_lt_of_le (chunkValue_lt c) ((Nat.pow_le_pow_right (by norm_num) hc).trans hkp)
    have hv := natCast_inj (hlt _ (List.length_take_le _ _)) (hlt _ (List.length_take_le _ _))
      he.1
    rw [chunkValue_eq, chunkValue_eq] at hv
    refine ⟨map_toNat_inj (ofDigits_inj _ _ (by simp only [List.length_map, hlen])
      (fun x hx ↦ ?_) (fun x hx ↦ ?_) hv), chunks_go_inj k hkp fuel _ _ (by
        simp only [List.length_drop, List.length_cons] at h ⊢; omega) he.2⟩
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact y.toNat_lt
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact y.toNat_lt

/-- On fields of at least `2 ^ 8` elements, the elements the challenger observes for bytes of one
length give the bytes back. -/
theorem toElems_inj (h8 : 2 ^ 8 ≤ Nat.card F) {bs bs' : List UInt8}
    (hlen : bs.length = bs'.length) (h : toElems F bs = toElems F bs') : bs = bs' := by
  set k := Nat.log2 (CompPoly.CanonicalNat.bound F) / 8 with hk
  have hcard : CompPoly.CanonicalNat.bound F = Nat.card F := by
    rw [← CompPoly.CanonicalNat.card_eq, Nat.card_eq_fintype_card]
  have hk1 : 1 ≤ k := by
    rw [hk, hcard]
    have : 8 ≤ Nat.log2 (Nat.card F) := by
      rw [Nat.le_log2 (by omega)]; exact h8
    omega
  have hkp : 256 ^ k ≤ Nat.card F := by
    have hpos : Nat.card F ≠ 0 := by omega
    calc 256 ^ k = 2 ^ (8 * k) := by rw [Nat.pow_mul]
      _ ≤ 2 ^ Nat.log2 (Nat.card F) := Nat.pow_le_pow_right (by norm_num) (by rw [hk, hcard]; omega)
      _ ≤ Nat.card F := Nat.log2_self_le hpos
  simp only [toElems, ← hk, List.cons.injEq] at h
  have hc := chunks_go_inj k hkp bs.length bs bs' hlen (by
    simp only [chunks, chunkValue] at h ⊢
    rw [← hlen] at h
    exact h.2)
  rw [← flatten_chunks_go k hk1 bs.length bs le_rfl,
    ← flatten_chunks_go k hk1 bs.length bs' (hlen ▸ le_rfl), hc]

/-- The big-endian bytes of a number below `256 ^ k` give the number back. -/
theorem bigEndian_inj (k : Nat) {n m : Nat} (hn : n < 256 ^ k) (hm : m < 256 ^ k)
    (h : bigEndian k n = bigEndian k m) : n = m := by
  have hdig : ∀ i < k, n / 256 ^ i % 256 = m / 256 ^ i % 256 := by
    intro i hi
    have h' := congrArg (fun l ↦ (l.reverse.getD i 0).toNat) h
    simp only [bigEndian, List.map_reverse, List.reverse_reverse, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
      Nat.toUInt8_eq, UInt8.toNat_ofNat'] at h'
    exact h'
  have key : ∀ j ≤ k, n % 256 ^ j = m % 256 ^ j := by
    intro j hj
    induction j with
    | zero => simp only [Nat.pow_zero, Nat.mod_one]
    | succ j ih =>
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (by omega), hdig j (by omega)]
  rw [← Nat.mod_eq_of_lt hn, ← Nat.mod_eq_of_lt hm, key k le_rfl]

/-- **The domain separator fixes the trace length.** On fields of at least `2 ^ 8` elements, two
trace lengths below `2 ^ 64` with one STARK domain separator are equal. -/
theorem starkSeedOf_inj (h8 : 2 ^ 8 ≤ Nat.card F) (P : Fri.Params) (A : Stark.Air F) {n m : Nat}
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (h : Stark.starkSeedOf EF P A n = Stark.starkSeedOf EF P A m) : n = m := by
  unfold Stark.starkSeedOf starkSeed at h
  have hb := toElems_inj h8
    (length_seedBytes _ _ _ (by simp only [List.length_cons, List.length_nil])) h
  simp only [seedBytes, List.append_assoc, List.append_cancel_left_eq, length_label,
    List.length_cons, List.length_nil] at hb
  have hl := List.append_cancel_right hb
  simp only [List.flatMap_cons, List.append_assoc, List.append_cancel_left_eq] at hl
  have h12 := congrArg (List.take 8) hl
  rw [List.take_left' (length_bigEndian 8 n), List.take_left' (length_bigEndian 8 m)] at h12
  exact bigEndian_inj 8 (by norm_num at hn ⊢; omega) (by norm_num at hm ⊢; omega) h12

end CompStark.DomainSeparator
