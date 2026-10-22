/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ExtWords
public import CompStark.Stark.Fast.Rel
public import CompPoly.Univariate.NTTFast.Packed.FieldStorage
public import CompPoly.Univariate.NTTFast.Packed.Rows
public import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas

/-! # The word kernels on encoded arrays

The word kernels of `CompStark.Stark.Words` and the plane operations of `EVec` on encoded field
arrays compute the field operations entrywise, under the sizes they index. Loops overwrite a
prefix of their output (`upto`), sixteen words or one word at a time. Batch inversion gives the
true inverses when no element is zero, and parallel pieces concatenate their ranges.
-/

@[expose] public section
namespace CompStark.Words
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul add_val sub_val mul_val ofWord_val
  size_encode_fields splice getD_splice size_splice lit16 getD_lit16 size_lit16
  array_eq_of_getD getD_ofFn_bounded getD_setIfInBounds)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write write16U zeroWords readUOffset)
open CompStark.Poseidon2.Packed (Fits)
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

/-! ### Words of encoded arrays -/

/-- The word of `0` is `0`. -/
theorem zero_val : (0 : F).val = 0 := rfl

/-- `n` zero words encode `n` zeros. -/
theorem zeroWords_eq (n : Nat) : zeroWords n = encode (Array.replicate n (0 : F)) := by
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords_eq,
    CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val, Array.map_replicate]
  rfl

/-- A word of an encoded array is its element. -/
theorem read_encode (a : Array F) (i : Nat) (hs : 4 * a.size < USize.size) (hi : i < a.size) : read
    (encode a) i = (a.getD i 0).val :=
  CompPoly.CPolynomial.NTTFast.Packed.Native.read_encode a i
    (by rw [size_encode_fields]; exact hs) hi

/-- A word read by a sixteen-word kernel is its element. -/
theorem rd_encode (a : Array F) (i : USize) (k : Nat) (h : Fits (encode a) i 15) (hk : k ≤ 15) : rd
    (encode a) i k h hk = (a.getD (i.toNat + k) 0).val := by
  rw [rd, CompPoly.CPolynomial.NTTFast.Packed.Native.readUOffset_encode,
    USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]

/-- Out of range reads default to zero. -/
theorem getD_eq_zero (a : Array F) (i : Nat) (hi : a.size ≤ i) : a.getD i 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi, Option.getD_none]

/-- An entry of a tabulated array. -/
theorem getD_ofFn (n : Nat) (f : Nat → F) (i : Nat) :
    (Array.ofFn (n := n) fun j ↦ f j.val).getD i 0 = if i < n then f i else 0 := by
  split
  · exact getD_ofFn_bounded _ _ (by assumption) _
  · exact getD_eq_zero _ _ (by rw [Array.size_ofFn]; omega)

/-! ### Partly overwritten arrays -/

/-- `o` with its entries below `k` replaced by `f`. -/
def upto (o : Array F) (f : Nat → F) (k : Nat) : Array F :=
  Array.ofFn (n := o.size) fun j ↦ if j.val < k then f j else o.getD j 0

@[simp] theorem size_upto (o : Array F) (f : Nat → F) (k : Nat) : (upto o f k).size = o.size :=
  Array.size_ofFn

/-- An entry of `upto`. -/
theorem getD_upto (o : Array F) (f : Nat → F) (k j : Nat) :
    (upto o f k).getD j 0 = if j < o.size then (if j < k then f j else o.getD j 0) else 0 :=
  getD_ofFn o.size (fun j ↦ if j < k then f j else o.getD j 0) j

/-- Nothing overwritten. -/
theorem upto_zero (o : Array F) (f : Nat → F) : upto o f 0 = o := by
  apply array_eq_of_getD _ _ 0 (size_upto _ _ _)
  intro j
  rw [getD_upto]
  split
  · rfl
  · rfl

/-- Everything overwritten. -/
theorem upto_full (o : Array F) (f : Nat → F) (k : Nat) (hk : o.size = k) :
    upto o f k = Array.ofFn (n := k) fun j ↦ f j.val := by
  subst hk
  apply array_eq_of_getD _ _ 0 (by rw [size_upto, Array.size_ofFn])
  intro j
  rw [getD_upto, getD_ofFn]
  split <;> rfl

/-- Writing entry `k` extends the overwritten prefix. -/
theorem write_upto (o : Array F) (f : Nat → F) (k : Nat) (hk : k < o.size)
    (hs : 4 * o.size < USize.size) :
    write (encode (upto o f k)) k (f k).val = encode (upto o f (k + 1)) := by
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _
    (by rw [size_encode_fields, size_upto]; exact hs) (by rw [size_upto]; exact hk)]
  congr 1
  apply array_eq_of_getD _ _ 0 (by simp only [Array.size_setIfInBounds, size_upto])
  intro j
  rw [getD_setIfInBounds _ _ _ _ _ (by rw [size_upto]; exact hk), getD_upto, getD_upto]
  by_cases hj : j = k
  · subst hj
    simp only [hk, Nat.lt_succ_self, ite_true]
  · simp only [hj, ite_false]
    split
    · by_cases hjk : j < k
      · simp only [hjk, ite_true, show j < k + 1 by omega]
      · simp only [hjk, ite_false, show ¬j < k + 1 by omega]
    · rfl

/-- Splicing sixteen entries at `i` extends the overwritten prefix. -/
theorem splice_upto (o : Array F) (f : Nat → F) (i : Nat) (hi : i + 16 ≤ o.size) :
    splice (upto o f i) i (lit16 fun t ↦ f (i + t)) = upto o f (i + 16) := by
  apply array_eq_of_getD _ _ 0
    (by rw [size_splice _ _ _ (by rw [size_upto, size_lit16]; omega), size_upto, size_upto])
  intro j
  rw [getD_splice _ _ _ (by rw [size_upto, size_lit16]; omega), getD_upto, getD_upto, size_lit16]
  by_cases h1 : j < i
  · simp only [h1, ite_true, show j < i + 16 by omega]
  · by_cases h2 : j < i + 16
    · simp only [h1, h2, ite_false, ite_true, show j < o.size by omega]
      rw [getD_lit16 _ _ (by omega), Nat.add_sub_cancel' (by omega)]
    · simp only [h1, h2, ite_false]

/-! ### Loops -/

/-- A guarded loop step that always continues. -/
theorem dite_pure_yield {β : Type} (c : Prop) [Decidable c] (a : c → β) (b : β) :
    (if h : c then (pure (ForInStep.yield (a h)) : Id (ForInStep β))
      else pure (ForInStep.yield b)) = pure (ForInStep.yield (if h : c then a h else b)) := by
  split <;> rfl

/-- Blocks of sixteen words, each overwriting its block with `f`. -/
theorem foldl_blocks (o : Array F) (f : Nat → F) (M : Nat) (B : ByteArray → Nat → ByteArray)
    (hB : ∀ m < M, B (encode (upto o f (16 * m))) m = encode (upto o f (16 * m + 16))) :
    (List.range M).foldl B (encode o) = encode (upto o f (16 * M)) := by
  induction M with
  | zero => rw [List.range_zero, List.foldl_nil, Nat.mul_zero, upto_zero]
  | succ M ih =>
    rw [List.range_succ, List.foldl_append, ih fun m hm ↦ hB m (by omega), List.foldl_cons,
      List.foldl_nil, hB M (by omega)]
    rfl

/-- Single words, each overwritten with `f`. -/
theorem foldl_tail (o : Array F) (f : Nat → F) (k0 len : Nat) (T : ByteArray → Nat → ByteArray)
    (hT : ∀ k, k0 ≤ k → k < k0 + len → T (encode (upto o f k)) k = encode (upto o f (k + 1))) :
    (List.range' k0 len).foldl T (encode (upto o f k0)) = encode (upto o f (k0 + len)) := by
  induction len generalizing k0 with
  | zero => rfl
  | succ len ih =>
    rw [List.range'_succ, List.foldl_cons, hT k0 (Nat.le_refl _) (by omega),
      ih (k0 + 1) fun k h1 h2 ↦ hT k (by omega) (by omega), Nat.add_right_comm, Nat.add_assoc]

/-! ### Elementwise kernels -/

/-- `zipWords` applies a word operation that refines `g` entrywise, when its sixteen-word
kernel does. -/
theorem zipWords_encode
    (k16 : (a b : ByteArray) → (i : USize) → ByteArray → Fits a i 15 → Fits b i 15 → ByteArray)
    (op : UInt32 → UInt32 → UInt32) (g : F → F → F) (hop : ∀ x y, op x.val y.val = (g x y).val)
    (hk : ∀ (a b o : Array F) (i : USize) ha hb, i.toNat + 16 ≤ o.size →
      4 * o.size < USize.size → k16 (encode a) (encode b) i (encode o) ha hb =
        encode (splice o i.toNat (lit16 fun t ↦
          g (a.getD (i.toNat + t) 0) (b.getD (i.toNat + t) 0))))
    (a b : Array F) (n : Nat) (ha : n ≤ a.size) (hb : n ≤ b.size)
    (hsa : 4 * a.size < USize.size) (hsb : 4 * b.size < USize.size) :
    zipWords k16 op (encode a) (encode b) n =
      encode (Array.ofFn (n := n) fun i ↦ g (a.getD i.val 0) (b.getD i.val 0)) := by
  unfold zipWords
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, pure_bind, dite_pure_yield, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hn : 4 * n < USize.size := by omega
  have hsa' : (encode a).size = 4 * a.size := size_encode_fields a
  have hsb' : (encode b).size = 4 * b.size := size_encode_fields b
  let f (j : Nat) : F := g (a.getD j 0) (b.getD j 0)
  rw [zeroWords_eq (p := p), foldl_blocks (Array.replicate n 0) f (n / 16) _ (fun m hm ↦ by
    have h16 : 16 * m + 16 ≤ n := by omega
    rw [dite_eq_left_of_eq_true (eq_true ⟨by omega, by omega, by omega, by omega⟩),
      hk _ _ _ _ _ _ (by simp only [USize.toNat_ofNatLT, size_upto, Array.size_replicate]; omega)
        (by simp only [size_upto, Array.size_replicate]; omega)]
    simp only [USize.toNat_ofNatLT]
    exact congrArg encode (splice_upto _ f _ (by rw [Array.size_replicate]; omega))),
    foldl_tail _ f _ _ _ (fun k _ hk ↦ by
      rw [read_encode a k hsa (by omega), read_encode b k hsb (by omega), hop]
      exact write_upto _ f k (by rw [Array.size_replicate]; omega)
        (by rw [Array.size_replicate]; omega)),
    Nat.add_sub_cancel' (Nat.mul_div_le n 16), upto_full _ f _ (Array.size_replicate ..)]

/-- `add16` splices sums. -/
theorem add16_encode (a b o : Array F) (i : USize) (ha hb) (hi : i.toNat + 16 ≤ o.size)
    (ho : 4 * o.size < USize.size) :
    add16 p (encode a) (encode b) i (encode o) ha hb = encode (splice o i.toNat
      (lit16 fun t ↦ a.getD (i.toNat + t) 0 + b.getD (i.toNat + t) 0)) := by
  unfold add16
  simp only [rd_encode, add_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- `sub16` splices differences. -/
theorem sub16_encode (a b o : Array F) (i : USize) (ha hb) (hi : i.toNat + 16 ≤ o.size)
    (ho : 4 * o.size < USize.size) :
    sub16 p (encode a) (encode b) i (encode o) ha hb = encode (splice o i.toNat
      (lit16 fun t ↦ a.getD (i.toNat + t) 0 - b.getD (i.toNat + t) 0)) := by
  unfold sub16
  simp only [rd_encode, sub_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- `mul16` splices products. -/
theorem mul16_encode (a b o : Array F) (i : USize) (ha hb) (hi : i.toNat + 16 ≤ o.size)
    (ho : 4 * o.size < USize.size) :
    mul16 p (encode a) (encode b) i (encode o) ha hb = encode (splice o i.toNat
      (lit16 fun t ↦ a.getD (i.toNat + t) 0 * b.getD (i.toNat + t) 0)) := by
  unfold mul16
  simp only [rd_encode, mul_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- `mulAdd16` splices multiply-adds. -/
theorem mulAdd16_encode (a b o : Array F) (c : F) (i : USize) (ha hb)
    (hi : i.toNat + 16 ≤ o.size) (ho : 4 * o.size < USize.size) :
    mulAdd16 p (encode a) (encode b) c.val i (encode o) ha hb = encode (splice o i.toNat
      (lit16 fun t ↦ a.getD (i.toNat + t) 0 + b.getD (i.toNat + t) 0 * c)) := by
  unfold mulAdd16
  simp only [rd_encode, add_val, mul_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- `a + b` on `n` words. -/
theorem addWords_encode (a b : Array F) (n : Nat) (ha : n ≤ a.size) (hb : n ≤ b.size)
    (hsa : 4 * a.size < USize.size) (hsb : 4 * b.size < USize.size) :
    addWords p (encode a) (encode b) n =
      encode (Array.ofFn (n := n) fun i ↦ a.getD i.val 0 + b.getD i.val 0) :=
  zipWords_encode _ _ (· + ·) add_val (fun a b o i ha hb hi ho ↦ add16_encode a b o i ha hb hi ho)
    a b n ha hb hsa hsb

/-- `a - b` on `n` words. -/
theorem subWords_encode (a b : Array F) (n : Nat) (ha : n ≤ a.size) (hb : n ≤ b.size)
    (hsa : 4 * a.size < USize.size) (hsb : 4 * b.size < USize.size) :
    subWords p (encode a) (encode b) n =
      encode (Array.ofFn (n := n) fun i ↦ a.getD i.val 0 - b.getD i.val 0) :=
  zipWords_encode _ _ (· - ·) sub_val (fun a b o i ha hb hi ho ↦ sub16_encode a b o i ha hb hi ho)
    a b n ha hb hsa hsb

/-- `a · b` on `n` words. -/
theorem mulWords_encode (a b : Array F) (n : Nat) (ha : n ≤ a.size) (hb : n ≤ b.size)
    (hsa : 4 * a.size < USize.size) (hsb : 4 * b.size < USize.size) :
    mulWords p (encode a) (encode b) n =
      encode (Array.ofFn (n := n) fun i ↦ a.getD i.val 0 * b.getD i.val 0) :=
  zipWords_encode _ _ (· * ·) mul_val (fun a b o i ha hb hi ho ↦ mul16_encode a b o i ha hb hi ho)
    a b n ha hb hsa hsb

/-- `a + b · c` on `n` words. -/
theorem mulAddWords_encode (a b : Array F) (c : F) (n : Nat) (ha : n ≤ a.size)
    (hb : n ≤ b.size) (hsa : 4 * a.size < USize.size) (hsb : 4 * b.size < USize.size) :
    mulAddWords p (encode a) (encode b) c.val n =
      encode (Array.ofFn (n := n) fun i ↦ a.getD i.val 0 + b.getD i.val 0 * c) :=
  zipWords_encode _ _ (fun x y ↦ x + y * c) (fun x y ↦ by rw [mul_val, add_val])
    (fun a b o i ha hb hi ho ↦ mulAdd16_encode a b o c i ha hb hi ho) a b n ha hb hsa hsb

/-- `n` copies of `c`. -/
theorem replicateWord_encode (c : F) (n : Nat) (hn : 4 * n < USize.size) :
    replicateWord c.val n = encode (Array.replicate n c) := by
  unfold replicateWord
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  rw [zeroWords_eq (p := p), ← upto_zero (Array.replicate n 0) fun _ ↦ c, List.range_eq_range',
    foldl_tail _ _ _ _ _ (fun k _ hk ↦ write_upto _ (fun _ ↦ c) k
      (by rw [Array.size_replicate]; omega) (by rw [Array.size_replicate]; omega)),
    Nat.zero_add, upto_full _ _ _ (Array.size_replicate ..)]
  congr 1
  apply Array.ext (by rw [Array.size_ofFn, Array.size_replicate])
  intro j _ _
  simp only [Array.getElem_ofFn, Array.getElem_replicate]

/-- `mulAddInto16` splices multiply-adds in place. -/
theorem mulAddInto16_encode (o b : Array F) (io ib : USize) (c : F) (hout hb)
    (hi : io.toNat + 16 ≤ o.size) (ho : 4 * o.size < USize.size) :
    mulAddInto16 p (encode o) io (encode b) ib c.val hout hb = encode (splice o io.toNat
      (lit16 fun t ↦ o.getD (io.toNat + t) 0 + b.getD (ib.toNat + t) 0 * c)) := by
  unfold mulAddInto16
  simp only [rd_encode, add_val, mul_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- The entries of `upto o f k` from `k` on are `o`'s. -/
theorem getD_upto_of_le (o : Array F) (f : Nat → F) (k j : Nat) (hj : k ≤ j) :
    (upto o f k).getD j 0 = o.getD j 0 := by
  rw [getD_upto]
  by_cases h : j < o.size
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), getD_eq_zero o j (by omega)]

/-- `out[k] += c · b[bo + k]` for `k < n`, in place. -/
theorem mulAddInto_upto (o b : Array F) (bo : Nat) (c : F) (n : Nat) (hn : n ≤ o.size)
    (hb : bo + n ≤ b.size) (hso : 4 * o.size < USize.size) (hsb : 4 * b.size < USize.size) :
    mulAddInto p (encode o) (encode b) bo c.val n =
      encode (upto o (fun k ↦ o.getD k 0 + b.getD (bo + k) 0 * c) n) := by
  unfold mulAddInto
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, pure_bind, dite_pure_yield, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hso' : (encode o).size = 4 * o.size := size_encode_fields o
  have hsb' : (encode b).size = 4 * b.size := size_encode_fields b
  let f (k : Nat) : F := o.getD k 0 + b.getD (bo + k) 0 * c
  rw [foldl_blocks o f (n / 16) _ (fun m hm ↦ by
    have h16 : 16 * m + 16 ≤ n := by omega
    rw [dite_eq_left_of_eq_true (eq_true ⟨by rw [size_encode_fields, size_upto]; omega,
      by omega, by rw [size_encode_fields, size_upto]; omega, by omega⟩),
      mulAddInto16_encode _ _ _ _ _ _ _ (by simp only [USize.toNat_ofNatLT, size_upto]; omega)
        (by rw [size_upto]; exact hso)]
    simp only [USize.toNat_ofNatLT]
    refine Eq.trans ?_ (congrArg encode (splice_upto o f _ (by omega)))
    congr 2
    refine congrArg lit16 (funext fun t ↦ ?_)
    rw [getD_upto_of_le _ _ _ _ (by omega), Nat.add_assoc]),
    foldl_tail _ f _ _ _ (fun k _ hk ↦ by
      rw [read_encode _ k (by rw [size_upto]; exact hso) (by rw [size_upto]; omega),
        read_encode b _ hsb (by omega), getD_upto_of_le _ _ _ _ (Nat.le_refl _), mul_val,
        add_val]
      exact write_upto _ f k (by omega) hso),
    Nat.add_sub_cancel' (Nat.mul_div_le n 16)]

/-- `out[k] += c · b[bo + k]` for all `n` words of `out`. -/
theorem mulAddInto_encode (o b : Array F) (bo : Nat) (c : F) (hb : bo + o.size ≤ b.size)
    (hso : 4 * o.size < USize.size) (hsb : 4 * b.size < USize.size) :
    mulAddInto p (encode o) (encode b) bo c.val o.size =
      encode (Array.ofFn (n := o.size) fun k ↦ o.getD k.val 0 + b.getD (bo + k.val) 0 * c) := by
  rw [mulAddInto_upto o b bo c o.size (Nat.le_refl _) hb hso hsb, upto_full _ _ _ rfl]

/-- `dotInto16` splices running dot products in place. -/
theorem dotInto16_encode (o b c : Array F) (io ib ic : USize) (hout hb hc)
    (hi : io.toNat + 16 ≤ o.size) (ho : 4 * o.size < USize.size) :
    dotInto16 p (encode o) io (encode b) ib (encode c) ic hout hb hc = encode (splice o io.toNat
      (lit16 fun t ↦ o.getD (io.toNat + t) 0 + b.getD (ib.toNat + t) 0 * c.getD (ic.toNat + t) 0))
    := by
  unfold dotInto16
  simp only [rd_encode, add_val, mul_val]
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _
    (by rw [size_encode_fields]; exact ho) hi]
  rfl

/-- A running sum of words of field elements. -/
theorem foldl_add (g : Nat → F) (r : Nat → UInt32) (k0 K : Nat)
    (hr : ∀ k, k0 ≤ k → k < k0 + K → r k = (g k).val) (s : F) :
    (List.range' k0 K).foldl (fun acc k ↦ add p acc (r k)) s.val =
      (s + ∑ k ∈ Finset.range K, g (k0 + k)).val := by
  induction K generalizing k0 s with
  | zero => rw [List.range'_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | succ K ih =>
    rw [List.range'_succ, List.foldl_cons, hr k0 (Nat.le_refl _) (by omega), add_val,
      ih (k0 + 1) (fun k h1 h2 ↦ hr k (by omega) (by omega)), Finset.sum_range_succ',
      add_assoc, add_comm (g k0)]
    simp only [Nat.add_assoc, Nat.add_comm 1, Nat.add_zero]

/-- Sixteen interleaved partial sums. -/
theorem sum_interleave (x : Nat → F) (M : Nat) :
    ∑ t ∈ Finset.range 16, ∑ m ∈ Finset.range M, x (16 * m + t) =
      ∑ k ∈ Finset.range (16 * M), x k := by
  induction M with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero, Nat.mul_zero]
  | succ M ih =>
    simp only [Finset.sum_range_succ (fun m ↦ x (16 * m + _)), Finset.sum_add_distrib, ih,
      Nat.mul_succ, Finset.sum_range_add]

/-- `∑ₖ b[bo + k] · c[k]` for `k < n`. -/
theorem dotAt_encode (b c : Array F) (bo n : Nat) (hb : bo + n ≤ b.size) (hc : n ≤ c.size)
    (hsb : 4 * b.size < USize.size) (hsc : 4 * c.size < USize.size) :
    dotAt p (encode b) bo (encode c) n =
      (∑ k ∈ Finset.range n, b.getD (bo + k) 0 * c.getD k 0).val := by
  unfold dotAt
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, pure_bind, dite_pure_yield, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hsb' : (encode b).size = 4 * b.size := size_encode_fields b
  have hsc' : (encode c).size = 4 * c.size := size_encode_fields c
  let x (k : Nat) : F := b.getD (bo + k) 0 * c.getD k 0
  let S (M t : Nat) : F := ∑ m ∈ Finset.range M, x (16 * m + t)
  have hacc : ∀ M ≤ n / 16, (List.range M).foldl (fun acc a ↦
      if h : 4 * 15 + 3 < acc.size ∧ 4 * (bo + 16 * a + 15) + 3 < (encode b).size ∧
          4 * (16 * a + 15) + 3 < (encode c).size ∧ acc.size < USize.size ∧
          (encode b).size < USize.size ∧ (encode c).size < USize.size then
        dotInto16 p acc 0 (encode b) (USize.ofNatLT (bo + 16 * a) (by omega)) (encode c)
          (USize.ofNatLT (16 * a) (by omega))
          (by simp only [Fits, USize.toNat_zero, Nat.zero_add]; exact ⟨h.1, h.2.2.2.1⟩)
          (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.1, h.2.2.2.2.1⟩)
          (by simp only [Fits, USize.toNat_ofNatLT]; exact ⟨h.2.2.1, h.2.2.2.2.2⟩)
      else acc) (zeroWords 16) = encode (Array.ofFn (n := 16) fun t ↦ S M t.val) := by
    intro M hM
    induction M with
    | zero =>
      rw [List.range_zero, List.foldl_nil, zeroWords_eq (p := p)]
      rfl
    | succ M ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      have h16 : 16 * M + 16 ≤ n := by omega
      have h0 : (0 : USize).toNat + 16 ≤ (Array.ofFn (n := 16) fun t ↦ S M t.val).size := by
        rw [USize.toNat_zero, Array.size_ofFn]
      have h1 : 4 * (Array.ofFn (n := 16) fun t ↦ S M t.val).size < USize.size := by
        rw [Array.size_ofFn]; have := USize.le_size; omega
      rw [dite_eq_left_of_eq_true (eq_true ⟨by rw [size_encode_fields, Array.size_ofFn]; omega,
        by omega, by omega, by rw [size_encode_fields]; omega, by omega,
        by omega⟩), dotInto16_encode _ _ _ _ _ _ _ _ _ h0 h1]
      refine congrArg encode ?_
      have h2 : ∀ g : Nat → F, (0 : USize).toNat + (lit16 g).size ≤
          (Array.ofFn (n := 16) fun t ↦ S M t.val).size := fun g ↦ by
        rw [size_lit16]; exact h0
      apply array_eq_of_getD _ _ 0 (by rw [size_splice _ _ _ (h2 _), Array.size_ofFn,
        Array.size_ofFn])
      intro t
      rw [getD_splice _ _ _ (h2 _), getD_ofFn, getD_ofFn]
      simp only [USize.toNat_zero, USize.toNat_ofNatLT, size_lit16, Nat.zero_add, Nat.not_lt_zero,
        ite_false]
      split
      · rw [getD_lit16 _ _ (by assumption), getD_ofFn, ite_eq_left_of_eq_true _ _
          (eq_true (by assumption)), Nat.sub_zero]
        simp only [S, x, Finset.sum_range_succ, Nat.add_assoc]
      · rfl
  have hA : 4 * (Array.ofFn (n := 16) fun t ↦ S (n / 16) t.val).size < USize.size := by
    rw [Array.size_ofFn]; have := USize.le_size; omega
  rw [hacc (n / 16) (Nat.le_refl _), List.range_eq_range', ← zero_val (p := p),
    foldl_add (S (n / 16)) _ 0 16 (fun k _ hk ↦ by
      rw [read_encode _ k hA (by rw [Array.size_ofFn]; omega), getD_ofFn,
        ite_eq_left_of_eq_true _ _ (eq_true (by omega))]),
    foldl_add x _ _ _ (fun k _ hk ↦ by
      rw [read_encode b _ hsb (by omega), read_encode c _ hsc (by omega), mul_val])]
  simp only [S, zero_add]
  rw [sum_interleave, ← Finset.sum_range_add, Nat.add_sub_cancel' (Nat.mul_div_le n 16)]

end CompStark.Words

namespace CompStark.Stark.EVec
open CompPoly.PackedRepr (encode)
open CompStark.Words
open CompStark.Stark.Fast (RV)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields getD_ofFn_bounded ofWord_val)
open CompPoly.CPolynomial.NTTFast.Packed.Native (zeroWords)
open CompPoly.CPolynomial.NTTFast.Packed (Native.encodeFields_eq)

open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p
local notation "W" => (Binomial4.W : FastField p)

/-- The fused sum of four products. -/
theorem mulAdd4_eq (a b c d e f g k : F) :
    Montgomery.Native32.mulAdd4 a b c d e f g k = a * b + c * d + e * f + g * k := by
  apply Montgomery.Native32.toField_injective
  simp only [Montgomery.Native32.toField_mulAdd4, Montgomery.Native32.toField_add,
    Montgomery.Native32.toField_mul]

/-- The coordinates of the products in `F[X] / (X⁴ - W)`. -/
theorem mul_coords [Binomial4 p] (x y : EF) : x * y =
    ⟨x.c0 * y.c0 + W * (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1),
      x.c0 * y.c1 + x.c1 * y.c0 + W * (x.c2 * y.c3 + x.c3 * y.c2),
      x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 + W * (x.c3 * y.c3),
      x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0⟩ := by
  apply Montgomery.Native32.Ext4.ext' <;>
    simp only [show x * y = Montgomery.Native32.Ext4.mul x y from rfl, Montgomery.Native32.Ext4.mul,
      Binomial4.mulW_eq, mulAdd4_eq] <;> ring

/-- An in-range coordinate of an array of extension elements. -/
theorem getD_map (a : Array EF) (pr : EF → F) (i : Nat) (h : i < a.size) :
    (a.map pr).getD i 0 = pr a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h]
  rfl

/-- Planes of tabulated coordinates represent the elements with those coordinates. -/
theorem rv_mk {n : Nat} {P0 P1 P2 P3 : ByteArray} (c : Array EF) (hn : c.size = n)
    (f0 f1 f2 f3 : Nat → F)
    (h0 : P0 = encode (Array.ofFn (n := n) fun i ↦ f0 i.val))
    (h1 : P1 = encode (Array.ofFn (n := n) fun i ↦ f1 i.val))
    (h2 : P2 = encode (Array.ofFn (n := n) fun i ↦ f2 i.val))
    (h3 : P3 = encode (Array.ofFn (n := n) fun i ↦ f3 i.val))
    (hc : ∀ i (h : i < c.size), c[i] = ⟨f0 i, f1 i, f2 i, f3 i⟩) :
    RV ⟨n, P0, P1, P2, P3⟩ c := by
  subst hn
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [h0, h1, h2, h3]
    congr 1
    apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
    intro i hi _
    rw [Array.size_ofFn] at hi
    simp only [Array.getElem_ofFn, Array.getElem_map, hc i hi]

/-- A plane is its tabulated coordinates. -/
theorem encode_map (a : Array EF) (pr : EF → F) :
    encode (a.map pr) = encode (Array.ofFn (n := a.size) fun i ↦ (a.map pr).getD i.val 0) := by
  congr 1
  apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
  intro i hi _
  rw [Array.size_map] at hi
  simp only [Array.getElem_ofFn, getD_map a pr i hi, Array.getElem_map]

/-- Represented, indexable planes read back their elements. -/
theorem toArray_eq {v : EVec p} {a : Array EF} (hv : RV v a)
    (hs : 4 * a.size < USize.size) : v.toArray = a := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  have hm : ∀ pr : EF → F, 4 * (a.map pr).size < USize.size := fun pr ↦ by
    rw [Array.size_map]; exact hs
  apply Array.ext (by rw [EVec.toArray, Array.size_ofFn, hvn])
  intro i hi _
  rw [EVec.toArray, Array.size_ofFn, hvn] at hi
  have hm' : ∀ pr : EF → F, i < (a.map pr).size := fun pr ↦ by rw [Array.size_map]; exact hi
  simp only [EVec.toArray, Array.getElem_ofFn, EVec.get, h0, h1, h2, h3,
    read_encode _ _ (hm _) (hm' _), EVec.ofW, ofWord_val, getD_map a _ i hi]

/-- The planes of an array represent it. -/
theorem ofArray_rel (a : Array EF) : RV (EVec.ofArray a) a := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> exact Native.encodeFields_eq _

/-- Zero planes represent zeros. -/
theorem zeros_rel (n : Nat) : RV (zeros (p := p) n) (Array.replicate n 0) := by
  refine ⟨(Array.size_replicate ..).symm, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [zeros, zeroWords_eq (p := p), Array.map_replicate]
    rfl

/-- Elementwise sums. -/
theorem add_rel {v w : EVec p} {a b : Array EF} (hv : RV v a) (hw : RV w b) (hn : v.n = w.n)
    (hs : 4 * a.size < USize.size) : RV (v.add w) (Array.zipWith (· + ·) a b) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  obtain ⟨hwn, g0, g1, g2, g3⟩ := hw
  have hb : 4 * b.size < USize.size := by omega
  have hab : a.size = b.size := by omega
  unfold EVec.add
  rw [h0, h1, h2, h3, g0, g1, g2, g3, hvn]
  refine rv_mk _ (by rw [Array.size_zipWith, hab, Nat.min_self])
    (fun i ↦ (a.map (·.c0)).getD i 0 + (b.map (·.c0)).getD i 0)
    (fun i ↦ (a.map (·.c1)).getD i 0 + (b.map (·.c1)).getD i 0)
    (fun i ↦ (a.map (·.c2)).getD i 0 + (b.map (·.c2)).getD i 0)
    (fun i ↦ (a.map (·.c3)).getD i 0 + (b.map (·.c3)).getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply addWords_encode <;> simp only [Array.size_map] <;> omega)
  rw [Array.size_zipWith] at hi
  simp only [Array.getElem_zipWith, getD_map a _ i (by omega), getD_map b _ i (by omega)]
  rfl

/-- Elementwise differences. -/
theorem sub_rel {v w : EVec p} {a b : Array EF} (hv : RV v a) (hw : RV w b) (hn : v.n = w.n)
    (hs : 4 * a.size < USize.size) : RV (v.sub w) (Array.zipWith (· - ·) a b) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  obtain ⟨hwn, g0, g1, g2, g3⟩ := hw
  have hb : 4 * b.size < USize.size := by omega
  have hab : a.size = b.size := by omega
  unfold EVec.sub
  rw [h0, h1, h2, h3, g0, g1, g2, g3, hvn]
  refine rv_mk _ (by rw [Array.size_zipWith, hab, Nat.min_self])
    (fun i ↦ (a.map (·.c0)).getD i 0 - (b.map (·.c0)).getD i 0)
    (fun i ↦ (a.map (·.c1)).getD i 0 - (b.map (·.c1)).getD i 0)
    (fun i ↦ (a.map (·.c2)).getD i 0 - (b.map (·.c2)).getD i 0)
    (fun i ↦ (a.map (·.c3)).getD i 0 - (b.map (·.c3)).getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply subWords_encode <;> simp only [Array.size_map] <;> omega)
  rw [Array.size_zipWith] at hi
  simp only [Array.getElem_zipWith, getD_map a _ i (by omega), getD_map b _ i (by omega)]
  rfl

/-- An in-range entry of a constant array. -/
theorem getD_replicate (n : Nat) (x : F) (i : Nat) (h : i < n) :
    (Array.replicate n x).getD i 0 = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, ite_eq_left_of_eq_true _ _
    (eq_true h), Option.getD_some]

/-- A scalar minus every element. -/
theorem rsub_rel {v : EVec p} {a : Array EF} (s : EF) (hv : RV v a)
    (hs : 4 * a.size < USize.size) : RV (rsub s v) (a.map (s - ·)) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  unfold EVec.rsub
  have hr : 4 * v.n < USize.size := by omega
  rw [replicateWord_encode _ _ hr, replicateWord_encode _ _ hr, replicateWord_encode _ _ hr,
    replicateWord_encode _ _ hr, h0, h1, h2, h3, hvn]
  refine rv_mk _ (by rw [Array.size_map])
    (fun i ↦ (Array.replicate a.size s.c0).getD i 0 - (a.map (·.c0)).getD i 0)
    (fun i ↦ (Array.replicate a.size s.c1).getD i 0 - (a.map (·.c1)).getD i 0)
    (fun i ↦ (Array.replicate a.size s.c2).getD i 0 - (a.map (·.c2)).getD i 0)
    (fun i ↦ (Array.replicate a.size s.c3).getD i 0 - (a.map (·.c3)).getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply subWords_encode <;> simp only [Array.size_map, Array.size_replicate] <;>
    omega)
  rw [Array.size_map] at hi
  simp only [Array.getElem_map, getD_map a _ i hi, getD_replicate _ _ i hi]
  rfl

/-- Every element times a base element. -/
theorem mulBase_rel [Mont32BaseField p] [Binomial4 p] {v : EVec p} {a : Array EF} (bs : Array F)
    (hv : RV v a)
    (hb : a.size ≤ bs.size) (hs : 4 * bs.size < USize.size) :
    RV (v.mulBase (encode bs)) (Array.zipWith (fun x y ↦ x * Ext.ofBase y) a bs) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  unfold EVec.mulBase
  rw [h0, h1, h2, h3, hvn]
  refine rv_mk _ (by rw [Array.size_zipWith, Nat.min_eq_left hb])
    (fun i ↦ (a.map (·.c0)).getD i 0 * bs.getD i 0)
    (fun i ↦ (a.map (·.c1)).getD i 0 * bs.getD i 0)
    (fun i ↦ (a.map (·.c2)).getD i 0 * bs.getD i 0)
    (fun i ↦ (a.map (·.c3)).getD i 0 * bs.getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply mulWords_encode <;> (try simp only [Array.size_map]) <;> omega)
  rw [Array.size_zipWith] at hi
  simp only [Array.getElem_zipWith, getD_map a _ i (by omega), mul_coords, Ext.ofBase,
    Mont32.ofBase_ext4, Montgomery.Native32.Ext4.ofBase, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem
      (show i < bs.size by omega), Option.getD_some]
  congr 1 <;> ring

/-- `∑ⱼ Xⱼ · sⱼ` for four planes. -/
theorem combine4_encode (n : Nat) (X0 X1 X2 X3 : Array F) (s0 s1 s2 s3 : F)
    (h0 : n ≤ X0.size) (h1 : n ≤ X1.size) (h2 : n ≤ X2.size) (h3 : n ≤ X3.size)
    (g0 : 4 * X0.size < USize.size) (g1 : 4 * X1.size < USize.size)
    (g2 : 4 * X2.size < USize.size) (g3 : 4 * X3.size < USize.size) :
    combine p n [(encode X0, s0.val), (encode X1, s1.val), (encode X2, s2.val),
      (encode X3, s3.val)] = encode (Array.ofFn (n := n) fun i ↦ X0.getD i.val 0 * s0 +
        X1.getD i.val 0 * s1 + X2.getD i.val 0 * s2 + X3.getD i.val 0 * s3) := by
  have hn : 4 * n < USize.size := by omega
  simp only [combine, List.foldl_cons, List.foldl_nil, zeroWords_eq (p := p)]
  rw [mulAddWords_encode _ _ _ _ (by rw [Array.size_replicate]) h0
      (by rw [Array.size_replicate]; exact hn) g0,
    mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) h1 (by rw [Array.size_ofFn]; exact hn) g1,
    mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) h2 (by rw [Array.size_ofFn]; exact hn) g2,
    mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) h3 (by rw [Array.size_ofFn]; exact hn) g3]
  refine congrArg encode (congrArg (Array.ofFn (n := n)) (funext fun i ↦ ?_))
  simp only [getD_ofFn_bounded _ _ i.isLt, getD_replicate _ _ _ i.isLt, zero_add]

/-- Every element times an extension scalar. -/
theorem smul_rel [Binomial4 p] {v : EVec p} {a : Array EF} (s : EF) (hv : RV v a)
    (hs : 4 * a.size < USize.size) : RV (v.smul s) (a.map (· * s)) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  unfold EVec.smul
  simp only [h0, h1, h2, h3, hvn]
  have hm : ∀ pr : EF → F, a.size ≤ (a.map pr).size := fun pr ↦ by rw [Array.size_map]
  have hm' : ∀ pr : EF → F, 4 * (a.map pr).size < USize.size := fun pr ↦ by
    rw [Array.size_map]; exact hs
  rw [combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _) (hm' _) (hm' _) (hm' _)
      (hm' _), combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _) (hm' _) (hm' _)
      (hm' _) (hm' _), combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _) (hm' _)
      (hm' _) (hm' _) (hm' _), combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _)
      (hm' _) (hm' _) (hm' _) (hm' _)]
  let A (pr : EF → F) (i : Nat) : F := (a.map pr).getD i 0
  refine rv_mk _ (Array.size_map ..)
    (fun i ↦ A (·.c0) i * s.c0 + A (·.c1) i * (Binomial4.mulW s.c3) + A (·.c2) i *
        (Binomial4.mulW s.c2) +
      A (·.c3) i * (Binomial4.mulW s.c1))
    (fun i ↦ A (·.c0) i * s.c1 + A (·.c1) i * s.c0 + A (·.c2) i * (Binomial4.mulW s.c3) +
      A (·.c3) i * (Binomial4.mulW s.c2))
    (fun i ↦ A (·.c0) i * s.c2 + A (·.c1) i * s.c1 + A (·.c2) i * s.c0 +
      A (·.c3) i * (Binomial4.mulW s.c3))
    (fun i ↦ A (·.c0) i * s.c3 + A (·.c1) i * s.c2 + A (·.c2) i * s.c1 + A (·.c3) i * s.c0)
    rfl rfl rfl rfl fun i hi ↦ ?_
  rw [Array.size_map] at hi
  simp only [A, Array.getElem_map, getD_map a _ i hi, mul_coords, Binomial4.mulW_eq]
  congr 1 <;> ring

/-- A plane as tabulated coordinates. -/
theorem encode_map_eq (a : Array EF) (pr : EF → F) (n : Nat) (h : a.size = n) :
    encode (a.map pr) = encode (Array.ofFn (n := n) fun i ↦ pr (a[i.val]'(by omega))) := by
  subst h
  congr 1
  apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
  intro i _ _
  simp only [Array.getElem_ofFn, Array.getElem_map]

/-- `n` zero words as a tabulated array. -/
theorem zeroWords_ofFn (n : Nat) : zeroWords n = encode (Array.ofFn (n := n) fun _ ↦ (0 : F)) := by
  rw [zeroWords_eq (p := p)]
  refine congrArg encode (Array.ext (by rw [Array.size_ofFn, Array.size_replicate]) ?_)
  intro i _ _
  simp only [Array.getElem_ofFn, Array.getElem_replicate]

/-- Sums of tabulated arrays. -/
theorem addWords_ofFn {n : Nat} (hn : 4 * n < USize.size) (f g : Fin n → F) :
    addWords p (encode (Array.ofFn f)) (encode (Array.ofFn g)) n =
      encode (Array.ofFn fun i ↦ f i + g i) := by
  rw [addWords_encode _ _ _ (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn])
    (by rw [Array.size_ofFn]; exact hn) (by rw [Array.size_ofFn]; exact hn)]
  refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
  rw [getD_ofFn_bounded _ _ i.isLt, getD_ofFn_bounded _ _ i.isLt]

/-- Differences of tabulated arrays. -/
theorem subWords_ofFn {n : Nat} (hn : 4 * n < USize.size) (f g : Fin n → F) :
    subWords p (encode (Array.ofFn f)) (encode (Array.ofFn g)) n =
      encode (Array.ofFn fun i ↦ f i - g i) := by
  rw [subWords_encode _ _ _ (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn])
    (by rw [Array.size_ofFn]; exact hn) (by rw [Array.size_ofFn]; exact hn)]
  refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
  rw [getD_ofFn_bounded _ _ i.isLt, getD_ofFn_bounded _ _ i.isLt]

/-- Products of tabulated arrays. -/
theorem mulWords_ofFn {n : Nat} (hn : 4 * n < USize.size) (f g : Fin n → F) :
    mulWords p (encode (Array.ofFn f)) (encode (Array.ofFn g)) n =
      encode (Array.ofFn fun i ↦ f i * g i) := by
  rw [mulWords_encode _ _ _ (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn])
    (by rw [Array.size_ofFn]; exact hn) (by rw [Array.size_ofFn]; exact hn)]
  refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
  rw [getD_ofFn_bounded _ _ i.isLt, getD_ofFn_bounded _ _ i.isLt]

/-- Multiply-adds of tabulated arrays. -/
theorem mulAddWords_ofFn {n : Nat} (hn : 4 * n < USize.size) (f g : Fin n → F)
    (c : F) : mulAddWords p (encode (Array.ofFn f)) (encode (Array.ofFn g)) c.val n =
      encode (Array.ofFn fun i ↦ f i + g i * c) := by
  rw [mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn])
    (by rw [Array.size_ofFn]; exact hn) (by rw [Array.size_ofFn]; exact hn)]
  refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
  rw [getD_ofFn_bounded _ _ i.isLt, getD_ofFn_bounded _ _ i.isLt]

/-- Planes of tabulated coordinates represent the elements with those coordinates. -/
theorem rv_ofFn {n : Nat} (c : Array EF) (hn : c.size = n) (f0 f1 f2 f3 : Fin n → F)
    (hc : ∀ i : Fin n, c[i.val]'(by omega) = ⟨f0 i, f1 i, f2 i, f3 i⟩) :
    RV ⟨n, encode (Array.ofFn f0), encode (Array.ofFn f1), encode (Array.ofFn f2),
      encode (Array.ofFn f3)⟩ c := by
  subst hn
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  · refine congrArg encode ?_
    apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
    intro i hi _
    rw [Array.size_ofFn] at hi
    simp only [Array.getElem_ofFn, Array.getElem_map, hc ⟨i, hi⟩]

/-- Elementwise products. -/
theorem mul_rel [Binomial4 p] {v w : EVec p} {a b : Array EF} (hv : RV v a) (hw : RV w b)
    (hn : v.n = w.n)
    (hs : 4 * a.size < USize.size) : RV (v.mul w) (Array.zipWith (· * ·) a b) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  obtain ⟨hwn, g0, g1, g2, g3⟩ := hw
  have hab : b.size = a.size := by omega
  simp only [EVec.mul, h0, h1, h2, h3, g0, g1, g2, g3, hvn, List.foldl_cons, List.foldl_nil]
  simp only [zeroWords_ofFn (p := p), encode_map_eq a _ a.size rfl, encode_map_eq b _ a.size hab]
  simp only [mulWords_ofFn hs]
  simp only [addWords_ofFn hs]
  simp only [mulAddWords_ofFn hs]
  refine rv_ofFn (n := a.size) (Array.zipWith (· * ·) a b) ?_ _ _ _ _ ?_
  · rw [Array.size_zipWith, hab, Nat.min_self]
  intro i
  simp only [Array.getElem_zipWith, mul_coords]
  generalize a[i.val] = x
  generalize b[i.val]'(by omega) = y
  simp only [Montgomery.Native32.Ext4.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

end CompStark.Stark.EVec

namespace CompStark.Stark
open CompPoly.PackedRepr (encode)
open CompStark.Words
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields getD_ofFn_bounded add_val mul_val
  ofWord_val mul array_eq_of_getD getD_setIfInBounds)
open CompPoly.CPolynomial.NTTFast.Packed.Native (zeroWords read write)

open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

/-- An entry of a tabulated array. -/
theorem getD_ofFn' {n : Nat} (f : Fin n → F) (i : Nat) :
    (Array.ofFn f).getD i 0 = if h : i < n then f ⟨i, h⟩ else 0 := by
  split
  · exact getD_ofFn_bounded _ _ (by assumption) _
  · exact getD_eq_zero _ _ (by rw [Array.size_ofFn]; omega)

/-- The inverses of words `i0, …, i0 + len - 1`, none of them zero. -/
theorem batchInvRange_encode (a : Array F) (i0 len : Nat) (ha : i0 + len ≤ a.size)
    (hs : 4 * a.size < USize.size) (hnz : ∀ k < len, a.getD (i0 + k) 0 ≠ 0) :
    batchInvRange p (encode a) i0 len =
      encode (Array.ofFn (n := len) fun k ↦ (a.getD (i0 + k.val) 0)⁻¹) := by
  unfold batchInvRange
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hl : 4 * len < USize.size := by omega
  let x (j : Nat) : F := a.getD (i0 + j) 0
  let P (k : Nat) : F := ∏ j ∈ Finset.range k, x j
  have hP : ∀ k ≤ len, P k ≠ 0 := fun k hk ↦
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ hnz j (by rw [Finset.mem_range] at hj; omega)
  have h1 : ∀ K ≤ len, (List.range K).foldl (fun b k ↦ (write b.1 k b.2,
      mul p b.2 (read (encode a) (i0 + k)))) (zeroWords len, (1 : F).val) =
      (encode (upto (Array.replicate len 0) P K), (P K).val) := by
    intro K hK
    induction K with
    | zero => rw [List.range_zero, List.foldl_nil, zeroWords_eq (p := p), upto_zero]; rfl
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      simp only
      rw [write_upto _ P K (by rw [Array.size_replicate]; omega)
        (by rw [Array.size_replicate]; omega), read_encode a _ hs (by omega), mul_val,
        show P (K + 1) = P K * x K from Finset.prod_range_succ _ _]
  have hpre : 4 * (upto (Array.replicate len 0) P len).size < USize.size := by
    rw [size_upto, Array.size_replicate]; exact hl
  let o (K : Nat) : Array F := Array.ofFn (n := len) fun j ↦ if len - K ≤ j.val then (x j)⁻¹ else 0
  have h2 : ∀ K ≤ len, (List.range K).foldl (fun b k ↦
      (mul p b.1 (read (encode a) (i0 + (len - 1 - k))),
        write b.2 (len - 1 - k) (mul p b.1 (read (encode (upto (Array.replicate len 0) P len))
          (len - 1 - k))))) (((P len)⁻¹).val, zeroWords len) =
      (((P (len - K))⁻¹).val, encode (o K)) := by
    intro K hK
    induction K with
    | zero =>
      rw [List.range_zero, List.foldl_nil, Nat.sub_zero, zeroWords_eq (p := p)]
      refine Prod.ext rfl (congrArg encode ?_)
      apply Array.ext (by rw [Array.size_ofFn, Array.size_replicate])
      intro j h _
      rw [Array.size_replicate] at h
      simp only [o, Array.getElem_replicate, Array.getElem_ofFn, Nat.sub_zero,
        ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_le_of_lt h))]
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      have hj : len - 1 - K < len := by omega
      have hPs : P (len - K) = P (len - 1 - K) * x (len - 1 - K) := by
        rw [show len - K = (len - 1 - K) + 1 by omega]
        exact Finset.prod_range_succ _ _
      have hx : x (len - 1 - K) ≠ 0 := hnz _ hj
      have hP' : P (len - 1 - K) ≠ 0 := hP _ (by omega)
      simp only
      rw [read_encode a _ hs (by omega), read_encode _ _ hpre (by
          rw [size_upto, Array.size_replicate]; exact hj), getD_upto, Array.size_replicate,
        ite_eq_left_of_eq_true _ _ (eq_true hj), ite_eq_left_of_eq_true _ _ (eq_true hj),
        mul_val, mul_val]
      refine Prod.ext ?_ ?_
      · simp only
        rw [show len - (K + 1) = len - 1 - K by omega, hPs, mul_inv, mul_assoc,
          inv_mul_cancel₀ hx, mul_one]
      · simp only
        rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode _ _ (by
          rw [size_encode_fields, Array.size_ofFn]; exact hl) (by rw [Array.size_ofFn]; exact hj)]
        refine congrArg encode ?_
        apply array_eq_of_getD _ _ 0 (by rw [Array.size_setIfInBounds, Array.size_ofFn,
          Array.size_ofFn])
        intro j
        simp only [o]
        rw [getD_setIfInBounds _ _ _ _ _ (by rw [Array.size_ofFn]; exact hj), getD_ofFn',
          getD_ofFn']
        by_cases hjj : j = len - 1 - K
        · subst hjj
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), dite_eq_left_of_eq_true (eq_true hj)]
          simp only [show len - (K + 1) ≤ len - 1 - K by omega, ite_true]
          rw [hPs, mul_inv, mul_comm (P _)⁻¹, mul_assoc, inv_mul_cancel₀ hP', mul_one]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hjj)]
          by_cases hjl : j < len
          · rw [dite_eq_left_of_eq_true (eq_true hjl), dite_eq_left_of_eq_true (eq_true hjl)]
            simp only [show (len - (K + 1) ≤ j) = (len - K ≤ j) from propext ⟨fun h ↦ by omega,
              fun h ↦ by omega⟩]
          · rw [dite_eq_right_of_eq_false (eq_false hjl), dite_eq_right_of_eq_false (eq_false hjl)]
  rw [h1 len (Nat.le_refl _), EVec.ofW, ofWord_val, h2 len (Nat.le_refl _)]
  refine congrArg encode ?_
  apply Array.ext (by rw [Array.size_ofFn, Array.size_ofFn])
  intro j h _
  simp only [o, Array.getElem_ofFn, Nat.sub_self, Nat.zero_le, ite_true, x]

/-! ### Parallel pieces -/

/-- A spawned task's value. -/
@[simp] theorem get_spawn {α : Type} (f : Unit → α) (prio : Task.Priority) :
    (Task.spawn f prio).get = f () := rfl

/-- Adjacent tabulated ranges. -/
theorem ofFn_append {α : Type} (g : Nat → α) (m l : Nat) :
    (Array.ofFn (n := m) fun j ↦ g j.val) ++ (Array.ofFn (n := l) fun j ↦ g (m + j.val)) =
      Array.ofFn (n := m + l) fun j ↦ g j.val := by
  apply Array.ext (by rw [Array.size_append, Array.size_ofFn, Array.size_ofFn, Array.size_ofFn])
  intro i h1 _
  rw [Array.size_append, Array.size_ofFn, Array.size_ofFn] at h1
  by_cases h : i < m
  · rw [Array.getElem_append_left (by rw [Array.size_ofFn]; exact h)]
    simp only [Array.getElem_ofFn]
  · rw [Array.getElem_append_right (by rw [Array.size_ofFn]; omega)]
    simp only [Array.getElem_ofFn, Array.size_ofFn]
    congr 1
    omega

/-- Tabulations of equal lengths. -/
theorem ofFn_len {α : Type} (h : Nat → α) {n m : Nat} (e : n = m) :
    (Array.ofFn (n := n) fun j ↦ h j.val) = Array.ofFn (n := m) fun j ↦ h j.val := by
  subst e; rfl

/-- Consecutive ranges of `size` elements, the last one up to `n`, concatenated. -/
theorem foldl_ranges {α : Type} (g : Nat → α) (n parts size : Nat) (hp : 0 < parts)
    (hs : (parts - 1) * size ≤ n) :
    (List.range parts).foldl (fun acc k ↦ acc ++
      Array.ofFn (n := if k + 1 = parts then n - k * size else size)
        fun j ↦ g (k * size + j.val)) #[] = Array.ofFn (n := n) fun j ↦ g j.val := by
  have key : ∀ K, K + 1 ≤ parts → (List.range K).foldl (fun acc k ↦ acc ++
      Array.ofFn (n := if k + 1 = parts then n - k * size else size)
        fun j ↦ g (k * size + j.val)) #[] = Array.ofFn (n := K * size) fun j ↦ g j.val := by
    intro K hK
    induction K with
    | zero =>
      rw [List.range_zero, List.foldl_nil, ofFn_len g (Nat.zero_mul size)]
      rfl
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      have hne : K + 1 ≠ parts := by omega
      rw [ofFn_len (fun j ↦ g (K * size + j)) (ite_eq_right_of_eq_false _ _ (eq_false hne)),
        ofFn_append g, ofFn_len g (Nat.succ_mul K size).symm]
  obtain ⟨P, rfl⟩ : ∃ P, parts = P + 1 := ⟨parts - 1, by omega⟩
  rw [List.range_succ, List.foldl_append, key P (Nat.le_refl _), List.foldl_cons, List.foldl_nil,
    ofFn_len (fun j ↦ g (P * size + j)) (ite_eq_left_of_eq_true _ _ (eq_true rfl)),
    ofFn_append g, ofFn_len g (Nat.add_sub_cancel' (by simpa using hs))]

/-- Encoded pieces, concatenated. -/
theorem foldl_bytes (parts : Nat) (B : Nat → ByteArray) (A : Nat → Array F)
    (hB : ∀ k < parts, B k = encode (A k)) :
    (List.range parts).foldl (fun acc k ↦ acc ++ B k) ByteArray.empty =
      encode ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]) := by
  rw [← CompPoly.PackedRepr.encode_empty (R := F)]
  generalize (#[] : Array F) = acc
  induction parts generalizing acc with
  | zero => rfl
  | succ P ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (fun k hk ↦ hB k (by omega)),
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil, hB P (by omega),
      CompPoly.PackedRepr.encode_append]

/-- Encoded pieces of parallel tasks, concatenated. -/
theorem foldl_tasks (parts : Nat) (B : Nat → ByteArray) (A : Nat → Array F)
    (hB : ∀ k < parts, B k = encode (A k)) :
    ((Array.range parts).map fun k ↦ Task.spawn fun _ ↦ B k).foldl
      (fun acc t ↦ acc ++ t.get) ByteArray.empty =
      encode ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]) := by
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
  exact foldl_bytes parts B A hB

/-- Mapping commutes with concatenation. -/
theorem foldl_append_map {α β : Type} (pr : α → β) (A : Nat → Array α) (L : List Nat)
    (acc : Array α) :
    L.foldl (fun acc k ↦ acc ++ (A k).map pr) (acc.map pr) =
      (L.foldl (fun acc k ↦ acc ++ A k) acc).map pr := by
  induction L generalizing acc with
  | nil => rfl
  | cons k L ih => rw [List.foldl_cons, List.foldl_cons, ← Array.map_append, ih]

/-- Ranges of `n / parts` elements, the last one up to `n`, fit below `n`. -/
theorem range_le (n parts k : Nat) (hk : k < parts) :
    k * (n / parts) + (if k + 1 = parts then n - k * (n / parts) else n / parts) ≤ n := by
  have h1 : (k + 1) * (n / parts) ≤ parts * (n / parts) := Nat.mul_le_mul_right _ (by omega)
  have h2 : parts * (n / parts) ≤ n := Nat.mul_div_le n parts
  rw [Nat.succ_mul] at h1
  generalize n / parts = size at h1 h2 ⊢
  split <;> omega

/-- Ranges of `n / parts` elements before the last start below `n`. -/
theorem ranges_cover (n parts : Nat) : (parts - 1) * (n / parts) ≤ n :=
  Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.mul_div_le n parts)

/-- The inverses of the first `n` words, none of them zero. -/
theorem batchInvWords_encode (a : Array F) (n : Nat) (ha : n ≤ a.size)
    (hs : 4 * a.size < USize.size) (hnz : ∀ k < n, a.getD k 0 ≠ 0) :
    batchInvWords p (encode a) n = encode (Array.ofFn (n := n) fun k ↦ (a.getD k.val 0)⁻¹) := by
  unfold batchInvWords
  have hp : 0 < (if n < 4096 then 1 else 16) := by split <;> decide
  generalize (if n < 4096 then 1 else 16) = parts at hp ⊢
  rw [foldl_tasks parts _
      (fun k ↦ Array.ofFn (n := if k + 1 = parts then n - k * (n / parts) else n / parts) fun j ↦
          (a.getD (k * (n / parts) + j.val) 0)⁻¹) fun k hk ↦
      batchInvRange_encode a _ _ (Nat.le_trans (range_le n parts k hk) ha) hs fun j hj ↦
        hnz _ (by have := range_le n parts k hk; omega),
    foldl_ranges (fun j ↦ (a.getD j 0)⁻¹) n parts _ hp (ranges_cover n parts)]

end CompStark.Stark

namespace CompStark.Stark.Fast
open CompPoly.PackedRepr (encode)

open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "EF" => Ext4 p

/-- Planes of parallel pieces, concatenated. -/
theorem joinPlanes_rel (n parts : Nat) (V : Nat → EVec p) (A : Nat → Array EF)
    (hV : ∀ k < parts, RV (V k) (A k))
    (hn : n = ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]).size) :
    RV (joinPlanes p n ((Array.range parts).map fun k ↦ Task.spawn fun _ ↦ #[(V k).c0, (V k).c1,
      (V k).c2, (V k).c3])) ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]) := by
  unfold joinPlanes
  simp only [← Array.foldl_toList, Array.toList_map, List.foldl_map, Array.toList_range,
    get_spawn]
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c0)) fun k hk ↦ (hV k hk).2.1).trans ?_
    rw [← foldl_append_map, Array.map_empty]
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c1)) fun k hk ↦ (hV k hk).2.2.1).trans ?_
    rw [← foldl_append_map, Array.map_empty]
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c2)) fun k hk ↦ (hV k hk).2.2.2.1).trans ?_
    rw [← foldl_append_map, Array.map_empty]
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c3)) fun k hk ↦ (hV k hk).2.2.2.2).trans ?_
    rw [← foldl_append_map, Array.map_empty]

end CompStark.Stark.Fast
