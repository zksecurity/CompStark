/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast
public import CompStark.Merkle.PackedCorrectness

/-! # The fast transcript is the specification's

The fast grinder, eight candidates per packed permutation in parallel waves, finds the
specification's smallest witness (`grind_eq`), so the fast transcript is the specification's
(`transcript_eq`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields Native.encodeFields_eq ofWord_val)
open CompStark.Poseidon2 CompStark.Poseidon2.Packed Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

/-- A word of an encoded array is its element. -/
theorem word_encode (a : Array F) (i : Nat) (hs : (encode a).size < USize.size)
    (hi : i < a.size) : word (encode a) i = a.getD i 0 := by
  rw [word, CompPoly.CPolynomial.NTTFast.Packed.Native.read_encode a i hs hi, ofWord_val]

/-- A witness check permutes the state overwritten by the input and the witness, and tests
coordinate 15; with `bits = 0` both accept. -/
theorem checkWitness_fst [Mont32BaseField p] (D : Duplex F 24) (hr : D.rate = 16) (c : Challenger F
    24)
    (bits : Nat) (w : F) :
    (Challenger.checkWitness D c bits w).1 =
      (D.canon (D.perm (Hash.overwrite c.state (c.input.push w).toList))[15] % 2 ^ bits == 0) := by
  by_cases hb : bits = 0
  · subst hb
    simp only [Challenger.checkWitness, ite_true, Nat.pow_zero, Nat.mod_one, beq_self_eq_true]
  simp only [Challenger.checkWitness, hb, ite_false, Challenger.sampleBits, Challenger.sample,
    Challenger.observe, Challenger.duplexing, hr]
  have hback (s : Vector F 24) : (s.toArray.extract 0 16).back?.getD 0 = s[15] := by
    simp only [Array.back?, Array.size_extract, Vector.size_toArray]
    simp
  by_cases h : (c.input.push w).size = 16
  · simp only [h, List.isEmpty_toArray, List.isEmpty_nil, Bool.not_true,
      Bool.false_or, Array.isEmpty_iff, Array.extract_eq_empty_iff, Vector.size_toArray,
      Nat.reduceLeDiff, inf_of_le_left, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, ↓reduceIte,
      hback]
  · simp only [h, Array.isEmpty_push, Bool.not_false, List.isEmpty_toArray,
      List.isEmpty_nil, Bool.or_self, ↓reduceIte, hback]

/-- The first `m` of `n, …, n + k - 1` with `P m`. -/
def firstFrom (P : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, n => if P n then some n else firstFrom P k (n + 1)

theorem firstFrom_add (P : Nat → Bool) (a b : Nat) : ∀ n,
    firstFrom P (a + b) n = (firstFrom P a n).or (firstFrom P b (n + a)) := by
  induction a with
  | zero => intro n; simp only [Nat.zero_add, firstFrom, Option.none_or, Nat.add_zero]
  | succ a ih =>
    intro n
    rw [Nat.add_right_comm, firstFrom, firstFrom, ih]
    split
    · rfl
    · rw [Nat.add_right_comm, Nat.add_assoc]

theorem firstFrom_congr {P Q : Nat → Bool} : ∀ k n, (∀ m, n ≤ m → m < n + k → P m = Q m) →
    firstFrom P k n = firstFrom Q k n
  | 0, _, _ => rfl
  | k + 1, n, h => by
    rw [firstFrom, firstFrom, h n (Nat.le_refl n) (by omega),
      firstFrom_congr k (n + 1) fun m h1 h2 ↦ h m (by omega) (by omega)]

theorem firstFrom_none {P : Nat → Bool} : ∀ k n, (∀ m, n ≤ m → m < n + k → P m = false) →
    firstFrom P k n = none
  | 0, _, _ => rfl
  | k + 1, n, h => by
    rw [firstFrom, h n (Nat.le_refl n) (by omega), firstFrom_none k (n + 1) fun m h1 h2 ↦
      h m (by omega) (by omega)]
    rfl

/-- `find?` over `0, …, k - 1` shifted by `n`. -/
theorem find?_range_map (P Q : Nat → Bool) : ∀ k n, (∀ l < k, Q l = P (n + l)) →
    ((List.range k).find? Q).map (n + ·) = firstFrom P k n
  | 0, _, _ => rfl
  | k + 1, n, hQ => by
    rw [List.range_succ_eq_map, List.find?_cons, firstFrom, hQ 0 (by omega), Nat.add_zero,
      ← find?_range_map P (Q ∘ Nat.succ) k (n + 1) fun l hl ↦ by
        rw [Function.comp, hQ (l + 1) (by omega), Nat.add_assoc, Nat.add_comm 1 l]]
    by_cases hP : P n
    · simp only [hP, ite_true, Option.map_some, Nat.add_zero]
    · simp only [hP, List.find?_map, Option.map_map, Bool.false_eq_true, ite_false]
      have e2 : ((fun l ↦ n + l) ∘ Nat.succ) = fun l ↦ n + 1 + l := by
        funext l; simp only [Function.comp, Nat.succ_eq_add_one]; omega
      rw [e2]

/-- The specification's grinding is a search for the first passing candidate. -/
theorem grindFrom_eq [Mont32BaseField p] (D : Duplex F 24) (c : Challenger F 24) (bits : Nat) : ∀
    fuel n,
    grindFrom D c bits fuel n =
      ((firstFrom (fun m ↦ (Challenger.checkWitness D c bits (m : F)).1) fuel n).map
        (fun m : Nat ↦ (m : F))).getD 0
  | 0, _ => rfl
  | fuel + 1, n => by
    rw [grindFrom, firstFrom]
    split
    · rfl
    · exact grindFrom_eq D c bits fuel (n + 1)

/-- A copy of an encoded array is the array. -/
theorem copy_encode (a : Array F) :
    (encode a).copySlice 0 ByteArray.empty 0 (encode a).size = encode a := by
  have h := CompPoly.PackedRepr.copySlice_encode a #[] 0 a.size
  have he : encode (#[] : Array F) = ByteArray.empty := rfl
  rw [Nat.mul_zero, he, Nat.zero_add, ← CompPoly.PackedRepr.size_encode, ByteArray.size_empty] at h
  rw [h, Array.empty_append, Array.extract_size]

/-- A word write sets an element in bounds and leaves the words past the end. -/
theorem write_encode_set (a : Array F) (i : Nat) (x : F) (hi : 4 * (i + 1) < USize.size)
    (ha : 4 * a.size < USize.size) :
    CompPoly.CPolynomial.NTTFast.Packed.Native.write (encode a) i x.val =
      encode (a.setIfInBounds i x) := by
  by_cases h : i < a.size
  · exact CompPoly.CPolynomial.NTTFast.Packed.Native.write_encode a i
      (by rw [size_encode_fields]; omega) h x
  · have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    have ho : (i.toUSize * 4).toNat = 4 * i := by
      rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' (by omega),
        CompPoly.CPolynomial.NTTFast.Packed.Native.usize_numeral 4 (by decide),
        Nat.mod_eq_of_lt (by rw [hsize]; omega)]
      omega
    have hs : (encode (a.map Subtype.val)).size < USize.size := by
      rw [CompPoly.PackedRepr.size_encode_uint32, Array.size_map]; exact ha
    have hf := CompPoly.CPolynomial.NTTFast.Packed.Native.storeWords_fits (a.map Subtype.val)
      (i.toUSize * 4) 1 i (by decide) ho hs
    rw [Array.setIfInBounds_eq_of_size_le (by omega)]
    unfold CompPoly.CPolynomial.NTTFast.Packed.Native.write
    rw [CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val,
      CompPoly.CPolynomial.NTTFast.Packed.Native.storeWords_eq]
    have hn : ¬ (i + (1 : UInt8).toNat ≤ (a.map Subtype.val).size) := by
      rw [Array.size_map, show (1 : UInt8).toNat = 1 by decide]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' ↦ hn (hf.mp h'))]

/-- The packed group of batch `b` with lanes `0, …, n - 1` written: lane `l` is `base` with the
candidate `8 b + l` in coordinate `wi`. -/
def batchGroup (base : Vector F 24) (wi b n : Nat) : Array F :=
  Array.ofFn (n := 192) fun k ↦
    if k.val / 8 = wi ∧ k.val % 8 < n then ((8 * b + k.val % 8 : Nat) : F)
    else base.toArray.getD (k.val / 8) 0

theorem size_batchGroup (base : Vector F 24) (wi b n : Nat) : (batchGroup base wi b n).size = 192 :=
  Array.size_ofFn

theorem writes_encode (base : Vector F 24) (wi b : Nat) (hw : wi ≤ 24) : ∀ n ≤ 8,
    (List.range n).foldl (fun W l ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write W
      (8 * wi + l) ((8 * b + l : Nat) : F).val) (encode (batchGroup base wi b 0)) =
      encode (batchGroup base wi b n)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, writes_encode base wi b hw n (by omega),
      List.foldl_cons, List.foldl_nil, write_encode_set _ _ _ (by have := USize.le_size; omega)
        (by rw [size_batchGroup]; have := USize.le_size; omega)]
    refine congrArg encode ?_
    apply Array.ext
    · rw [Array.size_setIfInBounds, size_batchGroup, size_batchGroup]
    · intro k h1 h2
      rw [Array.getElem_setIfInBounds (by rw [size_batchGroup] at h2 ⊢; exact h2)]
      simp only [batchGroup, Array.getElem_ofFn]
      by_cases hk : 8 * wi + n = k
      · subst hk
        have e1 : (8 * wi + n) / 8 = wi := by omega
        have e2 : (8 * wi + n) % 8 = n := by omega
        simp only [e1, e2, true_and, Nat.lt_succ_self, ite_true]
      · simp only [hk, ite_false]
        by_cases hw' : k / 8 = wi
        · have : k % 8 ≠ n := by omega
          simp only [hw', true_and, Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, this, or_false]
        · simp only [hw', false_and, ite_false]

/-- Lane `l` of the group of batch `b` is the state overwritten by the input and candidate
`8 b + l`; a candidate past coordinate 23 is dropped on both sides. -/
theorem lane_batchGroup [Mont32BaseField p] (c : Challenger F 24) (b l : Nat) (hl : l < 8) :
    lane 24 (batchGroup (Hash.overwrite c.state c.input.toList) (min c.input.size 24) b 8) 0 l =
      Hash.overwrite c.state (c.input.push ((8 * b + l : Nat) : F)).toList := by
  apply Vector.ext
  intro j hj
  have e1 : (8 * j + l) / 8 = j := by omega
  have e2 : (8 * j + l) % 8 = l := by omega
  simp only [lane, Vector.getElem_ofFn, Poseidon2.Packed.word, Nat.zero_add, batchGroup,
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, show 8 * j + l < 192 by omega, dite_true,
    Option.getD_some, e1, e2, hl, and_true, Hash.overwrite, Array.toList_push]
  by_cases hj' : j = min c.input.size 24
  · have hj2 : j = c.input.size := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hj')]
    subst hj2
    simp only [Fin.getElem_fin, List.getD_eq_getElem?_getD, List.length_append,
      Array.length_toList, List.length_cons, List.length_nil, zero_add, getElem?_pos,
      List.getElem_append_right, tsub_self, List.getElem_cons_zero, Option.getD_some,
      lt_add_iff_pos_right, Nat.lt_one_iff, Std.le_refl]
  · have hj2 : j ≠ c.input.size := by omega
    simp only [hj', ite_false, Fin.getElem_fin, List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Vector.toArray_ofFn]
    rw [Array.getElem?_ofFn, dite_eq_left_of_eq_true (eq_true hj), Option.getD_some]
    by_cases hlt : j < c.input.size
    · rw [List.getElem?_append_left (by rw [Array.length_toList]; exact hlt), Array.getElem?_toList]
    · rw [List.getElem?_append_right (by rw [Array.length_toList]; omega),
        Array.getElem?_eq_none (show c.input.size ≤ j by omega), Array.length_toList,
        List.getElem?_eq_none (by simp only [List.length_singleton]; omega)]

variable [Mont32BaseField p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]

/-- Whether candidate `m` is a grinding witness for `bits`, below the field size. -/
def passes (c : Challenger F 24) (bits m : Nat) : Bool :=
  m < p && FastField.toNat
    (permute (Poseidon2Field.params24 : Params (FastField p) 24)
      (Hash.overwrite c.state (c.input.push (m : F)).toList))[15] % 2 ^ bits == 0

/-- The packed group of eight copies of the duplexed state. -/
abbrev baseGroup (c : Challenger F 24) : ByteArray :=
  CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (Array.ofFn (n := 192) fun k ↦ (Hash.overwrite c.state c.input.toList).toArray.getD (k / 8) 0)

theorem grindBatch_eq (c : Challenger F 24) (bits b : Nat) :
    grindBatch p (baseGroup c) (min c.input.size 24) bits b =
      firstFrom (passes c bits) 8 (8 * b) := by
  have h0 : (Array.ofFn (n := 192) fun k ↦
      (Hash.overwrite c.state c.input.toList).toArray.getD (k / 8) 0) =
      batchGroup (Hash.overwrite c.state c.input.toList) (min c.input.size 24) b 0 := by
    apply Array.ext
    · rw [Array.size_ofFn, size_batchGroup]
    · intro k h1 _
      simp only [batchGroup, Array.getElem_ofFn, Nat.not_lt_zero, and_false, ite_false]
  obtain ⟨W', e, hsz, hl⟩ := Merkle.Packed.permute24_lanes
    (batchGroup (Hash.overwrite c.state c.input.toList) (min c.input.size 24) b 8)
    (size_batchGroup _ _ _ _)
  have hs' : (encode W').size < USize.size := by
    rw [size_encode_fields, hsz]; have := USize.le_size; omega
  rw [grindBatch, baseGroup, Native.encodeFields_eq, copy_encode, h0,
    writes_encode _ _ _ (by omega) 8 (Nat.le_refl 8), e]
  refine find?_range_map _ _ 8 (8 * b) fun l hl8 ↦ ?_
  rw [word_encode _ _ hs' (by rw [hsz]; omega), passes]
  have h15 := hl l hl8
  rw [lane_batchGroup c b l hl8] at h15
  have hw : W'.getD (8 * 15 + l) 0 = (lane 24 W' 0 l)[15]'(by decide) := by
    simp only [lane, Vector.getElem_ofFn, Poseidon2.Packed.word, Nat.zero_add]
  rw [hw, h15]

theorem grindRange_eq (c : Challenger F 24) (bits : Nat) :
    ∀ nb b, grindRange p (baseGroup c) (min c.input.size 24) bits nb b =
      firstFrom (passes c bits) (8 * nb) (8 * b)
  | 0, _ => rfl
  | nb + 1, b => by
    rw [grindRange, grindBatch_eq c bits b, grindRange_eq c bits nb (b + 1),
      show 8 * (nb + 1) = 8 + 8 * nb by omega, firstFrom_add, show 8 * b + 8 = 8 * (b + 1) by omega]
    cases firstFrom (passes c bits) 8 (8 * b) <;> rfl

/-- The first find among consecutive ranges of `L` is the first of their union. -/
theorem findSome?_ranges (P : Nat → Bool) (L a : Nat) : ∀ n,
    ((List.range n).map fun k ↦ firstFrom P L (a + L * k)).findSome? id = firstFrom P (L * n) a
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.findSome?_append, findSome?_ranges P L a n,
      Nat.mul_succ, firstFrom_add]
    simp only [List.map_cons, List.map_nil, List.findSome?_cons, id, List.findSome?_nil]
    cases firstFrom P L (a + L * n) <;> rfl

theorem grindWaves_eq (c : Challenger F 24) (bits : Nat) :
    ∀ fuel wave, grindWaves p (baseGroup c) (min c.input.size 24) bits fuel wave =
      ((firstFrom (passes c bits) (8192 * fuel) (8192 * wave)).map fun m : Nat ↦ (m : F)).getD 0
  | 0, _ => rfl
  | fuel + 1, wave => by
    have hw : ((Array.range 16).map fun k ↦ Task.spawn fun _ ↦
        grindRange p (baseGroup c) (min c.input.size 24) bits 64 (1024 * wave + 64 * k)).map
          Task.get =
        ((List.range 16).map fun k ↦
          firstFrom (passes c bits) 512 (8192 * wave + 512 * k)).toArray := by
      rw [Array.map_map]
      apply Array.ext'
      simp only [Array.toList_map, Array.toList_range, grindRange_eq c bits, Nat.mul_add,
        ← Nat.mul_assoc]
      rfl
    rw [grindWaves, hw, List.findSome?_toArray, findSome?_ranges,
      show 8192 * (fuel + 1) = 512 * 16 + 8192 * fuel by omega, firstFrom_add,
      show 8192 * wave + 512 * 16 = 8192 * (wave + 1) by omega]
    cases firstFrom (passes c bits) (512 * 16) (8192 * wave) with
    | some m => rfl
    | none => rw [grindWaves_eq c bits fuel (wave + 1)]; rfl

/-- The fast grinder finds the specification's witness. -/
theorem grind_eq (c : Challenger F 24) (bits : Nat) :
    grind c bits = grindFrom Poseidon2.duplex c bits p 0 := by
  rw [grind]
  refine (grindWaves_eq c bits _ 0).trans ?_
  rw [grindFrom_eq, Nat.mul_zero]
  have hp : 8192 * (p / 8192 + 1) =
      p + (8192 * (p / 8192 + 1) -
        p) := by omega
  rw [hp, firstFrom_add, firstFrom_none (P := passes c bits)
    (8192 * (p / 8192 + 1) - p)
    (0 + p) fun m h1 _ ↦ by
    simp only [passes, show ¬ m < p by omega,
      decide_false, Bool.false_and]]
  rw [Option.or_none, firstFrom_congr
    (Q := fun m ↦ (Challenger.checkWitness Poseidon2.duplex c bits (m : F)).1) _ 0
    fun m _ h2 ↦ by
      rw [checkWitness_fst Poseidon2.duplex rfl c bits _, passes,
        decide_eq_true (show m < p by omega), Bool.true_and,
        show (Poseidon2.duplex : Duplex F 24).perm = _ from
          funext (@Poseidon2Field.perm24 (FastField p) _ _).perm_eq]
      rfl]

/-- The fast transcript is the specification's. -/
theorem transcript_eq : transcript (p := p) = Poseidon2.initTranscript := by
  rw [transcript, Poseidon2.initTranscript]
  congr 1
  funext c bits
  rw [grind_eq]
  rfl

end CompStark.Stark.Fast
