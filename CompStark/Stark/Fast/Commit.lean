/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Rel
public import CompStark.Merkle.RootCorrectness
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # The fast commitments are the specification's

Rows and digests read from encoded matrices and digest layers are the specification's reads, in
range and out of it (`readRow_rel`, `readDigest_encodeDigests`), so roots, openings and heights
agree (`root_rel`, `openAt_rel`, `maxHeight_rel`). The packed Merkle commitment of matrices of one
height side by side has the specification's digest layers (`packedLayers_eq`), so `commit_rel`
for matrices the prover commits to (`CommitOk`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields ofWord_val Native.encodeFields_eq)
open CompStark.Poseidon2 Montgomery.Native32

variable {p : ℕ} [Mont32Field p] [Mont32BaseField p]

local notation "F" => FastField p

omit [Mont32BaseField p] in
/-- A word past the end of a buffer reads zero. -/
theorem word_oob (b : ByteArray) (i : Nat) (hb : b.size < USize.size)
    (hu : 4 * i + 3 < USize.size) (hi : b.size ≤ 4 * i + 3) : word (p := p) b i = 0 := by
  open CompPoly.CPolynomial.NTTFast.Packed.Native in
  have hr : CompPoly.CPolynomial.NTTFast.Packed.Native.read b i = 0 := by
    have hiu : i.toUSize.toNat = i := USize.toNat_ofNat_of_lt' (by omega)
    have hz : (0 : USize).toNat = 0 := rfl
    have hsz : b.usize.toNat = b.size := by
      rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' hb]
    have h4 := usize_numeral 4 (by decide)
    unfold CompPoly.CPolynomial.NTTFast.Packed.Native.read
      CompPoly.CPolynomial.NTTFast.Packed.Native.readAt
    rw [dite_eq_right_iff]
    intro hc
    exfalso
    have h1 := hc.1
    have h2 := hc.2
    rw [USize.le_iff_toNat_le, hsz, h4] at h1
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ hc.1, hsz, h4,
      wordOffset_toNat _ _ (by rw [hiu, hz]; omega), hiu, hz] at h2
    omega
  rw [word, hr]
  exact ofWord_val (0 : F)

omit [Mont32BaseField p] in
/-- A word of an encoded array is its entry, or zero past its end. -/
theorem word_encode_getD (a : Array F) (i : Nat) (hs : 4 * a.size < USize.size)
    (hu : 4 * i + 3 < USize.size) : word (encode a) i = a.getD i 0 := by
  by_cases hi : i < a.size
  · rw [word, CompPoly.CPolynomial.NTTFast.Packed.Native.read_encode a i
      (by rw [size_encode_fields]; exact hs) hi, ofWord_val]
  · rw [word_oob _ _ (by rw [size_encode_fields]; exact hs) hu
      (by rw [size_encode_fields]; omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by omega), Option.getD_none]

open CompStark.Merkle.Packed (flat size_flat getD_flat)

omit [Mont32BaseField p] in
theorem encodeDigests_eq (ds : Array (Digest F)) : encodeDigests ds = encode (flat ds.toList) := by
  rw [encodeDigests, Native.encodeFields_eq]
  congr 1
  apply Array.toList_inj.mp
  simp only [flat, Array.toList_flatMap, List.toList_toArray]
  rfl

omit [Mont32BaseField p] in
theorem size_encodeDigests (ds : Array (Digest F)) : (encodeDigests ds).size = 32 * ds.size := by
  rw [encodeDigests_eq, size_encode_fields, size_flat, Array.length_toList]
  omega

omit [Mont32BaseField p] in
theorem encodeDigests_empty : encodeDigests (p := p) #[] = .empty := by
  rw [encodeDigests_eq]; rfl

omit [Mont32BaseField p] in
theorem extract_encode (V : Array F) (a b : Nat) :
    (encode V).extract (4 * a) (4 * b) = encode (V.extract a b) := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact CompPoly.PackedRepr.encode_extract V a b

omit [Mont32BaseField p] in
/-- An entry of a window of `w` entries is the array's entry, in range and out of it. -/
theorem extract_getD (V : Array F) (a w j : Nat) (hj : j < w) :
    (V.extract a (a + w)).getD j 0 = V.getD (a + j) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]

omit [Mont32BaseField p] in
/-- A digest read from encoded digests is the digest, or zero past the end. -/
theorem readDigest_encodeDigests (ds : Array (Digest F)) (k : Nat) :
    Commit.readDigest (p := p) (encodeDigests ds) k = ds.getD k 0 := by
  ext j hj
  rw [Commit.readDigest, Vector.getElem_ofFn]
  dsimp only
  have hs : 4 * ((flat ds.toList).extract (8 * k) (8 * k + 8)).size < USize.size := by
    have := USize.le_size
    rw [Array.size_extract]
    omega
  rw [encodeDigests_eq, show 32 * k = 4 * (8 * k) by omega,
    show 4 * (8 * k) + 32 = 4 * (8 * k + 8) by omega, extract_encode,
    word_encode_getD _ _ hs (by have := USize.le_size; omega), extract_getD _ _ _ _ hj, getD_flat,
    show (8 * k + j) / 8 = k by omega, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]
  exact CompStark.Merkle.Packed.vget_congr _ (by omega) _ _

/-- A row read from a packed matrix is the row of its matrix. -/
theorem readRow_rel {pm : PMat} {m : Mat F} (h : RM pm m) (r : Nat) :
    Commit.readRow (p := p) pm r = rowOf m r := by
  obtain ⟨hw, -, he⟩ := h
  rw [Commit.readRow, rowOf, he, hw, extract_encode, CompPoly.PackedRepr.decode_encode]
  apply Array.ext
  · simp only [Array.size_ofFn]
  · intro j h1 _
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    rw [Array.size_ofFn] at h1
    exact extract_getD _ _ _ _ h1

omit [Mont32BaseField p] in
theorem foldl_maxHeight {ms : List PMat} {ss : List (Mat F)} (h : List.Forall₂ RM ms ss)
    (a : Nat) : ms.foldl (fun m x ↦ max m x.height) a = ss.foldl (fun m x ↦ max m x.height) a := by
  induction h generalizing a with
  | nil => rfl
  | cons hr _ ih => rw [List.foldl_cons, List.foldl_cons, hr.2.1, ih]

omit [Mont32BaseField p] in
/-- Heights are the represented matrices'. -/
theorem maxHeight_rel {c : Commit} {s : Committed F} (h : RC c s) : c.maxHeight = s.maxHeight :=
  foldl_maxHeight h.1 0

omit [Mont32BaseField p] in
theorem layer_rel {c : Commit} {s : Committed F} (h : RC c s) (i : Nat) :
    c.layers.getD i .empty = encodeDigests (s.layers.getD i #[]) := by
  rw [h.2, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    ← encodeDigests_empty (p := p), Option.getD_map]

/-- The packed root is the specification's. -/
theorem root_rel {c : Commit} {s : Committed F} (h : RC c s) : Commit.root (p := p) c = s.root := by
  have hb : ∀ {α : Type} (xs : Array α) (d : α), xs.back?.getD d = xs.getD (xs.size - 1) d :=
    fun xs d ↦ by rw [Array.back?_eq_getElem?, Array.getD_eq_getD_getElem?]
  have hs : c.layers.size = s.layers.size := by rw [h.2, Array.size_map]
  rw [Commit.root, Committed.root, hb, hb, layer_rel h, hs, readDigest_encodeDigests]

theorem rows_rel (g : Nat → Nat) {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss) : ms.map
        (fun m ↦ Commit.readRow (p := p) m (g m.height)) = ss.map fun m ↦ rowOf m (g m.height)
        := by
  induction h with
  | nil => rfl
  | cons hm _ ih => rw [List.map_cons, List.map_cons, ih, readRow_rel hm, hm.2.1]

/-- The packed opening is the specification's. -/
theorem openAt_rel {c : Commit} {s : Committed F} (i : Nat) (h : RC c s) :
    Commit.openAt (p := p) c i = s.openAt i := by
  unfold Commit.openAt Committed.openAt
  dsimp only
  rw [maxHeight_rel h, rows_rel (fun n ↦ i >>> (Merkle.log2Ceil s.maxHeight - Merkle.log2Ceil n))
    h.1]
  congr 1
  apply Array.ext
  · simp only [Array.size_ofFn]
  · intro k _ _
    rw [Array.getElem_ofFn, Array.getElem_ofFn, layer_rel h, readDigest_encodeDigests]

/-! ### The digest layers -/

variable [Poseidon2Field (FastField p)]

local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

/-- The layers from `L` up, with no matrices to inject. -/
abbrev upper (fuel : Nat) (L : List (Digest F)) : List (List (Digest F)) :=
  Merkle.upperLayersAll hashF compF fuel [] L

omit [Mont32BaseField p] in
theorem upper_succ (fuel : Nat) (L : List (Digest F)) :
    upper (fuel + 1) L =
      if L.length ≤ 1 then [L] else L :: upper fuel (Merkle.nextLayer hashF compF [] L) := by
  simp only [upper, Merkle.upperLayersAll, List.takeWhile_nil, List.length_nil, List.drop_nil]

omit [Mont32BaseField p] in
theorem upper_eq_cons (fuel : Nat) (L : List (Digest F)) : upper fuel L = L ::
    (upper fuel L).tail := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [upper_succ]
    split <;> rfl

omit [Mont32BaseField p] in
theorem length_nextLayer (L : List (Digest F)) (h2 : 2 ≤ L.length) :
    (Merkle.nextLayer hashF compF [] L).length =
      if L.length = 2 then 1 else (L.length / 2 + 1) / 2 * 2 := by
  have := CompStark.Merkle.Packed.length_step L
  rw [CompStark.Merkle.Packed.step, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at this
  exact this

omit [Mont32BaseField p] in
theorem length_nextLayer_le (L : List (Digest F)) (k : Nat) (h2 : 2 ≤ L.length)
    (hk : L.length ≤ 2 ^ (k + 1)) :
    (Merkle.nextLayer hashF compF [] L).length ≤ 2 ^ k ∧
      (Merkle.nextLayer hashF compF [] L).length ≤ L.length := by
  rw [length_nextLayer L h2]
  have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have := Nat.one_le_two_pow (n := k)
  split
  · omega
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp only [Nat.zero_add, Nat.pow_one] at hk; omega
    · have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      omega

omit [Mont32BaseField p] in
/-- Fuel past `log₂` of the length adds no layers. -/
theorem upper_stable (k : Nat) : ∀
    (L : List (Digest F)), L.length ≤ 2 ^ k → ∀ a, k ≤ a → upper a L = upper k L := by
  induction k with
  | zero =>
    intro L hL a _
    cases a with
    | zero => rfl
    | succ a =>
      rw [upper_succ, ite_eq_left_of_eq_true _ _ (eq_true (by simpa only [Nat.pow_zero] using hL))]
      rfl
  | succ k ih =>
    intro L hL a ha
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [upper_succ, upper_succ]
    split
    · rfl
    · rw [ih _ (length_nextLayer_le L k (by omega) hL).1 a (by omega)]

omit [Mont32BaseField p] in
/-- The packed layer loop builds the specification's layers. -/
theorem upperPacked_encode [PackedPoseidon2 p] (fuel : Nat) : ∀ (L : List (Digest F))
    (out : Array ByteArray),
    32 * L.length < USize.size →
    upperPacked p (encode (flat L)) L.length out fuel =
      out ++ ((upper fuel L).tail.map fun l ↦ encode (flat l)).toArray := by
  induction fuel with
  | zero => intro L out _; exact Array.append_empty.symm
  | succ fuel ih =>
    intro L out hu
    rw [upperPacked, upper_succ]
    by_cases h1 : L.length ≤ 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact Array.append_empty.symm
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _
        (eq_false h1), CompStark.Merkle.Packed.nextLayer_encode L (by omega)]
      dsimp only
      have hl := (length_nextLayer_le L L.length (by omega)
        (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega)))).2
      rw [ih _ _ (by omega), List.tail_cons]
      conv_rhs => rw [upper_eq_cons fuel, List.map_cons]
      apply Array.toList_inj.mp
      simp only [Array.toList_append, Array.toList_push, List.append_assoc, List.singleton_append]

/-- Chunk `k` of `parts` chunks of `rows` rows of width `W` of `V`, the last taking the rest. -/
def chunk (V : Array F) (W parts rows k : Nat) : Array F :=
  V.extract (W * (k * rows)) (if k + 1 = parts then V.size else W * ((k + 1) * rows))

omit [Mont32BaseField p] [Poseidon2Field F] in
/-- The chunks of `packedLayers` cover the matrix. -/
theorem chunks_flatten (V : Array F) (W H parts rows : Nat) (hV : V.size = H * W)
    (hp : 0 < parts) (hpr : parts * rows ≤ H) :
    ((List.range parts).map (chunk V W parts rows)).toArray.flatten = V := by
  let e (k : Nat) : Nat := if k = parts then V.size else W * (k * rows)
  have he : ∀ k < parts, chunk V W parts rows k = V.extract (e k) (e (k + 1)) := by
    intro k hk
    simp only [chunk, e, ite_eq_right_of_eq_false _ _ (eq_false (show ¬k = parts by omega))]
  have hmono : ∀ k < parts, e k ≤ e (k + 1) ∧ e (k + 1) ≤ V.size := by
    intro k hk
    have h1 : W * (k * rows) ≤ W * ((k + 1) * rows) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    have h2 : W * ((k + 1) * rows) ≤ V.size := by
      rw [hV, Nat.mul_comm H]
      exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _ (by omega)).trans hpr)
    simp only [e, ite_eq_right_of_eq_false _ _ (eq_false (show ¬k = parts by omega))]
    split <;> omega
  have key : ∀ n ≤ parts,
      ((List.range n).map (chunk V W parts rows)).toArray.flatten = V.extract 0 (e n) := by
    intro n hn
    induction n with
    | zero =>
      simp only [e, ite_eq_right_of_eq_false _ _ (eq_false (show ¬0 = parts by omega)),
        Nat.zero_mul, Nat.mul_zero, List.range_zero, List.map_nil, Array.extract_zero]
      rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, ← List.append_toArray, Array.flatten_append,
        ih (by omega), List.map_singleton, he n (by omega)]
      have : (([V.extract (e n) (e (n + 1))] : List (Array F))).toArray.flatten =
          V.extract (e n) (e (n + 1)) := by
        apply Array.toList_inj.mp
        simp only [Array.toList_flatten, List.map_cons,
          List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [this, Array.extract_append_extract, Nat.zero_min,
        Nat.max_eq_right (hmono n (by omega)).1]
  rw [key parts le_rfl]
  simp only [e, ite_true, Array.extract_size]

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem size_chunk_mod (V : Array F) (W H parts rows k : Nat) (hV : V.size = H * W)
    (hk : k < parts) (hpr : parts * rows ≤ H) : (chunk V W parts rows k).size % W = 0 := by
  have h2 : W * ((k + 1) * rows) ≤ V.size := by
    rw [hV, Nat.mul_comm H]
    exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _ (by omega)).trans hpr)
  apply Nat.mod_eq_zero_of_dvd
  rw [chunk, Array.size_extract]
  apply Nat.dvd_sub
  · split
    · rw [Nat.min_self, hV]; exact Nat.dvd_mul_left _ _
    · rw [Nat.min_eq_left h2]; exact Nat.dvd_mul_right _ _
  · exact Nat.dvd_mul_right _ _

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem sum_div_mul (W : Nat) (cs : List (Array F)) (hc : ∀ c ∈ cs, c.size % W = 0) :
    (cs.map (·.size / W)).sum * W = (cs.map (·.size)).sum := by
  induction cs with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.zero_mul]
  | cons c cs ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, Nat.add_mul,
      ih fun c' h ↦ hc c' (List.mem_cons_of_mem c h),
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (hc c List.mem_cons_self))]

omit [Mont32BaseField p] in
/-- The packed digest layers of a matrix are the specification's layers above its padded leaf
digests. -/
theorem packedLayers_encode [PackedPoseidon2 p] (W H : Nat) (V : Array F) (hV : V.size = H * W)
    (hW : 0 < W)
    (hu : 32 * (H * W + 1) < USize.size) :
    packedLayers p W (encode V) = ((upper 64 (Merkle.padTo 0 (Merkle.padEven H)
      ((List.range H).map fun r ↦ hashF ((⟨W, H, V⟩ : Merkle.Matrix F).row r)))).map
        fun l ↦ encode (flat l)).toArray := by
  unfold packedLayers
  have hh : (if W = 0 then 0 else (encode V).size / (4 * W)) = H := by
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), size_encode_fields, hV,
      Nat.mul_comm H W, ← Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
  simp only [hh]
  generalize hp : (if H < 1024 then 1 else 16) = parts
  have hp0 : 0 < parts := by rw [← hp]; split <;> omega
  have hpr : parts * (H / parts) ≤ H := Nat.mul_div_le H parts
  generalize H / parts = rows at hpr
  let cs := (List.range parts).map (chunk V W parts rows)
  have hc : (Array.range parts).map (fun k ↦ (encode V).extract (4 * W * (k * rows))
      (if k + 1 = parts then (encode V).size else 4 * W * ((k + 1) * rows))) =
      cs.toArray.map encode := by
    apply Array.toList_inj.mp
    simp only [cs, Array.toList_map, Array.toList_range, List.map_toArray, List.toList_toArray,
      List.map_map]
    refine List.map_congr_left fun k _ ↦ ?_
    simp only [Function.comp_apply, chunk, size_encode_fields, Nat.mul_assoc]
    split <;> rw [extract_encode]
  have hmem : ∀ c ∈ cs, ∃ k < parts, c = chunk V W parts rows k := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    exact ⟨k, List.mem_range.mp hk, rfl⟩
  have hmod : ∀ c ∈ cs, c.size % W = 0 := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := hmem c hc
    exact size_chunk_mod V W H parts rows k hV hk hpr
  have hfl : cs.toArray.flatten = V := chunks_flatten V W H parts rows hV hp0 hpr
  have hsz : ∀ c ∈ cs, 32 * c.size < USize.size := by
    intro c hc
    have : c.size ≤ V.size := by
      have := Array.size_flatten (xss := cs.toArray)
      rw [hfl, List.map_toArray, List.sum_toArray] at this
      rw [this]
      exact List.le_sum_of_mem (List.mem_map_of_mem hc)
    rw [hV] at this
    omega
  have hsum : (cs.map (·.size / W)).sum = H := by
    have h1 := sum_div_mul W cs hmod
    have := Array.size_flatten (xss := cs.toArray)
    rw [hfl, List.map_toArray, List.sum_toArray, hV, ← h1] at this
    exact (Nat.eq_of_mul_eq_mul_right hW this).symm
  rw [hc, CompStark.Merkle.Packed.leaves_encode W hW cs hmod hsz,
    CompStark.Merkle.Packed.flatMap_chunkLeaves W cs hmod H, hsum, hfl]
  dsimp only
  generalize hL : List.map (fun r ↦ hashF ((⟨W, H, V⟩ : Merkle.Matrix F).row r)) (List.range H) = L
  have hLl : L.length = H := by rw [← hL, List.length_map, List.length_range]
  have e := CompStark.Merkle.Packed.padDigests_flat L (Merkle.padEven H)
  rw [hLl] at e
  have hPl : (Merkle.padTo 0 (Merkle.padEven H) L).length = Merkle.padEven H := by
    rw [Merkle.padTo, List.length_append, List.length_replicate, hLl, Merkle.padEven]
    split <;> omega
  have hpe : Merkle.padEven H ≤ H + 1 := by rw [Merkle.padEven]; split <;> omega
  change upperPacked p (Merkle.Packed.padDigests (encode (flat L)) H (Merkle.padEven H))
    (Merkle.padEven H) #[Merkle.Packed.padDigests (encode (flat L)) H (Merkle.padEven H)] 64 = _
  rw [e]
  generalize Merkle.padTo 0 (Merkle.padEven H) L = P at hPl
  have := Nat.le_mul_of_pos_right H hW
  rw [← hPl, upperPacked_encode 64 _ _ (by rw [hPl]; omega)]
  conv_rhs => rw [upper_eq_cons, List.map_cons]
  apply Array.toList_inj.mp
  simp only [Array.toList_append]
  rfl

/-! ### Rows side by side -/

/-- Row `r` of matrices side by side. -/
def rowcat (ss : List (Mat F)) (r : Nat) : List F := ss.flatMap fun s ↦ s.toMatrix.row r

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem length_row (m : Merkle.Matrix F) (r : Nat) : (m.row r).length = m.width := by
  rw [Merkle.Matrix.row, List.length_map, List.length_range]

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem length_rowcat (ss : List (Mat F)) (r : Nat) :
    (rowcat ss r).length = (ss.map Mat.width).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    rw [rowcat, List.flatMap_cons, List.length_append, ← rowcat, ih, length_row, List.map_cons,
      List.sum_cons]
    rfl

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem toList_extract_eq (a : Array F) (i c : Nat) (h : i + c ≤ a.size) :
    (a.extract i (i + c)).toList = (List.range c).map fun j ↦ a.getD (i + j) 0 := by
  apply List.ext_getElem
  · simp only [Array.length_toList, Array.size_extract, List.length_map, List.length_range]
    omega
  · intro j h1 h2
    simp only [Array.getElem_toList, Array.getElem_extract, List.getElem_map, List.getElem_range,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show i + j < a.size by
        simp only [Array.length_toList, Array.size_extract] at h1; omega), Option.getD_some]

omit [Poseidon2Field F] in
omit [Mont32BaseField p] in
/-- Copying a range of a packed array over the zeros after a prefix. -/
theorem copySlice_mid (a P : Array F) (z i c : Nat) (hc : i + c ≤ a.size) :
    (encode a).copySlice (4 * i) (encode (P ++ Array.replicate z 0)) (4 * P.size) (4 * c) =
      encode (P ++ a.extract i (i + c) ++ Array.replicate (z - c) 0) := by
  have hs : (encode (P ++ Array.replicate z (0 : F))).data.size =
      4 * (P ++ Array.replicate z (0 : F)).size := size_encode_fields _
  have ha : (encode a).data.size = 4 * a.size := size_encode_fields _
  rw [ByteArray.copySlice_eq_append, hs, ha,
    show 4 * P.size + min (4 * c) (4 * a.size - 4 * i) = 4 * (P.size + c) by
      rw [Nat.min_eq_left (by omega)]; omega,
    show (0 : Nat) = 4 * 0 from rfl, show 4 * i + 4 * c = 4 * (i + c) by omega,
    extract_encode, extract_encode, extract_encode, ← CompPoly.PackedRepr.encode_append,
    ← CompPoly.PackedRepr.encode_append]
  congr 1
  rw [Array.extract_append, Array.extract_append]
  simp only [Array.extract_size, Nat.zero_sub, Nat.sub_self, Array.extract_zero,
    Array.append_empty, Array.size_append, Array.size_replicate, Nat.add_sub_cancel_left,
    Array.extract_replicate, Nat.min_self, Array.append_assoc,
    Array.extract_empty_of_size_le_start (show P.size ≤ P.size + c by omega), Array.empty_append]

theorem foldl_width (ms : List PMat) (a : Nat) :
    ms.foldl (fun x m ↦ x + m.width) a = a + (ms.map PMat.width).sum := by
  induction ms generalizing a with
  | nil => rfl
  | cons m ms ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem sum_width {ms : List PMat} {ss : List (Mat F)} (h : List.Forall₂ RM ms ss) :
    (ms.map PMat.width).sum = (ss.map Mat.width).sum := by
  induction h with
  | nil => rfl
  | cons hm _ ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, hm.1]

omit [Poseidon2Field F] in
omit [Mont32BaseField p] in
/-- One row of the copies of `sideBySide`. -/
theorem foldl_row (H r : Nat) (hr : r < H) {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss)
    (hf : ∀ s ∈ ss, s.values.size = s.width * s.height ∧ s.height = H) (P : Array F) (z : Nat) :
    ms.foldl (fun b m ↦ (m.words.copySlice (4 * r * m.width) b.1 (4 * b.2)
        (4 * m.width), b.2 + m.width)) (encode (P ++ Array.replicate z 0), P.size) =
      (encode (P ++ (rowcat ss r).toArray ++ Array.replicate (z - (ss.map Mat.width).sum) 0),
        P.size + (ss.map Mat.width).sum) := by
  induction h generalizing P z with
  | nil =>
    simp only [List.foldl_nil, rowcat, List.flatMap_nil, List.map_nil, List.sum_nil,
      Nat.sub_zero, Nat.add_zero]
    rfl
  | @cons pm s ms ss hm _ ih =>
    rw [List.foldl_cons]
    obtain ⟨hv, hhm⟩ := hf s List.mem_cons_self
    have hle : r * s.width + s.width ≤ s.values.size := by
      rw [hv, hhm, Nat.mul_comm s.width H]
      have := Nat.mul_le_mul_right s.width (show r + 1 ≤ H by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have e := ih (fun m h ↦ hf m (List.mem_cons_of_mem s h)) (P ++ s.values.extract
      (r * s.width) (r * s.width + s.width)) (z - s.width)
    rw [Array.size_append, Array.size_extract,
      Nat.min_eq_left hle, Nat.add_sub_cancel_left] at e
    rw [hm.1, hm.2.2, Nat.mul_assoc, copySlice_mid _ _ _ _ _ hle]
    rw [e]
    have hrow : s.toMatrix.row r =
        (s.values.extract (r * s.width) (r * s.width + s.width)).toList :=
      (toList_extract_eq _ _ _ hle).symm
    have hc : rowcat (s :: ss) r = s.toMatrix.row r ++ rowcat ss r := List.flatMap_cons
    simp only [hc, List.map_cons, List.sum_cons, hrow, Nat.sub_sub, Nat.add_assoc]
    congr 2
    apply Array.toList_inj.mp
    simp only [Array.toList_append, List.append_assoc]

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem length_flatMap_range (f : Nat → List F) (W : Nat) (hf : ∀ i, (f i).length = W) (n : Nat) :
    ((List.range n).flatMap f).length = n * W := by
  induction n with
  | zero => simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hf,
      Nat.succ_mul]

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem getD_flatMap_range (f : Nat → List F) (W : Nat) (hf : ∀ i, (f i).length = W) (n r j : Nat)
    (hr : r < n) (hj : j < W) : ((List.range n).flatMap f).getD (r * W + j) 0 = (f r).getD j 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hl := length_flatMap_range f W hf n
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.getD_eq_getElem?_getD,
      List.getElem?_append]
    by_cases hrn : r < n
    · have : r * W + j < n * W := by
        have := Nat.mul_le_mul_right W (show r + 1 ≤ n by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      rw [hl, ite_eq_left_of_eq_true _ _ (eq_true this), ← List.getD_eq_getElem?_getD,
        ih hrn]
    · obtain rfl : r = n := by omega
      rw [hl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left,
        ← List.getD_eq_getElem?_getD]

omit [Poseidon2Field F] in
omit [Mont32BaseField p] in
/-- Matrices of one height side by side are the packed matrix of their rows side by side. -/
theorem sideBySide_eq (H : Nat) {ms : List PMat} {ss : List (Mat F)} (h : List.Forall₂ RM ms ss)
    (hf : ∀ s ∈ ss, s.values.size = s.width * s.height ∧ s.height = H) :
    ∃ V, sideBySide ms H = encode V ∧ V.size = H * (ss.map Mat.width).sum ∧
      ∀ r < H, (⟨(ss.map Mat.width).sum, H, V⟩ : Merkle.Matrix F).row r = rowcat ss r := by
  unfold sideBySide
  split
  · rename_i m
    obtain ⟨s, rfl⟩ : ∃ s, ss = [s] := by
      cases h with
      | cons hm h' => cases h'; exact ⟨_, rfl⟩
    have hm : RM m s := by cases h; assumption
    obtain ⟨hv, hhm⟩ := hf s List.mem_cons_self
    refine ⟨s.values, hm.2.2, ?_, fun r _ ↦ ?_⟩
    · rw [hv, hhm]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Nat.mul_comm]
    · simp only [rowcat, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rfl
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, bind_pure, pure_bind, Nat.sub_zero,
      Nat.add_sub_cancel,
      Nat.div_one, ← List.range_eq_range', foldl_width, Nat.zero_add, sum_width h,
      CompStark.Merkle.Packed.zeroWords_fields (p := p)]
    generalize hW : (ss.map Mat.width).sum = W
    have hrow : ∀ i, (rowcat ss i).length = W := fun i ↦ by rw [length_rowcat, hW]
    have key : ∀ n ≤ H, (List.range n).foldl (fun b a ↦ (ms.foldl (fun b m ↦
        (m.words.copySlice (4 * a * m.width) b.1 (4 * b.2) (4 * m.width), b.2 + m.width))
          (b, a * W)).1) (encode (Array.replicate (H * W) (0 : F))) =
        encode (((List.range n).flatMap (rowcat ss)).toArray ++
          Array.replicate ((H - n) * W) 0) := by
      intro n hn
      induction n with
      | zero =>
        simp only [List.range_zero, List.foldl_nil, List.flatMap_nil, Nat.sub_zero]
        exact congrArg encode Array.empty_append.symm
      | succ n ih =>
        rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
        have hs : (((List.range n).flatMap (rowcat ss)).toArray).size = n * W := by
          rw [List.size_toArray, length_flatMap_range _ W hrow]
        rw [← hs, foldl_row H n (by omega) h hf, hW]
        dsimp only
        congr 1
        apply Array.toList_inj.mp
        simp only [Array.toList_append, List.flatMap_append, List.flatMap_singleton,
          List.append_assoc, Array.toList_replicate]
        congr 3
        rw [Nat.sub_mul, Nat.sub_mul, Nat.succ_mul, Nat.sub_sub]
    refine ⟨((List.range H).flatMap (rowcat ss)).toArray, by
      rw [key H le_rfl, Nat.sub_self, Nat.zero_mul, Array.replicate_zero, Array.append_empty],
      ?_, fun r hr ↦ ?_⟩
    · rw [List.size_toArray, length_flatMap_range _ W hrow]
    · apply List.ext_getElem
      · rw [length_row, hrow]
      · intro j h1 h2
        rw [length_row] at h1
        simp only [Merkle.Matrix.row, List.getElem_map, List.getElem_range,
          Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
          getD_flatMap_range _ W hrow H r j hr h1, List.getD_eq_getElem _ _ h2]

/-! ### Commitments -/

theorem takeWhile_all {α : Type*} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x) :
    l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.takeWhile_cons, ite_eq_left_of_eq_true _ _ (eq_true (h x List.mem_cons_self)),
      ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)]

omit [Mont32BaseField p] in
/-- The specification's layers of matrices of one height. -/
theorem layers_eq (H : Nat) (ss : List (Mat F)) (hne : ss ≠ [])
    (hH : ∀ s ∈ ss, s.height = H) : Merkle.layers hashF compF (ss.map Mat.toMatrix) =
      upper (Merkle.firstLayer hashF (ss.map Mat.toMatrix) H).length
        (Merkle.firstLayer hashF (ss.map Mat.toMatrix) H) := by
  have hall : ∀ x ∈ ss.map Mat.toMatrix, x.height = H := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact hH s hs
  have hsort : Merkle.sortTallest (ss.map Mat.toMatrix) = ss.map Mat.toMatrix :=
    List.mergeSort_of_pairwise (List.pairwise_of_forall_mem_list fun a ha b hb ↦ by
      rw [hall a ha, hall b hb]; exact decide_eq_true (Nat.le_refl H))
  obtain ⟨s, ss', rfl⟩ : ∃ s ss', ss = s :: ss' := by
    cases ss with
    | nil => exact absurd rfl hne
    | cons s ss' => exact ⟨s, ss', rfl⟩
  unfold Merkle.layers
  rw [hsort]
  simp only [List.map_cons, List.headD_cons]
  have hs : s.toMatrix.height = H := hH s List.mem_cons_self
  have htw : (s.toMatrix :: ss'.map Mat.toMatrix).takeWhile (fun x ↦ x.height == H) =
      s.toMatrix :: ss'.map Mat.toMatrix :=
    takeWhile_all _ _ fun x hx ↦ by
      rw [← List.map_cons] at hx; rw [hall x hx]; exact beq_self_eq_true H
  rw [hs, htw, List.drop_length]

omit [Poseidon2Field F] in
omit [Mont32BaseField p] in
theorem map_encodeDigests (L : List (List (Digest F))) :
    ((L.map List.toArray).toArray).map encodeDigests = (L.map fun l ↦ encode (flat l)).toArray := by
  rw [List.map_toArray, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ ↦ ?_
  rw [Function.comp_apply, encodeDigests_eq, List.toList_toArray]

/-- The packed commitment of matrices of one height has the specification's layers. -/
theorem packedLayers_eq [PackedPoseidon2 p] (H : Nat) {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss)
    (hne : ms ≠ []) (hf : ∀ s ∈ ss, s.values.size = s.width * s.height ∧ s.height = H)
    (hW : 0 < (ss.map Mat.width).sum)
    (hu : 32 * (H * (ss.map Mat.width).sum + 1) < USize.size) :
    packedLayers p (ss.map Mat.width).sum (sideBySide ms H) =
      (Committed.ofMats hashF compF ss).layers.map encodeDigests := by
  obtain ⟨V, e, hV, hrow⟩ := sideBySide_eq H h hf
  have hss : ss ≠ [] := by rintro rfl; cases h; exact hne rfl
  have hH : ∀ s ∈ ss, s.height = H := fun s hs ↦ (hf s hs).2
  rw [e, packedLayers_encode _ H V hV hW hu, Committed.ofMats, layers_eq H ss hss hH,
    map_encodeDigests]
  have hfirst : Merkle.firstLayer hashF (ss.map Mat.toMatrix) H =
      Merkle.padTo 0 (Merkle.padEven H) ((List.range H).map fun r ↦
        hashF ((⟨(ss.map Mat.width).sum, H, V⟩ : Merkle.Matrix F).row r)) := by
    rw [Merkle.firstLayer]
    congr 1
    refine List.map_congr_left fun r hr ↦ ?_
    rw [hrow r (List.mem_range.mp hr), rowcat, List.flatMap_map]
  rw [hfirst]
  generalize hL : (List.range H).map (fun r ↦
    hashF ((⟨(ss.map Mat.width).sum, H, V⟩ : Merkle.Matrix F).row r)) = L
  have hPl : (Merkle.padTo 0 (Merkle.padEven H) L).length ≤ H + 1 := by
    rw [Merkle.padTo, List.length_append, List.length_replicate, ← hL, List.length_map,
      List.length_range, Merkle.padEven]
    split <;> omega
  generalize Merkle.padTo 0 (Merkle.padEven H) L = P at hPl
  have h64 : P.length ≤ 2 ^ 64 := by
    have := Nat.le_mul_of_pos_right H hW
    rcases USize.size_eq with hs | hs <;> rw [hs] at hu <;> omega
  rw [← upper_stable 64 P h64 (64 + P.length) (by omega),
    ← upper_stable P.length P Nat.lt_two_pow_self.le (64 + P.length) (by omega)]

omit [Mont32BaseField p] [Poseidon2Field F] in
theorem foldl_width_mat (ss : List (Mat F)) (a : Nat) :
    ss.foldl (fun x m ↦ x + m.width) a = a + (ss.map Mat.width).sum := by
  induction ss generalizing a with
  | nil => rfl
  | cons m ss ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

/-- The fast commitment represents the specification's. -/
theorem commit_rel [PackedPoseidon2 p] {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss)
    (hok : CommitOk ss) : RC (commit p ms) (Committed.ofMats hashF compF ss) := by
  obtain ⟨H, hne, hall, hu⟩ := hok
  refine ⟨h, ?_⟩
  cases h with
  | nil => exact absurd rfl hne
  | @cons m s rest ss' hm hr =>
    have hf : ∀ x ∈ s :: ss', x.values.size = x.width * x.height ∧ x.height = H :=
      fun x hx ↦ ⟨(hall x hx).1.2.2.1, (hall x hx).2⟩
    have hW : 0 < ((s :: ss').map Mat.width).sum := by
      rw [List.map_cons, List.sum_cons]
      have := (hall s List.mem_cons_self).1.1
      omega
    rw [Addressable, foldl_width_mat, Nat.zero_add] at hu
    have hmH : m.height = H := by rw [hm.2.1]; exact (hall s List.mem_cons_self).2
    unfold commit
    dsimp only
    rw [foldl_width, Nat.zero_add, sum_width (List.Forall₂.cons hm hr), hmH]
    exact packedLayers_eq H (List.Forall₂.cons hm hr) (List.cons_ne_nil _ _) hf hW hu

end CompStark.Stark.Fast
