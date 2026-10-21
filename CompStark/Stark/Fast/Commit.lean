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
agree (`root_rel`, `openAt_rel`, `maxHeight_rel`). The packed Merkle commitment has the
specification's digest layers (`commitLayers_eq`), so `commit_rel` for matrices the prover commits
to (`CommitOk`), of mixed heights: the leaf layer of matrices side by side is the specification's
(`leafLayer_encode`), and so is every layer above, where the matrices of the layer's height are
injected by compressing the layer interleaved with their leaf digests (`nextLayer_inject`,
`injectLayer_encode`, `upperMixed_encode`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields ofWord_val Native.encodeFields_eq)
open CompStark.Poseidon2 Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

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

theorem encodeDigests_eq (ds : Array (Digest F)) : encodeDigests ds = encode (flat ds.toList) := by
  rw [encodeDigests, Native.encodeFields_eq]
  congr 1
  apply Array.toList_inj.mp
  simp only [flat, Array.toList_flatMap, List.toList_toArray]
  rfl

theorem size_encodeDigests (ds : Array (Digest F)) : (encodeDigests ds).size = 32 * ds.size := by
  rw [encodeDigests_eq, size_encode_fields, size_flat, Array.length_toList]
  omega

theorem encodeDigests_empty : encodeDigests (p := p) #[] = .empty := by
  rw [encodeDigests_eq]; rfl

theorem extract_encode (V : Array F) (a b : Nat) :
    (encode V).extract (4 * a) (4 * b) = encode (V.extract a b) := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact CompPoly.PackedRepr.encode_extract V a b

/-- An entry of a window of `w` entries is the array's entry, in range and out of it. -/
theorem extract_getD (V : Array F) (a w j : Nat) (hj : j < w) :
    (V.extract a (a + w)).getD j 0 = V.getD (a + j) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]

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

theorem map_encodeDigests (L : List (List (Digest F))) :
    ((L.map List.toArray).toArray).map encodeDigests = (L.map fun l ↦ encode (flat l)).toArray := by
  rw [List.map_toArray, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ ↦ ?_
  rw [Function.comp_apply, encodeDigests_eq, List.toList_toArray]

/-- A row read from a packed matrix is the row of its matrix. -/
theorem readRow_rel [Mont32BaseField p] {pm : PMat} {m : Mat F} (h : RM pm m) (r : Nat) :
    Commit.readRow (p := p) pm r = rowOf m r := by
  obtain ⟨hw, -, he⟩ := h
  rw [Commit.readRow, rowOf, he, hw, extract_encode, CompPoly.PackedRepr.decode_encode]
  apply Array.ext
  · simp only [Array.size_ofFn]
  · intro j h1 _
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    rw [Array.size_ofFn] at h1
    exact extract_getD _ _ _ _ h1

theorem foldl_maxHeight {ms : List PMat} {ss : List (Mat F)} (h : List.Forall₂ RM ms ss)
    (a : Nat) : ms.foldl (fun m x ↦ max m x.height) a = ss.foldl (fun m x ↦ max m x.height) a := by
  induction h generalizing a with
  | nil => rfl
  | cons hr _ ih => rw [List.foldl_cons, List.foldl_cons, hr.2.1, ih]

/-- Heights are the represented matrices'. -/
theorem maxHeight_rel {c : Commit} {s : Committed F} (h : RC c s) : c.maxHeight = s.maxHeight :=
  foldl_maxHeight h.1 0

theorem layer_rel {c : Commit} {s : Committed F} (h : RC c s) (i : Nat) :
    c.layers.getD i .empty = encodeDigests (s.layers.getD i #[]) := by
  rw [h.2, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    ← encodeDigests_empty (p := p), Option.getD_map]

/-- The packed root is the specification's. -/
theorem root_rel [Mont32BaseField p] {c : Commit} {s : Committed F} (h : RC c s) :
    Commit.root (p := p) c = s.root := by
  have hb : ∀ {α : Type} (xs : Array α) (d : α), xs.back?.getD d = xs.getD (xs.size - 1) d :=
    fun xs d ↦ by rw [Array.back?_eq_getElem?, Array.getD_eq_getD_getElem?]
  have hs : c.layers.size = s.layers.size := by rw [h.2, Array.size_map]
  rw [Commit.root, Committed.root, hb, hb, layer_rel h, hs, readDigest_encodeDigests]

theorem rows_rel [Mont32BaseField p] (g : Nat → Nat) {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss) : ms.map
        (fun m ↦ Commit.readRow (p := p) m (g m.height)) = ss.map fun m ↦ rowOf m (g m.height)
        := by
  induction h with
  | nil => rfl
  | cons hm _ ih => rw [List.map_cons, List.map_cons, ih, readRow_rel hm, hm.2.1]

/-- The packed opening is the specification's. -/
theorem openAt_rel [Mont32BaseField p] {c : Commit} {s : Committed F} (i : Nat) (h : RC c s) :
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

/-! ### Chunks -/

/-- Chunk `k` of `parts` chunks of `rows` rows of width `W` of `V`, the last taking the rest. -/
def chunk (V : Array F) (W parts rows k : Nat) : Array F :=
  V.extract (W * (k * rows)) (if k + 1 = parts then V.size else W * ((k + 1) * rows))

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

theorem sum_div_mul (W : Nat) (cs : List (Array F)) (hc : ∀ c ∈ cs, c.size % W = 0) :
    (cs.map (·.size / W)).sum * W = (cs.map (·.size)).sum := by
  induction cs with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.zero_mul]
  | cons c cs ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, Nat.add_mul,
      ih fun c' h ↦ hc c' (List.mem_cons_of_mem c h),
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (hc c List.mem_cons_self))]

/-! ### Rows side by side -/

/-- Row `r` of matrices side by side. -/
def rowcat (ss : List (Mat F)) (r : Nat) : List F := ss.flatMap fun s ↦ s.toMatrix.row r

theorem length_row (m : Merkle.Matrix F) (r : Nat) : (m.row r).length = m.width := by
  rw [Merkle.Matrix.row, List.length_map, List.length_range]

theorem length_rowcat (ss : List (Mat F)) (r : Nat) :
    (rowcat ss r).length = (ss.map Mat.width).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    rw [rowcat, List.flatMap_cons, List.length_append, ← rowcat, ih, length_row, List.map_cons,
      List.sum_cons]
    rfl

theorem toList_extract_eq (a : Array F) (i c : Nat) (h : i + c ≤ a.size) :
    (a.extract i (i + c)).toList = (List.range c).map fun j ↦ a.getD (i + j) 0 := by
  apply List.ext_getElem
  · simp only [Array.length_toList, Array.size_extract, List.length_map, List.length_range]
    omega
  · intro j h1 h2
    simp only [Array.getElem_toList, Array.getElem_extract, List.getElem_map, List.getElem_range,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show i + j < a.size by
        simp only [Array.length_toList, Array.size_extract] at h1; omega), Option.getD_some]

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

theorem foldl_width_mat (ss : List (Mat F)) (a : Nat) :
    ss.foldl (fun x m ↦ x + m.width) a = a + (ss.map Mat.width).sum := by
  induction ss generalizing a with
  | nil => rfl
  | cons m ss ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem sum_width {ms : List PMat} {ss : List (Mat F)} (h : List.Forall₂ RM ms ss) :
    (ms.map PMat.width).sum = (ss.map Mat.width).sum := by
  induction h with
  | nil => rfl
  | cons hm _ ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, hm.1]

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

theorem length_flatMap_range (f : Nat → List F) (W : Nat) (hf : ∀ i, (f i).length = W) (n : Nat) :
    ((List.range n).flatMap f).length = n * W := by
  induction n with
  | zero => simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hf,
      Nat.succ_mul]

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

theorem takeWhile_all {α : Type*} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x) :
    l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.takeWhile_cons, ite_eq_left_of_eq_true _ _ (eq_true (h x List.mem_cons_self)),
      ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)]

/-! ### Lists -/

/-- Two layers' digests alternating. -/
def interleave (a b : List (Digest F)) : List (Digest F) := (a.zip b).flatMap fun x ↦ [x.1, x.2]

theorem length_interleave : ∀ (a b : List (Digest F)),
    (interleave a b).length = 2 * min a.length b.length
  | [], _ => by simp only [interleave, List.zip_nil_left, List.flatMap_nil, List.length_nil,
      Nat.zero_min, Nat.mul_zero]
  | _ :: _, [] => by simp only [interleave, List.zip_nil_right, List.flatMap_nil,
      List.length_nil, Nat.min_zero, Nat.mul_zero]
  | x :: a, y :: b => by
    have := length_interleave a b
    simp only [interleave, List.zip_cons_cons, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at this ⊢
    rw [this]
    omega

theorem getD_interleave : ∀ (a b : List (Digest F)) (i : Nat), i < a.length → i < b.length →
    (interleave a b).getD (2 * i) 0 = a.getD i 0 ∧ (interleave a b).getD (2 * i + 1) 0 = b.getD i 0
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: a, y :: b, 0, _, _ => ⟨rfl, rfl⟩
  | x :: a, y :: b, i + 1, ha, hb => by
    have := getD_interleave a b i (by simp only [List.length_cons] at ha; omega)
      (by simp only [List.length_cons] at hb; omega)
    simp only [interleave, List.zip_cons_cons, List.flatMap_cons] at this ⊢
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by omega]
    simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
    exact this

theorem forall₂_takeWhile {α β : Type*} {R : α → β → Prop} {P : α → Bool} {Q : β → Bool}
    (hPQ : ∀ a b, R a b → P a = Q b) :
    ∀ {xs ys}, List.Forall₂ R xs ys → List.Forall₂ R (xs.takeWhile P) (ys.takeWhile Q)
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons h hs => by
    simp only [List.takeWhile_cons, hPQ a b h]
    split
    · exact .cons h (forall₂_takeWhile hPQ hs)
    · exact .nil

theorem takeWhile_congr {α : Type*} {P Q : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, P x = Q x) → xs.takeWhile P = xs.takeWhile Q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.takeWhile_cons, h x List.mem_cons_self,
      takeWhile_congr fun y hy ↦ h y (List.mem_cons_of_mem x hy)]

theorem isPowerOfTwo_two_pow : ∀ k, (2 ^ k).isPowerOfTwo
  | 0 => Nat.isPowerOfTwo_one
  | k + 1 => by
    rw [Nat.pow_succ]; exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo (isPowerOfTwo_two_pow k)

theorem mem_takeWhile {α : Type*} {P : α → Bool} :
    ∀ {l : List α} {x : α}, x ∈ l.takeWhile P → x ∈ l ∧ P x = true
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, x, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · rename_i hy
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨List.mem_cons_self, hy⟩
      · obtain ⟨h1, h2⟩ := mem_takeWhile h
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · exact absurd h List.not_mem_nil

theorem sum_takeWhile_le (P : Mat F → Bool) (l : List (Mat F)) :
    ((l.takeWhile P).map Mat.width).sum ≤ (l.map Mat.width).sum := by
  conv_rhs => rw [← List.takeWhile_append_dropWhile (p := P) (l := l)]
  rw [List.map_append, List.sum_append]
  omega

theorem sum_drop_le (k : Nat) (l : List (Mat F)) :
    ((l.drop k).map Mat.width).sum ≤ (l.map Mat.width).sum := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [List.map_append, List.sum_append]
  omega

theorem forall₂_mergeSort_height {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss) :
    List.Forall₂ RM (ms.mergeSort fun a b ↦ b.height ≤ a.height)
      (ss.mergeSort fun a b ↦ b.height ≤ a.height) := by
  have hl := h.length_eq
  have hms : ms = (ms.zip ss).map Prod.fst := (List.map_fst_zip hl.le).symm
  have hss : ss = (ms.zip ss).map Prod.snd := (List.map_snd_zip hl.ge).symm
  have hR : ∀ x ∈ ms.zip ss, RM x.1 x.2 := by
    intro x hx
    rw [List.forall₂_iff_zip] at h
    exact h.2 hx
  have e1 := List.map_mergeSort (l := ms.zip ss) (f := Prod.fst)
    (r := fun a b ↦ decide (b.2.height ≤ a.2.height)) (s := fun a b ↦ decide (b.height ≤ a.height))
    fun a ha b hb ↦ by rw [(hR a ha).2.1, (hR b hb).2.1]
  have e2 := List.map_mergeSort (l := ms.zip ss) (f := Prod.snd)
    (r := fun a b ↦ decide (b.2.height ≤ a.2.height)) (s := fun a b ↦ decide (b.height ≤ a.height))
    fun _ _ _ _ ↦ rfl
  rw [← hms] at e1
  rw [← hss] at e2
  rw [← e1, ← e2, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun x hx ↦ hR x ((List.mem_mergeSort).mp hx)

/-- Two packed layers of `n` digests side by side are the layers interleaved. -/
theorem sideBySide_interleave (a b : List (Digest F)) (n : Nat) (ha : a.length = n)
    (hb : b.length = n) :
    sideBySide [⟨8, n, encode (flat a)⟩, ⟨8, n, encode (flat b)⟩] n =
      encode (flat (interleave a b)) := by
  have hfa : (flat a).size = 8 * n := by rw [size_flat, ha]
  have hfb : (flat b).size = 8 * n := by rw [size_flat, hb]
  obtain ⟨V, e, hV, hrow⟩ := sideBySide_eq
    (ms := [⟨8, n, encode (flat a)⟩, ⟨8, n, encode (flat b)⟩])
    (ss := [⟨8, n, flat a⟩, ⟨8, n, flat b⟩]) n
    (.cons ⟨rfl, rfl, rfl⟩ (.cons ⟨rfl, rfl, rfl⟩ .nil)) (by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact ⟨by rw [hfa], rfl⟩
      · exact ⟨by rw [hfb], rfl⟩)
  rw [e]
  congr 1
  have hw : ([⟨8, n, flat a⟩, ⟨8, n, flat b⟩] : List (Mat F)).map Mat.width = [8, 8] := rfl
  simp only [hw, List.sum_cons, List.sum_nil] at hV hrow
  have hVs : V.size = 8 * (interleave a b).length := by
    rw [hV, length_interleave, ha, hb, Nat.min_self]; omega
  refine CompStark.Merkle.Packed.flat_eq V _ hVs fun i hi j hj ↦ ?_
  rw [length_interleave, ha, hb, Nat.min_self] at hi
  have hr := hrow (i / 2) (by omega)
  have hrj := congrArg (fun l ↦ l.getD (8 * (i % 2) + j) 0) hr
  simp only [Merkle.Matrix.row, rowcat, Mat.toMatrix, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hrj
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range] at hrj
  have hk : i / 2 * (8 + (8 + 0)) + (8 * (i % 2) + j) = 8 * i + j := by omega
  rw [hk] at hrj
  rw [hrj]
  have hga := getD_interleave a b (i / 2) (by omega) (by omega)
  rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
  · have hi2 : i = 2 * (i / 2) := by omega
    rw [h0, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by
      rw [List.length_map, List.length_range]; omega), List.getD_eq_getElem _ _ (by
      rw [List.length_map, List.length_range]; omega), List.getElem_map, List.getElem_range,
      CompStark.Merkle.Packed.getD_flat]
    conv_rhs => rw [hi2, hga.1]
    congr 2 <;> omega
  · have hi2 : i = 2 * (i / 2) + 1 := by omega
    have h8 : ((List.range 8).map fun j ↦ (flat a).getD (i / 2 * 8 + j) 0).length ≤ 8 + j := by
      rw [List.length_map, List.length_range]; omega
    rw [h1, Nat.mul_one, List.getD_append_right _ _ _ _ h8, List.length_map, List.length_range,
      Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by
      rw [List.length_map, List.length_range]; omega), List.getElem_map, List.getElem_range,
      CompStark.Merkle.Packed.getD_flat]
    conv_rhs => rw [hi2, hga.2]
    congr 2 <;> omega

/-! ### The digest layers -/

variable [Poseidon2Field (FastField p)]

local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

theorem length_nextLayer (L : List (Digest F)) (h2 : 2 ≤ L.length) :
    (Merkle.nextLayer hashF compF [] L).length =
      if L.length = 2 then 1 else (L.length / 2 + 1) / 2 * 2 := by
  have := CompStark.Merkle.Packed.length_step L
  rw [CompStark.Merkle.Packed.step, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at this
  exact this

/-- The next layer of `2 ^ (k + 1)` digests has `2 ^ k`. -/
theorem length_nextLayer_pow (L : List (Digest F)) (k : Nat) (h : L.length = 2 ^ (k + 1)) :
    (Merkle.nextLayer hashF compF [] L).length = 2 ^ k := by
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [length_nextLayer L (by rw [h, h2]; have := Nat.one_le_two_pow (n := k); omega), h, h2]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := Nat.one_le_two_pow (n := k); omega))]
    omega

/-! ### The leaf layer -/

/-- The packed leaf layer of a matrix is the specification's leaf digests, padded. -/
theorem leafLayer_encode [PackedPoseidon2 p] (W H : Nat) (V : Array F) (hV : V.size = H * W)
    (hW : 0 < W) (hu : 32 * (H * W + 1) < USize.size) :
    leafLayer p W (encode V) = (encode (flat (Merkle.padTo 0 (Merkle.padEven H)
      ((List.range H).map fun r ↦ hashF ((⟨W, H, V⟩ : Merkle.Matrix F).row r)))),
      Merkle.padEven H) := by
  unfold leafLayer
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
  change (Merkle.Packed.padDigests (encode (flat L)) H (Merkle.padEven H), Merkle.padEven H) = _
  rw [e]

/-! ### Injected matrices -/

/-- Matrices of height `n` injected into the layer above `prev` of `2 n` digests: the next layer of
the layer above `prev` interleaved with the injected rows' digests. -/
theorem nextLayer_inject (ms : List (Merkle.Matrix F)) (prev : List (Digest F)) (n : Nat)
    (hne : ms ≠ []) (hh : ∀ m ∈ ms, m.height = n) (hlen : prev.length = 2 * n) :
    Merkle.nextLayer hashF compF ms prev =
      Merkle.nextLayer hashF compF [] (interleave (Merkle.nextLayer hashF compF [] prev)
        ((List.range n).map fun i ↦ hashF (ms.flatMap (·.row i)))) := by
  obtain ⟨m, ms', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hm := hh m List.mem_cons_self
  have hinner : ∀ i < n, (Merkle.nextLayer hashF compF [] prev).getD i 0 =
      compF (prev.getD (2 * i) 0) (prev.getD (2 * i + 1) 0) := by
    intro i hi
    simp only [Merkle.nextLayer, Merkle.padTo, hlen]
    rw [List.getD_append _ _ _ _ (by rw [List.length_map, List.length_range]; omega),
      List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega),
      List.getElem_map, List.getElem_range]
  have hlen1 : n ≤ (Merkle.nextLayer hashF compF [] prev).length := by
    simp only [Merkle.nextLayer, Merkle.padTo, List.length_append, List.length_map,
      List.length_range, hlen]
    omega
  have hI : ∀ i < n,
      (interleave (Merkle.nextLayer hashF compF [] prev)
        ((List.range n).map fun i ↦ hashF ((m :: ms').flatMap (·.row i)))).getD (2 * i) 0 =
        compF (prev.getD (2 * i) 0) (prev.getD (2 * i + 1) 0) ∧
      (interleave (Merkle.nextLayer hashF compF [] prev)
        ((List.range n).map fun i ↦ hashF ((m :: ms').flatMap (·.row i)))).getD (2 * i + 1) 0 =
        hashF ((m :: ms').flatMap (·.row i)) := by
    intro i hi
    have hi' : i < ((List.range n).map fun i ↦ hashF ((m :: ms').flatMap (·.row i))).length := by
      rw [List.length_map, List.length_range]; exact hi
    obtain ⟨e1, e2⟩ := getD_interleave (Merkle.nextLayer hashF compF [] prev)
      ((List.range n).map fun i ↦ hashF ((m :: ms').flatMap (·.row i))) i (by omega) hi'
    rw [e1, e2, hinner i hi, List.getD_eq_getElem _ _ hi', List.getElem_map, List.getElem_range]
    exact ⟨rfl, rfl⟩
  have hlenI : (interleave (Merkle.nextLayer hashF compF [] prev)
      ((List.range n).map fun i ↦ hashF ((m :: ms').flatMap (·.row i)))).length = 2 * n := by
    rw [length_interleave, List.length_map, List.length_range, Nat.min_eq_right hlen1]
  generalize interleave (Merkle.nextLayer hashF compF [] prev)
    ((List.range n).map fun i ↦ hashF ((m :: ms').flatMap (·.row i))) = I at hI hlenI
  unfold Merkle.nextLayer
  simp only [hlenI, hlen]
  congr 1
  rw [show 2 * n / 2 = n by omega]
  refine List.map_congr_left fun i hi ↦ ?_
  have hi := List.mem_range.mp hi
  rw [(hI i hi).1, (hI i hi).2]
  simp only [hm, hi, ↓reduceIte]

/-- The packed injection of matrices of height `n` into a layer of `n` digests is the
specification's. -/
theorem injectLayer_encode [PackedPoseidon2 p] (L : List (Digest F)) (n : Nat)
    (hL : L.length = n) (hn : n = 1 ∨ 2 ∣ n) {inj : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM inj ss)
    (hf : ∀ s ∈ ss, s.values.size = s.width * s.height ∧ s.height = n ∧ 0 < s.width)
    (hu : 32 * (n * (ss.map Mat.width).sum + 1) < USize.size) (hu2 : 64 * n < USize.size) :
    injectLayer p (encode (flat L)) n inj = encode (flat (if ss = [] then L else
      Merkle.nextLayer hashF compF [] (interleave L
        ((List.range n).map fun i ↦ hashF (rowcat ss i))))) := by
  cases h with
  | nil => rfl
  | @cons m s ms ss' hm hr =>
    rw [ite_eq_right (List.cons_ne_nil _ _)]
    unfold injectLayer
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [foldl_width, Nat.zero_add, sum_width (.cons hm hr)]
    obtain ⟨V, e, hV, hrow⟩ := sideBySide_eq n (.cons hm hr)
      (fun x hx ↦ ⟨(hf x hx).1, (hf x hx).2.1⟩)
    have hW : 0 < ((s :: ss').map Mat.width).sum := by
      rw [List.map_cons, List.sum_cons]; have := (hf s List.mem_cons_self).2.2; omega
    rw [e, leafLayer_encode _ n V hV hW hu]
    dsimp only
    have hpad : Merkle.padEven n = n := by
      unfold Merkle.padEven
      split <;> omega
    have hhs : (List.range n).map (fun r ↦
        hashF ((⟨((s :: ss').map Mat.width).sum, n, V⟩ : Merkle.Matrix F).row r)) =
        (List.range n).map fun i ↦ hashF (rowcat (s :: ss') i) :=
      List.map_congr_left fun r hr ↦ by rw [hrow r (List.mem_range.mp hr)]
    have hP : Merkle.padTo 0 n ((List.range n).map fun i ↦ hashF (rowcat (s :: ss') i)) =
        (List.range n).map fun i ↦ hashF (rowcat (s :: ss') i) := by
      simp only [Merkle.padTo, List.length_map, List.length_range, Nat.sub_self,
        List.replicate_zero, List.append_nil]
    rw [hpad, hhs, hP, sideBySide_interleave L _ n hL (by rw [List.length_map, List.length_range])]
    have hlen : (interleave L ((List.range n).map fun i ↦ hashF (rowcat (s :: ss') i))).length =
        2 * n := by
      rw [length_interleave, List.length_map, List.length_range, hL, Nat.min_self]
    rw [← hlen, CompStark.Merkle.Packed.nextLayer_encode _ (by rw [hlen]; omega)]

theorem upperLayersAll_eq_cons (fuel : Nat) (rest : List (Merkle.Matrix F)) (L : List (Digest F)) :
    Merkle.upperLayersAll hashF compF fuel rest L =
      L :: (Merkle.upperLayersAll hashF compF fuel rest L).tail := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [Merkle.upperLayersAll]
    split <;> rfl

/-- The packed layer loop builds the specification's layers, injecting the matrices of each
layer's height, for layers of `2 ^ k` digests and matrices of the prover's shapes. -/
theorem upperMixed_encode [Mont32BaseField p] [PackedPoseidon2 p] (H W : Nat)
    (hu : 32 * (H * W + 1) < USize.size) (hW : 0 < W) : ∀ (fuel : Nat) {rest : List PMat} {restS : List (Mat F)},
    List.Forall₂ RM rest restS → (∀ s ∈ restS, MatOk s) → (restS.map Mat.width).sum ≤ W →
    ∀ (L : List (Digest F)) (out : Array ByteArray), (∃ k, L.length = 2 ^ k) → L.length ≤ H →
    upperMixed p rest (encode (flat L)) L.length out fuel =
      out ++ ((Merkle.upperLayersAll hashF compF fuel (restS.map Mat.toMatrix) L).tail.map
        fun l ↦ encode (flat l)).toArray := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ L out _ _
    exact Array.append_empty.symm
  | succ fuel ih =>
    intro rest restS h hok hsum L out hk hH
    rw [upperMixed, Merkle.upperLayersAll]
    by_cases h1 : L.length ≤ 1
    · rw [ite_eq_left h1, ite_eq_left h1]
      exact Array.append_empty.symm
    rw [ite_eq_right h1, ite_eq_right h1]
    obtain ⟨k, hk⟩ := hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [Nat.pow_zero] at hk; omega
      · omega⟩
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hWH : H ≤ H * W := Nat.le_mul_of_pos_right H hW
    rw [CompStark.Merkle.Packed.nextLayer_encode L (by omega)]
    dsimp only
    have hL1 := length_nextLayer_pow L k hk
    rw [hL1]
    -- The injected matrices.
    have hn : (L.length / 2).nextPowerOfTwo = 2 ^ k := by
      rw [hk, h2, Nat.mul_div_cancel_left _ (by decide)]
      exact Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow k)
    have hpred : ∀ s ∈ restS, ((fun x : Merkle.Matrix F ↦ x.height.nextPowerOfTwo == 2 ^ k) ∘
        Mat.toMatrix) s = (fun x : Mat F ↦ x.height == 2 ^ k) s := by
      intro s hs
      obtain ⟨j, -, hj⟩ := (hok s hs).2.1
      simp only [Function.comp_apply, Mat.toMatrix, hj,
        Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow j)]
    rw [hn, List.takeWhile_map, takeWhile_congr hpred]
    generalize hG : restS.takeWhile (fun x : Mat F ↦ x.height == 2 ^ k) = G
    have hinj : List.Forall₂ RM (rest.takeWhile (·.height == 2 ^ k)) G := by
      rw [← hG]
      exact forall₂_takeWhile (fun a b hab ↦ by rw [hab.2.1]) h
    have hGmem : ∀ s ∈ G, s ∈ restS := fun s hs ↦ by
      rw [← hG] at hs; exact (mem_takeWhile hs).1
    have hGsum : (G.map Mat.width).sum ≤ W := by
      rw [← hG]; exact (sum_takeWhile_le _ _).trans hsum
    have hGf : ∀ s ∈ G, s.values.size = s.width * s.height ∧ s.height = 2 ^ k ∧ 0 < s.width := by
      intro s hs
      have hs' := hs
      rw [← hG] at hs'
      have := (mem_takeWhile hs').2
      simp only [beq_iff_eq] at this
      exact ⟨(hok s (hGmem s hs)).2.2.1, this, (hok s (hGmem s hs)).1⟩
    have hkH : 2 ^ k ≤ H := by omega
    rw [injectLayer_encode _ (2 ^ k) hL1 (by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · left; rfl
        · right; exact dvd_pow_self 2 (by omega)) hinj hGf
      (by have := Nat.mul_le_mul hkH hGsum; omega) (by omega)]
    -- The specification's next layer.
    have hspec : Merkle.nextLayer hashF compF (G.map Mat.toMatrix) L =
        if G = [] then Merkle.nextLayer hashF compF [] L else
          Merkle.nextLayer hashF compF [] (interleave (Merkle.nextLayer hashF compF [] L)
            ((List.range (2 ^ k)).map fun i ↦ hashF (rowcat G i))) := by
      split
      · rename_i hG0; rw [hG0]; rfl
      · rename_i hG0
        rw [nextLayer_inject _ L (2 ^ k) (by simpa only [ne_eq, List.map_eq_nil_iff] using hG0)
          (fun m hm ↦ by
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
            exact (hGf s hs).2.1) (by rw [hk, h2])]
        congr 3
        funext i
        rw [rowcat, List.flatMap_map]
    rw [hspec]
    generalize hL2 : (if G = [] then Merkle.nextLayer hashF compF [] L else
      Merkle.nextLayer hashF compF [] (interleave (Merkle.nextLayer hashF compF [] L)
        ((List.range (2 ^ k)).map fun i ↦ hashF (rowcat G i)))) = L2
    have hL2len : L2.length = 2 ^ k := by
      rw [← hL2]
      split
      · exact hL1
      · apply length_nextLayer_pow
        rw [length_interleave, hL1, List.length_map, List.length_range, Nat.min_self,
          Nat.pow_succ, Nat.mul_comm]
    have hlenG := hinj.length_eq
    have e := ih (List.forall₂_drop G.length h) (fun s hs ↦ hok s (List.mem_of_mem_drop hs))
      ((sum_drop_le _ _).trans hsum) L2 (out.push (encode (flat L2))) ⟨k, hL2len⟩ (by omega)
    rw [hL2len] at e
    rw [hlenG, e, List.length_map, ← List.map_drop, upperLayersAll_eq_cons fuel, List.tail_cons]
    apply Array.toList_inj.mp
    simp only [Array.toList_append, Array.toList_push, List.map_cons, List.append_assoc,
      List.singleton_append, List.tail_cons]

/-! ### Commitments -/

/-- The packed commitment of matrices of the prover's shapes has the specification's layers. -/
theorem commitLayers_eq [Mont32BaseField p] [PackedPoseidon2 p] {ms : List PMat}
    {ss : List (Mat F)} (h : List.Forall₂ RM ms ss) (hok : CommitOk ss) :
    commitLayers p ms = (Committed.ofMats hashF compF ss).layers.map encodeDigests := by
  obtain ⟨H, hne, hall, hu⟩ := hok
  rw [Addressable, foldl_width_mat, Nat.zero_add] at hu
  generalize hW : (ss.map Mat.width).sum = W at hu
  have hW0 : 0 < W := by
    obtain ⟨s, ss', rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [← hW, List.map_cons, List.sum_cons]
    have := (hall s List.mem_cons_self).1.1
    omega
  rw [Committed.ofMats, map_encodeDigests]
  unfold commitLayers Merkle.layers Merkle.sortTallest
  have hsort := forall₂_mergeSort_height h
  have hmap : (ss.map Mat.toMatrix).mergeSort (fun a b ↦ decide (b.height ≤ a.height)) =
      (ss.mergeSort fun a b ↦ decide (b.height ≤ a.height)).map Mat.toMatrix :=
    (List.map_mergeSort (f := Mat.toMatrix) fun _ _ _ _ ↦ rfl).symm
  rw [hmap]
  have hperm := List.mergeSort_perm ss fun a b ↦ decide (b.height ≤ a.height)
  dsimp only
  generalize ss.mergeSort (fun a b ↦ decide (b.height ≤ a.height)) = sorted at hsort hperm
  generalize ms.mergeSort (fun a b ↦ decide (b.height ≤ a.height)) = sortedP at hsort
  have hall' : ∀ s ∈ sorted, MatOk s ∧ s.height ≤ H := fun s hs ↦ hall s (hperm.mem_iff.mp hs)
  have hWs : (sorted.map Mat.width).sum = W := by rw [← hW]; exact (hperm.map _).sum_eq
  cases hsort with
  | nil => exact absurd (List.Perm.nil_eq hperm).symm hne
  | @cons m s msP ssS hm hrest =>
    dsimp only
    simp only [List.map_cons, List.headD_cons, Mat.toMatrix]
    rw [hm.2.1]
    have hs := hall' s List.mem_cons_self
    obtain ⟨j, -, hj⟩ := hs.1.2.1
    -- The tallest matrices.
    have htall : List.Forall₂ RM ((m :: msP).takeWhile (·.height == s.height))
        ((s :: ssS).takeWhile (·.height == s.height)) :=
      forall₂_takeWhile (fun a b hab ↦ by rw [hab.2.1]) (.cons hm hrest)
    have hmatT : ((s :: ssS).map Mat.toMatrix).takeWhile (·.height == s.height) =
        ((s :: ssS).takeWhile (·.height == s.height)).map Mat.toMatrix := by
      rw [List.takeWhile_map]; rfl
    rw [show (⟨s.width, s.height, s.values⟩ : Merkle.Matrix F) :: ssS.map Mat.toMatrix =
      (s :: ssS).map Mat.toMatrix from rfl, hmatT]
    generalize hT : (s :: ssS).takeWhile (·.height == s.height) = T at htall
    have hTmem : ∀ x ∈ T, x ∈ s :: ssS := fun x hx ↦ by
      rw [← hT] at hx; exact (mem_takeWhile hx).1
    have hTf : ∀ x ∈ T, x.values.size = x.width * x.height ∧ x.height = s.height := by
      intro x hx
      have hx' := hx
      rw [← hT] at hx'
      have := (mem_takeWhile hx').2
      simp only [beq_iff_eq] at this
      exact ⟨(hall' x (hTmem x hx)).1.2.2.1, this⟩
    have hTsum : (T.map Mat.width).sum ≤ W := by
      rw [← hT, ← hWs]; exact sum_takeWhile_le _ _
    have hT0 : 0 < (T.map Mat.width).sum := by
      rw [← hT, List.takeWhile_cons, ite_eq_left (beq_self_eq_true _), List.map_cons,
        List.sum_cons]
      have := hs.1.1
      omega
    obtain ⟨V, e, hV, hrow⟩ := sideBySide_eq s.height htall hTf
    rw [foldl_width, Nat.zero_add, sum_width htall, e,
      leafLayer_encode _ s.height V hV hT0 (by
        have := Nat.mul_le_mul hs.2 hTsum; omega)]
    dsimp only
    have hpad : Merkle.padEven s.height = s.height := by
      unfold Merkle.padEven
      split
      · rename_i h1; exact h1.symm
      · rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simp only [Nat.pow_zero] at hj; omega
        · have : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
          omega
    have hfirst : Merkle.firstLayer hashF (T.map Mat.toMatrix) s.height =
        Merkle.padTo 0 (Merkle.padEven s.height) ((List.range s.height).map fun r ↦
          hashF ((⟨(T.map Mat.width).sum, s.height, V⟩ : Merkle.Matrix F).row r)) := by
      rw [Merkle.firstLayer]
      congr 1
      refine List.map_congr_left fun r hr ↦ ?_
      rw [hrow r (List.mem_range.mp hr), rowcat, List.flatMap_map]
    rw [hfirst]
    generalize hF : Merkle.padTo 0 (Merkle.padEven s.height) ((List.range s.height).map fun r ↦
      hashF ((⟨(T.map Mat.width).sum, s.height, V⟩ : Merkle.Matrix F).row r)) = first
    have hFlen : first.length = s.height := by
      rw [← hF, Merkle.padTo, List.length_append, List.length_replicate, List.length_map,
        List.length_range, hpad]
      omega
    have e := upperMixed_encode H W (by omega) hW0 first.length
      (List.forall₂_drop ((m :: msP).takeWhile (·.height == s.height)).length (.cons hm hrest))
      (fun x hx ↦ (hall' x (List.mem_of_mem_drop hx)).1) (hWs ▸ sum_drop_le _ _) first
      #[encode (flat first)] ⟨j, by rw [hFlen, hj]⟩ (by rw [hFlen]; exact hs.2)
    rw [hFlen] at e
    rw [hpad, hFlen, List.length_map, ← htall.length_eq, ← List.map_drop, e,
      upperLayersAll_eq_cons _ _ first, List.tail_cons]
    apply Array.toList_inj.mp
    simp only [Array.toList_append, List.map_cons, List.cons_append, List.nil_append]

/-- The fast commitment represents the specification's. -/
theorem commit_rel [Mont32BaseField p] [PackedPoseidon2 p] {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss) (hok : CommitOk ss) :
    RC (commit p ms) (Committed.ofMats hashF compF ss) :=
  ⟨h, commitLayers_eq h hok⟩

end CompStark.Stark.Fast
