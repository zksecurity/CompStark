/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Columns
public import CompStark.Merkle.RootCorrectness
public import CompStark.Merkle.PackedColumnsCorrectness
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # The fast commitments are the specification's

Rows and digests read from encoded matrices and digest layers are the specification's reads, in
range and out of it (`readRow_rel`, `readDigest_encodeDigests`), so caps, openings and heights
agree (`cap_rel`, `openAt_rel`, `maxHeight_rel`). The packed Merkle commitment has the
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

/-- A read past the end of a buffer is zero. -/
theorem read_oob (b : ByteArray) (i : Nat) (hb : b.size < USize.size)
    (hu : 4 * i + 3 < USize.size) (hi : b.size ≤ 4 * i + 3) :
    CompPoly.CPolynomial.NTTFast.Packed.Native.read b i = 0 := by
  open CompPoly.CPolynomial.NTTFast.Packed.Native in
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

/-- A word past the end of a buffer reads zero. -/
theorem word_oob (b : ByteArray) (i : Nat) (hb : b.size < USize.size)
    (hu : 4 * i + 3 < USize.size) (hi : b.size ≤ 4 * i + 3) : word (p := p) b i = 0 := by
  rw [word, read_oob b i hb hu hi]
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
  rw [Commit.readRow, rowOf]
  apply Array.ext
  · simp only [Array.size_ofFn, h.width]
  · intro j h1 _
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    rw [Array.size_ofFn, h.width] at h1
    by_cases hr : r < m.height
    · rw [word, read_colAt h r j hr h1, ofWord_val]
    · have hc : (colBlocks m pm.rows).getD (r / pm.rows * m.width + j) #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none, Option.getD_none]
        rw [size_colBlocks]
        have h1' : m.height / pm.rows ≤ r / pm.rows := Nat.div_le_div_right (by omega)
        have := Nat.mul_le_mul_right m.width h1'
        omega
      have hv : m.values.size ≤ r * m.width + j := by
        rw [h.size, Nat.mul_comm]
        have := Nat.mul_le_mul_right m.width (show m.height ≤ r by omega)
        omega
      have h0 : 4 * (#[] : Array F).size < USize.size := by
        simp only [List.size_toArray, List.length_nil]; have := USize.le_size; omega
      have h3 : 4 * (r % pm.rows) + 3 < USize.size := by
        have := h.addr; have := Nat.mod_lt r h.pos; omega
      rw [colAt_eq h, hc]
      dsimp only
      rw [word_encode_getD _ _ h0 h3, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none hv]
      rfl

theorem foldl_maxHeight {ms : List PMat} {ss : List (Mat F)} (h : List.Forall₂ RM ms ss)
    (a : Nat) : ms.foldl (fun m x ↦ max m x.height) a = ss.foldl (fun m x ↦ max m x.height) a := by
  induction h generalizing a with
  | nil => rfl
  | cons hr _ ih => rw [List.foldl_cons, List.foldl_cons, hr.height, ih]

/-- Heights are the represented matrices'. -/
theorem maxHeight_rel {c : Commit} {s : Committed F} (h : RC c s) : c.maxHeight = s.maxHeight :=
  foldl_maxHeight h.1 0

theorem layer_rel {c : Commit} {s : Committed F} (h : RC c s) (i : Nat) :
    c.layers.getD i .empty = encodeDigests (s.layers.getD i #[]) := by
  rw [h.2, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    ← encodeDigests_empty (p := p), Option.getD_map]

/-- Entry `t < n` of a list's first `n` entries padded to `n`. -/
theorem getD_padTo_take {α : Type} (x : α) (n : Nat) (l : List α) (t : Nat) (ht : t < n) :
    (CompStark.Merkle.padTo x n (l.take n)).getD t x = l.getD t x := by
  rw [CompStark.Merkle.padTo, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hl : t < l.length
  · rw [List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take_of_lt ht]
  · have hlt : (l.take n).length ≤ t := by rw [List.length_take]; omega
    rw [List.getElem?_append_right hlt, List.getElem?_replicate, List.getElem?_eq_none (by omega),
      ite_eq_left_of_eq_true _ _ (eq_true (by rw [List.length_take] at hlt ⊢; omega))]
    rfl

/-- The first `n` digests of a layer, padded with zero digests. -/
theorem ofFn_getD_eq_padTo (layer : Array (Digest F)) (n : Nat) :
    Array.ofFn (n := n) (fun t ↦ layer.getD t.val 0) =
      (CompStark.Merkle.padTo 0 n (layer.toList.take n)).toArray := by
  apply Array.ext
  · rw [Array.size_ofFn, List.size_toArray, CompStark.Merkle.padTo, List.length_append,
      List.length_replicate, List.length_take]
    omega
  · intro t h1 _
    rw [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, List.getElem_toArray, ← List.getD_eq_getElem _ 0,
      getD_padTo_take _ _ _ _ h1, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]

/-- The packed cap is the specification's. -/
theorem cap_rel [Mont32BaseField p] {c : Commit} {s : Committed F} (hc : RC c s) (h : Nat) :
    Commit.cap (p := p) c h = s.cap h := by
  have hs : c.layers.size = s.layers.size := by rw [hc.2, Array.size_map]
  have hlen : (s.layers.toList.map Array.toList).length = s.layers.size := by
    rw [List.length_map, Array.length_toList]
  set k := s.layers.size - 1 - min h (s.layers.size - 1)
  have hl : (s.layers.toList.map Array.toList).getD k [] = (s.layers.getD k #[]).toList := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
      Array.getElem?_toList]
    cases s.layers[k]? <;> rfl
  show Array.ofFn (n := 2 ^ min h (c.layers.size - 1)) (fun t ↦
      Commit.readDigest (p := p) (c.layers.getD (c.layers.size - 1 - min h (c.layers.size - 1))
        .empty) t) =
    (CompStark.Merkle.padTo 0 (2 ^ min h ((s.layers.toList.map Array.toList).length - 1))
      (((s.layers.toList.map Array.toList).getD ((s.layers.toList.map Array.toList).length - 1 -
        min h ((s.layers.toList.map Array.toList).length - 1)) []).take
        (2 ^ min h ((s.layers.toList.map Array.toList).length - 1)))).toArray
  rw [hlen, hs, hl, ← ofFn_getD_eq_padTo]
  congr 1
  funext t
  rw [layer_rel hc, readDigest_encodeDigests]

theorem rows_rel [Mont32BaseField p] (g : Nat → Nat) {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss) : ms.map
        (fun m ↦ Commit.readRow (p := p) m (g m.height)) = ss.map fun m ↦ rowOf m (g m.height)
        := by
  induction h with
  | nil => rfl
  | cons hm _ ih => rw [List.map_cons, List.map_cons, ih, readRow_rel hm, hm.height]

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
  | cons hm _ ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, hm.width]

/-- Column `jj` of a matrix from row `r0` on holds the entries of rows `r0, …, r0 + n - 1`, for
rows within one block. -/
theorem colAt_spec {pm : PMat} {s : Mat F} (hm : RM pm s) (r0 n jj : Nat)
    (hblk : r0 % pm.rows + n ≤ pm.rows) (hr : r0 + n ≤ s.height) (hn : 0 < n)
    (hj : jj < s.width) :
    ∃ A, (pm.colAt jj r0).1 = encode A ∧ (pm.colAt jj r0).2 + n ≤ A.size ∧
      4 * A.size < USize.size ∧ ∀ r < n, A.getD ((pm.colAt jj r0).2 + r) 0 =
        s.values.getD ((r0 + r) * s.width + jj) 0 := by
  have hr0 : r0 < s.height := by omega
  refine ⟨Array.ofFn (n := pm.rows) fun k ↦
      s.values.getD ((r0 / pm.rows * pm.rows + k) * s.width + jj) 0, ?_, ?_, ?_, fun r hrn ↦ ?_⟩
  · rw [colAt_eq hm, colBlocks_getD s _ r0 jj hm.pos hm.dvd hr0 hj]
  · unfold PMat.colAt; rw [Array.size_ofFn]; exact hblk
  · rw [Array.size_ofFn]; exact hm.addr
  · unfold PMat.colAt
    dsimp only
    rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ (by omega)]
    dsimp only
    rw [← Nat.add_assoc, Nat.div_add_mod']

/-- The columns of matrices side by side from row `r0` on hold their rows side by side, for rows
within one block of every matrix. -/
theorem colsList_spec {ms : List PMat} {ss : List (Mat F)} (h : List.Forall₂ RM ms ss)
    (r0 n : Nat) (hn : 0 < n) (hblk : ∀ m ∈ ms, r0 % m.rows + n ≤ m.rows)
    (hr : ∀ s ∈ ss, r0 + n ≤ s.height ∧ s.values.size = s.width * s.height)
    :
    ∀ j < (ss.map Mat.width).sum, ∃ A, ((colsList ms r0).getD j (.empty, 0)).1 = encode A ∧
      ((colsList ms r0).getD j (.empty, 0)).2 + n ≤ A.size ∧ 4 * A.size < USize.size ∧
      ∀ r < n, A.getD (((colsList ms r0).getD j (.empty, 0)).2 + r) 0 =
        (rowcat ss (r0 + r)).getD j 0 := by
  induction h with
  | nil => intro j hj; simp only [List.map_nil, List.sum_nil] at hj; omega
  | @cons pm s ms ss hm _ ih =>
    intro j hj
    rw [List.map_cons, List.sum_cons] at hj
    have hlen : ((List.range pm.width).map fun jj ↦ pm.colAt jj r0).length = s.width := by
      rw [List.length_map, List.length_range, hm.width]
    have hrow : (s.toMatrix.row (r0 + 0)).length = s.width := length_row _ _
    have hcl : colsList (pm :: ms) r0 =
        (List.range pm.width).map (fun jj ↦ pm.colAt jj r0) ++ colsList ms r0 := by
      simp only [colsList, List.flatMap_cons]
    have hrc (r : Nat) : rowcat (s :: ss) (r0 + r) = s.toMatrix.row (r0 + r) ++ rowcat ss (r0 + r)
      := by simp only [rowcat, List.flatMap_cons]
    have hlr (r : Nat) : (s.toMatrix.row (r0 + r)).length = s.width := length_row _ _
    rw [hcl]
    by_cases hjs : j < s.width
    · have hjl : j < ((List.range pm.width).map fun jj ↦ pm.colAt jj r0).length := by
        rw [hlen]; exact hjs
      rw [List.getD_append _ _ _ _ hjl, List.getD_eq_getElem _ _ hjl, List.getElem_map,
        List.getElem_range]
      obtain ⟨A, e1, e2, e3, e4⟩ := colAt_spec hm r0 n j
        (hblk pm List.mem_cons_self) (hr s List.mem_cons_self).1 hn hjs
      refine ⟨A, e1, e2, e3, fun r hrn ↦ ?_⟩
      have hjr : j < (s.toMatrix.row (r0 + r)).length := by rw [hlr]; exact hjs
      rw [e4 r hrn, hrc, List.getD_append _ _ _ _ hjr, List.getD_eq_getElem _ _ hjr]
      simp only [Mat.toMatrix, Merkle.Matrix.row, List.getElem_map, List.getElem_range]
    · have hjl : ((List.range pm.width).map fun jj ↦ pm.colAt jj r0).length ≤ j := by
        rw [hlen]; omega
      rw [List.getD_append_right _ _ _ _ hjl, hlen]
      obtain ⟨A, e1, e2, e3, e4⟩ := ih (fun m hm' ↦ hblk m (List.mem_cons_of_mem _ hm'))
        (fun s' hs' ↦ hr s' (List.mem_cons_of_mem _ hs')) (j - s.width) (by omega)
      refine ⟨A, e1, e2, e3, fun r hrn ↦ ?_⟩
      have hjr : (s.toMatrix.row (r0 + r)).length ≤ j := by rw [hlr]; omega
      rw [e4 r hrn, hrc, List.getD_append_right _ _ _ _ hjr, hlr]

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
    fun a ha b hb ↦ by rw [(hR a ha).height, (hR b hb).height]
  have e2 := List.map_mergeSort (l := ms.zip ss) (f := Prod.snd)
    (r := fun a b ↦ decide (b.2.height ≤ a.2.height)) (s := fun a b ↦ decide (b.height ≤ a.height))
    fun _ _ _ _ ↦ rfl
  rw [← hms] at e1
  rw [← hss] at e2
  rw [← e1, ← e2, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun x hx ↦ hR x ((List.mem_mergeSort).mp hx)

theorem flat_extract (a : List (Digest F)) (m : Nat) (hm : m < a.length) :
    (flat a).extract (8 * m) (8 * m + 8) = flat [a[m]] := by
  refine CompStark.Merkle.Packed.flat_eq _ _ (by
    rw [Array.size_extract, size_flat, List.length_singleton]; omega) fun i hi j hj ↦ ?_
  rw [List.length_singleton] at hi
  obtain rfl : i = 0 := by omega
  rw [Nat.mul_zero, Nat.zero_add, extract_getD _ _ 8 _ hj, getD_flat,
    show (8 * m + j) / 8 = m by omega, List.getD_eq_getElem _ _ hm]
  exact CompStark.Merkle.Packed.vget_congr _ (by omega) _ _

theorem interleave_take_succ (a b : List (Digest F)) (m : Nat) (ha : m < a.length)
    (hb : m < b.length) :
    interleave (a.take (m + 1)) (b.take (m + 1)) =
      interleave (a.take m) (b.take m) ++ [a[m], b[m]] := by
  rw [List.take_add_one, List.take_add_one, interleave, interleave, List.zip_append (by
    rw [List.length_take, List.length_take]; omega), List.flatMap_append,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
  rfl

/-- Two packed layers of `n` digests interleaved are the layers interleaved. -/
theorem interleaveDigests_eq (a b : List (Digest F)) (n : Nat) (ha : a.length = n)
    (hb : b.length = n) :
    interleaveDigests (encode (flat a)) (encode (flat b)) n = encode (flat (interleave a b)) := by
  unfold interleaveDigests
  rw [show ByteArray.emptyWithCapacity (64 * n) = encode (flat (p := p) []) from rfl]
  have key : ∀ m ≤ n, (List.range m).foldl (fun out i ↦ out ++
      (encode (flat a)).extract (32 * i) (32 * i + 32) ++
      (encode (flat b)).extract (32 * i) (32 * i + 32)) (encode (flat (p := p) [])) =
      encode (flat (interleave (a.take m) (b.take m))) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        show 32 * m = 4 * (8 * m) by omega, show 4 * (8 * m) + 32 = 4 * (8 * m + 8) by omega,
        extract_encode, extract_encode, flat_extract a m (by omega), flat_extract b m (by omega),
        ← CompPoly.PackedRepr.encode_append, ← CompPoly.PackedRepr.encode_append,
        ← CompStark.Merkle.Packed.flat_append, ← CompStark.Merkle.Packed.flat_append,
        interleave_take_succ a b m (by omega) (by omega), List.append_assoc]
      rfl
  rw [key n le_rfl, ← ha, List.take_length, ha, ← hb, List.take_length]

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

theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b, b ∈ l₂ ∧ R a b := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, r⟩ := ih ha; exact ⟨b, List.mem_cons_of_mem _ hb, r⟩

theorem forall₂_mem_right {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a, a ∈ l₁ ∧ R a b := by
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, hxy⟩
    · obtain ⟨a, ha, r⟩ := ih hb; exact ⟨a, List.mem_cons_of_mem _ ha, r⟩

/-- A multiple of `d` modulo a multiple `R` of `d` leaves room for `d` more. -/
theorem mod_add_le_of_dvd {R d x : Nat} (hR : 0 < R) (hd : d ∣ R) (hx : d ∣ x) :
    x % R + d ≤ R := by
  have h1 : d ∣ x % R := (Nat.dvd_mod_iff hd).mpr hx
  have h2 : x % R < R := Nat.mod_lt _ hR
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := hd
  have : a < b := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; omega
    · rw [ha, hb] at h2; exact Nat.lt_of_mul_lt_mul_left h2
  rw [ha, hb]
  have := Nat.mul_le_mul_left d (show a + 1 ≤ b by omega)
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem getD_map_toArray {α β : Type} (l : List α) (f : α → β) (j : Nat) (d : α) :
    (l.map f).toArray.getD j (f d) = f (l.getD j d) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases l[j]? <;> rfl

theorem gcd_dvd_init (ms : List PMat) : ∀ b, ms.foldl (fun a m ↦ Nat.gcd a m.rows) b ∣ b := by
  induction ms with
  | nil => intro b; exact dvd_rfl
  | cons x xs ih => intro b; rw [List.foldl_cons]; exact (ih _).trans (Nat.gcd_dvd_left _ _)

theorem gcd_dvd_rows (ms : List PMat) (a : Nat) :
    ∀ m ∈ ms, ms.foldl (fun a m ↦ Nat.gcd a m.rows) a ∣ m.rows := by
  induction ms generalizing a with
  | nil => intro m hm; exact absurd hm (List.not_mem_nil)
  | cons m' ms ih =>
    intro m hm
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (gcd_dvd_init ms _).trans (Nat.gcd_dvd_right _ _)
    · exact ih _ m hm

theorem gcd_pos (ms : List PMat) (a : Nat) (ha : 0 < a) :
    0 < ms.foldl (fun a m ↦ Nat.gcd a m.rows) a := by
  induction ms generalizing a with
  | nil => exact ha
  | cons m ms ih => rw [List.foldl_cons]; exact ih _ (Nat.gcd_pos_of_pos_left _ ha)

/-- **The packed leaf layer of matrices side by side** is the specification's leaf digests of
their rows side by side, padded. -/
theorem leafLayer_cols [PackedPoseidon2 p] (H : Nat) {ms : List PMat} {ss : List (Mat F)}
    (h : List.Forall₂ RM ms ss) (hH : ∀ s ∈ ss, s.height = H)
    (hW : 0 < (ss.map Mat.width).sum) (hu : 32 * (H + 1) < USize.size) :
    leafLayer p ms H = (encode (flat (Merkle.padTo 0 (Merkle.padEven H)
      ((List.range H).map fun r ↦ hashF (rowcat ss r)))), Merkle.padEven H) := by
  unfold leafLayer
  dsimp only
  rw [foldl_width, Nat.zero_add, sum_width h]
  generalize hWd : (ss.map Mat.width).sum = W at hW
  generalize hsz : ms.foldl (fun a m ↦ Nat.gcd a m.rows) 512 = size
  have hs0 : 0 < size := by rw [← hsz]; exact gcd_pos ms 512 (by decide)
  have hdv : ∀ m ∈ ms, size ∣ m.rows := fun m hm ↦ by rw [← hsz]; exact gcd_dvd_rows ms 512 m hm
  have hHs : H % size = 0 := by
    have h' := h
    cases h' with
    | nil => simp only [List.map_nil, List.sum_nil] at hWd; omega
    | @cons m s _ _ hm _ =>
      have h1 := hm.dvd
      rw [hH s List.mem_cons_self] at h1
      exact Nat.mod_eq_zero_of_dvd ((hdv m List.mem_cons_self).trans (Nat.dvd_of_mod_eq_zero h1))
  have hparts : H / size * size = H := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hHs)
  generalize H / size = parts at hparts ⊢
  have hss : ∀ s ∈ ss, s.values.size = s.width * s.height := fun s hs ↦ by
    obtain ⟨m, -, hm⟩ := forall₂_mem_right h hs
    exact hm.size
  have task : ∀ k < parts, Merkle.Packed.hashColumns p
      ((colsList ms (k * size)).map (·.1)).toArray ((colsList ms (k * size)).map (·.2)).toArray
        W size =
        encode (flat ((List.range size).map fun i ↦ hashF (rowcat ss (k * size + i)))) := by
    intro k hk
    have hk1 : k * size + size ≤ H := by
      rw [← hparts]; have := Nat.mul_le_mul_right size (show k + 1 ≤ parts by omega)
      rw [Nat.succ_mul] at this; exact this
    have spec := colsList_spec h (k * size) size hs0 (fun m hm ↦ by
        obtain ⟨s, -, hrm⟩ := forall₂_mem_left h hm
        exact mod_add_le_of_dvd hrm.pos (hdv m hm) (Nat.dvd_mul_left size k))
      (fun s hs ↦ ⟨by rw [hH s hs]; exact hk1, hss s hs⟩)
    rw [hWd] at spec
    generalize colsList ms (k * size) = L at spec
    have hC : Merkle.Packed.ColumnsOk (L.map (·.1)).toArray (L.map (·.2)).toArray
        (fun j ↦ (CompPoly.PackedRepr.decode (L.getD j (.empty, 0)).1 : Array F))
        (fun j ↦ (L.getD j (.empty, 0)).2) W size := by
      refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
      · obtain ⟨A, e1, -, -, -⟩ := spec j hj
        have e : (L.map (·.1)).toArray.getD j .empty = (L.getD j (.empty, 0)).1 :=
          getD_map_toArray L (·.1) j (ByteArray.empty, 0)
        rw [e, e1, CompPoly.PackedRepr.decode_encode]
      · exact getD_map_toArray L (·.2) j (ByteArray.empty, 0)
      · obtain ⟨A, e1, e2, -, -⟩ := spec j hj
        rw [e1, CompPoly.PackedRepr.decode_encode]; exact e2
      · obtain ⟨A, e1, -, e3, -⟩ := spec j hj
        rw [e1, CompPoly.PackedRepr.decode_encode]; exact e3
    rw [Merkle.Packed.hashColumns_encode hC (by omega)]
    congr 2
    refine List.map_congr_left fun r hr ↦ congrArg _ ?_
    have hr := List.mem_range.mp hr
    apply List.ext_getElem
    · simp only [Merkle.Matrix.row, List.length_map, List.length_range, length_rowcat, hWd]
    · intro c h1 h2
      simp only [Merkle.Matrix.row, List.length_map, List.length_range] at h1
      simp only [Merkle.Matrix.row, List.getElem_map, List.getElem_range]
      rw [Merkle.Packed.colMatrix_getD _ _ _ _ _ _ hr h1, ← List.getD_eq_getElem _ 0 h2]
      obtain ⟨A, e1, -, -, e4⟩ := spec c h1
      rw [e1, CompPoly.PackedRepr.decode_encode, e4 r hr]
  rw [CompStark.Merkle.Packed.foldl_spawnAll,
    show ByteArray.emptyWithCapacity (32 * (H + 1)) = ByteArray.emptyWithCapacity 0 from rfl,
    CompStark.Merkle.Packed.foldl_congr_mem _ _ _ (fun k hk acc ↦ by rw [task k
      (List.mem_range.mp hk)]), CompStark.Merkle.Packed.foldl_encode_flat]
  have hfold : (List.range parts).foldl (fun acc k ↦ acc ++ (List.range size).map fun i ↦
      hashF (rowcat ss (k * size + i))) [] = (List.range H).map fun r ↦ hashF (rowcat ss r) := by
    have htiles := CompStark.Merkle.Packed.foldl_tiles H size (fun r ↦ hashF (rowcat ss r)) parts
    rw [hparts, Nat.min_self] at htiles
    rw [← htiles]
    refine CompStark.Merkle.Packed.foldl_congr_mem _ _ _ (fun k hk acc ↦ ?_) []
    have hk := List.mem_range.mp hk
    have := Nat.mul_le_mul_right size (show k + 1 ≤ parts by omega)
    rw [Nat.succ_mul, hparts] at this
    rw [show min size (H - min H (k * size)) = size by omega]
  rw [hfold]
  generalize hL : (List.range H).map (fun r ↦ hashF (rowcat ss r)) = L
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
    have hW : 0 < ((s :: ss').map Mat.width).sum := by
      rw [List.map_cons, List.sum_cons]; have := (hf s List.mem_cons_self).2.2; omega
    rw [leafLayer_cols n (.cons hm hr) (fun x hx ↦ (hf x hx).2.1) hW (by
      have := USize.le_size; omega)]
    dsimp only
    have hpad : Merkle.padEven n = n := by
      unfold Merkle.padEven
      split <;> omega
    have hP : Merkle.padTo 0 n ((List.range n).map fun i ↦ hashF (rowcat (s :: ss') i)) =
        (List.range n).map fun i ↦ hashF (rowcat (s :: ss') i) := by
      simp only [Merkle.padTo, List.length_map, List.length_range, Nat.sub_self,
        List.replicate_zero, List.append_nil]
    have hlm : ((List.range n).map fun i ↦ hashF (rowcat (s :: ss') i)).length = n := by
      rw [List.length_map, List.length_range]
    rw [hpad, hP, interleaveDigests_eq L _ n hL hlm]
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
      exact forall₂_takeWhile (fun a b hab ↦ by rw [hab.height]) h
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
    rw [hm.height]
    have hs := hall' s List.mem_cons_self
    obtain ⟨j, -, hj⟩ := hs.1.2.1
    -- The tallest matrices.
    have htall : List.Forall₂ RM ((m :: msP).takeWhile (·.height == s.height))
        ((s :: ssS).takeWhile (·.height == s.height)) :=
      forall₂_takeWhile (fun a b hab ↦ by rw [hab.height]) (.cons hm hrest)
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
    have hTh : ∀ x ∈ T, x.height = s.height := fun x hx ↦ (hTf x hx).2
    rw [leafLayer_cols s.height htall hTh hT0 (by
        have := Nat.mul_le_mul hs.2 (show 1 ≤ W by omega); omega)]
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
          hashF (rowcat T r)) := by
      rw [Merkle.firstLayer]
      congr 1
      refine List.map_congr_left fun r hr ↦ ?_
      rw [rowcat, List.flatMap_map]
    rw [hfirst]
    generalize hF : Merkle.padTo 0 (Merkle.padEven s.height) ((List.range s.height).map fun r ↦
      hashF (rowcat T r)) = first
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
