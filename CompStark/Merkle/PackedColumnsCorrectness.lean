/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.PackedColumns
public import CompStark.Merkle.PackedCorrectness
public import CompStark.Merkle.RootCorrectness
import all CompStark.Merkle.Packed
import all CompStark.Merkle.PackedColumns
import all CompPoly.Univariate.NTTFast.Packed.Native
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas

/-! # Correctness of the Merkle leaves of a matrix given by its columns

`hashColumns_encode`: the leaf digests of the columns `C j` from the words `o j` are the
specification's digests of the rows of the matrix they hold (`colMatrix`).
-/

@[expose] public section
namespace CompStark.Merkle.Packed
open CompStark.Poseidon2 CompStark.Poseidon2.Packed Montgomery.Native32
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields array_eq_of_getD getD_ofFn_bounded)
open CompPoly.CPolynomial.NTTFast.Packed.Native (readUOffset_encode zeroWords)

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem loadColumns24_encode (C : Nat → Array F) (o : Nat → Nat)
    (hu : ∀ j < 16, (o j).toUSize.toNat = o j) (W : Array F) (i : USize)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hb) :
    loadColumns24 (encode (C 0)) (encode (C 1)) (encode (C 2)) (encode (C 3)) (encode (C 4))
      (encode (C 5)) (encode (C 6)) (encode (C 7)) (encode (C 8)) (encode (C 9)) (encode (C 10))
      (encode (C 11)) (encode (C 12)) (encode (C 13)) (encode (C 14)) (encode (C 15)) (o 0).toUSize
      (o 1).toUSize (o 2).toUSize (o 3).toUSize (o 4).toUSize (o 5).toUSize (o 6).toUSize
      (o 7).toUSize (o 8).toUSize (o 9).toUSize (o 10).toUSize (o 11).toUSize (o 12).toUSize
      (o 13).toUSize (o 14).toUSize (o 15).toUSize (encode W) i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      h11 h12 h13 h14 h15 hb =
      encode (spliceRows coords16 W i.toNat fun j l ↦ (C j).getD (o j + l) 0) := by
  have hs := hb
  simp only [GroupFits24, Fits, size_encode_fields] at hs
  unfold loadColumns24
  simp only [touch8_encode, readUOffset_encode, USize.reduceToNat,hu 0 (by decide),
    hu 1 (by decide), hu 2 (by decide), hu 3 (by decide), hu 4 (by decide), hu 5 (by decide),
    hu 6 (by decide), hu 7 (by decide), hu 8 (by decide), hu 9 (by decide), hu 10 (by decide),
    hu 11 (by decide), hu 12 (by decide), hu 13 (by decide), hu 14 (by decide), hu 15 (by decide),]
  simp (disch := (simp only [USize.reduceToNat, size_encode_fields]; omega)) only [store8_encode']
  simp only [USize.reduceToNat, spliceRows, coords16, lit8, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.add_zero]

/-- The row-major matrix of `rows` rows held by the columns `C j` from the words `o j`, `j < w`. -/
def colMatrix (C : Nat → Array F) (o : Nat → Nat) (w rows : Nat) : Array F :=
  Array.ofFn (n := rows * w) fun k ↦ (C (k.val % w)).getD (o (k.val % w) + k.val / w) 0

theorem colMatrix_getD (C : Nat → Array F) (o : Nat → Nat) (w rows r c : Nat) (hr : r < rows)
    (hc : c < w) : (colMatrix C o w rows).getD (r * w + c) 0 = (C c).getD (o c + r) 0 := by
  have hlt : r * w + c < rows * w := by
    have := Nat.mul_le_mul_right w (show r + 1 ≤ rows by omega)
    rw [Nat.succ_mul] at this; omega
  rw [colMatrix, getD_ofFn_bounded _ _ hlt]
  have h1 : (r * w + c) % w = c := by rw [Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hc]
  have h2 : (r * w + c) / w = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]
  simp only [h1, h2]

theorem size_colMatrix (C : Nat → Array F) (o : Nat → Nat) (w rows : Nat) :
    (colMatrix C o w rows).size = rows * w := Array.size_ofFn

/-- The columns `cs` from the words `os` hold the columns `C j` from the words `o j` of `rows`
rows, addressable. -/
structure ColumnsOk (cs : Array ByteArray) (os : Array Nat) (C : Nat → Array F) (o : Nat → Nat)
    (w rows : Nat) : Prop where
  enc : ∀ j < w, cs.getD j .empty = encode (C j)
  off : ∀ j < w, os.getD j 0 = o j
  fits : ∀ j < w, o j + rows ≤ (C j).size
  addr : ∀ j < w, 4 * (C j).size < USize.size

theorem scatterColumns_encode {cs : Array ByteArray} {os : Array Nat} {C : Nat → Array F}
    {o : Nat → Nat} {w rows : Nat} (h : ColumnsOk cs os C o w rows) (A : Array F) (r0 blk : Nat)
    (hA : 128 ≤ A.size) (hu' : 4 * A.size < USize.size) :
    ∃ A', scatterColumns cs os w rows r0 blk (encode A) = encode A' ∧ A'.size = A.size ∧
      ∀ l < 8, ∀ j, 8 * j + l < A.size → word A' 0 j l =
        if r0 + l < rows ∧ j < min 16 (w - 16 * blk) then
          (colMatrix C o w rows).getD ((r0 + l) * w + 16 * blk + j) 0
        else word A 0 j l := by
  have hM := colMatrix_getD C o w rows
  generalize colMatrix C o w rows = M at hM ⊢
  unfold scatterColumns
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, pure_bind, ite_pure_yield, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have key : ∀ L ≤ 8, ∃ A', (List.range L).foldl (fun b a ↦
      if r0 + a < rows then (List.range (min 16 (w - 16 * blk))).foldl (fun b a_1 ↦
        CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * a_1 + a)
          (CompPoly.CPolynomial.NTTFast.Packed.Native.read (cs.getD (16 * blk + a_1) .empty)
            (os.getD (16 * blk + a_1) 0 + r0 + a))) b
      else b) (encode A) = encode A' ∧ A'.size = A.size ∧
      ∀ l < 8, ∀ j, 8 * j + l < A.size → word A' 0 j l =
        if l < L ∧ r0 + l < rows ∧ j < min 16 (w - 16 * blk)
        then M.getD ((r0 + l) * w + 16 * blk + j) 0 else word A 0 j l := by
    intro L hL
    induction L with
    | zero =>
      refine ⟨A, rfl, rfl, fun l _ j _ ↦ ?_⟩
      simp only [Nat.not_lt_zero, false_and, ↓reduceIte]
    | succ L ih =>
      obtain ⟨A1, e1, s1, w1⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, e1, List.foldl_cons, List.foldl_nil]
      by_cases hrow : r0 + L < rows
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hrow)]
        let v (j : Nat) : F := M.getD ((r0 + L) * w + 16 * blk + j) 0
        have hc : ∀ j ∈ List.range (min 16 (w - 16 * blk)), ∀ b,
            CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * j + L)
              (CompPoly.CPolynomial.NTTFast.Packed.Native.read (cs.getD (16 * blk + j) .empty)
                (os.getD (16 * blk + j) 0 + r0 + L)) =
            CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * j + L) (v j).val := by
          intro j hj b
          have hj : j < min 16 (w - 16 * blk) := List.mem_range.mp hj
          have hj' : 16 * blk + j < w := by omega
          have hf := h.fits _ hj'
          rewrite [h.enc _ hj', h.off _ hj',
            CompPoly.CPolynomial.NTTFast.Packed.Native.read_encode _ _
              (by rw [size_encode_fields]; exact h.addr _ hj') (by omega)]
          show _ = CompPoly.CPolynomial.NTTFast.Packed.Native.write b (8 * j + L)
            (M.getD ((r0 + L) * w + 16 * blk + j) 0).val
          rewrite [Nat.add_assoc ((r0 + L) * w), hM _ _ hrow hj', Nat.add_assoc (o _) r0 L]
          rfl
        rw [foldl_congr_mem _ _ _ hc]
        rw [writes_column L _ v (by omega) A1 (by omega) (by rw [s1]; exact hu')]
        refine ⟨_, rfl, by rw [setColumn, Array.size_ofFn, s1], fun l hl j hj ↦ ?_⟩
        rw [word_setColumn A1 L _ v j l hl (by omega), w1 l hl j hj]
        by_cases hlL : l = L
        · subst hlL
          simp only [true_and, Nat.lt_succ_self, hrow, v]
          split_ifs <;> first | rfl | omega
        · simp only [hlL, false_and, ↓reduceIte]
          split_ifs <;> first | rfl | omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hrow)]
        refine ⟨A1, rfl, s1, fun l hl j hj ↦ ?_⟩
        rw [w1 l hl j hj]
        split_ifs <;> first | rfl | omega
  obtain ⟨A', e, s, wl⟩ := key 8 le_rfl
  refine ⟨A', e, s, fun l hl j hj ↦ ?_⟩
  rw [wl l hl j hj]
  split_ifs <;> first | rfl | omega

theorem absorbColumnsBlock_encode {cs : Array ByteArray} {os : Array Nat} {C : Nat → Array F}
    {o : Nat → Nat} {w rows : Nat} (h : ColumnsOk cs os C o w rows) (A : Array F)
    (r0 blk : Nat) (hA : A.size = 192) :
    ∃ A', absorbColumnsBlock cs os w rows r0 blk (encode A) = encode A' ∧ A'.size = 192 ∧
      ∀ l < 8, lane 24 A' 0 l = if r0 + l < rows then
        CompStark.Hash.overwrite (lane 24 A 0 l) (block (colMatrix C o w rows) w (r0 + l) blk)
      else lane 24 A 0 l := by
  have hM := colMatrix_getD C o w rows
  obtain ⟨A', e, s, wl⟩ := scatterColumns_encode h A r0 blk (by omega)
    (by rw [hA]; have := USize.le_size; omega)
  revert e s wl
  generalize colMatrix C o w rows = M at hM ⊢
  intro e s wl
  unfold absorbColumnsBlock
  split
  · rename_i hfull
    obtain ⟨hr, hw⟩ := hfull
    have hcnt : min 16 (w - 16 * blk) = 16 := by omega
    have hjw (j : Nat) (hj : j < 16) : 16 * blk + j < w := by omega
    have hq (j : Nat) (hj : j < 16) : o (16 * blk + j) + r0 + 8 ≤ (C (16 * blk + j)).size := by
      have := h.fits _ (hjw j hj); omega
    have hqu (j : Nat) (hj : j < 16) : o (16 * blk + j) + r0 < USize.size := by
      have := hq j hj; have := h.addr _ (hjw j hj); omega
    have hfit (j : Nat) (hj' : j < 16) :
        Fits (cs.getD (16 * blk + j) .empty) (os.getD (16 * blk + j) 0 + r0).toUSize 7 := by
      rw [h.enc _ (hjw j hj'), h.off _ (hjw j hj')]
      have := hq j hj'
      have := h.addr _ (hjw j hj')
      simp only [Fits, size_encode_fields, USize.toNat_ofNat_of_lt' (hqu j hj')]
      omega
    have hg : GroupFits24 (encode A) 0 := groupFits24_zero A hA
    unfold loadColumnLines24 loadColumnsAt
    rw [dite_eq_left_of_eq_true (eq_true ⟨hfit 0 (by decide), hfit 1 (by decide),
      hfit 2 (by decide), hfit 3 (by decide), hfit 4 (by decide), hfit 5 (by decide),
      hfit 6 (by decide), hfit 7 (by decide), hfit 8 (by decide), hfit 9 (by decide),
      hfit 10 (by decide), hfit 11 (by decide), hfit 12 (by decide), hfit 13 (by decide),
      hfit 14 (by decide), hfit 15 (by decide), hg⟩)]
    have he : ∀ j < 16, cs.getD (16 * blk + j) .empty = encode (C (16 * blk + j)) :=
      fun j hj' ↦ h.enc _ (hjw j hj')
    have ho : ∀ j < 16, os.getD (16 * blk + j) 0 + r0 = o (16 * blk + j) + r0 :=
      fun j hj' ↦ by rw [h.off _ (hjw j hj')]
    simp only [he 0 (by decide), he 1 (by decide), he 2 (by decide), he 3 (by decide),
      he 4 (by decide), he 5 (by decide), he 6 (by decide), he 7 (by decide), he 8 (by decide),
      he 9 (by decide), he 10 (by decide), he 11 (by decide), he 12 (by decide),
      he 13 (by decide), he 14 (by decide), he 15 (by decide), ho 0 (by decide),
      ho 1 (by decide), ho 2 (by decide), ho 3 (by decide), ho 4 (by decide), ho 5 (by decide),
      ho 6 (by decide), ho 7 (by decide), ho 8 (by decide), ho 9 (by decide), ho 10 (by decide),
      ho 11 (by decide), ho 12 (by decide), ho 13 (by decide), ho 14 (by decide),
      ho 15 (by decide)]
    rw [loadColumns24_encode (fun j ↦ C (16 * blk + j)) (fun j ↦ o (16 * blk + j) + r0)
      (fun j hj' ↦ USize.toNat_ofNat_of_lt' (hqu j hj'))]
    have hL : ∀ j ∈ coords16, j < 24 := fun j hj ↦ by have := coords16_spec.lt j hj; omega
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [spliceRows, USize.toNat_zero, (foldl_splice_rows 24 _ 0 coords16 hL A (by rw [hA])).1,
        hA]
    · intro l hl
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      ext j hj
      simp only [lane, Vector.getElem_ofFn, CompStark.Hash.overwrite, Fin.getElem_fin, getD_block,
        hcnt]
      rw [word, spliceRows, USize.toNat_zero,
        (foldl_splice_rows 24 _ 0 coords16 hL A (by rw [hA])).2.1 j hj l hl]
      by_cases hj16 : j < 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (coords16_spec.mem j hj16)),
          ite_eq_left_of_eq_true _ _ (eq_true hj16), Nat.add_assoc (o _),
          Nat.add_assoc ((r0 + l) * w), hM _ _ (by omega) (hjw j hj16)]
      · rw [ite_eq_right_of_eq_false _ _
          (eq_false fun h ↦ hj16 (coords16_spec.lt j h)), ite_eq_right_of_eq_false _ _
              (eq_false hj16)]
  · refine ⟨A', e, by rw [s, hA], fun l hl ↦ ?_⟩
    ext j hj
    simp only [lane, Vector.getElem_ofFn]
    rw [wl l hl j (by omega)]
    split_ifs with h1 h2
    · simp only [CompStark.Hash.overwrite, Vector.getElem_ofFn, getD_block, h1.2, ↓reduceIte]
    · omega
    · have hn : ¬j < min 16 (w - 16 * blk) := by omega
      simp only [CompStark.Hash.overwrite, Vector.getElem_ofFn, getD_block, hn, ↓reduceIte,
        Fin.getElem_fin]
    · simp only [Vector.getElem_ofFn]

/-- `g` groups each folded over the blocks, side by side: every block modifies every group in
turn. -/
theorem foldRange_modify {α : Type} (f : Nat → Nat → α → α) (g B : Nat) (a : α) :
    foldRange (fun (sts : Array α) blk ↦ foldRange (fun (sts : Array α) k ↦ sts.modify k
        (f blk k)) g 0 sts) B 0 (Array.replicate g a) =
      Array.ofFn (n := g) fun k ↦ foldRange (fun st blk ↦ f blk k st) B 0 a := by
  have inner : ∀ (blk : Nat) (X : Array α) (hX : X.size = g), ∀ m ≤ g,
      (List.range m).foldl (fun (sts : Array α) k ↦ sts.modify k (f blk k)) X =
        Array.ofFn (n := g) fun k ↦ if k.val < m then f blk k (X[k.val]'(hX ▸ k.isLt))
          else X[k.val]'(hX ▸ k.isLt) := by
    intro blk X hX m hm
    induction m with
    | zero =>
      rw [List.range_zero, List.foldl_nil]
      apply Array.ext (by rw [Array.size_ofFn, hX])
      intro k h1 h2
      simp only [Array.getElem_ofFn, Nat.not_lt_zero, ↓reduceIte]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      apply Array.ext (by rw [Array.size_modify, Array.size_ofFn, Array.size_ofFn])
      intro k h1 h2
      rw [Array.getElem_modify, Array.getElem_ofFn, Array.getElem_ofFn]
      simp only [Array.size_ofFn] at h2
      by_cases hk : m = k
      · subst hk
        simp only [↓reduceIte, Nat.lt_irrefl, Nat.lt_succ_self]
      · dsimp only
        split_ifs <;> first | rfl | omega
  rw [foldRange_eq]
  have outer : ∀ b, (List.range b).foldl (fun (sts : Array α) blk ↦ foldRange (fun sts k ↦
        sts.modify k (f blk k)) g 0 sts) (Array.replicate g a) =
      Array.ofFn (n := g) fun k ↦ (List.range b).foldl (fun st blk ↦ f blk k st) a := by
    intro b
    induction b with
    | zero =>
      rw [List.range_zero, List.foldl_nil]
      apply Array.ext (by rw [Array.size_ofFn, Array.size_replicate])
      intro k h1 h2
      simp only [Array.getElem_replicate, Array.getElem_ofFn, List.foldl_nil]
    | succ b ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, foldRange_eq,
        inner b _ Array.size_ofFn g le_rfl]
      apply Array.ext (by rw [Array.size_ofFn, Array.size_ofFn])
      intro k h1 h2
      simp only [Array.getElem_ofFn, Array.size_ofFn] at h1 ⊢
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), List.foldl_append, List.foldl_cons,
        List.foldl_nil]
  rw [outer]
  apply Array.ext (by rw [Array.size_ofFn, Array.size_ofFn])
  intro k h1 h2
  rw [Array.getElem_ofFn, Array.getElem_ofFn, foldRange_eq]

theorem absorbColumns_eq [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (cs : Array ByteArray)
    (os : Array Nat) (w rows r0 g : Nat) :
    absorbColumns p cs os w rows r0 g = Array.ofFn (n := g) fun k ↦ foldRange (fun st blk ↦
      PackedPoseidon2.permute24 p (absorbColumnsBlock cs os w rows (r0 + 8 * k.val) blk st))
        ((w + 15) / 16) 0 (zeroWords 192) := by
  have hb : ∀ blk sts, absorbBlockGroups p cs os w rows r0 blk g sts =
      foldRange (fun (sts : Array ByteArray) k ↦ sts.modify k fun st ↦
        PackedPoseidon2.permute24 p (absorbColumnsBlock cs os w rows (r0 + 8 * k) blk st)) g 0
          sts := by
    intro blk sts
    unfold absorbBlockGroups absorbColumnsBlock
    split
    · rename_i hw
      dsimp only
      congr 1
      funext sts k
      congr 1
      funext st
      congr 1
      by_cases hr : r0 + 8 * k + 8 ≤ rows
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hr),
          ite_eq_left_of_eq_true _ _ (eq_true ⟨hr, hw⟩)]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hr),
          ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hr h.1)]
    · rename_i hw
      congr 1
      funext sts k
      congr 1
      funext st
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hw h.2)]
  unfold absorbColumns
  simp only [hb]
  exact foldRange_modify (fun blk k st ↦
    PackedPoseidon2.permute24 p (absorbColumnsBlock cs os w rows (r0 + 8 * k) blk st)) _ _ _

theorem absorbGroup_encode [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    {cs : Array ByteArray} {os : Array Nat} {C : Nat → Array F} {o : Nat → Nat} {w rows : Nat}
    (h : ColumnsOk cs os C o w rows) (r0 : Nat) :
    ∃ A, foldRange (fun st blk ↦ PackedPoseidon2.permute24 p
        (absorbColumnsBlock cs os w rows r0 blk st)) ((w + 15) / 16) 0 (zeroWords 192) =
          encode A ∧
      A.size = 192 ∧ ∀ l < 8, r0 + l < rows → lane 24 A 0 l =
        CompStark.Hash.absorb (permute ((Poseidon2Field.params24 : Params (FastField p) 24))) 16
            (by decide) (Vector.replicate 24 0)
          ((⟨w, rows, colMatrix C o w rows⟩ : CompStark.Merkle.Matrix F).row (r0 + l)) := by
  have key : ∀ b, ∃ A, (List.range b).foldl (fun st blk ↦
      PackedPoseidon2.permute24 p (absorbColumnsBlock cs os w rows r0 blk st))
      (encode (Array.replicate 192 (0 : F))) = encode A ∧ A.size = 192 ∧
      ∀ l < 8, r0 + l < rows → lane 24 A 0 l = (List.range b).foldl (fun s blk ↦
        permute ((Poseidon2Field.params24 : Params (FastField p) 24)) (CompStark.Hash.overwrite s
          ((((⟨w, rows, colMatrix C o w rows⟩ : CompStark.Merkle.Matrix F).row (r0 + l)).drop
            (16 * blk)).take 16)))
        (Vector.replicate 24 0) := by
    intro b
    induction b with
    | zero =>
      refine ⟨_, rfl, Array.size_replicate, fun l hl _ ↦ ?_⟩
      ext j hj
      simp only [List.range_zero, List.foldl_nil, lane, Vector.getElem_ofFn, word,
        Vector.getElem_replicate, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split_ifs <;> rfl
    | succ b ih =>
      obtain ⟨A, e, hs, hprev⟩ := ih
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [e]
      obtain ⟨A1, e1, s1, l1⟩ := absorbColumnsBlock_encode h A r0 b hs
      rw [e1]
      obtain ⟨A2, e2, s2, l2⟩ := permute24_lanes A1 s1
      refine ⟨A2, e2, s2, fun l hl hr ↦ ?_⟩
      rw [l2 l hl, l1 l hl, ite_eq_left_of_eq_true _ _ (eq_true hr), hprev l hl hr,
        block_eq _ _ rows]
  obtain ⟨A, e, hs, hl⟩ := key ((w + 15) / 16)
  refine ⟨A, by rw [foldRange_eq, zeroWords_fields (p := p), e], hs, fun l h8 hr ↦ ?_⟩
  rw [hl l h8 hr, absorb_eq_foldl]
  simp only [CompStark.Merkle.Matrix.row, List.length_map, List.length_range,
    show w + 16 - 1 = w + 15 by omega]

/-- **The leaves of a matrix given by its columns** are the digests of its rows. -/
theorem hashColumns_encode [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    {cs : Array ByteArray} {os : Array Nat} {C : Nat → Array F} {o : Nat → Nat} {w n : Nat}
    (h : ColumnsOk cs os C o w n) (ho : 4 * (8 * n) < USize.size) :
    hashColumns p cs os w n = encode (flat ((List.range n).map fun r ↦
      Hash.Poseidon2.hash (FastField p)
        ((⟨w, n, colMatrix C o w n⟩ : CompStark.Merkle.Matrix F).row r))) := by
  have key : ∀ K ≤ (n + 7) / 8, ∃ D, (List.range K).foldl (fun out k ↦ storeRows
      ((Array.ofFn (n := (n + 7) / 8) fun k ↦ foldRange (fun st blk ↦ PackedPoseidon2.permute24 p
        (absorbColumnsBlock cs os w n (0 + 8 * k.val) blk st)) ((w + 15) / 16) 0
          (zeroWords 192)).getD k .empty) n (8 * k) out)
      (encode (Array.replicate (8 * n) (0 : F))) = encode D ∧ D.size = 8 * n ∧
      ∀ r < n, ∀ j (hj : j < 8), D.getD (8 * r + j) 0 = if r < 8 * K then
        (Hash.Poseidon2.hash (FastField p)
          ((⟨w, n, colMatrix C o w n⟩ : CompStark.Merkle.Matrix F).row r))[j]'hj
        else 0 := by
    intro K hK
    induction K with
    | zero =>
      refine ⟨_, rfl, Array.size_replicate, fun r hr j hj ↦ ?_⟩
      rw [ite_eq_right (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_replicate,
        ite_eq_left (by omega)]
      rfl
    | succ K ih =>
      obtain ⟨D, e, s, g⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, e, List.foldl_cons, List.foldl_nil,
        Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
      simp only [show K < (n + 7) / 8 by omega, ↓reduceDIte, Option.getD_some]
      obtain ⟨A, eA, sA, lA⟩ := absorbGroup_encode (p := p) h (0 + 8 * K)
      rw [eA]
      obtain ⟨D', e', s', g'⟩ := storeRows_encode A D n (8 * K) (by omega)
        (by rw [sA]; have := USize.le_size; omega) s (by rw [s]; exact ho)
      refine ⟨D', e', s', fun r hr j hj ↦ ?_⟩
      rw [g']
      by_cases hG : 8 * K ≤ r ∧ r < 8 * K + 8
      · have hl := lA (r - 8 * K) (by omega) (by omega)
        rw [show 0 + 8 * K + (r - 8 * K) = r by omega] at hl
        rw [ite_eq_left (by omega), ite_eq_left (by omega), getElem_hash _ _ hj, ← hl,
          show (8 * r + j) % 8 = j by omega,
          show (8 * r + j) / 8 - 8 * K = r - 8 * K by omega]
        simp only [lane, Vector.getElem_ofFn]
      · rw [ite_eq_right (by omega), g r hr j hj]
        split_ifs <;> first | rfl | omega
  obtain ⟨D, e, s, g⟩ := key ((n + 7) / 8) le_rfl
  unfold hashColumns
  dsimp only
  rw [absorbColumns_eq, foldRange_eq, zeroWords_fields (p := p) (8 * n), e,
    flat_eq D ((List.range n).map fun r ↦ Hash.Poseidon2.hash (FastField p)
    ((⟨w, n, colMatrix C o w n⟩ : CompStark.Merkle.Matrix F).row r))
    (by rw [s, List.length_map, List.length_range])]
  intro r hr j hj
  rw [List.length_map, List.length_range] at hr
  rw [g r hr j hj, ite_eq_left (by omega),
    List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hr)]
  simp only [List.getElem_map, List.getElem_range]

end CompStark.Merkle.Packed
