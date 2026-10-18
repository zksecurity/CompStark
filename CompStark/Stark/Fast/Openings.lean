/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Commit
public import CompStark.Stark.Fast.OpeningsSpec
public import CompStark.Stark.Fast.BatchInv
public import CompStark.Stark.Fast.Norm
public import CompStark.Stark.Fast.WordsLemmas
public import CompPoly.Univariate.NTTFast.Permutation
public import CompPoly.Univariate.NTTFast.Packed.BitReversal
public import CompPoly.Univariate.NTTFast.Packed.CosetLdeTransposes
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The fast opened values are the specification's

Coordinate by coordinate, the specification's opened value of a column is a sum over the
natural-order rows `i` of the stored row `bitrev i` times the barycentric weight of the `i`-th
coset point (`openedAt_coord`). Reindexed through the involution `bitrev`, it is the sum over the
stored rows of the row times the weight of its stored point, which the fast kernel computes by
parallel ranges.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTT.Transform (bitRevNat bitRevNat_lt bitRevNat_involutive)
open KoalaBear.Fast (Ext4)

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-! ### Coordinates -/

/-- Coordinate `c` of an extension element. -/
def coord (c : Nat) (a : EF) : F :=
  match c with
  | 0 => a.c0
  | 1 => a.c1
  | 2 => a.c2
  | _ => a.c3

theorem coord_add (c : Nat) (a b : EF) : coord c (a + b) = coord c a + coord c b := by
  match c with
  | 0 | 1 | 2 | _ + 3 => rfl

theorem coord_smul (c : Nat) (x : F) (a : EF) : coord c (Ext4.smul x a) = x * coord c a := by
  match c with
  | 0 | 1 | 2 | _ + 3 => rfl

theorem coord_zero (c : Nat) : coord c (0 : EF) = 0 := by
  match c with
  | 0 | 1 | 2 | _ + 3 => rfl

theorem ext_coord {a b : EF} (h : ∀ c < 4, coord c a = coord c b) : a = b :=
  Norm.ext (h 0 (by decide)) (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))

/-- Coordinate `c` of a sum of scaled elements is the sum of the scaled coordinates. -/
theorem coord_foldl_smul (f : Nat → F) (g : Nat → EF) (c : Nat) (acc : EF) : ∀ n,
    coord c ((List.range' 0 n).foldl (fun acc i ↦ acc + Ext4.smul (f i) (g i)) acc) =
      coord c acc + ∑ i ∈ Finset.range n, f i * coord c (g i)
  | 0 => by rw [List.range'_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | n + 1 => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, coord_add,
      coord_foldl_smul f g c acc n, Finset.sum_range_succ, coord_smul, Nat.zero_add, Nat.one_mul,
      add_assoc]

/-! ### Bit reversal -/

theorem size_bitRevPerm : ∀ b, (bitRevPerm b).size = 2 ^ b
  | 0 => rfl
  | b + 1 => by
    rw [bitRevPerm, Array.size_append, Array.size_map, Array.size_map, size_bitRevPerm b,
      Nat.pow_succ]
    omega

theorem bitRevPerm_getD : ∀ b i, i < 2 ^ b → (bitRevPerm b).getD i 0 = bitRevNat b i
  | 0, i, hi => by
    rw [show i = 0 by rw [Nat.pow_zero] at hi; omega]
    rfl
  | b + 1, i, hi => by
    have hs := size_bitRevPerm b
    rw [bitRevPerm, Array.getD_eq_getD_getElem?, Array.getElem?_append]
    have hc := CompPoly.CPolynomial.NTTFast.Packed.bitRevNat_concat 1 b
    rw [Nat.add_comm 1 b] at hc
    split
    · rename_i h
      rw [Array.size_map] at h
      have e := bitRevPerm_getD b i (by omega)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some] at e
      rw [Array.getElem?_map, Array.getElem?_eq_getElem h, Option.map_some, Option.getD_some, e]
      have := hc 0 i (by omega)
      rw [Nat.mul_zero, Nat.zero_add] at this
      rw [this]
      rfl
    · rename_i h
      rw [Array.size_map] at h
      have hi' : i - (bitRevPerm b).size < 2 ^ b := by rw [Nat.pow_succ] at hi; omega
      rw [Array.size_map, Array.getElem?_map, Array.getElem?_eq_getElem (by omega),
        Option.map_some, Option.getD_some]
      have e := bitRevPerm_getD b (i - (bitRevPerm b).size) hi'
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
        Option.getD_some] at e
      rw [e]
      have := hc 1 (i - (bitRevPerm b).size) hi'
      rw [hs, Nat.mul_one, Nat.add_sub_cancel' (by omega)] at this
      rw [this, hs]
      rfl

theorem bitRevNat_lt_of (b : Nat) (i : Nat) : bitRevNat b i < 2 ^ b := bitRevNat_lt b i

/-- Stored row `r` holds the coset point `bitrev r`. -/
theorem cosetPointsBitRev_getD (shift : F) (b r : Nat) (hr : r < 2 ^ b) :
    (cosetPointsBitRev shift b).getD r 0 = (cosetPoints shift b).getD (bitRevNat b r) 0 := by
  rw [cosetPointsBitRev, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem (by rw [size_bitRevPerm]; exact hr), Option.map_some,
    Option.getD_some]
  have e := bitRevPerm_getD b r hr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [size_bitRevPerm]; exact hr),
    Option.getD_some] at e
  rw [e]

theorem size_cosetPointsBitRev (shift : F) (b : Nat) :
    (cosetPointsBitRev shift b).size = 2 ^ b := by
  rw [cosetPointsBitRev, Array.size_map, size_bitRevPerm]

/-! ### The specification's opened values -/

/-- The extension element of four coordinates. -/
def mk4 (f : Nat → F) : EF := ⟨f 0, f 1, f 2, f 3⟩

theorem coord_mk4 (f : Nat → F) (c : Nat) (hc : c < 4) : coord c (mk4 f) = f c := by
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- The barycentric weight `x / (z - x)`. -/
def bw (z : EF) (x : F) : EF := Ext4.smul x (z - Ext4.ofBase x)⁻¹

theorem nonBase_iff (z : EF) : nonBase z = true ↔ z.c1 ≠ 0 ∨ z.c2 ≠ 0 ∨ z.c3 ≠ 0 := by
  simp only [nonBase, Bool.or_eq_true, bne_iff_ne, ne_eq, or_assoc]

theorem sub_ofBase_ne_zero {z : EF} (hz : nonBase z = true) (x : F) :
    Ext4.toSpec (z - Ext4.ofBase x) ≠ 0 := by
  refine Norm.toSpec_ne_zero fun h ↦ ?_
  have h1 := congrArg Ext4.c1 h
  have h2 := congrArg Ext4.c2 h
  have h3 := congrArg Ext4.c3 h
  simp only [Norm.sub_c1, Norm.sub_c2, Norm.sub_c3, Ext4.ofBase, sub_zero] at h1 h2 h3
  rcases (nonBase_iff z).mp hz with h | h | h
  · exact h h1
  · exact h h2
  · exact h h3

theorem baryWeights_getD {z : EF} (hz : nonBase z = true) (logH i : Nat) (hi : i < 2 ^ logH) :
    (baryWeights logH z).getD i 0 = bw z ((cosetPoints gen logH).getD i 0) := by
  have hb := batchInv_eq Ext4.toSpec Ext4.toSpec_injective Ext4.toSpec_mul Ext4.toSpec_inv
    Ext4.toSpec_one ((cosetPoints gen logH).map fun x ↦ z - Ext.ofBase x) (fun y hy ↦ by
      obtain ⟨x, -, rfl⟩ := Array.mem_map.mp hy
      exact sub_ofBase_ne_zero hz x)
  have hs := size_cosetPoints gen logH
  rw [baryWeights, hb, Array.getD_eq_getD_getElem?, Array.getElem?_zipWith,
    Array.getElem?_map, Array.getElem?_map, Array.getElem?_eq_getElem (by omega), Option.map_some,
    Option.map_some, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
  rfl

/-- A column sum of the specification, coordinate by coordinate, reindexed to the stored rows. -/
theorem coord_colSum (values : Array F) (w L j : Nat) {z : EF} (hz : nonBase z = true) (c : Nat) :
    coord c (colSum values (bitRevPerm L) (baryWeights L z) w (2 ^ L) j) =
      ∑ r ∈ Finset.range (2 ^ L), values.getD (r * w + j) 0 *
        coord c (bw z ((cosetPointsBitRev gen L).getD r 0)) := by
  rw [colSum, coord_foldl_smul, coord_zero, zero_add]
  refine Finset.sum_nbij' (bitRevNat L) (bitRevNat L) (fun i _ ↦ ?_) (fun i _ ↦ ?_)
    (fun i hi ↦ ?_) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
  · exact Finset.mem_range.mpr (bitRevNat_lt L i)
  · exact Finset.mem_range.mpr (bitRevNat_lt L i)
  · exact bitRevNat_involutive L i (Finset.mem_range.mp hi)
  · exact bitRevNat_involutive L i (Finset.mem_range.mp hi)
  · have hi := Finset.mem_range.mp hi
    rw [bitRevPerm_getD L i hi, baryWeights_getD hz L i hi,
      cosetPointsBitRev_getD _ _ _ (bitRevNat_lt L i), bitRevNat_involutive L i hi]

/-- The specification's opened values, coordinate by coordinate a sum over the stored rows of
the row times the weight of its stored point. -/
theorem openedAt_sum (b : Nat) (s : Mat) {z : EF} (hz : nonBase z = true) :
    Fri.openedAt b s z = Array.ofFn (n := s.width) fun j ↦
      KoalaBear.Fast.cosetFactor (Nat.log2 s.height - b) gen z * mk4 fun c ↦
        ∑ r ∈ Finset.range (2 ^ (Nat.log2 s.height - b)), s.values.getD (r * s.width + j.val) 0 *
          coord c (bw z ((cosetPointsBitRev gen (Nat.log2 s.height - b)).getD r 0)) := by
  rw [openedAt_eq]
  refine Array.ext (by rw [Array.size_ofFn, Array.size_ofFn]) fun j h1 h2 ↦ ?_
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  exact congrArg _ (ext_coord fun c hc ↦ by rw [coord_mk4 _ _ hc, coord_colSum _ _ _ _ hz])

/-! ### Inverses by the norm on words -/

theorem mulAddWords_ofFn {n : Nat} (hn : 4 * n < USize.size) (f g : Fin n → F) (c : F) :
    Words.mulAddWords (encode (Array.ofFn f)) (encode (Array.ofFn g)) c.val n =
      encode (Array.ofFn fun i ↦ f i + g i * c) := by
  rw [Words.mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn])
    (by rw [Array.size_ofFn]; exact hn) (by rw [Array.size_ofFn]; exact hn)]
  refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
  rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt,
    CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt]

theorem replicateWord_ofFn {n : Nat} (hn : 4 * n < USize.size) (c : F) :
    Words.replicateWord c.val n = encode (Array.ofFn (n := n) fun _ ↦ c) := by
  rw [Words.replicateWord_encode _ _ hn]
  refine congrArg encode (Array.ext (by rw [Array.size_ofFn, Array.size_replicate]) ?_)
  intro i _ _
  simp only [Array.getElem_ofFn, Array.getElem_replicate]

theorem batchInvWords_ofFn {n : Nat} (hn : 4 * n < USize.size) (f : Fin n → F)
    (hf : ∀ i, f i ≠ 0) :
    batchInvWords (encode (Array.ofFn f)) n = encode (Array.ofFn fun i ↦ (f i)⁻¹) := by
  rw [batchInvWords_encode _ _ (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn]; exact hn)
    fun k hk ↦ by rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hk]; exact hf _]
  refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
  rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt]

theorem encode_ofFn_getElem (X : Array F) :
    encode X = encode (Array.ofFn (n := X.size) fun i ↦ X[i.val]) := by
  rw [Array.ofFn_getElem]

/-- `invDenoms` inverts `z - x` for every base point `x`, for `z` outside the base field. -/
theorem invDenoms_rel {z : EF} (hz : nonBase z = true) (X : Array F)
    (hs : 4 * X.size < USize.size) :
    RV (invDenoms z (encode X) X.size) (X.map fun x ↦ (z - Ext4.ofBase x)⁻¹) := by
  have hz' := (nonBase_iff z).mp hz
  simp only [invDenoms]
  rw [encode_ofFn_getElem X]
  simp only [EVec.mulWords_ofFn hs, EVec.addWords_ofFn hs, mulAddWords_ofFn hs,
    replicateWord_ofFn hs, ite_true, Bool.false_eq_true, ite_false]
  rw [batchInvWords_ofFn hs _ ?_]
  · simp only [EVec.mulWords_ofFn hs]
    refine EVec.rv_ofFn _ (Array.size_map ..) _ _ _ _ fun i ↦ ?_
    rw [Array.getElem_map, Norm.inv_eq hz']
    apply Norm.ext <;>
      simp only [KoalaBear.Fast.Ext4.smul, Norm.cubic, Norm.norm, Norm.e1, Norm.e2, Norm.e3,
        Norm.conj] <;> ring
  · intro i
    have := Norm.norm_ne_zero hz' X[i.val]
    simp only [Norm.norm, Norm.e1, Norm.e2, Norm.e3, Norm.conj] at this
    convert this using 1
    ring

/-! ### The fast column sums -/

open CompPoly.CPolynomial.NTTFast.Packed (getD_ofFn_bounded size_encode_fields)
open CompPoly.CPolynomial.NTTFast.Packed.Native (write zeroWords transposeRows)

/-- Words `0, …, w - 1` written in order. -/
theorem writeAll_eq (f : Nat → F) (g : Nat → UInt32) (w : Nat) (hw : 4 * w < USize.size)
    (hg : ∀ j < w, g j = (f j).val) :
    (List.range' 0 w).foldl (fun b j ↦ write b j (g j)) (zeroWords w) =
      encode (Array.ofFn (n := w) fun j ↦ f j.val) := by
  rw [Words.zeroWords_eq, ← Words.upto_zero (Array.replicate w 0) f,
    Words.foldl_tail _ _ _ _ _ (fun k _ hk ↦ by
      rw [hg k (by omega)]
      exact Words.write_upto _ f k (by rw [Array.size_replicate]; omega)
        (by rw [Array.size_replicate]; omega)),
    Nat.zero_add, Words.upto_full _ _ _ (Array.size_replicate ..)]

theorem transposeRows_encode (M : Array F) (w r0 rows : Nat) (hM : (r0 + rows) * w ≤ M.size)
    (hs : 4 * M.size < USize.size) :
    transposeRows (encode M) w r0 rows = encode (Array.ofFn (n := w * rows) fun k ↦
      M.getD ((r0 + k.val % rows) * w + k.val / rows) 0) := by
  rw [CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val M,
    CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows_encodeWords _ _ _ _
      (by rw [Array.size_map]; exact hM) (by rw [Array.size_map]; exact hs),
    CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val]
  refine congrArg encode (Array.ext (by rw [Array.size_map, Array.size_ofFn, Array.size_ofFn])
    fun k _ _ ↦ ?_)
  rw [Array.getElem_map, Array.getElem_ofFn, Array.getElem_ofFn,
    CompPoly.CPolynomial.NTTFast.Packed.getD_map_val]

theorem mul_ofBase (a : EF) (x : F) : a * Ext4.ofBase x = Ext4.smul x a := by
  apply Norm.ext <;>
    simp only [Norm.mul_c0, Norm.mul_c1, Norm.mul_c2, Norm.mul_c3, Ext4.ofBase, Ext4.smul] <;>
    ring

/-- The weight planes of a range of stored points. -/
theorem weightPlane {z : EF} (hz : nonBase z = true) (X : Array F) (r0 len : Nat)
    (hX : r0 + len ≤ X.size) (hs : 4 * X.size < USize.size) :
    #[((invDenoms z (slice (encode X) r0 len) len).mulBase (slice (encode X) r0 len)).c0,
      ((invDenoms z (slice (encode X) r0 len) len).mulBase (slice (encode X) r0 len)).c1,
      ((invDenoms z (slice (encode X) r0 len) len).mulBase (slice (encode X) r0 len)).c2,
      ((invDenoms z (slice (encode X) r0 len) len).mulBase (slice (encode X) r0 len)).c3] =
    Array.ofFn (n := 4) fun c ↦ encode (Array.ofFn (n := len)
      fun t ↦ coord c (bw z (X.getD (r0 + t.val) 0))) := by
  have hxr : slice (encode X) r0 len = encode (X.extract r0 (r0 + len)) :=
    extract_encode X r0 (r0 + len)
  have hsz : (X.extract r0 (r0 + len)).size = len := by rw [Array.size_extract]; omega
  have hs' : 4 * (X.extract r0 (r0 + len)).size < USize.size := by omega
  have hrv := EVec.mulBase_rel (X.extract r0 (r0 + len))
    (invDenoms_rel hz (X.extract r0 (r0 + len)) hs') (by rw [Array.size_map]) hs'
  rw [hsz] at hrv
  obtain ⟨-, h0, h1, h2, h3⟩ := hrv
  have hp (c : Nat) : encode ((Array.zipWith (fun x y ↦ x * Ext.ofBase y)
      ((X.extract r0 (r0 + len)).map fun x ↦ (z - Ext4.ofBase x)⁻¹)
      (X.extract r0 (r0 + len))).map (coord c)) = encode (Array.ofFn (n := len)
      fun t ↦ coord c (bw z (X.getD (r0 + t.val) 0))) := by
    refine congrArg encode (Array.ext (by
      rw [Array.size_map, Array.size_zipWith, Array.size_map, Array.size_ofFn, hsz,
        Nat.min_self]) fun t h1 _ ↦ ?_)
    rw [Array.size_map, Array.size_zipWith, Array.size_map, hsz, Nat.min_self] at h1
    rw [Array.getElem_map, Array.getElem_zipWith, Array.getElem_map, Array.getElem_ofFn,
      Array.getElem_extract, mul_ofBase, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega), Option.getD_some]
    rfl
  rw [hxr]
  refine Array.ext (by rw [Array.size_ofFn]; rfl) fun c hc _ ↦ ?_
  rw [Array.getElem_ofFn, ← hp c]
  match c, hc with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3

/-- Appending four elements per item. -/
theorem foldl_append_ofFn4 {α : Type} (R : EF → Fin 4 → α) : ∀ (l : List EF) (b : Array α),
    l.foldl (fun b z ↦ b ++ Array.ofFn (R z)) b =
      b ++ Array.ofFn (n := 4 * l.length) fun i ↦ R (l.getD (i.val / 4) 0) ⟨i.val % 4, by omega⟩
  | [], b => by rw [List.foldl_nil, Array.eq_empty_of_size_eq_zero (xs := Array.ofFn _)
      (by rw [Array.size_ofFn]; rfl), Array.append_empty]
  | a :: l, b => by
    rw [List.foldl_cons, foldl_append_ofFn4 R l, Array.append_assoc]
    congr 1
    refine Array.ext (by rw [Array.size_append, Array.size_ofFn, Array.size_ofFn, Array.size_ofFn,
      List.length_cons]; omega) fun i h1 h2 ↦ ?_
    rw [Array.getElem_ofFn, Array.getElem_append]
    split
    · rename_i h
      rw [Array.size_ofFn] at h
      rw [Array.getElem_ofFn, show i / 4 = 0 by omega, List.getD_cons_zero]
      exact congrArg _ (Fin.ext (by simp only; omega))
    · rename_i h
      rw [Array.size_ofFn] at h
      simp only [Array.getElem_ofFn, Array.size_ofFn]
      congr 1
      · rw [show i / 4 = (i - 4) / 4 + 1 by omega, List.getD_cons_succ]
      · exact Fin.ext (by simp only; omega)

/-- One plane of column sums: column `j` of the transposed range dotted with a weight plane. -/
theorem colPlane_eq (M P : Array F) (w r0 len : Nat) (hM : (r0 + len) * w ≤ M.size)
    (hP : len ≤ P.size) (hsM : 4 * M.size < USize.size) (hsP : 4 * P.size < USize.size)
    (hw : 4 * w < USize.size) :
    (List.range' 0 w).foldl (fun b j ↦ write b j
      (Words.dotAt (transposeRows (encode M) w r0 len) (j * len) (encode P) len)) (zeroWords w) =
      encode (Array.ofFn (n := w) fun j ↦
        ∑ t ∈ Finset.range len, M.getD ((r0 + t) * w + j.val) 0 * P.getD t 0) := by
  have hwl : w * len ≤ M.size := by
    have := Nat.mul_le_mul_right w (Nat.le_add_left len r0)
    rw [Nat.mul_comm w len]; omega
  refine writeAll_eq (fun j ↦ ∑ t ∈ Finset.range len, M.getD ((r0 + t) * w + j) 0 * P.getD t 0)
    _ w hw fun j hj ↦ ?_
  rw [transposeRows_encode M w r0 len hM hsM, Words.dotAt_encode _ _ _ _
    (by rw [Array.size_ofFn]; have := Nat.mul_le_mul_right len (show j + 1 ≤ w by omega)
        rw [Nat.succ_mul] at this; exact this)
    hP (by rw [Array.size_ofFn]; omega) hsP]
  refine congrArg _ (Finset.sum_congr rfl fun t ht ↦ ?_)
  have ht := Finset.mem_range.mp ht
  rw [getD_ofFn_bounded _ _ (by
    have := Nat.mul_le_mul_right len (show j + 1 ≤ w by omega)
    rw [Nat.succ_mul] at this; omega)]
  simp only
  rw [Nat.add_comm (j * len) t, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht,
    Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]

/-- The fast column sums of a range of stored rows: for every point and coordinate, a plane of
`w` sums of the rows times the weights of their points. -/
theorem weightedColumns_encode (M : Array F) (w : Nat) (zs : Array EF)
    (hz : ∀ z ∈ zs, nonBase z = true) (X : Array F) (r0 len : Nat)
    (hM : (r0 + len) * w ≤ M.size) (hX : r0 + len ≤ X.size) (hsM : 4 * M.size < USize.size)
    (hsX : 4 * X.size < USize.size) (hw : 4 * w < USize.size) :
    weightedColumns (encode M) w zs (encode X) r0 len =
      Array.ofFn (n := 4 * zs.size) fun i ↦ encode (Array.ofFn (n := w) fun j ↦
        ∑ t ∈ Finset.range len, M.getD ((r0 + t) * w + j.val) 0 *
          coord (i.val % 4) (bw (zs.toList.getD (i.val / 4) 0) (X.getD (r0 + t) 0))) := by
  simp only [Fast.weightedColumns, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl, pure_bind, bind_pure,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← Array.foldl_toList, List.foldl_ext _ (fun b z ↦ b ++ Array.ofFn (n := 4) fun c ↦
    encode (Array.ofFn (n := w) fun j ↦ ∑ t ∈ Finset.range len,
      M.getD ((r0 + t) * w + j.val) 0 * coord c.val (bw z (X.getD (r0 + t) 0)))) _ ?_,
    foldl_append_ofFn4, Array.empty_append]
  · rfl
  intro b z hz'
  rw [weightPlane (hz z (Array.mem_toList_iff.mp hz')) X r0 len hX hsX,
    Array.foldl_push_eq_append rfl, Array.map_ofFn]
  refine congrArg (b ++ ·) (congrArg Array.ofFn (funext fun c ↦ ?_))
  simp only [Function.comp_apply]
  have hP : (Array.ofFn (n := len) fun t ↦ coord c.val (bw z (X.getD (r0 + t.val) 0))).size =
      len := Array.size_ofFn
  rw [colPlane_eq M _ w r0 len hM (by rw [hP]) hsM (by rw [hP]; omega) hw]
  refine congrArg encode (congrArg Array.ofFn (funext fun j ↦ Finset.sum_congr rfl fun t ht ↦ ?_))
  rw [getD_ofFn_bounded _ _ (Finset.mem_range.mp ht)]

theorem zip_map_addWords (N w : Nat) (hw : 4 * w < USize.size) (A B : Fin N → Fin w → F) :
    ((Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (A i))).zip
      (Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (B i)))).map
        (fun (a, b) ↦ Words.addWords a b w) =
      Array.ofFn (n := N) fun i ↦ encode (Array.ofFn fun j ↦ A i j + B i j) := by
  refine Array.ext (by rw [Array.size_map, Array.size_zip, Array.size_ofFn, Array.size_ofFn,
    Array.size_ofFn, Nat.min_self]) fun i h1 h2 ↦ ?_
  rw [Array.getElem_map, Array.getElem_zip, Array.getElem_ofFn, Array.getElem_ofFn,
    Array.getElem_ofFn]
  exact EVec.addWords_ofFn hw _ _

/-- Sums over parallel ranges of `h` rows, added plane by plane, are the sums over all rows. -/
theorem parts_sum (N w h parts : Nat) (hp : 0 < parts) (hw : 4 * w < USize.size)
    (g : Nat → Nat → Nat → F) (WC : Nat → Nat → Array ByteArray)
    (hWC : ∀ r0 len, r0 + len ≤ h → WC r0 len = Array.ofFn (n := N) fun i ↦
      encode (Array.ofFn (n := w) fun j ↦ ∑ t ∈ Finset.range len, g i j (r0 + t))) :
    ((Array.range parts).map fun k ↦ Task.spawn fun _ ↦
      WC (k * (h / parts)) (if k + 1 = parts then h - k * (h / parts) else h / parts)).foldl
        (fun acc t ↦ (acc.zip t.get).map fun (a, b) ↦ Words.addWords a b w)
        (Array.replicate N (zeroWords w)) =
      Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (n := w) fun j ↦
        ∑ r ∈ Finset.range h, g i j r) := by
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
  have hsz : parts * (h / parts) ≤ h := Nat.mul_div_le h parts
  generalize h / parts = sz at hsz ⊢
  have key : ∀ K ≤ parts, (List.range K).foldl (fun acc k ↦ (acc.zip (WC (k * sz)
      (if k + 1 = parts then h - k * sz else sz))).map
        fun (a, b) ↦ Words.addWords a b w) (Array.replicate N (zeroWords w)) =
      Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (n := w) fun j ↦
        ∑ r ∈ Finset.range (if K = parts then h else K * sz), g i j r) := by
    intro K
    induction K with
    | zero =>
      intro _
      rw [List.range_zero, List.foldl_nil, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        Nat.zero_mul]
      refine Array.ext (by rw [Array.size_replicate, Array.size_ofFn]) fun i _ _ ↦ ?_
      rw [Array.getElem_replicate, Array.getElem_ofFn, EVec.zeroWords_ofFn]
      rfl
    | succ K ih =>
      intro hK
      have hK' : K * sz + sz ≤ h := by
        have := Nat.mul_le_mul_right sz hK
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        ite_eq_right_of_eq_false _ _ (eq_false (show K ≠ parts by omega))]
      rw [hWC _ _ (by split <;> omega), zip_map_addWords N w hw]
      refine congrArg Array.ofFn (funext fun i ↦ congrArg encode
        (congrArg Array.ofFn (funext fun j ↦ ?_)))
      rw [← Finset.sum_range_add]
      congr 2
      by_cases hk : K + 1 = parts
      · simp only [hk, ite_true]; omega
      · simp only [hk, ite_false, Nat.add_mul, Nat.one_mul]
  have := key parts (Nat.le_refl _)
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at this
  exact this

/-- A word of a plane of tabulated sums. -/
theorem word_plane (n w : Nat) (G : Nat → Nat → F) (idx j : Nat) (hidx : idx < n) (hj : j < w)
    (hw : 4 * w < USize.size) :
    word ((Array.ofFn (n := n) fun i ↦ encode (Array.ofFn (n := w) fun j ↦ G i.val j.val)).getD
      idx .empty) j = G idx j := by
  rw [getD_ofFn_bounded _ _ hidx, word_encode_getD _ _ (by rw [Array.size_ofFn]; exact hw)
    (by omega), getD_ofFn_bounded _ _ hj]

theorem size_openedAt (b : Nat) (s : Mat) (z : EF) : (Fri.openedAt b s z).size = s.width := by
  rw [openedAt_eq, Array.size_ofFn]

/-- The fast opened values are the specification's. -/
theorem openedAt_rel (b : Nat) (zs : List KoalaBear.Fast.Ext4) {m : PMat} {s : Mat} (h : RM m s) :
    openedAt b m zs = zs.map (Fri.openedAt b s) := by
  unfold Fast.openedAt
  split
  · rw [toMat_of_RM h]
  rename_i hc
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
    not_or, Bool.not_eq_false, Nat.not_lt, List.all_eq_true] at hc
  obtain ⟨⟨hf, hz⟩, hle⟩ := hc
  have hM := values_size h hf
  obtain ⟨hw, hh, he⟩ := h
  have hfits := hf
  simp only [PMat.fits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfits
  rw [he, size_encode_fields] at hfits
  dsimp only
  rw [hh] at hle
  rw [hw, hh, he]
  generalize hL : Nat.log2 s.height - b = L at hle ⊢
  -- An empty row: both sides are empty.
  by_cases hw0 : s.width = 0
  · refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_zipIdx])
      fun k h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_map]
    refine Array.ext (by rw [Array.size_ofFn, size_openedAt, hw0]) fun j h1 _ ↦ ?_
    rw [Array.size_ofFn] at h1
    omega
  have hpos : 0 < s.height := lt_of_lt_of_le (Nat.two_pow_pos L) hle
  have hsM : 4 * s.values.size < USize.size := hfits.2
  have hX : (cosetPointsBitRev gen L).size = 2 ^ L := size_cosetPointsBitRev gen L
  have hw4 : 4 * s.width < USize.size := by
    have := Nat.mul_le_mul_left s.width (show 1 ≤ s.height from hpos)
    omega
  have hsX : 4 * (cosetPointsBitRev gen L).size < USize.size := by
    have := Nat.mul_le_mul_right s.height (show 1 ≤ s.width by omega)
    omega
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq]
  have hp : 0 < (if 2 ^ L < 4096 then 1 else 16) := by split <;> decide
  rw [parts_sum (4 * zs.length) s.width (2 ^ L) _ hp hw4
    (fun i j r ↦ s.values.getD (r * s.width + j) 0 *
      coord (i % 4) (bw (zs.getD (i / 4) 0) ((cosetPointsBitRev gen L).getD r 0)))
    (fun r0 len ↦ weightedColumns (encode s.values) s.width zs.toArray
      (encode (cosetPointsBitRev gen L)) r0 len) (fun r0 len hr ↦ ?_)]
  · refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_zipIdx])
      fun k h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [List.length_map, List.length_zipIdx] at h1
    rw [openedAt_sum b s (hz _ (List.getElem_mem _)), hL]
    have hwp : ∀ idx, idx < 4 * zs.length → ∀ j, j < s.width →
        word ((Array.ofFn (n := 4 * zs.length) fun i ↦ encode (Array.ofFn (n := s.width) fun j ↦
          ∑ r ∈ Finset.range (2 ^ L), s.values.getD (r * s.width + j.val) 0 * coord (i.val % 4)
            (bw (zs.getD (i.val / 4) 0) ((cosetPointsBitRev gen L).getD r 0)))).getD
          idx .empty) j =
        ∑ r ∈ Finset.range (2 ^ L), s.values.getD (r * s.width + j) 0 * coord (idx % 4)
          (bw (zs.getD (idx / 4) 0) ((cosetPointsBitRev gen L).getD r 0)) :=
      fun idx hidx j hj ↦ word_plane (4 * zs.length) s.width (fun i j ↦
        ∑ r ∈ Finset.range (2 ^ L), s.values.getD (r * s.width + j) 0 * coord (i % 4)
          (bw (zs.getD (i / 4) 0) ((cosetPointsBitRev gen L).getD r 0))) idx j hidx hj hw4
    refine congrArg Array.ofFn (funext fun j ↦ congrArg _ (Norm.ext ?_ ?_ ?_ ?_)) <;>
      dsimp only [mk4] <;>
      rw [hwp _ (by omega) _ j.isLt] <;>
      refine Finset.sum_congr rfl fun r _ ↦ ?_ <;>
      simp only [show (4 * k + 1) / 4 = k by omega, show (4 * k + 2) / 4 = k by omega,
        show (4 * k + 3) / 4 = k by omega, show 4 * k / 4 = k by omega,
        show (4 * k + 1) % 4 = 1 by omega, show (4 * k + 2) % 4 = 2 by omega,
        show (4 * k + 3) % 4 = 3 by omega, show 4 * k % 4 = 0 by omega,
        List.getD_eq_getElem _ _ h1]
  · rw [weightedColumns_encode s.values s.width zs.toArray
      (fun z hz' ↦ hz z (List.mem_toArray.mp hz'))
      _ r0 len (by
        rw [hM, Nat.mul_comm s.width]
        exact Nat.mul_le_mul_right s.width (show r0 + len ≤ s.height by omega))
      (by omega) hsM hsX hw4]
    rfl

/-! ### The specification's reduction row by row -/

/-- Row `r` of a matrix of width `w` batched by the powers `ap` of `α`. -/
def crow (V : Array F) (ap : Array EF) (w r : Nat) : EF :=
  (List.range' 0 w).foldl (fun acc i ↦ acc + Ext4.smul (V.getD (r * w + i) 0) (ap.getD i 0)) 0

theorem compress_eq (s : Mat) (ap : Array EF) :
    compress s ap = Array.ofFn (n := s.height) fun r ↦ crow s.values ap s.width r.val := by
  unfold compress
  refine parChunks_eq _ _ _ (fun r ↦ crow s.values ap s.width r) (fun r0 len _ ↦ ?_)
    (Or.inl (by split <;> decide))
  simp only [compressRows, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Nat.add_sub_cancel_left]
  have := foldl_push_range' (fun r ↦ crow s.values ap s.width r) r0 len
    (Array.emptyWithCapacity len)
  rw [Array.emptyWithCapacity_eq, Array.empty_append] at this
  exact this

/-- One point's term at a row: `offset · (yz - comp) / (z - x)`. -/
def termStep (comp : EF) (x : F) (acc : EF) (t : EF × EF × EF) : EF :=
  acc + t.2.2 * (t.2.1 - comp) * (t.1 - Ext4.ofBase x)⁻¹

theorem accumulateRows_eq (acc comp : Array EF) (xs : Array F) {z : EF} (hz : nonBase z = true)
    (yz offset : EF) (r0 len : Nat) (hr : r0 + len ≤ xs.size) :
    accumulateRows acc comp xs z yz offset r0 len = Array.ofFn (n := len) fun k ↦
      termStep (comp.getD (r0 + k.val) 0) (xs.getD (r0 + k.val) 0) (acc.getD (r0 + k.val) 0)
        (z, yz, offset) := by
  simp only [accumulateRows, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [batchInv_eq Ext4.toSpec Ext4.toSpec_injective Ext4.toSpec_mul Ext4.toSpec_inv
    Ext4.toSpec_one _ (fun y hy ↦ by
      obtain ⟨x, -, rfl⟩ := Array.mem_map.mp hy
      exact sub_ofBase_ne_zero hz x)]
  have := foldl_push_range' (fun k ↦ termStep (comp.getD (r0 + k) 0) (xs.getD (r0 + k) 0)
    (acc.getD (r0 + k) 0) (z, yz, offset)) 0 len (Array.emptyWithCapacity len)
  rw [Array.emptyWithCapacity_eq, Array.empty_append] at this
  simp only [Nat.zero_add] at this
  rw [← this]
  refine List.foldl_ext _ _ _ fun b k hk ↦ ?_
  have hk := (List.mem_range'_1.mp hk).2
  rw [Nat.zero_add] at hk
  refine congrArg b.push ?_
  have e : ((Array.map (fun x ↦ x⁻¹) (Array.map (fun x ↦ z - Ext.ofBase x)
      (xs.extract r0 (r0 + len)))).getD k 0) = (z - Ext4.ofBase (xs.getD (r0 + k) 0))⁻¹ := by
    have hx : k < (xs.extract r0 (r0 + len)).size := by rw [Array.size_extract]; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_map,
      Array.getElem?_eq_getElem hx, Array.getElem_extract, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show r0 + k < xs.size by omega)]
    rfl
  rw [e]
  rfl

/-- The batched opened value of a point: `∑ᵢ αⁱ ys[i]`. -/
def yzOf (ap : Array EF) (w : Nat) (ys : Array EF) : EF :=
  (List.range w).foldl (fun s i ↦ s + ap.getD i 0 * ys.getD i 0) 0

/-- The points of a matrix with their batched values and offsets `α ^ cnt`, `cnt` stepping by the
width: the fast reduction's terms. -/
def termsStep (alpha : EF) (ap : Array EF) (w : Nat) (b : Nat × List (EF × EF × EF))
    (p : EF × Array EF) : Nat × List (EF × EF × EF) :=
  (b.1 + w, b.2 ++ [(p.1, yzOf ap w p.2, Ext.pow alpha b.1)])

theorem foldl_termsStep (alpha : EF) (ap : Array EF) (w : Nat) :
    ∀ (pts : List (EF × Array EF)) (c : Nat) (T : List (EF × EF × EF)),
      pts.foldl (termsStep alpha ap w) (c, T) =
        ((pts.foldl (termsStep alpha ap w) (c, [])).1,
          T ++ (pts.foldl (termsStep alpha ap w) (c, [])).2)
  | [], c, T => by rw [List.foldl_nil, List.foldl_nil, List.append_nil]
  | p :: pts, c, T => by
    rw [List.foldl_cons, List.foldl_cons, termsStep, termsStep,
      foldl_termsStep alpha ap w pts _ (T ++ _), foldl_termsStep alpha ap w pts _ ([] ++ _),
      List.nil_append, List.append_assoc]

theorem parChunks_accumulate (n : Nat) (f : Nat → EF) (comp : Array EF) (xs : Array F)
    (hxs : n ≤ xs.size) {z : EF} (hz : nonBase z = true) (yz offset : EF) :
    parChunks n (if n < 4096 then 1 else 16) (fun r0 len ↦
      accumulateRows (Array.ofFn (n := n) fun r ↦ f r.val) comp xs z yz offset r0 len) =
      Array.ofFn (n := n) fun r ↦ termStep (comp.getD r.val 0) (xs.getD r.val 0) (f r.val)
        (z, yz, offset) := by
  refine parChunks_eq n _ _ (fun r ↦ termStep (comp.getD r 0) (xs.getD r 0) (f r) (z, yz, offset))
    (fun r0 len hr ↦ ?_) (Or.inl (show 0 < (if n < 4096 then 1 else 16) by split <;> decide))
  have hr' : r0 + len ≤ n ∨ len = 0 := hr
  rcases hr' with hr' | hr'
  · rw [accumulateRows_eq _ _ _ hz _ _ _ _ (by omega)]
    refine congrArg Array.ofFn (funext fun k ↦ ?_)
    rw [getD_ofFn_bounded _ _ (by omega)]
  · subst hr'
    simp only [accumulateRows, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
      List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, List.range'_zero, List.foldl_nil]
    rfl

/-- The specification's accumulation of a matrix's points onto the running sums of its height,
row by row a fold of the fast reduction's terms. -/
theorem foldl_accumulate (alpha : EF) (ap : Array EF) (w n : Nat) (comp : Array EF)
    (xs : Array F) (hxs : n ≤ xs.size) :
    ∀ (pts : List (EF × Array EF)), (∀ p ∈ pts, nonBase p.1 = true) → ∀ (c : Nat) (f : Nat → EF),
      pts.foldl (fun b p ↦ (b.1 + w, parChunks n (if n < 4096 then 1 else 16) fun r0 len ↦
        accumulateRows b.2 comp xs p.1 (yzOf ap w p.2) (Ext.pow alpha b.1) r0 len))
        (c, Array.ofFn (n := n) fun r ↦ f r.val) =
      ((pts.foldl (termsStep alpha ap w) (c, [])).1, Array.ofFn (n := n) fun r ↦
        (pts.foldl (termsStep alpha ap w) (c, [])).2.foldl
          (termStep (comp.getD r.val 0) (xs.getD r.val 0)) (f r.val))
  | [], _, c, f => rfl
  | p :: pts, hz, c, f => by
    rw [List.foldl_cons, List.foldl_cons, parChunks_accumulate n f comp xs hxs
      (hz p List.mem_cons_self)]
    have ih := foldl_accumulate alpha ap w n comp xs hxs pts
      (fun q hq ↦ hz q (List.mem_cons_of_mem p hq)) (c + w) (fun r ↦ termStep (comp.getD r 0)
        (xs.getD r 0) (f r) (p.1, yzOf ap w p.2, Ext.pow alpha c))
    dsimp only at ih ⊢
    rw [ih, termsStep, foldl_termsStep alpha ap w pts _ ([] ++ _)]
    simp only [List.nil_append, List.cons_append, List.foldl_cons]
