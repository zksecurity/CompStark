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
public import CompStark.Stark.Fast.Vectors
public import CompPoly.Univariate.NTTFast.Permutation
public import CompPoly.Univariate.NTTFast.Packed.BitReversal
public import CompPoly.Univariate.NTTFast.Packed.CosetLdeTransposes
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The fast opened values are the specification's

Coordinate by coordinate, the specification's opened value of a column is a sum over the
natural-order rows `i` of the stored row `bitrev i` times the barycentric weight of the `i`-th
coset point (`openedAt_coord`). Reindexed through the involution `bitrev`, it is the sum over the
stored rows of the row times the weight of its stored point, which the fast kernel computes by
parallel ranges (`openedAt_rel`).

The fast reduction groups the matrices by height exactly like the specification's fold
(`groupStep_rel`): a group's planes hold, at every row, the fold of its matrices' terms
`offset · (yz - comp) / (z - x)` in the specification's order (`gval`, `reduceRange_rel`), and
sorting by height keeps the groups related (`reduce_rel`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTT.Transform (bitRevNat bitRevNat_lt bitRevNat_involutive)
open Montgomery.Native32

section
open CompPoly.CPolynomial.NTTFast.Packed (getD_ofFn_bounded)
variable {F : Type} [BaseField F] {K : Type} [Challenge F K]

/-- Row `r` of a matrix of width `w` batched by the powers `ap` of `α`. -/
def crow (V : Array F) (ap : Array K) (w r : Nat) : K :=
  (List.range' 0 w).foldl (fun acc i ↦ acc + Challenge.smul (V.getD (r * w + i) 0) (ap.getD i 0)) 0

theorem compress_eq (s : Mat F) (ap : Array K) :
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
def termStep (comp : K) (x : F) (acc : K) (t : K × K × K) : K :=
  acc + t.2.2 * (t.2.1 - comp) * (t.1 - Ext.ofBase x)⁻¹

theorem accumulateRows_eq (acc comp : Array K) (xs : Array F) {z : K} (hz : Ext.OutsideBase z)
    (yz offset : K) (r0 len : Nat) (hr : r0 + len ≤ xs.size) :
    accumulateRows acc comp xs z yz offset r0 len = Array.ofFn (n := len) fun k ↦
      termStep (comp.getD (r0 + k.val) 0) (xs.getD (r0 + k.val) 0) (acc.getD (r0 + k.val) 0)
        (z, yz, offset) := by
  simp only [accumulateRows, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [batchInv_eq Challenge.toSpec Challenge.toSpec_injective Challenge.toSpec_mul
    Challenge.toSpec_inv Challenge.toSpec_one _ (fun y hy ↦ by
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
      (xs.extract r0 (r0 + len)))).getD k 0) = (z - Ext.ofBase (xs.getD (r0 + k) 0))⁻¹ := by
    have hx : k < (xs.extract r0 (r0 + len)).size := by rw [Array.size_extract]; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_map,
      Array.getElem?_eq_getElem hx, Array.getElem_extract, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show r0 + k < xs.size by omega)]
    rfl
  rw [e]
  rfl

/-- The batched opened value of a point: `∑ᵢ αⁱ ys[i]`. -/
abbrev yzOf (ap : Array K) (w : Nat) (ys : Array K) : K :=
  (List.range w).foldl (fun s i ↦ s + ap.getD i 0 * ys.getD i 0) 0

/-- The points of a matrix with their batched values and offsets `α ^ cnt`, `cnt` stepping by the
width: the fast reduction's terms. -/
def termsStep (alpha : K) (ap : Array K) (w : Nat) (b : Nat × List (K × K × K))
    (pr : K × Array K) : Nat × List (K × K × K) :=
  (b.1 + w, b.2 ++ [(pr.1, yzOf ap w pr.2, Ext.pow alpha b.1)])

theorem foldl_termsStep (alpha : K) (ap : Array K) (w : Nat) :
    ∀ (pts : List (K × Array K)) (c : Nat) (T : List (K × K × K)),
      pts.foldl (termsStep alpha ap w) (c, T) =
        ((pts.foldl (termsStep alpha ap w) (c, [])).1,
          T ++ (pts.foldl (termsStep alpha ap w) (c, [])).2)
  | [], c, T => by rw [List.foldl_nil, List.foldl_nil, List.append_nil]
  | pr :: pts, c, T => by
    rw [List.foldl_cons, List.foldl_cons, termsStep, termsStep,
      foldl_termsStep alpha ap w pts _ (T ++ _), foldl_termsStep alpha ap w pts _ ([] ++ _),
      List.nil_append, List.append_assoc]

theorem parChunks_accumulate (n : Nat) (f : Nat → K) (comp : Array K) (xs : Array F)
    (hxs : n ≤ xs.size) {z : K} (hz : Ext.OutsideBase z) (yz offset : K) :
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
theorem foldl_accumulate (alpha : K) (ap : Array K) (w n : Nat) (comp : Array K)
    (xs : Array F) (hxs : n ≤ xs.size) :
    ∀ (pts : List (K × Array K)), (∀ pr ∈ pts, Ext.OutsideBase pr.1) → ∀ (c : Nat) (f : Nat → K),
      pts.foldl (fun b pr ↦ (b.1 + w, parChunks n (if n < 4096 then 1 else 16) fun r0 len ↦
        accumulateRows b.2 comp xs pr.1 (yzOf ap w pr.2) (Ext.pow alpha b.1) r0 len))
        (c, Array.ofFn (n := n) fun r ↦ f r.val) =
      ((pts.foldl (termsStep alpha ap w) (c, [])).1, Array.ofFn (n := n) fun r ↦
        (pts.foldl (termsStep alpha ap w) (c, [])).2.foldl
          (termStep (comp.getD r.val 0) (xs.getD r.val 0)) (f r.val))
  | [], _, c, f => rfl
  | pr :: pts, hz, c, f => by
    rw [List.foldl_cons, List.foldl_cons, parChunks_accumulate n f comp xs hxs
      (hz pr List.mem_cons_self)]
    have ih := foldl_accumulate alpha ap w n comp xs hxs pts
      (fun q hq ↦ hz q (List.mem_cons_of_mem pr hq)) (c + w) (fun r ↦ termStep (comp.getD r 0)
        (xs.getD r 0) (f r) (pr.1, yzOf ap w pr.2, Ext.pow alpha c))
    dsimp only at ih ⊢
    rw [ih, termsStep, foldl_termsStep alpha ap w pts _ ([] ++ _)]
    simp only [List.nil_append, List.cons_append, List.foldl_cons]

/-- The powers `1, α, …, α ^ (w - 1)`. -/
abbrev powers (alpha : K) (w : Nat) : Array K := Array.ofFn (n := w) fun i ↦ Ext.pow alpha i.val

end

section
variable {F : Type} [BaseField F]

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

end

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-! ### Coordinates -/

theorem coord_add (c : Nat) (a b : EF) : coord c (a + b) = coord c a + coord c b := by
  match c with
  | 0 | 1 | 2 | _ + 3 => rfl

theorem coord_smul [Mont32BaseField p] [Binomial4 p] (c : Nat) (x : F) (a : EF) : coord c
    (Challenge.smul x a) = x * coord c a := by
  match c with
  | 0 | 1 | 2 | _ + 3 => rfl

theorem coord_zero (c : Nat) : coord c (0 : EF) = 0 := by
  match c with
  | 0 | 1 | 2 | _ + 3 => rfl

theorem ext_coord {a b : EF} (h : ∀ c < 4, coord c a = coord c b) : a = b :=
  Norm.ext (h 0 (by decide)) (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))

/-- Coordinate `c` of a sum of scaled elements is the sum of the scaled coordinates. -/
theorem coord_foldl_smul [Mont32BaseField p] [Binomial4 p] (f : Nat → F) (g : Nat → EF) (c : Nat)
    (acc : EF) : ∀ n,
    coord c ((List.range' 0 n).foldl (fun acc i ↦ acc + Challenge.smul (f i) (g i)) acc) =
      coord c acc + ∑ i ∈ Finset.range n, f i * coord c (g i)
  | 0 => by rw [List.range'_zero, List.foldl_nil, Finset.sum_range_zero, add_zero]
  | n + 1 => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, coord_add,
      coord_foldl_smul f g c acc n, Finset.sum_range_succ, coord_smul, Nat.zero_add, Nat.one_mul,
      add_assoc]

/-! ### Bit reversal -/

/-! ### The specification's opened values -/

/-- The extension element of four coordinates. -/
def mk4 (f : Nat → F) : EF := ⟨f 0, f 1, f 2, f 3⟩

theorem coord_mk4 (f : Nat → F) (c : Nat) (hc : c < 4) : coord c (mk4 f) = f c := by
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- A column sum of the specification, coordinate by coordinate, reindexed to the stored rows. -/
theorem coord_colSum [Mont32BaseField p] [Binomial4 p] (values : Array F) (w L j : Nat) {z : EF}
    (hz : Ext.OutsideBase z)
    (c : Nat) : coord c (colSum values (bitRevPerm L) (baryWeights L z) w (2 ^ L) j) =
      ∑ r ∈ Finset.range (2 ^ L), values.getD (r * w + j) 0 *
        coord c (bw z ((cosetPointsBitRev (gen : F) L).getD r 0)) := by
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
theorem openedAt_sum [Mont32BaseField p] [Binomial4 p] (b : Nat) (s : Mat F) {z : EF}
    (hz : Ext.OutsideBase z) :
    Fri.openedAt b s z = Array.ofFn (n := s.width) fun j ↦
      Fri.cosetFactor (Nat.log2 s.height - b) gen z * mk4 fun c ↦
        ∑ r ∈ Finset.range (2 ^ (Nat.log2 s.height - b)), s.values.getD (r * s.width + j.val) 0 *
          coord c (bw z ((cosetPointsBitRev (gen : F) (Nat.log2 s.height - b)).getD r 0)) := by
  rw [openedAt_eq]
  refine Array.ext (by rw [Array.size_ofFn, Array.size_ofFn]) fun j h1 h2 ↦ ?_
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  exact congrArg _ (ext_coord fun c hc ↦ by rw [coord_mk4 _ _ hc, coord_colSum _ _ _ _ hz])

/-! ### Inverses by the norm on words -/

theorem mulAddWords_ofFn {n : Nat} (hn : 4 * n < USize.size) (f g : Fin n → F)
    (c : F) : Words.mulAddWords p (encode (Array.ofFn f)) (encode (Array.ofFn g)) c.val n =
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
    batchInvWords p (encode (Array.ofFn f)) n = encode (Array.ofFn fun i ↦ (f i)⁻¹) := by
  rw [batchInvWords_encode _ _ (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn]; exact hn)
    fun k hk ↦ by rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hk]; exact hf _]
  refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
  rw [CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt]

theorem encode_ofFn_getElem (X : Array F) :
    encode X = encode (Array.ofFn (n := X.size) fun i ↦ X[i.val]) := by
  rw [Array.ofFn_getElem]

/-- `invDenoms` inverts `z - x` for every base point `x`, for `z` outside the base field. -/
theorem invDenoms_rel [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F) {z : EF}
    (hz : Ext.OutsideBase z) (X : Array F)
    (hs : 4 * X.size < USize.size) :
    RV (invDenoms z (encode X) X.size) (X.map fun x ↦ (z - Ext4.ofBase x)⁻¹) := by
  have hz' := (Mont32.outsideBase_ext4 z).mp hz
  simp only [invDenoms]
  rw [encode_ofFn_getElem X]
  simp only [EVec.mulWords_ofFn hs, EVec.addWords_ofFn hs, mulAddWords_ofFn hs,
    replicateWord_ofFn hs, ite_true, Bool.false_eq_true, ite_false]
  rw [batchInvWords_ofFn hs _ ?_]
  · simp only [EVec.mulWords_ofFn hs]
    refine EVec.rv_ofFn _ (Array.size_map ..) _ _ _ _ fun i ↦ ?_
    rw [Array.getElem_map, Norm.inv_eq hζ hz']
    apply Norm.ext <;>
      simp only [Montgomery.Native32.Ext4.smul, Norm.cubic, Norm.norm, Norm.e1, Norm.e2, Norm.e3,
        Norm.conj] <;> ring
  · intro i
    have := Norm.norm_ne_zero hζ hz' X[i.val]
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
  rw [Words.zeroWords_eq (p := p), ← Words.upto_zero (Array.replicate w 0) f,
    Words.foldl_tail _ _ _ _ _ (fun k _ hk ↦ by
      rw [hg k (by omega)]
      exact Words.write_upto _ f k (by rw [Array.size_replicate]; omega)
        (by rw [Array.size_replicate]; omega)),
    Nat.zero_add, Words.upto_full _ _ _ (Array.size_replicate ..)]

/-- The transpose of a range of rows of an encoded matrix, on field elements. -/
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

theorem mul_ofBase [Binomial4 p] (a : EF) (x : F) : a * Ext4.ofBase x = Ext4.smul x a := by
  apply Norm.ext <;>
    simp only [Norm.mul_c0, Norm.mul_c1, Norm.mul_c2, Norm.mul_c3, Ext4.ofBase, Ext4.smul] <;>
    ring

/-- The weight planes of a range of stored points. -/
theorem weightPlane [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F) {z : EF}
    (hz : Ext.OutsideBase z) (X : Array F)
    (r0 len : Nat)
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
    (invDenoms_rel hζ hz (X.extract r0 (r0 + len)) hs') (by rw [Array.size_map]) hs'
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
      Array.getElem_extract, Ext.ofBase, Mont32.ofBase_ext4, mul_ofBase,
      Array.getD_eq_getD_getElem?,
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
theorem foldl_append_ofFn4 {α : Type} (R : EF → Fin 4 → α) : ∀ (l : List EF) (b : Array α), l.foldl
    (fun b z ↦ b ++ Array.ofFn (R z)) b =
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

/-- The weight planes of a range of stored points, for every point and coordinate. -/
theorem weightPlanes_encode [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F)
    (zs : Array EF) (hz : ∀ z ∈ zs, Ext.OutsideBase z) (X : Array F) (r0 len : Nat)
    (hX : r0 + len ≤ X.size) (hsX : 4 * X.size < USize.size) :
    weightPlanes zs (encode X) r0 len = Array.ofFn (n := 4 * zs.size) fun i ↦
      encode (Array.ofFn (n := len) fun t ↦
        coord (i.val % 4) (bw (zs.toList.getD (i.val / 4) 0) (X.getD (r0 + t.val) 0))) := by
  unfold weightPlanes
  rw [← Array.foldl_toList, List.foldl_ext _ (fun b z ↦ b ++ Array.ofFn (n := 4) fun c ↦
    encode (Array.ofFn (n := len) fun t ↦ coord c.val (bw z (X.getD (r0 + t.val) 0)))) _ ?_,
    foldl_append_ofFn4, Array.empty_append]
  · rfl
  intro b z hz'
  dsimp only
  rw [weightPlane hζ (hz z (Array.mem_toList_iff.mp hz')) X r0 len hX hsX]

/-- The fast column sums of a range of stored rows within one block of the matrix: for every point
and coordinate, a plane of a sum per column, of the rows times the weights of their points. -/
theorem weightedColumns_cols [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F)
    {pm : PMat} {s : Mat F} (h : RM pm s) (zs : Array EF)
    (hz : ∀ z ∈ zs, Ext.OutsideBase z) (X : Array F) (r0 len : Nat) (hlen : 0 < len)
    (hblk : r0 % pm.rows + len ≤ pm.rows) (hr : r0 + len ≤ s.height) (hX : r0 + len ≤ X.size)
    (hsX : 4 * X.size < USize.size) :
    weightedColumns pm zs (encode X) r0 len =
      Array.ofFn (n := 4 * zs.size) fun i ↦ encode (Array.ofFn (n := s.width) fun j ↦
        ∑ t ∈ Finset.range len, s.values.getD ((r0 + t) * s.width + j.val) 0 *
          coord (i.val % 4) (bw (zs.toList.getD (i.val / 4) 0) (X.getD (r0 + t) 0))) := by
  unfold Fast.weightedColumns
  dsimp only
  rw [weightPlanes_encode hζ zs hz X r0 len hX hsX, Array.size_ofFn, h.width]
  let P (i t : Nat) : F := coord (i % 4) (bw (zs.toList.getD (i / 4) 0) (X.getD (r0 + t) 0))
  have hl : 4 * len < USize.size := by omega
  apply Array.ext (by rw [Array.size_map, Array.size_range, Array.size_ofFn])
  intro i h1 h2
  rw [Array.size_map, Array.size_range] at h1
  rw [Array.getElem_map, Array.getElem_range, Array.getElem_ofFn,
    CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq]
  refine congrArg encode (Array.ext (by rw [Array.size_ofFn, Array.size_ofFn]) fun j j1 _ ↦ ?_)
  rw [Array.size_ofFn] at j1
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  dsimp only
  rw [CompPoly.CPolynomial.NTTFast.Packed.getD_map_range _ _ _ j1, Array.getD_eq_getD_getElem?,
    Array.getElem?_map,
    Array.getElem?_ofFn, dite_eq_left_of_eq_true (eq_true h1), Option.map_some,
    Option.getD_some]
  obtain ⟨A, e1, e2, e3, e4⟩ := colAt_spec h r0 len j hblk hr hlen j1
  have hpl : (Array.ofFn (n := len) fun t ↦ P i t.val).size = len := Array.size_ofFn
  rw [e1, Words.dotAt_encode _ _ _ _ e2 (by rw [hpl]) e3 (by rw [hpl]; exact hl),
    CompPoly.CPolynomial.NTTFast.Packed.ofWord_val]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have ht := Finset.mem_range.mp ht
  rw [e4 t ht, getD_ofFn_bounded _ _ ht]

theorem zip_map_addWords (N w : Nat) (hw : 4 * w < USize.size) (A B : Fin N → Fin w → F) :
    ((Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (A i))).zip
      (Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (B i)))).map
        (fun (a, b) ↦ Words.addWords p a b w) =
      Array.ofFn (n := N) fun i ↦ encode (Array.ofFn fun j ↦ A i j + B i j) := by
  refine Array.ext (by rw [Array.size_map, Array.size_zip, Array.size_ofFn, Array.size_ofFn,
    Array.size_ofFn, Nat.min_self]) fun i h1 h2 ↦ ?_
  rw [Array.getElem_map, Array.getElem_zip, Array.getElem_ofFn, Array.getElem_ofFn,
    Array.getElem_ofFn]
  exact EVec.addWords_ofFn hw _ _

/-- Sums over parallel ranges of `h` rows, added plane by plane, are the sums over all rows. -/
theorem parts_sum (N w h parts : Nat) (hp : 0 < parts) (hw : 4 * w < USize.size)
    (g : Nat → Nat → Nat → F) (WC : Nat → Nat → Array ByteArray)
    (hWC : ∀ k < parts, WC (k * (h / parts))
      (if k + 1 = parts then h - k * (h / parts) else h / parts) = Array.ofFn (n := N) fun i ↦
        encode (Array.ofFn (n := w) fun j ↦ ∑ t ∈ Finset.range
          (if k + 1 = parts then h - k * (h / parts) else h / parts),
            g i j (k * (h / parts) + t))) :
    ((Array.range parts).map fun k ↦ Task.spawn fun _ ↦
      WC (k * (h / parts)) (if k + 1 = parts then h - k * (h / parts) else h / parts)).foldl
        (fun acc t ↦ (acc.zip t.get).map fun (a, b) ↦ Words.addWords p a b w)
        (Array.replicate N (zeroWords w)) =
      Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (n := w) fun j ↦
        ∑ r ∈ Finset.range h, g i j r) := by
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
  have hsz : parts * (h / parts) ≤ h := Nat.mul_div_le h parts
  generalize h / parts = sz at hsz hWC ⊢
  have key : ∀ K ≤ parts, (List.range K).foldl (fun acc k ↦ (acc.zip (WC (k * sz)
      (if k + 1 = parts then h - k * sz else sz))).map
        fun (a, b) ↦ Words.addWords p a b w) (Array.replicate N (zeroWords w)) =
      Array.ofFn (n := N) fun i ↦ encode (Array.ofFn (n := w) fun j ↦
        ∑ r ∈ Finset.range (if K = parts then h else K * sz), g i j r) := by
    intro K
    induction K with
    | zero =>
      intro _
      rw [List.range_zero, List.foldl_nil, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        Nat.zero_mul]
      refine Array.ext (by rw [Array.size_replicate, Array.size_ofFn]) fun i _ _ ↦ ?_
      rw [Array.getElem_replicate, Array.getElem_ofFn, EVec.zeroWords_ofFn (p := p)]
      rfl
    | succ K ih =>
      intro hK
      have hK' : K * sz + sz ≤ h := by
        have := Nat.mul_le_mul_right sz hK
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        ite_eq_right_of_eq_false _ _ (eq_false (show K ≠ parts by omega))]
      rw [hWC K (by omega), zip_map_addWords N w hw]
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

theorem size_openedAt [Mont32BaseField p] [Binomial4 p] (b : Nat) (s : Mat F) (z : EF) :
    (Fri.openedAt b s z).size = s.width := by
  rw [openedAt_eq, Array.size_ofFn]

/-- Ranges of `h / parts` rows, `parts = h / G` for a divisor `G` of `h`: every range has `G`
rows. -/
theorem uniform_ranges {h G : Nat} (hG : 0 < G) (hGh : G ∣ h) (hh : 0 < h) :
    0 < h / G ∧ h / (h / G) = G ∧ ∀ k < h / G,
      (if k + 1 = h / G then h - k * (h / (h / G)) else h / (h / G)) = G ∧
        k * G + G ≤ h := by
  obtain ⟨c, rfl⟩ := hGh
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hh)
  rw [Nat.mul_div_cancel_left _ hG, Nat.mul_div_cancel _ hc]
  refine ⟨hc, rfl, fun k hk ↦ ⟨?_, ?_⟩⟩
  · split
    · rename_i e
      rw [← e, Nat.mul_comm G (k + 1), Nat.succ_mul, Nat.add_sub_cancel_left]
    · rfl
  · have := Nat.mul_le_mul_left G (show k + 1 ≤ c by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    rw [Nat.mul_comm k G]; exact this

/-- The divisor of a power of two `h` that the fast kernels range by: `h`, or `h / 16` from
`4096` rows on, and the rows of every block of a matrix. -/
theorem gcd_range_dvd (L R : Nat) :
    Nat.gcd (if 2 ^ L < 4096 then 2 ^ L else 2 ^ L / 16) R ∣ 2 ^ L := by
  refine (Nat.gcd_dvd_left _ _).trans ?_
  split
  · exact dvd_rfl
  · rename_i hL
    have h4 : 4 ≤ L := by
      by_contra hc
      have := Nat.pow_lt_pow_right (show 1 < 2 by decide) (show L < 4 by omega)
      omega
    exact Nat.div_dvd_of_dvd (Nat.pow_dvd_pow 2 h4)

/-- The fast opened values are the specification's. -/
theorem openedAt_rel [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F) (b : Nat)
    (zs : List EF) {m : PMat} {s : Mat F}
    (h : RM m s)
    (hs : MatOk s) (hz : ∀ z ∈ zs, Ext.OutsideBase z) :
    openedAt b m zs = zs.map (Fri.openedAt b s) := by
  unfold Fast.openedAt
  obtain ⟨-, ⟨k, -, hk⟩, hM, hA⟩ := hs
  have hle : s.height ≥ 2 ^ (Nat.log2 s.height - b) := by
    rw [hk, Nat.log2_two_pow]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le k b)
  have hfits : 4 * s.values.size < USize.size := by
    unfold Addressable at hA
    omega
  dsimp only
  rw [h.width, h.height]
  generalize hL : Nat.log2 s.height - b = L at hle ⊢
  -- An empty row: both sides are empty.
  by_cases hw0 : s.width = 0
  · refine List.ext_getElem
      (by rw [List.length_map, List.length_map, List.length_zipIdx]) fun k h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_map]
    refine Array.ext (by rw [Array.size_ofFn, size_openedAt, hw0]) fun j h1 _ ↦ ?_
    rw [Array.size_ofFn] at h1
    omega
  have hpos : 0 < s.height := lt_of_lt_of_le (Nat.two_pow_pos L) hle
  have hsM : 4 * s.values.size < USize.size := hfits
  have hX : (cosetPointsBitRev (gen : F) L).size = 2 ^ L := size_cosetPointsBitRev (gen : F) L
  have hw4 : 4 * s.width < USize.size := by
    have := Nat.mul_le_mul_left s.width (show 1 ≤ s.height from hpos)
    omega
  have hsX : 4 * (cosetPointsBitRev (gen : F) L).size < USize.size := by
    have := Nat.mul_le_mul_right s.height (show 1 ≤ s.width by omega)
    omega
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq]
  have hGd := gcd_range_dvd L m.rows
  generalize hG : Nat.gcd (if 2 ^ L < 4096 then 2 ^ L else 2 ^ L / 16) m.rows = G at hGd ⊢
  have hG0 : 0 < G := by rw [← hG]; exact Nat.gcd_pos_of_pos_right _ h.pos
  have hGR : G ∣ m.rows := by rw [← hG]; exact Nat.gcd_dvd_right _ _
  obtain ⟨hp, hpG, hranges⟩ := uniform_ranges hG0 hGd (Nat.two_pow_pos L)
  rw [parts_sum (4 * zs.length) s.width (2 ^ L) _ hp hw4
    (fun i j r ↦ s.values.getD (r * s.width + j) 0 *
      coord (i % 4) (bw (zs.getD (i / 4) 0) ((cosetPointsBitRev (gen : F) L).getD r 0)))
    (fun r0 len ↦ weightedColumns m zs.toArray
      (encode (cosetPointsBitRev (gen : F) L)) r0 len) (fun k hk ↦ ?_)]
  · refine List.ext_getElem
      (by rw [List.length_map, List.length_map, List.length_zipIdx]) fun k h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [List.length_map, List.length_zipIdx] at h1
    rw [openedAt_sum b s (hz _ (List.getElem_mem _)), hL]
    have hwp : ∀ idx, idx < 4 * zs.length → ∀ j, j < s.width →
        word ((Array.ofFn (n := 4 * zs.length) fun i ↦ encode (Array.ofFn (n := s.width) fun j ↦
          ∑ r ∈ Finset.range (2 ^ L), s.values.getD (r * s.width + j.val) 0 * coord (i.val % 4)
            (bw (zs.getD (i.val / 4) 0) ((cosetPointsBitRev (gen : F) L).getD r 0)))).getD
          idx .empty) j =
        ∑ r ∈ Finset.range (2 ^ L), s.values.getD (r * s.width + j) 0 * coord (idx % 4)
          (bw (zs.getD (idx / 4) 0) ((cosetPointsBitRev (gen : F) L).getD r 0)) :=
      fun idx hidx j hj ↦ word_plane (4 * zs.length) s.width (fun i j ↦
        ∑ r ∈ Finset.range (2 ^ L), s.values.getD (r * s.width + j) 0 * coord (i % 4)
          (bw (zs.getD (i / 4) 0) ((cosetPointsBitRev (gen : F) L).getD r 0))) idx j hidx hj hw4
    refine congrArg Array.ofFn (funext fun j ↦ congrArg _ (Norm.ext ?_ ?_ ?_ ?_)) <;>
      dsimp only [mk4] <;>
      rw [hwp _ (by omega) _ j.isLt] <;>
      refine Finset.sum_congr rfl fun r _ ↦ ?_ <;>
      simp only [show (4 * k + 1) / 4 = k by omega, show (4 * k + 2) / 4 = k by omega,
        show (4 * k + 3) / 4 = k by omega, show 4 * k / 4 = k by omega,
        show (4 * k + 1) % 4 = 1 by omega, show (4 * k + 2) % 4 = 2 by omega,
        show (4 * k + 3) % 4 = 3 by omega, show 4 * k % 4 = 0 by omega,
        List.getD_eq_getElem _ _ h1]
  · obtain ⟨hlen, hcov⟩ := hranges k hk
    rw [hlen, hpG]
    rw [weightedColumns_cols hζ h zs.toArray (fun z hz' ↦ hz z (List.mem_toArray.mp hz'))
      _ (k * G) G hG0 (mod_add_le_of_dvd h.pos hGR (Nat.dvd_mul_left G k)) (by omega)
      (by omega) hsX]
    rfl

/-! ### The specification's reduction row by row -/


/-! ### The fast reduction as a fold -/

/-- A matrix of a group of the fast reduction: the packed matrix, the powers of `α` as planes,
and its terms `(z, yz, offset)`. -/
abbrev GItem (q : ℕ) [Mont32Field q] := PMat × EVec q × List (Ext4 q × Ext4 q × Ext4 q)

/-- One matrix of the fast reduction's grouping by height. -/
def groupStep [Mont32BaseField p] [Binomial4 p] (alpha : EF) (groups : List (Nat × Nat × Array
    (GItem p)))
    (it : PMat × List (EF × Array EF)) : List (Nat × Nat × Array (GItem p)) :=
  let m := it.1
  let logH := Nat.log2 m.height
  let start := (groups.lookup logH).getD (0, #[])
  let ap := Array.ofFn (n := m.width) fun i ↦ Ext.pow alpha i.val
  let res := it.2.foldl (termsStep alpha ap m.width) (start.1, [])
  (logH, res.1, start.2.push (m, EVec.ofArray ap, res.2)) ::
    groups.filter (·.1 != logH)

/-- The batched quotient of one group, by parallel ranges of rows within one block of every
matrix. -/
def groupPlanes [Mont32BaseField p] [Binomial4 p] (G : Nat × Nat × Array
    (GItem p)) : Nat × EVec p :=
  let n := 2 ^ G.1
  let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (cosetPointsBitRev (gen : F) G.1)
  let parts := n / G.2.2.foldl (fun a (m, _) ↦ Nat.gcd a m.rows) (if n < 4096 then n else n / 16)
  let size := n / parts
  (G.1, joinPlanes p n <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    let v := reduceRange G.2.2 xs (k * size) (if k + 1 = parts then n - k * size else size)
    #[v.c0, v.c1, v.c2, v.c3])

/-- The fast reduction groups by height, then computes every group's planes. -/
theorem reduce_fast [Mont32BaseField p] [Binomial4 p] (alpha : EF) (items : List (PMat × List
    (EF × Array EF))) :
    reduce alpha items = ((items.foldl (groupStep alpha) []).map groupPlanes).mergeSort
      fun a b ↦ decide (b.1 ≤ a.1) := by
  simp only [reduce, Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

/-! ### The grouping simulates the specification's fold -/

/-- Row `r` of a group's batched quotient: every term of every matrix in order. -/
def gval [Mont32BaseField p] [Binomial4 p] (alpha : EF) (logH : Nat) (g : Array (GItem p))
    (r : Nat) : EF :=
  g.toList.foldl (fun a it ↦ it.2.2.foldl (termStep
    (crow (it.1.vals p) (powers alpha it.1.width) it.1.width r)
    ((cosetPointsBitRev (gen : F) logH).getD r 0)) a) 0

/-- A matrix of a group of height `2 ^ logH` the fast kernels compute on. -/
def Good [Mont32BaseField p] [Binomial4 p] (alpha : EF) (logH : Nat) (it : GItem p) : Prop :=
  ∃ s : Mat F, RM it.1 s ∧ s.height = 2 ^ logH ∧ 4 * s.values.size < USize.size ∧
    4 * 2 ^ logH < USize.size ∧ it.2.1 = EVec.ofArray (powers alpha it.1.width) ∧
    ∀ t ∈ it.2.2, Ext.OutsideBase t.1

/-- A fast group represents the specification's running sums of its height. -/
def GR [Mont32BaseField p] [Binomial4 p] (alpha : EF) (G : Nat × Nat × Array (GItem p))
    (S : Nat × Nat × Array EF) : Prop :=
  G.1 = S.1 ∧ G.2.1 = S.2.1 ∧ S.2.2 = Array.ofFn (n := 2 ^ G.1) (fun r ↦ gval alpha G.1 G.2.2 r) ∧
    4 * 2 ^ G.1 < USize.size ∧ ∀ it ∈ G.2.2, Good alpha G.1 it

/-- Related group lists hold related groups of every height. -/
theorem lookup_rel [Mont32BaseField p] [Binomial4 p] (alpha : EF) (k : Nat) {l1 : List
    (Nat × Nat × Array (GItem p))}
    {l2 : List (Nat × Nat × Array EF)} (h : List.Forall₂ (GR alpha) l1 l2) :
    (l1.lookup k = none ∧ l2.lookup k = none) ∨ ∃ c g, l1.lookup k = some (c, g) ∧
      l2.lookup k = some (c, Array.ofFn (n := 2 ^ k) fun r ↦ gval alpha k g r) ∧
      ∀ it ∈ g, Good alpha k it := by
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons G S l1 l2 hGS _ ih =>
    obtain ⟨h1, h2, h3, -, h4⟩ := hGS
    obtain ⟨k1, c1, g1⟩ := G
    obtain ⟨k2, c2, a2⟩ := S
    simp only at h1 h2 h3 h4
    subst h1 h2 h3
    by_cases hk : k = k1
    · subst hk
      refine Or.inr ⟨c1, g1, ?_, ?_, h4⟩ <;> simp only [List.lookup, beq_self_eq_true]
    · have e : (k == k1) = false := beq_false_of_ne hk
      simp only [List.lookup, e]
      exact ih

theorem filter_rel [Mont32BaseField p] [Binomial4 p] (alpha : EF) (k : Nat) {l1 : List
    (Nat × Nat × Array (GItem p))}
    {l2 : List (Nat × Nat × Array EF)} (h : List.Forall₂ (GR alpha) l1 l2) :
    List.Forall₂ (GR alpha) (l1.filter (·.1 != k)) (l2.filter (·.1 != k)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons G S l1 l2 hGS _ ih =>
    rw [List.filter_cons, List.filter_cons, hGS.1]
    split
    · exact List.Forall₂.cons hGS ih
    · exact ih

theorem mem_terms [Mont32BaseField p] [Binomial4 p] (alpha : EF) (ap : Array EF) (w : Nat) : ∀
    (pts : List (EF × Array EF))
    (c : Nat), ∀ t ∈ (pts.foldl (termsStep alpha ap w) (c, [])).2, ∃ pr ∈ pts, t.1 = pr.1
  | [], _, t, ht => absurd ht List.not_mem_nil
  | pr :: pts, c, t, ht => by
    rw [List.foldl_cons, termsStep, foldl_termsStep, List.nil_append] at ht
    rcases List.mem_append.mp ht with ht | ht
    · rw [List.mem_singleton.mp ht]
      exact ⟨pr, List.mem_cons_self, rfl⟩
    · obtain ⟨q, hq, e⟩ := mem_terms alpha ap w pts _ t ht
      exact ⟨q, List.mem_cons_of_mem pr hq, e⟩

theorem gval_push [Mont32BaseField p] [Binomial4 p] (alpha : EF) (logH : Nat) (g : Array (GItem p))
    (it : GItem p)
    (r : Nat) : gval alpha logH (g.push it) r = it.2.2.foldl (termStep
      (crow (it.1.vals p) (powers alpha it.1.width) it.1.width r)
      ((cosetPointsBitRev (gen : F) logH).getD r 0)) (gval alpha logH g r) := by
  rw [gval, gval, Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- One matrix of the grouping simulates one step of the specification's fold. -/
theorem groupStep_rel [Mont32BaseField p] [Binomial4 p] (alpha : EF) {groups : List
    (Nat × Nat × Array (GItem p))}
    {red : List (Nat × Nat × Array EF)} (hgr : List.Forall₂ (GR alpha) groups red) {m : PMat}
    {s : Mat F} (hm : RM m s) (pts : List (EF × Array EF)) (hs : MatOk s)
    (hz : ∀ pr ∈ pts, Ext.OutsideBase pr.1) :
    List.Forall₂ (GR alpha) (groupStep alpha groups (m, pts)) (reduceStep alpha red (s, pts)) := by
  obtain ⟨hw0, ⟨k, -, hk⟩, hM, hA⟩ := hs
  unfold Addressable at hA
  have hsV : 4 * s.values.size < USize.size := by omega
  have hpow : m.height = 2 ^ Nat.log2 m.height := by rw [hm.height, hk, Nat.log2_two_pow]
  have hus : 4 * m.height < USize.size := by
    have := Nat.le_mul_of_pos_left s.height hw0
    rw [hm.height]
    omega
  have hw := hm.width
  have hh := hm.height
  unfold groupStep reduceStep
  dsimp only
  rw [hw, hh]
  rw [hh] at hpow hus
  generalize hL : Nat.log2 s.height = logH at hpow
  refine List.Forall₂.cons ?_ (filter_rel alpha logH hgr)
  -- The running sums and count of the height before this matrix.
  obtain ⟨c, g, h1, h2, hg⟩ : ∃ c g, (groups.lookup logH).getD (0, #[]) = (c, g) ∧
      (red.lookup logH).getD (0, Array.replicate s.height 0) =
        (c, Array.ofFn (n := s.height) fun r ↦ gval alpha logH g r.val) ∧
      ∀ it ∈ g, Good alpha logH it := by
    rcases lookup_rel alpha logH hgr with ⟨h1, h2⟩ | ⟨c, g, h1, h2, hg⟩
    · refine ⟨0, #[], by rw [h1]; rfl, by
        rw [h2, Option.getD_none]
        refine congrArg _ (Array.ext (by rw [Array.size_replicate, Array.size_ofFn])
          fun i _ _ ↦ ?_)
        rw [Array.getElem_replicate, Array.getElem_ofFn]
        rfl, fun it hit ↦ absurd hit (by simp only [Array.not_mem_empty, not_false_eq_true])⟩
    · refine ⟨c, g, by rw [h1]; rfl, by rw [h2, Option.getD_some, ← hpow], hg⟩
  rw [h1, h2]
  dsimp only
  have hxs : s.height ≤ (cosetPointsBitRev (gen : F) logH).size := by
    rw [size_cosetPointsBitRev, ← hpow]
  rw [foldl_accumulate alpha (powers alpha s.width) s.width s.height _ _ hxs pts hz c]
  refine ⟨rfl, rfl, ?_, show 4 * 2 ^ logH < USize.size by rw [← hpow]; exact hus,
    fun it hit ↦ ?_⟩
  · dsimp only
    rw [← hpow]
    refine Array.ext (by rw [Array.size_ofFn, Array.size_ofFn]) fun r h1 _ ↦ ?_
    rw [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn, gval_push]
    dsimp only
    rw [compress_eq, vals_rel hm, hw]
    have e : (Array.ofFn (n := s.height) fun r ↦ crow s.values
        (powers alpha s.width) s.width r.val).getD r 0 = crow s.values
            (powers alpha s.width) s.width r :=
      getD_ofFn_bounded _ _ h1 _
    rw [e]
  · rcases Array.mem_push.mp hit with hit | hit
    · exact hg it hit
    · subst hit
      refine ⟨s, hm, hpow, hsV, by rw [← hpow]; exact hus, by rw [hw],
        fun t ht ↦ ?_⟩
      obtain ⟨pr, hp, e⟩ := mem_terms alpha _ _ pts c t ht
      rw [e]
      exact hz pr hp

/-- The grouping simulates the specification's fold. -/
theorem foldl_groupStep_rel [Mont32BaseField p] [Binomial4 p] (alpha : EF) :
    ∀ {items : List (PMat × List (EF × Array EF))}
      {sitems : List (Mat F × List (EF × Array EF))},
      List.Forall₂ (fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) items sitems →
      (∀ x ∈ sitems, MatOk x.1 ∧ ∀ pr ∈ x.2, Ext.OutsideBase pr.1) →
      ∀ {groups : List (Nat × Nat × Array (GItem p))} {red : List (Nat × Nat × Array EF)},
      List.Forall₂ (GR alpha) groups red →
      List.Forall₂ (GR alpha) (items.foldl (groupStep alpha) groups)
        (sitems.foldl (reduceStep alpha) red)
  | _, _, .nil, _, _, _, hgr => hgr
  | (m, pts) :: _, (s, _) :: _, .cons ⟨hm, hp⟩ hrest, hgood, _, _, hgr => by
    simp only at hp
    subst hp
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨hs, hz⟩ := hgood (s, pts) List.mem_cons_self
    exact foldl_groupStep_rel alpha hrest (fun it hit ↦ hgood it (List.mem_cons_of_mem _ hit))
      (groupStep_rel alpha hgr hm pts hs hz)

theorem forall₂_zip {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) : ∀ pr ∈ l1.zip l2, R pr.1 pr.2 := by
  induction h with
  | nil => intro pr hp; exact absurd hp List.not_mem_nil
  | cons hab _ ih =>
    intro pr hp
    rw [List.zip_cons_cons] at hp
    rcases List.mem_cons.mp hp with hp | hp
    · rw [hp]; exact hab
    · exact ih pr hp

theorem forall₂_map_fst_snd {α β : Type} {R : α → β → Prop} :
    ∀ (Q : List (α × β)), (∀ q ∈ Q, R q.1 q.2) → List.Forall₂ R (Q.map (·.1)) (Q.map (·.2))
  | [], _ => List.Forall₂.nil
  | q :: Q, h => List.Forall₂.cons (h q List.mem_cons_self)
      (forall₂_map_fst_snd Q fun x hx ↦ h x (List.mem_cons_of_mem q hx))

/-- Sorting by a key keeps related lists related when related elements have equal keys. -/
theorem forall₂_mergeSort {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (key1 : α → Nat) (key2 : β → Nat) (h : List.Forall₂ R l1 l2)
    (hk : ∀ a b, R a b → key1 a = key2 b) :
    List.Forall₂ R (l1.mergeSort fun a b ↦ decide (key1 b ≤ key1 a))
      (l2.mergeSort fun a b ↦ decide (key2 b ≤ key2 a)) := by
  have hl := h.length_eq
  obtain ⟨P, e1, e2, hz⟩ : ∃ P : List (α × β), l1 = P.map (·.1) ∧ l2 = P.map (·.2) ∧
      ∀ q ∈ P, R q.1 q.2 :=
    ⟨l1.zip l2, by rw [List.map_fst_zip (le_of_eq hl)], by rw [List.map_snd_zip (le_of_eq hl.symm)],
      forall₂_zip h⟩
  subst e1 e2
  rw [← List.map_mergeSort (r := fun a b ↦ decide (key1 b.1 ≤ key1 a.1))
    (fun a _ b _ ↦ rfl), ← List.map_mergeSort (r := fun a b ↦ decide (key1 b.1 ≤ key1 a.1))
    (fun a ha b hb ↦ by rw [hk _ _ (hz a ha), hk _ _ (hz b hb)])]
  exact forall₂_map_fst_snd _ fun q hq ↦ hz q (List.mem_mergeSort.mp hq)

/-! ### The fast kernel of one group -/

/-- The fast batching of a range of rows within one block of a packed matrix by the powers `ap`
of `α`, coordinate by coordinate. -/
theorem compressRange_cols [Mont32BaseField p] [Binomial4 p] {pm : PMat} {s : Mat F}
    (h : RM pm s) (ap : Array EF) (hap : ap.size = s.width) (r0 len : Nat) (hlen : 0 < len)
    (hblk : r0 % pm.rows + len ≤ pm.rows) (hr : r0 + len ≤ s.height)
    (hsa : 4 * ap.size < USize.size) (hl : 4 * len < USize.size) :
    compressRange p pm (encode (ap.map (·.c0))) (encode (ap.map (·.c1)))
      (encode (ap.map (·.c2))) (encode (ap.map (·.c3))) r0 len =
      Array.ofFn (n := 4) fun c ↦ encode (Array.ofFn (n := len) fun t ↦
        coord c.val (crow s.values ap s.width (r0 + t.val))) := by
  unfold compressRange
  dsimp only
  rw [CompStark.Merkle.Packed.foldRange_eq, h.width]
  -- The rows batched by the first `J` columns.
  let part (c J t : Nat) : F := coord c ((List.range' 0 J).foldl (fun acc i ↦
    acc + Challenge.smul (s.values.getD ((r0 + t) * s.width + i) 0) (ap.getD i 0)) 0)
  let P (c J : Nat) : ByteArray := encode (Array.ofFn (n := len) fun t ↦ part c J t.val)
  have hz : CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len = encode
      (Array.ofFn (n := len) fun _ ↦ (0 : F)) := by
    rw [CompStark.Merkle.Packed.zeroWords_fields (p := p)]
    exact congrArg encode (Array.ext (by rw [Array.size_replicate, Array.size_ofFn])
      fun _ _ _ ↦ by rw [Array.getElem_replicate, Array.getElem_ofFn])
  have hstep (c J : Nat) (hJ : J < s.width) (pr : EF → F) (hpr : ∀ a, pr a = coord c a) :
      Words.mulAddInto p (P c J) (pm.colAt J r0).1 (pm.colAt J r0).2
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode (ap.map pr)) J) len =
        P c (J + 1) := by
    obtain ⟨A, e1, e2, e3, e4⟩ := colAt_spec h r0 len J hblk hr hlen hJ
    have hs : (Array.ofFn (n := len) fun t ↦ part c J t.val).size = len := Array.size_ofFn
    have hrd : CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode (ap.map pr)) J =
        (coord c (ap.getD J 0)).val := by
      rw [Words.read_encode _ _ (by rw [Array.size_map]; exact hsa) (by
        rw [Array.size_map, hap]; exact hJ), EVec.getD_map _ _ _ (by rw [hap]; exact hJ), hpr,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hap]; exact hJ),
        Option.getD_some]
    have e := Words.mulAddInto_encode (p := p) (Array.ofFn (n := len) fun t ↦ part c J t.val) A
      (pm.colAt J r0).2 (coord c (ap.getD J 0)) (by rw [hs]; exact e2) (by rw [hs]; exact hl) e3
    rw [hs] at e
    rw [hrd, e1, e]
    refine congrArg encode (congrArg Array.ofFn (funext fun t ↦ ?_))
    rw [getD_ofFn_bounded _ _ t.isLt, e4 t t.isLt]
    simp only [part]
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul, coord_add, coord_smul, mul_comm]
  have key : ∀ J ≤ s.width, (List.range J).foldl (fun (ps : ByteArray × ByteArray × ByteArray ×
      ByteArray) j ↦ (Words.mulAddInto p ps.1 (pm.colAt j r0).1 (pm.colAt j r0).2
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode (ap.map (·.c0))) j) len,
      Words.mulAddInto p ps.2.1 (pm.colAt j r0).1 (pm.colAt j r0).2
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode (ap.map (·.c1))) j) len,
      Words.mulAddInto p ps.2.2.1 (pm.colAt j r0).1 (pm.colAt j r0).2
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode (ap.map (·.c2))) j) len,
      Words.mulAddInto p ps.2.2.2 (pm.colAt j r0).1 (pm.colAt j r0).2
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read (encode (ap.map (·.c3))) j) len))
      (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len,
        CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len,
        CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len,
        CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len) =
      (P 0 J, P 1 J, P 2 J, P 3 J) := by
    intro J hJ
    induction J with
    | zero =>
      rw [List.range_zero, List.foldl_nil, hz]
      have e (c : Nat) : P c 0 = encode (Array.ofFn (n := len) fun _ ↦ (0 : F)) := by
        simp only [P, part, List.range'_zero, List.foldl_nil, coord_zero]
      rw [e 0, e 1, e 2, e 3]
    | succ J ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      dsimp only
      rw [hstep 0 J (by omega) (·.c0) fun _ ↦ rfl, hstep 1 J (by omega) (·.c1) fun _ ↦ rfl,
        hstep 2 J (by omega) (·.c2) fun _ ↦ rfl, hstep 3 J (by omega) (·.c3) fun _ ↦ rfl]
  rw [key s.width le_rfl]
  refine Array.ext (by rfl) fun c hc _ ↦ ?_
  change c < 4 at hc
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- A loop in `Id` whose every step yields simulates a fold. -/
theorem forIn_sim {α β γ : Type} (Inv : β → γ → Prop) (σ : α → γ → γ)
    (f : α → β → Id (ForInStep β)) : ∀ (l : List α) (b : β) (c : γ), Inv b c →
      (∀ a ∈ l, ∀ b c, Inv b c → ∃ b', f a b = pure (.yield b') ∧ Inv b' (σ a c)) →
      Inv (forIn l b f) (l.foldl (fun c a ↦ σ a c) c)
  | [], _, _, h, _ => h
  | a :: l, b, c, h, hs => by
    obtain ⟨b', e, h'⟩ := hs a List.mem_cons_self b c h
    rw [List.forIn_cons, e, List.foldl_cons]
    exact forIn_sim Inv σ f l b' (σ a c) h' fun a ha ↦ hs a (List.mem_cons_of_mem _ ha)

/-- A fold of functions, pointwise. -/
theorem foldl_pointwise {α : Type} (g : Nat → EF → α → EF) :
    ∀ (l : List α) (S : Nat → EF) (t : Nat),
    (l.foldl (fun c a ↦ fun r ↦ g r (c r) a) S) t = l.foldl (g t) (S t)
  | [], _, _ => rfl
  | a :: l, S, t => by
    rw [List.foldl_cons, List.foldl_cons, foldl_pointwise g l _ t]

theorem mul_comm' [Binomial4 p] (a b : EF) : a * b = b * a :=
  Ext4.toSpec_injective (by rw [Ext4.toSpec_mul, Ext4.toSpec_mul, mul_comm])

theorem mul_assoc' [Binomial4 p] (a b c : EF) : a * b * c = a * (b * c) :=
  Ext4.toSpec_injective (by
    rw [Ext4.toSpec_mul, Ext4.toSpec_mul, Ext4.toSpec_mul, Ext4.toSpec_mul, mul_assoc])

/-- The state of `reduceRange`: the running sums and the cached inverses. -/
def RInv [Mont32BaseField p] [Binomial4 p] (xr : ByteArray) (len : Nat) (s : EVec p × List
    (EF × EVec p)) (S : Nat → EF) : Prop :=
  RV s.1 (Array.ofFn (n := len) fun t ↦ S t.val) ∧ ∀ pr ∈ s.2, pr.2 = invDenoms pr.1 xr len

/-- One term of `reduceRange` on planes. -/
theorem term_rel [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F) {len : Nat}
    {acc comp : EVec p} {S C : Nat → EF}
    (X : Array F)
    (hX : X.size = len) (hl : 4 * len < USize.size)
    (hacc : RV acc (Array.ofFn (n := len) fun t ↦ S t.val))
    (hcomp : RV comp (Array.ofFn (n := len) fun t ↦ C t.val)) {z : EF} (hz : Ext.OutsideBase z)
    (yz offset : EF) :
    RV (acc.add (((EVec.rsub yz comp).mul (invDenoms z (encode X) len)).smul offset))
      (Array.ofFn (n := len) fun t ↦ termStep (C t.val) (X.getD t.val 0) (S t.val)
        (z, yz, offset)) := by
  have hinv := invDenoms_rel hζ hz X (by omega)
  rw [hX] at hinv
  have hsz : (Array.ofFn (n := len) fun t ↦ C t.val).size = len := Array.size_ofFn
  have h1 := EVec.rsub_rel yz hcomp (by rw [hsz]; exact hl)
  have h2 := EVec.mul_rel h1 hinv (by rw [h1.1, hinv.1, Array.size_map, hsz, Array.size_map, hX])
    (by rw [Array.size_map, hsz]; exact hl)
  have h3 := EVec.smul_rel offset h2 (by
    rw [Array.size_zipWith, Array.size_map, hsz, Array.size_map, hX, Nat.min_self]; exact hl)
  have h4 := EVec.add_rel hacc h3 (by
    rw [hacc.1, h3.1, Array.size_ofFn, Array.size_map, Array.size_zipWith, Array.size_map, hsz,
      Array.size_map, hX, Nat.min_self]) (by rw [Array.size_ofFn]; exact hl)
  convert h4 using 1
  refine Array.ext (by
    rw [Array.size_ofFn, Array.size_zipWith, Array.size_ofFn, Array.size_map, Array.size_zipWith,
      Array.size_map, hsz, Array.size_map, hX, Nat.min_self, Nat.min_self]) fun t h1 _ ↦ ?_
  rw [Array.size_ofFn] at h1
  simp only [Array.getElem_ofFn, Array.getElem_zipWith, Array.getElem_map, termStep, Ext.ofBase,
    Mont32.ofBase_ext4]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
    mul_assoc', mul_comm' offset, mul_assoc']

/-- The rows of a range of a group's matrix batched by the powers of `α`, as planes. -/
theorem comp_rel [Mont32BaseField p] [Binomial4 p] (alpha : EF) (logH : Nat) (it : GItem p)
    (hit : Good alpha logH it) (r0 len : Nat) (hlen : 0 < len)
    (hblk : r0 % it.1.rows + len ≤ it.1.rows) (hr : r0 + len ≤ 2 ^ logH) :
    RV ⟨len, (compressRange p it.1 it.2.1.c0 it.2.1.c1 it.2.1.c2 it.2.1.c3 r0 len).getD 0 .empty,
      (compressRange p it.1 it.2.1.c0 it.2.1.c1 it.2.1.c2 it.2.1.c3 r0 len).getD 1 .empty,
      (compressRange p it.1 it.2.1.c0 it.2.1.c1 it.2.1.c2 it.2.1.c3 r0 len).getD 2 .empty,
      (compressRange p it.1 it.2.1.c0 it.2.1.c1 it.2.1.c2 it.2.1.c3 r0 len).getD 3 .empty⟩
      (Array.ofFn (n := len) fun t ↦
        crow (it.1.vals p) (powers alpha it.1.width) it.1.width (r0 + t.val)) := by
  obtain ⟨m, a, ts⟩ := it
  obtain ⟨s, hm, h2, h3, h4, h5, -⟩ := hit
  simp only at hblk h5 ⊢
  subst h5
  generalize hap0 : powers alpha m.width = ap
  have hap : ap.size = s.width := by rw [← hap0, powers, Array.size_ofFn, hm.width]
  have hw4 : 4 * s.width < USize.size := by
    rw [hm.size] at h3
    have := Nat.mul_le_mul_left s.width (Nat.one_le_two_pow (n := logH))
    rw [h2] at h3
    omega
  have hc := compressRange_cols hm ap hap r0 len hlen hblk (by omega)
    (by rw [hap]; exact hw4) (by have := Nat.pow_le_pow_left hr 1; omega)
  simp only [EVec.ofArray, CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq, hc]
  rw [vals_rel hm, hm.width]
  have hg (c : Nat) (hc4 : c < 4) :
      (Array.ofFn (n := 4) fun c ↦ encode
          (Array.ofFn (n := len) fun t ↦ coord c.val
              (crow s.values ap s.width (r0 + t.val)))).getD c .empty =
      encode (Array.ofFn (n := len) fun t ↦ coord c
        (crow s.values ap s.width (r0 + t.val))) :=
    getD_ofFn_bounded _ _ hc4 _
  rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide), hg 3 (by decide)]
  exact EVec.rv_ofFn _ Array.size_ofFn _ _ _ _ fun t ↦ by rw [Array.getElem_ofFn]; rfl

theorem lookup_mem {k : EF} {v : EVec p} : ∀ {l : List (EF × EVec p)}, l.lookup k = some v →
    (k, v) ∈ l
  | [], h => absurd h (by simp only [List.lookup, reduceCtorEq, not_false_eq_true])
  | (k', v') :: l, h => by
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      rw [h]
      exact List.mem_cons_self
    · simp only [List.lookup, beq_false_of_ne hk] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A range of rows of a group's batched quotient, on planes. -/
theorem reduceRange_rel [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F) (alpha : EF)
    (logH : Nat) (g : Array (GItem p))
    (hg : ∀ it ∈ g, Good alpha logH it) (h4 : 4 * 2 ^ logH < USize.size) (r0 len : Nat)
    (hlen : 0 < len) (hblk : ∀ it ∈ g, r0 % it.1.rows + len ≤ it.1.rows)
    (hr : r0 + len ≤ 2 ^ logH) :
    RV (reduceRange g (encode (cosetPointsBitRev (gen : F) logH)) r0 len)
      (Array.ofFn (n := len) fun t ↦ gval alpha logH g (r0 + t.val)) := by
  have hXs := size_cosetPointsBitRev (gen : F) logH
  have hxr : slice (encode (cosetPointsBitRev (gen : F) logH)) r0 len =
      encode ((cosetPointsBitRev (gen : F) logH).extract r0 (r0 + len)) := extract_encode _ r0
          (r0 + len)
  generalize hXr : (cosetPointsBitRev (gen : F) logH).extract r0 (r0 + len) = Xr at hxr
  have hXrs : Xr.size = len := by rw [← hXr, Array.size_extract]; omega
  have hXget (t : Nat) (ht : t < len) :
      Xr.getD t 0 = (cosetPointsBitRev (gen : F) logH).getD (r0 + t) 0 := by
    rw [← hXr, Array.getD_eq_getD_getElem?, Array.getElem?_extract,
      ite_eq_left_of_eq_true _ _ (eq_true (by rw [Nat.min_def]; split <;> omega)),
      Array.getD_eq_getD_getElem?]
  have hl : 4 * len < USize.size := by omega
  -- One term at row `r` of the range, for the matrix `it`.
  let σ' (it : GItem p) (S : Nat → EF) (tm : EF × EF × EF) : Nat → EF := fun r ↦
    termStep (crow (it.1.vals p) (powers alpha it.1.width) it.1.width (r0 + r))
      (Xr.getD r 0) (S r) tm
  let σ (it : GItem p) (S : Nat → EF) : Nat → EF := it.2.2.foldl (σ' it) S
  suffices H : ∀ f, (∀ a ∈ g.toList, ∀ b c, RInv (encode Xr) len b c →
      ∃ b', f a b = pure (.yield b') ∧ RInv (encode Xr) len b' (σ a c)) →
      RV ((forIn g.toList (EVec.zeros len, []) f) >>= fun s ↦ pure s.1 : Id (EVec p))
        (Array.ofFn (n := len) fun t ↦ gval alpha logH g (r0 + t.val)) by
    simp only [reduceRange, Id.run, pure_bind]
    rw [hxr, ← Array.forIn_toList]
    refine H _ fun it hit b c hb ↦ ⟨_, rfl, ?_⟩
    obtain ⟨-, -, -, -, -, -, hz⟩ := hg it (Array.mem_toList_iff.mp hit)
    have hcomp := comp_rel alpha logH it (hg it (Array.mem_toList_iff.mp hit)) r0 len hlen
      (hblk it (Array.mem_toList_iff.mp hit)) hr
    exact forIn_sim (RInv (encode Xr) len) (fun tm S ↦ σ' it S tm) _ it.2.2 (b.1, b.2) c hb
      fun tm htm b c hb ↦ by
        split
        · rename_i inv hinv
          have e : inv = invDenoms tm.1 (encode Xr) len := hb.2 _ (lookup_mem hinv)
          subst e
          refine ⟨_, rfl, ?_, hb.2⟩
          exact term_rel hζ (C := fun r ↦ crow (it.1.vals p) (powers alpha it.1.width)
            it.1.width (r0 + r)) Xr hXrs hl hb.1 hcomp (hz tm htm) tm.2.1 tm.2.2
        · refine ⟨_, rfl, term_rel hζ
            (C := fun r ↦ crow (it.1.vals p) (powers alpha it.1.width) it.1.width
                (r0 + r)) Xr hXrs hl hb.1 hcomp (hz tm htm) tm.2.1 tm.2.2,
            ?_⟩
          intro pr hp
          rcases List.mem_cons.mp hp with hp | hp
          · rw [hp]
          · exact hb.2 pr hp
  intro f hf
  have := forIn_sim (RInv (encode Xr) len) σ f g.toList (EVec.zeros len, []) (fun _ ↦ 0)
    ⟨by
      have := EVec.zeros_rel (p := p) len
      convert this using 1
      exact Array.ext (by rw [Array.size_ofFn, Array.size_replicate]) fun i _ _ ↦ by
        rw [Array.getElem_ofFn, Array.getElem_replicate],
     fun pr hp ↦ absurd hp List.not_mem_nil⟩ hf
  convert this.1 using 1
  refine congrArg Array.ofFn (funext fun t ↦ ?_)
  have key : ∀ (l : List (GItem p)) (S : Nat → EF), (l.foldl (fun c a ↦ σ a c) S) t.val = l.foldl
      (fun a it ↦ it.2.2.foldl (termStep
        (crow (it.1.vals p) (powers alpha it.1.width) it.1.width (r0 + t.val))
        ((cosetPointsBitRev (gen : F) logH).getD (r0 + t.val) 0)) a) (S t.val) := by
    intro l
    induction l with
    | nil => intro S; rfl
    | cons a l ih =>
      intro S
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      rw [← hXget t.val t.isLt]
      exact foldl_pointwise (fun r acc tm ↦ termStep (crow (a.1.vals p)
        (powers alpha a.1.width) a.1.width (r0 + r)) (Xr.getD r 0) acc tm) a.2.2 S t.val
  rw [key]
  rfl

theorem gcd_fold_dvd_init {α : Type} (f : α → Nat) :
    ∀ (l : List α) (b : Nat), l.foldl (fun a x ↦ Nat.gcd a (f x)) b ∣ b
  | [], _ => dvd_rfl
  | x :: l, b => by
    rw [List.foldl_cons]; exact (gcd_fold_dvd_init f l _).trans (Nat.gcd_dvd_left _ _)

theorem gcd_fold_dvd {α : Type} (f : α → Nat) :
    ∀ (l : List α) (b : Nat), ∀ x ∈ l, l.foldl (fun a x ↦ Nat.gcd a (f x)) b ∣ f x
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: l, b, x, hx => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (gcd_fold_dvd_init f l _).trans (Nat.gcd_dvd_right _ _)
    · exact gcd_fold_dvd f l _ x hx

theorem gcd_fold_pos {α : Type} (f : α → Nat) :
    ∀ (l : List α) (b : Nat), 0 < b → 0 < l.foldl (fun a x ↦ Nat.gcd a (f x)) b
  | [], _, hb => hb
  | _ :: l, _, hb => by
    rw [List.foldl_cons]; exact gcd_fold_pos f l _ (Nat.gcd_pos_of_pos_left _ hb)

/-- A group's planes, by parallel ranges within one block of every matrix, hold its batched
quotient. -/
theorem groupPlanes_rel [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F) (alpha : EF)
    (G : Nat × Nat × Array (GItem p))
    (h4 : 4 * 2 ^ G.1 < USize.size)
    (hg : ∀ it ∈ G.2.2, Good alpha G.1 it) :
    RV (groupPlanes G).2 (Array.ofFn (n := 2 ^ G.1) fun r ↦ gval alpha G.1 G.2.2 r.val) := by
  obtain ⟨logH, c, g⟩ := G
  simp only at h4 hg ⊢
  unfold groupPlanes
  dsimp only
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq]
  have hfold : g.foldl (fun a (x : GItem p) ↦ match x with | (m, _) => Nat.gcd a m.rows)
      (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) =
      g.toList.foldl (fun a (x : GItem p) ↦ Nat.gcd a x.1.rows)
        (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) := by
    rw [← Array.foldl_toList]
  rw [hfold]
  have hDd : g.toList.foldl (fun a (x : GItem p) ↦ Nat.gcd a x.1.rows)
      (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) ∣ 2 ^ logH :=
    (gcd_fold_dvd_init _ _ _).trans (by
      split
      · exact dvd_rfl
      · rename_i hL
        have h4 : 4 ≤ logH := by
          by_contra hc
          have := Nat.pow_lt_pow_right (show 1 < 2 by decide) (show logH < 4 by omega)
          omega
        exact Nat.div_dvd_of_dvd (Nat.pow_dvd_pow 2 h4))
  have hA0 : 0 < (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) := by
    split
    · exact Nat.two_pow_pos _
    · omega
  have hD0 : 0 < g.toList.foldl (fun a (x : GItem p) ↦ Nat.gcd a x.1.rows)
      (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) :=
    gcd_fold_pos (fun x : GItem p ↦ x.1.rows) g.toList _ hA0
  have hDr : ∀ it ∈ g, g.toList.foldl (fun a (x : GItem p) ↦ Nat.gcd a x.1.rows)
      (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) ∣ it.1.rows :=
    fun it hit ↦ gcd_fold_dvd (fun x : GItem p ↦ x.1.rows) _ _ it (Array.mem_toList_iff.mpr hit)
  generalize g.toList.foldl (fun a (x : GItem p) ↦ Nat.gcd a x.1.rows)
    (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) = D at hDd hD0 hDr ⊢
  obtain ⟨hp, hpD, hranges⟩ := uniform_ranges hD0 hDd (Nat.two_pow_pos logH)
  generalize 2 ^ logH / D = parts at hp hpD hranges ⊢
  rw [← foldl_ranges (fun r ↦ gval alpha logH g r) (2 ^ logH) parts (2 ^ logH / parts) hp
    (ranges_cover _ _)]
  refine joinPlanes_rel _ parts _ _ (fun k hk ↦ ?_) (by
    rw [foldl_ranges (fun r ↦ gval alpha logH g r) (2 ^ logH) parts (2 ^ logH / parts) hp
      (ranges_cover _ _), Array.size_ofFn])
  obtain ⟨hlen, hcov⟩ := hranges k hk
  rw [hlen, hpD]
  exact reduceRange_rel hζ alpha logH g hg h4 (k * D) D hD0
    (fun it hit ↦ mod_add_le_of_dvd (by obtain ⟨s, hm, -⟩ := hg it hit; exact hm.pos)
      (hDr it hit) (Nat.dvd_mul_left D k))
    hcov

/-- The fast reduction is the specification's. -/
theorem reduce_rel [Mont32BaseField p] [Binomial4 p] (hζ : 2 ≤ twoAdicity F) (alpha : EF)
    {items : List (PMat × List (EF × Array EF))}
    {sitems : List (Mat F × List (EF × Array EF))}
    (h : List.Forall₂ (fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) items sitems)
    (hok : ∀ x ∈ sitems, MatOk x.1 ∧ ∀ pr ∈ x.2, Ext.OutsideBase pr.1) :
    List.Forall₂ (fun x y ↦ x.1 = y.1 ∧ RV x.2 y.2) (reduce alpha items)
      (Fri.reduce alpha sitems) := by
  rw [reduce_fast alpha items, reduce_eq, List.map_mergeSort
    (r := fun (a b : Nat × Nat × Array EF) ↦ decide (b.1 ≤ a.1))
    (s := fun (a b : Nat × Array EF) ↦ decide (b.1 ≤ a.1)) (f := fun x ↦ (x.1, x.2.2))
    (fun _ _ _ _ ↦ rfl)]
  refine forall₂_mergeSort (fun (a : Nat × EVec p) ↦ a.1) (fun (b : Nat × Array EF) ↦ b.1) ?_
    (fun _ _ hab ↦ hab.1)
  have hgr := foldl_groupStep_rel alpha h hok List.Forall₂.nil
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine hgr.imp fun G S hGS ↦ ⟨hGS.1, ?_⟩
  obtain ⟨-, -, h3, h4, h5⟩ := hGS
  rw [h3]
  exact groupPlanes_rel hζ alpha G h4 h5
