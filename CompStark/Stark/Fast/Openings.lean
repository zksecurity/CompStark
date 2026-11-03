/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Commit
public import CompStark.Stark.Fast.OpeningsSpec
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
open Montgomery.Native32.Words
open CompPoly.Array (batchInv batchInv_eq)
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

variable {p : ℕ} [Mont32Field p] {EF : Type} [FastExt p EF]

local notation "F" => FastField p

/-! ### Coordinates -/

theorem coord_add (c : Nat) (a b : EF) : coord c (a + b) = coord c a + coord c b := by
  unfold coord
  split
  · rw [FastExt.coord_add]; rfl
  · rw [add_zero]

theorem coord_smul [Mont32BaseField p] [Mont32.AlgebraId EF] (c : Nat) (x : F) (a : EF) :
    coord c (Challenge.smul x a) = x * coord c a := by
  unfold coord
  split
  · show FastExt.coord (FastExt.ofCoords fun i ↦ x * FastExt.coord a i) _ = _
    rw [FastExt.coord_ofCoords]
  · rw [mul_zero]

theorem coord_zero (c : Nat) : coord c (0 : EF) = 0 := by
  unfold coord
  split
  · rw [FastExt.coord_zero]; rfl
  · rfl

theorem ext_coord {a b : EF} (h : ∀ c < FastExt.d p EF, coord c a = coord c b) : a = b :=
  FastExt.ext fun i ↦ by rw [← coord_fin, ← coord_fin, h i i.isLt]

/-- Coordinate `c` of a sum of scaled elements is the sum of the scaled coordinates. -/
theorem coord_foldl_smul [Mont32BaseField p] [Mont32.AlgebraId EF] (f : Nat → F) (g : Nat → EF) (c :
    Nat)
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

/-- The extension element of the coordinates `f`. -/
def mkE (f : Nat → F) : EF := FastExt.ofCoords fun i ↦ f i

theorem coord_mkE (f : Nat → F) (c : Nat) (hc : c < FastExt.d p EF) :
    coord c (mkE (EF := EF) f) = f c := by
  rw [coord, dite_eq_left hc, mkE, FastExt.coord_ofCoords]

/-- A column sum of the specification, coordinate by coordinate, reindexed to the stored rows. -/
theorem coord_colSum [Mont32BaseField p] [Mont32.AlgebraId EF] (values : Array F) (w L j : Nat) {z :
    EF}
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
theorem openedAt_sum [Mont32BaseField p] [Mont32.AlgebraId EF] (b : Nat) (s : Mat F) {z : EF}
    (hz : Ext.OutsideBase z) :
    Fri.openedAt b s z = Array.ofFn (n := s.width) fun j ↦
      Fri.cosetFactor (Nat.log2 s.height - b) gen z * mkE fun c ↦
        ∑ r ∈ Finset.range (2 ^ (Nat.log2 s.height - b)), s.values.getD (r * s.width + j.val) 0 *
          coord c (bw z ((cosetPointsBitRev (gen : F) (Nat.log2 s.height - b)).getD r 0)) := by
  rw [openedAt_eq]
  refine Array.ext (by rw [Array.size_ofFn, Array.size_ofFn]) fun j h1 h2 ↦ ?_
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  exact congrArg _ (ext_coord fun c hc ↦ by rw [coord_mkE _ _ hc, coord_colSum _ _ _ _ hz])

/-! ### `1 / (z - x)` once per point -/

/-- Reversing the bits of `0`. -/
theorem bitRevNat_zero : ∀ b, bitRevNat b 0 = 0
  | 0 => by
    have := bitRevNat_lt 0 0
    rw [Nat.pow_zero] at this
    omega
  | b + 1 => by
    have := CompPoly.CPolynomial.NTT.Transform.bitRevNat_even b 0
    rw [Nat.mul_zero, bitRevNat_zero b] at this
    exact this

/-- The stored points of `shift · ⟨ω⟩` of size `2 ^ k` are the first ones of any larger size. -/
theorem cosetPointsBitRev_prefix {G : Type} [BaseField G] (shift : G) {k L : Nat} (hkL : k ≤ L)
    (hL : L ≤ twoAdicity G) {i : Nat} (hi : i < 2 ^ k) :
    (cosetPointsBitRev shift L).getD i 0 = (cosetPointsBitRev shift k).getD i 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, L = e + k := ⟨L - k, by omega⟩
  have hi' : i < 2 ^ (e + k) := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega))
  have hc := CompPoly.CPolynomial.NTTFast.Packed.bitRevNat_concat e k 0 i hi
  rw [Nat.mul_zero, Nat.zero_add, bitRevNat_zero, Nat.add_zero] at hc
  rw [cosetPointsBitRev_getD _ _ _ hi', cosetPointsBitRev_getD _ _ _ hi, cosetPoints_eq,
    cosetPoints_eq, CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ (bitRevNat_lt _ _),
    CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ (bitRevNat_lt _ _)]
  show _ * _ ^ bitRevNat (e + k) i = _ * _ ^ bitRevNat k i
  rw [hc, pow_mul, Nat.add_comm e k, BaseField.twoAdicGen_pow k e (by omega)]

/-- The planes `invs` hold `1 / (z - x)` for the point `z` on the stored points `x` of a height
`2 ^ L` of at least `2 ^ logH`. -/
def DenomsOk [Mont32BaseField p] (invs : List (EF × Nat × ExtPlanes p EF)) (z : EF)
    (logH : Nat) : Prop :=
  ∃ L, logH ≤ L ∧ L ≤ twoAdicity F ∧ ExtPlanes.Rel (denomsOf invs z)
    (tab (2 ^ L) fun r ↦ (z - FastExt.ofBase ((cosetPointsBitRev (gen : F) L).getD r 0))⁻¹)

theorem DenomsOk.mono [Mont32BaseField p] {invs : List (EF × Nat × ExtPlanes p EF)} {z : EF} {k logH : Nat}
    (h : DenomsOk invs z logH) (hk : k ≤ logH) : DenomsOk invs z k := by
  obtain ⟨L, h1, h2, h3⟩ := h
  exact ⟨L, by omega, h2, h3⟩

/-- A range of the planes of `1 / (z - x)` on the stored points of height `2 ^ logH`. -/
theorem DenomsOk.slice [Mont32BaseField p] {invs : List (EF × Nat × ExtPlanes p EF)} {z : EF} {logH : Nat}
    (h : DenomsOk invs z logH) {r0 len : Nat} (hr : r0 + len ≤ 2 ^ logH) :
    ExtPlanes.Rel (slicePlanes (denomsOf invs z) r0 len) (tab len fun t ↦
      (z - FastExt.ofBase ((cosetPointsBitRev (gen : F) logH).getD (r0 + t) 0))⁻¹) := by
  obtain ⟨L, h1, h2, h3⟩ := h
  obtain ⟨-, hc⟩ := ExtPlanes.rel_tab_iff.mp h3
  have hle : 2 ^ logH ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) h1
  refine ExtPlanes.rel_mk _ _ fun k ↦ ?_
  have hk := hc k
  simp only [Fin.getElem_fin] at hk ⊢
  rw [Vector.getElem_map, hk, slice_encode]
  refine congrArg encode (Array.ext (by rw [Array.size_extract, size_tab, size_tab]; omega)
    fun t h4 _ ↦ ?_)
  rw [Array.size_extract, size_tab] at h4
  rw [Array.getElem_extract, getElem_tab, getElem_tab,
    cosetPointsBitRev_prefix (gen : F) h1 h2 (by omega)]

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
    transposeRows (encode M) w 0 w r0 rows = encode (Array.ofFn (n := w * rows) fun k ↦
      M.getD ((r0 + k.val % rows) * w + k.val / rows) 0) := by
  rw [CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val M,
    CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows_encodeWords _ _ _ _ _ _ (by omega)
      (by rw [Array.size_map]; exact hM) (by rw [Array.size_map]; exact hs),
    CompPoly.CPolynomial.NTTFast.Packed.encode_eq_map_val]
  refine congrArg encode (Array.ext (by rw [Array.size_map, Array.size_ofFn, Array.size_ofFn])
    fun k _ _ ↦ ?_)
  rw [Array.getElem_map, Array.getElem_ofFn, Array.getElem_ofFn,
    CompPoly.CPolynomial.NTTFast.Packed.getD_map_val, Nat.add_zero]

/-- The weight planes of a range of stored points. -/
theorem weightPlane [Mont32BaseField p] [Mont32.AlgebraId EF]
    (invs : List (EF × Nat × ExtPlanes p EF)) {z : EF} (X : Array F) (r0 len : Nat)
    (hX : r0 + len ≤ X.size) (hs : 4 * X.size < USize.size)
    (hinv : ExtPlanes.Rel (slicePlanes (denomsOf invs z) r0 len)
      (tab len fun t ↦ (z - FastExt.ofBase (X.getD (r0 + t) 0))⁻¹)) :
    ((slicePlanes (denomsOf invs z) r0 len).mulBase (slice (encode X) r0 len)).c.toArray =
    Array.ofFn (n := FastExt.d p EF) fun c ↦ encode (Array.ofFn (n := len)
      fun t ↦ coord c (bw z (X.getD (r0 + t.val) 0))) := by
  have hn : 4 * len < USize.size := by omega
  let g (t : Nat) : F := X.getD (r0 + t) 0
  have hxr : slice (encode X) r0 len = encode (tab len g) := by
    rw [show slice (encode X) r0 len = encode (X.extract r0 (r0 + len)) from
      extract_encode X r0 (r0 + len)]
    refine congrArg encode (Array.ext (by rw [Array.size_extract, size_tab]; omega)
      fun t h1 _ ↦ ?_)
    rw [Array.size_extract] at h1
    rw [Array.getElem_extract, getElem_tab]
    exact (getD_lt X _ (by omega)).symm
  have hrv := ExtPlanes.mulBase_rel hn g hinv
  rw [hxr]
  obtain ⟨-, hc⟩ := ExtPlanes.rel_tab_iff.mp hrv
  refine Array.ext (by simp) fun c h1 _ ↦ ?_
  simp only [Vector.size_toArray] at h1
  rw [Vector.getElem_toArray, Array.getElem_ofFn]
  have := hc ⟨c, h1⟩
  simp only [Fin.getElem_fin] at this
  rw [this]
  refine congrArg encode (congrArg Array.ofFn (funext fun t ↦ ?_))
  rw [coord, dite_eq_left h1, bw, Mont32.smul_eq, FastExt.mul_comm, ← Mont32.ofBase_eq]
  rfl

/-- Appending `n` elements per item. -/
theorem foldl_append_ofFnN {α : Type} {n : Nat} (hn : 0 < n) (R : EF → Fin n → α) :
    ∀ (l : List EF) (b : Array α), l.foldl (fun b z ↦ b ++ Array.ofFn (R z)) b =
      b ++ Array.ofFn (n := n * l.length) fun i ↦ R (l.getD (i.val / n) 0)
        ⟨i.val % n, Nat.mod_lt _ hn⟩
  | [], b => by rw [List.foldl_nil, Array.eq_empty_of_size_eq_zero (xs := Array.ofFn _)
      (by rw [Array.size_ofFn]; rfl), Array.append_empty]
  | a :: l, b => by
    rw [List.foldl_cons, foldl_append_ofFnN hn R l, Array.append_assoc]
    congr 1
    refine Array.ext (by rw [Array.size_append, Array.size_ofFn, Array.size_ofFn, Array.size_ofFn,
      List.length_cons, Nat.mul_succ, Nat.add_comm]) fun i h1 h2 ↦ ?_
    rw [Array.getElem_ofFn, Array.getElem_append]
    split
    · rename_i h
      rw [Array.size_ofFn] at h
      rw [Array.getElem_ofFn, Nat.div_eq_of_lt h, List.getD_cons_zero]
      exact congrArg _ (Fin.ext (by simp only; exact (Nat.mod_eq_of_lt h).symm))
    · rename_i h
      rw [Array.size_ofFn] at h
      simp only [Array.getElem_ofFn, Array.size_ofFn]
      have hq : i / n = (i - n) / n + 1 := by
        rw [Nat.div_eq_sub_div hn (by omega)]
      have hr : i % n = (i - n) % n := by
        rw [Nat.mod_eq_sub_mod (by omega)]
      congr 1
      · rw [hq, List.getD_cons_succ]
      · exact Fin.ext (by simp only; exact hr.symm)

/-- The weight planes of a range of stored points, for every point and coordinate. -/
theorem weightPlanes_encode [Mont32BaseField p] [Mont32.AlgebraId EF]
    (invs : List (EF × Nat × ExtPlanes p EF)) (zs : Array EF) (X : Array F) (r0 len : Nat)
    (hX : r0 + len ≤ X.size) (hsX : 4 * X.size < USize.size)
    (hinv : ∀ z ∈ zs, ExtPlanes.Rel (slicePlanes (denomsOf invs z) r0 len)
      (tab len fun t ↦ (z - FastExt.ofBase (X.getD (r0 + t) 0))⁻¹)) :
    weightPlanes invs zs (encode X) r0 len = Array.ofFn (n := FastExt.d p EF * zs.size) fun i ↦
      encode (Array.ofFn (n := len) fun t ↦
        coord (i.val % FastExt.d p EF) (bw (zs.toList.getD (i.val / FastExt.d p EF) 0)
          (X.getD (r0 + t.val) 0))) := by
  unfold weightPlanes
  rw [← Array.foldl_toList, List.foldl_ext _ (fun b z ↦ b ++
    Array.ofFn (n := FastExt.d p EF) fun c ↦
    encode (Array.ofFn (n := len) fun t ↦ coord c.val (bw z (X.getD (r0 + t.val) 0)))) _ ?_,
    foldl_append_ofFnN (FastExt.params (p := p) EF).d_pos, Array.empty_append]
  · rfl
  intro b z hz'
  dsimp only
  rw [weightPlane invs X r0 len hX hsX (hinv z (Array.mem_toList_iff.mp hz'))]

/-- The fast column sums of a range of stored rows within one block of the matrix: for every point
and coordinate, a plane of a sum per column, of the rows times the weights of their points. -/
theorem weightedColumns_cols [Mont32BaseField p] [Mont32.AlgebraId EF]
    (invs : List (EF × Nat × ExtPlanes p EF)) {pm : PMat} {s : Mat F} (h : RM pm s)
    (zs : Array EF) (X : Array F) (r0 len : Nat) (hlen : 0 < len)
    (hblk : r0 % pm.rows + len ≤ pm.rows) (hr : r0 + len ≤ s.height) (hX : r0 + len ≤ X.size)
    (hsX : 4 * X.size < USize.size)
    (hinv : ∀ z ∈ zs, ExtPlanes.Rel (slicePlanes (denomsOf invs z) r0 len)
      (tab len fun t ↦ (z - FastExt.ofBase (X.getD (r0 + t) 0))⁻¹)) :
    weightedColumns invs pm zs (encode X) r0 len =
      Array.ofFn (n := FastExt.d p EF * zs.size) fun i ↦ encode (Array.ofFn (n := s.width) fun j ↦
        ∑ t ∈ Finset.range len, s.values.getD ((r0 + t) * s.width + j.val) 0 *
          coord (i.val % FastExt.d p EF) (bw (zs.toList.getD (i.val / FastExt.d p EF) 0)
            (X.getD (r0 + t) 0))) := by
  unfold Fast.weightedColumns
  dsimp only
  rw [weightPlanes_encode invs zs X r0 len hX hsX hinv, Array.size_ofFn, h.width]
  let P (i t : Nat) : F := coord (i % FastExt.d p EF)
    (bw (zs.toList.getD (i / FastExt.d p EF) 0) (X.getD (r0 + t) 0))
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
  exact Words.addWords_ofFn hw _ _

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
      rw [Array.getElem_replicate, Array.getElem_ofFn, Words.zeroWords_ofFn (p := p)]
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

theorem size_openedAt [Mont32BaseField p] [Mont32.AlgebraId EF] (b : Nat) (s : Mat F) (z : EF) :
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
theorem openedAt_rel [Mont32BaseField p] [Mont32.AlgebraId EF]
    (invs : List (EF × Nat × ExtPlanes p EF)) (b : Nat) (zs : List EF) {m : PMat} {s : Mat F}
    (h : RM m s) (hs : MatOk s) (hz : ∀ z ∈ zs, Ext.OutsideBase z)
    (hinv : ∀ z ∈ zs, DenomsOk invs z (Nat.log2 s.height - b)) :
    openedAt invs b m zs = zs.map (Fri.openedAt b s) := by
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
  generalize hL : Nat.log2 s.height - b = L at hle hinv ⊢
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
  have hd := (FastExt.params (p := p) EF).d_pos
  rw [parts_sum (FastExt.d p EF * zs.length) s.width (2 ^ L) _ hp hw4
    (fun i j r ↦ s.values.getD (r * s.width + j) 0 *
      coord (i % FastExt.d p EF) (bw (zs.getD (i / FastExt.d p EF) 0)
        ((cosetPointsBitRev (gen : F) L).getD r 0)))
    (fun r0 len ↦ weightedColumns invs m zs.toArray
      (encode (cosetPointsBitRev (gen : F) L)) r0 len) (fun k hk ↦ ?_)]
  · refine List.ext_getElem
      (by rw [List.length_map, List.length_map, List.length_zipIdx]) fun k h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [List.length_map, List.length_zipIdx] at h1
    rw [openedAt_sum b s (hz _ (List.getElem_mem _)), hL]
    refine congrArg Array.ofFn (funext fun j ↦ congrArg _ (FastExt.ext fun c ↦ ?_))
    rw [mkE, FastExt.coord_ofCoords]
    have hidx : FastExt.d p EF * k + c < FastExt.d p EF * zs.length := by
      have := Nat.mul_le_mul_left (FastExt.d p EF) (show k + 1 ≤ zs.length by omega)
      have hc : (c : ℕ) < FastExt.d p EF := c.isLt
      rw [Nat.mul_succ] at this; omega
    rw [word_plane (FastExt.d p EF * zs.length) s.width (fun i j ↦
        ∑ r ∈ Finset.range (2 ^ L), s.values.getD (r * s.width + j) 0 *
          coord (i % FastExt.d p EF) (bw (zs.getD (i / FastExt.d p EF) 0)
            ((cosetPointsBitRev (gen : F) L).getD r 0))) _ j hidx j.isLt hw4]
    have hq : (FastExt.d p EF * k + c) / FastExt.d p EF = k := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt c.isLt, Nat.zero_add]
    have hr : (FastExt.d p EF * k + c) % FastExt.d p EF = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]
    simp only [hq, hr, List.getD_eq_getElem _ _ h1, FastExt.coord_ofCoords]
  · obtain ⟨hlen, hcov⟩ := hranges k hk
    rw [hlen, hpG]
    rw [weightedColumns_cols invs h zs.toArray _ (k * G) G hG0
      (mod_add_le_of_dvd h.pos hGR (Nat.dvd_mul_left G k)) (by omega) (by omega) hsX
      fun z hz' ↦ (hinv z (List.mem_toArray.mp hz')).slice (by omega)]
    rfl

/-! ### The specification's reduction row by row -/


/-! ### The fast reduction as a fold -/

section
variable (invs : List (EF × Nat × ExtPlanes p EF))

/-- A matrix of a group of the fast reduction: the packed matrix, the powers of `α` as planes,
and its terms `(z, yz, offset)`. -/
abbrev GItem (q : ℕ) [Mont32Field q] (E : Type) [FastExt q E] :=
  PMat × ExtPlanes q E × List (E × E × E)

/-- One matrix of the fast reduction's grouping by height. -/
def groupStep [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (groups : List (Nat × Nat ×
    Array
    (GItem p EF)))
    (it : PMat × List (EF × Array EF)) : List (Nat × Nat × Array (GItem p EF)) :=
  let m := it.1
  let logH := Nat.log2 m.height
  let start := (groups.lookup logH).getD (0, #[])
  let ap := Array.ofFn (n := m.width) fun i ↦ Ext.pow alpha i.val
  let res := it.2.foldl (termsStep alpha ap m.width) (start.1, [])
  (logH, res.1, start.2.push (m, ExtPlanes.ofArray ap, res.2)) ::
    groups.filter (·.1 != logH)

/-- The batched quotient of one group, by parallel ranges of rows within one block of every
matrix. -/
def groupPlanes [Mont32BaseField p] [Mont32.AlgebraId EF] (G : Nat × Nat × Array
    (GItem p EF)) : Nat × ExtPlanes p EF :=
  let n := 2 ^ G.1
  let parts := n / G.2.2.foldl (fun a (m, _) ↦ Nat.gcd a m.rows) (if n < 4096 then n else n / 16)
  let size := n / parts
  (G.1, ExtPlanes.join n <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    (reduceRange invs G.2.2 (k * size) (if k + 1 = parts then n - k * size else size)).c.toArray)

/-- The fast reduction groups by height, then computes every group's planes. -/
theorem reduce_fast [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (items : List (PMat ×
    List
    (EF × Array EF))) :
    reduce invs alpha items = ((items.foldl (groupStep alpha) []).map (groupPlanes invs)).mergeSort
      fun a b ↦ decide (b.1 ≤ a.1) := by
  simp only [reduce, Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

/-! ### The grouping simulates the specification's fold -/

/-- Row `r` of a group's batched quotient: every term of every matrix in order. -/
def gval [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (logH : Nat) (g : Array (GItem p
    EF))
    (r : Nat) : EF :=
  g.toList.foldl (fun a it ↦ it.2.2.foldl (termStep
    (crow (it.1.vals p) (powers alpha it.1.width) it.1.width r)
    ((cosetPointsBitRev (gen : F) logH).getD r 0)) a) 0

/-- A matrix of a group of height `2 ^ logH` the fast kernels compute on. -/
def Good [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (logH : Nat) (it : GItem p EF) :
    Prop :=
  ∃ s : Mat F, RM it.1 s ∧ s.height = 2 ^ logH ∧ 4 * s.values.size < USize.size ∧
    16 * 2 ^ logH < USize.size ∧ it.2.1 = ExtPlanes.ofArray (powers alpha it.1.width) ∧
    ∀ t ∈ it.2.2, Ext.OutsideBase t.1 ∧ DenomsOk invs t.1 logH

/-- A fast group represents the specification's running sums of its height. -/
def GR [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (G : Nat × Nat × Array (GItem p EF))
    (S : Nat × Nat × Array EF) : Prop :=
  G.1 = S.1 ∧ G.2.1 = S.2.1 ∧ S.2.2 = Array.ofFn (n := 2 ^ G.1) (fun r ↦ gval alpha G.1 G.2.2 r) ∧
    16 * 2 ^ G.1 < USize.size ∧ ∀ it ∈ G.2.2, Good invs alpha G.1 it

/-- Related group lists hold related groups of every height. -/
theorem lookup_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (k : Nat) {l1 : List
    (Nat × Nat × Array (GItem p EF))}
    {l2 : List (Nat × Nat × Array EF)} (h : List.Forall₂ (GR invs alpha) l1 l2) :
    (l1.lookup k = none ∧ l2.lookup k = none) ∨ ∃ c g, l1.lookup k = some (c, g) ∧
      l2.lookup k = some (c, Array.ofFn (n := 2 ^ k) fun r ↦ gval alpha k g r) ∧
      ∀ it ∈ g, Good invs alpha k it := by
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

theorem filter_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (k : Nat) {l1 : List
    (Nat × Nat × Array (GItem p EF))}
    {l2 : List (Nat × Nat × Array EF)} (h : List.Forall₂ (GR invs alpha) l1 l2) :
    List.Forall₂ (GR invs alpha) (l1.filter (·.1 != k)) (l2.filter (·.1 != k)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons G S l1 l2 hGS _ ih =>
    rw [List.filter_cons, List.filter_cons, hGS.1]
    split
    · exact List.Forall₂.cons hGS ih
    · exact ih

theorem mem_terms [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (ap : Array EF) (w : Nat) :
    ∀
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

theorem gval_push [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (logH : Nat) (g : Array
    (GItem p EF))
    (it : GItem p EF)
    (r : Nat) : gval alpha logH (g.push it) r = it.2.2.foldl (termStep
      (crow (it.1.vals p) (powers alpha it.1.width) it.1.width r)
      ((cosetPointsBitRev (gen : F) logH).getD r 0)) (gval alpha logH g r) := by
  rw [gval, gval, Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- One matrix of the grouping simulates one step of the specification's fold. -/
theorem groupStep_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) {groups : List
    (Nat × Nat × Array (GItem p EF))}
    {red : List (Nat × Nat × Array EF)} (hgr : List.Forall₂ (GR invs alpha) groups red) {m : PMat}
    {s : Mat F} (hm : RM m s) (pts : List (EF × Array EF)) (hs : MatOk s)
    (hz : ∀ pr ∈ pts, Ext.OutsideBase pr.1 ∧ DenomsOk invs pr.1 (Nat.log2 s.height)) :
    List.Forall₂ (GR invs alpha) (groupStep alpha groups (m, pts)) (reduceStep alpha red (s, pts)) := by
  obtain ⟨hw0, ⟨k, -, hk⟩, hM, hA⟩ := hs
  unfold Addressable at hA
  have hsV : 4 * s.values.size < USize.size := by omega
  have hpow : m.height = 2 ^ Nat.log2 m.height := by rw [hm.height, hk, Nat.log2_two_pow]
  have hus : 16 * m.height < USize.size := by
    have := Nat.le_mul_of_pos_left s.height hw0
    rw [hm.height]
    omega
  have hw := hm.width
  have hh := hm.height
  unfold groupStep reduceStep
  dsimp only
  rw [hw, hh]
  rw [hh] at hpow hus
  generalize hL : Nat.log2 s.height = logH at hpow hz
  refine List.Forall₂.cons ?_ (filter_rel invs alpha logH hgr)
  -- The running sums and count of the height before this matrix.
  obtain ⟨c, g, h1, h2, hg⟩ : ∃ c g, (groups.lookup logH).getD (0, #[]) = (c, g) ∧
      (red.lookup logH).getD (0, Array.replicate s.height 0) =
        (c, Array.ofFn (n := s.height) fun r ↦ gval alpha logH g r.val) ∧
      ∀ it ∈ g, Good invs alpha logH it := by
    rcases lookup_rel invs alpha logH hgr with ⟨h1, h2⟩ | ⟨c, g, h1, h2, hg⟩
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
  rw [foldl_accumulate alpha (powers alpha s.width) s.width s.height _ _ hxs pts
    (fun pr hp ↦ (hz pr hp).1) c]
  refine ⟨rfl, rfl, ?_, show 16 * 2 ^ logH < USize.size by rw [← hpow]; exact hus,
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
theorem foldl_groupStep_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) :
    ∀ {items : List (PMat × List (EF × Array EF))}
      {sitems : List (Mat F × List (EF × Array EF))},
      List.Forall₂ (fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) items sitems →
      (∀ x ∈ sitems, MatOk x.1 ∧
        ∀ pr ∈ x.2, Ext.OutsideBase pr.1 ∧ DenomsOk invs pr.1 (Nat.log2 x.1.height)) →
      ∀ {groups : List (Nat × Nat × Array (GItem p EF))} {red : List (Nat × Nat × Array EF)},
      List.Forall₂ (GR invs alpha) groups red →
      List.Forall₂ (GR invs alpha) (items.foldl (groupStep alpha) groups)
        (sitems.foldl (reduceStep alpha) red)
  | _, _, .nil, _, _, _, hgr => hgr
  | (m, pts) :: _, (s, _) :: _, .cons ⟨hm, hp⟩ hrest, hgood, _, _, hgr => by
    simp only at hp
    subst hp
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨hs, hz⟩ := hgood (s, pts) List.mem_cons_self
    exact foldl_groupStep_rel alpha hrest (fun it hit ↦ hgood it (List.mem_cons_of_mem _ hit))
      (groupStep_rel invs alpha hgr hm pts hs hz)

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

/-- Four planes of a range of rows within one block of a packed matrix, batched by the scalars
`W c J` of plane `c` and column `J`, zero past the last column, given as words `a c J`. -/
theorem compress4_cols {pm : PMat} {s : Mat F} (h : RM pm s) (W : Nat → Nat → F)
    (hW : ∀ c J, s.width ≤ J → W c J = 0) (a : Nat → Nat → UInt32)
    (ha : ∀ c < 4, ∀ J, a c J = (W c J).val) (r0 len : Nat) (hlen : 0 < len)
    (hblk : r0 % pm.rows + len ≤ pm.rows) (hr : r0 + len ≤ s.height)
    (hl : 16 * len < USize.size) (c : Nat) (hc : c < 4) :
    (compress4 p pm a r0 len).extract (4 * (c * len)) (4 * ((c + 1) * len)) =
      encode (Array.ofFn (n := len) fun t ↦ ∑ J ∈ Finset.range s.width,
        s.values.getD ((r0 + t.val) * s.width + J) 0 * W c J) := by
  unfold compress4
  rw [CompStark.Merkle.Packed.foldRange_eq, h.width]
  -- The rows batched by the first `J` columns.
  let x (J t : Nat) : F := s.values.getD ((r0 + t) * s.width + J) 0
  let part (c J t : Nat) : F := ∑ i ∈ Finset.range J, x i t * W c i
  have hpart (c J t : Nat) : part c (J + 1) t = part c J t + x J t * W c J := by
    simp only [part, Finset.sum_range_succ]
  -- The four planes of the rows batched by the first `J` columns, in one array.
  let pl (J j : Nat) : F := if j < len then part 0 J j else if j < 2 * len then part 1 J (j - len)
    else if j < 3 * len then part 2 J (j - 2 * len) else part 3 J (j - 3 * len)
  let Q (J : Nat) : Array F := Array.ofFn (n := 4 * len) fun j ↦ pl J j.val
  have hQ (J c r : Nat) (hc : c < 4) (hr : r < len) : (Q J).getD (c * len + r) 0 = part c J r := by
    rw [getD_ofFn_bounded _ _ (by interval_cases c <;> omega)]
    interval_cases c <;> simp only [pl] <;>
      simp (disch := omega) only [Words.ite_of_pos, Words.ite_of_neg] <;> congr 1 <;> omega
  have hpl (J c r : Nat) (hc : c < 4) (hr : r < len) : pl J (c * len + r) = part c J r := by
    have := hQ J c r hc hr
    rwa [getD_ofFn_bounded _ _ (by interval_cases c <;> omega)] at this
  have hw0 (G : Nat) (hG : G < (s.width + 3) / 4) : 0 < s.width := by omega
  -- A column's word times a zero scalar when the column is past the last.
  have hterm (J c t : Nat) (A : Array F) (o : Nat)
      (hA : s.width ≤ J ∨ A.getD (o + t) 0 = x J t) :
      A.getD (o + t) 0 * W c J = x J t * W c J := by
    rcases hA with hA | hA
    · rw [hW c J hA, mul_zero, mul_zero]
    · rw [hA]
  have hcol (J : Nat) (hJ : 0 < s.width) : ∃ A, (pm.colAt (min J (s.width - 1)) r0).1 =
      encode A ∧ (pm.colAt (min J (s.width - 1)) r0).2 + len ≤ A.size ∧
      4 * A.size < USize.size ∧ ∀ t < len, s.width ≤ J ∨
        A.getD ((pm.colAt (min J (s.width - 1)) r0).2 + t) 0 = x J t := by
    obtain ⟨A, e1, e2, e3, e4⟩ := colAt_spec h r0 len (min J (s.width - 1)) hblk hr hlen
      (by omega)
    refine ⟨A, e1, e2, e3, fun t ht ↦ ?_⟩
    by_cases hJw : J < s.width
    · right
      rw [e4 t ht, show min J (s.width - 1) = J by omega]
    · left; omega
  have hstep (G : Nat) (hG : G < (s.width + 3) / 4) :
      Words.mulAdd4x4Into p (encode (Q (4 * G))) (pm.colAt (min (4 * G) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G + 1) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G + 2) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G + 3) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G) (s.width - 1)) r0).2
        (pm.colAt (min (4 * G + 1) (s.width - 1)) r0).2
        (pm.colAt (min (4 * G + 2) (s.width - 1)) r0).2
        (pm.colAt (min (4 * G + 3) (s.width - 1)) r0).2
        (a 0 (4 * G)) (a 0 (4 * G + 1)) (a 0 (4 * G + 2)) (a 0 (4 * G + 3))
        (a 1 (4 * G)) (a 1 (4 * G + 1)) (a 1 (4 * G + 2)) (a 1 (4 * G + 3))
        (a 2 (4 * G)) (a 2 (4 * G + 1)) (a 2 (4 * G + 2)) (a 2 (4 * G + 3))
        (a 3 (4 * G)) (a 3 (4 * G + 1)) (a 3 (4 * G + 2)) (a 3 (4 * G + 3)) len =
      encode (Q (4 * G + 4)) := by
    have hw := hw0 G hG
    obtain ⟨A0, e10, e20, e30, e40⟩ := hcol (4 * G) hw
    obtain ⟨A1, e11, e21, e31, e41⟩ := hcol (4 * G + 1) hw
    obtain ⟨A2, e12, e22, e32, e42⟩ := hcol (4 * G + 2) hw
    obtain ⟨A3, e13, e23, e33, e43⟩ := hcol (4 * G + 3) hw
    rw [e10, e11, e12, e13]
    simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]
    have hf (c : Nat) (hc : c < 4) (r : Nat) (hr : r < len) : pl (4 * G + 4) (c * len + r) =
        (Q (4 * G)).getD (c * len + r) 0 +
          (A0.getD ((pm.colAt (min (4 * G) (s.width - 1)) r0).2 + r) 0 * W c (4 * G) +
          A1.getD ((pm.colAt (min (4 * G + 1) (s.width - 1)) r0).2 + r) 0 * W c (4 * G + 1) +
          A2.getD ((pm.colAt (min (4 * G + 2) (s.width - 1)) r0).2 + r) 0 * W c (4 * G + 2) +
          A3.getD ((pm.colAt (min (4 * G + 3) (s.width - 1)) r0).2 + r) 0 * W c (4 * G + 3)) := by
      rw [hpl _ c r hc hr, hQ _ c r hc hr, hterm _ c r A0 _ (e40 r hr),
        hterm _ c r A1 _ (e41 r hr), hterm _ c r A2 _ (e42 r hr),
        hterm _ c r A3 _ (e43 r hr), show 4 * G + 4 = 4 * G + 1 + 1 + 1 + 1 by omega,
        hpart, hpart, hpart, hpart]
      ring
    exact Words.mulAdd4x4Into_encode (Q (4 * G)) A0 A1 A2 A3 _ _ _ _ len _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ (pl (4 * G + 4)) Array.size_ofFn e20 e21 e22 e23 (by rw [Array.size_ofFn]; omega)
      e30 e31 e32 e33
      (fun r hr ↦ by simpa only [Nat.zero_mul, Nat.zero_add] using hf 0 (by decide) r hr)
      (fun r hr ↦ by simpa only [Nat.one_mul] using hf 1 (by decide) r hr)
      (fun r hr ↦ hf 2 (by decide) r hr) (fun r hr ↦ hf 3 (by decide) r hr)
  have key : ∀ G ≤ (s.width + 3) / 4, (List.range G).foldl (fun out g ↦
      Words.mulAdd4x4Into p out (pm.colAt (min (4 * g) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g + 1) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g + 2) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g + 3) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g) (s.width - 1)) r0).2
        (pm.colAt (min (4 * g + 1) (s.width - 1)) r0).2
        (pm.colAt (min (4 * g + 2) (s.width - 1)) r0).2
        (pm.colAt (min (4 * g + 3) (s.width - 1)) r0).2
        (a 0 (4 * g)) (a 0 (4 * g + 1)) (a 0 (4 * g + 2)) (a 0 (4 * g + 3))
        (a 1 (4 * g)) (a 1 (4 * g + 1)) (a 1 (4 * g + 2)) (a 1 (4 * g + 3))
        (a 2 (4 * g)) (a 2 (4 * g + 1)) (a 2 (4 * g + 2)) (a 2 (4 * g + 3))
        (a 3 (4 * g)) (a 3 (4 * g + 1)) (a 3 (4 * g + 2)) (a 3 (4 * g + 3)) len)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (4 * len)) = encode (Q (4 * G)) := by
    intro G hG
    induction G with
    | zero =>
      rw [List.range_zero, List.foldl_nil, CompStark.Merkle.Packed.zeroWords_fields (p := p)]
      refine congrArg encode (Array.ext (by rw [Array.size_replicate, Array.size_ofFn])
        fun j h1 _ ↦ ?_)
      rw [Array.getElem_replicate, Array.getElem_ofFn]
      simp only [pl, part, Nat.mul_zero, Finset.range_zero, Finset.sum_empty]
      split_ifs <;> rfl
    | succ G ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        hstep G (by omega), show 4 * (G + 1) = 4 * G + 4 by omega]
  rw [key _ le_rfl]
  -- Columns past the last add nothing.
  have hfull (c t : Nat) : ∀ J, part c (s.width + J) t = part c s.width t := by
    intro J
    induction J with
    | zero => rfl
    | succ J ih =>
      rw [← Nat.add_assoc, hpart, ih, hW c _ (by omega), mul_zero, add_zero]
  rw [show 4 * ((c + 1) * len) = 4 * (c * len + len) by ring, extract_encode]
  have hsz : ((Q (4 * ((s.width + 3) / 4))).extract (c * len) (c * len + len)).size =
      (Array.ofFn (n := len) fun t ↦ ∑ J ∈ Finset.range s.width,
        s.values.getD ((r0 + t.val) * s.width + J) 0 * W c J).size := by
    rw [Array.size_extract, Array.size_ofFn, Array.size_ofFn]
    interval_cases c <;> omega
  refine congrArg encode (Array.ext hsz fun t h1 h2 ↦ ?_)
  rw [Array.size_ofFn] at h2
  rw [Array.getElem_eq_getD 0, extract_getD _ _ _ _ h2, hQ _ c t hc h2, Array.getElem_ofFn,
    show 4 * ((s.width + 3) / 4) = s.width + (4 * ((s.width + 3) / 4) - s.width) by omega,
    hfull]

/-- The fast batching of a range of rows within one block of a packed matrix into one plane. -/
theorem compress1_cols {pm : PMat} {s : Mat F} (h : RM pm s) (W : Nat → F)
    (hW : ∀ J, s.width ≤ J → W J = 0) (a : Nat → UInt32) (ha : ∀ J, a J = (W J).val)
    (r0 len : Nat) (hlen : 0 < len) (hblk : r0 % pm.rows + len ≤ pm.rows)
    (hr : r0 + len ≤ s.height) :
    compress1 p pm a r0 len = encode (Array.ofFn (n := len) fun t ↦ ∑ J ∈ Finset.range s.width,
        s.values.getD ((r0 + t.val) * s.width + J) 0 * W J) := by
  unfold compress1
  rw [CompStark.Merkle.Packed.foldRange_eq, h.width]
  -- The rows batched by the first `J` columns.
  let x (J t : Nat) : F := s.values.getD ((r0 + t) * s.width + J) 0
  let part (J t : Nat) : F := ∑ i ∈ Finset.range J, x i t * W i
  have hpart (J t : Nat) : part (J + 1) t = part J t + x J t * W J := by
    simp only [part, Finset.sum_range_succ]
  let Q (J : Nat) : Array F := Array.ofFn (n := len) fun t ↦ part J t.val
  have hQ (J t : Nat) (ht : t < len) : (Q J).getD t 0 = part J t :=
    getD_ofFn_bounded _ _ ht _
  have hw0 (G : Nat) (hG : G < (s.width + 3) / 4) : 0 < s.width := by omega
  -- A column's word times a zero scalar when the column is past the last.
  have hterm (J t : Nat) (A : Array F) (o : Nat)
      (hA : s.width ≤ J ∨ A.getD (o + t) 0 = x J t) :
      A.getD (o + t) 0 * W J = x J t * W J := by
    rcases hA with hA | hA
    · rw [hW J hA, mul_zero, mul_zero]
    · rw [hA]
  have hcol (J : Nat) (hJ : 0 < s.width) : ∃ A, (pm.colAt (min J (s.width - 1)) r0).1 =
      encode A ∧ (pm.colAt (min J (s.width - 1)) r0).2 + len ≤ A.size ∧
      4 * A.size < USize.size ∧ ∀ t < len, s.width ≤ J ∨
        A.getD ((pm.colAt (min J (s.width - 1)) r0).2 + t) 0 = x J t := by
    obtain ⟨A, e1, e2, e3, e4⟩ := colAt_spec h r0 len (min J (s.width - 1)) hblk hr hlen
      (by omega)
    refine ⟨A, e1, e2, e3, fun t ht ↦ ?_⟩
    by_cases hJw : J < s.width
    · right
      rw [e4 t ht, show min J (s.width - 1) = J by omega]
    · left; omega
  have hstep (G : Nat) (hG : G < (s.width + 3) / 4) :
      Words.mulAdd4Into p (encode (Q (4 * G))) (pm.colAt (min (4 * G) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G + 1) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G + 2) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G + 3) (s.width - 1)) r0).1
        (pm.colAt (min (4 * G) (s.width - 1)) r0).2
        (pm.colAt (min (4 * G + 1) (s.width - 1)) r0).2
        (pm.colAt (min (4 * G + 2) (s.width - 1)) r0).2
        (pm.colAt (min (4 * G + 3) (s.width - 1)) r0).2
        (a (4 * G)) (a (4 * G + 1)) (a (4 * G + 2)) (a (4 * G + 3)) len =
      encode (Q (4 * G + 4)) := by
    have hw := hw0 G hG
    obtain ⟨A0, e10, e20, e30, e40⟩ := hcol (4 * G) hw
    obtain ⟨A1, e11, e21, e31, e41⟩ := hcol (4 * G + 1) hw
    obtain ⟨A2, e12, e22, e32, e42⟩ := hcol (4 * G + 2) hw
    obtain ⟨A3, e13, e23, e33, e43⟩ := hcol (4 * G + 3) hw
    have hQs : (Q (4 * G)).size = len := Array.size_ofFn
    rw [e10, e11, e12, e13, ha, ha, ha, ha, ← hQs,
      Words.mulAdd4Into_encode (Q (4 * G)) A0 A1 A2 A3 _ _ _ _ _ _ _ _ (by rw [hQs]; exact e20)
        (by rw [hQs]; exact e21) (by rw [hQs]; exact e22) (by rw [hQs]; exact e23)
        (by rw [hQs]; omega) e30 e31 e32 e33]
    refine congrArg encode (Array.ext (by simp only [Q, Array.size_ofFn]) fun t ht _ ↦ ?_)
    rw [Array.size_ofFn, hQs] at ht
    simp only [Q, Array.getElem_ofFn]
    rw [getD_ofFn_bounded _ _ ht, hterm _ _ A0 _ (e40 _ ht), hterm _ _ A1 _ (e41 _ ht),
      hterm _ _ A2 _ (e42 _ ht),
      hterm _ _ A3 _ (e43 _ ht), show 4 * G + 4 = 4 * G + 1 + 1 + 1 + 1 by omega, hpart, hpart,
      hpart, hpart]
    ring
  have key : ∀ G ≤ (s.width + 3) / 4, (List.range G).foldl (fun out g ↦
      Words.mulAdd4Into p out (pm.colAt (min (4 * g) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g + 1) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g + 2) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g + 3) (s.width - 1)) r0).1
        (pm.colAt (min (4 * g) (s.width - 1)) r0).2
        (pm.colAt (min (4 * g + 1) (s.width - 1)) r0).2
        (pm.colAt (min (4 * g + 2) (s.width - 1)) r0).2
        (pm.colAt (min (4 * g + 3) (s.width - 1)) r0).2
        (a (4 * g)) (a (4 * g + 1)) (a (4 * g + 2)) (a (4 * g + 3)) len)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len) = encode (Q (4 * G)) := by
    intro G hG
    induction G with
    | zero =>
      rw [List.range_zero, List.foldl_nil, CompStark.Merkle.Packed.zeroWords_fields (p := p)]
      refine congrArg encode (Array.ext (by rw [Array.size_replicate, Array.size_ofFn])
        fun j h1 _ ↦ ?_)
      rw [Array.getElem_replicate, Array.getElem_ofFn]
      simp only [part, Nat.mul_zero, Finset.range_zero, Finset.sum_empty]
    | succ G ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        hstep G (by omega), show 4 * (G + 1) = 4 * G + 4 by omega]
  rw [key _ le_rfl]
  -- Columns past the last add nothing.
  have hfull (t : Nat) : ∀ J, part (s.width + J) t = part s.width t := by
    intro J
    induction J with
    | zero => rfl
    | succ J ih =>
      rw [← Nat.add_assoc, hpart, ih, hW _ (by omega), mul_zero, add_zero]
  refine congrArg encode (congrArg Array.ofFn (funext fun t ↦ ?_))
  rw [show 4 * ((s.width + 3) / 4) = s.width + (4 * ((s.width + 3) / 4) - s.width) by omega,
    hfull]

/-- `flatMap_chunks` on the chunks spelled out. -/
theorem flatMap_chunks_aux {α : Type} (n : Nat) (f : Nat → α) (g : Nat → Nat → α)
    (hg : ∀ q c, c < 4 → 4 * q + c < n → g q c = f (4 * q + c)) : ∀ Q,
    (Array.range Q).flatMap (fun q ↦ (Array.range (min 4 (n - 4 * q))).map (g q)) =
      Array.ofFn (n := min n (4 * Q)) fun i ↦ f i.val
  | 0 => by
    rw [Array.eq_empty_of_size_eq_zero (Array.size_range (n := 0)), Array.flatMap_empty]
    exact Array.ext (by simp) fun i h1 _ ↦ absurd h1 (by simp)
  | Q + 1 => by
    rw [Array.range_succ, Array.flatMap_append, flatMap_chunks_aux n f g hg Q]
    have e : (#[Q] : Array Nat).flatMap (fun q ↦ (Array.range (min 4 (n - 4 * q))).map (g q)) =
        (Array.range (min 4 (n - 4 * Q))).map (g Q) := by
      apply Array.toList_inj.mp; simp
    rw [e]
    have hs : (Array.ofFn (n := min n (4 * Q)) fun i ↦ f i.val).size = min n (4 * Q) :=
      Array.size_ofFn
    refine Array.ext (by simp only [Array.size_append, Array.size_ofFn, Array.size_map,
      Array.size_range]; omega) fun i h1 h2 ↦ ?_
    simp only [Array.size_append, Array.size_ofFn, Array.size_map, Array.size_range] at h1
    rw [Array.getElem_append, Array.getElem_ofFn]
    split
    · rename_i h; rw [Array.getElem_ofFn]
    · rename_i h
      rw [hs] at h
      rw [Array.getElem_map, Array.getElem_range, hs, hg _ _ (by omega) (by omega)]
      dsimp only
      congr 1
      omega

/-- Chunks of four, the last one short, are all the elements. -/
theorem flatMap_chunks {α : Type} (n : Nat) (f : Nat → α) (g : Nat → Nat → α)
    (hg : ∀ q c, c < 4 → 4 * q + c < n → g q c = f (4 * q + c)) (G : Nat → Array α)
    (hG : ∀ q, G q = (Array.range (min 4 (n - 4 * q))).map (g q)) (Q : Nat) :
    (Array.range Q).flatMap G = Array.ofFn (n := min n (4 * Q)) fun i ↦ f i.val := by
  obtain rfl : G = fun q ↦ (Array.range (min 4 (n - 4 * q))).map (g q) := funext hG
  exact flatMap_chunks_aux n f g hg Q

/-- The fast batching of a range of rows within one block of a packed matrix by the powers `ap`
of `α`, coordinate by coordinate. -/
theorem compressRange_cols [Mont32BaseField p] [Mont32.AlgebraId EF] {pm : PMat} {s : Mat F}
    (h : RM pm s) (ap : Array EF) (hap : ap.size = s.width) (r0 len : Nat) (hlen : 0 < len)
    (hblk : r0 % pm.rows + len ≤ pm.rows) (hr : r0 + len ≤ s.height)
    (hsa : 4 * ap.size < USize.size) (hl : 16 * len < USize.size) :
    compressRange p pm (ExtPlanes.ofArray ap).c.toArray r0 len =
      Array.ofFn (n := FastExt.d p EF) fun c ↦ encode (Array.ofFn (n := len) fun t ↦
        coord c.val (crow s.values ap s.width (r0 + t.val))) := by
  unfold compressRange
  have hsz : (ExtPlanes.ofArray ap).c.toArray.size = FastExt.d p EF := by simp
  -- The planes' words are the coordinates of the powers.
  have hpw (P J : Nat) : planeWord pm (ExtPlanes.ofArray ap).c.toArray P J =
      (coord P (ap.getD J 0)).val := by
    unfold planeWord
    rw [hsz]
    split
    · rename_i hj
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp; exact hj.1),
        Option.getD_some, Vector.getElem_toArray]
      simp only [ExtPlanes.ofArray, Vector.getElem_ofFn,
        CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq]
      rw [h.width] at hj
      rw [Words.read_encode _ _ (by rw [Array.size_map]; exact hsa)
          (by rw [Array.size_map, hap]; exact hj.2),
        ExtPlanes.getD_map _ _ _ (by rw [hap]; exact hj.2), coord, dite_eq_left hj.1,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hap]; exact hj.2),
        Option.getD_some]
    · rename_i hj
      rw [h.width] at hj
      by_cases h1 : P < FastExt.d p EF
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
          rw [hap]; exact Nat.le_of_not_lt fun h2 ↦ hj ⟨h1, h2⟩), Option.getD_none, coord_zero]
        rfl
      · rw [coord, dite_eq_right h1]; rfl
  have hW (P J : Nat) (hJ : s.width ≤ J) : coord P (ap.getD J 0) = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
      coord_zero]
  have hcrow (P : Nat) : (Array.ofFn (n := len) fun t ↦ ∑ J ∈ Finset.range s.width,
      s.values.getD ((r0 + t.val) * s.width + J) 0 * coord P (ap.getD J 0)) =
      Array.ofFn (n := len) fun t ↦ coord P (crow s.values ap s.width (r0 + t.val)) :=
    congrArg Array.ofFn (funext fun t ↦ by rw [crow, coord_foldl_smul, coord_zero, zero_add])
  refine flatMap_chunks _ (fun c ↦ encode (Array.ofFn (n := len) fun t ↦
      coord c (crow s.values ap s.width (r0 + t.val))))
    (fun q c ↦ if min 4 ((ExtPlanes.ofArray ap).c.toArray.size - 4 * q) = 4 then
      (compress4 p pm (fun c j ↦ planeWord pm (ExtPlanes.ofArray ap).c.toArray (4 * q + c) j)
        r0 len).extract (4 * (c * len)) (4 * ((c + 1) * len))
      else compress1 p pm (planeWord pm (ExtPlanes.ofArray ap).c.toArray (4 * q + c)) r0 len)
    (fun q c hc4 hc ↦ ?_) _ (fun q ↦ by split <;> rfl) _ |>.trans ?_
  · split
    · rw [compress4_cols h (fun c J ↦ coord (4 * q + c) (ap.getD J 0)) (fun c J hJ ↦ hW _ J hJ)
        _ (fun c _ J ↦ hpw _ J) r0 len hlen hblk hr hl c hc4, hcrow]
    · rw [compress1_cols h (fun J ↦ coord (4 * q + c) (ap.getD J 0)) (fun J hJ ↦ hW _ J hJ) _
        (fun J ↦ hpw _ J) r0 len hlen hblk hr, hcrow]
  · rw [hsz]
    exact ofFn_len (fun c ↦ encode (Array.ofFn (n := len) fun t ↦
      coord c (crow s.values ap s.width (r0 + t.val)))) (by omega)

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

/-- `addToPoint` on the sums' values as functions of the row. -/
def addToPointS (z y : EF) (C : Nat → EF) :
    List (EF × EF × (Nat → EF)) → List (EF × EF × (Nat → EF))
  | [] => [(z, y, C)]
  | e :: es => if e.1 == z then (z, e.2.1 + y, fun t ↦ e.2.2 t + C t) :: es
    else e :: addToPointS z y C es

theorem mem_addToPointS (z y : EF) (C : Nat → EF) :
    ∀ (L : List (EF × EF × (Nat → EF))), ∀ l ∈ addToPointS z y C L, l.1 = z ∨ ∃ l' ∈ L, l'.1 = l.1
  | [], l, hl => by
    simp only [addToPointS, List.mem_singleton] at hl
    exact Or.inl (by rw [hl])
  | e :: es, l, hl => by
    simp only [addToPointS] at hl
    split at hl
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact Or.inl rfl
      · exact Or.inr ⟨l, List.mem_cons_of_mem _ hl, rfl⟩
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact Or.inr ⟨l, List.mem_cons_self, rfl⟩
      · rcases mem_addToPointS z y C es l hl with h | ⟨l', hl', h⟩
        · exact Or.inl h
        · exact Or.inr ⟨l', List.mem_cons_of_mem _ hl', h⟩

/-- The value at row `t` of per-point sums `(z, Y, D)`: `∑ (Y - D t) / (z - x t)`. -/
def sumsVal [Mont32BaseField p] (x : Nat → F) (L : List (EF × EF × (Nat → EF))) (t : Nat) : EF :=
  (L.map fun e ↦ (e.2.1 - e.2.2 t) * (e.1 - FastExt.ofBase (x t))⁻¹).sum

/-- Planes of per-point sums representing their values. -/
def SR (len : Nat) (sums : List (EF × EF × ExtPlanes p EF)) (L : List (EF × EF × (Nat → EF))) :
    Prop :=
  List.Forall₂ (fun e l ↦ e.1 = l.1 ∧ e.2.1 = l.2.1 ∧ ExtPlanes.Rel e.2.2 (tab len l.2.2)) sums L

theorem addToPoint_rel {len : Nat} (hl : 4 * len < USize.size) (z y : EF) {c : ExtPlanes p EF}
    {C : Nat → EF} (hc : ExtPlanes.Rel c (tab len C)) :
    ∀ {sums L}, SR len sums L → SR len (addToPoint z y c sums) (addToPointS z y C L)
  | [], [], .nil => .cons ⟨rfl, rfl, hc⟩ .nil
  | e :: es, l :: ls, .cons he hs => by
    simp only [addToPoint, addToPointS, he.1]
    split
    · exact .cons ⟨rfl, by rw [he.2.1], ExtPlanes.add_rel hl he.2.2 hc⟩ hs
    · exact .cons he (addToPoint_rel hl z y hc hs)

theorem sumsVal_addToPointS [Mont32BaseField p] (x : Nat → F) (z y : EF) (C : Nat → EF) (t : Nat) :
    ∀ L : List (EF × EF × (Nat → EF)), sumsVal x (addToPointS z y C L) t =
      sumsVal x L t + (y - C t) * (z - FastExt.ofBase (x t))⁻¹
  | [] => by
    simp only [sumsVal, addToPointS, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    refine FastExt.toSpec_injective ?_
    simp only [FastExt.toSpec_add, FastExt.toSpec_zero]
    ring
  | l :: ls => by
    simp only [addToPointS]
    split
    · rename_i h
      have h := beq_iff_eq.mp h
      subst h
      simp only [sumsVal, List.map_cons, List.sum_cons]
      refine FastExt.toSpec_injective ?_
      simp only [FastExt.toSpec_add, FastExt.toSpec_sub, FastExt.toSpec_mul, FastExt.toSpec_inv]
      ring
    · have ih := sumsVal_addToPointS x z y C t ls
      simp only [sumsVal, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      refine FastExt.toSpec_injective ?_
      simp only [FastExt.toSpec_add]
      ring

/-- The last step of `reduceRange`: every point's `(Y - D) / (z - x)` added. -/
theorem foldl_points_rel [Mont32BaseField p] (invs : List (EF × Nat × ExtPlanes p EF))
    {logH r0 len : Nat} (hl : 4 * len < USize.size) (hr : r0 + len ≤ 2 ^ logH) :
    ∀ {sums L} (A : Nat → EF) {acc : ExtPlanes p EF}, SR len sums L →
      (∀ l ∈ L, DenomsOk invs l.1 logH) → ExtPlanes.Rel acc (tab len A) →
      ExtPlanes.Rel (sums.foldl (fun acc (e : EF × EF × ExtPlanes p EF) ↦
          acc.add ((ExtPlanes.rsub e.2.1 e.2.2).mul (slicePlanes (denomsOf invs e.1) r0 len))) acc)
        (tab len fun t ↦ A t +
          sumsVal (fun t ↦ (cosetPointsBitRev (gen : F) logH).getD (r0 + t) 0) L t)
  | [], [], A, acc, .nil, _, hacc => by
    refine hacc.congr_tab fun t _ ↦ ?_
    simp only [sumsVal, List.map_nil, List.sum_nil]
    refine FastExt.toSpec_injective ?_
    simp only [FastExt.toSpec_add, FastExt.toSpec_zero]
    ring
  | (z, y, c) :: es, (z', y', D) :: ls, A, acc, .cons he hs, hd, hacc => by
    obtain ⟨h1, h2, h3⟩ := he
    dsimp only at h1 h2 h3
    subst h1 h2
    rw [List.foldl_cons]
    have hden : DenomsOk invs z logH := hd _ List.mem_cons_self
    have hstep := ExtPlanes.add_rel hl hacc (ExtPlanes.mul_rel hl (ExtPlanes.rsub_rel hl y h3)
      (hden.slice hr))
    have := foldl_points_rel invs hl hr _ hs (fun l hl' ↦ hd l (List.mem_cons_of_mem _ hl'))
      hstep
    refine this.congr_tab fun t _ ↦ ?_
    simp only [sumsVal, List.map_cons, List.sum_cons]
    refine FastExt.toSpec_injective ?_
    simp only [FastExt.toSpec_add]
    ring

/-- The rows of a range of a group's matrix batched by the powers of `α`, as planes. -/
theorem comp_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (logH : Nat)
    (it : GItem p EF) (hit : Good invs alpha logH it) (r0 len : Nat) (hlen : 0 < len)
    (hblk : r0 % it.1.rows + len ≤ it.1.rows) (hr : r0 + len ≤ 2 ^ logH) :
    ExtPlanes.Rel ⟨len, Vector.ofFn fun k ↦
        (compressRange p it.1 it.2.1.c.toArray r0 len).getD k .empty⟩
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
  rw [hc, vals_rel hm, hm.width]
  show ExtPlanes.Rel _ (tab len fun t ↦ crow s.values ap s.width (r0 + t))
  refine ExtPlanes.rel_mk _ _ fun k ↦ ?_
  rw [ExtPlanes.getElem_ofFn_fin, getD_ofFn_bounded _ _ k.isLt]
  refine congrArg encode (congrArg Array.ofFn (funext fun t ↦ ?_))
  exact coord_fin _ k

theorem lookup_mem {k : EF} {v : ExtPlanes p EF} :
    ∀ {l : List (EF × ExtPlanes p EF)}, l.lookup k = some v → (k, v) ∈ l
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
theorem reduceRange_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF)
    (logH : Nat) (g : Array (GItem p EF))
    (hg : ∀ it ∈ g, Good invs alpha logH it) (h4 : 4 * 2 ^ logH < USize.size) (r0 len : Nat)
    (hlen : 0 < len) (hblk : ∀ it ∈ g, r0 % it.1.rows + len ≤ it.1.rows)
    (hr : r0 + len ≤ 2 ^ logH) :
    ExtPlanes.Rel (reduceRange invs g r0 len)
      (Array.ofFn (n := len) fun t ↦ gval alpha logH g (r0 + t.val)) := by
  have hl : 4 * len < USize.size := by omega
  let x (t : Nat) : F := (cosetPointsBitRev (gen : F) logH).getD (r0 + t) 0
  -- One term at row `r` of the range, for the matrix `it`.
  let σ' (it : GItem p EF) (S : Nat → EF) (tm : EF × EF × EF) : Nat → EF := fun r ↦
    termStep (crow (it.1.vals p) (powers alpha it.1.width) it.1.width (r0 + r)) (x r) (S r) tm
  let σ (it : GItem p EF) (S : Nat → EF) : Nat → EF := it.2.2.foldl (σ' it) S
  let Inv (sums : List (EF × EF × ExtPlanes p EF)) (S : Nat → EF) : Prop :=
    ∃ L, SR len sums L ∧ (∀ l ∈ L, DenomsOk invs l.1 logH) ∧ ∀ t < len, sumsVal x L t = S t
  suffices H : ∀ f, (∀ a ∈ g.toList, ∀ b c, Inv b c →
      ∃ b', f a b = pure (.yield b') ∧ Inv b' (σ a c)) →
      ExtPlanes.Rel ((forIn g.toList [] f) >>= fun sums ↦ pure (sums.foldl
          (fun acc (e : EF × EF × ExtPlanes p EF) ↦ acc.add ((ExtPlanes.rsub e.2.1 e.2.2).mul
            (slicePlanes (denomsOf invs e.1) r0 len))) (ExtPlanes.zeros len)) : Id (ExtPlanes p EF))
        (Array.ofFn (n := len) fun t ↦ gval alpha logH g (r0 + t.val)) by
    simp only [reduceRange, Id.run]
    rw [← Array.forIn_toList]
    refine H _ fun it hit b c hb ↦ ⟨_, rfl, ?_⟩
    obtain ⟨-, -, -, -, -, -, hz⟩ := hg it (Array.mem_toList_iff.mp hit)
    have hcomp := comp_rel invs alpha logH it (hg it (Array.mem_toList_iff.mp hit)) r0 len hlen
      (hblk it (Array.mem_toList_iff.mp hit)) hr
    exact forIn_sim Inv (fun tm S ↦ σ' it S tm) _ it.2.2 b c hb fun tm htm b c hb ↦ by
      obtain ⟨L, hL, hd, hv⟩ := hb
      refine ⟨_, rfl, _, addToPoint_rel hl tm.1 (tm.2.2 * tm.2.1)
        (ExtPlanes.smul_rel hl tm.2.2 (show ExtPlanes.Rel _ (tab len fun t ↦
          crow (it.1.vals p) (powers alpha it.1.width) it.1.width (r0 + t)) from hcomp)) hL, fun l hl' ↦ ?_, fun t ht ↦ ?_⟩
      · rcases mem_addToPointS _ _ _ L l hl' with h | ⟨l', hl'', h⟩
        · rw [h]; exact (hz tm htm).2
        · rw [← h]; exact hd l' hl''
      · rw [sumsVal_addToPointS, hv t ht]
        simp only [σ', termStep, Ext.ofBase, Mont32.ofBase_eq]
        refine FastExt.toSpec_injective ?_
        simp only [FastExt.toSpec_add, FastExt.toSpec_sub, FastExt.toSpec_mul]
        ring
  intro f hf
  have := forIn_sim Inv σ f g.toList [] (fun _ ↦ 0) ⟨[], .nil, fun l hl' ↦ absurd hl' List.not_mem_nil,
    fun t _ ↦ rfl⟩ hf
  obtain ⟨L, hL, hd, hv⟩ := this
  have hfin := foldl_points_rel invs hl hr (fun _ ↦ 0) hL hd (by
    have := ExtPlanes.zeros_rel (p := p) (E := EF) len
    convert this using 1
    exact Array.ext (by rw [size_tab, Array.size_replicate]) fun i _ _ ↦ by
      rw [getElem_tab, Array.getElem_replicate])
  show ExtPlanes.Rel _ (tab len fun t ↦ gval alpha logH g (r0 + t))
  refine hfin.congr_tab fun t ht ↦ ?_
  have key : ∀ (l : List (GItem p EF)) (S : Nat → EF), (l.foldl (fun c a ↦ σ a c) S) t =
      l.foldl (fun a it ↦ it.2.2.foldl (termStep
        (crow (it.1.vals p) (powers alpha it.1.width) it.1.width (r0 + t))
        ((cosetPointsBitRev (gen : F) logH).getD (r0 + t) 0)) a) (S t) := by
    intro l
    induction l with
    | nil => intro S; rfl
    | cons a l ih =>
      intro S
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      exact foldl_pointwise (fun r acc tm ↦ termStep (crow (a.1.vals p)
        (powers alpha a.1.width) a.1.width (r0 + r)) (x r) acc tm) a.2.2 S t
  rw [hv t ht, key]
  refine FastExt.toSpec_injective ?_
  simp only [FastExt.toSpec_add, FastExt.toSpec_zero, zero_add]
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
theorem groupPlanes_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF)
    (G : Nat × Nat × Array (GItem p EF))
    (h4 : 4 * 2 ^ G.1 < USize.size)
    (hg : ∀ it ∈ G.2.2, Good invs alpha G.1 it) :
    ExtPlanes.Rel (groupPlanes invs G).2 (Array.ofFn (n := 2 ^ G.1) fun r ↦ gval alpha G.1 G.2.2
        r.val) := by
  obtain ⟨logH, c, g⟩ := G
  simp only at h4 hg ⊢
  unfold groupPlanes
  dsimp only
  have hfold : g.foldl (fun a (x : GItem p EF) ↦ match x with | (m, _) => Nat.gcd a m.rows)
      (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) =
      g.toList.foldl (fun a (x : GItem p EF) ↦ Nat.gcd a x.1.rows)
        (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) := by
    rw [← Array.foldl_toList]
  rw [hfold]
  have hDd : g.toList.foldl (fun a (x : GItem p EF) ↦ Nat.gcd a x.1.rows)
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
  have hD0 : 0 < g.toList.foldl (fun a (x : GItem p EF) ↦ Nat.gcd a x.1.rows)
      (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) :=
    gcd_fold_pos (fun x : GItem p EF ↦ x.1.rows) g.toList _ hA0
  have hDr : ∀ it ∈ g, g.toList.foldl (fun a (x : GItem p EF) ↦ Nat.gcd a x.1.rows)
      (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) ∣ it.1.rows :=
    fun it hit ↦ gcd_fold_dvd (fun x : GItem p EF ↦ x.1.rows) _ _ it (Array.mem_toList_iff.mpr hit)
  generalize g.toList.foldl (fun a (x : GItem p EF) ↦ Nat.gcd a x.1.rows)
    (if 2 ^ logH < 4096 then 2 ^ logH else 2 ^ logH / 16) = D at hDd hD0 hDr ⊢
  obtain ⟨hp, hpD, hranges⟩ := uniform_ranges hD0 hDd (Nat.two_pow_pos logH)
  generalize 2 ^ logH / D = parts at hp hpD hranges ⊢
  rw [← foldl_ranges (fun r ↦ gval alpha logH g r) (2 ^ logH) parts (2 ^ logH / parts) hp
    (ranges_cover _ _)]
  refine ExtPlanes.join_rel _ parts _ _ (fun k hk ↦ ?_) (by
    rw [foldl_ranges (fun r ↦ gval alpha logH g r) (2 ^ logH) parts (2 ^ logH / parts) hp
      (ranges_cover _ _), Array.size_ofFn])
  obtain ⟨hlen, hcov⟩ := hranges k hk
  rw [hlen, hpD]
  exact reduceRange_rel invs alpha logH g hg h4 (k * D) D hD0
    (fun it hit ↦ mod_add_le_of_dvd (by obtain ⟨s, hm, -⟩ := hg it hit; exact hm.pos)
      (hDr it hit) (Nat.dvd_mul_left D k))
    hcov

/-- The fast reduction is the specification's. -/
theorem reduce_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF)
    {items : List (PMat × List (EF × Array EF))}
    {sitems : List (Mat F × List (EF × Array EF))}
    (h : List.Forall₂ (fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) items sitems)
    (hok : ∀ x ∈ sitems, MatOk x.1 ∧
      ∀ pr ∈ x.2, Ext.OutsideBase pr.1 ∧ DenomsOk invs pr.1 (Nat.log2 x.1.height)) :
    List.Forall₂ (fun x y ↦ x.1 = y.1 ∧ ExtPlanes.Rel x.2 y.2) (reduce invs alpha items)
      (Fri.reduce alpha sitems) := by
  rw [reduce_fast invs alpha items, reduce_eq, List.map_mergeSort
    (r := fun (a b : Nat × Nat × Array EF) ↦ decide (b.1 ≤ a.1))
    (s := fun (a b : Nat × Array EF) ↦ decide (b.1 ≤ a.1)) (f := fun x ↦ (x.1, x.2.2))
    (fun _ _ _ _ ↦ rfl)]
  refine forall₂_mergeSort (fun (a : Nat × ExtPlanes p EF) ↦ a.1) (fun (b : Nat × Array EF) ↦ b.1)
      ?_
    (fun _ _ hab ↦ hab.1)
  have hgr := foldl_groupStep_rel invs alpha h hok List.Forall₂.nil
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine hgr.imp fun G S hGS ↦ ⟨hGS.1, ?_⟩
  obtain ⟨-, -, h3, h4, h5⟩ := hGS
  rw [h3]
  exact groupPlanes_rel invs alpha G (by omega) h5

end

/-! ### `1 / (z - x)` once per point, for the opened values and the reduction -/

theorem slice_encode_tab (X : Array F) (r0 len : Nat) (h : r0 + len ≤ X.size) :
    slice (encode X) r0 len = encode (tab len fun t ↦ X.getD (r0 + t) 0) := by
  rw [slice_encode]
  refine congrArg encode (Array.ext (by rw [Array.size_extract, size_tab]; omega) fun t h1 _ ↦ ?_)
  rw [Array.size_extract] at h1
  rw [Array.getElem_extract, getElem_tab]
  exact (getD_lt X _ (by omega)).symm

/-- `denomPlanes` holds `1 / (z - x)` on the stored points of its height. -/
theorem denomPlanes_rel [Mont32BaseField p] [Mont32.AlgebraId EF] {z : EF} (hz : Ext.OutsideBase z) (L : Nat)
    (hL : 4 * 2 ^ L < USize.size) :
    ExtPlanes.Rel (denomPlanes z L) (tab (2 ^ L) fun r ↦
      (z - FastExt.ofBase ((cosetPointsBitRev (gen : F) L).getD r 0))⁻¹) := by
  unfold denomPlanes
  dsimp only
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq]
  generalize hP : (if 2 ^ L < 4096 then 1 else 16) = parts
  have hp : 0 < parts := by rw [← hP]; split <;> decide
  have hX := size_cosetPointsBitRev (gen : F) L
  let f (r : Nat) : EF := (z - FastExt.ofBase ((cosetPointsBitRev (gen : F) L).getD r 0))⁻¹
  show ExtPlanes.Rel _ (Array.ofFn (n := 2 ^ L) fun r ↦ f r.val)
  have hcov := ranges_cover (2 ^ L) parts
  rw [← foldl_ranges f (2 ^ L) parts (2 ^ L / parts) hp hcov]
  refine ExtPlanes.join_rel _ parts _ _ (fun k hk ↦ ?_)
    (by rw [foldl_ranges f (2 ^ L) parts (2 ^ L / parts) hp hcov, Array.size_ofFn])
  have hle : k * (2 ^ L / parts) + (if k + 1 = parts then 2 ^ L - k * (2 ^ L / parts)
      else 2 ^ L / parts) ≤ 2 ^ L := by
    split
    · rename_i e
      have : k * (2 ^ L / parts) ≤ 2 ^ L := by rw [show k = parts - 1 by omega]; exact hcov
      omega
    · have := Nat.mul_le_mul_right (2 ^ L / parts) (show k + 1 ≤ parts - 1 by omega)
      rw [Nat.succ_mul] at this
      omega
  generalize (if k + 1 = parts then 2 ^ L - k * (2 ^ L / parts) else 2 ^ L / parts) = len
    at hle ⊢
  rw [slice_encode_tab _ _ _ (by rw [hX]; exact hle)]
  exact ExtPlanes.invDenoms_rel (by omega) (Mont32.ne_ofBase hz) _

theorem tallest_ge (items : List (PMat × List EF)) {m : PMat} {zs : List EF} {z : EF}
    (hm : (m, zs) ∈ items) (hz : z ∈ zs) : Nat.log2 m.height ≤ tallest items z := by
  unfold tallest
  have key : ∀ (l : List (PMat × List EF)) (a : Nat), a ≤ l.foldl (fun a (x : PMat × List EF) ↦
      if x.2.contains z then max a (Nat.log2 x.1.height) else a) a := by
    intro l
    induction l with
    | nil => intro a; exact le_rfl
    | cons x l ih =>
      intro a
      rw [List.foldl_cons]
      refine le_trans ?_ (ih _)
      split
      · exact le_max_left _ _
      · exact le_rfl
  have go : ∀ (l : List (PMat × List EF)) (a : Nat), (m, zs) ∈ l →
      Nat.log2 m.height ≤ l.foldl (fun a (x : PMat × List EF) ↦
        if x.2.contains z then max a (Nat.log2 x.1.height) else a) a := by
    intro l
    induction l with
    | nil => intro a h; exact absurd h List.not_mem_nil
    | cons x l ih =>
      intro a h
      rw [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h
      · refine le_trans ?_ (key _ _)
        rw [ite_eq_left_of_eq_true _ _ (eq_true (List.contains_iff_mem.mpr hz))]
        exact le_max_right _ _
      · exact ih _ h
  exact go items 0 hm

theorem tallest_cases (items : List (PMat × List EF)) (z : EF) :
    tallest items z = 0 ∨ ∃ x ∈ items, tallest items z = Nat.log2 x.1.height := by
  unfold tallest
  have go : ∀ (l : List (PMat × List EF)) (a : Nat), (a = 0 ∨ ∃ x ∈ items, a = Nat.log2 x.1.height) →
      (∀ x ∈ l, x ∈ items) →
      (l.foldl (fun a (x : PMat × List EF) ↦
        if x.2.contains z then max a (Nat.log2 x.1.height) else a) a = 0 ∨
      ∃ x ∈ items, l.foldl (fun a (x : PMat × List EF) ↦
        if x.2.contains z then max a (Nat.log2 x.1.height) else a) a = Nat.log2 x.1.height) := by
    intro l
    induction l with
    | nil => intro a h _; exact h
    | cons y l ih =>
      intro a h hl
      rw [List.foldl_cons]
      refine ih _ ?_ fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)
      split
      · rcases Nat.le_total a (Nat.log2 y.1.height) with hle | hle
        · exact Or.inr ⟨y, hl y List.mem_cons_self, max_eq_right hle⟩
        · rw [max_eq_left hle]; exact h
      · exact h
  exact go items 0 (Or.inl rfl) fun _ h ↦ h

theorem lookup_map_self {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) {z : α} :
    ∀ {l : List α}, z ∈ l → (l.map fun y ↦ (y, f y)).lookup z = some (f z)
  | y :: l, h => by
    rw [List.map_cons, List.lookup]
    by_cases e : z = y
    · subst e; rw [beq_self_eq_true]
    · rw [beq_false_of_ne e]
      exact lookup_map_self f ((List.mem_cons.mp h).resolve_left e)

/-- The planes of every point of the matrices hold `1 / (z - x)` on the tallest height it is
opened at. -/
theorem denoms_ok [Mont32BaseField p] [Mont32.AlgebraId EF] {items : List (PMat × List EF)}
    (hok : ∀ x ∈ items, 16 * x.1.height < USize.size ∧
      (∃ k ≤ twoAdicity F, x.1.height = 2 ^ k) ∧ ∀ z ∈ x.2, Ext.OutsideBase z)
    {m : PMat} {zs : List EF} (hm : (m, zs) ∈ items) {z : EF} (hz : z ∈ zs) :
    DenomsOk (denoms items) z (Nat.log2 m.height) := by
  have hmem : z ∈ (items.flatMap (·.2)).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(m, zs), hm, hz⟩)
  have hd : denomsOf (denoms items) z = denomPlanes z (tallest items z) := by
    unfold denomsOf denoms
    rw [List.map_congr_left (g := fun y ↦ (y, (tallest items y, denomPlanes y (tallest items y))))
      (fun _ _ ↦ rfl), lookup_map_self (fun y ↦ (tallest items y, denomPlanes y (tallest items y)))
      hmem]
    rfl
  have hbound : tallest items z ≤ twoAdicity F ∧ 4 * 2 ^ tallest items z < USize.size := by
    rcases tallest_cases items z with h | ⟨x, hx, h⟩
    · obtain ⟨h1, ⟨k, -, hk'⟩, -⟩ := hok _ hm
      have : 1 ≤ m.height := by rw [hk']; exact Nat.one_le_two_pow
      rw [h]; exact ⟨Nat.zero_le _, by simp only at h1; omega⟩
    · obtain ⟨h1, ⟨k, hk, hk'⟩, -⟩ := hok x hx
      rw [h, hk', Nat.log2_two_pow]
      exact ⟨hk, by rw [hk'] at h1; omega⟩
  refine ⟨tallest items z, tallest_ge items hm hz, hbound.1, ?_⟩
  rw [hd]
  exact denomPlanes_rel ((hok _ hm).2.2 z hz) _ hbound.2

theorem forall₂_mem_both {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ (fun a b ↦ R a b ∧ a ∈ l₁ ∧ b ∈ l₂) l₁ l₂
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs =>
    .cons ⟨h, List.mem_cons_self, List.mem_cons_self⟩ ((forall₂_mem_both hs).imp
      fun _ _ ⟨h, ha, hb⟩ ↦ ⟨h, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩)

theorem forall₂_map_eq' {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) : ∀ {xs ys}, List.Forall₂ R xs ys → xs.map f = ys.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    rw [List.map_cons, List.map_cons, hfg _ _ h, forall₂_map_eq' hfg hs]

theorem forall₂_mem_left' {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

omit [FastExt p EF] in
/-- The items of related rounds with the same values are related, each point one of its
matrix's. -/
theorem openItems_rel {rs : List (List (PMat × List EF))} {srs : List (List (Mat F × List EF))}
    (hr : List.Forall₂ (List.Forall₂ fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) rs srs)
    (ov : List (List (List (Array EF)))) :
    List.Forall₂ (fun x y ↦ (RM x.1 y.1 ∧ x.2 = y.2) ∧
        ∃ zs, (x.1, zs) ∈ rs.flatten ∧ (y.1, zs) ∈ srs.flatten ∧ ∀ pr ∈ x.2, pr.1 ∈ zs)
      (Fri.openItems rs ov) (Fri.openItems srs ov) := by
  unfold Fri.openItems
  induction hr generalizing ov with
  | nil => exact .nil
  | @cons ms sms rs srs hms _ ih =>
    cases ov with
    | nil => exact .nil
    | cons os ov =>
      simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons]
      refine List.rel_append ?_ ((ih ov).imp fun x y ⟨h1, zs, h2, h3, h4⟩ ↦
        ⟨h1, zs, List.mem_append_right _ h2, List.mem_append_right _ h3, h4⟩)
      clear ih
      induction hms generalizing os with
      | nil => exact .nil
      | @cons a b as bs hab _ ih =>
        cases os with
        | nil => exact .nil
        | cons o os =>
          simp only [List.zip_cons_cons, List.map_cons]
          obtain ⟨hm, hz⟩ := hab
          refine .cons ⟨⟨hm, by rw [hz]⟩, a.2, List.mem_append_left _ List.mem_cons_self,
            by simp only [hz, Prod.mk.eta]; exact List.mem_append_left _ List.mem_cons_self,
            fun pr hp ↦ (List.of_mem_zip hp).1⟩ ((ih os).imp fun x y ⟨h1, zs, h2, h3, h4⟩ ↦
              ⟨h1, zs, ?_, ?_, h4⟩)
          · rcases List.mem_append.mp h2 with h | h
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
            · exact List.mem_append_right _ h
          · rcases List.mem_append.mp h3 with h | h
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
            · exact List.mem_append_right _ h

/-- The fast opened values and reduction are the specification's. -/
theorem openings_rel [Mont32BaseField p] [Mont32.AlgebraId EF] (b : Nat)
    {rs : List (List (PMat × List EF))} {srs : List (List (Mat F × List EF))}
    (hr : List.Forall₂ (List.Forall₂ fun x y ↦ RM x.1 y.1 ∧ x.2 = y.2) rs srs)
    (hok : ∀ ms ∈ srs, ∀ x ∈ ms, MatOk x.1 ∧ ∀ z ∈ x.2, Ext.OutsideBase z) :
    (openings b rs).1 = (Fri.openings b srs).1 ∧
      ∀ alpha, List.Forall₂ (fun x y ↦ x.1 = y.1 ∧ ExtPlanes.Rel x.2 y.2)
        ((openings b rs).2 alpha) ((Fri.openings b srs).2 alpha) := by
  have hflat := List.rel_flatten hr
  -- Every fast matrix with its points is related to a specification matrix of the prover's
  -- shapes.
  have hrel : ∀ x ∈ rs.flatten, ∃ y ∈ srs.flatten, (RM x.1 y.1 ∧ x.2 = y.2) ∧ MatOk y.1 ∧
      ∀ z ∈ y.2, Ext.OutsideBase z := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := forall₂_mem_left' hflat hx
    obtain ⟨ms, hms, hy'⟩ := List.mem_flatten.mp hy
    exact ⟨y, hy, hxy, hok ms hms y hy'⟩
  have hfast : ∀ x ∈ rs.flatten, 16 * x.1.height < USize.size ∧
      (∃ k ≤ twoAdicity F, x.1.height = 2 ^ k) ∧ ∀ z ∈ x.2, Ext.OutsideBase z := by
    intro x hx
    obtain ⟨y, -, ⟨hm, hz⟩, ⟨hw, hk, -, hA⟩, hzs⟩ := hrel x hx
    unfold Addressable at hA
    have := Nat.le_mul_of_pos_left y.1.height hw
    refine ⟨by rw [hm.height]; omega, by rw [hm.height]; exact hk, fun z h ↦ hzs z (hz ▸ h)⟩
  have hd : ∀ x ∈ rs.flatten, ∀ z ∈ x.2, DenomsOk (denoms rs.flatten) z (Nat.log2 x.1.height) :=
    fun x hx z hz ↦ denoms_ok hfast hx hz
  have hov : rs.map (·.map fun x ↦ openedAt (denoms rs.flatten) b x.1 x.2) =
      srs.map (·.map fun x ↦ x.2.map (Fri.openedAt b x.1)) := by
    refine forall₂_map_eq' (fun ms sms hms ↦ ?_) (forall₂_mem_both hr)
    obtain ⟨hms, hms1, hms2⟩ := hms
    refine forall₂_map_eq' (fun x y hxy ↦ ?_) (forall₂_mem_both hms)
    obtain ⟨⟨hm, hz⟩, hx, hy⟩ := hxy
    obtain ⟨hs, hzs⟩ := hok sms hms2 y hy
    have hx' : x ∈ rs.flatten := List.mem_flatten.mpr ⟨ms, hms1, hx⟩
    show openedAt _ b x.1 x.2 = y.2.map (Fri.openedAt b y.1)
    rw [hz]
    exact openedAt_rel _ b y.2 hm hs hzs fun z hz' ↦
      (hd x hx' z (hz ▸ hz')).mono (by rw [hm.height]; exact Nat.sub_le _ _)
  refine ⟨hov, fun alpha ↦ ?_⟩
  show List.Forall₂ _ (reduce (denoms rs.flatten) alpha (Fri.openItems rs _))
    (Fri.reduce alpha (Fri.openItems srs _))
  rw [hov]
  have hit := openItems_rel hr (srs.map (·.map fun x ↦ x.2.map (Fri.openedAt b x.1)))
  refine reduce_rel _ alpha (hit.imp fun _ _ h ↦ h.1) fun y hy ↦ ?_
  obtain ⟨x, hx, ⟨hm, hz⟩, zs, hx1, hy1, hpts⟩ := forall₂_mem_right hit hy
  obtain ⟨ms, hms, hy2⟩ := List.mem_flatten.mp hy1
  obtain ⟨hs, hzs⟩ := hok ms hms _ hy2
  refine ⟨hs, fun pr hpr ↦ ⟨hzs _ (hpts pr (hz ▸ hpr)), ?_⟩⟩
  rw [← hm.height]
  exact hd _ hx1 _ (hpts pr (hz ▸ hpr))
