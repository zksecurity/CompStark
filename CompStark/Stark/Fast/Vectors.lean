/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Columns
public import CompStark.Stark.Fast.OpeningsSpec

/-! # The fast backend's vector laws

The fast backend's vectors of extension elements read back, scale-add, fold and lay out as leaves
as the specification's.
-/

@[expose] public section
namespace CompStark.Stark
open CompPoly.Array (batchInv batchInv_eq)
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (getD_ofFn_bounded)

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The bit-reversal permutation of `2 ^ bits` indices below `2 ^ bits`. -/
theorem bitRevPerm_spec (bits : Nat) :
    (bitRevPerm bits).size = 2 ^ bits ∧ ∀ x ∈ bitRevPerm bits, x < 2 ^ bits := by
  induction bits with
  | zero =>
    refine ⟨rfl, fun x hx ↦ ?_⟩
    simp only [bitRevPerm, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    decide
  | succ b ih =>
    obtain ⟨hs, hl⟩ := ih
    refine ⟨by simp only [bitRevPerm, Array.size_append, Array.size_map, hs, Nat.pow_succ]; omega,
      fun x hx ↦ ?_⟩
    simp only [bitRevPerm, Array.mem_append, Array.mem_map] at hx
    rw [Nat.pow_succ]
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> have := hl y hy <;> omega

/-- The points of `shift · ⟨ω⟩` in order. -/
theorem cosetPoints_eq (shift : F) (L : Nat) :
    cosetPoints shift L = Array.ofFn (n := 2 ^ L) fun i ↦ shift * twoAdicGen L ^ i.val := by
  unfold cosetPoints
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have key : ∀ K, (List.range K).foldl (fun b _ ↦ (b.1.push b.2, b.2 * twoAdicGen L))
      (Array.emptyWithCapacity (2 ^ L), shift) =
      (Array.ofFn (n := K) fun i ↦ shift * twoAdicGen L ^ i.val, shift * twoAdicGen L ^ K) := by
    intro K
    induction K with
    | zero => simp only [List.range_zero, List.foldl_nil, pow_zero, mul_one]; rfl
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, Array.ofFn_succ,
        pow_succ, mul_assoc]
      rfl
  rw [key]

/-- An in-range entry. -/
theorem getD_lt {α : Type} (xs : Array α) (i : Nat) {d : α} (h : i < xs.size) :
    xs.getD i d = xs[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

/-- A loop pushing entries tabulates them. -/
theorem foldl_push_ofFn {α : Type} (f g : Nat → α) (K : Nat) (hfg : ∀ a < K, f a = g a) :
    (List.range K).foldl (fun b a ↦ b.push (f a)) #[] = Array.ofFn (n := K) fun k ↦ g k.val := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [List.range_succ, List.foldl_append, ih fun a ha ↦ hfg a (by omega), List.foldl_cons,
      List.foldl_nil, Array.ofFn_succ, hfg K (Nat.lt_succ_self _)]
    rfl

/-- The `2 x` of pair `i` of the arity-2 fold. -/
abbrev twoX (pw : Array F) (perm : Array Nat) (i : Nat) : F := 2 * pw.getD (perm.getD i 0) 0

/-- Pair `i` of the arity-2 fold. -/
abbrev foldAt (vs : Array EF) (pw : Array F) (perm : Array Nat) (beta half : EF) (i : Nat) : EF :=
  (vs.getD (2 * i) 0 + vs.getD (2 * i + 1) 0) * half +
    beta * (vs.getD (2 * i) 0 - vs.getD (2 * i + 1) 0) * Ext.ofBase (twoX pw perm i)⁻¹

/-- A range of pairs of the fold, when their `2 x` are nonzero. -/
theorem foldRange_eq (vs : Array EF) (pw : Array F) (perm : Array Nat) (beta half : EF)
    (r0 len : Nat) (hnz : ∀ k < len, twoX pw perm (r0 + k) ≠ 0) :
    Fri.foldRange vs pw perm beta half r0 len =
      Array.ofFn (n := len) fun k ↦ foldAt vs pw perm beta half (r0 + k.val) := by
  unfold Fri.foldRange
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure, Array.emptyWithCapacity_eq]
  rw [batchInv_eq id Function.injective_id (fun _ _ ↦ rfl) (fun _ ↦ rfl) rfl _ fun x hx ↦ by
    obtain ⟨k, rfl⟩ := Array.mem_ofFn.mp hx
    exact hnz k k.isLt]
  refine foldl_push_ofFn _ (fun k ↦ foldAt vs pw perm beta half (r0 + k)) len fun a ha ↦ ?_
  rw [getD_lt _ a (by rw [Array.size_map, Array.size_ofFn]; exact ha)]
  simp only [Array.getElem_map, Array.getElem_ofFn]

/-- The `2 x` of the fold's pairs are nonzero. -/
theorem twoX_ne_zero (L : Nat) (hL : L < twoAdicity F) (i : Nat) (hi : i < 2 ^ L) :
    twoX (cosetPoints (1 : F) (L + 1)) (bitRevPerm L) i ≠ 0 := by
  obtain ⟨hs, hb⟩ := bitRevPerm_spec L
  have hp : (bitRevPerm L).getD i 0 < 2 ^ L := by
    rw [getD_lt _ i (by omega)]
    exact hb _ (Array.getElem_mem _)
  have hw : (twoAdicGen (L + 1) : F) ≠ 0 :=
    BaseField.twoAdicGen_ne_zero _ (by omega)
  rw [twoX, cosetPoints_eq, getD_ofFn_bounded _ _ (by rw [Nat.pow_succ]; omega)]
  exact mul_ne_zero BaseField.two_ne_zero (mul_ne_zero one_ne_zero (pow_ne_zero _ hw))

/-- The fold, pair by pair. -/
theorem foldPairs_eq (vs : Array EF) (beta : EF) (L : Nat) (hL : L < twoAdicity F) :
    Fri.foldPairs vs beta L = Array.ofFn (n := 2 ^ L) fun i ↦
      foldAt vs (cosetPoints (1 : F) (L + 1)) (bitRevPerm L) beta (Ext.ofBase (2 : F)⁻¹) i.val := by
  unfold Fri.foldPairs
  exact parChunks_eq _ _ _ _ (fun r0 len h ↦
    foldRange_eq _ _ _ _ _ _ _ fun k hk ↦ twoX_ne_zero L hL _ (by omega))
    (Or.inl (by split <;> decide))

end CompStark.Stark

namespace CompStark.Stark.Fast
open Montgomery.Native32.Words
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (getD_ofFn_bounded size_encode_fields)
open CompPoly.CPolynomial.NTTFast.Packed.Native (zeroWords read write)
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p] {EF : Type} [FastExt p EF]

local notation "F" => FastField p

/-- Coordinate `c` of an extension element, zero beyond the degree. -/
def coord (c : Nat) (x : EF) : F := if h : c < FastExt.d p EF then FastExt.coord x ⟨c, h⟩ else 0

theorem coord_fin (x : EF) (k : Fin (FastExt.d p EF)) : coord k x = FastExt.coord x k := by
  rw [coord, dite_eq_left k.isLt]

/-- Representation transfers along equal arrays. -/
theorem RV_congr {v : ExtPlanes p EF} {a b : Array EF} (h : ExtPlanes.Rel v a) (e : a = b) :
    ExtPlanes.Rel v b := e ▸ h

/-- Values in the extension's bit-reversed order: entry `s` is entry `bitrev s` of `a`. -/
def bitRevValues (a : Array EF) : Array EF :=
  Array.ofFn (n := a.size) fun s ↦
    a.getD (CompPoly.CPolynomial.NTT.Transform.bitRevNat (Nat.log2 a.size) s.val) 0

/-- Quotient values as planes in the extension's bit-reversed order. -/
def QRel (q : ExtPlanes p EF) (a : Array EF) : Prop := ExtPlanes.Rel q (bitRevValues a)

/-- A slice of words is the encoded range. -/
theorem slice_encode (X : Array F) (i B : Nat) :
    slice (encode X) i B = encode (X.extract i (i + B)) := by
  apply ByteArray.ext
  rw [slice, ByteArray.data_extract]
  exact CompPoly.PackedRepr.encode_extract X i (i + B)

/-- The even and odd words. -/
theorem deinterleave_encode (Y : Array F) (n : Nat) (hn : 2 * n ≤ Y.size)
    (hs : 4 * Y.size < USize.size) :
    deinterleave (encode Y) n = (encode (Array.ofFn (n := n) fun i ↦ Y.getD (2 * i.val) 0),
      encode (Array.ofFn (n := n) fun i ↦ Y.getD (2 * i.val + 1) 0)) := by
  unfold deinterleave
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hz : 4 * (Array.replicate n (0 : F)).size < USize.size := by
    rw [Array.size_replicate]; omega
  let fe (i : Nat) : F := Y.getD (2 * i) 0
  let fo (i : Nat) : F := Y.getD (2 * i + 1) 0
  have key : ∀ K ≤ n, (List.range K).foldl
      (fun b i ↦ (write b.1 i (read (encode Y) (2 * i)), write b.2 i
          (read (encode Y) (2 * i + 1)))) (zeroWords n, zeroWords n) =
      (encode (upto (Array.replicate n 0) fe K), encode (upto (Array.replicate n 0) fo K)) := by
    intro K hK
    induction K with
    | zero => rw [List.range_zero, List.foldl_nil, zeroWords_eq (p := p), upto_zero, upto_zero]
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      simp only
      rw [read_encode Y _ hs (by omega), read_encode Y _ hs (by omega),
        write_upto _ fe K (by rw [Array.size_replicate]; omega) hz,
        write_upto _ fo K (by rw [Array.size_replicate]; omega) hz]
  rw [key n (Nat.le_refl _), upto_full _ _ _ (Array.size_replicate ..),
    upto_full _ _ _ (Array.size_replicate ..)]

/-- A plane of an array, tabulated. -/
theorem encode_map_coord (a : Array EF) (k : Fin (FastExt.d p EF)) :
    encode (a.map (FastExt.coord · k)) =
      encode (tab a.size fun i ↦ FastExt.coord (a.getD i 0) k) := by
  refine congrArg encode (Array.ext (by rw [Array.size_map, size_tab]) fun i h1 _ ↦ ?_)
  rw [Array.size_map] at h1
  rw [Array.getElem_map, getElem_tab, getD_lt a i h1]

/-- The even and odd elements of pairs `r0, …, r0 + len - 1`. -/
theorem split_rel {v : ExtPlanes p EF} {a : Array EF} (hv : ExtPlanes.Rel v a) (r0 len : Nat)
    (hr : 2 * (r0 + len) ≤ a.size) (hs : 4 * a.size < USize.size) :
    ExtPlanes.Rel ⟨len, (v.c.map fun b ↦ deinterleave (slice b (2 * r0) (2 * len)) len).map (·.1)⟩
      (tab len fun i ↦ a.getD (2 * (r0 + i)) 0) ∧
    ExtPlanes.Rel ⟨len, (v.c.map fun b ↦ deinterleave (slice b (2 * r0) (2 * len)) len).map (·.2)⟩
      (tab len fun i ↦ a.getD (2 * (r0 + i) + 1) 0) := by
  obtain ⟨-, hc⟩ := hv
  have hx (k : Fin (FastExt.d p EF)) :
      2 * r0 + 2 * len ≤ (a.map (FastExt.coord · k)).size := by rw [Array.size_map]; omega
  have hd (k : Fin (FastExt.d p EF)) :
      2 * len ≤ ((a.map (FastExt.coord · k)).extract (2 * r0) (2 * r0 + 2 * len)).size := by
    rw [Array.size_extract, Array.size_map]; omega
  have hds (k : Fin (FastExt.d p EF)) :
      4 * ((a.map (FastExt.coord · k)).extract (2 * r0) (2 * r0 + 2 * len)).size < USize.size := by
    rw [Array.size_extract, Array.size_map]; omega
  have he (k : Fin (FastExt.d p EF)) (j : Nat) (hj : j < 2 * len) :
      ((a.map (FastExt.coord · k)).extract (2 * r0) (2 * r0 + 2 * len)).getD j 0 =
        FastExt.coord (a.getD (2 * r0 + j) 0) k := by
    rw [CompPoly.CPolynomial.NTTFast.Packed.getD_extract _ _ _ _ _ (hx k) hj,
      ExtPlanes.getD_map a _ _ (by omega), getD_lt a _ (by omega)]
  constructor
  · refine ExtPlanes.rel_mk _ _ fun k ↦ ?_
    rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_map, ← Fin.getElem_fin, hc k,
      slice_encode, deinterleave_encode _ _ (hd k) (hds k)]
    refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
    rw [he k _ (by omega)]
    show _ = FastExt.coord (a.getD (2 * (r0 + i.val)) 0) k
    rw [Nat.mul_add]
  · refine ExtPlanes.rel_mk _ _ fun k ↦ ?_
    rw [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_map, ← Fin.getElem_fin, hc k,
      slice_encode, deinterleave_encode _ _ (hd k) (hds k)]
    refine congrArg encode (congrArg Array.ofFn (funext fun i ↦ ?_))
    rw [he k _ (by omega)]
    show _ = FastExt.coord (a.getD (2 * (r0 + i.val) + 1) 0) k
    rw [Nat.mul_add, Nat.add_assoc]

/-- Pairs `r0, …, r0 + len - 1` of the fold, given the encoded `2 x` of all pairs. -/
theorem fold2Range_rel [Mont32BaseField p] [Mont32.AlgebraId EF] {v : ExtPlanes p EF}
    {a : Array EF} (hv : ExtPlanes.Rel v a) (T : Array F) (beta : EF)
    (r0 len : Nat) (hr : 2 * (r0 + len) ≤ a.size) (hs : 4 * a.size < USize.size)
    (hT : r0 + len ≤ T.size) (hsT : 4 * T.size < USize.size)
    (hnz : ∀ k < len, T.getD (r0 + k) 0 ≠ 0) :
    ExtPlanes.Rel (fold2Range v (encode T) beta r0 len) (Array.ofFn (n := len) fun k ↦
      (a.getD (2 * (r0 + k.val)) 0 + a.getD (2 * (r0 + k.val) + 1) 0) * Ext.ofBase (2 : F)⁻¹ +
        beta * (a.getD (2 * (r0 + k.val)) 0 - a.getD (2 * (r0 + k.val) + 1) 0) *
          Ext.ofBase (T.getD (r0 + k.val) 0)⁻¹) := by
  obtain ⟨hl, hh⟩ := split_rel hv r0 len hr hs
  have hn : 4 * len < USize.size := by omega
  unfold fold2Range
  simp only
  rw [batchInvRange_encode T r0 len hT hsT hnz]
  have h1 := ExtPlanes.mulBase_rel hn (fun _ ↦ (2 : F)⁻¹) (ExtPlanes.add_rel hn hl hh)
  rw [← Words.replicateWord_tab hn] at h1
  have h2 := ExtPlanes.smul_rel hn beta (ExtPlanes.mulBase_rel hn
    (fun k ↦ (T.getD (r0 + k) 0)⁻¹) (ExtPlanes.sub_rel hn hl hh))
  refine RV_congr (ExtPlanes.add_rel hn h1 h2) (congrArg Array.ofFn (funext fun k ↦ ?_))
  apply FastExt.toSpec_injective
  simp only [← Mont32.toSpec_eq, Challenge.toSpec_add, Challenge.toSpec_mul, Challenge.toSpec_sub,
    ← Mont32.ofBase_eq]
  ring

/-- Vectors within the two-adic subgroups have indexable coordinates when the largest
subgroup's do. -/
theorem size_bound [Mont32BaseField p] {n : Nat}
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size)
    (h : n ≤ 2 ^ twoAdicity F) : 4 * (FastExt.d p EF * n) < USize.size := by
  have := Nat.mul_le_mul_left (FastExt.d p EF) h
  omega

theorem size_bound' [Mont32BaseField p] {n : Nat}
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size)
    (h : n ≤ 2 ^ twoAdicity F) : 4 * n < USize.size := by
  have := size_bound hA h
  have : n ≤ FastExt.d p EF * n :=
    Nat.le_mul_of_pos_left n (FastExt.params (p := p) EF).d_pos
  omega

/-- The fast fold is the specification's: both invert every `2 x` of the pairs, which are
nonzero within the two-adic subgroups. -/
theorem fold2_rel [Mont32BaseField p] [Mont32.AlgebraId EF]
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size)
    {v : ExtPlanes p EF} {a : Array EF} (beta : EF)
    (k : Nat) (h : ExtPlanes.Rel v a) (ha : a.size = 2 ^ (k + 1)) (hk : k < twoAdicity F) :
    ExtPlanes.Rel (fold2 v beta k) (Fri.foldPairs a beta k) := by
  unfold fold2
  have hs : 4 * a.size < USize.size :=
    size_bound' hA (by rw [ha]; exact Nat.pow_le_pow_right (by decide) hk)
  rw [Nat.pow_succ, Nat.mul_comm] at ha
  simp only [CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq]
  have hp : 0 < (if 2 ^ k < 4096 then 1 else 16) := by split <;> decide
  generalize (if 2 ^ k < 4096 then 1 else 16) = parts at hp ⊢
  let pw := cosetPoints (1 : F) (k + 1)
  let perm := bitRevPerm k
  let T : Array F := perm.map fun i ↦ 2 * pw.getD i 0
  have hT : T.size = 2 ^ k := by rw [Array.size_map]; exact (bitRevPerm_spec k).1
  have hTx : ∀ i < 2 ^ k, T.getD i 0 = twoX pw perm i := fun i hi ↦ by
    rw [getD_lt _ _ (by rw [hT]; exact hi), Array.getElem_map, twoX,
      getD_lt perm _ (by rw [(bitRevPerm_spec k).1]; exact hi)]
  let E (i : Nat) : EF := (a.getD (2 * i) 0 + a.getD (2 * i + 1) 0) * Ext.ofBase (2 : F)⁻¹ +
    beta * (a.getD (2 * i) 0 - a.getD (2 * i + 1) 0) * Ext.ofBase (T.getD i 0)⁻¹
  have hcat := foldl_ranges E (2 ^ k) parts _ hp (ranges_cover (2 ^ k) parts)
  have hj := ExtPlanes.join_rel (2 ^ k) parts
    (fun p ↦ fold2Range v (encode T) beta (p * (2 ^ k / parts))
      (if p + 1 = parts then 2 ^ k - p * (2 ^ k / parts) else 2 ^ k / parts))
    (fun p ↦ Array.ofFn (n := if p + 1 = parts then 2 ^ k - p * (2 ^ k / parts)
      else 2 ^ k / parts) fun j ↦ E (p * (2 ^ k / parts) + j.val))
    (fun p hp' ↦ by
      have hle := range_le (2 ^ k) parts p hp'
      exact fold2Range_rel h T beta _ _ (by omega) hs (by omega) (by omega)
        fun j hj ↦ by
          rw [hTx _ (by omega)]
          exact twoX_ne_zero k hk _ (by omega))
    (by rw [hcat, Array.size_ofFn])
  rw [hcat] at hj
  refine RV_congr hj ?_
  rw [foldPairs_eq a beta k hk]
  refine congrArg (Array.ofFn (n := 2 ^ k)) (funext fun i ↦ ?_)
  simp only [E, hTx i.val i.isLt]
  rfl

/-- The fast fold by `2 ^ la` is the specification's. -/
theorem fold_rel [Mont32BaseField p] [Mont32.AlgebraId EF]
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size)
    (la : Nat) (beta : EF) (s : Nat) {v : ExtPlanes p EF} {a : Array EF}
    (h : ExtPlanes.Rel v a) (ha : a.size = 2 ^ s) (hla : la ≤ s) (hs : s ≤ twoAdicity F) :
    ExtPlanes.Rel (fold la beta v) (Fri.foldOnce la beta a) := by
  have hrows : v.n / 2 ^ la = 2 ^ (s - la) := by rw [h.1, ha, Nat.pow_div hla (by decide)]
  have hrows' : a.size / 2 ^ la = 2 ^ (s - la) := by rw [← h.1, hrows]
  unfold fold Fri.foldOnce
  dsimp only
  rw [hrows, hrows', Nat.log2_two_pow]
  split
  · rename_i h1
    subst h1
    exact fold2_rel hA beta (s - 1) h (by rw [ha]; congr 1; omega) (by omega)
  · rw [ExtPlanes.toArray_eq h (size_bound' hA (n := a.size) (by
      rw [ha]; exact Nat.pow_le_pow_right (by decide) hs))]
    rw [parChunks_eq (2 ^ (s - la)) _ _ (fun r ↦ Fri.foldRow r (s - la) la beta
      ((List.range (2 ^ la)).map fun k ↦ a.getD (r * 2 ^ la + k) 0)) (fun _ _ _ ↦ rfl)
      (by split <;> simp only [Nat.zero_lt_one, Nat.ofNat_pos, true_or])]
    exact ExtPlanes.ofArray_rel _

/-- Represented planes read back their elements. -/
theorem toArray_rel [Mont32BaseField p]
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size) {v : ExtPlanes p EF}
    {a : Array EF} (h : ExtPlanes.Rel v a) (ha : a.size ≤ 2 ^ twoAdicity F) : v.toArray = a :=
  ExtPlanes.toArray_eq h (size_bound' hA ha)

/-- `a + x · b` on planes. -/
theorem addScaled_rel [Mont32BaseField p] [Mont32.AlgebraId EF]
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size)
    {v w : ExtPlanes p EF} {a b : Array EF}
    (x : EF) (hv : ExtPlanes.Rel v a) (hw : ExtPlanes.Rel w b) (hab : a.size = b.size)
    (ha : a.size ≤ 2 ^ twoAdicity F) :
    ExtPlanes.Rel (addScaled v w x) (Array.zipWith (fun u v ↦ u + x * v) a b) := by
  have hs : 4 * a.size < USize.size := size_bound' hA ha
  rw [ExtPlanes.tab_getD a] at hv
  rw [ExtPlanes.tab_getD b, ← hab] at hw
  unfold addScaled
  refine RV_congr (ExtPlanes.add_rel hs hv (ExtPlanes.smul_rel hs x hw))
    (Array.ext (by simp only [size_tab, Array.size_zipWith, hab, Nat.min_self]) fun i h1 _ ↦ ?_)
  rw [size_tab] at h1
  rw [getElem_tab, Array.getElem_zipWith, ← getD_lt a i h1, ← getD_lt b i (by omega)]
  exact congrArg _ (FastExt.mul_comm _ _)

/-- A bit-reversed index is an index. -/
theorem bitRevNat_log2_lt {n s : Nat} (hs : s < n) :
    CompPoly.CPolynomial.NTT.Transform.bitRevNat (Nat.log2 n) s < n :=
  Nat.lt_of_lt_of_le (CompPoly.CPolynomial.NTT.Transform.bitRevNat_lt _ _)
    (Nat.log2_self_le (by omega))

/-- `q · x + l` on quotient values in bit-reversed order. -/
theorem combine_rel [Mont32BaseField p] [Mont32.AlgebraId EF]
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size)
    {q r : ExtPlanes p EF} {a b : Array EF} (x : EF) (hq : QRel q a) (hr : QRel r b)
    (hab : a.size = b.size) (ha : a.size ≤ 2 ^ twoAdicity F) :
    QRel (addScaled r q x) (Array.zipWith (fun q l ↦ q * x + l) a b) := by
  have h := addScaled_rel hA x hr hq (by simp only [bitRevValues, Array.size_ofFn, hab])
    (by simp only [bitRevValues, Array.size_ofFn, ← hab]; exact ha)
  refine RV_congr h (Array.ext (by simp only [bitRevValues, Array.size_zipWith, Array.size_ofFn,
    hab, Nat.min_self]) fun s h1 _ ↦ ?_)
  simp only [bitRevValues, Array.size_zipWith, Array.size_ofFn, hab, Nat.min_self] at h1
  have hs := bitRevNat_log2_lt h1
  simp only [bitRevValues, Array.getElem_zipWith, Array.getElem_ofFn, Array.size_zipWith, hab,
    Nat.min_self]
  rw [getD_lt _ _ hs, getD_lt _ _ (by rw [hab]; exact hs), getD_lt _ _ (by
    rw [Array.size_zipWith, hab, Nat.min_self]; exact hs), Array.getElem_zipWith]
  apply FastExt.toSpec_injective
  simp only [← Mont32.toSpec_eq, Challenge.toSpec_add, Challenge.toSpec_mul]
  ring

/-- The coordinates of tabulated elements, flattened. -/
theorem flatMap_coeffs [Mont32BaseField p] [Mont32.AlgebraId EF] (n : Nat) (g : Nat → EF) :
    (Array.ofFn (n := n) fun j ↦ g j.val).flatMap (fun x ↦ (Ext.coeffs x).toArray) =
      Array.ofFn (n := FastExt.d p EF * n) fun t ↦
        coord (t.val % FastExt.d p EF) (g (t.val / FastExt.d p EF)) := by
  have hd := (FastExt.params (p := p) EF).d_pos
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Array.ofFn_succ, Array.flatMap_push]
    simp only [Fin.val_castSucc]
    rw [ih, ofFn_len (fun t ↦ coord (t % FastExt.d p EF) (g (t / FastExt.d p EF)))
      (show FastExt.d p EF * (n + 1) = FastExt.d p EF * n + FastExt.d p EF by ring),
      ← ofFn_append (fun t ↦ coord (t % FastExt.d p EF) (g (t / FastExt.d p EF)))
        (FastExt.d p EF * n) (FastExt.d p EF)]
    congr 1
    apply Array.ext (by simp only [Array.size_ofFn, Ext.coeffs, Mont32.coeffs_eq,
      List.size_toArray, List.length_ofFn])
    intro t _ h1
    rw [Array.size_ofFn] at h1
    simp only [Array.getElem_ofFn, Ext.coeffs, Mont32.coeffs_eq, List.getElem_toArray,
      List.getElem_ofFn]
    rw [show (FastExt.d p EF * n + t) / FastExt.d p EF = n by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h1,
          Nat.zero_add],
      show (FastExt.d p EF * n + t) % FastExt.d p EF = t by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]]
    rw [coord, dite_eq_left h1]

/-- Every `k`-th word from word `i`. -/
theorem strided_encode (A : Array F) (i k count : Nat) (hA : ∀ r < count, r * k + i < A.size)
    (hs : 4 * A.size < USize.size) (hc : 4 * count < USize.size) :
    strided (encode A) i k count = encode (Array.ofFn (n := count) fun r ↦ A.getD (r.val * k + i) 0)
    := by
  unfold strided
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  let f (r : Nat) : F := A.getD (r * k + i) 0
  have ho : 4 * (Array.replicate count (0 : F)).size < USize.size := by
    rw [Array.size_replicate]; exact hc
  have key : ∀ K ≤ count, (List.range K).foldl (fun b r ↦ write b r (read (encode A) (r * k + i)))
      (zeroWords count) = encode (upto (Array.replicate count 0) f K) := by
    intro K hK
    induction K with
    | zero => rw [List.range_zero, List.foldl_nil, zeroWords_eq (p := p), upto_zero]
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        read_encode _ _ hs (hA K (by omega)),
        write_upto _ f _ (by rw [Array.size_replicate]; omega) ho]
  rw [key count le_rfl, upto_full _ _ _ (Array.size_replicate ..)]

/-- The leaves are the elements' coordinates, `k` elements per row. -/
theorem leaves_rel [Mont32BaseField p] [Mont32.AlgebraId EF]
    (hA : 4 * (FastExt.d p EF * 2 ^ twoAdicity F) < USize.size)
    {v : ExtPlanes p EF} {a : Array EF} (k : Nat)
    (h : ExtPlanes.Rel v a) (ha : a.size ≤ 2 ^ twoAdicity F) (hk : k ∣ a.size) (h0 : 0 < a.size) :
    RM (leaves k v) (Mat.ofValues (FastExt.d p EF * k) (a.size / k)
      (a.flatMap fun x ↦ (Ext.coeffs x).toArray)) := by
  have hs := size_bound hA ha
  have hd := (FastExt.params (p := p) EF).d_pos
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_dvd] at hk; omega)
  obtain ⟨n, hn⟩ := hk
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hn; omega)
  have hdiv : a.size / k = n := by rw [hn, Nat.mul_div_cancel_left _ hk0]
  have hna : n ≤ a.size := by rw [hn]; exact Nat.le_mul_of_pos_left n hk0
  have hsa : 4 * a.size < USize.size := by
    have : a.size ≤ FastExt.d p EF * a.size := Nat.le_mul_of_pos_left _ hd
    omega
  obtain ⟨hvn, hc⟩ := h
  unfold leaves
  rw [hvn, hdiv]
  have hfl : (a.flatMap fun x ↦ (Ext.coeffs x).toArray) =
      Array.ofFn (n := FastExt.d p EF * a.size) fun t ↦
        coord (t.val % FastExt.d p EF) (a.getD (t.val / FastExt.d p EF) 0) := by
    have e : a = Array.ofFn (n := a.size) fun j ↦ a.getD j.val 0 :=
      Array.ext (by rw [Array.size_ofFn]) fun j h1 _ ↦ by
        rw [Array.getElem_ofFn, getD_lt a j h1]
    conv_lhs => rw [e]
    rw [flatMap_coeffs a.size (fun j ↦ a.getD j 0)]
  refine ⟨rfl, rfl, ?_, hn0, ?_, Nat.mod_self n, ?_⟩
  · show (a.flatMap fun x ↦ (Ext.coeffs x).toArray).size = FastExt.d p EF * k * n
    rw [hfl, Array.size_ofFn, hn, Nat.mul_assoc]
  · show 4 * n < USize.size
    omega
  · show (CompPoly.Tasks.join (CompPoly.Tasks.spawnAll (FastExt.d p EF * k) fun j ↦
      strided (v.c.toArray.getD (j % FastExt.d p EF) .empty) (j / FastExt.d p EF) k n)).get = _
    rw [CompPoly.Tasks.get_join, CompPoly.Tasks.map_get_spawnAll]
    apply Array.ext (by
      simp only [Array.size_map, Array.size_range, size_colBlocks, Mat.ofValues,
        Nat.div_self hn0, Nat.one_mul])
    intro j h1 _
    simp only [Array.size_map, Array.size_range] at h1
    simp only [Array.getElem_map, Array.getElem_ofFn, Array.getElem_range, colBlocks,
      Mat.ofValues]
    have hjd : j % FastExt.d p EF < FastExt.d p EF := Nat.mod_lt _ hd
    have hjk : j / FastExt.d p EF < k := by
      rw [Nat.div_lt_iff_lt_mul hd, Nat.mul_comm]; exact h1
    have hj : v.c.toArray.getD (j % FastExt.d p EF) .empty =
        encode (a.map fun x ↦ coord (j % FastExt.d p EF) x) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hjd),
        Option.getD_some, Vector.getElem_toArray]
      have := hc ⟨j % FastExt.d p EF, hjd⟩
      simp only [Fin.getElem_fin] at this
      rw [this]
      exact congrArg encode (Array.map_congr_left fun x _ ↦ (coord_fin x _).symm)
    rw [hj, strided_encode _ _ _ _ (fun r hr ↦ by
        rw [Array.size_map, hn]
        have := Nat.mul_le_mul_right k (show r + 1 ≤ n by omega)
        rw [Nat.succ_mul] at this
        rw [Nat.mul_comm k n]; omega) (by rw [Array.size_map]; exact hsa) (by omega)]
    refine congrArg encode (congrArg Array.ofFn (funext fun r ↦ ?_))
    have hr : r.val * k + j / FastExt.d p EF < a.size := by
      rw [hn]
      have := Nat.mul_le_mul_right k (show r.val + 1 ≤ n by omega)
      rw [Nat.succ_mul] at this
      rw [Nat.mul_comm k n]; omega
    rw [ExtPlanes.getD_map _ _ _ hr]
    have hidx : (j / (FastExt.d p EF * k) * n + r.val) * (FastExt.d p EF * k) +
        j % (FastExt.d p EF * k) = r.val * (FastExt.d p EF * k) + j := by
      rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.zero_mul, Nat.zero_add]
    have hlt : r.val * (FastExt.d p EF * k) + j < FastExt.d p EF * a.size := by
      rw [hn]
      have := Nat.mul_le_mul_right (FastExt.d p EF * k) (show r.val + 1 ≤ n by omega)
      rw [Nat.succ_mul] at this
      have : FastExt.d p EF * (k * n) = n * (FastExt.d p EF * k) := by ring
      omega
    rw [hidx, hfl, CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hlt]
    dsimp only
    have e4 : r.val * (FastExt.d p EF * k) = FastExt.d p EF * (r.val * k) := by ring
    rw [e4, Nat.mul_add_mod, Nat.mul_add_div hd, getD_lt a _ hr]

end CompStark.Stark.Fast
