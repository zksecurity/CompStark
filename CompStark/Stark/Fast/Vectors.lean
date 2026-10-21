/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.WordsLemmas
public import CompStark.Stark.Fast.OpeningsSpec
public import CompStark.Stark.Fast.BatchInv

/-! # The fast backend's vector laws

The fast backend's vectors of extension elements read back, scale-add, fold and lay out as leaves
as the specification's.
-/

@[expose] public section
namespace CompStark.Stark
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
open CompPoly.PackedRepr (encode)
open CompStark.Words
open CompPoly.CPolynomial.NTTFast.Packed (getD_ofFn_bounded size_encode_fields)
open CompPoly.CPolynomial.NTTFast.Packed.Native (zeroWords read write)
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p] [Mont32BaseField p] [Binomial4 p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

omit [Mont32BaseField p] [Binomial4 p] in
/-- Representation transfers along equal arrays. -/
theorem RV_congr {v : EVec p} {a b : Array EF} (h : RV v a) (e : a = b) : RV v b := e ▸ h

omit [Mont32BaseField p] [Binomial4 p] in
/-- A slice of words is the encoded range. -/
theorem slice_encode (X : Array F) (i B : Nat) :
    slice (encode X) i B = encode (X.extract i (i + B)) := by
  apply ByteArray.ext
  rw [slice, ByteArray.data_extract]
  exact CompPoly.PackedRepr.encode_extract X i (i + B)

omit [Mont32BaseField p] [Binomial4 p] in
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
  have key : ∀ K ≤ n, (List.range K).foldl (fun b i ↦ (write b.1 i (read (encode Y) (2 * i)),
      write b.2 i (read (encode Y) (2 * i + 1)))) (zeroWords n, zeroWords n) =
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

omit [Mont32BaseField p] [Binomial4 p] in
/-- The even and odd elements of pairs `r0, …, r0 + len - 1`. -/
theorem split_rel {v : EVec p} {a : Array EF} (hv : RV v a) (r0 len : Nat)
    (hr : 2 * (r0 + len) ≤ a.size) (hs : 4 * a.size < USize.size) :
    RV ⟨len, (deinterleave (slice v.c0 (2 * r0) (2 * len)) len).1,
      (deinterleave (slice v.c1 (2 * r0) (2 * len)) len).1,
      (deinterleave (slice v.c2 (2 * r0) (2 * len)) len).1,
      (deinterleave (slice v.c3 (2 * r0) (2 * len)) len).1⟩
      (Array.ofFn (n := len) fun i ↦ a.getD (2 * (r0 + i.val)) 0) ∧
    RV ⟨len, (deinterleave (slice v.c0 (2 * r0) (2 * len)) len).2,
      (deinterleave (slice v.c1 (2 * r0) (2 * len)) len).2,
      (deinterleave (slice v.c2 (2 * r0) (2 * len)) len).2,
      (deinterleave (slice v.c3 (2 * r0) (2 * len)) len).2⟩
      (Array.ofFn (n := len) fun i ↦ a.getD (2 * (r0 + i.val) + 1) 0) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  have hx : ∀ p : EF → F, 2 * r0 + 2 * len ≤ (a.map p).size := fun p ↦ by
    rw [Array.size_map]; omega
  have hd : ∀ p : EF → F, 2 * len ≤ ((a.map p).extract (2 * r0) (2 * r0 + 2 * len)).size :=
    fun p ↦ by rw [Array.size_extract, Array.size_map]; omega
  have hds : ∀ p : EF → F,
      4 * ((a.map p).extract (2 * r0) (2 * r0 + 2 * len)).size < USize.size :=
    fun p ↦ by rw [Array.size_extract, Array.size_map]; omega
  have he : ∀ (p : EF → F) (j : Nat), j < 2 * len →
      ((a.map p).extract (2 * r0) (2 * r0 + 2 * len)).getD j 0 = p (a.getD (2 * r0 + j) 0) :=
    fun p j hj ↦ by
      rw [CompPoly.CPolynomial.NTTFast.Packed.getD_extract _ _ _ _ _ (hx p) hj,
        EVec.getD_map a p _ (by omega), getD_lt a _ (by omega)]
  simp only [h0, h1, h2, h3, slice_encode, deinterleave_encode _ _ (hd _) (hds _)]
  let E (p : EF → F) (j : Nat) : F := ((a.map p).extract (2 * r0) (2 * r0 + 2 * len)).getD j 0
  constructor
  · refine EVec.rv_mk _ (Array.size_ofFn ..) (fun i ↦ E (·.c0) (2 * i)) (fun i ↦ E (·.c1) (2 * i))
      (fun i ↦ E (·.c2) (2 * i)) (fun i ↦ E (·.c3) (2 * i)) rfl rfl rfl rfl fun i hi ↦ ?_
    rw [Array.size_ofFn] at hi
    simp only [E, Array.getElem_ofFn, he _ _ (show 2 * i < 2 * len by omega), Nat.mul_add]
  · refine EVec.rv_mk _ (Array.size_ofFn ..) (fun i ↦ E (·.c0) (2 * i + 1))
      (fun i ↦ E (·.c1) (2 * i + 1)) (fun i ↦ E (·.c2) (2 * i + 1)) (fun i ↦ E (·.c3) (2 * i + 1))
      rfl rfl rfl rfl fun i hi ↦ ?_
    rw [Array.size_ofFn] at hi
    simp only [E, Array.getElem_ofFn, he _ _ (show 2 * i + 1 < 2 * len by omega), Nat.mul_add,
      Nat.add_assoc]

/-- Pairs `r0, …, r0 + len - 1` of the fold, given the encoded `2 x` of all pairs. -/
theorem fold2Range_rel {v : EVec p} {a : Array EF} (hv : RV v a) (T : Array F) (beta : EF)
    (r0 len : Nat) (hr : 2 * (r0 + len) ≤ a.size) (hs : 4 * a.size < USize.size)
    (hT : r0 + len ≤ T.size) (hsT : 4 * T.size < USize.size)
    (hnz : ∀ k < len, T.getD (r0 + k) 0 ≠ 0) :
    RV (fold2Range v (encode T) beta r0 len) (Array.ofFn (n := len) fun k ↦
      (a.getD (2 * (r0 + k.val)) 0 + a.getD (2 * (r0 + k.val) + 1) 0) * Ext.ofBase (2 : F)⁻¹ +
        beta * (a.getD (2 * (r0 + k.val)) 0 - a.getD (2 * (r0 + k.val) + 1) 0) *
          Ext.ofBase (T.getD (r0 + k.val) 0)⁻¹) := by
  obtain ⟨hl, hh⟩ := split_rel hv r0 len hr hs
  have hn : 4 * (Array.ofFn (n := len) fun i ↦ a.getD (2 * (r0 + i.val)) 0).size < USize.size := by
    rw [Array.size_ofFn]; omega
  unfold fold2Range
  simp only
  rw [batchInvRange_encode T r0 len hT hsT hnz]
  have h1 := EVec.smul_rel (Ext.ofBase (2 : F)⁻¹) (EVec.add_rel hl hh rfl hn)
    (by rw [Array.size_zipWith, Array.size_ofFn, Array.size_ofFn, Nat.min_self]; omega)
  have h2 := EVec.smul_rel beta (EVec.mulBase_rel
    (Array.ofFn (n := len) fun k ↦ (T.getD (r0 + k.val) 0)⁻¹) (EVec.sub_rel hl hh rfl hn)
    (by rw [Array.size_zipWith, Array.size_ofFn, Array.size_ofFn, Array.size_ofFn, Nat.min_self])
    (by rw [Array.size_ofFn]; omega))
    (by rw [Array.size_zipWith, Array.size_zipWith, Array.size_ofFn, Array.size_ofFn,
      Array.size_ofFn, Nat.min_self, Nat.min_self]; omega)
  have h3 := EVec.add_rel h1 h2 (by simp only [EVec.smul, EVec.add, EVec.sub, EVec.mulBase]) (by
    rw [Array.size_map, Array.size_zipWith, Array.size_ofFn, Array.size_ofFn, Nat.min_self]; omega)
  refine RV_congr h3 (Array.ext ?_ fun k h1 h2 ↦ ?_)
  · simp only [Array.size_zipWith, Array.size_map, Array.size_ofFn, Nat.min_self]
  · simp only [Array.getElem_zipWith, Array.getElem_map, Array.getElem_ofFn]
    apply Montgomery.Native32.Ext4.toSpec_injective
    simp only [Montgomery.Native32.Ext4.toSpec_add, Montgomery.Native32.Ext4.toSpec_mul,
      Montgomery.Native32.Ext4.toSpec_sub]
    ring

omit [Binomial4 p] in
/-- Vectors within the two-adic subgroups have indexable coordinates when the largest
subgroup's do. -/
theorem size_bound {n : Nat} (hA : 16 * 2 ^ twoAdicity F < USize.size)
    (h : n ≤ 2 ^ twoAdicity F) : 16 * n < USize.size := by
  omega

/-- The fast fold is the specification's: both invert every `2 x` of the pairs, which are
nonzero within the two-adic subgroups. -/
theorem fold2_rel (hA : 16 * 2 ^ twoAdicity F < USize.size) {v : EVec p} {a : Array EF}
    (beta : EF) (k : Nat) (h : RV v a) (ha : a.size = 2 ^ (k + 1)) (hk : k < twoAdicity F) :
    RV (fold2 v beta k) (Fri.foldPairs a beta k) := by
  unfold fold2
  have hs : 4 * a.size < USize.size := by
    have := size_bound (n := a.size) hA (by rw [ha]; exact Nat.pow_le_pow_right (by decide) hk)
    omega
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
  have hj := joinPlanes_rel (2 ^ k) parts
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

omit [Binomial4 p] in
/-- Represented planes read back their elements. -/
theorem toArray_rel (hA : 16 * 2 ^ twoAdicity F < USize.size) {v : EVec p} {a : Array EF}
    (h : RV v a) (ha : a.size ≤ 2 ^ twoAdicity F) : v.toArray = a :=
  EVec.toArray_eq h (by have := size_bound hA ha; omega)

omit [Mont32BaseField p] [Binomial4 p] in
/-- The planes of an array represent it. -/
theorem ofArray_rel (a : Array EF) : RV (EVec.ofArray a) a := EVec.ofArray_rel a

/-- `a + x · b` on planes. -/
theorem addScaled_rel (hA : 16 * 2 ^ twoAdicity F < USize.size) {v w : EVec p} {a b : Array EF}
    (x : EF) (hv : RV v a) (hw : RV w b) (hab : a.size = b.size) (ha : a.size ≤ 2 ^ twoAdicity F) :
    RV (addScaled v w x) (Array.zipWith (fun u v ↦ u + x * v) a b) := by
  have hs : 4 * a.size < USize.size := by have := size_bound hA ha; omega
  unfold addScaled
  have h := EVec.add_rel hv (EVec.smul_rel x hw (by omega))
    (by simp only [EVec.smul]; rw [hv.1, hw.1, hab]) hs
  refine RV_congr h (Array.ext (by simp only [Array.size_zipWith, Array.size_map])
    fun i _ _ ↦ ?_)
  simp only [Array.getElem_zipWith, Array.getElem_map]
  apply Montgomery.Native32.Ext4.toSpec_injective
  simp only [Montgomery.Native32.Ext4.toSpec_add, Montgomery.Native32.Ext4.toSpec_mul]
  ring

/-- Coordinate `c` of an extension element. -/
def coord (c : Nat) (x : EF) : F :=
  match c with
  | 0 => x.c0
  | 1 => x.c1
  | 2 => x.c2
  | _ => x.c3

/-- The coordinates of tabulated elements, flattened. -/
theorem flatMap_coeffs (n : Nat) (g : Nat → EF) :
    (Array.ofFn (n := n) fun j ↦ g j.val).flatMap (fun x ↦ (Ext.coeffs x).toArray) =
      Array.ofFn (n := 4 * n) fun t ↦ coord (t.val % 4) (g (t.val / 4)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Array.ofFn_succ, Array.flatMap_push]
    simp only [Fin.val_castSucc]
    rw [ih, ofFn_len (fun t ↦ coord (t % 4) (g (t / 4)))
      (show 4 * (n + 1) = 4 * n + 4 by omega),
      ← ofFn_append (fun t ↦ coord (t % 4) (g (t / 4))) (4 * n) 4]
    congr 1
    apply Array.ext (by simp only [Array.size_ofFn, Ext.coeffs, Mont32.coeffs_ext4,
      List.size_toArray, List.length_cons, List.length_nil])
    intro t _ h1
    rw [Array.size_ofFn] at h1
    simp only [Array.getElem_ofFn, Ext.coeffs, Mont32.coeffs_ext4]
    rw [show (4 * n + t) / 4 = n by omega, show (4 * n + t) % 4 = t by omega]
    interval_cases t <;> rfl

/-- The coordinates of elements `i0, …, i0 + len - 1`, interleaved. -/
theorem interleaveRange_encode {v : EVec p} {a : Array EF} (hv : RV v a) (i0 len : Nat)
    (hi : i0 + len ≤ a.size) (hs : 16 * a.size < USize.size) :
    interleaveRange v.c0 v.c1 v.c2 v.c3 i0 len = encode ((Array.ofFn (n := len) fun j ↦
      a.getD (i0 + j.val) 0).flatMap fun x ↦ (Ext.coeffs x).toArray) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  unfold interleaveRange
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure, h0, h1, h2, h3]
  let f (t : Nat) : F := coord (t % 4) (a.getD (i0 + t / 4) 0)
  have ho : 4 * (Array.replicate (4 * len) (0 : F)).size < USize.size := by
    rw [Array.size_replicate]; omega
  have hm : ∀ p : EF → F, 4 * (a.map p).size < USize.size := fun p ↦ by
    rw [Array.size_map]; omega
  have hr : ∀ (p : EF → F) (c K : Nat), K < len → c < 4 →
      (∀ x : EF, coord c x = p x) → read (encode (a.map p)) (i0 + K) = (f (4 * K + c)).val :=
    fun p c K hK hc hp ↦ by
      rw [read_encode _ _ (hm p) (by rw [Array.size_map]; omega),
        EVec.getD_map a p _ (by omega), ← getD_lt a _ (by omega), ← hp]
      simp only [f]
      rw [show (4 * K + c) % 4 = c by omega, show (4 * K + c) / 4 = K by omega]
  have key : ∀ K ≤ len, (List.range K).foldl (fun b k ↦
      write (write (write (write b (4 * k) (read (encode (a.map (·.c0))) (i0 + k))) (4 * k + 1)
        (read (encode (a.map (·.c1))) (i0 + k))) (4 * k + 2)
        (read (encode (a.map (·.c2))) (i0 + k))) (4 * k + 3)
        (read (encode (a.map (·.c3))) (i0 + k)))
      (zeroWords (4 * len)) = encode (upto (Array.replicate (4 * len) 0) f (4 * K)) := by
    intro K hK
    induction K with
    | zero => rw [List.range_zero, List.foldl_nil, zeroWords_eq (p := p), Nat.mul_zero, upto_zero]
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      have hK : K < len := by omega
      have r0 := hr (·.c0) 0 K hK (by decide) fun _ ↦ rfl
      rw [Nat.add_zero] at r0
      rw [r0, hr (·.c1) 1 K hK (by decide) fun _ ↦ rfl, hr (·.c2) 2 K hK (by decide) fun _ ↦ rfl,
        hr (·.c3) 3 K hK (by decide) fun _ ↦ rfl]
      rw [write_upto _ f _ (by rw [Array.size_replicate]; omega) ho,
        write_upto _ f _ (by rw [Array.size_replicate]; omega) ho,
        write_upto _ f _ (by rw [Array.size_replicate]; omega) ho,
        write_upto _ f _ (by rw [Array.size_replicate]; omega) ho, Nat.mul_succ]
  rw [key len (Nat.le_refl _), upto_full _ _ _ (Array.size_replicate ..),
    flatMap_coeffs len fun j ↦ a.getD (i0 + j) 0]

/-- Flattening commutes with concatenation. -/
theorem foldl_append_flatMap {α β : Type} (g : α → Array β) (A : Nat → Array α) (L : List Nat)
    (acc : Array α) :
    L.foldl (fun acc k ↦ acc ++ (A k).flatMap g) (acc.flatMap g) =
      (L.foldl (fun acc k ↦ acc ++ A k) acc).flatMap g := by
  induction L generalizing acc with
  | nil => rfl
  | cons k L ih => rw [List.foldl_cons, List.foldl_cons, ← Array.flatMap_append, ih]

/-- The leaves are the elements' coordinates, `k` elements per row. -/
theorem leaves_rel (hA : 16 * 2 ^ twoAdicity F < USize.size) {v : EVec p} {a : Array EF}
    (k : Nat) (h : RV v a) (ha : a.size ≤ 2 ^ twoAdicity F) :
    RM (leaves k v) (Mat.ofValues (4 * k) (a.size / k)
      (a.flatMap fun x ↦ (Ext.coeffs x).toArray)) := by
  unfold leaves
  have hs := size_bound hA ha
  rw [h.1]
  refine ⟨rfl, rfl, ?_⟩
  simp only [Mat.ofValues]
  have hp : 0 < (if a.size < 4096 then 1 else 16) := by split <;> decide
  generalize (if a.size < 4096 then 1 else 16) = parts at hp ⊢
  rw [foldl_tasks parts _ (fun p ↦ (Array.ofFn (n := if p + 1 = parts then
      a.size - p * (a.size / parts) else a.size / parts) fun j ↦
      a.getD (p * (a.size / parts) + j.val) 0).flatMap fun x ↦ (Ext.coeffs x).toArray)
      fun p hp' ↦ interleaveRange_encode h _ _ (range_le a.size parts p hp') hs,
    ← Array.flatMap_empty (fun x : EF ↦ (Ext.coeffs x).toArray), foldl_append_flatMap,
    foldl_ranges (fun j ↦ a.getD j 0) a.size parts _ hp (ranges_cover a.size parts)]
  congr 2
  apply Array.ext (by rw [Array.size_ofFn])
  intro i h1 _
  rw [Array.size_ofFn] at h1
  simp only [Array.getElem_ofFn, getD_lt a i h1]

end CompStark.Stark.Fast
