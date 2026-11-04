/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.LookupQuotient
public import CompStark.Stark.Fast.Lde

/-! # The fast permutation trace is the specification's

Inverses of planes are the extension's inversion of planes, zeros left zero
(`PlanesInv.inv_rel`). So a block's fractions are the specification's
(`fractionsX_rel`), the rows of a block are the transpose of its planes, the accumulator's the
running sums of the fractions' (`blockRows_eq`), the rows of a range of blocks are the permutation
trace's with the accumulator from the range's start (`rangeRows_eq`), and shifting it by the sums
before the range gives the permutation trace (`permutationWords_eq`, `permutationLdeWith_rel`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open Montgomery.Native32.Words
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial
open CompPoly.CPolynomial.NTTFast.Packed (LdePlan)

open Montgomery.Native32

variable {p : ℕ} [Mont32Field p] {EF : Type} [FastExt p EF]

local notation "F" => FastField p
local notation "d" => FastExt.d p EF

/-! ### Fractions -/

theorem length_fractionsX [PlanesInv p EF] {β E : Type} (B : Nat) (get : β → E → ByteArray)
    (v : β) (ts : List (List (List E × E))) (chs : List EF) (apl : Array (ExtPlanes p EF)) :
    (fractionsX B get v ts chs apl).length = ts.length := by
  rw [fractionsX, List.length_map, List.length_zipIdx]


theorem ofBase_zero : FastExt.ofBase (E := EF) (0 : F) = 0 :=
  FastExt.toSpec_injective (by
    rw [FastExt.toSpec_ofBase, FastExt.toSpec_zero]
    exact map_zero (CompPoly.Extension.Ext.ofBaseRingHom _))

section Fractions
variable [Mont32BaseField p] [Mont32.AlgebraId EF]

theorem combineX_fold {B : Nat} (hB : 4 * B < USize.size) (b : EF) :
    ∀ (ws : List ByteArray) (vs : List (Nat → F)),
      List.Forall₂ (fun w v ↦ w = encode (tab B v)) ws vs →
      ∀ (acc : XVal p EF) (f : Nat → EF), XRel B acc f →
      XRel B (ws.foldl (fun acc y ↦ (XVal.base y).add B (acc.mul B (.const b))) acc)
        (fun i ↦ (vs.map (· i)).foldl (fun acc y ↦ Ext.ofBase y + acc * b) (f i))
  | [], [], .nil, _, _, h => h
  | w :: ws, v :: vs, .cons hw hs, acc, f, h => by
    rw [List.foldl_cons]
    refine combineX_fold hB b ws vs hs _ _ (XRel.add hB (x := .base w) (f := fun i ↦
      FastExt.ofBase (v i)) ⟨v, hw, fun _ _ ↦ rfl⟩ (XRel.mul hB h (y := .const b)
        (g := fun _ ↦ b) fun _ _ ↦ rfl))

/-- `combineX` is `combine` on every row of the block. -/
theorem combineX_rel {B : Nat} (hB : 4 * B < USize.size) (b : EF) (ws : List ByteArray)
    (vs : List (Nat → F)) (h : List.Forall₂ (fun w v ↦ w = encode (tab B v)) ws vs) :
    XRel B (combineX B b ws) fun i ↦ Lookup.combine b (vs.map (· i)) := by
  cases h with
  | nil => exact fun _ _ ↦ rfl
  | cons hw hs =>
    exact combineX_fold hB b _ _ hs _ _ ⟨_, hw, fun _ _ ↦ rfl⟩

theorem fractionX_fold [PlanesInv p EF] {E : Type} {B : Nat} (hB : 4 * B < USize.size) (ev : E →
    ByteArray)
    (val : E → Nat → F) (a b : EF) (apl : ExtPlanes p EF)
    (hapl : ExtPlanes.Rel apl (tab B fun _ ↦ a)) :
    ∀ xs : List (List E × E),
      (∀ x ∈ xs, (∀ e ∈ x.1, ev e = encode (tab B (val e))) ∧
        ev x.2 = encode (tab B (val x.2))) →
      ∀ (z : ExtPlanes p EF) (S : Nat → EF), ExtPlanes.Rel z (tab B S) →
      ExtPlanes.Rel (xs.foldl (fun s (t, m) ↦
          let den := (XVal.ext apl).sub B (combineX B b (t.map ev))
          s.add ((PlanesInv.inv (den.planes B)).mulBase (ev m))) z)
        (tab B fun i ↦ xs.foldl (fun s (t, m) ↦
          let mv := val m i
          if mv = 0 then s
          else s + Challenge.smul mv (a - Lookup.combine b (t.map (val · i)))⁻¹) (S i))
  | [], _, z, S, hz => hz
  | (t, m) :: xs, hev, z, S, hz => by
    obtain ⟨ht, hm⟩ := hev (t, m) List.mem_cons_self
    simp only [List.foldl_cons]
    refine fractionX_fold hB ev val a b apl hapl xs
      (fun x hx ↦ hev x (List.mem_cons_of_mem _ hx)) _ _ ?_
    have hcomb := combineX_rel hB b (t.map ev) (t.map val)
      (by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact List.forall₂_same.mpr fun e he ↦ ht e he)
    have hden := XRel.sub hB (x := .ext apl) (f := fun _ ↦ a) hapl hcomb
    have hinv := PlanesInv.inv_rel (hden.planes hB) (by rw [size_tab]; exact hB)
    rw [tab_map] at hinv
    have hmb := ExtPlanes.mulBase_rel hB (val m) hinv
    rw [← hm] at hmb
    have hadd := ExtPlanes.add_rel hB hz hmb
    refine hadd.congr_tab fun i _ ↦ ?_
    by_cases h0 : val m i = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), h0, ofBase_zero]
      exact FastExt.toSpec_injective (by
        rw [FastExt.toSpec_add, FastExt.toSpec_mul, FastExt.toSpec_zero, MulZeroClass.mul_zero,
            add_zero])
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), Mont32.smul_eq, FastExt.mul_comm
        (FastExt.ofBase _)]
      simp only [List.map_map]
      rfl

/-- The fraction of the tuples `t` with the values `val`, a tuple of multiplicity `0` adding
nothing (`Lookup.fraction`). -/
def fracOf {E : Type} (val : E → F) (a b : EF) (t : List (List E × E)) : EF :=
  t.foldl (fun s (tv, m) ↦
    let mv := val m
    if mv = 0 then s else s + Challenge.smul mv (a - Lookup.combine b (tv.map val))⁻¹) 0

/-- A lookup's fraction on a block of rows, `ev` its expressions' values there. -/
theorem fractionX_rel [PlanesInv p EF] {E : Type} {B : Nat} (hB : 4 * B < USize.size) (ev : E →
    ByteArray)
    (val : E → Nat → F) (t : List (List E × E)) (a b : EF) (apl : ExtPlanes p EF)
    (hapl : ExtPlanes.Rel apl (tab B fun _ ↦ a))
    (hev : ∀ x ∈ t, (∀ e ∈ x.1, ev e = encode (tab B (val e))) ∧
      ev x.2 = encode (tab B (val x.2))) :
    ExtPlanes.Rel (t.foldl (fun s (t, m) ↦
        let den := (XVal.ext apl).sub B (combineX B b (t.map ev))
        s.add ((PlanesInv.inv (den.planes B)).mulBase (ev m))) (ExtPlanes.zeros B))
      (tab B fun i ↦ fracOf (val · i) a b t) := by
  have hz : ExtPlanes.Rel (ExtPlanes.zeros (p := p) (E := EF) B) (tab B fun _ ↦ 0) := by
    have := ExtPlanes.zeros_rel (p := p) (E := EF) B
    rwa [show Array.replicate B (0 : EF) = tab B fun _ ↦ 0 from by
      apply Array.ext (by simp only [Array.size_replicate, size_tab])
      intro i h1 h2
      simp only [tab, Array.getElem_replicate, Array.getElem_ofFn]] at this
  exact fractionX_fold hB ev val a b apl hapl t hev _ _ hz

/-- Lookup `c`'s fraction planes on a block. -/
theorem fractionsX_getD [PlanesInv p EF] {β E : Type} {B : Nat} (hB : 4 * B < USize.size)
    (get : β → E → ByteArray) (v : β)
    (val : E → Nat → F) (ts : List (List (List E × E))) (chs : List EF)
    (apl : Array (ExtPlanes p EF))
    (hapl : ∀ c < ts.length, ExtPlanes.Rel (apl.getD c (ExtPlanes.zeros B)) (tab B fun _
        ↦ chs.getD (2 * c) 0))
    (hev : ∀ t ∈ ts, ∀ x ∈ t, (∀ e ∈ x.1, get v e = encode (tab B (val e))) ∧
      get v x.2 = encode (tab B (val x.2))) (c : Nat) (hc : c < ts.length) :
    ExtPlanes.Rel ((fractionsX B get v ts chs apl).toArray.getD c (ExtPlanes.zeros B))
      (tab B fun i ↦ fracOf (val · i) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) ts[c]) := by
  have hc' : c < (fractionsX B get v ts chs apl).length := by rw [length_fractionsX]; exact hc
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hc',
    Option.getD_some]
  simp only [fractionsX, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  exact fractionX_rel hB (get v) val ts[c] _ _ _ (hapl c hc) (hev _ (List.getElem_mem hc))

end Fractions

/-! ### Writing the rows -/

theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by rw [List.length_map, List.length_finRange, List.length_range])
    fun i h1 h2 ↦ by rw [List.getElem_map, List.getElem_finRange, List.getElem_range]; rfl

/-- A fold over `Fin n` reading its index's value only is the fold over `0, …, n - 1`. -/
theorem foldl_finRange {α : Type} (n : Nat) (G : α → Fin n → α) (g : α → Nat → α)
    (hG : ∀ a k, G a k = g a k.val) (init : α) :
    (List.finRange n).foldl G init = (List.range n).foldl g init := by
  rw [show G = fun a k ↦ g a k.val from funext fun a ↦ funext fun k ↦ hG a k, ← map_val_finRange,
    List.foldl_map]

theorem write_add (X : Array F) (k : Nat) (c : F) (hk : k < X.size)
    (hs : 4 * X.size < USize.size) :
    NTTFast.Packed.Native.write (encode X) k
        (NTTFast.Packed.add p (NTTFast.Packed.Native.read (encode X) k) c.val) =
      encode (X.setIfInBounds k (X.getD k 0 + c)) := by
  rw [Words.read_encode X k hs hk, NTTFast.Packed.add_val]
  exact NTTFast.Packed.Native.write_encode X k
    (by rw [CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]; omega) hk _

/-! ### Shifting the accumulator -/

theorem ite_of {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  split
  · rfl
  · contradiction

theorem ite_of_not {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  split
  · contradiction
  · rfl

/-- `O` with the accumulator columns of its first `i` rows of `W` words shifted by `s`. -/
def shiftedTo (O : Array F) (W : Nat) (s : EF) (i : Nat) : Array F :=
  Array.ofFn (n := O.size) fun k ↦
    if k.val < i * W ∧ k.val % W < d then O.getD k 0 + coord (k.val % W) s else O.getD k 0

theorem size_shiftedTo (O : Array F) (W : Nat) (s : EF) (i : Nat) :
    (shiftedTo O W s i).size = O.size := Array.size_ofFn

theorem getD_shiftedTo (O : Array F) (W : Nat) (s : EF) (i k : Nat) (hk : k < O.size) :
    (shiftedTo O W s i).getD k 0 =
      if k < i * W ∧ k % W < d then O.getD k 0 + coord (k % W) s else O.getD k 0 := by
  rw [shiftedTo, NTTFast.Packed.getD_ofFn_bounded _ _ hk]

/-- Words `o, …, o + d - 1` shifted by the coordinates of `s`. -/
theorem shiftRow_eq (X : Array F) (o : Nat) (s : EF) (ho : o + d ≤ X.size)
    (hs : 4 * X.size < USize.size) :
    shiftRow (encode X) o s = encode (Array.ofFn (n := X.size) fun j ↦
      if o ≤ j.val ∧ j.val < o + d then X.getD j 0 + coord (j.val - o) s else X.getD j 0) := by
  unfold shiftRow
  rw [foldl_finRange d _ (fun out k ↦ NTTFast.Packed.Native.write out (o + k)
    (NTTFast.Packed.add p (NTTFast.Packed.Native.read out (o + k)) (coord k s).val))
    (fun out k ↦ by rw [coord_fin])]
  suffices h : ∀ m ≤ d, (List.range m).foldl (fun out k ↦ NTTFast.Packed.Native.write out (o + k)
      (NTTFast.Packed.add p (NTTFast.Packed.Native.read out (o + k)) (coord k s).val))
      (encode X) = encode (Array.ofFn (n := X.size) fun j ↦
        if o ≤ j.val ∧ j.val < o + m then X.getD j 0 + coord (j.val - o) s else X.getD j 0) from
    h d le_rfl
  intro m hm
  induction m with
  | zero =>
    rw [List.range_zero, List.foldl_nil]
    congr 1
    apply NTTFast.Packed.array_eq_of_getD _ _ 0 (by rw [Array.size_ofFn])
    intro j
    by_cases hj : j < X.size
    · rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj, ite_of_not (by omega)]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega),
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega)]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      write_add _ (o + m) (coord m s) (by rw [Array.size_ofFn]; omega)
        (by rw [Array.size_ofFn]; exact hs)]
    congr 1
    apply NTTFast.Packed.array_eq_of_getD _ _ 0
      (by rw [Array.size_setIfInBounds, Array.size_ofFn, Array.size_ofFn])
    intro j
    rw [NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by rw [Array.size_ofFn]; omega),
      NTTFast.Packed.getD_ofFn_bounded _ _ (show o + m < X.size by omega)]
    dsimp only
    rw [ite_of_not (show ¬(o ≤ o + m ∧ o + m < o + m) by omega)]
    by_cases hj : j < X.size
    · rw [NTTFast.Packed.getD_ofFn_bounded _ _ hj, NTTFast.Packed.getD_ofFn_bounded _ _ hj]
      dsimp only
      by_cases hjm : j = o + m
      · subst hjm
        rw [ite_of rfl, ite_of (by omega), Nat.add_sub_cancel_left]
      · rw [ite_of_not hjm]
        by_cases hin : o ≤ j ∧ j < o + m
        · rw [ite_of hin, ite_of (by omega)]
        · rw [ite_of_not hin, ite_of_not (by omega)]
    · rw [ite_of_not (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
          rw [Array.size_ofFn]; omega), Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega)]

theorem mod_of_block (m W e : Nat) (he : e < W) : (m * W + e) % W = e := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

/-- Shifting the accumulator columns of `rows` rows. -/
theorem shiftAccumulator_eq (O : Array F) (rows W : Nat) (s : EF) (hW : d ≤ W)
    (hO : rows * W ≤ O.size) (hs : 4 * O.size < USize.size) :
    shiftAccumulator (encode O) rows W s = encode (shiftedTo O W s rows) := by
  unfold shiftAccumulator
  suffices h : ∀ m ≤ rows, (List.range m).foldl (fun out i ↦ shiftRow out (i * W) s)
      (encode O) = encode (shiftedTo O W s m) from h rows le_rfl
  intro m hm
  induction m with
  | zero =>
    rw [List.range_zero, List.foldl_nil]
    congr 1
    apply NTTFast.Packed.array_eq_of_getD _ _ 0 (by rw [size_shiftedTo])
    intro k
    by_cases hk : k < O.size
    · rw [getD_shiftedTo _ _ _ _ _ hk, Nat.zero_mul, ite_of_not (by omega)]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega),
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_shiftedTo]; omega)]
  | succ m ih =>
    have hmW : (m + 1) * W ≤ O.size := le_trans (Nat.mul_le_mul_right W hm) hO
    have hmw : m * W + d ≤ O.size := by rw [Nat.succ_mul] at hmW; omega
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      shiftRow_eq _ _ _ (by rw [size_shiftedTo]; exact hmw) (by rw [size_shiftedTo]; exact hs)]
    congr 1
    apply NTTFast.Packed.array_eq_of_getD _ _ 0 (by rw [Array.size_ofFn, size_shiftedTo,
      size_shiftedTo])
    intro k
    by_cases hk : k < O.size
    · rw [NTTFast.Packed.getD_ofFn_bounded _ _ (by rw [size_shiftedTo]; exact hk),
        getD_shiftedTo O W s (m + 1) k hk, getD_shiftedTo O W s m k hk]
      by_cases hin : m * W ≤ k ∧ k < m * W + d
      · have hmod : k % W = k - m * W := by
          have e : k = (k - m * W) + m * W := by omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
          omega
        rw [ite_of hin, ite_of_not (show ¬(k < m * W ∧ k % W < d) by omega),
          ite_of (show k < (m + 1) * W ∧ k % W < d by rw [Nat.succ_mul]; omega), hmod]
      · rw [ite_of_not hin]
        by_cases hlt : k < m * W
        · have hlt' : k < (m + 1) * W := by rw [Nat.succ_mul]; omega
          simp only [hlt, hlt', true_and]
        · have hcond : ¬(k < (m + 1) * W ∧ k % W < d) := by
            rintro ⟨hk1, hk2⟩
            have e : k = (k - m * W) + m * W := by omega
            have hlt2 : k - m * W < W := by rw [Nat.succ_mul] at hk1; omega
            have hmod : k % W = k - m * W := by
              rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
              omega
            omega
          rw [ite_of_not hcond, ite_of_not (by omega)]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
          rw [Array.size_ofFn, size_shiftedTo]; omega),
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_shiftedTo]; omega)]

/-! ### The specification's permutation trace in closed form -/


/-- The accumulator before row `i`: every earlier row's fractions summed in order. -/
def specAcc (frs : Nat → List EF) (i : Nat) : EF :=
  (List.range i).foldl (fun acc r ↦ (frs r).foldl (· + ·) acc) 0

/-- Entry `k` of the permutation trace of `L` lookups with the rows' fractions `frs`. -/
def specEntry (frs : Nat → List EF) (L k : Nat) : EF :=
  if k % (L + 1) = 0 then specAcc frs (k / (L + 1))
  else (frs (k / (L + 1))).getD (k % (L + 1) - 1) 0

theorem permutationTrace_eq [Mont32BaseField p] [Mont32.AlgebraId EF] (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (t : Array F)
    (pis : List F) (chs : List EF) :
    Lookup.permutationTrace A ls logN t pis chs =
      (tab (2 ^ logN * (ls.length + 1))
        (specEntry (Lookup.rowFractions A ls logN t pis chs) ls.length),
        specAcc (Lookup.rowFractions A ls logN t pis chs) (2 ^ logN)) := by
  unfold Lookup.permutationTrace
  generalize hfrs : Lookup.rowFractions A ls logN t pis chs = frs
  have hlen : ∀ i, (frs i).length = ls.length := fun i ↦ by
    rw [← hfrs, Lookup.rowFractions, List.length_map, List.length_zipIdx]
  suffices h : ∀ m, (List.range m).foldl (fun (out, acc) i ↦
      ((out.push acc) ++ (frs i).toArray, (frs i).foldl (· + ·) acc)) (#[], 0) =
      (tab (m * (ls.length + 1)) (specEntry frs ls.length), specAcc frs m) from h _
  intro m
  induction m with
  | zero =>
    rw [List.range_zero, List.foldl_nil]
    refine Prod.ext ?_ rfl
    exact (Array.eq_empty_of_size_eq_zero (by rw [size_tab, Nat.zero_mul])).symm
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    dsimp only
    refine Prod.ext ?_ ?_
    · apply Array.ext (by
        simp only [Array.size_append, Array.size_push, size_tab, List.size_toArray, hlen]
        ring)
      intro k h1 h2
      rw [size_tab] at h2
      have hk' : k / (ls.length + 1) ≤ m := by
        apply Nat.lt_succ_iff.mp
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
      rw [getElem_tab]
      by_cases hlt : k < m * (ls.length + 1)
      · rw [Array.getElem_append_left (by rw [Array.size_push, size_tab]; omega),
          Array.getElem_push_lt (by rw [size_tab]; exact hlt), getElem_tab]
      · have hq : k / (ls.length + 1) = m := by
          apply Nat.le_antisymm hk'
          exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
        by_cases heq : k = m * (ls.length + 1)
        · subst heq
          rw [Array.getElem_append_left (by rw [Array.size_push, size_tab]; omega)]
          rw [Array.getElem_push, dite_eq_right_iff.mpr fun h ↦ absurd h (by rw [size_tab]; omega)]
          simp only [specEntry, Nat.mul_mod_left, ite_true,
            Nat.mul_div_cancel _ (Nat.succ_pos _)]
        · rw [Array.getElem_append_right (by rw [Array.size_push, size_tab]; omega)]
          simp only [List.getElem_toArray, Array.size_push, size_tab]
          have hr : k % (ls.length + 1) = k - m * (ls.length + 1) := by
            rw [Nat.mod_def, hq, Nat.mul_comm]
          have hr0 : k % (ls.length + 1) ≠ 0 := by omega
          have h2' : k < m * (ls.length + 1) + (ls.length + 1) := by
            rw [Nat.succ_mul] at h2; exact h2
          simp only [specEntry, hr0, ite_false, hq]
          rw [hr, List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
          simp only [Nat.sub_sub]
    · show (frs m).foldl (· + ·) (specAcc frs m) = specAcc frs (m + 1)
      rw [specAcc, specAcc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]


theorem tab_succ {α : Type} (N : Nat) (g : Nat → α) : tab (N + 1) g = (tab N g).push (g N) := by
  apply Array.ext (by rw [Array.size_push, size_tab, size_tab])
  intro k h1 h2
  rw [getElem_tab, Array.getElem_push]
  split
  · rw [getElem_tab]
  · rw [size_tab] at h1; rw [size_tab] at *; congr 1; omega

/-- A tabulated array of extension elements in base coordinates. -/
theorem flatten_tab [Mont32BaseField p] [Mont32.AlgebraId EF] (N : Nat) (g : Nat → EF) :
    Lookup.flatten (tab N g) = tab (N * d) fun idx ↦ coord (idx % d) (g (idx / d)) := by
  rw [Lookup.flatten, tab, flatMap_coeffs]
  exact ofFn_len (fun idx ↦ coord (idx % d) (g (idx / d))) (Nat.mul_comm _ _)


theorem ext_add_assoc (a b c : EF) : a + b + c = a + (b + c) :=
  FastExt.toSpec_injective (by simp only [FastExt.toSpec_add, add_assoc])

theorem ext_add_zero (a : EF) : a + 0 = a :=
  FastExt.toSpec_injective (by rw [FastExt.toSpec_add, FastExt.toSpec_zero, add_zero])

theorem foldl_add_shift (s : EF) : ∀ (xs : List EF) (a : EF),
    xs.foldl (· + ·) (s + a) = s + xs.foldl (· + ·) a
  | [], _ => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, List.foldl_cons, ext_add_assoc, foldl_add_shift s xs]

/-! ### A range of blocks -/

/-- The accumulator `i` rows into a range of rows from row `R0`, from `0`. -/
def localAcc (frs : Nat → List EF) (R0 i : Nat) : EF :=
  (List.range i).foldl (fun acc r ↦ (frs (R0 + r)).foldl (· + ·) acc) 0

/-- Word `j` of a range of rows from row `R0`, `W` words per row, with the accumulator from `0`. -/
def rangeVal (frs : Nat → List EF) (R0 W j : Nat) : F :=
  if j % W < d then coord (j % W) (localAcc frs R0 (j / W))
  else coord (j % W % d) ((frs (R0 + j / W)).getD (j % W / d - 1) 0)

theorem localAcc_succ (frs : Nat → List EF) (R0 i : Nat) :
    localAcc frs R0 (i + 1) = (frs (R0 + i)).foldl (· + ·) (localAcc frs R0 i) := by
  rw [localAcc, localAcc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem accWords_eq (a : EF) :
    accWords a = encode (Array.ofFn fun k : Fin d ↦ FastExt.coord a k) :=
  NTTFast.Packed.Native.encodeFields_eq _

theorem read_accWords (hd : 4 * d < USize.size) (a : EF) (k : Fin d) :
    NTTFast.Packed.Native.read (accWords a) k = (FastExt.coord a k).val := by
  rw [accWords_eq, Words.read_encode _ _ (by rw [Array.size_ofFn]; exact hd)
      (by rw [Array.size_ofFn]; exact k.isLt),
    NTTFast.Packed.getD_ofFn_bounded _ _ k.isLt]

/-- Running sums of the words of `s` from word `k` on, `rem` of them. -/
theorem scanWords_eq {B : Nat} (hB : 4 * B < USize.size) (g h : Nat → F)
    (hg : ∀ i < B, g (i + 1) = g i + h i) :
    ∀ rem k, k + rem ≤ B → scanWords (p := p) (encode (tab B h))
      (encode (Words.upto (Array.replicate B 0) g k)) (g k).val k rem =
      (encode (Words.upto (Array.replicate B 0) g (k + rem)), (g (k + rem)).val) := by
  intro rem
  induction rem with
  | zero => intro k _; rfl
  | succ rem ih =>
    intro k hk
    rw [scanWords, Words.write_upto _ g k (by rw [Array.size_replicate]; omega)
      (by rw [Array.size_replicate]; omega), read_tab hB h k (by omega),
      NTTFast.Packed.add_val, ← hg k (by omega), ih (k + 1) (by omega), Nat.add_right_comm,
      Nat.add_assoc]

/-- The sum of the first `m` planes of `fs`. -/
theorem foldl_add_rel {B : Nat} (hB : 4 * B < USize.size) (fs : Array (ExtPlanes p EF))
    (rf : Nat → List EF) (hfs : ∀ c (hc : c < fs.size), ExtPlanes.Rel fs[c]
      (tab B fun i ↦ (rf i).getD c 0)) :
    ∀ m ≤ fs.size, ExtPlanes.Rel ((fs.toList.take m).foldl (fun a f ↦ a.add f) (ExtPlanes.zeros B))
      (tab B fun i ↦ ((rf i).take m).foldl (· + ·) 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    have := ExtPlanes.zeros_rel (E := EF) (p := p) B
    simp only [List.take_zero, List.foldl_nil]
    refine RV_congr this (Array.ext (by rw [Array.size_replicate, size_tab]) fun i h1 _ ↦ ?_)
    rw [Array.getElem_replicate, getElem_tab]
  | succ m ih =>
    intro hm
    have hm' : m < fs.size := by omega
    rw [List.take_succ_eq_append_getElem (by simpa using hm'), List.foldl_append, List.foldl_cons,
      List.foldl_nil, Array.getElem_toList]
    refine RV_congr (ExtPlanes.add_rel hB (ih (by omega)) (hfs m hm'))
      (congrArg (tab B) (funext fun i ↦ ?_))
    by_cases hmi : m < (rf i).length
    · rw [List.take_succ_eq_append_getElem hmi, List.foldl_append, List.foldl_cons,
        List.foldl_nil, List.getD_eq_getElem _ _ hmi]
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.getD_eq_default _ _ (by omega), ext_add_zero]

/-- **A block of rows**: the accumulators `accs` before every row from `acc`, then the row's
fractions `rf i`, one per plane vector of `fs`, as packed rows of `W = (L + 1) d` words; and the
accumulator after the block. -/
theorem blockRows_eq (fs : Array (ExtPlanes p EF)) (acc : EF) (B W : Nat) (rf : Nat → List EF)
    (accs : Nat → EF) (hW : W = (fs.size + 1) * d) (hB : 4 * B < USize.size)
    (hdu : 4 * d < USize.size) (hBW : 4 * (B * W) < USize.size) (hrows : B < 512 ∨ 512 ∣ B)
    (hfs : ∀ c (hc : c < fs.size), ExtPlanes.Rel fs[c] (tab B fun i ↦ (rf i).getD c 0))
    (hlen : ∀ i, (rf i).length = fs.size) (hacc0 : accs 0 = acc)
    (hstep : ∀ i < B, accs (i + 1) = (rf i).foldl (· + ·) (accs i)) :
    blockRows fs acc B = (encode (tab (B * W) fun j ↦
      if j % W < d then coord (j % W) (accs (j / W))
      else coord (j % W % d) ((rf (j / W)).getD (j % W / d - 1) 0)), accs B) := by
  have hd : 0 < d := (FastExt.params (p := p) (E := EF)).d_pos
  let Sm (i : Nat) : EF := (rf i).foldl (· + ·) 0
  have hS : ExtPlanes.Rel (fs.foldl (fun a f ↦ a.add f) (ExtPlanes.zeros B)) (tab B Sm) := by
    have := foldl_add_rel hB fs rf hfs fs.size le_rfl
    rw [List.take_of_length_le (by simp), Array.foldl_toList] at this
    exact RV_congr this (congrArg (tab B) (funext fun i ↦ by
      rw [List.take_of_length_le (by rw [hlen])]))
  obtain ⟨-, hSc⟩ := ExtPlanes.rel_tab_iff.mp hS
  have hsplit (i : Nat) (hi : i < B) : accs (i + 1) = accs i + Sm i := by
    rw [hstep i hi, show (rf i).foldl (· + ·) (accs i) = (rf i).foldl (· + ·) (accs i + 0) by
      rw [ext_add_zero], foldl_add_shift]
  -- The accumulator's planes.
  have hscan (k : Nat) (hk : k < d) :
      (((Array.range d).map fun k ↦ scanWords (p := p)
        ((fs.foldl (fun a f ↦ a.add f) (ExtPlanes.zeros B)).c.toArray.getD k .empty)
        (NTTFast.Packed.Native.zeroWords B) (NTTFast.Packed.Native.read (accWords acc) k) 0 B).getD
        k (.empty, 0)) = (encode (tab B fun i ↦ coord k (accs i)), (coord k (accs B)).val) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
      ite_eq_left_of_eq_true _ _ (eq_true hk), Option.map_some, Option.getD_some]
    let g (i : Nat) : F := coord k (accs i)
    have hc : (fs.foldl (fun a f ↦ a.add f) (ExtPlanes.zeros B)).c.toArray.getD k .empty =
        encode (tab B fun i ↦ FastExt.coord (Sm i) ⟨k, hk⟩) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
        Option.getD_some, Vector.getElem_toArray]
      exact hSc ⟨k, hk⟩
    rw [hc, zeroWords_eq (p := p), ← Words.upto_zero (Array.replicate B (0 : F)) g,
      show NTTFast.Packed.Native.read (accWords acc) k = (g 0).val by
        rw [show k = ((⟨k, hk⟩ : Fin d) : Nat) from rfl, read_accWords hdu, ← hacc0, ← coord_fin],
      scanWords_eq hB g _ (fun i hi ↦ by
        simp only [g]
        rw [hsplit i hi]
        simp only [coord, hk, dite_true, FastExt.coord_add, Pi.add_apply]) B 0 (by omega),
      Nat.zero_add, Words.upto_full _ _ _ (Array.size_replicate ..)]
    rfl
  -- The columns: the accumulator's planes, then every lookup's.
  let val (q i : Nat) : F :=
    if q < d then coord q (accs i) else coord ((q - d) % d) ((rf i).getD ((q - d) / d) 0)
  let Cw : Array (Array UInt32) := Array.ofFn (n := W) fun q ↦ (tab B (val q.val)).map Subtype.val
  have hCw : Cw.size = W := Array.size_ofFn
  unfold blockRows
  dsimp only
  have hcols : (Array.ofFn (n := (fs.size + 1) * d) fun q ↦
      if q.val < d then (((Array.range d).map fun k ↦ scanWords (p := p)
        ((fs.foldl (fun a f ↦ a.add f) (ExtPlanes.zeros B)).c.toArray.getD k .empty)
        (NTTFast.Packed.Native.zeroWords B) (NTTFast.Packed.Native.read (accWords acc) k) 0 B).getD
        q.val (.empty, 0)).1
      else ((fs.getD ((q.val - d) / d) (ExtPlanes.zeros 0)).c.toArray.getD ((q.val - d) % d)
        .empty)) = Cw.map encode := by
    apply Array.ext (by rw [Array.size_ofFn, Array.size_map, hCw, hW])
    intro q h1 h2
    rw [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, Array.getElem_map, Array.getElem_ofFn,
      ← NTTFast.Packed.encode_eq_map_val]
    dsimp only
    by_cases hq : q < d
    · rw [if_pos hq, hscan q hq]
      exact congrArg encode (congrArg (tab B) (funext fun i ↦ by simp only [val, hq, ite_true]))
    · rw [if_neg hq]
      have hc : (q - d) / d < fs.size := by
        have : q - d < fs.size * d := by
          have := h1; rw [Nat.add_mul, Nat.one_mul] at this; omega
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact this)
      have hk : (q - d) % d < d := Nat.mod_lt _ hd
      have hget : (fs.getD ((q - d) / d) (ExtPlanes.zeros 0)).c.toArray.getD ((q - d) % d)
          .empty = fs[(q - d) / d].c[(⟨(q - d) % d, hk⟩ : Fin d)] := by
        rw [show fs.getD ((q - d) / d) (ExtPlanes.zeros 0) = fs[(q - d) / d] by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc, Option.getD_some]]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
          Option.getD_some, Vector.getElem_toArray]
        rfl
      rw [hget, (ExtPlanes.rel_tab_iff.mp (hfs _ hc)).2 ⟨(q - d) % d, hk⟩]
      exact congrArg encode (congrArg (tab B) (funext fun i ↦ by
        simp only [val, hq, ite_false, coord, hk, dite_true]))
  rw [hcols]
  have hW0 : 0 < W := by rw [hW]; exact Nat.mul_pos (Nat.succ_pos _) hd
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [NTTFast.Packed.Native.rowsOfColumns_encodeWords Cw 0 B (fun j hj ↦ by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some,
          Array.getElem_ofFn, Array.size_map, size_tab]
        refine ⟨by omega, by omega⟩) (by rw [hCw]; exact hBW) hrows,
      NTTFast.Packed.encode_eq_map_val (tab (B * W) _)]
    refine congrArg encode (Array.ext (by rw [Array.size_ofFn, Array.size_map, size_tab, hCw])
      fun k h1 _ ↦ ?_)
    rw [Array.size_ofFn, hCw] at h1
    have hkW : k % W < W := Nat.mod_lt _ hW0
    have hkB : k / W < B := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
    rw [Array.getElem_ofFn, Array.getElem_map, getElem_tab]
    dsimp only
    have hcol : Cw.getD (k % W) #[] = (tab B (val (k % W))).map Subtype.val := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hCw]; exact hkW),
        Option.getD_some, Array.getElem_ofFn]
    rw [hCw, Nat.zero_add, hcol, NTTFast.Packed.getD_map_val, getD_tab _ _ _ hkB]
    simp only [val]
    by_cases hq : k % W < d
    · simp only [hq, ite_true]
    · simp only [hq, ite_false]
      have hle : d ≤ k % W := Nat.le_of_not_lt hq
      generalize k % W = q at hle ⊢
      obtain ⟨t, rfl⟩ : ∃ t, q = d + t := ⟨q - d, by omega⟩
      rw [Nat.add_sub_cancel_left, Nat.add_mod_left, Nat.add_div_left _ hd, Nat.add_sub_cancel]
  · apply FastExt.ext
    intro k
    dsimp only
    rw [FastExt.coord_ofCoords, hscan k k.isLt, NTTFast.Packed.ofWord_val, coord_fin]

/-- **A range of blocks**: its rows of the permutation trace, the accumulator from `0`, and the
sum of their fractions. -/
theorem rangeRows_eq [Mont32BaseField p] [Mont32.AlgebraId EF] [PlanesInv p EF] {β E : Type}
    (blk : Nat → β)
    (get : β → E → ByteArray)
    (ts : List (List (List E × E)))
    (chs : List EF) (B W b0 nb : Nat) (val : E → Nat → F) (frs : Nat → List EF)
    (hW : W = (ts.length + 1) * d) (hB : 4 * B < USize.size) (hdU : 4 * d < USize.size)
    (hrows : B < 512 ∨ 512 ∣ B)
    (hsz : 4 * (nb * B * W) < USize.size)
    (hfrs : ∀ r, frs r = ts.zipIdx.map fun (t, c) ↦
      fracOf (val · r) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) t)
    (hev : ∀ j < nb, ∀ t ∈ ts, ∀ x ∈ t,
      (∀ e ∈ x.1,
        get (blk ((b0 + j) * B)) e = encode (tab B fun i ↦ val e ((b0 + j) * B + i))) ∧
      get (blk ((b0 + j) * B)) x.2 = encode (tab B fun i ↦ val x.2 ((b0 + j) * B + i))) :
    rangeRows blk get ts chs B W b0 nb =
      (encode (tab (nb * B * W) (rangeVal frs (b0 * B) W)), localAcc frs (b0 * B) (nb * B)) := by
  unfold rangeRows
  dsimp only
  have hd : 0 < d := (FastExt.params (p := p) (E := EF)).d_pos
  have hapl : ∀ c < ts.length, ExtPlanes.Rel
      (((Array.range ts.length).map fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B).getD c
        (ExtPlanes.zeros B)) (tab B fun _ ↦ chs.getD (2 * c) 0) := by
    intro c hc
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hc, ite_true, Option.map_some, Option.getD_some]
    exact XRel.planes hB (x := .const _) (fun _ _ ↦ rfl)
  generalize (Array.range ts.length).map (fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B) =
    apl at hapl
  have hlen (r : Nat) : (frs r).length = ts.length := by
    rw [hfrs, List.length_map, List.length_zipIdx]
  suffices h : ∀ m ≤ nb, (List.range m).foldl (fun st j ↦
      ((st.1 ++ (blockRows (fractionsX B get (blk ((b0 + j) * B)) ts chs apl).toArray st.2 B).1),
        (blockRows (fractionsX B get (blk ((b0 + j) * B)) ts chs apl).toArray st.2 B).2))
      (ByteArray.emptyWithCapacity (4 * (nb * B * W)), 0) =
      (encode (tab (m * B * W) (rangeVal frs (b0 * B) W)), localAcc frs (b0 * B) (m * B)) from
    h nb le_rfl
  intro m hm
  induction m with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.zero_mul]
    refine Prod.ext ?_ rfl
    show ByteArray.emptyWithCapacity (4 * (nb * B * W)) = encode (tab 0 (rangeVal frs (b0 * B) W))
    rw [show tab 0 (rangeVal frs (b0 * B) W) = #[] from
      Array.eq_empty_of_size_eq_zero (by rw [size_tab]), CompPoly.PackedRepr.encode_empty]
    rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    dsimp only
    let fs := (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).toArray
    have hsize : fs.size = ts.length := by rw [List.size_toArray, length_fractionsX]
    let rf (i : Nat) : List EF := frs ((b0 + m) * B + i)
    have hfs (c : Nat) (hc : c < fs.size) :
        ExtPlanes.Rel fs[c] (tab B fun i ↦ (rf i).getD c 0) := by
      rw [hsize] at hc
      have := fractionsX_getD hB get (blk ((b0 + m) * B))
        (fun e i ↦ val e ((b0 + m) * B + i)) ts chs apl hapl (hev m (by omega)) c hc
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsize]; exact hc),
        Option.getD_some] at this
      refine RV_congr this (congrArg (tab B) (funext fun i ↦ ?_))
      show _ = (frs ((b0 + m) * B + i)).getD c 0
      conv_rhs => rw [hfrs, List.getD_eq_getElem _ _ (by
        rw [List.length_map, List.length_zipIdx]; exact hc), List.getElem_map, List.getElem_zipIdx]
      simp only [Nat.zero_add]
    have hBW : 4 * (B * W) < USize.size := by
      have : B * W ≤ nb * B * W := by
        rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left (B * W) (by omega)
      omega
    rw [blockRows_eq fs (localAcc frs (b0 * B) (m * B)) B W rf
      (fun i ↦ localAcc frs (b0 * B) (m * B + i)) (by rw [hsize, hW]) hB hdU hBW hrows hfs
      (fun i ↦ by rw [hlen, hsize]) rfl (fun i _ ↦ by
        rw [show m * B + (i + 1) = (m * B + i) + 1 by omega, localAcc_succ,
          show b0 * B + (m * B + i) = (b0 + m) * B + i by ring])]
    refine Prod.ext ?_ (by rw [show (m + 1) * B = m * B + B by ring])
    dsimp only
    rw [← CompPoly.PackedRepr.encode_append]
    refine congrArg encode (Array.ext (by
      simp only [Array.size_append, size_tab]; ring) fun j h1 h2 ↦ ?_)
    simp only [Array.size_append, size_tab] at h1 h2
    rw [getElem_tab]
    by_cases hj : j < m * B * W
    · rw [Array.getElem_append_left (by rw [size_tab]; exact hj), getElem_tab]
    · rw [Array.getElem_append_right (by rw [size_tab]; omega), getElem_tab]
      simp only [size_tab]
      have hWpos : 0 < W := by rw [hW]; exact Nat.mul_pos (Nat.succ_pos _) hd
      obtain ⟨t, rfl⟩ : ∃ t, j = m * B * W + t := ⟨j - m * B * W, by omega⟩
      rw [Nat.add_sub_cancel_left]
      have e1 : (m * B * W + t) % W = t % W := by
        rw [show m * B * W = (m * B) * W from rfl, Nat.add_comm, Nat.add_mul_mod_self_right]
      have e2 : (m * B * W + t) / W = m * B + t / W := by
        rw [show m * B * W = (m * B) * W from rfl, Nat.add_comm, Nat.add_mul_div_right _ _ hWpos,
          Nat.add_comm]
      simp only [rangeVal, e1, e2, rf]
      rw [show b0 * B + (m * B + t / W) = (b0 + m) * B + t / W by ring]

/-! ### The whole permutation trace -/

/-- The accumulator before row `R0 + i` is the one before row `R0` plus the range's. -/
theorem specAcc_add (frs : Nat → List EF) (R0 i : Nat) :
    specAcc frs (R0 + i) = specAcc frs R0 + localAcc frs R0 i := by
  unfold specAcc localAcc
  rw [List.range_add, List.foldl_append, List.foldl_map]
  generalize (List.range R0).foldl (fun acc r ↦ (frs r).foldl (· + ·) acc) 0 = s
  suffices h : ∀ (l : List Nat) (a : EF), l.foldl (fun acc r ↦ (frs (R0 + r)).foldl (· + ·) acc)
      (s + a) = s + l.foldl (fun acc r ↦ (frs (R0 + r)).foldl (· + ·) acc) a by
    rw [← h, ext_add_zero]
  intro l
  induction l with
  | nil => intro a; rfl
  | cons r l ih => intro a; rw [List.foldl_cons, List.foldl_cons, foldl_add_shift, ih]

/-- The generation's shape of `2 ^ logN` rows: pieces of `2 ^ e` rows, blocks of `B` rows, and
tasks dividing the blocks. -/
theorem genShape (logN : Nat) : ∃ e, 2 ^ logN / (if 2 ^ logN < 4096 then 1 else 16) = 2 ^ e ∧
    (if 2 ^ logN < 4096 then 1 else 16) * 2 ^ e = 2 ^ logN ∧
    min (2 ^ e) 1024 ∣ 2 ^ e ∧ 0 < min (2 ^ e) 1024 ∧
    2 ^ logN / min (2 ^ e) 1024 * min (2 ^ e) 1024 = 2 ^ logN ∧
    (if 2 ^ logN / min (2 ^ e) 1024 < 16 then 1 else 16) ∣ 2 ^ logN / min (2 ^ e) 1024 ∧
    (min (2 ^ e) 1024 < 512 ∨ 512 ∣ min (2 ^ e) 1024) := by
  have hpow : ∃ e, 2 ^ logN / (if 2 ^ logN < 4096 then 1 else 16) = 2 ^ e ∧
      (if 2 ^ logN < 4096 then 1 else 16) * 2 ^ e = 2 ^ logN := by
    split
    · exact ⟨logN, Nat.div_one _, Nat.one_mul _⟩
    · rename_i hge
      have h12 : 12 ≤ logN := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega : logN < 12))
          (le_refl _))
      have h16 : 2 ^ logN = 16 * 2 ^ (logN - 4) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]
        congr 1
        omega
      refine ⟨logN - 4, ?_, h16.symm⟩
      rw [h16, Nat.mul_div_cancel_left _ (by decide)]
  obtain ⟨e, h1, h2⟩ := hpow
  refine ⟨e, h1, h2, ?_⟩
  -- `B = 2 ^ b` for `b = min e 10`.
  have hB : min (2 ^ e) 1024 = 2 ^ (min e 10) := by
    rcases Nat.le_total e 10 with h | h
    · rw [Nat.min_eq_left h, Nat.min_eq_left (le_trans (Nat.pow_le_pow_right (by decide) h)
        (le_refl (2 ^ 10)))]
    · rw [Nat.min_eq_right h, Nat.min_eq_right (le_trans (le_refl (2 ^ 10))
        (Nat.pow_le_pow_right (by decide) h))]
  rw [hB]
  have hle : min e 10 ≤ logN := by
    have : 2 ^ e ≤ 2 ^ logN := by rw [← h2]; exact Nat.le_mul_of_pos_left _ (by split <;> omega)
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp this
    omega
  have hdiv : 2 ^ logN / 2 ^ (min e 10) = 2 ^ (logN - min e 10) := Nat.pow_div hle (by decide)
  refine ⟨Nat.pow_dvd_pow 2 (Nat.min_le_left e 10), Nat.two_pow_pos _, ?_, ?_, ?_⟩
  · rw [hdiv, ← Nat.pow_add]; congr 1; omega
  · rw [hdiv]
    split
    · exact Nat.one_dvd _
    · rename_i hge
      have h4 : 4 ≤ logN - min e 10 := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega :
          logN - min e 10 < 4)) (le_refl _))
      exact (Nat.pow_dvd_pow 2 h4 : 2 ^ 4 ∣ _)
  · rcases Nat.lt_or_ge (min e 10) 9 with h9 | h9
    · left
      exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) h9) (le_refl _)
    · right
      exact (Nat.pow_dvd_pow 2 h9 : 2 ^ 9 ∣ _)

/-- Word `R0 W + j` of rows of `W = d (L + 1)` words: entry `(R0 + j / W, j % W / d)` of the
trace, coordinate `j % W % d`. -/
theorem idx_decomp (L R0 j : Nat) :
    (R0 * ((L + 1) * d) + j) / d / (L + 1) = R0 + j / ((L + 1) * d) ∧
    (R0 * ((L + 1) * d) + j) / d % (L + 1) = j % ((L + 1) * d) / d ∧
    (R0 * ((L + 1) * d) + j) % d = j % ((L + 1) * d) % d := by
  have hd : 0 < d := (FastExt.params (p := p) (E := EF)).d_pos
  have hW : 0 < (L + 1) * d := Nat.mul_pos (Nat.succ_pos L) hd
  have hj := Nat.div_add_mod j ((L + 1) * d)
  have hr := Nat.mod_lt j hW
  generalize j / ((L + 1) * d) = q at hj
  generalize j % ((L + 1) * d) = r at hj hr
  subst hj
  have e1 : R0 * ((L + 1) * d) + ((L + 1) * d * q + r) = r + (R0 + q) * (L + 1) * d := by ring
  have hr4 : r / d < L + 1 := (Nat.div_lt_iff_lt_mul hd).mpr hr
  rw [e1, Nat.add_mul_div_right _ _ hd, Nat.add_mul_div_right _ _ (Nat.succ_pos L),
    Nat.div_eq_of_lt hr4, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr4,
    Nat.add_mul_mod_self_right]
  exact ⟨rfl, rfl, rfl⟩

/-- Consecutive tabulated ranges of `S` values. -/
theorem foldl_tab_ranges {α : Type} (g : Nat → α) (S : Nat) : ∀ K : Nat,
    (List.range K).foldl (fun acc k ↦ acc ++ tab S fun j ↦ g (k * S + j)) #[] = tab (K * S) g
  | 0 => (Array.eq_empty_of_size_eq_zero (by rw [size_tab, Nat.zero_mul])).symm
  | K + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_tab_ranges g S K, List.foldl_cons,
      List.foldl_nil]
    have := Words.ofFn_append g (K * S) S
    rw [show K * S + S = (K + 1) * S by ring] at this
    exact this

/-- The words of the permutation trace with entries `specEntry frs L`. -/
abbrev specWord (frs : Nat → List EF) (L idx : Nat) : F :=
  coord (idx % d) (specEntry frs L (idx / d))

/-- A range's rows shifted by the accumulator before it are the permutation trace's. -/
theorem shifted_rangeVal (frs : Nat → List EF) (L R0 rows : Nat) :
    shiftedTo (tab (rows * ((L + 1) * d)) (rangeVal frs R0 ((L + 1) * d))) ((L + 1) * d)
        (specAcc frs R0) rows =
      tab (rows * ((L + 1) * d)) fun j ↦ specWord frs L (R0 * ((L + 1) * d) + j) := by
  apply NTTFast.Packed.array_eq_of_getD _ _ 0 (by rw [size_shiftedTo, size_tab, size_tab])
  intro j
  by_cases hj : j < rows * ((L + 1) * d)
  · rw [getD_shiftedTo _ _ _ _ _ (by rw [size_tab]; exact hj), getD_tab _ _ _ hj,
      getD_tab _ _ _ hj]
    obtain ⟨h1, h2, h3⟩ := idx_decomp (EF := EF) L R0 j
    simp only [specWord, specEntry, h1, h2, h3, rangeVal]
    by_cases hc : j % ((L + 1) * d) < d
    · have h0 : j % ((L + 1) * d) / d = 0 := Nat.div_eq_of_lt hc
      have h4 : j % ((L + 1) * d) % d = j % ((L + 1) * d) := Nat.mod_eq_of_lt hc
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hj, hc⟩), ite_eq_left_of_eq_true _ _ (eq_true hc),
        ite_eq_left_of_eq_true _ _ (eq_true h0), h4, specAcc_add, coord_add, add_comm]
    · have hd : 0 < d := (FastExt.params (p := p) (E := EF)).d_pos
      have h0 : j % ((L + 1) * d) / d ≠ 0 := by
        intro h0
        have := Nat.div_add_mod (j % ((L + 1) * d)) d
        rw [h0, Nat.mul_zero, Nat.zero_add] at this
        have := Nat.mod_lt (j % ((L + 1) * d)) hd
        omega
      rw [ite_of_not (fun h ↦ hc h.2), ite_of_not hc, ite_of_not h0]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [size_shiftedTo, size_tab]; omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [size_tab]; omega)]

/-- **The parallel ranges of blocks** give the permutation trace's words and its terminal. -/
theorem assembleRanges_eq [Mont32BaseField p] [Mont32.AlgebraId EF] [PlanesInv p EF] {β E : Type}
    (blk : Nat → β) (get : β → E → ByteArray) (ts : List (List (List E × E)))
    (chs : List EF) (B blocks : Nat) (val : E → Nat → F) (frs : Nat → List EF)
    (hB : 4 * B < USize.size) (hd : 4 * d < USize.size) (hrows : B < 512 ∨ 512 ∣ B)
    (hsz : 4 * (blocks * B * ((ts.length + 1) * d)) < USize.size)
    (hdiv : (if blocks < 16 then 1 else 16) ∣ blocks)
    (hfrs : ∀ r, frs r = ts.zipIdx.map fun (t, c) ↦
      fracOf (val · r) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) t)
    (hev : ∀ j < blocks, ∀ t ∈ ts, ∀ x ∈ t,
      (∀ e ∈ x.1, get (blk (j * B)) e = encode (tab B fun i ↦ val e (j * B + i))) ∧
      get (blk (j * B)) x.2 = encode (tab B fun i ↦ val x.2 (j * B + i))) :
    assembleRanges blk get ts chs B ((ts.length + 1) * d) blocks =
      (encode (tab (blocks * B * ((ts.length + 1) * d)) (specWord frs ts.length)),
        specAcc frs (blocks * B)) := by
  unfold assembleRanges
  dsimp only
  have htpos : 0 < (if blocks < 16 then 1 else 16) := by split <;> omega
  generalize (if blocks < 16 then 1 else 16) = tasks at hdiv htpos ⊢
  generalize hW : (ts.length + 1) * d = W at hsz ⊢
  obtain ⟨size, rfl⟩ := hdiv
  have ht0 := htpos
  have hsize : tasks * size / tasks = size := Nat.mul_div_cancel_left size ht0
  rw [hsize]
  have hcount (k : Nat) (hk : k < tasks) :
      (if k + 1 = tasks then tasks * size - k * size else size) = size := by
    split
    · rename_i h; rw [← h, Nat.succ_mul]; omega
    · rfl
  -- Every range.
  have hrange (k : Nat) (hk : k < tasks) :
      rangeRows blk get ts chs B W (k * size) (if k + 1 = tasks then tasks * size - k * size else size)
        = (encode (tab (size * B * W) (rangeVal frs (k * size * B) W)),
          localAcc frs (k * size * B) (size * B)) := by
    rw [hcount k hk]
    refine rangeRows_eq blk get ts chs B W (k * size) size val frs hW.symm hB hd hrows ?_ hfrs
      fun j hj ↦ ?_
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right W
        (Nat.mul_le_mul_right B (Nat.le_mul_of_pos_left size ht0)))) hsz
    · exact hev (k * size + j) (by nlinarith)
  -- The accumulators before the ranges, and the terminal.
  have hstarts : (Array.map (fun k ↦ Task.spawn fun _ ↦ rangeRows blk get ts chs B W (k * size)
      (if k + 1 = tasks then tasks * size - k * size else size)) (Array.range tasks)).foldl
      (fun (acc : Array EF × EF) t ↦ (acc.1.push acc.2, acc.2 + t.get.2)) (#[], 0) =
      (tab tasks fun k ↦ specAcc frs (k * size * B), specAcc frs (tasks * size * B)) := by
    rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
    suffices h : ∀ m ≤ tasks, (List.range m).foldl (fun (acc : Array EF × EF) k ↦
        (acc.1.push acc.2, acc.2 + (Task.spawn fun _ ↦ rangeRows blk get ts chs B W (k * size)
          (if k + 1 = tasks then tasks * size - k * size else size)).get.2)) (#[], 0) =
        (tab m fun k ↦ specAcc frs (k * size * B), specAcc frs (m * size * B)) from h tasks le_rfl
    intro m hm
    induction m with
    | zero =>
      rw [List.range_zero, List.foldl_nil, Array.eq_empty_of_size_eq_zero (size_tab 0 _),
        Nat.zero_mul, Nat.zero_mul]
      rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        get_spawn, hrange m (by omega), tab_succ, ← specAcc_add]
      congr 2
      ring
  rw [hstarts]
  refine Prod.ext ?_ rfl
  dsimp only
  rw [foldl_tasks tasks _ (fun k ↦ tab (size * B * W) fun j ↦
      specWord frs ts.length (k * (size * B * W) + j)) fun k hk ↦ ?_,
    foldl_tab_ranges (specWord frs ts.length) (size * B * W) tasks,
    show tasks * (size * B * W) = tasks * size * B * W by ring]
  have hget : ((Array.range tasks).map fun k ↦ Task.spawn fun _ ↦ rangeRows blk get ts chs B W
      (k * size) (if k + 1 = tasks then tasks * size - k * size else size)).getD k
      (Task.pure (ByteArray.empty, 0)) = Task.spawn fun _ ↦ rangeRows blk get ts chs B W (k * size)
        (if k + 1 = tasks then tasks * size - k * size else size) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hk, ite_true, Option.map_some, Option.getD_some]
  rw [hget, get_spawn, hrange k hk, getD_tab _ _ _ hk, hcount k hk]
  subst hW
  rw [shiftAccumulator_eq _ _ _ _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    (by rw [size_tab, Nat.mul_assoc])
    (by rw [size_tab]; exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right B (Nat.le_mul_of_pos_left size ht0)))) hsz),
    show size * B * ((ts.length + 1) * d) = (size * B) * ((ts.length + 1) * d) from rfl,
    shifted_rangeVal]
  refine congrArg encode (tab_congr fun j _ ↦ ?_)
  congr 1
  ring

/-! ### Lookups' tuples as indices -/

/-- A lookup's tuples' expressions in order: every tuple's elements, then its multiplicity. -/
abbrev flatL {α : Type} (l : List (List α × α)) : List α := l.flatMap fun (t, m) ↦ t ++ [m]

/-- A lookup's tuples as indices from `k` (`indexLookup`) name its expressions in order, through
`k + n` for its `n` expressions. -/
theorem indexLookup_spec {α β : Type} (f : Nat → β) (h : α → β) :
    ∀ (l : List (List α × α)) (k : Nat),
      (∀ j (hj : j < (flatL l).length), f (k + j) = h (flatL l)[j]) →
      (indexLookup l k).2 = k + (flatL l).length ∧
      (indexLookup l k).1.map (fun x ↦ (x.1.map f, f x.2)) = l.map (fun x ↦ (x.1.map h, h x.2)) ∧
      ∀ x ∈ (indexLookup l k).1, (∀ e ∈ x.1, k ≤ e ∧ e < k + (flatL l).length) ∧
        k ≤ x.2 ∧ x.2 < k + (flatL l).length
  | [], k, _ => ⟨rfl, rfl, fun x hx ↦ absurd hx List.not_mem_nil⟩
  | (t, m) :: l, k, hf => by
    have hfl : flatL ((t, m) :: l) = t ++ [m] ++ flatL l := by
      simp only [flatL, List.flatMap_cons]
    have hlen : (flatL ((t, m) :: l)).length = t.length + 1 + (flatL l).length := by
      rw [hfl, List.length_append, List.length_append, List.length_singleton]
    obtain ⟨ih1, ih2, ih3⟩ := indexLookup_spec f h l (k + t.length + 1) fun j hj ↦ by
      have := hf (t.length + 1 + j) (by rw [hlen]; omega)
      rw [show k + (t.length + 1 + j) = k + t.length + 1 + j by omega] at this
      rw [this]
      congr 1
      simp only [hfl]
      rw [List.getElem_append_right (by
        simp only [List.length_append, List.length_singleton]; omega)]
      congr 1
      simp only [List.length_append, List.length_singleton]
      omega
    simp only [indexLookup]
    refine ⟨by rw [ih1, hlen]; omega, ?_, ?_⟩
    · rw [List.map_cons, List.map_cons, ih2]
      congr 2
      · apply List.ext_getElem (by simp only [List.length_map, List.length_range'])
        intro j h1 h2
        rw [List.length_map, List.length_range'] at h1
        rw [List.getElem_map, List.getElem_map, List.getElem_range', Nat.one_mul,
          hf j (by rw [hlen]; omega)]
        congr 1
        simp only [hfl]
        rw [List.getElem_append_left (by
            simp only [List.length_append, List.length_singleton]; omega),
          List.getElem_append_left (by omega)]
      · have := hf t.length (by rw [hlen]; omega)
        rw [this]
        congr 1
        simp only [hfl]
        rw [List.getElem_append_left (by
            simp only [List.length_append, List.length_singleton]; omega),
          List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_singleton]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨fun e he ↦ ?_, by omega, by rw [hlen]; omega⟩
        rw [List.mem_range'_1] at he
        rw [hlen]; omega
      · obtain ⟨h1, h2, h3⟩ := ih3 x hx
        exact ⟨fun e he ↦ by have := h1 e he; rw [hlen]; omega, by omega, by rw [hlen]; omega⟩

/-- Lookups' tuples as indices from `k` (`indexTuples`) name their expressions in order. -/
theorem indexTuples_spec {α β : Type} (f : Nat → β) (h : α → β) :
    ∀ (ls : List (List (List α × α))) (k : Nat),
      (∀ j (hj : j < (flatTuples ls).length), f (k + j) = h (flatTuples ls)[j]) →
      (indexTuples ls k).map (·.map fun x ↦ (x.1.map f, f x.2)) =
        ls.map (·.map fun x ↦ (x.1.map h, h x.2)) ∧
      ∀ t ∈ indexTuples ls k, ∀ x ∈ t, (∀ e ∈ x.1, k ≤ e ∧ e < k + (flatTuples ls).length) ∧
        k ≤ x.2 ∧ x.2 < k + (flatTuples ls).length
  | [], k, _ => ⟨rfl, fun t ht ↦ absurd ht List.not_mem_nil⟩
  | l :: ls, k, hf => by
    have hft : flatTuples (l :: ls) = flatL l ++ flatTuples ls := by
      simp only [flatTuples, List.flatMap_cons]
    have hlen : (flatTuples (l :: ls)).length = (flatL l).length + (flatTuples ls).length := by
      rw [hft, List.length_append]
    obtain ⟨l1, l2, l3⟩ := indexLookup_spec f h l k fun j hj ↦ by
      rw [hf j (by rw [hlen]; omega)]
      congr 1
      simp only [hft]
      rw [List.getElem_append_left hj]
    obtain ⟨t2, t3⟩ := indexTuples_spec f h ls (indexLookup l k).2 fun j hj ↦ by
      rw [l1, Nat.add_assoc, hf _ (by rw [hlen]; omega)]
      congr 1
      simp only [hft]
      rw [List.getElem_append_right (by omega)]
      congr 1
      omega
    simp only [indexTuples]
    refine ⟨by rw [List.map_cons, List.map_cons, l2, t2], fun t ht x hx ↦ ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · obtain ⟨h1, h2, h3⟩ := l3 x hx
      exact ⟨fun e he ↦ by have := h1 e he; rw [hlen]; omega, h2, by rw [hlen]; omega⟩
    · obtain ⟨h1, h2, h3⟩ := t3 t ht x hx
      rw [l1] at h1 h2 h3
      exact ⟨fun e he ↦ by have := h1 e he; rw [hlen]; omega, by omega, by rw [hlen]; omega⟩

theorem length_indexTuples {α : Type} :
    ∀ (ls : List (List (List α × α))) (k : Nat), (indexTuples ls k).length = ls.length
  | [], _ => rfl
  | _ :: ls, _ => by simp only [indexTuples, List.length_cons, length_indexTuples ls]

/-- `fracOf` reads its tuples' values only. -/
theorem fracOf_map [Mont32BaseField p] [Mont32.AlgebraId EF] {E : Type} (val : E → F) (a b : EF)
    (t : List (List E × E)) : fracOf val a b t =
      fracOf id a b (t.map fun x ↦ (x.1.map val, val x.2)) := by
  simp only [fracOf, List.foldl_map, List.map_id]
  rfl

/-- The columns of an encoded row-major matrix, in one block. -/
theorem rowMajorCols_eq (M : Array F) (w n : Nat) (hn : 0 < n) (hM : M.size = n * w)
    (hs : 4 * M.size < USize.size) :
    rowMajorCols (encode M) w n = (⟨colBlocks ⟨w, n, M⟩ n, w, n⟩ : Prog.ColsF p).enc := by
  unfold rowMajorCols Prog.ColsF.enc
  dsimp only
  rw [transposeRows_encode M w 0 n (by rw [Nat.zero_add, hM]) hs]
  congr 1
  apply Array.ext (by rw [Array.size_map, Array.size_range, Array.size_map, size_colBlocks,
    Nat.div_self hn, Nat.one_mul])
  intro j h1 h2
  rw [Array.size_map, Array.size_range] at h1
  simp only [Array.getElem_map, Array.getElem_range, colBlocks, Array.getElem_ofFn]
  rw [extract_encode]
  congr 1
  apply Array.ext (by rw [Array.size_extract, Array.size_ofFn, Array.size_ofFn]
                      have := Nat.mul_le_mul_right n (show j + 1 ≤ w by omega)
                      rw [Nat.succ_mul] at this; omega)
  intro k k1 k2
  rw [Array.size_ofFn] at k2
  have hlt : j * n + k < w * n := by
    have := Nat.mul_le_mul_right n (show j + 1 ≤ w by omega)
    rw [Nat.succ_mul] at this; omega
  rw [Array.getElem_extract, Array.getElem_ofFn, Array.getElem_ofFn]
  dsimp only
  have e1 : (j * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k2]
  have e2 : (j * n + k) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt k2, Nat.zero_add]
  have e3 : j / w = 0 := Nat.div_eq_of_lt h1
  have e4 : j % w = j := Nat.mod_eq_of_lt h1
  simp only [e1, e2, e3, e4, Nat.zero_mul, Nat.zero_add]

/-- **The fast permutation trace is the specification's**, in base coordinates as packed words,
with its terminal. -/
theorem permutationWords_eq [Mont32BaseField p] [Mont32.AlgebraId EF] [PlanesInv p EF]
    (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat)
    (trace : Array F) (pis : List F) (chs : List EF)
    (htr : trace.size = 2 ^ logN * A.width)
    (hpre : A.preprocessed.size = 2 ^ logN * A.preprocessedWidth) (hw : 0 < A.width)
    (hls : ∀ l ∈ ls, l.ColsBelow A.width A.preprocessedWidth)
    (hmem : Addressable (2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * d))) :
    permutationWords A ls logN (NTTFast.Packed.Native.encodeFields trace) pis chs =
      (encode (permutationOf A ls logN trace pis chs).1,
        (permutationOf A ls logN trace pis chs).2) := by
  generalize hfrs : Lookup.rowFractions A ls logN trace pis chs = frs
  have hspec : permutationOf A ls logN trace pis chs =
      (tab (2 ^ logN * (ls.length + 1) * d) fun idx ↦
        coord (idx % d) (specEntry frs ls.length (idx / d)), specAcc frs (2 ^ logN)) := by
    unfold permutationOf
    dsimp only
    rw [permutationTrace_eq, flatten_tab, hfrs]
  rw [hspec]
  unfold permutationWords
  dsimp only
  obtain ⟨e, hRe, -, -, hB0, hnB, htasks, hrows⟩ := genShape logN
  rw [← hRe] at hB0 hnB htasks hrows
  set B := min (2 ^ logN / (if 2 ^ logN < 4096 then 1 else 16)) 1024 with hBdef
  set blocks := 2 ^ logN / B with hbl
  have hBs : 4 * B < USize.size := blockSize_lt _
  have hsz : 4 * (blocks * B * ((ls.length + 1) * d)) < USize.size := by
    rw [hnB]; unfold Addressable at hmem; nlinarith
  let tups := ls.map Stark.Lookup.tuples
  let flat := flatTuples tups
  let genRow := Lookup.generationRow A logN trace pis
  let val (k r : Nat) : F := (flat.getD k (.const 0)).eval (genRow r)
  have hlen : (indexTuples tups 0).length = ls.length := by
    rw [length_indexTuples, List.length_map]
  conv_lhs => rw [show ls.length = (indexTuples tups 0).length from hlen.symm]
  have hd : 4 * d < USize.size := by
    unfold Addressable at hmem
    have h1 : d ≤ (ls.length + 1) * d := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h2 := Nat.le_mul_of_pos_left (A.width + A.preprocessedWidth + (ls.length + 1) * d)
      (Nat.two_pow_pos logN)
    omega
  rw [assembleRanges_eq _ _ (indexTuples tups 0) chs B blocks val frs hBs hd hrows
    (by rw [hlen]; exact hsz)
    htasks (fun r ↦ ?hfrs) ?hev, hnB, hlen]
  case hfrs =>
    rw [← hfrs]
    unfold Lookup.rowFractions
    obtain ⟨hmap, -⟩ := indexTuples_spec (fun k ↦ val k r) (fun e ↦ e.eval (genRow r)) tups 0
      fun j hj ↦ by
        show (flat.getD (0 + j) (.const 0)).eval _ = _
        rw [Nat.zero_add, List.getD_eq_getElem _ _ hj]
    have hl1 : (ls.zipIdx.map fun (l, c) ↦ Lookup.fraction (genRow r) (chs.getD (2 * c) 0)
        (chs.getD (2 * c + 1) 0) l).length = ls.length := by
      rw [List.length_map, List.length_zipIdx]
    apply List.ext_getElem (by rw [hl1, List.length_map, List.length_zipIdx, hlen])
    intro c h1 h2
    rw [hl1] at h1
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hc : c < (indexTuples tups 0).length := by rw [hlen]; exact h1
    have hm := List.getElem_of_eq hmap (by rw [List.length_map]; exact hc)
    rw [List.getElem_map, List.getElem_map] at hm
    rw [fracOf_map, hm]
    show fracOf (fun e ↦ e.eval (genRow r)) _ _ ls[c].tuples = _
    rw [fracOf_map]
    simp only [tups, List.getElem_map]
  case hev =>
    intro j hj t ht x hx
    have hjB : j * B + B ≤ 2 ^ logN := by
      have := Nat.mul_le_mul_right B (show j + 1 ≤ blocks from hj)
      rw [Nat.succ_mul, hnB] at this; exact this
    have hn : 4 * 2 ^ logN < USize.size := by
      unfold Addressable at hmem
      have : 2 ^ logN ≤ 2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * d) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hus : 4 * trace.size < USize.size := by
      unfold Addressable at hmem
      have : 2 ^ logN * A.width ≤
          2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * d) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [htr]; omega
    have husp : 4 * A.preprocessed.size < USize.size := by
      unfold Addressable at hmem
      have : 2 ^ logN * A.preprocessedWidth ≤
          2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * d) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [hpre]; omega
    -- The expressions read the columns below the widths.
    have hflat : ∀ ex ∈ flat, ex.colsBelow A.width A.width A.preprocessedWidth
        A.preprocessedWidth = true := by
      intro ex hex
      simp only [flat, tups, flatTuples, List.mem_flatMap, List.mem_map] at hex
      obtain ⟨_, ⟨l, hl, rfl⟩, y, hy, hey⟩ := hex
      rcases List.mem_append.mp hey with hey | hey
      · exact ((hls l hl) y hy).1 ex hey
      · rw [List.mem_singleton.mp hey]; exact ((hls l hl) y hy).2
    let n := 2 ^ logN
    let mt : Mat F := ⟨A.width, n, trace⟩
    let mp : Mat F := ⟨A.preprocessedWidth, n, A.preprocessed⟩
    let r0 := j * B
    let FS : Array F := Array.ofFn (n := n) fun i ↦ if (i.val == 0) = true then 1 else 0
    let LS : Array F := Array.ofFn (n := n) fun i ↦ if (i.val + 1 == n) = true then 1 else 0
    let TS : Array F := Array.ofFn (n := n) fun i ↦ if decide (i.val + 1 < n) = true then 1 else 0
    let L : Prog.LoadsF p := ⟨⟨colBlocks mt n, A.width, n⟩,
      ⟨colBlocks mp n, A.preprocessedWidth, n⟩, blockT mp r0 B, ⟨#[], 0, 1⟩, #[], r0,
      Array.ofFn (n := n) fun i ↦ (i.val + 1) % n,
      seqRows (Array.ofFn (n := n) fun i ↦ (i.val + 1) % n) r0 B, #[], FS, LS, TS⟩
    have hRn (m : Mat F) (hm : m.height = n) : RowsOk m n :=
      ⟨Nat.two_pow_pos _, by rw [hm, Nat.mod_self], hn⟩
    have hmt : (r0 + B) * A.width ≤ trace.size := by
      rw [htr]; exact Nat.mul_le_mul_right _ hjB
    have hmp : (r0 + B) * A.preprocessedWidth ≤ A.preprocessed.size := by
      rw [hpre]; exact Nat.mul_le_mul_right _ hjB
    have hnext (k : Nat) (hk : k < B) :
        (Array.ofFn (n := n) fun i ↦ (i.val + 1) % n).getD (r0 + k) 0 < n := by
      rw [NTTFast.Packed.getD_ofFn_bounded _ _ (by omega)]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hrow (m : Mat F) (hm : m.values.size = n * m.width) {r c : Nat} (hr : r < n)
        (hc : c < m.width) : r * m.width + c < m.values.size := by
      have := Nat.mul_le_mul_right m.width (show r + 1 ≤ n by omega)
      rw [Nat.succ_mul] at this; rw [hm]; omega
    have hcolB (m : Mat F) (c : Nat) (hc : c < m.width) : c * B + B ≤ (blockT m r0 B).size := by
      rw [size_blockT]
      have := Nat.mul_le_mul_right B (show c + 1 ≤ m.width by omega)
      rw [Nat.succ_mul] at this; omega
    have hpB : A.preprocessedWidth * B ≤ A.preprocessed.size := by
      refine le_trans ?_ hmp
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    have htB : A.width * B ≤ trace.size := by
      refine le_trans ?_ hmt
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    have hL : L.Addr := ⟨colsF_addr (hRn mt rfl), colsF_addr (hRn mp rfl), by
        show 4 * (blockT mp r0 B).size < USize.size
        rw [size_blockT]
        show 4 * (A.preprocessedWidth * B) < USize.size
        omega,
      fun a ha ↦ absurd ha (Array.not_mem_empty a), by show 4 * 0 < USize.size; omega,
      fun c hc ↦ absurd hc (Array.not_mem_empty c),
      by show 4 * FS.size < USize.size; rw [Array.size_ofFn]; exact hn,
      by show 4 * LS.size < USize.size; rw [Array.size_ofFn]; exact hn,
      by show 4 * TS.size < USize.size; rw [Array.size_ofFn]; exact hn⟩
    have hVs : 4 * (blockT mt r0 B).size < USize.size := by
      rw [size_blockT]
      show 4 * (A.width * B) < USize.size
      omega
    let prog := Prog.compileOuts flat
    have hlo := Prog.compileOuts_leafOk flat A.width A.width A.preprocessedWidth
      A.preprocessedWidth 0 hflat
    have hcq (c : Nat) (hc : c < A.width) : 0 + c * B + B ≤ (blockT mt r0 B).size := by
      rw [Nat.zero_add]; exact hcolB mt c hc
    have hlq : ∀ src, Prog.Src.Below A.width A.preprocessedWidth A.preprocessedWidth 0 src →
        L.InRange B src := by
      intro src hsrc
      cases src with
      | next c => exact ⟨fun k hk ↦ colsF_has (hRn mt rfl) _ c (hnext k hk) hsrc, seqRows_spec⟩
      | prepCur c => exact hcolB mp c hsrc
      | prepNext c =>
        exact ⟨fun k hk ↦ colsF_has (hRn mp rfl) _ c (hnext k hk) hsrc, seqRows_spec⟩
      | permCur c => exact absurd hsrc (Nat.not_lt_zero c)
      | permNext c => exact absurd hsrc (Nat.not_lt_zero c)
      | periodic j => exact fun h ↦ absurd h (Nat.not_lt_zero j)
      | isFirstRow => show r0 + B ≤ FS.size; rw [Array.size_ofFn]; exact hjB
      | isLastRow => show r0 + B ≤ LS.size; rw [Array.size_ofFn]; exact hjB
      | isTransition => show r0 + B ≤ TS.size; rw [Array.size_ofFn]; exact hjB
    have hcode : ∀ ins ∈ prog.code, ins.InRange (blockT mt r0 B) 0 B L B prog.regs :=
      fun ins hins ↦ Prog.Instr.inRange_of (cq := (· < A.width))
        (lq := Prog.Src.Below A.width A.preprocessedWidth A.preprocessedWidth 0) hcq hlq ins
        ((Prog.compileOuts_run flat ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ _ ↦ 0⟩
          ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2.2 ins hins) (hlo.1 ins hins)
    obtain ⟨hosz, -, -⟩ := Prog.compileOuts_run flat ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0,
      fun _ _ ↦ 0⟩ ⟨fun _ ↦ 0, fun _ ↦ 0⟩
    have hout : ∀ o ∈ prog.outs, o.InRange (blockT mt r0 B) 0 B B prog.regs := by
      intro o ho
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp ho
      have hg : prog.outs[k] = prog.outs.getD k (.reg 0) := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
      have hreg := ((Prog.compileOuts_run flat ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ _ ↦ 0⟩
        ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2.1 k (by rw [← hosz]; exact hk)).2
      have hleaf := hlo.2 _ ho
      rw [← hg] at hreg
      generalize prog.outs[k] = o at hreg hleaf ⊢
      cases o with
      | reg r => exact hreg
      | cur c => exact hcq c hleaf
      | const x => trivial
    have key : ∀ (vb : ByteArray) (Lc : Prog.Loads) (h0 : (NTTFast.Packed.Native.zeroWords
        B).size = 4 * B), vb = encode (blockT mt r0 B) → Lc = L.enc → ∀ k < flat.length,
        (Prog.outWords p 0 prog.outs ⟨vb, 0, B⟩
          (Prog.runBlock p 0 prog.code ⟨vb, 0, B⟩ Lc pis.toArray #[] B hBs
            (Array.replicate prog.regs ⟨NTTFast.Packed.Native.zeroWords B, h0⟩)) B).getD k
          ByteArray.empty = encode (tab B fun i ↦ val k (r0 + i)) := by
      intro vb Lc h0 hvb hLc k hk
      subst hvb hLc
      have hz := Prog.blockRel_zeros (p := p) 0 B prog.regs h0
      rw [Nat.zero_add] at hz
      have hrel := Prog.runBlock_rel 0 prog.code (blockT mt r0 B) 0 B L pis.toArray #[] B prog.regs
        (4 * B) hBs _ _ hz (by exact hVs) hL hcode
      rw [Prog.outWords_rel prog.outs (blockT mt r0 B) 0 B L pis.toArray #[] _ _ hrel hBs hout,
        Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem (by rw [hosz]; exact hk), Option.map_some, Option.getD_some]
      refine congrArg encode (tab_congr fun i hi ↦ ?_)
      have hg : prog.outs[k]'(by rw [hosz]; exact hk) = prog.outs.getD k (.reg 0) := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem, Option.getD_some]
      rw [hg, ((Prog.compileOuts_run flat (Prog.blockCtx 0 (blockT mt r0 B) 0 B L pis.toArray #[]
        B i) ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2.1 k hk).1]
      show _ = (flat.getD k (.const 0)).eval (genRow (r0 + i))
      rw [List.getD_eq_getElem _ _ hk]
      have hri : r0 + i < n := by omega
      refine Expr.eval_hom (R := F) (S := F) id (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        A.width A.width A.preprocessedWidth A.preprocessedWidth
        (Prog.blockCtx 0 (blockT mt r0 B) 0 B L pis.toArray #[] B i).env (genRow (r0 + i))
        (fun c hc ↦ ?_)
        (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun c hc ↦ ?_) (fun jj ↦ ?_) (fun jj ↦ ?_)
        (fun _ ↦ rfl) ?_ ?_ ?_ _ (hflat _ (List.getElem_mem hk))
      · show (blockT mt r0 B).getD (0 + c * B + i) 0 = trace.getD ((r0 + i) * A.width + c) 0
        rw [Nat.zero_add]
        exact blockT_getD mt r0 B c i hc hi
      · show (⟨colBlocks mt n, A.width, n⟩ : Prog.ColsF p).at
          ((Array.ofFn (n := n) fun i ↦ (i.val + 1) % n).getD (r0 + i) 0) c =
          trace.getD ((r0 + i + 1) % 2 ^ logN * A.width + c) 0
        rw [colsF_at (hRn mt rfl) _ c (hnext i hi) hc, NTTFast.Packed.getD_ofFn_bounded _ _ hri]
      · show (blockT mp r0 B).getD (c * B + i) 0 =
          A.preprocessed.getD ((r0 + i) * A.preprocessedWidth + c) 0
        exact blockT_getD mp r0 B c i hc hi
      · show (⟨colBlocks mp n, A.preprocessedWidth, n⟩ : Prog.ColsF p).at
          ((Array.ofFn (n := n) fun i ↦ (i.val + 1) % n).getD (r0 + i) 0) c =
          A.preprocessed.getD ((r0 + i + 1) % 2 ^ logN * A.preprocessedWidth + c) 0
        rw [colsF_at (hRn mp rfl) _ c (hnext i hi) hc, NTTFast.Packed.getD_ofFn_bounded _ _ hri]
      · show ((#[] : Array (Array F)).getD jj #[]).getD (r0 + i) 0 = 0
        simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_nil,
          Option.getD_none]
      · show pis.toArray.getD jj 0 = pis.getD jj 0
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
      · show FS.getD (r0 + i) 0 = if r0 + i = 0 then 1 else 0
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ hri]
        simp only [beq_iff_eq]
      · show LS.getD (r0 + i) 0 = if r0 + i + 1 = 2 ^ logN then 1 else 0
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ hri]
        simp only [beq_iff_eq, n]
      · show TS.getD (r0 + i) 0 = if r0 + i + 1 < 2 ^ logN then 1 else 0
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ hri]
        simp only [decide_eq_true_eq, n]
    obtain ⟨-, hidx⟩ := indexTuples_spec (fun k ↦ flat.getD k (.const 0)) id tups 0
      fun jj hj' ↦ by rw [Nat.zero_add, List.getD_eq_getElem _ _ hj']; rfl
    obtain ⟨h1, -, h2⟩ := hidx t ht x hx
    have hvb : NTTFast.Packed.Native.transposeRows (NTTFast.Packed.Native.encodeFields trace)
        A.width 0 A.width r0 B = encode (blockT mt r0 B) := by
      rw [NTTFast.Packed.Native.encodeFields_eq]
      exact transposeRows_encode trace A.width r0 B hmt hus
    have hLc : (⟨rowMajorCols (NTTFast.Packed.Native.encodeFields trace) A.width n,
        rowMajorCols (NTTFast.Packed.Native.encodeFields A.preprocessed) A.preprocessedWidth n,
        NTTFast.Packed.Native.transposeRows (NTTFast.Packed.Native.encodeFields A.preprocessed)
          A.preprocessedWidth 0 A.preprocessedWidth r0 B, PMat.empty.toCols, ByteArray.empty, r0,
        Array.ofFn (n := n) fun i ↦ (i.val + 1) % n,
        seqRows (Array.ofFn (n := n) fun i ↦ (i.val + 1) % n) r0 B, #[],
        NTTFast.Packed.Native.encodeFields FS, NTTFast.Packed.Native.encodeFields LS,
        NTTFast.Packed.Native.encodeFields TS⟩ : Prog.Loads) = L.enc := by
      rw [NTTFast.Packed.Native.encodeFields_eq, NTTFast.Packed.Native.encodeFields_eq,
        transposeRows_encode A.preprocessed A.preprocessedWidth r0 B hmp husp,
        NTTFast.Packed.Native.encodeFields_eq, NTTFast.Packed.Native.encodeFields_eq,
        NTTFast.Packed.Native.encodeFields_eq,
        rowMajorCols_eq trace A.width n (Nat.two_pow_pos _) (by rw [htr]) hus,
        rowMajorCols_eq A.preprocessed A.preprocessedWidth n (Nat.two_pow_pos _) (by rw [hpre])
          husp]
      simp only [L, Prog.LoadsF.enc, mp, mt, blockT, CompPoly.PackedRepr.encode_empty,
        PMat.empty, PMat.toCols, List.map_toArray, List.map_nil, Prog.ColsF.enc]
    exact ⟨fun e he ↦ key _ _ _ hvb hLc e (by
        have := (h1 e he).2; simpa only [Nat.zero_add] using this),
      key _ _ _ hvb hLc x.2 (by simpa only [Nat.zero_add] using h2)⟩
  rw [show 2 ^ logN * (ls.length + 1) * d = 2 ^ logN * ((ls.length + 1) * d) by ring]

/-- **The fast extension of the permutation trace is the specification's**, and so is its
terminal. -/
theorem permutationLdeWith_rel [Mont32BaseField p] [Mont32.AlgebraId EF] [PlanesInv p EF]
    (plans : List (Nat × Nat × F × LdePlan p))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2) (bits : Nat) (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (ts : Array ByteArray) (t : Array F)
    (pis : List F) (chs : List EF) (hts : NTTFast.Packed.Native.joinRows ts = encode t)
    (hok : PermutationOk EF A ls logN bits t) :
    RM (permutationLdeWith plans bits A ls logN ts pis chs).1
        (permutationLdeOf bits A ls logN t pis chs).1 ∧
      (permutationLdeWith plans bits A ls logN ts pis chs).2 =
        (permutationLdeOf bits A ls logN t pis chs).2 := by
  have hmem : Addressable (2 ^ logN * (A.width + A.preprocessedWidth + (ls.length + 1) * d)) := by
    have := hok.mem
    unfold Addressable at this ⊢
    rw [Mont32.d_eq] at this
    have h1 : 2 ^ logN ≤ 2 ^ (logN + bits) := Nat.pow_le_pow_right (by decide) (by omega)
    have := Nat.mul_le_mul_right (A.width + A.preprocessedWidth + (ls.length + 1) * d) h1
    omega
  have hw := permutationWords_eq A ls logN t pis chs hok.trace hok.preprocessed hok.width
    hok.lookups hmem
  have hsize : (permutationOf A ls logN t pis chs).1.size =
      2 ^ logN * ((ls.length + 1) * d) := by
    unfold permutationOf
    dsimp only
    rw [permutationTrace_eq, flatten_tab, size_tab]
    ring
  unfold permutationLdeWith permutationLdeOf
  rw [hts, ← NTTFast.Packed.Native.encodeFields_eq, hw]
  dsimp only
  refine ⟨ldeWordsWith_one_rel plans hplans logN bits gen _ _ hsize hok.twoAdic ?_, rfl⟩
  have := hok.mem
  unfold Addressable at this ⊢
  rw [Mont32.d_eq] at this
  have := Nat.mul_le_mul_left (2 ^ (logN + bits))
    (Nat.le_add_left ((ls.length + 1) * d) (A.width + A.preprocessedWidth))
  omega


end CompStark.Stark.Fast
