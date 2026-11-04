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
(`fractionsX_rel`), the rows written block by block are the permutation trace's rows with the
accumulator from the range's start (`writeBlock_rel`), and shifting it by the sums before the range
gives the permutation trace (`permutationWords_eq`, `permutationLdeWith_rel`).
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

/-- The reads of a row: the fractions' coordinates at row `i` are `f`'s from word `o`. -/
def RowReads (f : Nat → F) (o : Nat) (fs : Array (ExtPlanes p EF)) (i : Nat) : Prop :=
  ∀ c < fs.size, ∀ k : Fin d,
    NTTFast.Packed.Native.read (fs.getD c (ExtPlanes.zeros 0)).c[k] i = (f (o + d * (c + 1) +
        k)).val

theorem write_add (X : Array F) (k : Nat) (c : F) (hk : k < X.size)
    (hs : 4 * X.size < USize.size) :
    NTTFast.Packed.Native.write (encode X) k
        (NTTFast.Packed.add p (NTTFast.Packed.Native.read (encode X) k) c.val) =
      encode (X.setIfInBounds k (X.getD k 0 + c)) := by
  rw [Words.read_encode X k hs hk, NTTFast.Packed.add_val]
  exact NTTFast.Packed.Native.write_encode X k
    (by rw [CompPoly.CPolynomial.NTTFast.Packed.size_encode_fields]; omega) hk _

/-- Writing `d` words from word `o`, word `o + k` the value `f (o + k)`, by a loop over
`0, …, d - 1`. -/
theorem writeRange_upto (O : Array F) (f : Nat → F) (o : Nat) (x : Nat → UInt32)
    (hx : ∀ k < d, x k = (f (o + k)).val) (hO : o + d ≤ O.size)
    (hs : 4 * O.size < USize.size) :
    (List.range' 0 d).foldl (fun out k ↦ NTTFast.Packed.Native.write out (o + k) (x k))
      (encode (Words.upto O f o)) = encode (Words.upto O f (o + d)) := by
  rw [← List.range_eq_range']
  suffices h : ∀ m ≤ d, (List.range m).foldl (fun out k ↦
      NTTFast.Packed.Native.write out (o + k) (x k)) (encode (Words.upto O f o)) =
      encode (Words.upto O f (o + m)) from h d le_rfl
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      hx m (by omega), Words.write_upto O f (o + m) (by omega) hs, Nat.add_assoc]

theorem accWords_eq (a : EF) :
    accWords a = encode (Array.ofFn fun k : Fin d ↦ FastExt.coord a k) :=
  NTTFast.Packed.Native.encodeFields_eq _

theorem read_accWords (hd : 4 * d < USize.size) (a : EF) (k : Fin d) :
    NTTFast.Packed.Native.read (accWords a) k = (FastExt.coord a k).val := by
  rw [accWords_eq, Words.read_encode _ _ (by rw [Array.size_ofFn]; exact hd)
      (by rw [Array.size_ofFn]; exact k.isLt),
    NTTFast.Packed.getD_ofFn_bounded _ _ k.isLt]

/-- Element `i` of planes whose words at `i` are canonical has those words as coordinates. -/
theorem coord_get (v : ExtPlanes p EF) (i : Nat) (k : Fin d) (z : F)
    (h : NTTFast.Packed.Native.read v.c[k] i = z.val) : FastExt.coord (v.get i) k = z := by
  rw [ExtPlanes.get, FastExt.coord_ofCoords, h, NTTFast.Packed.ofWord_val]

/-- The accumulator's words plus element `i` of planes whose words at `i` are canonical. -/
theorem addCoords_accWords (hd : 4 * d < USize.size) (a : EF) (v : ExtPlanes p EF) (i : Nat)
    (hv : ∀ k : Fin d, ∃ z : F, NTTFast.Packed.Native.read v.c[k] i = z.val) :
    addCoords (accWords a) v i = accWords (a + v.get i) := by
  let X (m : Nat) : Array F := Array.ofFn fun j : Fin d ↦
    if j.val < m then FastExt.coord a j + FastExt.coord (v.get i) j else FastExt.coord a j
  have hX : 4 * (X 0).size < USize.size := by rw [Array.size_ofFn]; omega
  unfold addCoords
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    ← List.range_eq_range']
  have h0 : accWords a = encode (X 0) := by
    rw [accWords_eq]
    exact congrArg encode (congrArg Array.ofFn (funext fun j ↦ by simp only [Nat.not_lt_zero,
      ite_false]))
  suffices h : ∀ m ≤ d, (List.range m).foldl (fun accW k ↦ NTTFast.Packed.Native.write accW k
      (NTTFast.Packed.add p (NTTFast.Packed.Native.read accW k)
        (NTTFast.Packed.Native.read (v.c.toArray.getD k .empty) i))) (encode (X 0)) =
      encode (X m) by
    rw [h0, h d le_rfl, accWords_eq]
    refine congrArg encode (congrArg Array.ofFn (funext fun j ↦ ?_))
    simp only [j.isLt, ite_true, FastExt.coord_add, Pi.add_apply]
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    have hm' : m < d := by omega
    obtain ⟨z, hz⟩ := hv ⟨m, hm'⟩
    have hget : v.c.toArray.getD m .empty = v.c[(⟨m, hm'⟩ : Fin d)] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hm'),
        Option.getD_some, Vector.getElem_toArray]
      rfl
    rw [hget, hz, ← coord_get v i ⟨m, hm'⟩ z hz,
      write_add (X m) m _ (by rw [Array.size_ofFn]; exact hm') (by rw [Array.size_ofFn]; omega)]
    refine congrArg encode (NTTFast.Packed.array_eq_of_getD _ _ 0 (by
      rw [Array.size_setIfInBounds, Array.size_ofFn, Array.size_ofFn]) fun j ↦ ?_)
    rw [NTTFast.Packed.getD_setIfInBounds _ _ _ _ _ (by rw [Array.size_ofFn]; exact hm')]
    simp only [X, getD_ofFn']
    by_cases hj : j = m
    · subst hj
      simp only [hm', dite_true, ite_true, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
    · simp only [hj, ite_false]
      by_cases hjd : j < d
      · simp only [hjd, dite_true]
        by_cases hjm : j < m
        · simp only [hjm, ite_true, show j < m + 1 by omega]
        · simp only [hjm, ite_false, show ¬j < m + 1 by omega]
      · simp only [hjd, dite_false]

/-- A row written at `o`: the accumulator's `d` coordinates, then `d` per lookup; and the
accumulator plus the row's fractions. -/
theorem writeRow_rel (O : Array F) (f : Nat → F) (o : Nat) (fs : Array (ExtPlanes p EF))
    (acc : EF) (i : Nat) (hO : o + (fs.size + 1) * d ≤ O.size) (hs : 4 * O.size < USize.size)
    (hacc : ∀ k : Fin d, f (o + k) = FastExt.coord acc k) (hfs : RowReads f o fs i) :
    writeRow (encode (Words.upto O f o)) (accWords acc) o fs i =
      (encode (Words.upto O f (o + (fs.size + 1) * d)),
        accWords (fs.foldl (fun a v ↦ a + v.get i) acc)) := by
  have hle (m : Nat) (hm : m ≤ fs.size) : o + d * (m + 1) ≤ O.size := by
    have := Nat.mul_le_mul_left d (show m + 1 ≤ fs.size + 1 by omega)
    rw [Nat.mul_comm d (fs.size + 1)] at this
    omega
  have hd : 4 * d < USize.size := by have := hle 0 (Nat.zero_le _); omega
  have hcopy : copyCoords (p := p) (EF := EF) (encode (Words.upto O f o)) o (accWords acc) 0 =
      encode (Words.upto O f (o + d)) := by
    unfold copyCoords
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind]
    exact writeRange_upto O f o _ (fun k hk ↦ by
      rw [Nat.zero_add, show k = ((⟨k, hk⟩ : Fin d) : Nat) from rfl, read_accWords hd, hacc])
      (by have := hle 0 (Nat.zero_le _); omega) hs
  unfold writeRow
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind]
  rw [hcopy]
  suffices h : ∀ m ≤ fs.size, (List.range' 0 m).foldl (fun st c ↦
      ((List.range' 0 d).foldl (fun out k ↦ NTTFast.Packed.Native.write out
        (o + d * (c + 1) + k)
        (NTTFast.Packed.Native.read ((fs.getD c (ExtPlanes.zeros 0)).c.toArray.getD k .empty) i))
        st.1, addCoords st.2 (fs.getD c (ExtPlanes.zeros 0)) i))
      (encode (Words.upto O f (o + d)), accWords acc) =
      (encode (Words.upto O f (o + d * (m + 1))),
        accWords ((fs.toList.take m).foldl (fun a v ↦ a + v.get i) acc)) by
    rw [h fs.size le_rfl, Nat.mul_comm d (fs.size + 1), List.take_of_length_le (by simp),
      Array.foldl_toList]
    rfl
  intro m hm
  induction m with
  | zero => rw [Nat.zero_add, Nat.mul_one]; rfl
  | succ m ih =>
    rw [List.range'_concat, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      Nat.zero_add, Nat.one_mul]
    have hm' : m < fs.size := by omega
    have hfsm : fs.getD m (ExtPlanes.zeros 0) = fs[m] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hm', Option.getD_some]
    have hreads (k : Fin d) : NTTFast.Packed.Native.read (fs.getD m (ExtPlanes.zeros 0)).c[k] i =
        (f (o + d * (m + 1) + k)).val := hfs m hm' k
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [writeRange_upto O f (o + d * (m + 1)) _ (fun k hk ↦ by
          have hget : (fs.getD m (ExtPlanes.zeros 0)).c.toArray.getD k .empty =
              (fs.getD m (ExtPlanes.zeros 0)).c[(⟨k, hk⟩ : Fin d)] := by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
              Option.getD_some, Vector.getElem_toArray]
            rfl
          rw [hget, hreads ⟨k, hk⟩])
        (by have := hle (m + 1) hm; rw [Nat.mul_succ] at this; omega) hs,
        show o + d * (m + 1) + d = o + d * (m + 1 + 1) by ring]
    · dsimp only
      rw [addCoords_accWords hd _ _ i (fun k ↦ ⟨_, hreads k⟩), hfsm,
        List.take_succ_eq_append_getElem (by simpa using hm'), List.foldl_append, List.foldl_cons,
        List.foldl_nil, Array.getElem_toList]

/-- A block written from row `r`, the accumulators `accs` row by row. -/
theorem writeBlock_rel (O : Array F) (f : Nat → F) (r : Nat) (fs : Array (ExtPlanes p EF))
    (acc : EF) (B W : Nat) (accs : Nat → EF) (hW : W = (fs.size + 1) * d)
    (hd : 4 * d < USize.size)
    (hO : (r + B) * W ≤ O.size) (hs : 4 * O.size < USize.size) (hacc0 : accs 0 = acc)
    (hstep : ∀ i < B, accs (i + 1) = fs.foldl (fun a v ↦ a + v.get i) (accs i))
    (hacc : ∀ i < B, ∀ k : Fin d, f ((r + i) * W + k) = FastExt.coord (accs i) k)
    (hreads : ∀ i < B, RowReads f ((r + i) * W) fs i) :
    writeBlock (encode (Words.upto O f (r * W))) r fs acc B W =
      (encode (Words.upto O f ((r + B) * W)), accs B) := by
  unfold writeBlock
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind]
  suffices h : ∀ m ≤ B, (List.range' 0 m).foldl (fun st i ↦
      writeRow st.1 st.2 ((r + i) * W) fs i) (encode (Words.upto O f (r * W)), accWords acc) =
      (encode (Words.upto O f ((r + m) * W)), accWords (accs m)) by
    rw [h B le_rfl]
    refine Prod.ext rfl (FastExt.ext fun k ↦ ?_)
    show FastExt.coord (FastExt.ofCoords _) k = _
    rw [FastExt.coord_ofCoords, read_accWords hd, NTTFast.Packed.ofWord_val]
  intro m hm
  induction m with
  | zero => rw [hacc0]; rfl
  | succ m ih =>
    rw [List.range'_concat, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      Nat.zero_add, Nat.one_mul]
    dsimp only
    have hle : (r + m) * W + W ≤ O.size := by
      have := Nat.mul_le_mul_right W (show r + m + 1 ≤ r + B by omega)
      rw [Nat.succ_mul] at this
      omega
    rw [writeRow_rel O f _ fs (accs m) m (by rw [← hW]; exact hle) hs (hacc m (by omega))
      (hreads m (by omega)), ← hstep m (by omega), ← hW]
    congr 3
    ring

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

theorem div_mod_row (W row e : Nat) (he : e < W) :
    (row * W + e) / W = row ∧ (row * W + e) % W = e :=
  ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he, Nat.zero_add],
    mod_of_block row W e he⟩

/-- **A range of blocks**: its rows of the permutation trace, the accumulator from `0`, and the
sum of their fractions. -/
theorem rangeRows_eq [Mont32BaseField p] [Mont32.AlgebraId EF] [PlanesInv p EF] {β E : Type}
    (blk : Nat → β)
    (get : β → E → ByteArray)
    (ts : List (List (List E × E)))
    (chs : List EF) (B W b0 nb : Nat) (val : E → Nat → F) (frs : Nat → List EF)
    (hW : W = (ts.length + 1) * d) (hB : 4 * B < USize.size) (hdU : 4 * d < USize.size)
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
  have hWd : d ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hapl : ∀ c < ts.length, ExtPlanes.Rel
      (((Array.range ts.length).map fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B).getD c
        (ExtPlanes.zeros B)) (tab B fun _ ↦ chs.getD (2 * c) 0) := by
    intro c hc
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hc, ite_true, Option.map_some, Option.getD_some]
    exact XRel.planes hB (x := .const _) (fun _ _ ↦ rfl)
  generalize (Array.range ts.length).map (fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B) =
    apl at hapl
  let Z : Array F := tab (nb * B * W) fun _ ↦ 0
  have hZ : CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (nb * B * W) =
      encode (Words.upto Z (rangeVal frs (b0 * B) W) (0 * B * W)) := by
    rw [Nat.zero_mul, Nat.zero_mul, Words.upto_zero, zeroWords_tab (p := p)]
  have hZs : 4 * Z.size < USize.size := by rw [size_tab]; exact hsz
  rw [hZ]
  suffices h : ∀ m ≤ nb, (List.range m).foldl (fun st j ↦
      writeBlock st.1 (j * B) (fractionsX B get (blk ((b0 + j) * B)) ts chs apl).toArray st.2 B W)
      (encode (Words.upto Z (rangeVal frs (b0 * B) W) (0 * B * W)), 0) =
      (encode (Words.upto Z (rangeVal frs (b0 * B) W) (m * B * W)),
        localAcc frs (b0 * B) (m * B)) by
    rw [h nb le_rfl, Words.upto_full _ _ _ (size_tab _ _)]
    rfl
  intro m hm
  induction m with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.zero_mul]
    rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    dsimp only
    have hfs (c : Nat) (hc : c < ts.length) := fractionsX_getD hB get (blk ((b0 + m) * B))
      (fun e i ↦ val e ((b0 + m) * B + i)) ts chs apl hapl (hev m (by omega)) c hc
    have hsize : (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).toArray.size = ts.length := by
      rw [List.size_toArray, length_fractionsX]
    have hrow (i : Nat) (hi : i < B) : (frs ((b0 + m) * B + i)) =
        (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).map (·.get i) := by
      apply List.ext_getElem (by rw [List.length_map, length_fractionsX, hfrs, List.length_map,
        List.length_zipIdx])
      intro c h1 h2
      have hc : c < ts.length := by rwa [hfrs, List.length_map, List.length_zipIdx] at h1
      rw [List.getElem_map]
      have := hfs c hc
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some] at this
      rw [ExtPlanes.get_eq this hB i hi]
      simp only [hfrs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hx := writeBlock_rel Z (rangeVal frs (b0 * B) W) (m * B)
      (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).toArray (localAcc frs (b0 * B) (m * B)) B W
      (fun i ↦ localAcc frs (b0 * B) (m * B + i)) (by rw [hsize, hW]) hdU
      (by
        rw [size_tab]
        have := Nat.mul_le_mul_right (B * W) hm
        calc (m * B + B) * W = (m + 1) * (B * W) := by ring
          _ ≤ nb * (B * W) := this
          _ = nb * B * W := by ring)
      hZs rfl (fun i hi ↦ by
        rw [show m * B + (i + 1) = (m * B + i) + 1 by omega, localAcc_succ, List.foldl_toArray,
          show b0 * B + (m * B + i) = (b0 + m) * B + i by ring, hrow i hi, List.foldl_map])
      (fun i hi k ↦ by
        obtain ⟨hq, hr⟩ := div_mod_row W (m * B + i) k (by have := k.isLt; omega)
        simp only [rangeVal, hq, hr, ite_of k.isLt, coord_fin]) (fun i hi c hc k ↦ by
        rw [hsize] at hc
        have := hfs c hc
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some] at this
        obtain ⟨-, hcs⟩ := ExtPlanes.rel_tab_iff.mp this
        have hfsc : (fractionsX B get (blk ((b0 + m) * B)) ts chs apl).toArray.getD c
            (ExtPlanes.zeros 0) =
            (fractionsX B get (blk ((b0 + m) * B)) ts chs apl)[c]'(by
              rw [length_fractionsX]; exact hc) := by
          rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
            List.getElem?_eq_getElem (by rw [length_fractionsX]; exact hc), Option.getD_some]
        have hcW : d * (c + 1) + k < W := by
          have := Nat.mul_le_mul_left d (show c + 1 + 1 ≤ ts.length + 1 by omega)
          rw [Nat.mul_succ, Nat.mul_comm d (ts.length + 1), ← hW] at this
          have := k.isLt
          omega
        obtain ⟨hq, hr⟩ := div_mod_row W (m * B + i) (d * (c + 1) + k) hcW
        rw [← Nat.add_assoc] at hq hr
        have hfr : (frs (b0 * B + (m * B + i))).getD c 0 = fracOf
            (val · ((b0 + m) * B + i)) (chs.getD (2 * c) 0) (chs.getD (2 * c + 1) 0) ts[c] := by
          rw [show b0 * B + (m * B + i) = (b0 + m) * B + i by ring, hfrs,
            List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_zipIdx]; exact hc)]
          simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
        have e1 : (d * (c + 1) + k) / d - 1 = c := by
          rw [Nat.mul_add_div hd, Nat.div_eq_of_lt k.isLt]; omega
        have e2 : (d * (c + 1) + k) % d = k := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]
        have e3 : ¬(d * (c + 1) + k < d) := by
          have : d ≤ d * (c + 1) := Nat.le_mul_of_pos_right d (Nat.succ_pos c)
          omega
        rw [hfsc, hcs k, read_tab hB _ i hi]
        simp only [rangeVal, hq, hr, e1, e2, ite_of_not e3, hfr, coord_fin])
    rw [show (m + 1) * B * W = (m * B + B) * W by ring, show (m + 1) * B = m * B + B by ring,
      show m * B * W = m * B * W from rfl] at *
    rw [show m * B * W = (m * B) * W from rfl] at hx ⊢
    exact hx


/-! ### The whole permutation trace -/

theorem ext_add_assoc (a b c : EF) : a + b + c = a + (b + c) :=
  FastExt.toSpec_injective (by simp only [FastExt.toSpec_add, add_assoc])

theorem ext_add_zero (a : EF) : a + 0 = a :=
  FastExt.toSpec_injective (by rw [FastExt.toSpec_add, FastExt.toSpec_zero, add_zero])

theorem foldl_add_shift (s : EF) : ∀ (xs : List EF) (a : EF),
    xs.foldl (· + ·) (s + a) = s + xs.foldl (· + ·) a
  | [], _ => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, List.foldl_cons, ext_add_assoc, foldl_add_shift s xs]

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
    min (2 ^ e) 256 ∣ 2 ^ e ∧ 0 < min (2 ^ e) 256 ∧
    2 ^ logN / min (2 ^ e) 256 * min (2 ^ e) 256 = 2 ^ logN ∧
    (if 2 ^ logN / min (2 ^ e) 256 < 16 then 1 else 16) ∣ 2 ^ logN / min (2 ^ e) 256 := by
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
  -- `B = 2 ^ b` for `b = min e 8`.
  have hB : min (2 ^ e) 256 = 2 ^ (min e 8) := by
    rcases Nat.le_total e 8 with h | h
    · rw [Nat.min_eq_left h, Nat.min_eq_left (le_trans (Nat.pow_le_pow_right (by decide) h)
        (le_refl (2 ^ 8)))]
    · rw [Nat.min_eq_right h, Nat.min_eq_right (le_trans (le_refl (2 ^ 8))
        (Nat.pow_le_pow_right (by decide) h))]
  rw [hB]
  have hle : min e 8 ≤ logN := by
    have : 2 ^ e ≤ 2 ^ logN := by rw [← h2]; exact Nat.le_mul_of_pos_left _ (by split <;> omega)
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp this
    omega
  have hdiv : 2 ^ logN / 2 ^ (min e 8) = 2 ^ (logN - min e 8) := Nat.pow_div hle (by decide)
  refine ⟨Nat.pow_dvd_pow 2 (Nat.min_le_left e 8), Nat.two_pow_pos _, ?_, ?_⟩
  · rw [hdiv, ← Nat.pow_add]; congr 1; omega
  · rw [hdiv]
    split
    · exact Nat.one_dvd _
    · rename_i hge
      have h4 : 4 ≤ logN - min e 8 := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega :
          logN - min e 8 < 4)) (le_refl _))
      exact (Nat.pow_dvd_pow 2 h4 : 2 ^ 4 ∣ _)

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
    (hB : 4 * B < USize.size) (hd : 4 * d < USize.size)
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
    refine rangeRows_eq blk get ts chs B W (k * size) size val frs hW.symm hB hd ?_ hfrs fun j hj ↦ ?_
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
    permutationWords A ls logN trace pis chs =
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
  obtain ⟨e, hRe, -, -, hB0, hnB, htasks⟩ := genShape logN
  rw [← hRe] at hB0 hnB htasks
  set B := min (2 ^ logN / (if 2 ^ logN < 4096 then 1 else 16)) 256 with hBdef
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
  rw [assembleRanges_eq _ _ (indexTuples tups 0) chs B blocks val frs hBs hd (by rw [hlen]; exact hsz)
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
    (ls : List (Stark.Lookup F)) (logN : Nat) (t : Array F) (pis : List F) (chs : List EF)
    (hok : PermutationOk EF A ls logN bits t) :
    RM (permutationLdeWith plans bits A ls logN t pis chs).1
        (permutationLdeOf bits A ls logN t pis chs).1 ∧
      (permutationLdeWith plans bits A ls logN t pis chs).2 =
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
  rw [hw]
  dsimp only
  refine ⟨ldeWordsWith_one_rel plans hplans logN bits gen _ _ hsize hok.twoAdic ?_, rfl⟩
  have := hok.mem
  unfold Addressable at this ⊢
  rw [Mont32.d_eq] at this
  have := Nat.mul_le_mul_left (2 ^ (logN + bits))
    (Nat.le_add_left ((ls.length + 1) * d) (A.width + A.preprocessedWidth))
  omega


end CompStark.Stark.Fast
