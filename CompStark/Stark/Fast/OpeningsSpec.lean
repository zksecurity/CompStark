/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.QuotientSpec

/-! # The specification's openings in closed form

`parChunks` concatenates its ranges (`parChunks_eq`), so the values of a matrix's columns at a
point are, column by column, a weighted sum over the rows (`openedAt_eq`).
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

theorem ofFn_append_ofFn {α : Type} (g : Nat → α) (a b : Nat) :
    (Array.ofFn (n := a) fun i ↦ g i.val) ++ (Array.ofFn (n := b) fun i ↦ g (a + i.val)) =
      Array.ofFn (n := a + b) fun i ↦ g i.val := by
  apply Array.toList_inj.mp
  simp only [Array.toList_append, Array.toList_ofFn, List.ofFn_add, Fin.val_castLE,
    Fin.val_natAdd]

theorem toList_ofFn_eq_map {α : Type} (g : Nat → α) (m : Nat) :
    (Array.ofFn (n := m) fun i ↦ g i.val).toList = (List.range m).map g := by
  apply List.ext_getElem
  · rw [Array.length_toList, Array.size_ofFn, List.length_map, List.length_range]
  · intro i h1 h2
    rw [Array.getElem_toList, Array.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- Ranges of `f` concatenated in order give the whole. -/
theorem parChunks_eq {α : Type} (n parts : Nat) (f : Nat → Nat → Array α) (g : Nat → α)
    (hf : ∀ s len, s + len ≤ n ∨ len = 0 → f s len = Array.ofFn (n := len) fun k ↦ g (s + k.val))
    (hp : 0 < parts ∨ n = 0) :
    parChunks n parts f = Array.ofFn (n := n) fun i ↦ g i.val := by
  unfold parChunks
  generalize hsz : (n + parts - 1) / parts = size
  have hstep : ∀ k, ((List.range k).foldl (fun acc i ↦ acc ++
      f (i * size) (min size (n - min n (i * size)))) #[]).toList =
      (List.range (min n (k * size))).map g := by
    intro k
    induction k with
    | zero => rw [List.range_zero, List.foldl_nil, Nat.zero_mul, Nat.min_zero]; rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.toList_append,
        ih, hf _ _ (by omega), toList_ofFn_eq_map (fun x ↦ g (k * size + x))]
      by_cases hk : k * size ≤ n
      · rw [show min n ((k + 1) * size) = min n (k * size) + min size (n - min n (k * size)) by
          rw [Nat.succ_mul]; omega, List.range_add, List.map_append, List.map_map,
          Nat.min_eq_right hk]
        rfl
      · rw [show min size (n - min n (k * size)) = 0 by omega,
          show min n ((k + 1) * size) = min n (k * size) by rw [Nat.succ_mul]; omega,
          List.range_zero, List.map_nil, List.append_nil]
  have hn : min n (parts * size) = n := by
    rcases hp with hp | hp
    · have := Nat.lt_div_mul_add (a := n + parts - 1) hp
      rw [hsz] at this
      rw [Nat.min_eq_left (by rw [Nat.mul_comm]; omega)]
    · rw [hp, Nat.zero_min]
  apply Array.toList_inj.mp
  rw [toList_ofFn_eq_map, Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
  have := hstep parts
  rw [hn] at this
  exact this

/-- `∑ᵢ m[perm[i]][j] · weights[i]` over the first `h` rows, in order. -/
def colSum (m : Array F) (perm : Array Nat) (weights : Array EF) (w h j : Nat) : EF :=
  (List.range' 0 h).foldl (fun acc i ↦
    acc + KoalaBear.Fast.Ext4.smul (m.getD (perm.getD i 0 * w + j) 0) (weights.getD i 0)) 0

theorem weightedColumns_eq (m : Array F) (perm : Array Nat) (weights : Array EF)
    (w h j0 nj : Nat) (factor : EF) :
    weightedColumns m perm weights w h j0 nj factor =
      Array.ofFn (n := nj) fun k ↦ factor * colSum m perm weights w h (j0 + k.val) := by
  simp only [weightedColumns, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Nat.add_sub_cancel_left]
  have := foldl_push_range' (fun j ↦ factor * colSum m perm weights w h j) j0 nj
    (Array.emptyWithCapacity nj)
  rw [Array.emptyWithCapacity_eq, Array.empty_append] at this
  exact this

/-- The barycentric weights `x / (z - x)` of the natural-order coset of `2 ^ logH` points. -/
abbrev baryWeights (logH : Nat) (z : EF) : Array EF :=
  Array.zipWith KoalaBear.Fast.Ext4.smul (cosetPoints gen logH)
    (batchInv ((cosetPoints gen logH).map fun x ↦ z - Ext.ofBase x))

theorem openedAt_eq (b : Nat) (m : Mat) (z : EF) :
    Fri.openedAt b m z = Array.ofFn (n := m.width) fun j ↦
      KoalaBear.Fast.cosetFactor (Nat.log2 m.height - b) gen z *
        colSum m.values (bitRevPerm (Nat.log2 m.height - b)) (baryWeights (Nat.log2 m.height - b) z)
          m.width (2 ^ (Nat.log2 m.height - b)) j.val := by
  unfold Fri.openedAt
  dsimp only
  refine parChunks_eq _ _ _ (fun j ↦ KoalaBear.Fast.cosetFactor (Nat.log2 m.height - b) gen z *
    colSum m.values (bitRevPerm (Nat.log2 m.height - b)) (baryWeights (Nat.log2 m.height - b) z)
      m.width (2 ^ (Nat.log2 m.height - b)) j) (fun s len _ ↦ ?_) ?_
  · rw [weightedColumns_eq]
  · by_cases h : m.width = 0
    · exact Or.inr h
    · exact Or.inl (Nat.lt_min.mpr ⟨Nat.pos_of_ne_zero h, by decide⟩)

end CompStark.Stark
