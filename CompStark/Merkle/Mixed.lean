/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.VCVio

/-! # Merkle trees of mixed heights

The Merkle tree of matrices whose heights are powers of two `2 ^ j ≤ 2 ^ k` (Plonky3's trees with
injected matrices), with any leaf hash `hash` and compression `compress`:

* `heightGroups_eq`: the verifier's height groups are the distinct heights, tallest first, each
  with the indices of its matrices in order.
* `layers_eq_injNode`: the digest layers are the nodes `injNode`: a leaf hashes the rows of the
  tallest matrices, and a node compresses its children, then, if some matrices have the height of
  its layer, compresses the result with the hash of their rows.
* `verifyMulti_prune_mixed`: the honest multi-opening, every matrix's row at the index shifted to
  its height and the pruned siblings of the tree's paths, is accepted against the tree's root.
-/

@[expose] public section
namespace CompStark.Merkle

open MixedMerkleTree (nodeValue nodeValue_zero nodeValue_succ)

variable {F : Type} {d : Nat}

/-! ### Sorting by height -/

section Sorting
variable {α : Type} (κ : α → Nat)

/-- Merge sort by a key, largest first, keeps the order among equal keys. -/
theorem filter_mergeSort_key (l : List α) (h : Nat) :
    (l.mergeSort fun a b ↦ decide (κ b ≤ κ a)).filter (κ · == h) = l.filter (κ · == h) := by
  have trans : ∀ a b c : α, decide (κ b ≤ κ a) = true → decide (κ c ≤ κ b) = true →
      decide (κ c ≤ κ a) = true := fun a b c h1 h2 ↦ by
    simp only [decide_eq_true_eq] at *; omega
  have total : ∀ a b : α, (decide (κ b ≤ κ a) || decide (κ a ≤ κ b)) = true := fun a b ↦ by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have hpw : (l.filter (κ · == h)).Pairwise fun a b ↦ decide (κ b ≤ κ a) = true := by
    refine List.Pairwise.imp_of_mem (R := fun _ _ ↦ True) ?_
      (List.pairwise_of_forall fun _ _ ↦ trivial)
    intro a b ha hb _
    simp only [List.mem_filter, beq_iff_eq] at ha hb
    simp only [ha.2, hb.2, Nat.le_refl, decide_true]
  have hsub := List.sublist_mergeSort trans total hpw (List.filter_sublist (l := l))
  have hsub' := hsub.filter (κ · == h)
  rw [List.filter_filter, List.filter_congr (fun a _ ↦ Bool.and_self _)] at hsub'
  refine (hsub'.eq_of_length ?_).symm
  exact ((List.mergeSort_perm l _).filter _).length_eq.symm

/-- A list sorted by a key, largest first, grouped as `heightGroups` groups it: one group per
distinct key, largest first, each with its elements in order. -/
theorem foldr_groups (heights : List Nat) :
    ∀ S : List Nat, S.Pairwise (fun a b ↦ heights.getD b 0 ≤ heights.getD a 0) →
      ∃ keys : List Nat, keys.Pairwise (· > ·) ∧
        (∀ h, h ∈ keys ↔ ∃ i ∈ S, heights.getD i 0 = h) ∧
        keys.head? = (S.map (heights.getD · 0)).head? ∧
        S.foldr (fun i gs ↦
          match gs with
          | (h, is) :: rest => if heights.getD i 0 = h then (h, i :: is) :: rest
              else (heights.getD i 0, [i]) :: gs
          | [] => [(heights.getD i 0, [i])]) [] =
          keys.map fun h ↦ (h, S.filter (heights.getD · 0 == h))
  | [], _ => ⟨[], List.Pairwise.nil, fun h ↦ by simp only [List.not_mem_nil, false_and,
      exists_false], rfl, rfl⟩
  | a :: S, hs => by
    obtain ⟨keys, hk, hmem, hhead, heq⟩ := foldr_groups heights S hs.of_cons
    have hle : ∀ i ∈ S, heights.getD i 0 ≤ heights.getD a 0 := fun i hi ↦
      List.rel_of_pairwise_cons hs hi
    rw [List.foldr_cons, heq]
    rcases S with _ | ⟨b, S'⟩
    · have hk0 : keys = [] := by
        cases keys with
        | nil => rfl
        | cons _ _ => simp only [List.map_nil, List.head?_nil, List.head?_cons,
            reduceCtorEq] at hhead
      subst hk0
      refine ⟨[heights.getD a 0], List.pairwise_singleton _ _, fun h ↦ ?_, rfl, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
        exact eq_comm
      · simp only [List.map_nil, List.map_cons, List.filter_cons, beq_self_eq_true, ↓reduceIte,
          List.filter_nil]
    · obtain ⟨k0, ks, rfl⟩ : ∃ k0 ks, keys = k0 :: ks := by
        cases keys with
        | nil => simp only [List.map_cons, List.head?_nil, List.head?_cons,
            reduceCtorEq] at hhead
        | cons k0 ks => exact ⟨k0, ks, rfl⟩
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have hks : ∀ h ∈ ks, h < heights.getD b 0 := fun h hh ↦
        List.rel_of_pairwise_cons hk hh
      simp only [List.map_cons]
      by_cases hab : heights.getD a 0 = heights.getD b 0
      · rw [ite_eq_left hab]
        refine ⟨heights.getD b 0 :: ks, hk, fun h ↦ ?_, by simp only [List.head?_cons, hab], ?_⟩
        · rw [hmem]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_cons_of_mem _ hi, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            rcases List.mem_cons.mp hi with rfl | hi
            · exact ⟨b, List.mem_cons_self, hab.symm⟩
            · exact ⟨i, hi, rfl⟩
        · rw [List.map_cons, List.filter_cons_of_pos (a := a) (l := b :: S')
            (by rw [hab, beq_self_eq_true])]
          refine congrArg₂ List.cons rfl (List.map_congr_left fun h hh ↦ ?_)
          have := hks h hh
          rw [List.filter_cons_of_neg (a := a) (l := b :: S') (by rw [hab, beq_iff_eq]; omega)]
      · rw [ite_eq_right hab]
        have hlt : heights.getD b 0 < heights.getD a 0 := by
          have := hle b List.mem_cons_self; omega
        have hbS : ∀ i ∈ b :: S', heights.getD i 0 ≤ heights.getD b 0 := fun i hi ↦ by
          rcases List.mem_cons.mp hi with rfl | hi
          · exact Nat.le_refl _
          · exact List.rel_of_pairwise_cons hs.of_cons hi
        refine ⟨heights.getD a 0 :: heights.getD b 0 :: ks, ?_, fun h ↦ ?_, rfl, ?_⟩
        · refine List.Pairwise.cons (fun h hh ↦ ?_) hk
          rcases List.mem_cons.mp hh with rfl | hh
          · exact hlt
          · have := hks h hh; omega
        · rw [List.mem_cons, hmem]
          constructor
          · rintro (rfl | ⟨i, hi, rfl⟩)
            · exact ⟨a, List.mem_cons_self, rfl⟩
            · exact ⟨i, List.mem_cons_of_mem _ hi, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            rcases List.mem_cons.mp hi with rfl | hi
            · exact Or.inl rfl
            · exact Or.inr ⟨i, hi, rfl⟩
        · have hnil : (b :: S').filter (fun x ↦ heights.getD x 0 == heights.getD a 0) = [] :=
            List.filter_eq_nil_iff.mpr fun i hi ↦ by have := hbS i hi; rw [beq_iff_eq]; omega
          have hself : (a :: b :: S').filter (fun x ↦ heights.getD x 0 == heights.getD a 0) =
              [a] := by
            rw [List.filter_cons_of_pos (by rw [beq_self_eq_true]), hnil]
          rw [List.map_cons (a := heights.getD a 0), hself]
          refine congrArg₂ List.cons rfl ?_
          rw [← List.map_cons (f := fun h ↦ (h, (b :: S').filter (heights.getD · 0 == h)))]
          refine List.map_congr_left fun h hh ↦ ?_
          have : h ≤ heights.getD b 0 := by
            rcases List.mem_cons.mp hh with rfl | hh
            · exact Nat.le_refl _
            · have := hks h hh; omega
          rw [List.filter_cons_of_neg (a := a) (l := b :: S') (by rw [beq_iff_eq]; omega)]

/-- `heightGroups`: the distinct heights, tallest first, each with the indices of its matrices in
order. -/
theorem heightGroups_eq (heights : List Nat) :
    ∃ keys : List Nat, keys.Pairwise (· > ·) ∧ (∀ h, h ∈ keys ↔ h ∈ heights) ∧
      heightGroups heights =
        keys.map fun h ↦ (h, (List.range heights.length).filter (heights.getD · 0 == h)) := by
  have trans : ∀ a b c : Nat, decide (heights.getD b 0 ≤ heights.getD a 0) = true →
      decide (heights.getD c 0 ≤ heights.getD b 0) = true →
      decide (heights.getD c 0 ≤ heights.getD a 0) = true := fun a b c h1 h2 ↦ by
    simp only [decide_eq_true_eq] at *; omega
  have total : ∀ a b : Nat, (decide (heights.getD b 0 ≤ heights.getD a 0) ||
      decide (heights.getD a 0 ≤ heights.getD b 0)) = true := fun a b ↦ by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have hs := List.pairwise_mergeSort trans total (List.range heights.length)
  obtain ⟨keys, hk, hmem, -, heq⟩ := foldr_groups heights _
    (hs.imp fun h ↦ by simpa only [decide_eq_true_eq] using h)
  refine ⟨keys, hk, fun h ↦ ?_, ?_⟩
  · rw [hmem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [List.mem_mergeSort, List.mem_range] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    · intro hh
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hh
      exact ⟨i, by rw [List.mem_mergeSort, List.mem_range]; exact hi,
        by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]⟩
  · unfold heightGroups
    dsimp only
    refine heq.trans (List.map_congr_left fun h _ ↦ ?_)
    rw [filter_mergeSort_key (heights.getD · 0)]

end Sorting

/-! ### The tree -/

/-- A list of matrices sorted tallest first, all of height at most `M`: those of height `M` come
first. -/
theorem takeWhile_height (M : Nat) (q : Matrix F → Bool) : ∀ L : List (Matrix F),
    (∀ m ∈ L, q m = (m.height == M)) → L.Pairwise (fun a b ↦ b.height ≤ a.height) →
    (∀ m ∈ L, m.height ≤ M) →
    L.takeWhile q = L.filter (·.height == M) ∧
      L.drop (L.takeWhile q).length = L.filter (·.height < M)
  | [], _, _, _ => ⟨rfl, rfl⟩
  | m :: L, hq, hs, hle => by
    by_cases hm : m.height = M
    · have hqm : q m = true := by rw [hq m List.mem_cons_self, hm, beq_self_eq_true]
      obtain ⟨h1, h2⟩ := takeWhile_height M q L (fun x hx ↦ hq x (List.mem_cons_of_mem _ hx))
        hs.of_cons fun x hx ↦ hle x (List.mem_cons_of_mem _ hx)
      rw [List.takeWhile_cons_of_pos hqm, List.filter_cons_of_pos (by rw [hm, beq_self_eq_true]),
        List.length_cons, List.drop_succ_cons, h2, h1,
        List.filter_cons_of_neg (by rw [hm]; simp only [Nat.lt_irrefl, decide_false,
          Bool.false_eq_true, not_false_eq_true])]
      exact ⟨rfl, rfl⟩
    · have hlt : m.height < M := lt_of_le_of_ne (hle m List.mem_cons_self) hm
      have hqm : q m = false := by rw [hq m List.mem_cons_self, beq_eq_false_iff_ne]; exact hm
      have hL : ∀ x ∈ L, x.height < M := fun x hx ↦
        lt_of_le_of_lt (List.rel_of_pairwise_cons hs hx) hlt
      rw [List.takeWhile_cons_of_neg (by rw [hqm]; exact Bool.false_ne_true),
        List.filter_eq_nil_iff.mpr fun x hx ↦ by
          rcases List.mem_cons.mp hx with rfl | hx
          · rw [beq_iff_eq]; exact hm
          · have := hL x hx; rw [beq_iff_eq]; omega,
        List.filter_eq_self.mpr fun x hx ↦ by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact decide_eq_true hlt
          · exact decide_eq_true (hL x hx)]
      exact ⟨rfl, rfl⟩

/-- `padEven` of a power of two. -/
theorem padEven_two_pow (k : Nat) : padEven (2 ^ k) = 2 ^ k := by
  rcases k with _ | k
  · rfl
  · simp only [padEven, Nat.pow_succ, Nat.mul_mod_left, Nat.add_zero]
    have := Nat.one_le_two_pow (n := k)
    simp only [show 2 ^ k * 2 ≠ 1 by omega, ↓reduceIte]

/-- Sorted tallest first, matrices of one height keep their order. -/
theorem filter_sortTallest (ms : List (Matrix F)) (h : Nat) :
    (sortTallest ms).filter (·.height == h) = ms.filter (·.height == h) :=
  filter_mergeSort_key (·.height) ms h

theorem pairwise_sortTallest (ms : List (Matrix F)) :
    (sortTallest ms).Pairwise fun a b ↦ b.height ≤ a.height := by
  have := List.pairwise_mergeSort (le := fun a b : Matrix F ↦ decide (b.height ≤ a.height))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) ms
  exact this.imp fun h ↦ by simpa only [decide_eq_true_eq] using h

section Tree
variable [Zero F] (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- The rows `i` of the matrices of height `2 ^ j`, concatenated. -/
def groupRows (ms : List (Matrix F)) (j i : Nat) : List F :=
  (ms.filter (·.height == 2 ^ j)).flatMap (·.row i)

/-- The injections of the tree of matrices `ms`: depth `t` injects the rows of the matrices of
height `2 ^ t`, if there are any. -/
def injRows (ms : List (Matrix F)) (t : Nat) : Option (Nat → List F) :=
  if ms.any (·.height == 2 ^ t) then some (groupRows ms t) else none

/-- The node at level `l` and index `i` of the tree of matrices `ms` of heights at most
`2 ^ k`: VCVio's `MixedMerkleTree.node` whose leaves hash the rows of the tallest matrices and
whose nodes at depth `t` inject the rows of the matrices of height `2 ^ t`. -/
def injNode (ms : List (Matrix F)) (k : Nat) : Nat → Nat → Vector F d :=
  MixedMerkleTree.node hash compress k (groupRows ms k) (injRows ms)

theorem injNode_zero (ms : List (Matrix F)) (k i : Nat) :
    injNode hash compress ms k 0 i = hash (groupRows ms k i) := rfl

/-- A node compresses its children, then, if some matrices have the height `2 ^ (k - l)` of its
layer, compresses that with the hash of their rows. -/
theorem injNode_succ (ms : List (Matrix F)) (k l i : Nat) :
    injNode hash compress ms k (l + 1) i =
      if ms.any (·.height == 2 ^ (k - (l + 1))) then
        compress (compress (injNode hash compress ms k l (2 * i))
          (injNode hash compress ms k l (2 * i + 1))) (hash (groupRows ms (k - (l + 1)) i))
      else compress (injNode hash compress ms k l (2 * i))
        (injNode hash compress ms k l (2 * i + 1)) := by
  simp only [injNode, MixedMerkleTree.node, injRows]
  split <;> rfl

/-- Reading a tabulated list. -/
theorem getD_map_range' {β : Type} (g : Nat → β) (n i : Nat) (x : β) (hi : i < n) :
    ((List.range n).map g).getD i x = g i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

/-- One layer up from a full layer of level `l`, injecting the matrices of height `2 ^ e`. -/
theorem nextLayer_inj (ms : List (Matrix F)) (k l e : Nat) (hk : l + 1 + e = k) :
    nextLayer hash compress (ms.filter (·.height == 2 ^ e))
        ((List.range (2 ^ (e + 1))).map (injNode hash compress ms k l)) =
      (List.range (2 ^ e)).map (injNode hash compress ms k (l + 1)) := by
  have hpow : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ, Nat.mul_comm]
  have he : k - (l + 1) = e := by omega
  simp only [nextLayer, List.length_map, List.length_range, hpow]
  rw [Nat.mul_div_cancel_left _ (by decide)]
  rw [padTo_of_length]
  · apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    rw [getD_map_range' _ _ _ _ (by omega), getD_map_range' _ _ _ _ (by omega)]
    simp only [injNode_succ, he]
    generalize hG : ms.filter (·.height == 2 ^ e) = G
    rcases G with _ | ⟨m, G⟩
    · have hany : ms.any (·.height == 2 ^ e) = false := by
        rw [List.filter_eq_nil_iff] at hG
        rw [List.any_eq_false]
        exact hG
      rw [hany]; rfl
    · have hm : m ∈ ms.filter (·.height == 2 ^ e) := by rw [hG]; exact List.mem_cons_self
      rw [List.mem_filter, beq_iff_eq] at hm
      have hany : ms.any (·.height == 2 ^ e) = true :=
        List.any_eq_true.mpr ⟨m, hm.1, by rw [hm.2, beq_self_eq_true]⟩
      simp only [hany, hm.2, ht, ↓reduceIte, groupRows, hG]
  · simp only [List.length_map, List.length_range]
    rcases e with _ | e
    · rfl
    · have := Nat.one_le_two_pow (n := e)
      have h2 : ¬2 * (2 ^ e * 2) = 2 := by omega
      simp only [Nat.pow_succ, h2, ↓reduceIte]
      omega

/-- The layers from a full layer of level `l` up, injecting the matrices of `R`, the matrices of
`ms` below the layer's height, tallest first. -/
theorem upperLayersAll_inj (ms : List (Matrix F)) (k : Nat) :
    ∀ (e l fuel : Nat) (R : List (Matrix F)), l + e = k → e ≤ fuel →
      R.Pairwise (fun a b ↦ b.height ≤ a.height) → (∀ m ∈ R, ∃ j < e, m.height = 2 ^ j) →
      (∀ j < e, R.filter (·.height == 2 ^ j) = ms.filter (·.height == 2 ^ j)) →
      upperLayersAll hash compress fuel R
          ((List.range (2 ^ e)).map (injNode hash compress ms k l)) =
        (List.range (e + 1)).map fun j ↦
          (List.range (2 ^ (e - j))).map (injNode hash compress ms k (l + j))
  | 0, l, fuel, R, _, _, _, _, _ => by
    cases fuel with
    | zero => rfl
    | succ fuel => simp only [upperLayersAll]; rfl
  | e + 1, l, fuel, R, hk, hfuel, hs, hR, hf => by
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlen : ¬ ((List.range (2 ^ (e + 1))).map (injNode hash compress ms k l)).length ≤ 1 := by
      simp only [List.length_map, List.length_range, Nat.pow_succ]
      have := Nat.one_le_two_pow (n := e); omega
    have hn : (((List.range (2 ^ (e + 1))).map (injNode hash compress ms k l)).length / 2
        ).nextPowerOfTwo = 2 ^ e := by
      simp only [List.length_map, List.length_range, Nat.pow_succ,
        Nat.mul_div_cancel _ (show 0 < 2 by decide), nextPowerOfTwo_two_pow]
    obtain ⟨h1, h2⟩ := takeWhile_height (2 ^ e) (·.height.nextPowerOfTwo == 2 ^ e) R
      (fun m hm ↦ by
        obtain ⟨j, -, hj⟩ := hR m hm
        rw [hj, nextPowerOfTwo_two_pow]) hs
      (fun m hm ↦ by
        obtain ⟨j, hj, hj'⟩ := hR m hm
        rw [hj']; exact Nat.pow_le_pow_right (by decide) (by omega))
    simp only [upperLayersAll, hlen, ite_false, hn]
    rw [h2, h1, hf e (by omega), nextLayer_inj hash compress ms k l e (by omega),
      upperLayersAll_inj ms k e (l + 1) fuel _ (by omega) (by omega)
        (hs.sublist List.filter_sublist)
        (fun m hm ↦ by
          rw [List.mem_filter, decide_eq_true_eq] at hm
          obtain ⟨j, -, hj⟩ := hR m hm.1
          refine ⟨j, ?_, hj⟩
          rw [hj] at hm
          exact (Nat.pow_lt_pow_iff_right (by decide)).mp hm.2)
        (fun j hj ↦ by
          rw [List.filter_filter, ← hf j (by omega)]
          refine List.filter_congr fun m _ ↦ ?_
          by_cases hm : m.height = 2 ^ j
          · rw [hm, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
            exact Nat.pow_lt_pow_right (by decide) hj
          · rw [beq_eq_false_iff_ne.mpr hm, Bool.false_and])]
    rw [List.range_succ_eq_map (n := e + 1), List.map_cons, List.map_map]
    simp only [Nat.add_zero, Nat.sub_zero]
    refine congrArg _ (List.map_congr_left fun j _ ↦ ?_)
    simp only [Function.comp_apply, Nat.succ_sub_succ, Nat.add_assoc, Nat.add_comm 1 j]

/-- The digest layers of matrices of heights `2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`: layer `j`
holds the nodes `injNode` at level `j`. -/
theorem layers_eq_injNode (ms : List (Matrix F)) (k : Nat)
    (hpow : ∀ m ∈ ms, ∃ j ≤ k, m.height = 2 ^ j) (htop : ∃ m ∈ ms, m.height = 2 ^ k) :
    layers hash compress ms = (List.range (k + 1)).map fun j ↦
      (List.range (2 ^ (k - j))).map (injNode hash compress ms k j) := by
  have hs := pairwise_sortTallest ms
  have hmem : ∀ m, m ∈ sortTallest ms ↔ m ∈ ms := fun m ↦ List.mem_mergeSort
  have hle : ∀ m ∈ sortTallest ms, m.height ≤ 2 ^ k := fun m hm ↦ by
    obtain ⟨j, hj, hj'⟩ := hpow m ((hmem m).mp hm)
    rw [hj']; exact Nat.pow_le_pow_right (by decide) hj
  obtain ⟨t, ht, htk⟩ := htop
  obtain ⟨s0, srest, hsr⟩ : ∃ s0 srest, sortTallest ms = s0 :: srest := by
    cases h : sortTallest ms with
    | nil => rw [← hmem, h] at ht; exact absurd ht List.not_mem_nil
    | cons s0 srest => exact ⟨s0, srest, rfl⟩
  have hs0 : s0.height = 2 ^ k := by
    have h1 := hle s0 (by rw [hsr]; exact List.mem_cons_self)
    have ht' : t ∈ s0 :: srest := by rw [← hsr, hmem]; exact ht
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact htk
    · have := List.rel_of_pairwise_cons (hsr ▸ hs) ht'
      omega
  obtain ⟨h1, h2⟩ := takeWhile_height (2 ^ k) (·.height == 2 ^ k) (sortTallest ms)
    (fun _ _ ↦ rfl) hs hle
  have hfirst : firstLayer hash ((sortTallest ms).takeWhile (·.height == 2 ^ k)) (2 ^ k) =
      (List.range (2 ^ k)).map (injNode hash compress ms k 0) := by
    rw [firstLayer, padEven_two_pow, padTo_of_length _ _ _ (by
      simp only [List.length_map, List.length_range])]
    refine List.map_congr_left fun i _ ↦ ?_
    rw [h1, filter_sortTallest]
    rfl
  unfold layers
  simp only [hsr, List.headD_cons, hs0]
  rw [← hsr, hfirst, h2]
  rw [upperLayersAll_inj hash compress ms k k 0 _ _ (by omega) (by
      simp only [List.length_map, List.length_range]; exact Nat.lt_two_pow_self.le)
    (hs.sublist List.filter_sublist)
    (fun m hm ↦ by
      rw [List.mem_filter, decide_eq_true_eq] at hm
      obtain ⟨j, -, hj⟩ := hpow m ((hmem m).mp hm.1)
      refine ⟨j, ?_, hj⟩
      rw [hj] at hm
      exact (Nat.pow_lt_pow_iff_right (by decide)).mp hm.2)
    (fun j hj ↦ by
      rw [List.filter_filter, ← filter_sortTallest ms (2 ^ j)]
      refine List.filter_congr fun m _ ↦ ?_
      by_cases hm : m.height = 2 ^ j
      · rw [hm, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
        exact Nat.pow_lt_pow_right (by decide) hj
      · rw [beq_eq_false_iff_ne.mpr hm, Bool.false_and])]
  simp only [Nat.zero_add]

/-- Matrices all of height `2 ^ k` inject nowhere: the nodes up to the root are those of the
perfect tree on the hashes of their rows. -/
theorem injNode_uniform (ms : List (Matrix F)) (k : Nat) (hms : ∀ m ∈ ms, m.height = 2 ^ k) :
    ∀ l ≤ k, ∀ i, injNode hash compress ms k l i = nodeValue compress (leafHashes hash ms) l i
  | 0, _, i => by
    rw [injNode_zero, nodeValue_zero, leafHashes, groupRows,
      List.filter_eq_self.mpr fun m hm ↦ by rw [hms m hm, beq_self_eq_true]]
  | l + 1, hl, i => by
    have hany : ms.any (·.height == 2 ^ (k - (l + 1))) = false := by
      rw [List.any_eq_false]
      intro m hm
      rw [hms m hm, beq_iff_eq]
      intro he
      have := Nat.pow_right_injective (le_refl 2) he
      omega
    rw [injNode_succ, hany, nodeValue_succ, injNode_uniform ms k hms l (by omega),
      injNode_uniform ms k hms l (by omega)]
    rfl

end Tree

/-! ### Honest multi-openings -/

section Honest
variable [Zero F] (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- Concatenating the images of a list's elements that pass `p`, by index. -/
theorem flatMap_filter_range {α β : Type} (l : List α) (x : α) (p : α → Bool) (g : α → List β) :
    ((List.range l.length).filter (fun i ↦ p (l.getD i x))).flatMap (fun i ↦ g (l.getD i x)) =
      (l.filter p).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    simp only [List.getD_cons_zero, List.filter_cons]
    by_cases hp : p a = true
    · simp only [hp, ↓reduceIte, List.flatMap_cons, List.flatMap_map]
      exact congrArg _ ih
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, List.flatMap_map]
      exact ih

/-- `(2 ^ k - 1) >>> (k - j) + 1 = 2 ^ j` for `j ≤ k`. -/
theorem shiftRight_two_pow_sub_one {j k : Nat} (hj : j ≤ k) :
    (2 ^ k - 1) >>> (k - j) + 1 = 2 ^ j := by
  have hk : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hj]
  have h1 := Nat.one_le_two_pow (n := j)
  have h2 := Nat.one_le_two_pow (n := k - j)
  have h3 : 1 ≤ 2 ^ j * 2 ^ (k - j) := Nat.mul_pos h1 h2
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt_le (k := 2 ^ j - 1)]
  · omega
  · rw [hk, Nat.sub_mul, Nat.one_mul]; omega
  · rw [hk, Nat.sub_add_cancel h1]; omega

end Honest

section Mixed
variable [Zero F] (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- **Honest multi-openings of mixed heights verify.** The multi-opening at `indices` of matrices
of heights `2 ^ j ≤ 2 ^ k`, some of height `2 ^ k` and none below the cap of height
`h = min capHeight k`, with every matrix's row at the index shifted to its height and the pruned
siblings of the tree's paths below the cap, is accepted against the tree's cap: its nodes `h`
levels below the root. -/
theorem verifyMulti_prune_mixed [DecidableEq F] (ms : List (Matrix F)) (k capHeight : Nat)
    (hpow : ∀ m ∈ ms, ∃ j ≤ k, m.height = 2 ^ j) (htop : ∃ m ∈ ms, m.height = 2 ^ k)
    (hcap : ∀ m ∈ ms, 2 ^ min capHeight k ≤ m.height)
    (indices : List Nat) (hidx : ∀ i ∈ indices, i < 2 ^ k) (paths : List (List (Vector F d)))
    (hpaths : ∀ q (hq : q < indices.length), ∀ j < k,
      (paths.getD q []).getD j 0 = injNode hash compress ms k j ((indices[q] >>> j) ^^^ 1)) :
    verifyMultiM (m := Id) hash compress
      ((List.range (2 ^ min capHeight k)).map
        (injNode hash compress ms k (k - min capHeight k))) capHeight
      (ms.map fun m ↦ (m.height, m.width)) indices
      (indices.map fun i ↦ ms.map fun m ↦ m.row (i >>> (k - Nat.log2 m.height)))
      (MixedMerkleTree.prune 0 (k - min capHeight k) indices paths) = true := by
  set N := injNode hash compress ms k with hN
  set rowsAt : Nat → List (List F) := fun i ↦ ms.map fun m ↦ m.row (i >>> (k - Nat.log2 m.height))
    with hrowsAt
  have hheights : (ms.map fun m ↦ (m.height, m.width)).map (·.1) = ms.map (·.height) := by
    rw [List.map_map]; rfl
  obtain ⟨keys, hk, hmem, hG⟩ := heightGroups_eq (ms.map (·.height))
  have hmem' : ∀ h, h ∈ keys ↔ ∃ m ∈ ms, m.height = h := fun h ↦ by
    rw [hmem, List.mem_map]
  have hpowK : ∀ h ∈ keys, ∃ j, h = 2 ^ j := fun h hh ↦ by
    obtain ⟨m, hm, rfl⟩ := (hmem' h).mp hh
    obtain ⟨j, -, hj⟩ := hpow m hm
    exact ⟨j, hj⟩
  have hleK : ∀ h ∈ keys, h ≤ 2 ^ k := fun h hh ↦ by
    obtain ⟨m, hm, rfl⟩ := (hmem' h).mp hh
    obtain ⟨j, hj, hj'⟩ := hpow m hm
    rw [hj']; exact Nat.pow_le_pow_right (by decide) hj
  have htopK : 2 ^ k ∈ keys := by
    obtain ⟨m, hm, hmk⟩ := htop
    exact (hmem' _).mpr ⟨m, hm, hmk⟩
  obtain ⟨ks, hks⟩ : ∃ ks, keys = 2 ^ k :: ks := by
    rcases keys with _ | ⟨a, ks⟩
    · exact absurd htopK List.not_mem_nil
    · refine ⟨ks, ?_⟩
      have ha := hleK a List.mem_cons_self
      rcases List.mem_cons.mp htopK with h | h
      · rw [h]
      · have := List.rel_of_pairwise_cons hk h; omega
  have hksl : ∀ h ∈ ks, h < 2 ^ k := fun h hh ↦ by
    have := List.rel_of_pairwise_cons (hks ▸ hk) hh; omega
  set idx : Nat → List Nat := fun h ↦
    (List.range (ms.map (·.height)).length).filter ((ms.map (·.height)).getD · 0 == h) with hidxdef
  -- The rows of a group at a query are the group's rows at the query's index.
  have hrows : ∀ q (hq : q < indices.length), ∀ j ≤ k,
      (idx (2 ^ j)).flatMap (fun k' ↦ (((indices.map rowsAt).getD q []).getD k' [])) =
        groupRows ms j (indices[q] >>> (k - j)) := by
    intro q hq j hj
    have hq' : (indices.map rowsAt).getD q [] = rowsAt indices[q] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq,
        Option.map_some, Option.getD_some]
    rw [hq', groupRows, ← flatMap_filter_range ms ⟨0, 0, #[]⟩]
    simp only [hidxdef, List.length_map]
    have hf : ((List.range ms.length).filter fun i ↦ (ms.map (·.height)).getD i 0 == 2 ^ j) =
        (List.range ms.length).filter fun i ↦ (ms.getD i ⟨0, 0, #[]⟩).height == 2 ^ j := by
      refine List.filter_congr fun i hi ↦ ?_
      rw [List.mem_range] at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some]
    rw [hf]
    refine List.flatMap_congr fun i hi ↦ ?_
    rw [List.mem_filter, List.mem_range, beq_iff_eq] at hi
    simp only [hrowsAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi.1, Option.map_some, Option.getD_some] at hi ⊢
    rw [hi.2, Nat.log2_two_pow]
  set h := min capHeight k with hh
  have hhk : h ≤ k := Nat.min_le_right _ _
  have hshape : multiShapeOk (ms.map fun m ↦ (m.height, m.width)) (2 ^ k) (k - h) indices
      (indices.map rowsAt) (MixedMerkleTree.prune 0 (k - h) indices paths) = true := by
    have hshift : ∀ m ∈ ms, log2Ceil (2 ^ k) - log2Ceil m.height = k - Nat.log2 m.height :=
      fun m hm ↦ by
        obtain ⟨j, -, hj⟩ := hpow m hm
        rw [hj, log2Ceil_two_pow, log2Ceil_two_pow, Nat.log2_two_pow]
    have hmemzip : ∀ a ∈ indices.zip (indices.map rowsAt), a.2 = rowsAt a.1 := fun a ha ↦ by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
      simp only [List.getElem_zip, List.getElem_map]
    simp only [multiShapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
      List.length_map]
    refine ⟨⟨⟨⟨⟨⟨fun x hx ↦ ?_, Nat.two_pow_pos k⟩, trivial⟩, fun r hr ↦ ?_⟩, hidx⟩, ?_⟩, ?_⟩
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, hj, hj'⟩ := hpow m hm
      dsimp only
      rw [hj', log2Ceil_two_pow, log2Ceil_two_pow, shiftRight_two_pow_sub_one hj]
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
      refine ⟨by simp only [hrowsAt, List.length_map], fun x hx ↦ ?_⟩
      rw [hrowsAt, List.zip_map'] at hx
      obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
      simp only [Matrix.row, List.length_map, List.length_range]
    · intro a ha b hb x hx
      rw [hmemzip a ha, hmemzip b hb, hrowsAt] at hx
      dsimp only at hx
      rw [List.zip_map', List.zip_map'] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      dsimp only
      rw [hshift m hm]
      by_cases he : a.1 >>> (k - Nat.log2 m.height) = b.1 >>> (k - Nat.log2 m.height)
      · rw [he, bne_self_eq_false, Bool.false_or, beq_self_eq_true]
      · rw [bne_iff_ne.mpr he, Bool.true_or]
    · rw [MixedMerkleTree.length_prune]
  set G := ks.map fun h ↦ (h, idx h) with hGdef
  have hGs : G.Pairwise fun a b ↦ b.1 < a.1 := List.pairwise_map.mpr ((hks ▸ hk).of_cons.imp id)
  have hGp : ∀ g ∈ G, ∃ j < k, g.1 = 2 ^ j := fun g hg ↦ by
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨j, rfl⟩ := hpowK g' (hks ▸ List.mem_cons_of_mem _ hg')
    exact ⟨j, (Nat.pow_lt_pow_iff_right (by decide)).mp (hksl _ hg'), rfl⟩
  have hcapRest : G.all (fun g ↦ 2 ^ h ≤ g.1.nextPowerOfTwo) = true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨m, hm, hmg⟩ := (hmem' g').mp (hks ▸ List.mem_cons_of_mem _ hg')
    obtain ⟨j, -, hj⟩ := hpow m hm
    have := hcap m hm
    rw [hj] at this
    rw [← hmg, hj, nextPowerOfTwo_two_pow]
    exact decide_eq_true this
  have hcapLen : ((List.range (2 ^ h)).map (N (k - h))).length == 2 ^ h := by
    rw [List.length_map, List.length_range, beq_self_eq_true]
  -- The nodes of the tree are the injected pairs, the payloads the walk's.
  have hNstep : ∀ l < k - h, ∀ q (hq : q < indices.length),
      N (l + 1) (indices[q] >>> (l + 1)) =
        MixedMerkleTree.inject hash compress
          ((walkPays (indices.map rowsAt) (k - h) G (2 ^ k) (k - h - (l + 1))).map (· q))
          (compress (N l (2 * (indices[q] >>> (l + 1))))
            (N l (2 * (indices[q] >>> (l + 1)) + 1))) := by
    intro l hl q hq
    have hpays : (walkPays (indices.map rowsAt) (k - h) G (2 ^ k) (k - h - (l + 1))).map (· q) =
        if 2 ^ (k - (l + 1)) ∈ ks then
          some (groupRows ms (k - (l + 1)) (indices[q] >>> (l + 1)))
        else none := by
      rw [walkPays, sched_eq_find (k - h) k G (Nat.sub_le _ _) hGs hGp _ (by omega),
        show k - h - (l + 1) + (k - (k - h)) = k - (l + 1) by omega]
      by_cases hin : 2 ^ (k - (l + 1)) ∈ ks
      · have hg : (2 ^ (k - (l + 1)), idx (2 ^ (k - (l + 1)))) ∈ G := List.mem_map_of_mem hin
        rw [find?_height_eq hGs hg]
        simp only [hin, ↓reduceIte, Option.map_some, Option.some.injEq]
        rw [hrows q hq _ (by omega), show k - (k - (l + 1)) = l + 1 by omega]
      · simp only [hin, ↓reduceIte]
        have : G.find? (fun g ↦ g.1 == 2 ^ (k - (l + 1))) = none := by
          rw [List.find?_eq_none]
          intro g hg
          obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
          simp only [beq_iff_eq]
          rintro rfl
          exact hin hg'
        rw [this]
        rfl
    have hany : ms.any (·.height == 2 ^ (k - (l + 1))) = decide (2 ^ (k - (l + 1)) ∈ ks) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨m, hm, hmh⟩
        rw [beq_iff_eq] at hmh
        have := (hmem' _).mpr ⟨m, hm, hmh⟩
        rw [hks] at this
        rcases List.mem_cons.mp this with e | e
        · have := Nat.pow_right_injective (le_refl 2) e
          omega
        · exact e
      · intro hin
        obtain ⟨m, hm, hmh⟩ := (hmem' _).mp (hks ▸ List.mem_cons_of_mem _ hin)
        exact ⟨m, hm, by rw [hmh, beq_self_eq_true]⟩
    rw [hpays, hN, injNode_succ, hany]
    by_cases hin : 2 ^ (k - (l + 1)) ∈ ks
    · simp only [hin, decide_true, ↓reduceIte, MixedMerkleTree.inject]
    · simp only [hin, decide_false, Bool.false_eq_true, ↓reduceIte, MixedMerkleTree.inject]
  unfold verifyMultiM
  rw [hheights, hG, hks, List.map_cons]
  dsimp only
  rw [capLevels_two_pow, nextPowerOfTwo_two_pow]
  dsimp only
  rw [← hh, ← hGdef]
  simp only [hshape, hcapLen, hcapRest, Bool.and_self, ↓reduceIte]
  have hleaves : ((MixedMerkleTree.frontier indices).mapM (m := Id) fun (x : Nat × Nat) ↦
      match x with
      | (i, q) => do
        return (i, q, ← hash ((idx (2 ^ k)).flatMap fun k' ↦
          ((indices.map rowsAt).getD q []).getD k' []))) =
        (MixedMerkleTree.frontier indices).map fun e ↦ (e.1, e.2, N 0 e.1) := by
    refine List.idRun_mapM.trans ?_
    apply List.map_congr_left
    rintro ⟨i, q⟩ he
    obtain ⟨hql, hqi⟩ := MixedMerkleTree.lead_of_mem_frontier he
    dsimp only at hql hqi ⊢
    rw [hrows q hql k le_rfl, Nat.sub_self, Nat.shiftRight_zero, hqi]
    rfl
  rw [hleaves]
  obtain ⟨ns', hns', hwalk⟩ := MixedMerkleTree.walk_prune hash compress 0 N indices (k - h)
    (walkPays (indices.map rowsAt) (k - h) G (2 ^ k)) paths
    (fun q hq j hj ↦ hpaths q hq j (by omega)) hNstep
  change ((walkM (m := Id) hash compress (indices.map rowsAt) (k - h) G (2 ^ k)
    ((MixedMerkleTree.frontier indices).map fun e ↦ (e.1, e.2, N 0 e.1))
    (MixedMerkleTree.prune 0 (k - h) indices paths)).1.all
    fun (x : Nat × Nat × Vector F d) ↦ x.2.2 == ((List.range (2 ^ h)).map (N (k - h))).getD x.1 0)
      = true
  rw [walkM_eq, hwalk, List.all_eq_true]
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hq, hi⟩ := hns' e he
  have hlt : e.1 < 2 ^ h := by
    rw [← hi, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      ← Nat.pow_add, Nat.add_sub_cancel' hhk]
    exact hidx _ (List.getElem_mem hq)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
    Option.map_some, Option.getD_some, beq_self_eq_true]

end Mixed

end CompStark.Merkle
