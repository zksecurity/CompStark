/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Multi

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

/-- The node at level `l` and index `i` of the tree of matrices `ms` of heights at most
`2 ^ k`: a leaf hashes the rows of the tallest matrices; a node compresses its children, then, if
some matrices have the height `2 ^ (k - l)` of its layer, compresses that with the hash of their
rows. -/
def injNode (ms : List (Matrix F)) (k : Nat) : Nat → Nat → Vector F d
  | 0, i => hash (groupRows ms k i)
  | l + 1, i =>
    let p := compress (injNode ms k l (2 * i)) (injNode ms k l (2 * i + 1))
    if ms.any (·.height == 2 ^ (k - (l + 1))) then
      compress p (hash (groupRows ms (k - (l + 1)) i))
    else p

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
    simp only [injNode, he]
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
    rw [injNode, nodeValue_zero, leafHashes, groupRows,
      List.filter_eq_self.mpr fun m hm ↦ by rw [hms m hm, beq_self_eq_true]]
  | l + 1, hl, i => by
    have hany : ms.any (·.height == 2 ^ (k - (l + 1))) = false := by
      rw [List.any_eq_false]
      intro m hm
      rw [hms m hm, beq_iff_eq]
      intro he
      have := Nat.pow_right_injective (le_refl 2) he
      omega
    rw [injNode, hany, nodeValue_succ, injNode_uniform ms k hms l (by omega),
      injNode_uniform ms k hms l (by omega)]
    rfl

end Tree

/-! ### Honest multi-openings -/

section Honest
variable (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
  (N : Nat → Nat → Vector F d)

/-- The nodes of a level, each with its digest `N l i`. -/
def nodesOf (l : Nat) (ns : List (Nat × Nat)) : List (Nat × Nat × Vector F d) :=
  ns.map fun e ↦ (e.1, e.2, N l e.1)

/-- The compression of the children of node `t` one level up from level `l`. -/
def pairOf (l t : Nat) : Vector F d := compress (N l (2 * t)) (N l (2 * t + 1))

/-- A node compressed with its sibling, on the node's side, is the pair of its parent. -/
theorem pairOf_parent (l i : Nat) :
    (if i % 2 = 0 then compress (N l i) (N l (i ^^^ 1)) else compress (N l (i ^^^ 1)) (N l i)) =
      pairOf compress N l (i / 2) := by
  have hx : i ^^^ 1 = if i % 2 = 0 then i + 1 else i - 1 := by
    rw [show i ^^^ 1 = 2 * (i / 2) + (i + 1) % 2 from by
      have h1 : (i ^^^ 1) / 2 = i / 2 := by
        rw [Nat.xor_div_two]; simp only [Nat.reduceDiv, Nat.xor_zero]
      have h2 : (i ^^^ 1) % 2 = (i + 1) % 2 := by
        have := Nat.xor_mod_two_pow (a := i) (b := 1) (n := 1)
        rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
          simp only [Nat.pow_one, h, Nat.one_mod, Nat.reduceXor] at this <;> omega
      have := Nat.div_add_mod (i ^^^ 1) 2
      omega]
    split <;> omega
  unfold pairOf
  by_cases h : i % 2 = 0
  · simp only [hx, h, ↓reduceIte]
    congr 2 <;> omega
  · simp only [hx, h, ↓reduceIte]
    congr 2 <;> omega

variable [Zero F]

/-- One level of the honest walk: the pruned siblings of the leads' paths take the frontier's
nodes to the pairs of their parents. -/
theorem level_pruneOf (paths : List (List (Vector F d))) (l : Nat) :
    ∀ (ns : List (Nat × Nat)) (rest : List (Vector F d)),
      (∀ e ∈ ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1)) →
      level compress (nodesOf N l ns) ((pruneLevel paths l ns).2 ++ rest) =
        (nodesOf (fun l t ↦ pairOf compress N l t) l (pruneLevel paths l ns).1, rest)
  | [], rest, _ => rfl
  | [(i, q)], rest, h => by
    simp only [nodesOf, List.map_cons, List.map_nil, pruneLevel, List.singleton_append,
      level_single, List.headD_cons, List.tail_cons]
    rw [h (i, q) (List.mem_singleton_self _), pairOf_parent]
  | (i, q) :: (j, q') :: ns, rest, h => by
    have h1 := h (i, q) List.mem_cons_self
    have hj : ∀ e ∈ (j, q') :: ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1) :=
      fun e he ↦ h e (List.mem_cons_of_mem _ he)
    have hns : ∀ e ∈ ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1) :=
      fun e he ↦ hj e (List.mem_cons_of_mem _ he)
    simp only [nodesOf, List.map_cons]
    rw [level_cons_cons]
    simp only [pruneLevel]
    split
    · rename_i hp
      obtain ⟨he, rfl⟩ := hp
      have := level_pruneOf paths l ns rest hns
      simp only [nodesOf] at this
      rw [this]
      simp only [List.map_cons, pairOf]
      rw [show 2 * (i / 2) = i by omega]
    · have := level_pruneOf paths l ((j, q') :: ns) rest hj
      simp only [nodesOf, List.map_cons] at this
      simp only [List.cons_append, List.headD_cons, List.tail_cons, this, h1, pairOf_parent,
        List.map_cons]

/-- A walk step injecting the group `(h, is)` when its height is the next layer's. -/
theorem walkM_succ_cons (rows : List (List (List F))) (levels h : Nat) (is : List Nat)
    (rest : List (Nat × List Nat)) (padded : Nat) (nodes : List (Nat × Nat × Vector F d))
    (sibs : List (Vector F d)) :
    walkM (m := Id) hash compress rows (levels + 1) ((h, is) :: rest) padded nodes sibs =
      if h.nextPowerOfTwo = padded / 2 then
        walkM (m := Id) hash compress rows levels rest (padded / 2)
          ((level compress nodes sibs).1.map fun x ↦
            (x.1, x.2.1, compress x.2.2 (hash (is.flatMap fun k ↦ (rows.getD x.2.1 []).getD k []))))
          (level compress nodes sibs).2
      else walkM (m := Id) hash compress rows levels ((h, is) :: rest) (padded / 2)
        (level compress nodes sibs).1 (level compress nodes sibs).2 := by
  simp only [walkM]
  split
  · exact congrArg (fun ps ↦ walkM (m := Id) hash compress rows levels rest (padded / 2) ps
      (level compress nodes sibs).2) List.idRun_mapM
  · rfl

/-- A walk step without groups left. -/
theorem walkM_succ_nil (rows : List (List (List F))) (levels padded : Nat)
    (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) :
    walkM (m := Id) hash compress rows (levels + 1) [] padded nodes sibs =
      walkM (m := Id) hash compress rows levels [] (padded / 2) (level compress nodes sibs).1
        (level compress nodes sibs).2 := rfl

end Honest

/-- In a strictly decreasing list, the elements below `B` are its largest such element `x`
followed by those below `x`. -/
theorem filter_lt_of_max : ∀ (L : List Nat) (x B : Nat), L.Pairwise (· > ·) → x ∈ L → x < B →
    (∀ y ∈ L, y < B → y ≤ x) → L.filter (· < B) = x :: L.filter (· < x)
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: L, x, B, hs, hx, hxB, hmax => by
    have hL : ∀ y ∈ L, y < a := fun y hy ↦ List.rel_of_pairwise_cons hs hy
    by_cases ha : a < B
    · have hax : a ≤ x := hmax a List.mem_cons_self ha
      have hxa : x = a := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · have := hL x hx; omega
      subst hxa
      rw [List.filter_cons_of_pos (p := fun y ↦ decide (y < B)) (decide_eq_true ha),
        List.filter_cons_of_neg (p := fun y ↦ decide (y < x)) (by
          simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true, not_false_eq_true]),
        List.filter_eq_self.mpr fun y hy ↦ decide_eq_true (lt_trans (hL y hy) ha),
        List.filter_eq_self.mpr fun y hy ↦ decide_eq_true (hL y hy)]
    · have hxL : x ∈ L := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hxB ha
        · exact hx
      rw [List.filter_cons_of_neg (by rw [decide_eq_true_eq]; exact ha),
        List.filter_cons_of_neg (by rw [decide_eq_true_eq]; omega),
        filter_lt_of_max L x B hs.of_cons hxL hxB fun y hy ↦ hmax y (List.mem_cons_of_mem _ hy)]

/-- Heights `2 ^ j`, tallest first: those below `2 ^ (e + 1)` are `2 ^ e`, if present, then those
below `2 ^ e`. -/
theorem filter_keys_step (keys : List Nat) (hkeys : keys.Pairwise (· > ·))
    (hpow : ∀ h ∈ keys, ∃ j, h = 2 ^ j) (e : Nat) :
    (2 ^ e ∈ keys → keys.filter (· < 2 ^ (e + 1)) = 2 ^ e :: keys.filter (· < 2 ^ e)) ∧
      (2 ^ e ∉ keys → keys.filter (· < 2 ^ (e + 1)) = keys.filter (· < 2 ^ e)) := by
  refine ⟨fun hin ↦ filter_lt_of_max keys _ _ hkeys hin
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self e)) fun y hy hyB ↦ ?_, fun hin ↦ ?_⟩
  · obtain ⟨j, rfl⟩ := hpow y hy
    have := (Nat.pow_lt_pow_iff_right (by decide)).mp hyB
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · refine List.filter_congr fun y hy ↦ ?_
    obtain ⟨j, rfl⟩ := hpow y hy
    have hj : j ≠ e := fun h ↦ hin (h ▸ hy)
    simp only [decide_eq_decide, Nat.pow_lt_pow_iff_right (show 1 < 2 by decide)]
    omega

section Honest
variable [Zero F] (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
  (N : Nat → Nat → Vector F d)

/-- **The honest walk with injections.** From the frontier `ns` at level `l`, whose leads open the
paths of the tree of nodes `N`, the walk over `levels` levels injecting the groups of heights
`keys` below the layer's, of indices `idx`, ends at the nodes `N` of its parents, when every node
`N` is the pair of its children, compressed with the hash of the injected rows of its lead if a
group has its layer's height. -/
theorem walk_inj (rows : List (List (List F))) (indices : List Nat) (k : Nat) (keys : List Nat)
    (idx : Nat → List Nat) (hkeys : keys.Pairwise (· > ·)) (hpow : ∀ h ∈ keys, ∃ j, h = 2 ^ j)
    (paths : List (List (Vector F d)))
    (hpaths : ∀ q (hq : q < indices.length), ∀ j < k,
      (paths.getD q []).getD j 0 = N j ((indices[q] >>> j) ^^^ 1))
    (hN : ∀ l < k, ∀ q (hq : q < indices.length),
      N (l + 1) (indices[q] >>> (l + 1)) =
        if 2 ^ (k - (l + 1)) ∈ keys then
          compress (pairOf compress N l (indices[q] >>> (l + 1)))
            (hash ((idx (2 ^ (k - (l + 1)))).flatMap fun k' ↦ (rows.getD q []).getD k' []))
        else pairOf compress N l (indices[q] >>> (l + 1))) :
    ∀ (levels l : Nat) (ns : List (Nat × Nat)) (rest : List (Vector F d)),
      l + levels ≤ k → (∀ e ∈ ns, ∃ h : e.2 < indices.length, indices[e.2] >>> l = e.1) →
      ∃ ns' : List (Nat × Nat), (∀ e ∈ ns', ∃ h : e.2 < indices.length,
          indices[e.2] >>> (l + levels) = e.1) ∧
        walkM (m := Id) hash compress rows levels
          ((keys.filter (· < 2 ^ (k - l))).map fun h ↦ (h, idx h)) (2 ^ (k - l))
          (nodesOf N l ns) (pruneWalk paths levels l ns ++ rest) =
          (nodesOf N (l + levels) ns', rest)
  | 0, l, ns, rest, _, hns => ⟨ns, hns, rfl⟩
  | levels + 1, l, ns, rest, hk, hns => by
    have hlev : ∀ e ∈ ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1) := fun e he ↦ by
      obtain ⟨hq, hi⟩ := hns e he
      rw [hpaths e.2 hq l (by omega), hi]
    have hpar : ∀ e ∈ (pruneLevel paths l ns).1, ∃ h : e.2 < indices.length,
        indices[e.2] >>> (l + 1) = e.1 := fun e' he' ↦ by
      obtain ⟨e, he, rfl⟩ := pruneLevel_parents paths l ns e' he'
      obtain ⟨hq, hi⟩ := hns e he
      exact ⟨hq, by rw [shiftRight_succ, hi]⟩
    obtain ⟨e, he⟩ : ∃ e, k - (l + 1) = e := ⟨_, rfl⟩
    have hkl : k - l = e + 1 := by omega
    have hpad : 2 ^ (e + 1) / 2 = 2 ^ e := by
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    have hlevel := level_pruneOf compress N paths l ns (pruneWalk paths levels (l + 1)
      (pruneLevel paths l ns).1 ++ rest) hlev
    obtain ⟨ns', h1, h2⟩ := walk_inj rows indices k keys idx hkeys hpow paths hpaths hN levels
      (l + 1) (pruneLevel paths l ns).1 rest (by omega) hpar
    rw [he] at h2
    refine ⟨ns', by rw [show l + (levels + 1) = l + 1 + levels by omega]; exact h1, ?_⟩
    rw [show l + (levels + 1) = l + 1 + levels by omega, ← h2]
    simp only [pruneWalk, List.append_assoc]
    obtain ⟨hin, hout⟩ := filter_keys_step keys hkeys hpow e
    rw [hkl]
    by_cases hk' : 2 ^ e ∈ keys
    · rw [hin hk', List.map_cons, walkM_succ_cons, hpad, nextPowerOfTwo_two_pow,
        ite_eq_left rfl, hlevel]
      refine congrArg₂ _ ?_ rfl
      simp only [nodesOf, List.map_map]
      refine List.map_congr_left fun x hx ↦ ?_
      obtain ⟨hq, hi⟩ := hpar x hx
      simp only [Function.comp_apply]
      rw [← hi, hN l (by omega) x.2 hq, he, ite_eq_left hk']
    · rw [hout hk']
      have hnodes : nodesOf (fun l t ↦ pairOf compress N l t) l (pruneLevel paths l ns).1 =
          nodesOf N (l + 1) (pruneLevel paths l ns).1 := by
        refine List.map_congr_left fun x hx ↦ ?_
        obtain ⟨hq, hi⟩ := hpar x hx
        rw [← hi, hN l (by omega) x.2 hq, he, ite_eq_right hk']
      generalize hG : (keys.filter (· < 2 ^ e)).map (fun h ↦ (h, idx h)) = G
      rcases G with _ | ⟨⟨h, is⟩, G⟩
      · rw [walkM_succ_nil, hlevel, hnodes, hpad]
      · have hh : h ∈ keys.filter (· < 2 ^ e) := by
          have : (h, is) ∈ (keys.filter (· < 2 ^ e)).map (fun h ↦ (h, idx h)) := by
            rw [hG]; exact List.mem_cons_self
          obtain ⟨h', hh', he'⟩ := List.mem_map.mp this
          rw [Prod.mk.injEq] at he'
          rwa [← he'.1]
        rw [List.mem_filter, decide_eq_true_eq] at hh
        obtain ⟨j, rfl⟩ := hpow h hh.1
        have hne : (2 ^ j).nextPowerOfTwo ≠ 2 ^ (e + 1) / 2 := by
          rw [nextPowerOfTwo_two_pow, hpad]
          exact Nat.ne_of_lt hh.2
        rw [walkM_succ_cons, ite_eq_right hne, hlevel, hnodes, hpad]

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
      (prune (k - min capHeight k) indices paths) = true := by
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
  -- The nodes of the tree are the injected pairs.
  have hNstep : ∀ l < k, ∀ q (hq : q < indices.length),
      N (l + 1) (indices[q] >>> (l + 1)) =
        if 2 ^ (k - (l + 1)) ∈ keys then
          compress (pairOf compress N l (indices[q] >>> (l + 1)))
            (hash ((idx (2 ^ (k - (l + 1)))).flatMap fun k' ↦
              ((indices.map rowsAt).getD q []).getD k' []))
        else pairOf compress N l (indices[q] >>> (l + 1)) := by
    intro l hl q hq
    have hany : ms.any (·.height == 2 ^ (k - (l + 1))) = decide (2 ^ (k - (l + 1)) ∈ keys) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, hmem']
      simp only [beq_iff_eq]
    rw [hrows q hq _ (by omega), show k - (k - (l + 1)) = l + 1 by omega]
    simp only [hN, injNode, pairOf, hany]
    by_cases h : 2 ^ (k - (l + 1)) ∈ keys
    · simp only [h, decide_true, ↓reduceIte]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
  set h := min capHeight k with hh
  have hhk : h ≤ k := Nat.min_le_right _ _
  have hshape : multiShapeOk (ms.map fun m ↦ (m.height, m.width)) (2 ^ k) (k - h) indices
      (indices.map rowsAt) (prune (k - h) indices paths) = true := by
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
    · rw [prune, length_pruneWalk]
  have hrest : ks.map (fun h ↦ (h, idx h)) =
      (keys.filter (· < 2 ^ (k - 0))).map fun h ↦ (h, idx h) := by
    rw [Nat.sub_zero, hks, List.filter_cons_of_neg (by simp only [Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, not_false_eq_true]), List.filter_eq_self.mpr fun h hh ↦
        decide_eq_true (hksl h hh)]
  have hcapRest : ((keys.filter (· < 2 ^ (k - 0))).map fun g ↦ (g, idx g)).all
      (fun g ↦ 2 ^ h ≤ g.1.nextPowerOfTwo) = true := by
    rw [← hrest, List.all_eq_true]
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
  unfold verifyMultiM
  rw [hheights, hG, hks, List.map_cons]
  dsimp only
  rw [capLevels_two_pow, nextPowerOfTwo_two_pow]
  dsimp only
  rw [← hh, hrest]
  simp only [hshape, hcapLen, hcapRest, Bool.and_self, ↓reduceIte]
  have hleaves : ((frontier indices).mapM (m := Id) fun (x : Nat × Nat) ↦ match x with
      | (i, q) => do
        return (i, q, ← hash ((idx (2 ^ k)).flatMap fun k' ↦
          ((indices.map rowsAt).getD q []).getD k' []))) =
        nodesOf N 0 (frontier indices) := by
    rw [nodesOf]
    refine List.idRun_mapM.trans ?_
    apply List.map_congr_left
    rintro ⟨i, q⟩ he
    obtain ⟨hi, hq⟩ := mem_frontier.mp he
    dsimp only at hi hq ⊢
    have hql : q < indices.length := hq ▸ List.idxOf_lt_length_of_mem hi
    have hqi : indices[q] = i := by subst hq; exact List.getElem_idxOf hql
    rw [hrows q hql k le_rfl, Nat.sub_self, Nat.shiftRight_zero, hqi]
    rfl
  rw [hleaves]
  obtain ⟨ns', hns', hwalk⟩ := walk_inj hash compress N (indices.map rowsAt) indices k keys idx hk
    hpowK paths hpaths hNstep (k - h) 0 (frontier indices) [] (by omega) fun ⟨i, q⟩ he ↦ by
      obtain ⟨hi, hq⟩ := mem_frontier.mp he
      dsimp only at hi hq ⊢
      subst hq
      have hql : indices.idxOf i < indices.length := List.idxOf_lt_length_of_mem hi
      exact ⟨hql, by rw [Nat.shiftRight_zero]; exact List.getElem_idxOf hql⟩
  rw [Nat.sub_zero] at hwalk
  rw [Nat.sub_zero, prune, ← List.append_nil (pruneWalk paths (k - h) 0 (frontier indices))]
  change ((walkM (m := Id) hash compress _ (k - h) _ (2 ^ k) _ _).1.all
    fun (x : Nat × Nat × Vector F d) ↦ x.2.2 == ((List.range (2 ^ h)).map (N (k - h))).getD x.1 0)
      = true
  rw [hwalk, List.all_eq_true]
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hq, hi⟩ := hns' e he
  have hlt : e.1 < 2 ^ h := by
    rw [← hi, Nat.zero_add, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      ← Nat.pow_add, Nat.add_sub_cancel' hhk]
    exact hidx _ (List.getElem_mem hq)
  simp only [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some, beq_self_eq_true]



end Mixed

end CompStark.Merkle
