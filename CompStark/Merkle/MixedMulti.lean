/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Mixed

/-! # Accepted multi-openings

`verifyBatch_of_verifyMulti_mixed`: an accepted multi-opening of matrices of heights
`2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`, gives every query an accepted single opening
(`verifyBatch`) of its rows; `verifyBatch_of_verifyMulti` for matrices of one height. The walk is
VCVio's (`walkM_eq`), and VCVio's `MixedMerkleTree.exists_climb_of_walk` restores each query's
path, given that the queries below a node where the walk injects the hash of a group of shorter
matrices open the same rows of those matrices, as the multi-opening's shape check demands
(`multiShapeOk_rows`). The query's climb is then Plonky3's climb in the subtree under its cap
entry (`climb_scale`).
-/

@[expose] public section
namespace CompStark.Merkle

variable {F : Type} {d : Nat}

/-! ### The shape check -/

/-- The shape checks of a multi-opening: as many rows as indices, a row per matrix in each,
indices below the tallest height, and equal rows of a matrix wherever two queries' indices,
shifted to its height, agree. -/
theorem multiShapeOk_rows [DecidableEq F] {dims : List (Nat × Nat)} {maxH levels : Nat}
    {indices : List Nat} {rows : List (List (List F))} {sibs : List (Vector F d)}
    (h : multiShapeOk dims maxH levels indices rows sibs = true) :
    rows.length = indices.length ∧ (∀ r < rows.length, (rows.getD r []).length = dims.length) ∧
      (∀ r (hr : r < indices.length), indices[r] < maxH) ∧
      ∀ r q (hr : r < indices.length) (hq : q < indices.length) (m : Nat) (hm : m < dims.length),
        indices[r] >>> (log2Ceil maxH - log2Ceil dims[m].1) =
          indices[q] >>> (log2Ceil maxH - log2Ceil dims[m].1) →
        (rows.getD r []).getD m [] = (rows.getD q []).getD m [] := by
  simp only [multiShapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hrl⟩, hw⟩, hidx⟩, hcons⟩, -⟩ := h
  have hgetD : ∀ r (hr : r < rows.length), rows.getD r [] = rows[r] := fun r hr ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  have hrow : ∀ r < rows.length, (rows.getD r []).length = dims.length := fun r hr ↦ by
    rw [hgetD r hr]
    exact (hw _ (List.getElem_mem hr)).1
  refine ⟨hrl, hrow, fun r hr ↦ hidx _ (List.getElem_mem hr), fun r q hr hq m hm he ↦ ?_⟩
  have hr' : r < rows.length := hrl ▸ hr
  have hq' : q < rows.length := hrl ▸ hq
  have hmem : ∀ j (hj : j < indices.length), (indices[j], rows.getD j []) ∈ indices.zip rows :=
    fun j hj ↦ by
      rw [hgetD j (hrl ▸ hj)]
      exact List.mem_iff_getElem.mpr ⟨j, by rw [List.length_zip]; omega,
        by rw [List.getElem_zip]⟩
  have hc := hcons _ (hmem r hr) _ (hmem q hq)
  have hmr : m < (rows.getD r []).length := by rw [hrow r hr']; exact hm
  have hmq : m < (rows.getD q []).length := by rw [hrow q hq']; exact hm
  have := hc (dims[m], (rows.getD r [])[m], (rows.getD q [])[m]) (List.mem_iff_getElem.mpr
    ⟨m, by simp only [List.length_zip]; omega, by simp only [List.getElem_zip]⟩)
  dsimp only at this
  rw [he, bne_self_eq_false, Bool.false_or, beq_iff_eq] at this
  have h1 : (rows.getD r []).getD m [] = (rows.getD r [])[m] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmr, Option.getD_some]
  have h2 : (rows.getD q []).getD m [] = (rows.getD q [])[m] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmq, Option.getD_some]
  rw [h1, h2, this]

/-! ### Subtrees under a cap -/

section Scale

/-- `v` is `0` or a power of two of at least `2 ^ c`. -/
def ScaleOk (c v : Nat) : Prop := v = 0 ∨ ∃ j, c ≤ j ∧ v = 2 ^ j

theorem div_two_pow_le_iff {c u v : Nat} (hu : ScaleOk c u) (hv : ScaleOk c v) :
    u / 2 ^ c ≤ v / 2 ^ c ↔ u ≤ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ Nat.div_le_div_right h⟩
  rcases hu with rfl | ⟨j, hj, rfl⟩
  · exact Nat.zero_le _
  rcases hv with rfl | ⟨i, hi, rfl⟩
  · rw [Nat.pow_div hj (by decide), Nat.zero_div] at h
    exact absurd h (Nat.not_le.mpr (Nat.two_pow_pos _))
  rw [Nat.pow_div hj (by decide), Nat.pow_div hi (by decide)] at h
  exact Nat.pow_le_pow_right (by decide)
    (by have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h; omega)

theorem div_two_pow_inj {c u v : Nat} (hu : ScaleOk c u) (hv : ScaleOk c v) :
    u / 2 ^ c = v / 2 ^ c ↔ u = v := by
  constructor
  · intro h
    exact Nat.le_antisymm ((div_two_pow_le_iff hu hv).mp h.le) ((div_two_pow_le_iff hv hu).mp h.ge)
  · intro h; rw [h]

/-- Heights that are powers of two of at least `2 ^ c` group as their quotients by `2 ^ c`. -/
theorem heightGroups_scale (heights : List Nat) (c : Nat)
    (hpow : ∀ h ∈ heights, ∃ j, c ≤ j ∧ h = 2 ^ j) :
    heightGroups (heights.map (· / 2 ^ c)) =
      (heightGroups heights).map fun g ↦ (g.1 / 2 ^ c, g.2) := by
  have hget : ∀ i, (heights.map (· / 2 ^ c)).getD i 0 = heights.getD i 0 / 2 ^ c := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases heights[i]? with
    | none => simp only [Option.map_none, Option.getD_none, Nat.zero_div]
    | some x => simp only [Option.map_some, Option.getD_some]
  have hok : ∀ i, ScaleOk c (heights.getD i 0) := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases hi : heights[i]? with
    | none => exact Or.inl rfl
    | some x => exact Or.inr (hpow x (List.mem_of_getElem? hi))
  have hcmp : (fun a b ↦ decide ((heights.map (· / 2 ^ c)).getD b 0 ≤
      (heights.map (· / 2 ^ c)).getD a 0)) =
      fun a b ↦ decide (heights.getD b 0 ≤ heights.getD a 0) := by
    funext a b
    rw [hget, hget]
    exact decide_eq_decide.mpr (div_two_pow_le_iff (hok b) (hok a))
  unfold heightGroups
  simp only [List.length_map]
  rw [hcmp]
  generalize (List.range heights.length).mergeSort _ = sorted
  -- The groups of the original heights, by a fold.
  let step : Nat → List (Nat × List Nat) → List (Nat × List Nat) := fun i gs ↦
    match gs with
    | (h, is) :: rest =>
      if heights.getD i 0 = h then (h, i :: is) :: rest else (heights.getD i 0, [i]) :: gs
    | [] => [(heights.getD i 0, [i])]
  let step' : Nat → List (Nat × List Nat) → List (Nat × List Nat) := fun i gs ↦
    match gs with
    | (h, is) :: rest => if (heights.map (· / 2 ^ c)).getD i 0 = h then (h, i :: is) :: rest
        else ((heights.map (· / 2 ^ c)).getD i 0, [i]) :: gs
    | [] => [((heights.map (· / 2 ^ c)).getD i 0, [i])]
  suffices h : ∀ l : List Nat, (∀ g ∈ l.foldr step [], ScaleOk c g.1) ∧
      l.foldr step' [] = (l.foldr step []).map fun g ↦ (g.1 / 2 ^ c, g.2) from (h sorted).2
  intro l
  induction l with
  | nil => exact ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl⟩
  | cons i l ih =>
    obtain ⟨hall, heq⟩ := ih
    rw [List.foldr_cons, List.foldr_cons, heq]
    generalize List.foldr step [] l = G at hall ⊢
    rcases G with _ | ⟨⟨h, is⟩, rest⟩
    · refine ⟨fun g hg ↦ ?_, ?_⟩
      · simp only [step, List.mem_singleton] at hg
        rw [hg]; exact hok i
      · simp only [step, step', hget, List.map_cons, List.map_nil]
    · have hh : ScaleOk c h := hall _ List.mem_cons_self
      by_cases he : heights.getD i 0 = h
      · refine ⟨fun g hg ↦ ?_, ?_⟩
        · simp only [step, he, ↓reduceIte, List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact hh
          · exact hall g (List.mem_cons_of_mem _ hg)
        · simp only [step, step', hget, he, ↓reduceIte, List.map_cons]
      · refine ⟨fun g hg ↦ ?_, ?_⟩
        · simp only [step, he, ↓reduceIte, List.mem_cons] at hg
          rcases hg with rfl | rfl | hg
          · exact hok i
          · exact hh
          · exact hall g (List.mem_cons_of_mem _ hg)
        · have he' : ¬heights.getD i 0 / 2 ^ c = h / 2 ^ c := by
            rw [div_two_pow_inj (hok i) hh]; exact he
          simp only [step, step', hget, he, he', ↓reduceIte, List.map_cons]

variable (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- A climb of `l` levels to the layer of padded height `2 ^ c`, its groups of heights powers of
two of at least `2 ^ c`, is the climb in the subtree: the heights and the padded height divided
by `2 ^ c`, at the index's low `l` bits. -/
theorem climb_scale (values : List (List F)) (c : Nat) :
    ∀ (path : List (Vector F d)) (groups : List (Nat × List Nat)) (i : Nat) (root : Vector F d),
      (∀ g ∈ groups, ∃ j, c ≤ j ∧ g.1 = 2 ^ j) →
      climb hash compress values path groups i (2 ^ (path.length + c)) root =
        climb hash compress values path (groups.map fun g ↦ (g.1 / 2 ^ c, g.2))
          (i % 2 ^ path.length) (2 ^ path.length) root
  | [], _, _, _, _ => rfl
  | s :: path, groups, i, root, hg => by
    have h2 : i % 2 ^ (path.length + 1) % 2 = i % 2 :=
      Nat.mod_mod_of_dvd i (Nat.dvd_of_mod_eq_zero (by rw [Nat.pow_succ, Nat.mul_mod_left]))
    have hd : i % 2 ^ (path.length + 1) / 2 = i / 2 % 2 ^ path.length := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    have hp : 2 ^ (path.length + 1 + c) / 2 = 2 ^ (path.length + c) := by
      rw [show path.length + 1 + c = path.length + c + 1 by omega, Nat.pow_succ,
        Nat.mul_div_cancel _ (by decide)]
    have hp' : 2 ^ (path.length + 1) / 2 = 2 ^ path.length := by
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    rcases groups with _ | ⟨⟨h, is⟩, rest⟩
    · simp only [List.length_cons, climb, h2, hd, hp, hp', List.map_nil]
      have := climb_scale values c path [] (i / 2) (if i % 2 = 0 then compress root s
        else compress s root) (by simp only [List.not_mem_nil, false_imp_iff, implies_true])
      simpa only [List.map_nil] using this
    · obtain ⟨j, hj, hh⟩ := hg (h, is) List.mem_cons_self
      have hrest : ∀ g ∈ rest, ∃ j, c ≤ j ∧ g.1 = 2 ^ j :=
        fun g hg' ↦ hg g (List.mem_cons_of_mem _ hg')
      simp only at hh
      have hcond : (h.nextPowerOfTwo = 2 ^ (path.length + c)) ↔
          ((h / 2 ^ c).nextPowerOfTwo = 2 ^ path.length) := by
        rw [hh, Nat.pow_div hj (by decide), nextPowerOfTwo_two_pow, nextPowerOfTwo_two_pow]
        constructor
        · intro e; have := Nat.pow_right_injective (le_refl 2) e; rw [this]; congr 1; omega
        · intro e; have := Nat.pow_right_injective (le_refl 2) e; congr 1; omega
      simp only [List.length_cons, List.map_cons, climb, h2, hd, hp, hp']
      by_cases hc : h.nextPowerOfTwo = 2 ^ (path.length + c)
      · simp only [hc, hcond.mp hc, ↓reduceIte]
        exact climb_scale values c path rest (i / 2) _ hrest
      · simp only [hc, (not_congr hcond).mp hc, ↓reduceIte]
        have := climb_scale values c path ((h, is) :: rest) (i / 2) (if i % 2 = 0 then
          compress root s else compress s root) hg
        simpa only [List.map_cons] using this

end Scale

/-! ### Accepted multi-openings -/

section Accept
variable [Zero F] (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- Distinct powers of two, tallest first: adjacent ones have distinct padded heights. -/
theorem compatible_of_pairwise {α : Type} :
    ∀ (keys : List Nat), keys.Pairwise (· > ·) → (∀ h ∈ keys, ∃ j, h = 2 ^ j) →
      ∀ f : Nat → α, ((keys.map fun h ↦ (h, f h)).zip (keys.map fun h ↦ (h, f h)).tail).all
        (fun x ↦ x.1.1.nextPowerOfTwo != x.2.1.nextPowerOfTwo) = true
  | [], _, _, _ => rfl
  | [_], _, _, _ => rfl
  | a :: b :: rest, hk, hpow, f => by
    simp only [List.map_cons, List.tail_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · obtain ⟨i, rfl⟩ := hpow a List.mem_cons_self
      obtain ⟨j, rfl⟩ := hpow b (List.mem_cons_of_mem _ List.mem_cons_self)
      have : 2 ^ j < 2 ^ i := List.rel_of_pairwise_cons hk List.mem_cons_self
      rw [nextPowerOfTwo_two_pow, nextPowerOfTwo_two_pow, bne_iff_ne]
      omega
    · have := compatible_of_pairwise (b :: rest) hk.of_cons
        (fun h hh ↦ hpow h (List.mem_cons_of_mem _ hh)) f
      simpa only [List.map_cons, List.tail_cons] using this

/-- Heights at most `2 ^ k`, one of them `2 ^ k`, group with `2 ^ k` first. -/
theorem heightGroups_top (heights : List Nat) (k : Nat) (hle : ∀ h ∈ heights, h ≤ 2 ^ k)
    (htop : 2 ^ k ∈ heights) : ∃ g rest, heightGroups heights = g :: rest ∧ g.1 = 2 ^ k := by
  obtain ⟨keys, hk, hmem, hG⟩ := heightGroups_eq heights
  rcases keys with _ | ⟨a, ks⟩
  · exact absurd ((hmem _).mpr htop) List.not_mem_nil
  refine ⟨_, _, hG, ?_⟩
  have ha := hle a ((hmem a).mp List.mem_cons_self)
  rcases List.mem_cons.mp ((hmem _).mpr htop) with e | e
  · exact e.symm
  · have := List.rel_of_pairwise_cons hk e
    dsimp only
    omega

/-- An accepted multi-opening's cap has an entry per node of the cap layer of the tree of its
tallest matrices. -/
theorem length_cap_of_verifyMulti [DecidableEq F] (cap : List (Vector F d)) (capHeight : Nat)
    (dims : List (Nat × Nat)) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress cap capHeight dims indices rows sibs = true)
    (g : Nat × List Nat) (rest : List (Nat × List Nat))
    (hg : heightGroups (dims.map (·.1)) = g :: rest) :
    cap.length = 2 ^ (capLevels g.1 capHeight).2 := by
  unfold verifyMultiM at h
  rw [hg] at h
  obtain ⟨maxH, tallest⟩ := g
  dsimp only at h ⊢
  generalize capLevels maxH capHeight = lc at h ⊢
  obtain ⟨levels, c⟩ := lc
  dsimp only at h ⊢
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.1.2
  · exact absurd h Bool.false_ne_true

/-- An accepted multi-opening of matrices of heights at most `2 ^ k`, some of height `2 ^ k`, has
a cap of `2 ^ c` entries, `c` the cap height capped at `k`. -/
theorem length_cap_of_verifyMulti_mixed [DecidableEq F] (cap : List (Vector F d))
    (capHeight k : Nat) (dims : List (Nat × Nat)) (hpow : ∀ x ∈ dims, ∃ j ≤ k, x.1 = 2 ^ j)
    (htop : ∃ x ∈ dims, x.1 = 2 ^ k) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress cap capHeight dims indices rows sibs = true) :
    cap.length = 2 ^ min capHeight k := by
  obtain ⟨g, rest, hg, hg1⟩ := heightGroups_top (dims.map (·.1)) k
    (fun h hh ↦ by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hh
      obtain ⟨j, hj, e⟩ := hpow x hx
      rw [e]
      exact Nat.pow_le_pow_right (by decide) hj)
    (by obtain ⟨x, hx, e⟩ := htop; exact e ▸ List.mem_map_of_mem hx)
  have := length_cap_of_verifyMulti hash compress cap capHeight dims indices rows sibs h g rest hg
  rwa [hg1, capLevels_two_pow] at this

/-- An accepted multi-opening of matrices of heights `2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`, has
every matrix at least as tall as its cap of `2 ^ c` entries, `c` the cap height capped at `k`. -/
theorem cap_le_of_verifyMulti_mixed [DecidableEq F] (cap : List (Vector F d))
    (capHeight k : Nat) (dims : List (Nat × Nat)) (hpow : ∀ x ∈ dims, ∃ j ≤ k, x.1 = 2 ^ j)
    (htop : ∃ x ∈ dims, x.1 = 2 ^ k) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress cap capHeight dims indices rows sibs = true) :
    ∀ x ∈ dims, 2 ^ min capHeight k ≤ x.1 := by
  obtain ⟨keys, hk, hmem, hG⟩ := heightGroups_eq (dims.map (·.1))
  have htopK : 2 ^ k ∈ keys := by
    obtain ⟨x, hx, e⟩ := htop
    exact (hmem _).mpr (e ▸ List.mem_map_of_mem hx)
  obtain ⟨ks, hks⟩ : ∃ ks, keys = 2 ^ k :: ks := by
    rcases keys with _ | ⟨a, ks⟩
    · exact absurd htopK List.not_mem_nil
    · refine ⟨ks, ?_⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hmem a).mp List.mem_cons_self)
      obtain ⟨j, hj, e⟩ := hpow x hx
      rw [e]
      rcases List.mem_cons.mp htopK with h | h
      · rw [← e, h]
      · have := List.rel_of_pairwise_cons hk h
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj
        omega
  unfold verifyMultiM at h
  rw [hG, hks, List.map_cons] at h
  dsimp only at h
  rw [capLevels_two_pow, nextPowerOfTwo_two_pow] at h
  dsimp only at h
  split at h
  swap
  · exact absurd h Bool.false_ne_true
  rename_i hcond
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨-, hrestCap⟩ := hcond
  intro x hx
  obtain ⟨j, -, hxj⟩ := hpow x hx
  have hxk : 2 ^ j ∈ keys := (hmem _).mpr (hxj ▸ List.mem_map_of_mem hx)
  rw [hxj]
  rw [hks] at hxk
  rcases List.mem_cons.mp hxk with e | e
  · rw [e]
    exact Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
  · rw [List.all_eq_true] at hrestCap
    have := decide_eq_true_eq.mp (hrestCap _ (List.mem_map_of_mem e))
    rwa [nextPowerOfTwo_two_pow] at this

/-- **Restoring the paths at mixed heights.** An accepted multi-opening of matrices of heights
`2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`, against a cap of height `c = min capHeight k` gives
every query an accepted single opening of its rows in the subtree under its cap entry: the
heights divided by `2 ^ c`, at its index's low `k - c` bits. -/
theorem verifyBatch_of_verifyMulti_mixed [DecidableEq F] (cap : List (Vector F d))
    (capHeight k : Nat) (dims : List (Nat × Nat)) (hpow : ∀ x ∈ dims, ∃ j ≤ k, x.1 = 2 ^ j)
    (htop : ∃ x ∈ dims, x.1 = 2 ^ k) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress cap capHeight dims indices rows sibs = true)
    (r : Nat) (hr : r < indices.length) :
    ∃ path, verifyBatch hash compress (cap.getD (indices[r] >>> (k - min capHeight k)) 0)
      (dims.map (·.1 / 2 ^ min capHeight k)) (indices[r] % 2 ^ (k - min capHeight k))
      (rows.getD r []) path = true := by
  set heights := dims.map (·.1) with hheights
  obtain ⟨keys, hk, hmem, hG⟩ := heightGroups_eq heights
  have hpowK : ∀ h ∈ keys, ∃ j ≤ k, h = 2 ^ j := fun h hh ↦ by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hmem h).mp hh)
    exact hpow x hx
  have htopK : 2 ^ k ∈ keys := by
    obtain ⟨x, hx, e⟩ := htop
    exact (hmem _).mpr (e ▸ List.mem_map_of_mem hx)
  obtain ⟨ks, hks⟩ : ∃ ks, keys = 2 ^ k :: ks := by
    rcases keys with _ | ⟨a, ks⟩
    · exact absurd htopK List.not_mem_nil
    · refine ⟨ks, ?_⟩
      obtain ⟨j, hj, rfl⟩ := hpowK a List.mem_cons_self
      rcases List.mem_cons.mp htopK with h | h
      · rw [h]
      · have := List.rel_of_pairwise_cons hk h
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj
        omega
  have hksl : ∀ h ∈ ks, ∃ j < k, h = 2 ^ j := fun h hh ↦ by
    obtain ⟨j, hj, rfl⟩ := hpowK h (hks ▸ List.mem_cons_of_mem _ hh)
    have := List.rel_of_pairwise_cons (hks ▸ hk) hh
    exact ⟨j, (Nat.pow_lt_pow_iff_right (by decide)).mp this, rfl⟩
  set idx : Nat → List Nat := fun h ↦
    (List.range heights.length).filter (heights.getD · 0 == h) with hidxdef
  have hidx : ∀ h m, m ∈ idx h → ∃ hm : m < dims.length, dims[m].1 = h := fun h m hm ↦ by
    rw [hidxdef, List.mem_filter, List.mem_range, beq_iff_eq] at hm
    have hm' : m < dims.length := by rw [hheights, List.length_map] at hm; exact hm.1
    refine ⟨hm', ?_⟩
    have := hm.2
    rw [hheights, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm',
      Option.map_some, Option.getD_some] at this
    exact this
  set c := min capHeight k with hc
  have hck : c ≤ k := Nat.min_le_right _ _
  unfold verifyMultiM at h
  rw [hG, hks, List.map_cons] at h
  dsimp only at h
  rw [capLevels_two_pow, nextPowerOfTwo_two_pow] at h
  dsimp only at h
  rw [← hc] at h
  split at h
  swap
  · exact absurd h Bool.false_ne_true
  rename_i hcond
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨⟨hshape, -⟩, hrestCap⟩ := hcond
  obtain ⟨hrl, hrow, hlt, hcons⟩ := multiShapeOk_rows hshape
  -- Every height is a power of two of at least `2 ^ c`.
  have hksc : ∀ h ∈ ks, ∃ j, c ≤ j ∧ h = 2 ^ j := fun h hh ↦ by
    obtain ⟨j, -, rfl⟩ := hksl h hh
    rw [List.all_eq_true] at hrestCap
    have := decide_eq_true_eq.mp (hrestCap (2 ^ j, idx (2 ^ j)) (List.mem_map_of_mem hh))
    rw [nextPowerOfTwo_two_pow] at this
    exact ⟨j, (Nat.pow_le_pow_iff_right (by decide)).mp this, rfl⟩
  have hkeysc : ∀ h ∈ keys, ∃ j, c ≤ j ∧ h = 2 ^ j := fun h hh ↦ by
    rw [hks] at hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact ⟨k, hck, rfl⟩
    · exact hksc h hh
  have hheightsc : ∀ h ∈ heights, ∃ j, c ≤ j ∧ h = 2 ^ j := fun h hh ↦
    hkeysc h ((hmem h).mpr hh)
  -- Queries agreeing on a group's index open its rows equally.
  have hgrp : ∀ j ≤ k, ∀ r q (hr : r < indices.length) (hq : q < indices.length),
      indices[r] >>> (k - j) = indices[q] >>> (k - j) →
      (idx (2 ^ j)).flatMap (fun m ↦ (rows.getD r []).getD m []) =
        (idx (2 ^ j)).flatMap fun m ↦ (rows.getD q []).getD m [] := by
    intro j hj r q hr hq he
    refine List.flatMap_congr fun m hm ↦ ?_
    obtain ⟨hm', hdm⟩ := hidx _ m hm
    exact hcons r q hr hq m hm' (by rw [hdm, log2Ceil_two_pow, log2Ceil_two_pow]; exact he)
  set G0 := ks.map fun h ↦ (h, idx h) with hG0def
  set tallest := idx (2 ^ k)
  set leafOf : Nat → Vector F d := fun q ↦ hash (tallest.flatMap fun m ↦ (rows.getD q []).getD m [])
    with hleafOf
  have hl : ((MixedMerkleTree.frontier indices).mapM (m := Id) fun (x : Nat × Nat) ↦ match x with
      | (i, q) => do
        return (i, q, ← hash (tallest.flatMap fun k ↦ (rows.getD q []).getD k []))) =
      (MixedMerkleTree.frontier indices).map fun e ↦ (e.1, e.2, leafOf e.2) :=
    List.idRun_mapM
  rw [hl] at h
  change ((walkM (m := Id) hash compress rows (k - c) G0 (2 ^ k)
    ((MixedMerkleTree.frontier indices).map fun e ↦ (e.1, e.2, leafOf e.2)) sibs).1.all
    fun (x : Nat × Nat × Vector F d) ↦ x.2.2 == cap.getD x.1 0) = true at h
  rw [walkM_eq] at h
  have hGs : G0.Pairwise fun a b ↦ b.1 < a.1 :=
    List.pairwise_map.mpr ((hks ▸ hk).of_cons.imp id)
  have hGp : ∀ g ∈ G0, ∃ j < k, g.1 = 2 ^ j := fun g hg ↦ by
    obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hg
    exact hksl h' hh'
  have hsched := sched_eq_find (k - c) k G0 (Nat.sub_le _ _) hGs hGp
  obtain ⟨e, he, hei, p, hp, hcl⟩ := MixedMerkleTree.exists_climb_of_walk (hash := hash)
    (compress := compress) (fill := 0) (indices := indices) (leaf := leafOf)
    (pays := walkPays rows (k - c) G0 (2 ^ k)) (L := k - c) sibs
    (fun r q hr hq he ↦ by
      simp only [hleafOf]
      rw [hgrp k le_rfl r q hr hq (by rw [Nat.sub_self, Nat.shiftRight_zero, Nat.shiftRight_zero,
        he])])
    (fun d' hd r q hr hq he ↦ by
      rw [paysOf_walkPays, paysOf_walkPays, climbPays, climbPays, hsched d' hd]
      cases hf : G0.find? (fun g ↦ g.1 == 2 ^ (d' + (k - (k - c)))) with
      | none => rfl
      | some g =>
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
        have hgh := List.find?_some hf
        simp only [beq_iff_eq] at hgh
        obtain ⟨j, hj, rfl⟩ := hksl g' hg'
        have hjd : j = d' + (k - (k - c)) := Nat.pow_right_injective (le_refl 2) hgh
        simp only [Option.map_some]
        congr 1
        exact hgrp j hj.le r q hr hq (by rw [show k - j = k - c - d' by omega]; exact he))
    r hr
  rw [paysOf_walkPays, ← hp, ← climb_eq] at hcl
  have hcap : e.2.2 = cap.getD (indices[r] >>> (k - c)) 0 := by
    rw [List.all_eq_true] at h
    rw [← hei]
    exact beq_iff_eq.mp (h e he)
  refine ⟨p, ?_⟩
  have hr' : r < rows.length := hrl ▸ hr
  -- The subtree's groups: the heights divided by `2 ^ c`.
  have hscale : dims.map (·.1 / 2 ^ c) = heights.map (· / 2 ^ c) := by
    rw [hheights, List.map_map]; rfl
  have hGs := heightGroups_scale heights c hheightsc
  rw [hG, hks, List.map_cons, List.map_cons] at hGs
  have hkc : 2 ^ k / 2 ^ c = 2 ^ (k - c) := Nat.pow_div hck (by decide)
  have hdivmul : ∀ h ∈ keys, h / 2 ^ c * 2 ^ c = h := fun h hh ↦ by
    obtain ⟨j, hj, rfl⟩ := hkeysc h hh
    rw [Nat.pow_div hj (by decide), ← Nat.pow_add, Nat.sub_add_cancel hj]
  have hcomp := compatible_of_pairwise (keys.map (· / 2 ^ c)) (by
      rw [List.pairwise_map]
      refine hk.imp_of_mem fun ha hb hab ↦ ?_
      obtain ⟨i, hi, rfl⟩ := hkeysc _ ha
      obtain ⟨j, hj, rfl⟩ := hkeysc _ hb
      rw [Nat.pow_div hi (by decide), Nat.pow_div hj (by decide)]
      exact Nat.pow_lt_pow_right (by decide)
        (by have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hab; omega))
    (fun h hh ↦ by
      obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
      obtain ⟨j, hj, rfl⟩ := hkeysc h' hh'
      exact ⟨j - c, Nat.pow_div hj (by decide)⟩) (fun h ↦ idx (h * 2 ^ c))
  rw [List.map_map] at hcomp
  have hmapeq : (keys.map fun h ↦ (h / 2 ^ c, idx (h / 2 ^ c * 2 ^ c))) =
      keys.map fun h ↦ (h / 2 ^ c, idx h) :=
    List.map_congr_left fun h hh ↦ by rw [hdivmul h hh]
  rw [show (fun h ↦ (h, idx (h * 2 ^ c))) ∘ (· / 2 ^ c) =
    fun h ↦ (h / 2 ^ c, idx (h / 2 ^ c * 2 ^ c)) from rfl, hmapeq, hks, List.map_cons] at hcomp
  unfold verifyBatch
  rw [hscale, hGs]
  dsimp only
  rw [hkc, nextPowerOfTwo_two_pow, Nat.log2_two_pow]
  have hrl' : (rows.getD r []).length = (heights.map (· / 2 ^ c)).length := by
    rw [hrow r hr', hheights, List.length_map, List.length_map]
  have hmod : indices[r] % 2 ^ (k - c) < 2 ^ (k - c) := Nat.mod_lt _ (Nat.two_pow_pos _)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hp, hrl', hmod, and_true]
  refine ⟨by simpa only [hkc, List.map_map, Function.comp_def] using hcomp, ?_⟩
  have hG0 : ∀ g ∈ G0, ∃ j, c ≤ j ∧ g.1 = 2 ^ j := fun g hg ↦ by
    obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hg
    exact hksc h' hh'
  have := climb_scale hash compress (rows.getD r []) c p G0 indices[r] (leafOf r) hG0
  rw [hp, Nat.sub_add_cancel hck] at this
  rw [← hcap]
  exact this.symm.trans hcl

/-- An accepted multi-opening of `n > 0` matrices of height `2 ^ k` has a cap of `2 ^ c`
entries, `c` the cap height capped at `k`. -/
theorem length_cap_of_verifyMulti_replicate [DecidableEq F] (cap : List (Vector F d))
    (capHeight n k : Nat) (hn : 0 < n) (dims : List (Nat × Nat))
    (hdims : dims.map (·.1) = List.replicate n (2 ^ k)) (indices : List Nat)
    (rows : List (List (List F))) (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress cap capHeight dims indices rows sibs = true) :
    cap.length = 2 ^ min capHeight k := by
  have := length_cap_of_verifyMulti hash compress cap capHeight dims indices rows sibs h _ []
    (by rw [hdims, heightGroups_replicate n _ hn])
  rwa [capLevels_two_pow] at this

/-- **Restoring the paths.** An accepted multi-opening of `n > 0` matrices of one height `2 ^ k`
against a cap gives every query an accepted single opening of its rows in the subtree under its
cap entry: the tree of `2 ^ l` rows, `l` the levels below the cap, at its index's low `l` bits. -/
theorem verifyBatch_of_verifyMulti [DecidableEq F] (cap : List (Vector F d))
    (capHeight n k : Nat) (hn : 0 < n)
    (dims : List (Nat × Nat)) (hdims : dims.map (·.1) = List.replicate n (2 ^ k))
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress cap capHeight dims indices rows sibs = true)
    (r : Nat) (hr : r < indices.length) :
    ∃ path, verifyBatch hash compress (cap.getD (indices[r] >>> (k - min capHeight k)) 0)
      (List.replicate n (2 ^ (k - min capHeight k))) (indices[r] % 2 ^ (k - min capHeight k))
      (rows.getD r []) path = true := by
  have hmem : ∀ x ∈ dims, x.1 = 2 ^ k := fun x hx ↦
    List.eq_of_mem_replicate (hdims ▸ List.mem_map_of_mem hx)
  have hne : dims ≠ [] := by
    rintro rfl
    simp only [List.map_nil] at hdims
    exact absurd (congrArg List.length hdims) (by
      simp only [List.length_nil, List.length_replicate]; omega)
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil dims hne
  have hscale : dims.map (·.1 / 2 ^ min capHeight k) =
      List.replicate n (2 ^ (k - min capHeight k)) := by
    rw [show (fun x : Nat × Nat ↦ x.1 / 2 ^ min capHeight k) =
      (· / 2 ^ min capHeight k) ∘ (·.1) from rfl, ← List.map_map, hdims, List.map_replicate,
      Nat.pow_div (Nat.min_le_right _ _) (by decide)]
  rw [← hscale]
  exact verifyBatch_of_verifyMulti_mixed hash compress cap capHeight k dims
    (fun y hy ↦ ⟨k, le_rfl, hmem y hy⟩) ⟨x, hx, hmem x hx⟩ indices rows sibs h r hr

end Accept

end CompStark.Merkle
