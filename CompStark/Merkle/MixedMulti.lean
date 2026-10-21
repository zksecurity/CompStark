/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Mixed

/-! # Accepted multi-openings of mixed heights

`verifyBatch_of_verifyMulti_mixed`: an accepted multi-opening of matrices of heights
`2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`, gives every query an accepted single opening
(`verifyBatch`) of its rows. As for one height (`verifyBatch_of_verifyMulti`), the walk restores
each query's path: every node of a frontier is reached by the climbs of the queries below it, a
climb's next sibling being the node's partner or a sibling of the list (`level_struct`). Where the
walk injects the hash of a group of shorter matrices, it hashes its lead's rows, and every query
below the node opens the same rows of those matrices, as the multi-opening's shape check demands
(`multiShapeOk_rows`); so the query's own climb injects the same digest (`frontier_walkM`).
-/

@[expose] public section
namespace CompStark.Merkle

variable {F : Type} {d : Nat}

/-! ### One level of a walk -/

/-- In a list sorted strictly by index, two entries of one index are equal. -/
theorem eq_of_pairwise_lt {nodes : List (Nat × Nat × Vector F d)}
    (hs : nodes.Pairwise fun a b ↦ a.1 < b.1) {a b : Nat × Nat × Vector F d} (ha : a ∈ nodes)
    (hb : b ∈ nodes) (h : a.1 = b.1) : a = b := by
  induction nodes with
  | nil => exact absurd ha List.not_mem_nil
  | cons c rest ih =>
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · rw [ha, hb]
    · rw [ha] at h; have := hs.1 b hb; omega
    · rw [hb] at h; have := hs.1 a ha; omega
    · exact ih hs.2 ha hb

section Level
variable [Zero F] (compress : Vector F d → Vector F d → Vector F d)

/-- One level of a walk on a sorted frontier: the parents are sorted, each the parent of a node
and led by its lead, and every node has its parent among them, whose digest compresses the node's
with a sibling on the node's side. -/
theorem level_struct : ∀ (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)),
    (nodes.Pairwise fun a b ↦ a.1 < b.1) →
    ((level compress nodes sibs).1.Pairwise fun a b ↦ a.1 < b.1) ∧
      (∀ e' ∈ (level compress nodes sibs).1, ∃ e ∈ nodes, e'.1 = e.1 / 2 ∧ e'.2.1 = e.2.1) ∧
      ∀ e ∈ nodes, ∃ e' ∈ (level compress nodes sibs).1, e'.1 = e.1 / 2 ∧
        ∃ s, e'.2.2 = if e.1 % 2 = 0 then compress e.2.2 s else compress s e.2.2
  | [], sibs, _ => by
    simp only [level_nil, List.Pairwise.nil, List.not_mem_nil, false_and, exists_false,
      imp_self, implies_true, and_self]
  | [(i, q, x)], sibs, _ => by
    rw [level_single]
    refine ⟨List.pairwise_singleton _ _, fun e' he' ↦ ?_, fun e he ↦ ?_⟩
    · rw [List.mem_singleton] at he'
      exact ⟨(i, q, x), List.mem_singleton_self _, by rw [he'], by rw [he']⟩
    · rw [List.mem_singleton] at he
      subst he
      exact ⟨_, List.mem_singleton_self _, rfl, sibs.headD 0, rfl⟩
  | (i, q, x) :: (j, q', y) :: rest, sibs, hs => by
    have hij : i < j := List.rel_of_pairwise_cons hs List.mem_cons_self
    have hrest : ∀ e ∈ rest, j < e.1 :=
      fun e he ↦ List.rel_of_pairwise_cons (List.Pairwise.of_cons hs) he
    have hsrest : rest.Pairwise fun a b ↦ a.1 < b.1 := (hs.of_cons).of_cons
    have hsj : ((j, q', y) :: rest).Pairwise fun a b ↦ a.1 < b.1 := hs.of_cons
    rw [level_cons_cons]
    split
    · rename_i hpair
      obtain ⟨hi2, rfl⟩ := hpair
      obtain ⟨ihs, ihp, ihc⟩ := level_struct rest sibs hsrest
      have habove : ∀ e' ∈ (level compress rest sibs).1, i / 2 < e'.1 := by
        intro e' he'
        obtain ⟨e, he, h, -⟩ := ihp e' he'
        have := hrest e he
        rw [h]
        omega
      refine ⟨List.Pairwise.cons (fun e' he' ↦ habove e' he') ihs, fun e' he' ↦ ?_, fun e he ↦ ?_⟩
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨e, he, h⟩ := ihp e' he'
          exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he), h⟩
      · rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, rfl, y, by simp only [hi2, ↓reduceIte]⟩
        rcases List.mem_cons.mp he with rfl | he
        · refine ⟨_, List.mem_cons_self, by dsimp only; omega, x, ?_⟩
          have hodd : (i + 1) % 2 ≠ 0 := by omega
          simp only [hodd, ↓reduceIte]
        · obtain ⟨e', he', h⟩ := ihc e he
          exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · obtain ⟨ihs, ihp, ihc⟩ := level_struct ((j, q', y) :: rest) sibs.tail hsj
      have hjp : i / 2 < j / 2 := by
        rename_i hpair
        omega
      have habove : ∀ e' ∈ (level compress ((j, q', y) :: rest) sibs.tail).1, i / 2 < e'.1 := by
        intro e' he'
        obtain ⟨e, he, h, -⟩ := ihp e' he'
        rw [h]
        rcases List.mem_cons.mp he with rfl | he
        · exact hjp
        · have := hrest e he
          omega
      refine ⟨List.Pairwise.cons (fun e' he' ↦ habove e' he') ihs, fun e' he' ↦ ?_, fun e he ↦ ?_⟩
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨e, he, h⟩ := ihp e' he'
          exact ⟨e, List.mem_cons_of_mem _ he, h⟩
      · rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, rfl, sibs.headD 0, rfl⟩
        · obtain ⟨e', he', h⟩ := ihc e he
          exact ⟨e', List.mem_cons_of_mem _ he', h⟩

end Level

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

/-! ### Injections -/

section Steps
variable (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- The digest of a node after its layer's injection: compressed with the hash of the rows of
the group `inj` of a query, if a group has the layer's height. -/
def injectWith (inj : Option (List Nat)) (values : List (List F)) (z : Vector F d) : Vector F d :=
  match inj with
  | some is => compress z (hash (is.flatMap fun m ↦ values.getD m []))
  | none => z

/-- One step of a climb that injects the group `(h, is)` when its height is the next layer's. -/
theorem climb_cons_cons (values : List (List F)) (s : Vector F d) (tail : List (Vector F d))
    (h : Nat) (is : List Nat) (rest : List (Nat × List Nat)) (i padded : Nat) (root : Vector F d) :
    climb hash compress values (s :: tail) ((h, is) :: rest) i padded root =
      if h.nextPowerOfTwo = padded / 2 then
        climb hash compress values tail rest (i / 2) (padded / 2)
          (injectWith hash compress (some is) values
            (if i % 2 = 0 then compress root s else compress s root))
      else climb hash compress values tail ((h, is) :: rest) (i / 2) (padded / 2)
        (injectWith hash compress none values
          (if i % 2 = 0 then compress root s else compress s root)) := by
  simp only [climb, injectWith, hashRows]

/-- One step of a climb without groups left. -/
theorem climb_cons_nil (values : List (List F)) (s : Vector F d) (tail : List (Vector F d))
    (i padded : Nat) (root : Vector F d) :
    climb hash compress values (s :: tail) [] i padded root =
      climb hash compress values tail [] (i / 2) (padded / 2)
        (injectWith hash compress none values
          (if i % 2 = 0 then compress root s else compress s root)) := by
  simp only [climb, injectWith]

theorem map_injectWith_none (rows : List (List (List F))) (ps : List (Nat × Nat × Vector F d)) :
    (ps.map fun x ↦ (x.1, x.2.1, injectWith hash compress none (rows.getD x.2.1 []) x.2.2)) =
      ps := by
  simp only [injectWith, Prod.mk.eta, List.map_id']

end Steps

/-! ### Restoring the paths with injections -/

section Restore
variable [Zero F] (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
  (rows : List (List (List F))) (indices : List Nat) (tallest : List Nat)
  (G0 : List (Nat × List Nat)) (P0 : Nat)

/-- The leaf digest of query `r`: the hash of its rows of the tallest matrices. -/
def leafOfGroup (r : Nat) : Vector F d :=
  hash (tallest.flatMap fun m ↦ (rows.getD r []).getD m [])

/-- Every query below the node `e` of level `l` climbs from its leaf along `l` siblings, injecting
the groups `G0` from the padded height `P0` on, to the node's digest with the groups `groups` and
the padded height `padded` left. -/
def ClimbsG (l : Nat) (groups : List (Nat × List Nat)) (padded : Nat)
    (e : Nat × Nat × Vector F d) : Prop :=
  ∀ r (hr : r < indices.length), indices[r] >>> l = e.1 → ∃ p : List (Vector F d), p.length = l ∧
    ∀ tail, climb hash compress (rows.getD r []) (p ++ tail) G0 indices[r] P0
        (leafOfGroup hash rows tallest r) =
      climb hash compress (rows.getD r []) tail groups (indices[r] >>> l) padded e.2.2

/-- A frontier at level `l`, with the groups `groups` and the padded height `padded` left: sorted
by index, every query below one of its nodes, every node led by a query below it, and reached by
its queries' climbs. -/
structure FrontierG (l : Nat) (groups : List (Nat × List Nat)) (padded : Nat)
    (nodes : List (Nat × Nat × Vector F d)) : Prop where
  sorted : nodes.Pairwise fun a b ↦ a.1 < b.1
  covers : ∀ r (hr : r < indices.length), ∃ e ∈ nodes, e.1 = indices[r] >>> l
  leads : ∀ e ∈ nodes, ∃ h : e.2.1 < indices.length, indices[e.2.1] >>> l = e.1
  climbs : ∀ e ∈ nodes, ClimbsG hash compress rows indices tallest G0 P0 l groups padded e

variable {hash compress rows indices tallest G0 P0}

/-- One level of a walk from a frontier, injecting the group `inj`, if any, with each parent's
lead's rows, all of whose matrices the queries below a parent open equally: a frontier one level
up. -/
theorem frontier_level (l : Nat) (groups groups' : List (Nat × List Nat)) (padded : Nat)
    (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d))
    (h : FrontierG hash compress rows indices tallest G0 P0 l groups padded nodes)
    (inj : Option (List Nat))
    (hstep : ∀ (r : Nat) (root s : Vector F d) (tail : List (Vector F d)) (i : Nat),
      climb hash compress (rows.getD r []) (s :: tail) groups i padded root =
        climb hash compress (rows.getD r []) tail groups' (i / 2) (padded / 2)
          (injectWith hash compress inj (rows.getD r [])
            (if i % 2 = 0 then compress root s else compress s root)))
    (hcons : ∀ r q (hr : r < indices.length) (hq : q < indices.length),
      indices[r] >>> (l + 1) = indices[q] >>> (l + 1) → ∀ z,
        injectWith hash compress inj (rows.getD r []) z =
          injectWith hash compress inj (rows.getD q []) z) :
    FrontierG hash compress rows indices tallest G0 P0 (l + 1) groups' (padded / 2)
      ((level compress nodes sibs).1.map fun x ↦
        (x.1, x.2.1, injectWith hash compress inj (rows.getD x.2.1 []) x.2.2)) := by
  obtain ⟨hs, hpar, hc⟩ := level_struct compress nodes sibs h.sorted
  set ps := (level compress nodes sibs).1
  -- The node a query sits below at level `l`, and its parent.
  have hparent : ∀ r (hr : r < indices.length), ∃ e ∈ nodes, e.1 = indices[r] >>> l ∧
      ∃ e' ∈ ps, e'.1 = indices[r] >>> (l + 1) ∧
        ∃ s, e'.2.2 = if e.1 % 2 = 0 then compress e.2.2 s else compress s e.2.2 := by
    intro r hr
    obtain ⟨e, he, hei⟩ := h.covers r hr
    obtain ⟨e', he', h1, h2⟩ := hc e he
    exact ⟨e, he, hei, e', he', by rw [h1, hei, shiftRight_succ], h2⟩
  -- Every parent is led by a query below it.
  have hlead : ∀ e' ∈ ps, ∃ h : e'.2.1 < indices.length,
      indices[e'.2.1] >>> (l + 1) = e'.1 := by
    intro e' he'
    obtain ⟨e, he, h1, h2⟩ := hpar e' he'
    obtain ⟨hl, hle⟩ := h.leads e he
    rw [h2]
    exact ⟨hl, by rw [shiftRight_succ, hle, h1]⟩
  refine ⟨List.pairwise_map.mpr hs, fun r hr ↦ ?_, fun e' he' ↦ ?_, fun e' he' r hr hre ↦ ?_⟩
  · obtain ⟨-, -, -, e', he', h1, -⟩ := hparent r hr
    exact ⟨_, List.mem_map_of_mem he', h1⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    exact hlead x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    dsimp only at hre ⊢
    obtain ⟨e, he, hei, e'', he'', hi'', s, hs''⟩ := hparent r hr
    have hee : e'' = x := eq_of_pairwise_lt hs he'' hx (by rw [hi'', hre])
    subst hee
    obtain ⟨p, hp, hpc⟩ := h.climbs e he r hr hei.symm
    obtain ⟨hl, hle⟩ := hlead e'' hx
    refine ⟨p ++ [s], by rw [List.length_append, hp, List.length_singleton], fun tail ↦ ?_⟩
    rw [List.append_assoc, List.singleton_append, hpc, hstep, ← hei, ← hs'', hei,
      ← shiftRight_succ, hcons r e''.2.1 hr hl (by rw [hle, hi''])]

/-- **A walk with injections.** The walk over `levels` levels from a frontier at level `l` of a
tree of height `2 ^ k`, with groups left of heights `2 ^ j < 2 ^ k` among `G0`, each opened
equally by the queries that agree on its rows' index, ends at a frontier. -/
theorem frontier_walkM (k : Nat) (hG : ∀ g ∈ G0, ∃ j < k, g.1 = 2 ^ j)
    (hcons : ∀ g ∈ G0, ∀ r q (hr : r < indices.length) (hq : q < indices.length),
      indices[r] >>> (k - Nat.log2 g.1) = indices[q] >>> (k - Nat.log2 g.1) →
      g.2.flatMap (fun m ↦ (rows.getD r []).getD m []) =
        g.2.flatMap fun m ↦ (rows.getD q []).getD m []) :
    ∀ (levels l : Nat) (groups : List (Nat × List Nat)) (nodes : List (Nat × Nat × Vector F d))
      (sibs : List (Vector F d)), l + levels ≤ k → (∀ g ∈ groups, g ∈ G0) →
      FrontierG hash compress rows indices tallest G0 P0 l groups (2 ^ (k - l)) nodes →
      ∃ groups', FrontierG hash compress rows indices tallest G0 P0 (l + levels) groups'
        (2 ^ (k - (l + levels)))
        (walkM (m := Id) hash compress rows levels groups (2 ^ (k - l)) nodes sibs).1
  | 0, l, groups, nodes, sibs, _, _, h => ⟨groups, h⟩
  | levels + 1, l, groups, nodes, sibs, hk, hsub, h => by
    have hpad : 2 ^ (k - l) / 2 = 2 ^ (k - (l + 1)) := by
      rw [show k - l = k - (l + 1) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    have hlev : l + (levels + 1) = l + 1 + levels := by omega
    have hnone : ∀ r q (hr : r < indices.length) (hq : q < indices.length),
        indices[r] >>> (l + 1) = indices[q] >>> (l + 1) → ∀ z,
          injectWith hash compress none (rows.getD r []) z =
            injectWith hash compress none (rows.getD q []) z := fun _ _ _ _ _ _ ↦ rfl
    rw [hlev]
    match groups, hsub with
    | [], _ =>
      have hstep := frontier_level l [] [] _ nodes sibs h none
        (fun r root s tail i ↦ climb_cons_nil hash compress _ s tail i _ root) hnone
      rw [map_injectWith_none hash compress rows, hpad] at hstep
      rw [walkM_succ_nil]
      have := frontier_walkM k hG hcons levels (l + 1) [] _ (level compress nodes sibs).2
        (by omega) (fun _ h ↦ absurd h List.not_mem_nil) (by rw [hpad] at *; exact hstep)
      rw [hpad]
      exact this
    | (hh, is) :: rest, hsub =>
      rw [walkM_succ_cons]
      by_cases hi : hh.nextPowerOfTwo = 2 ^ (k - l) / 2
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hi)]
        obtain ⟨j, hj, hjh⟩ := hG _ (hsub _ List.mem_cons_self)
        change hh = 2 ^ j at hjh
        have hjl : j = k - (l + 1) := by
          rw [hjh, nextPowerOfTwo_two_pow, hpad] at hi
          exact Nat.pow_right_injective (le_refl 2) hi
        have hstep := frontier_level l ((hh, is) :: rest) rest _ nodes sibs h (some is)
          (fun r root s tail i ↦ by rw [climb_cons_cons, ite_eq_left_of_eq_true _ _ (eq_true hi)]) (fun r q hr hq he z ↦ by
            have hc := hcons _ (hsub _ List.mem_cons_self) r q hr hq (by
              dsimp only
              rw [hjh, Nat.log2_two_pow, show k - j = l + 1 by omega]
              exact he)
            simp only [injectWith]
            rw [hc])
        rw [hpad] at hstep
        rw [hpad]
        exact frontier_walkM k hG hcons levels (l + 1) rest _ _ (by omega)
          (fun g hg ↦ hsub g (List.mem_cons_of_mem _ hg)) hstep
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hi)]
        have hstep := frontier_level l ((hh, is) :: rest) ((hh, is) :: rest) _ nodes sibs h none
          (fun r root s tail i ↦ by rw [climb_cons_cons, ite_eq_right_of_eq_false _ _ (eq_false hi)]) hnone
        rw [map_injectWith_none hash compress rows, hpad] at hstep
        rw [hpad]
        exact frontier_walkM k hG hcons levels (l + 1) _ _ _ (by omega) hsub hstep

end Restore

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

/-- **Restoring the paths at mixed heights.** An accepted multi-opening of matrices of heights
`2 ^ j ≤ 2 ^ k`, some of height `2 ^ k`, gives every query an accepted single opening of its
rows. -/
theorem verifyBatch_of_verifyMulti_mixed [DecidableEq F] (commit : Vector F d) (k : Nat)
    (dims : List (Nat × Nat)) (hpow : ∀ x ∈ dims, ∃ j ≤ k, x.1 = 2 ^ j)
    (htop : ∃ x ∈ dims, x.1 = 2 ^ k) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress commit dims indices rows sibs = true)
    (r : Nat) (hr : r < indices.length) :
    ∃ path, verifyBatch hash compress commit (dims.map (·.1)) indices[r] (rows.getD r [])
      path = true := by
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
  unfold verifyMultiM at h
  rw [hG, hks, List.map_cons] at h
  dsimp only at h
  rw [nextPowerOfTwo_two_pow, Nat.log2_two_pow] at h
  split at h
  swap
  · exact absurd h Bool.false_ne_true
  rename_i hshape
  obtain ⟨hrl, hrow, hlt, hcons⟩ := multiShapeOk_rows hshape
  -- Queries agreeing on a group's index open its rows equally.
  have hgrp : ∀ j ≤ k, ∀ r q (hr : r < indices.length) (hq : q < indices.length),
      indices[r] >>> (k - j) = indices[q] >>> (k - j) →
      (idx (2 ^ j)).flatMap (fun m ↦ (rows.getD r []).getD m []) =
        (idx (2 ^ j)).flatMap fun m ↦ (rows.getD q []).getD m [] := by
    intro j hj r q hr hq he
    refine List.flatMap_congr fun m hm ↦ ?_
    obtain ⟨hm', hdm⟩ := hidx _ m hm
    exact hcons r q hr hq m hm' (by rw [hdm, log2Ceil_two_pow, log2Ceil_two_pow]; exact he)
  set G0 := ks.map fun h ↦ (h, idx h)
  set tallest := idx (2 ^ k)
  set leaves := (frontier indices).map fun (e : Nat × Nat) ↦
    (e.1, e.2, leafOfGroup hash rows tallest e.2) with hleaves
  have hl : ((frontier indices).mapM (m := Id) fun (x : Nat × Nat) ↦ match x with
      | (i, q) => do
        return (i, q, ← hash (tallest.flatMap fun k ↦ (rows.getD q []).getD k []))) =
      leaves := by
    rw [hleaves]
    exact List.idRun_mapM
  rw [hl] at h
  have h0 : FrontierG hash compress rows indices tallest G0 (2 ^ k) 0 G0 (2 ^ (k - 0))
      leaves := by
    refine ⟨?_, fun r' hr' ↦ ?_, fun e he ↦ ?_, fun e he r' hr' hre ↦ ?_⟩
    · rw [hleaves, List.pairwise_map]
      exact pairwise_frontier indices
    · refine ⟨(indices[r'], indices.idxOf indices[r'], leafOfGroup hash rows tallest
        (indices.idxOf indices[r'])), ?_, by rw [Nat.shiftRight_zero]⟩
      exact List.mem_map.mpr ⟨(indices[r'], indices.idxOf indices[r']),
        mem_frontier.mpr ⟨List.getElem_mem hr', rfl⟩, rfl⟩
    · obtain ⟨⟨i, q⟩, hiq, rfl⟩ := List.mem_map.mp he
      obtain ⟨hi, hq⟩ := mem_frontier.mp hiq
      dsimp only at hi hq ⊢
      subst hq
      have hq : indices.idxOf i < indices.length := List.idxOf_lt_length_of_mem hi
      exact ⟨hq, by rw [Nat.shiftRight_zero]; exact List.getElem_idxOf hq⟩
    · obtain ⟨⟨i, q⟩, hiq, rfl⟩ := List.mem_map.mp he
      obtain ⟨hi, hq⟩ := mem_frontier.mp hiq
      dsimp only at hi hq hre ⊢
      subst hq
      rw [Nat.shiftRight_zero] at hre
      have hq : indices.idxOf i < indices.length := List.idxOf_lt_length_of_mem hi
      have hqi : indices[indices.idxOf i] = i := List.getElem_idxOf hq
      refine ⟨[], rfl, fun tail ↦ ?_⟩
      rw [List.nil_append, Nat.shiftRight_zero, Nat.sub_zero, leafOfGroup, leafOfGroup,
        hgrp k le_rfl r' (indices.idxOf i) hr' hq (by rw [Nat.sub_self, Nat.shiftRight_zero,
          Nat.shiftRight_zero, hre, hqi])]
  obtain ⟨gs', hfin⟩ := frontier_walkM (hash := hash) (compress := compress) (rows := rows)
    (indices := indices) (tallest := tallest) (G0 := G0) (P0 := 2 ^ k) k
    (fun g hg ↦ by
      obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hg
      exact hksl h' hh')
    (fun g hg r q hr hq he ↦ by
      obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hg
      obtain ⟨j, hj, rfl⟩ := hksl h' hh'
      dsimp only at he ⊢
      rw [Nat.log2_two_pow] at he
      exact hgrp j hj.le r q hr hq he)
    k 0 G0 leaves sibs (by omega) (fun _ hg ↦ hg) h0
  change ((walkM (m := Id) hash compress rows k G0 (2 ^ k) leaves sibs).1.all
    fun (x : Nat × Nat × Vector F d) ↦ x.2.2 == commit) = true at h
  obtain ⟨e, he, hei⟩ := hfin.covers r hr
  obtain ⟨p, hp, hc⟩ := hfin.climbs e he r hr hei.symm
  have hcommit : e.2.2 = commit := by
    rw [List.all_eq_true] at h
    exact beq_iff_eq.mp (h e he)
  refine ⟨p, ?_⟩
  have hr' : r < rows.length := hrl ▸ hr
  have hc0 := hc []
  rw [List.append_nil] at hc0
  have hcomp := compatible_of_pairwise keys hk (fun h hh ↦ by
    obtain ⟨j, -, hj⟩ := hpowK h hh
    exact ⟨j, hj⟩) idx
  rw [hks, List.map_cons] at hcomp
  rw [Nat.zero_add] at hp
  unfold verifyBatch
  rw [hG, hks, List.map_cons]
  dsimp only
  rw [nextPowerOfTwo_two_pow, Nat.log2_two_pow]
  have hrl' : (rows.getD r []).length = heights.length := by
    rw [hrow r hr', hheights, List.length_map]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hp, hrl', hlt r hr, and_true]
  rw [← hcommit]
  exact ⟨hcomp, hc0⟩

end Accept

end CompStark.Merkle
