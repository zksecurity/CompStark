/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.VCVio

/-! # Multi-openings of one height

The pruned multi-openings of `verifyMultiM`, for batches of matrices of one height `2 ^ k`, with
pure hashes:

* `verifyBatch_of_verifyMulti`: an accepted multi-opening gives every query an accepted single
  opening (`verifyBatch`): the walk restores each query's path, every sibling a node of the
  frontier or a sibling of the list.
* `verifyMulti_prune`: the honest multi-opening of a tree, its rows and the pruned siblings of
  its paths (`prune`), is accepted. Every node of the walk is the tree's node.
-/

@[expose] public section
namespace CompStark.Merkle

variable {F : Type} {d : Nat}

section Level
variable [Zero F] (compress : Vector F d → Vector F d → Vector F d)

/-- `levelM` with a pure compression. -/
abbrev level (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) :
    List (Nat × Nat × Vector F d) × List (Vector F d) :=
  levelM (m := Id) compress nodes sibs

theorem level_nil (sibs : List (Vector F d)) : level compress [] sibs = ([], sibs) := rfl

theorem level_single (i q : Nat) (x : Vector F d) (sibs : List (Vector F d)) :
    level compress [(i, q, x)] sibs =
      ([(i / 2, q, if i % 2 = 0 then compress x (sibs.headD 0) else compress (sibs.headD 0) x)],
        sibs.tail) := by
  simp only [level, levelM]
  split <;> rfl

theorem level_cons_cons (i q j q' : Nat) (x y : Vector F d) (rest : List (Nat × Nat × Vector F d))
    (sibs : List (Vector F d)) :
    level compress ((i, q, x) :: (j, q', y) :: rest) sibs =
      if i % 2 = 0 ∧ j = i + 1 then
        ((i / 2, q, compress x y) :: (level compress rest sibs).1, (level compress rest sibs).2)
      else
        ((i / 2, q, if i % 2 = 0 then compress x (sibs.headD 0) else compress (sibs.headD 0) x) ::
          (level compress ((j, q', y) :: rest) sibs.tail).1,
          (level compress ((j, q', y) :: rest) sibs.tail).2) := by
  simp only [level, levelM]
  split
  · rfl
  · split <;> rfl

end Level

section Walk
variable [Zero F] (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- `walkM` with pure hashes and no shorter matrices. -/
abbrev walk (rows : List (List (List F))) (levels padded : Nat)
    (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) :
    List (Nat × Nat × Vector F d) × List (Vector F d) :=
  walkM (m := Id) hash compress rows levels [] padded nodes sibs

theorem walk_zero (rows : List (List (List F))) (padded : Nat)
    (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) :
    walk hash compress rows 0 padded nodes sibs = (nodes, sibs) := rfl

theorem walk_succ (rows : List (List (List F))) (levels padded : Nat)
    (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) :
    walk hash compress rows (levels + 1) padded nodes sibs =
      walk hash compress rows levels (padded / 2) (level compress nodes sibs).1
        (level compress nodes sibs).2 := rfl

end Walk

/-! ### Restoring the paths -/

section Restore
variable (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
  (rows : List (List (List F))) (n : Nat) (indices : List Nat)

/-- The leaf digest of query `r`: the hash of its concatenated rows. -/
def leafOf (r : Nat) : Vector F d :=
  hash ((List.range n).flatMap fun k ↦ (rows.getD r []).getD k [])

/-- Every query below the node `e` of level `l` climbs from its leaf to the node's digest along a
path of `l` siblings. -/
def Climbs (l : Nat) (e : Nat × Nat × Vector F d) : Prop :=
  ∀ r (hr : r < indices.length), indices[r] >>> l = e.1 → ∃ p : List (Vector F d), p.length = l ∧
    climb hash compress (rows.getD r []) p [] indices[r] 0 (leafOf hash rows n r) = e.2.2

variable {hash compress rows n indices}

/-- A query below the parent of a node climbs to the parent through the node and one more
sibling, on the side of the node's parity. -/
theorem climbs_step {l i : Nat} {q : Nat} {x s : Vector F d}
    (hx : Climbs hash compress rows n indices l (i, q, x)) (r : Nat) (hr : r < indices.length)
    (hi : indices[r] >>> l = i) :
    ∃ p : List (Vector F d), p.length = l + 1 ∧
      climb hash compress (rows.getD r []) p [] indices[r] 0 (leafOf hash rows n r) =
        if i % 2 = 0 then compress x s else compress s x := by
  obtain ⟨p, hp, hc⟩ := hx r hr hi
  refine ⟨p ++ [s], by rw [List.length_append, hp, List.length_singleton], ?_⟩
  rw [climb_append, hc, hp, ← Nat.shiftRight_eq_div_pow, hi]

theorem shiftRight_succ (x l : Nat) : x >>> (l + 1) = x >>> l / 2 := by
  rw [Nat.shiftRight_succ]

/-- Every query below a parent whose node one level lower is in the frontier climbs to the
parent. -/
def ClimbsFrom (nodes : List (Nat × Nat × Vector F d)) (l : Nat) (e' : Nat × Nat × Vector F d) :
    Prop :=
  ∀ r (hr : r < indices.length), indices[r] >>> (l + 1) = e'.1 →
    (∃ e ∈ nodes, e.1 = indices[r] >>> l) → ∃ p : List (Vector F d), p.length = l + 1 ∧
      climb hash compress (rows.getD r []) p [] indices[r] 0 (leafOf hash rows n r) = e'.2.2

variable [Zero F]

/-- One level of a walk on a sorted frontier: the parents are sorted, each the parent of a node,
every node has its parent among them, and the queries of the frontier climb to their parents. -/
theorem level_spec : ∀ (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)) (l : Nat),
    (nodes.Pairwise fun a b ↦ a.1 < b.1) →
    (∀ e ∈ nodes, Climbs hash compress rows n indices l e) →
    ((level compress nodes sibs).1.Pairwise fun a b ↦ a.1 < b.1) ∧
      (∀ e' ∈ (level compress nodes sibs).1, ∃ e ∈ nodes, e'.1 = e.1 / 2) ∧
      (∀ e ∈ nodes, ∃ e' ∈ (level compress nodes sibs).1, e'.1 = e.1 / 2) ∧
      ∀ e' ∈ (level compress nodes sibs).1,
        ClimbsFrom (hash := hash) (compress := compress) (rows := rows) (n := n)
          (indices := indices) nodes l e'
  | [], sibs, l, _, _ => by
    simp only [level_nil, List.Pairwise.nil, List.not_mem_nil, false_and, exists_false,
      imp_self, implies_true, and_self, IsEmpty.forall_iff]
  | [(i, q, x)], sibs, l, _, hc => by
    rw [level_single]
    refine ⟨List.pairwise_singleton _ _, ?_, ?_, ?_⟩
    · intro e he
      rw [List.mem_singleton] at he
      exact ⟨(i, q, x), List.mem_singleton_self _, by rw [he]⟩
    · intro e he
      rw [List.mem_singleton] at he
      exact ⟨_, List.mem_singleton_self _, by rw [he]⟩
    · intro e he
      rw [List.mem_singleton] at he
      subst he
      intro r hr _ ⟨e, he, hei⟩
      rw [List.mem_singleton] at he
      subst he
      exact climbs_step (hc _ (List.mem_singleton_self _)) r hr hei.symm
  | (i, q, x) :: (j, q', y) :: rest, sibs, l, hs, hc => by
    have hij : i < j := List.rel_of_pairwise_cons hs List.mem_cons_self
    have hrest : ∀ e ∈ rest, j < e.1 :=
      fun e he ↦ List.rel_of_pairwise_cons (List.Pairwise.of_cons hs) he
    have hrest' : ∀ e ∈ rest, i < e.1 := fun e he ↦ lt_trans hij (hrest e he)
    have hsrest : rest.Pairwise fun a b ↦ a.1 < b.1 := (hs.of_cons).of_cons
    have hsj : ((j, q', y) :: rest).Pairwise fun a b ↦ a.1 < b.1 := hs.of_cons
    have hcx := hc _ List.mem_cons_self
    have hcy := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hcrest : ∀ e ∈ rest, Climbs hash compress rows n indices l e :=
      fun e he ↦ hc e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
    have hcj : ∀ e ∈ (j, q', y) :: rest, Climbs hash compress rows n indices l e :=
      fun e he ↦ hc e (List.mem_cons_of_mem _ he)
    rw [level_cons_cons]
    split
    · rename_i hpair
      obtain ⟨hi2, rfl⟩ := hpair
      obtain ⟨ihs, ihp, ihc, ihcl⟩ := level_spec rest sibs l hsrest hcrest
      -- Parents of `rest` lie above `i / 2`.
      have habove : ∀ e' ∈ (level compress rest sibs).1, i / 2 < e'.1 := by
        intro e' he'
        obtain ⟨e, he, h⟩ := ihp e' he'
        have := hrest e he
        rw [h]
        omega
      refine ⟨List.Pairwise.cons (fun e' he' ↦ habove e' he') ihs, ?_, ?_, ?_⟩
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact ⟨_, List.mem_cons_self, rfl⟩
        · obtain ⟨e, he, h⟩ := ihp e' he'
          exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he), h⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, rfl⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, by dsimp only; omega⟩
        · obtain ⟨e', he', h⟩ := ihc e he
          exact ⟨e', List.mem_cons_of_mem _ he', h⟩
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · intro r hr hrp ⟨e, he, hei⟩
          rcases List.mem_cons.mp he with rfl | he
          · have := climbs_step (s := y) hcx r hr hei.symm
            simpa only [hi2, ↓reduceIte] using this
          rcases List.mem_cons.mp he with rfl | he
          · have := climbs_step (s := x) hcy r hr hei.symm
            have hodd : (i + 1) % 2 ≠ 0 := by omega
            simpa only [hodd, ↓reduceIte] using this
          · have h1 := hrest e he
            rw [shiftRight_succ, ← hei] at hrp
            dsimp only at h1 hrp
            omega
        · intro r hr hrp ⟨e, he, hei⟩
          refine ihcl e' he' r hr hrp ⟨e, ?_, hei⟩
          rcases List.mem_cons.mp he with rfl | he
          · have := habove e' he'
            rw [← hrp, shiftRight_succ, ← hei] at this
            dsimp only at this
            omega
          rcases List.mem_cons.mp he with rfl | he
          · have := habove e' he'
            rw [← hrp, shiftRight_succ, ← hei] at this
            dsimp only at this
            omega
          · exact he
    · rename_i hpair
      obtain ⟨ihs, ihp, ihc, ihcl⟩ := level_spec ((j, q', y) :: rest) sibs.tail l hsj hcj
      have hjp : i / 2 < j / 2 := by omega
      have habove : ∀ e' ∈ (level compress ((j, q', y) :: rest) sibs.tail).1, i / 2 < e'.1 := by
        intro e' he'
        obtain ⟨e, he, h⟩ := ihp e' he'
        rw [h]
        rcases List.mem_cons.mp he with rfl | he
        · exact hjp
        · have := hrest e he
          omega
      refine ⟨List.Pairwise.cons (fun e' he' ↦ habove e' he') ihs, ?_, ?_, ?_⟩
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact ⟨_, List.mem_cons_self, rfl⟩
        · obtain ⟨e, he, h⟩ := ihp e' he'
          exact ⟨e, List.mem_cons_of_mem _ he, h⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, rfl⟩
        · obtain ⟨e', he', h⟩ := ihc e he
          exact ⟨e', List.mem_cons_of_mem _ he', h⟩
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · intro r hr hrp ⟨e, he, hei⟩
          rcases List.mem_cons.mp he with rfl | he
          · exact climbs_step hcx r hr hei.symm
          · exfalso
            have h1 : j ≤ e.1 := by
              rcases List.mem_cons.mp he with rfl | he
              · exact le_rfl
              · exact (hrest e he).le
            rw [shiftRight_succ, ← hei] at hrp
            dsimp only at hrp h1
            omega
        · intro r hr hrp ⟨e, he, hei⟩
          refine ihcl e' he' r hr hrp ⟨e, ?_, hei⟩
          rcases List.mem_cons.mp he with rfl | he
          · have := habove e' he'
            rw [← hrp, shiftRight_succ, ← hei] at this
            dsimp only at this
            omega
          · exact he

/-- A frontier at level `l`: sorted by index, every query below one of its nodes, and every node
reached by its queries' climbs. -/
structure Frontier (l : Nat) (nodes : List (Nat × Nat × Vector F d)) : Prop where
  sorted : nodes.Pairwise fun a b ↦ a.1 < b.1
  covers : ∀ r (hr : r < indices.length), ∃ e ∈ nodes, e.1 = indices[r] >>> l
  climbs : ∀ e ∈ nodes, Climbs hash compress rows n indices l e

/-- A walk over `levels` levels from a frontier at level `l` ends at a frontier at level
`l + levels`. -/
theorem frontier_walk : ∀ (levels l padded : Nat) (nodes : List (Nat × Nat × Vector F d))
    (sibs : List (Vector F d)),
    Frontier (hash := hash) (compress := compress) (rows := rows) (n := n) (indices := indices)
      l nodes →
    Frontier (hash := hash) (compress := compress) (rows := rows) (n := n) (indices := indices)
      (l + levels) (walk hash compress rows levels padded nodes sibs).1
  | 0, l, _, nodes, sibs, h => by rw [walk_zero]; exact h
  | levels + 1, l, padded, nodes, sibs, h => by
    rw [walk_succ, show l + (levels + 1) = l + 1 + levels by omega]
    refine frontier_walk levels (l + 1) _ _ _ ?_
    obtain ⟨hs, hp, hc, hcl⟩ := level_spec (sibs := sibs) nodes l h.sorted h.climbs
    refine ⟨hs, fun r hr ↦ ?_, fun e' he' r hr hrp ↦ ?_⟩
    · obtain ⟨e, he, hei⟩ := h.covers r hr
      obtain ⟨e', he', h'⟩ := hc e he
      exact ⟨e', he', by rw [h', hei, shiftRight_succ]⟩
    · obtain ⟨e, he, hei⟩ := h.covers r hr
      exact hcl e' he' r hr hrp ⟨e, he, hei⟩

/-- The frontier's indices are the distinct indices, sorted. -/
theorem pairwise_frontier (indices : List Nat) :
    (frontier indices).Pairwise fun a b ↦ a.1 < b.1 := by
  unfold frontier
  rw [List.pairwise_map]
  have hle := List.pairwise_mergeSort (le := fun a b : Nat ↦ decide (a ≤ b))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) indices.dedup
  have hnd : (indices.dedup.mergeSort fun a b ↦ decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup indices)
  refine (hle.and hnd).imp fun {a b} ⟨h1, h2⟩ ↦ ?_
  simp only [decide_eq_true_eq] at h1
  omega

theorem mem_frontier {indices : List Nat} {e : Nat × Nat} :
    e ∈ frontier indices ↔ e.1 ∈ indices ∧ e.2 = indices.idxOf e.1 := by
  unfold frontier
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    rw [List.mem_mergeSort, List.mem_dedup] at hi
    exact ⟨hi, rfl⟩
  · rintro ⟨h1, h2⟩
    refine List.mem_map.mpr ⟨e.1, by rw [List.mem_mergeSort, List.mem_dedup]; exact h1, ?_⟩
    rw [← h2]

end Restore

/-! ### Accepted multi-openings -/

section Accept
variable (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)

/-- Two rows lists of `n` matrices that agree entrywise are equal. -/
theorem eq_of_zip_all {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (xs ys : List α), xs.length = ys.length → (xs.zip ys).all (fun p ↦ p.1 == p.2) → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, eq_of_zip_all xs ys (by simpa only [List.length_cons, Nat.add_right_cancel_iff]
      using hl) h.2]

/-- The shape checks of a multi-opening of matrices of one height `2 ^ k`: as many rows as
indices, `n` rows per query, indices below the height, and equal rows at equal indices. -/
theorem multiShapeOk_spec [DecidableEq F] {n k : Nat} {dims : List (Nat × Nat)}
    (hdims : dims.map (·.1) = List.replicate n (2 ^ k)) {indices : List Nat}
    {rows : List (List (List F))} {sibs : List (Vector F d)}
    (h : multiShapeOk dims (2 ^ k) k indices rows sibs = true) :
    rows.length = indices.length ∧ (∀ r < rows.length, (rows.getD r []).length = n) ∧
      (∀ r (hr : r < indices.length), indices[r] < 2 ^ k) ∧
      ∀ r q (hr : r < indices.length) (hq : q < indices.length), indices[r] = indices[q] →
        rows.getD r [] = rows.getD q [] := by
  have hlen : dims.length = n := by
    rw [← List.length_map (f := (·.1)), hdims, List.length_replicate]
  have hh : ∀ x ∈ dims, x.1 = 2 ^ k := fun x hx ↦ by
    have : x.1 ∈ dims.map (·.1) := List.mem_map_of_mem hx
    rw [hdims] at this
    exact List.eq_of_mem_replicate this
  simp only [multiShapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hrl⟩, hw⟩, hidx⟩, hcons⟩, -⟩ := h
  have hgetD : ∀ r (hr : r < rows.length), rows.getD r [] = rows[r] := fun r hr ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  have hrow : ∀ r < rows.length, (rows.getD r []).length = n := fun r hr ↦ by
    rw [hgetD r hr]
    exact (hw _ (List.getElem_mem hr)).1.trans hlen
  refine ⟨hrl, hrow, fun r hr ↦ hidx _ (List.getElem_mem hr), fun r q hr hq he ↦ ?_⟩
  have hr' : r < rows.length := hrl ▸ hr
  have hq' : q < rows.length := hrl ▸ hq
  have hmem : ∀ j (hj : j < indices.length), (indices[j], rows.getD j []) ∈ indices.zip rows :=
    fun j hj ↦ by
      rw [hgetD j (hrl ▸ hj)]
      exact List.mem_iff_getElem.mpr ⟨j, by rw [List.length_zip]; omega,
        by rw [List.getElem_zip]⟩
  have hc := hcons _ (hmem r hr) _ (hmem q hq)
  have hshift : ∀ x ∈ dims, Merkle.log2Ceil (2 ^ k) - Merkle.log2Ceil x.1 = 0 :=
    fun x hx ↦ by rw [hh x hx, Nat.sub_self]
  apply eq_of_zip_all
  · rw [hrow r hr', hrow q hq']
  · rw [List.all_eq_true]
    intro p hp
    obtain ⟨j, hj, hpj⟩ := List.mem_iff_getElem.mp hp
    have hjd : j < dims.length := by
      simp only [List.length_zip, hrow r hr', hrow q hq', Nat.min_self] at hj; omega
    have := hc (dims[j], p) (List.mem_iff_getElem.mpr ⟨j, by
      simp only [List.length_zip, hrow r hr', hrow q hq', Nat.min_self] at hj ⊢; omega,
      by rw [List.getElem_zip, hpj]⟩)
    rw [hshift _ (List.getElem_mem hjd), Nat.shiftRight_zero, Nat.shiftRight_zero, he,
      bne_self_eq_false, Bool.false_or] at this
    exact this

theorem nextPowerOfTwo_two_pow : ∀ k, (2 ^ k).nextPowerOfTwo = 2 ^ k :=
  fun k ↦ Nat.nextPowerOfTwo_eq_self (go k)
where
  go : ∀ k, (2 ^ k).isPowerOfTwo
    | 0 => Nat.isPowerOfTwo_one
    | k + 1 => by rw [Nat.pow_succ]; exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo (go k)

/-- A climb without shorter matrices does not read the padded height. -/
theorem climb_nil_padded (values : List (List F)) :
    ∀ (path : List (Vector F d)) (i padded padded' : Nat) (r : Vector F d),
      climb hash compress values path [] i padded r = climb hash compress values path [] i padded' r
  | [], _, _, _, _ => rfl
  | _ :: path, i, padded, padded', r => by
    simp only [climb]
    exact climb_nil_padded values path _ _ _ _

variable [Zero F]

/-- **Restoring the paths.** An accepted multi-opening of `n > 0` matrices of one height `2 ^ k`
gives every query an accepted single opening of its rows. -/
theorem verifyBatch_of_verifyMulti [DecidableEq F] (commit : Vector F d) (n k : Nat) (hn : 0 < n)
    (dims : List (Nat × Nat)) (hdims : dims.map (·.1) = List.replicate n (2 ^ k))
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Vector F d))
    (h : verifyMultiM (m := Id) hash compress commit dims indices rows sibs = true)
    (r : Nat) (hr : r < indices.length) :
    ∃ path, verifyBatch hash compress commit (List.replicate n (2 ^ k)) indices[r]
      (rows.getD r []) path = true := by
  have hpad : (2 ^ k).nextPowerOfTwo = 2 ^ k := nextPowerOfTwo_two_pow k
  unfold verifyMultiM at h
  rw [hdims, heightGroups_replicate n _ hn] at h
  dsimp only at h
  rw [hpad, Nat.log2_two_pow] at h
  split at h
  swap
  · exact absurd h Bool.false_ne_true
  rename_i hshape
  obtain ⟨hrl, hrow, hidx, hcons⟩ := multiShapeOk_spec hdims hshape
  -- The leaves: the initial frontier.
  set leaves := (frontier indices).map fun (e : Nat × Nat) ↦
    (e.1, e.2, leafOf hash rows n e.2) with hleaves
  have hl : ((frontier indices).mapM (m := Id) fun (x : Nat × Nat) ↦ match x with
      | (i, q) => do
        return (i, q, ← hash ((List.range n).flatMap fun k ↦ (rows.getD q []).getD k []))) =
      leaves := by
    rw [hleaves]
    exact List.idRun_mapM
  have h0 : Frontier (hash := hash) (compress := compress) (rows := rows) (n := n)
      (indices := indices) 0 leaves := by
    refine ⟨?_, fun r' hr' ↦ ?_, fun e he r' hr' hre ↦ ?_⟩
    · rw [hleaves, List.pairwise_map]
      exact pairwise_frontier indices
    · refine ⟨(indices[r'], indices.idxOf indices[r'], leafOf hash rows n
        (indices.idxOf indices[r'])), ?_, by rw [Nat.shiftRight_zero]⟩
      exact List.mem_map.mpr ⟨(indices[r'], indices.idxOf indices[r']),
        mem_frontier.mpr ⟨List.getElem_mem hr', rfl⟩, rfl⟩
    · obtain ⟨⟨i, q⟩, hiq, rfl⟩ := List.mem_map.mp he
      obtain ⟨hi, hq⟩ := mem_frontier.mp hiq
      dsimp only at hi hq
      subst hq
      rw [Nat.shiftRight_zero] at hre
      dsimp only at hre ⊢
      refine ⟨[], rfl, ?_⟩
      have hq : indices.idxOf i < indices.length := List.idxOf_lt_length_of_mem hi
      have hqi : indices[indices.idxOf i] = i := List.getElem_idxOf hq
      rw [show climb hash compress (rows.getD r' []) [] [] indices[r'] 0 (leafOf hash rows n r') =
        leafOf hash rows n r' from rfl, leafOf, leafOf,
        hcons r' (indices.idxOf i) hr' hq (by rw [hre, hqi])]
  rw [hl] at h
  have hk := frontier_walk (hash := hash) (compress := compress) k 0 (2 ^ k) leaves sibs h0
  rw [Nat.zero_add] at hk
  change (walk hash compress rows k (2 ^ k) leaves sibs).1.all
    (fun (x : Nat × Nat × Vector F d) ↦ x.2.2 == commit) = true at h
  obtain ⟨e, he, hei⟩ := hk.covers r hr
  obtain ⟨p, hp, hc⟩ := hk.climbs e he r hr hei.symm
  have hcommit : e.2.2 = commit := by
    rw [List.all_eq_true] at h
    exact beq_iff_eq.mp (h e he)
  refine ⟨p, ?_⟩
  have hr' : r < rows.length := hrl ▸ hr
  simp only [verifyBatch, heightGroups_replicate n _ hn, List.tail_cons, List.zip_nil_right,
    List.all_nil, Bool.true_and, List.length_replicate, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, hpad, Nat.log2_two_pow, hp, hrow r hr', hidx r hr, true_and]
  rw [hashRows, ← hcommit, ← hc, climb_nil_padded hash compress _ p _ _ 0]
  rfl

end Accept

/-! ### Honest multi-openings -/

section Honest
variable (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
  (g : Nat → Vector F d)

local notation "N" => nodeValue compress g

/-- The nodes of a level, each with its digest in the tree of leaves `g`. -/
def nodesAt (l : Nat) (ns : List (Nat × Nat)) : List (Nat × Nat × Vector F d) :=
  ns.map fun e ↦ (e.1, e.2, N l e.1)

/-- A parent is the compression of its node and the node's sibling, on the node's side. -/
theorem nodeValue_parent (l i : Nat) :
    (if i % 2 = 0 then compress (N l i) (N l (i ^^^ 1)) else compress (N l (i ^^^ 1)) (N l i)) =
      N (l + 1) (i / 2) := by
  rw [nodeValue_succ]
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
  by_cases h : i % 2 = 0
  · simp only [hx, h, ↓reduceIte]
    congr 2 <;> omega
  · simp only [hx, h, ↓reduceIte]
    congr 2 <;> omega

variable [Zero F]

/-- One level of the honest walk: the pruned siblings of the leads' paths take the frontier's
nodes to their parents. -/
theorem level_prune (paths : List (List (Vector F d))) (l : Nat) :
    ∀ (ns : List (Nat × Nat)) (rest : List (Vector F d)),
      (∀ e ∈ ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1)) →
      level compress (nodesAt compress g l ns) ((pruneLevel paths l ns).2 ++ rest) =
        (nodesAt compress g (l + 1) (pruneLevel paths l ns).1, rest)
  | [], rest, _ => rfl
  | [(i, q)], rest, h => by
    simp only [nodesAt, List.map_cons, List.map_nil, pruneLevel, List.singleton_append,
      level_single, List.headD_cons, List.tail_cons]
    rw [h (i, q) (List.mem_singleton_self _), nodeValue_parent]
  | (i, q) :: (j, q') :: ns, rest, h => by
    have h1 := h (i, q) List.mem_cons_self
    have hj : ∀ e ∈ (j, q') :: ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1) :=
      fun e he ↦ h e (List.mem_cons_of_mem _ he)
    have hns : ∀ e ∈ ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1) :=
      fun e he ↦ hj e (List.mem_cons_of_mem _ he)
    simp only [nodesAt, List.map_cons]
    rw [level_cons_cons]
    simp only [pruneLevel]
    split
    · rename_i hp
      obtain ⟨he, rfl⟩ := hp
      have := level_prune paths l ns rest hns
      simp only [nodesAt] at this
      rw [this]
      simp only [List.map_cons]
      rw [nodeValue_succ, show 2 * (i / 2) = i by omega]
    · have := level_prune paths l ((j, q') :: ns) rest hj
      simp only [nodesAt, List.map_cons] at this
      simp only [List.cons_append, List.headD_cons, List.tail_cons, this, h1, nodeValue_parent,
        List.map_cons]

/-- The parents of `pruneLevel`, each the parent of a node led by the node's lead. -/
theorem pruneLevel_parents (paths : List (List (Vector F d))) (l : Nat) :
    ∀ ns : List (Nat × Nat), ∀ e' ∈ (pruneLevel paths l ns).1, ∃ e ∈ ns, e' = (e.1 / 2, e.2)
  | [], e', he' => absurd he' List.not_mem_nil
  | [(i, q)], e', he' => by
    simp only [pruneLevel, List.mem_singleton] at he'
    exact ⟨(i, q), List.mem_singleton_self _, he'⟩
  | (i, q) :: (j, q') :: ns, e', he' => by
    simp only [pruneLevel] at he'
    split at he'
    · rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨e, he, rfl⟩ := pruneLevel_parents paths l ns e' he'
        exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he), rfl⟩
    · rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨e, he, rfl⟩ := pruneLevel_parents paths l ((j, q') :: ns) e' he'
        exact ⟨e, List.mem_cons_of_mem _ he, rfl⟩

/-- `pruneLevel` takes as many siblings, and keeps the same parents, as `countLevel`. -/
theorem pruneLevel_count (paths : List (List (Vector F d))) (l : Nat) :
    ∀ ns : List (Nat × Nat), (pruneLevel paths l ns).2.length = (countLevel (ns.map (·.1))).2 ∧
      (pruneLevel paths l ns).1.map (·.1) = (countLevel (ns.map (·.1))).1
  | [] => ⟨rfl, rfl⟩
  | [(i, q)] => ⟨rfl, rfl⟩
  | (i, q) :: (j, q') :: ns => by
    simp only [pruneLevel, List.map_cons, countLevel]
    split
    · obtain ⟨h1, h2⟩ := pruneLevel_count paths l ns
      exact ⟨h1, by rw [List.map_cons, h2]⟩
    · obtain ⟨h1, h2⟩ := pruneLevel_count paths l ((j, q') :: ns)
      simp only [List.map_cons] at h1 h2
      exact ⟨by rw [List.length_cons, h1], by rw [List.map_cons, h2]⟩

/-- `pruneWalk` takes the siblings `siblingCount` counts. -/
theorem length_pruneWalk (paths : List (List (Vector F d))) :
    ∀ (levels l : Nat) (ns : List (Nat × Nat)),
      (pruneWalk paths levels l ns).length = siblingCount levels (ns.map (·.1))
  | 0, _, _ => rfl
  | levels + 1, l, ns => by
    obtain ⟨h1, h2⟩ := pruneLevel_count paths l ns
    simp only [pruneWalk, siblingCount, List.length_append, h1, length_pruneWalk paths levels,
      h2]

/-- The honest walk over `levels` levels from the frontier `ns` at level `l`, whose leads open
the tree's paths: every node is the tree's node. -/
theorem walk_prune (rows : List (List (List F))) (indices : List Nat) (k : Nat)
    (paths : List (List (Vector F d)))
    (hpaths : ∀ q (hq : q < indices.length), ∀ j < k,
      (paths.getD q []).getD j 0 = N j ((indices[q] >>> j) ^^^ 1)) :
    ∀ (levels l padded : Nat) (ns : List (Nat × Nat)) (rest : List (Vector F d)),
      l + levels ≤ k → (∀ e ∈ ns, ∃ h : e.2 < indices.length, indices[e.2] >>> l = e.1) →
      ∃ ns' : List (Nat × Nat), (∀ e ∈ ns', ∃ h : e.2 < indices.length,
          indices[e.2] >>> (l + levels) = e.1) ∧
        walk hash compress rows levels padded (nodesAt compress g l ns)
          (pruneWalk paths levels l ns ++ rest) = (nodesAt compress g (l + levels) ns', rest)
  | 0, l, _, ns, rest, _, hns => ⟨ns, hns, rfl⟩
  | levels + 1, l, padded, ns, rest, hk, hns => by
    have hlev : ∀ e ∈ ns, (paths.getD e.2 []).getD l 0 = N l (e.1 ^^^ 1) := fun e he ↦ by
      obtain ⟨hq, hi⟩ := hns e he
      rw [hpaths e.2 hq l (by omega), hi]
    have hpar : ∀ e ∈ (pruneLevel paths l ns).1, ∃ h : e.2 < indices.length,
        indices[e.2] >>> (l + 1) = e.1 := fun e' he' ↦ by
      obtain ⟨e, he, rfl⟩ := pruneLevel_parents paths l ns e' he'
      obtain ⟨hq, hi⟩ := hns e he
      exact ⟨hq, by rw [shiftRight_succ, hi]⟩
    simp only [pruneWalk, List.append_assoc]
    rw [walk_succ, level_prune compress g paths l ns _ hlev]
    obtain ⟨ns', h1, h2⟩ := walk_prune rows indices k paths hpaths levels (l + 1) (padded / 2)
      (pruneLevel paths l ns).1 rest (by omega) hpar
    exact ⟨ns', by rw [show l + (levels + 1) = l + 1 + levels by omega]; exact h1,
      by rw [h2, show l + 1 + levels = l + (levels + 1) by omega]⟩

/-- **Honest multi-openings verify.** The multi-opening at `indices` of `n > 0` matrices of one
height `2 ^ k` whose leaves hash to `g`, with the rows at the indices and the pruned siblings of
the tree's paths, is accepted against the tree's root. -/
theorem verifyMulti_prune [DecidableEq F] (n k : Nat) (hn : 0 < n) (dims : List (Nat × Nat))
    (hdims : dims.map (·.1) = List.replicate n (2 ^ k)) (rowsAt : Nat → List (List F))
    (hw : ∀ i, (rowsAt i).map List.length = dims.map (·.2))
    (hleaf : ∀ i, hash ((List.range n).flatMap fun m ↦ (rowsAt i).getD m []) = g i)
    (indices : List Nat) (hidx : ∀ i ∈ indices, i < 2 ^ k) (paths : List (List (Vector F d)))
    (hpaths : ∀ q (hq : q < indices.length), ∀ j < k,
      (paths.getD q []).getD j 0 = N j ((indices[q] >>> j) ^^^ 1)) :
    verifyMultiM (m := Id) hash compress (N k 0) dims indices (indices.map rowsAt)
      (prune k indices paths) = true := by
  have hlen : dims.length = n := by
    rw [← List.length_map (f := (·.1)), hdims, List.length_replicate]
  have hh : ∀ x ∈ dims, x.1 = 2 ^ k := fun x hx ↦ by
    have : x.1 ∈ dims.map (·.1) := List.mem_map_of_mem hx
    rw [hdims] at this
    exact List.eq_of_mem_replicate this
  have hrowlen : ∀ i, (rowsAt i).length = dims.length := fun i ↦ by
    rw [← List.length_map (f := List.length), hw, List.length_map]
  have hzip : ∀ i, ∀ x ∈ (rowsAt i).zip dims, x.1.length = x.2.2 := fun i x hx ↦ by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.getElem_zip]
    have hj1 : j < (rowsAt i).length := by rw [List.length_zip] at hj; omega
    have := congrArg (·[j]?) (hw i)
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj1,
      List.getElem?_eq_getElem (show j < dims.length by rw [← hrowlen i]; exact hj1),
      Option.map_some, Option.some.injEq] at this
    exact this
  have hgetD : ∀ q (hq : q < indices.length), (indices.map rowsAt).getD q [] = rowsAt indices[q] :=
    fun q hq ↦ by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq,
        Option.map_some, Option.getD_some]
  have hshape : multiShapeOk dims (2 ^ k) k indices (indices.map rowsAt)
      (prune k indices paths) = true := by
    simp only [multiShapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
      List.length_map]
    have hzipself : ∀ i, ∀ x ∈ dims.zip ((rowsAt i).zip (rowsAt i)), x.2.1 = x.2.2 :=
      fun i x hx ↦ by
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
        simp only [List.getElem_zip]
    have hmemzip : ∀ a ∈ indices.zip (indices.map rowsAt), a.2 = rowsAt a.1 := fun a ha ↦ by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
      simp only [List.getElem_zip, List.getElem_map]
    refine ⟨⟨⟨⟨⟨⟨fun x hx ↦ ?_, Nat.two_pow_pos k⟩, trivial⟩, fun r hr ↦ ?_⟩, hidx⟩, ?_⟩, ?_⟩
    · rw [hh x hx, Nat.sub_self, Nat.shiftRight_zero]
      have := Nat.two_pow_pos k
      omega
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
      exact ⟨hrowlen i, hzip i⟩
    · intro a ha b hb x hx
      rw [hh x.1 (List.of_mem_zip hx).1, Nat.sub_self, Nat.shiftRight_zero, Nat.shiftRight_zero]
      by_cases he : a.1 = b.1
      · rw [hmemzip a ha, hmemzip b hb, he] at hx
        rw [he, hzipself b.1 x hx]
        simp only [bne_self_eq_false, beq_self_eq_true, Bool.false_or]
      · have : (a.1 != b.1) = true := bne_iff_ne.mpr he
        rw [this, Bool.true_or]
    · rw [prune, length_pruneWalk]
  have hpad : (2 ^ k).nextPowerOfTwo = 2 ^ k := nextPowerOfTwo_two_pow k
  unfold verifyMultiM
  rw [hdims, heightGroups_replicate n _ hn]
  dsimp only
  rw [hpad, Nat.log2_two_pow]
  simp only [hshape, ↓reduceIte]
  have hleaves : ((frontier indices).mapM (m := Id) fun (x : Nat × Nat) ↦ match x with
      | (i, q) => do
        return (i, q, ← hash ((List.range n).flatMap fun m ↦
          ((indices.map rowsAt).getD q []).getD m []))) =
        nodesAt compress g 0 (frontier indices) := by
    rw [nodesAt]
    refine List.idRun_mapM.trans ?_
    apply List.map_congr_left
    rintro ⟨i, q⟩ he
    obtain ⟨hi, hq⟩ := mem_frontier.mp he
    dsimp only at hi hq ⊢
    have hql : q < indices.length := hq ▸ List.idxOf_lt_length_of_mem hi
    have hqi : indices[q] = i := by subst hq; exact List.getElem_idxOf hql
    rw [hgetD q hql, hqi, hleaf, nodeValue_zero]
    rfl
  rw [hleaves]
  obtain ⟨ns', hns', hwalk⟩ := walk_prune hash compress g (indices.map rowsAt) indices k paths
    hpaths k 0 (2 ^ k) (frontier indices) [] (by omega) fun ⟨i, q⟩ he ↦ by
      obtain ⟨hi, hq⟩ := mem_frontier.mp he
      dsimp only at hi hq ⊢
      subst hq
      have hql : indices.idxOf i < indices.length := List.idxOf_lt_length_of_mem hi
      exact ⟨hql, by rw [Nat.shiftRight_zero]; exact List.getElem_idxOf hql⟩
  rw [prune, ← List.append_nil (pruneWalk paths k 0 (frontier indices))]
  change ((walk hash compress _ k (2 ^ k) _ _).1.all fun (x : Nat × Nat × Vector F d) ↦
    x.2.2 == N k 0) = true
  rw [hwalk, List.all_eq_true]
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hq, hi⟩ := hns' e he
  have h0 : indices[e.2] >>> (0 + k) = 0 := by
    rw [Nat.zero_add, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (hidx _ (List.getElem_mem hq))
  rw [h0] at hi
  simp only [← hi, Nat.zero_add, beq_self_eq_true]

end Honest



end CompStark.Merkle
