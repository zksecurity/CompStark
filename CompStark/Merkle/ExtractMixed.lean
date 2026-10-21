/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Extract
public import CompStark.Merkle.MixedMulti

/-! # Extracting committed rows of mixed heights

A Plonky3 tree of matrices of heights `2 ^ j ≤ 2 ^ K` hashes the rows of the tallest matrices into
its leaves, and at each level `t < K` that some matrices' height `2 ^ t` reaches, it compresses
every node's pair of children with the hash of those matrices' rows (`injNode`). Extraction reads
such a tree back from a cache of hash queries, walking down from the root:

* `nodeAtInj cache inj t i root`: the node `i` of level `t`, where the levels `inj` inject: an
  injected node's first child is its pair, whose children are the next level's nodes.
* `extractGroup cache inj K t i root`: the rows of the matrices of height `2 ^ t` at their row
  `i`: a cached preimage of the leaf at level `K`, or of an injected node's second child.
* `extractGroup_of_climb`: in an injective cache, an opening's climb whose queries are all cached
  (`ClimbCached`) opens the extracted rows of every group of matrices.
* `climbCached_of_fresh`: answering every query outside the cache by a digest `dstar` that no
  cached query answers or holds, a climb that does not end at `dstar` made only cached queries.
* `extractGroup_eq_of_noPrediction`: extraction does not change when the cache grows by entries
  whose answers are not digests the extraction could reach.

Without injected levels, `extractGroup` at the leaf level is `extractRow` (`extractGroup_nil`).
-/

@[expose] public section
namespace CompStark.Merkle

/-! ### Extraction through injected levels -/

section Extract
variable {F D : Type*}

/-- The node `i` of level `t` (`2 ^ t` nodes) below `root` of a tree that injects at the levels
`inj`, walking down cached compressions: an injected node compresses its pair of children with an
injected hash. -/
noncomputable def nodeAtInj (cache : Cache F D) (inj : List Nat) :
    (t i : Nat) → (root : D) → Option D
  | 0, _, root => some root
  | t + 1, i, root => (nodeAtInj cache inj t (i / 2) root).bind fun y ↦
      ((if t ∈ inj then (children cache y).map Prod.fst else some y).bind fun p ↦
        (children cache p).map fun lr ↦ if i % 2 = 0 then lr.1 else lr.2)

/-- The rows at row `i` of the matrices of height `2 ^ t` of the tree with leaves at level `K`: a
cached preimage of leaf `i`, or of the hash node `i` of level `t` is compressed with. -/
noncomputable def extractGroup (cache : Cache F D) (inj : List Nat) (K t i : Nat) (root : D) :
    Option (List F) :=
  (nodeAtInj cache inj t i root).bind fun y ↦
    ((if t = K then some y else (children cache y).map Prod.snd).bind fun h ↦
      pick fun row ↦ cache.leaf row h)

/-- Without injected levels, the nodes are `nodeAt`'s. -/
theorem nodeAtInj_nil (cache : Cache F D) : ∀ t i root, nodeAtInj cache [] t i root =
    nodeAt cache t i root
  | 0, _, _ => rfl
  | t + 1, i, root => by
    simp only [nodeAtInj, nodeAt, List.not_mem_nil, ↓reduceIte, Option.bind_some,
      nodeAtInj_nil cache t]

/-- Without injected levels, extraction at the leaf level is `extractRow`. -/
theorem extractGroup_nil (cache : Cache F D) (K i : Nat) (root : D) :
    extractGroup cache [] K K i root = extractRow cache K i root := by
  simp only [extractGroup, extractRow, nodeAtInj_nil, ↓reduceIte, Option.bind_some]

/-- Every node and injected hash extraction reaches is `Known`. -/
theorem known_of_nodeAtInj (cache : Cache F D) (inj : List Nat) (root : D) :
    (t i : Nat) → (y : D) → nodeAtInj cache inj t i root = some y → cache.Known root y
  | 0, _, y, h => by
    simp only [nodeAtInj, Option.some.injEq] at h
    exact Or.inl h.symm
  | t + 1, i, y, h => by
    simp only [nodeAtInj, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨parent, -, p, -, ⟨left, right⟩, hc, hy⟩ := h
    have hnode : cache.node left right p :=
      pick_spec (fun pair : D × D ↦ cache.node pair.1 pair.2 p) _ hc
    refine Or.inr ⟨left, right, p, hnode, ?_⟩
    by_cases hi : i % 2 = 0
    · simp only [hi, ↓reduceIte] at hy; exact Or.inl hy.symm
    · simp only [hi, ↓reduceIte] at hy; exact Or.inr hy.symm

/-- Without prediction, extracted nodes stay the same. -/
theorem nodeAtInj_eq_of_noPrediction (now later : Cache F D) (inj : List Nat) (root : D)
    (h : now.NoPrediction later root) :
    (t i : Nat) → nodeAtInj later inj t i root = nodeAtInj now inj t i root
  | 0, _ => rfl
  | t + 1, i => by
    simp only [nodeAtInj, nodeAtInj_eq_of_noPrediction now later inj root h t (i / 2)]
    cases hp : nodeAtInj now inj t (i / 2) root with
    | none => rfl
    | some y =>
      have hy := known_of_nodeAtInj now inj root _ _ _ hp
      simp only [Option.bind_some, children_eq_of_noPrediction now later root y h hy]
      split
      · cases hc : children now y with
        | none => rfl
        | some pq =>
          have hpq : now.node pq.1 pq.2 y :=
            pick_spec (fun pair : D × D ↦ now.node pair.1 pair.2 y) _ hc
          simp only [Option.map_some, Option.bind_some,
            children_eq_of_noPrediction now later root pq.1 h
              (Or.inr ⟨pq.1, pq.2, y, hpq, Or.inl rfl⟩)]
      · simp only [Option.bind_some, children_eq_of_noPrediction now later root y h hy]

/-- **Stability of extraction.** Extraction under `root` does not change when the cache grows by
entries that predict no digest it can reach. -/
theorem extractGroup_eq_of_noPrediction (now later : Cache F D) (inj : List Nat) (root : D)
    (h : now.NoPrediction later root) (K t i : Nat) :
    extractGroup later inj K t i root = extractGroup now inj K t i root := by
  simp only [extractGroup, nodeAtInj_eq_of_noPrediction now later inj root h]
  cases hp : nodeAtInj now inj t i root with
  | none => rfl
  | some y =>
    have hy := known_of_nodeAtInj now inj root _ _ _ hp
    have hleaf : ∀ x, now.Known root x →
        (fun row ↦ later.leaf row x) = fun row ↦ now.leaf row x := fun x hx ↦
      funext fun row ↦ propext ⟨fun hl ↦ h.leaf_new _ _ hl hx, h.leaf_le _ _⟩
    simp only [Option.bind_some]
    split
    · simp only [Option.bind_some, hleaf y hy]
    · rw [children_eq_of_noPrediction now later root y h hy]
      cases hc : children now y with
      | none => rfl
      | some pq =>
        have hpq : now.node pq.1 pq.2 y :=
          pick_spec (fun pair : D × D ↦ now.node pair.1 pair.2 y) _ hc
        simp only [Option.map_some, Option.bind_some,
          hleaf pq.2 (Or.inr ⟨pq.1, pq.2, y, hpq, Or.inr rfl⟩)]

end Extract

/-! ### Openings of mixed heights -/

section Climb
variable {F : Type} {d : Nat} (cache : Cache F (Vector F d)) (hash : List F → Vector F d)
  (compress : Vector F d → Vector F d → Vector F d) (values : List (List F))

/-- Every query of a climb is cached: each compression with a sibling, and each injected group's
leaf hash and its compression. -/
def ClimbCached : List (Vector F d) → List (Nat × List Nat) → Nat → Nat → Vector F d → Prop
  | [], _, _, _, _ => True
  | s :: path, groups, i, padded, x =>
    let pair := if i % 2 = 0 then (x, s) else (s, x)
    let z := compress pair.1 pair.2
    cache.node pair.1 pair.2 z ∧
      match groups with
      | (h, is) :: rest =>
        if h.nextPowerOfTwo = padded / 2 then
          cache.leaf (is.flatMap fun m ↦ values.getD m [])
              (hash (is.flatMap fun m ↦ values.getD m [])) ∧
            cache.node z (hash (is.flatMap fun m ↦ values.getD m []))
              (compress z (hash (is.flatMap fun m ↦ values.getD m []))) ∧
            ClimbCached path rest (i / 2) (padded / 2)
              (compress z (hash (is.flatMap fun m ↦ values.getD m [])))
        else ClimbCached path groups (i / 2) (padded / 2) z
      | [] => ClimbCached path [] (i / 2) (padded / 2) z

/-- **Opened climbs are extracted.** In an injective cache, a climb from `x` at node `i` of level
`t`, its queries cached, injecting the groups `groups` of heights `2 ^ l < 2 ^ t` at their
levels, which are the injected levels `inj` below `t`, ends at `root` only if `x` is the
extracted node and every group's rows are extracted at their row. -/
theorem extractGroup_of_climb (hinj : cache.Injective) (inj : List Nat) (K : Nat)
    (root : Vector F d) :
    ∀ (path : List (Vector F d)) (t : Nat) (groups : List (Nat × List Nat)) (i : Nat)
      (x : Vector F d), path.length = t → t ≤ K →
      groups.Pairwise (fun a b ↦ b.1 < a.1) → (∀ g ∈ groups, ∃ l < t, g.1 = 2 ^ l) →
      (∀ l < t, l ∈ inj ↔ ∃ g ∈ groups, g.1 = 2 ^ l) →
      ClimbCached cache hash compress values path groups i (2 ^ t) x →
      climb hash compress values path groups i (2 ^ t) x = root →
      nodeAtInj cache inj t i root = some x ∧
        ∀ g ∈ groups, ∀ l, g.1 = 2 ^ l →
          extractGroup cache inj K l (i >>> (t - l)) root =
            some (g.2.flatMap fun m ↦ values.getD m [])
  | [], t, groups, i, x, hl, _, _, hg, _, _, hc => by
    simp only [List.length_nil] at hl
    subst hl
    refine ⟨by rw [← hc]; rfl, fun g hgm ↦ ?_⟩
    obtain ⟨l, hl, -⟩ := hg g hgm
    omega
  | s :: path, t, groups, i, x, hl, hK, hs, hg, hinjl, hcached, hc => by
    simp only [List.length_cons] at hl
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hpad : 2 ^ (t' + 1) / 2 = 2 ^ t' := by
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    set pair := if i % 2 = 0 then (x, s) else (s, x) with hpair
    set z := compress pair.1 pair.2
    obtain ⟨hz, hrest⟩ := hcached
    -- The pair's children give the node `x`.
    have hchild : (children cache z).map (fun lr ↦ if i % 2 = 0 then lr.1 else lr.2) =
        some x := by
      rw [children_eq cache hinj _ _ _ hz]
      by_cases hi : i % 2 = 0 <;> simp only [hi, ↓reduceIte, Option.map_some]
    -- A group of a level below `t'`, its rows extracted at their row from level `t'` down.
    have hlow : ∀ (groups' : List (Nat × List Nat)), (∀ g ∈ groups', ∃ l < t', g.1 = 2 ^ l) →
        (∀ g ∈ groups', ∀ l, g.1 = 2 ^ l → extractGroup cache inj K l ((i / 2) >>> (t' - l)) root =
          some (g.2.flatMap fun m ↦ values.getD m [])) →
        ∀ g ∈ groups', ∀ l, g.1 = 2 ^ l → extractGroup cache inj K l (i >>> (t' + 1 - l)) root =
          some (g.2.flatMap fun m ↦ values.getD m []) := by
      intro groups' hg' hext g hgm l hgl
      obtain ⟨l', hl', hgl'⟩ := hg' g hgm
      have hll : l = l' := Nat.pow_right_injective (le_refl 2) (hgl.symm.trans hgl')
      subst hll
      have hidx : i >>> (t' + 1 - l) = (i / 2) >>> (t' - l) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          ← Nat.pow_succ']
        congr 2
        omega
      rw [hidx]
      exact hext g hgm l hgl
    have hz' : (if i % 2 = 0 then compress x s else compress s x) = z := by
      by_cases hi : i % 2 = 0 <;> simp only [hpair, hi, ↓reduceIte, z]
    -- A node whose children's pair is `z` reaches `x`.
    have hnode : ∀ x', nodeAtInj cache inj t' (i / 2) root = some x' →
        (if t' ∈ inj then (children cache x').map Prod.fst else some x') = some z →
        nodeAtInj cache inj (t' + 1) i root = some x := by
      intro x' hn hp
      simp only [nodeAtInj, hn, Option.bind_some, hp, hchild]
    rcases groups with _ | ⟨⟨h, is⟩, rest⟩
    · have hc' : climb hash compress values path [] (i / 2) (2 ^ t') z = root := by
        rw [← hc, ← hpad, ← hz']
        rfl
      have hrest' : ClimbCached cache hash compress values path [] (i / 2) (2 ^ t') z := by
        rw [← hpad]; exact hrest
      have ht' : t' ∉ inj := fun h ↦ by
        obtain ⟨g, hg, -⟩ := (hinjl t' (by omega)).mp h
        exact absurd hg List.not_mem_nil
      obtain ⟨hn, -⟩ := extractGroup_of_climb hinj inj K root path t' [] (i / 2) z (by omega) (by omega)
        List.Pairwise.nil (fun _ h ↦ absurd h List.not_mem_nil)
        (fun l hl ↦ hinjl l (by omega)) hrest' hc'
      exact ⟨hnode z hn (by simp only [ht', ↓reduceIte]), fun g hg ↦ absurd hg List.not_mem_nil⟩
    · have hle : ∀ g ∈ rest, g.1 < h := fun g hg ↦ List.rel_of_pairwise_cons hs hg
      obtain ⟨lh, hlh, hhl⟩ := hg _ List.mem_cons_self
      change h = 2 ^ lh at hhl
      have hrestlev : ∀ g ∈ rest, ∃ l < t', g.1 = 2 ^ l := fun g hgm ↦ by
        obtain ⟨l, hl, hgl⟩ := hg g (List.mem_cons_of_mem _ hgm)
        refine ⟨l, ?_, hgl⟩
        have h1 := hle g hgm
        rw [hgl, hhl] at h1
        have := (Nat.pow_lt_pow_iff_right (by decide)).mp h1
        omega
      by_cases hh : h.nextPowerOfTwo = 2 ^ (t' + 1) / 2
      · rw [hpad, hhl, nextPowerOfTwo_two_pow] at hh
        have hlt : lh = t' := Nat.pow_right_injective (le_refl 2) hh
        subst hlt
        set hv := hash (is.flatMap fun m ↦ values.getD m [])
        have hcond : h.nextPowerOfTwo = 2 ^ (lh + 1) / 2 := by
          rw [hpad, hhl, nextPowerOfTwo_two_pow]
        have hcl : climb hash compress values (s :: path) ((h, is) :: rest) i (2 ^ (lh + 1)) x =
            climb hash compress values path rest (i / 2) (2 ^ lh) (compress z hv) := by
          rw [climb_cons_cons, ite_eq_left_of_eq_true _ _ (eq_true hcond), hpad, hz']
          rfl
        simp only [hcond, ↓reduceIte, hpad] at hrest
        obtain ⟨hleafc, hzv, hrest'⟩ := hrest
        have hinjt : lh ∈ inj := (hinjl lh (by omega)).mpr ⟨_, List.mem_cons_self, hhl⟩
        obtain ⟨hn, hext⟩ := extractGroup_of_climb hinj inj K root path lh rest (i / 2)
          (compress z hv) (by omega) (by omega) hs.of_cons hrestlev
          (fun l hl ↦ by
            rw [hinjl l (by omega)]
            constructor
            · rintro ⟨g, hgm, hgl⟩
              rcases List.mem_cons.mp hgm with rfl | hgm
              · rw [hhl] at hgl
                have := Nat.pow_right_injective (le_refl 2) hgl
                omega
              · exact ⟨g, hgm, hgl⟩
            · rintro ⟨g, hgm, hgl⟩
              exact ⟨g, List.mem_cons_of_mem _ hgm, hgl⟩)
          hrest' (hcl ▸ hc)
        have hch : children cache (compress z hv) = some (z, hv) :=
          children_eq cache hinj _ _ _ hzv
        refine ⟨hnode _ hn (by simp only [hinjt, ↓reduceIte, hch, Option.map_some]),
          fun g hgm l hgl ↦ ?_⟩
        rcases List.mem_cons.mp hgm with rfl | hgm
        · rw [hhl] at hgl
          have := Nat.pow_right_injective (le_refl 2) hgl
          subst this
          have hi1 : i >>> (lh + 1 - lh) = i / 2 := by
            rw [show lh + 1 - lh = 1 by omega, Nat.shiftRight_eq_div_pow, Nat.pow_one]
          rw [hi1]
          simp only [extractGroup, hn, Option.bind_some, show lh ≠ K by omega, ↓reduceIte, hch,
            Option.map_some]
          exact pick_eq _ _ hleafc fun row h' ↦ hinj.leaf _ _ _ h' hleafc
        · exact hlow rest hrestlev hext g hgm l hgl
      · have hlt' : lh < t' := by
          rw [hpad, hhl, nextPowerOfTwo_two_pow] at hh
          have : lh ≠ t' := fun e ↦ hh (by rw [e])
          omega
        have hcl : climb hash compress values (s :: path) ((h, is) :: rest) i (2 ^ (t' + 1)) x =
            climb hash compress values path ((h, is) :: rest) (i / 2) (2 ^ t') z := by
          rw [climb_cons_cons, ite_eq_right_of_eq_false _ _ (eq_false hh), hpad, hz']
          rfl
        have hrest' : ClimbCached cache hash compress values path ((h, is) :: rest) (i / 2)
            (2 ^ t') z := by
          have := hrest
          simp only [hh, ↓reduceIte] at this
          rw [hpad] at this
          exact this
        have ht' : t' ∉ inj := fun hm ↦ by
          obtain ⟨g, hgm, hgl⟩ := (hinjl t' (by omega)).mp hm
          rcases List.mem_cons.mp hgm with rfl | hgm
          · rw [hhl] at hgl
            have := Nat.pow_right_injective (le_refl 2) hgl
            omega
          · obtain ⟨l, hl, hgl'⟩ := hrestlev g hgm
            rw [hgl] at hgl'
            have := Nat.pow_right_injective (le_refl 2) hgl'
            omega
        obtain ⟨hn, hext⟩ := extractGroup_of_climb hinj inj K root path t' ((h, is) :: rest)
          (i / 2) z (by omega) (by omega) hs
          (fun g hgm ↦ by
            rcases List.mem_cons.mp hgm with rfl | hgm
            · exact ⟨lh, hlt', hhl⟩
            · exact hrestlev g hgm)
          (fun l hl ↦ hinjl l (by omega)) hrest' (hcl ▸ hc)
        refine ⟨hnode z hn (by simp only [ht', ↓reduceIte]), ?_⟩
        refine hlow _ (fun g hgm ↦ ?_) hext
        rcases List.mem_cons.mp hgm with rfl | hgm
        · exact ⟨lh, hlt', hhl⟩
        · exact hrestlev g hgm

/-- **Climbing out of the cache.** If every uncached query is answered `dstar`, and a compression
involving `dstar` gives `dstar`, a climb that does not end at `dstar` starts off `dstar` and makes
only cached queries. -/
theorem climbCached_of_fresh (dstar : Vector F d)
    (hnode : ∀ a b, compress a b ≠ dstar → cache.node a b (compress a b))
    (hleaf : ∀ row, hash row ≠ dstar → cache.leaf row (hash row))
    (hstuck : ∀ a b, (a = dstar ∨ b = dstar) → compress a b = dstar) :
    ∀ (path : List (Vector F d)) (groups : List (Nat × List Nat)) (i padded : Nat)
      (x : Vector F d), climb hash compress values path groups i padded x ≠ dstar →
      x ≠ dstar ∧ ClimbCached cache hash compress values path groups i padded x
  | [], _, _, _, x, h => ⟨h, trivial⟩
  | s :: path, groups, i, padded, x, h => by
    set pair := if i % 2 = 0 then (x, s) else (s, x) with hpair
    set z := compress pair.1 pair.2
    have hz' : (if i % 2 = 0 then compress x s else compress s x) = z := by
      by_cases hi : i % 2 = 0 <;> simp only [hpair, hi, ↓reduceIte, z]
    have hx : z ≠ dstar → x ≠ dstar := fun hzd hxd ↦ hzd (hstuck _ _ (by
      by_cases hi : i % 2 = 0 <;> simp only [hpair, hi, ↓reduceIte, hxd, true_or, or_true]))
    match groups with
    | [] =>
      rw [climb_cons_nil] at h
      obtain ⟨hzd, hrest⟩ := climbCached_of_fresh dstar hnode hleaf hstuck path [] _ _ z
        (by simpa only [injectWith, hz'] using h)
      exact ⟨hx hzd, hnode _ _ hzd, hrest⟩
    | (h', is) :: rest =>
      rw [climb_cons_cons] at h
      by_cases hc : h'.nextPowerOfTwo = padded / 2
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
        obtain ⟨hzv, hrest⟩ := climbCached_of_fresh dstar hnode hleaf hstuck path rest _ _
          (compress z (hash (is.flatMap fun m ↦ values.getD m [])))
          (by simpa only [injectWith, hz'] using h)
        have hzd : z ≠ dstar := fun e ↦ hzv (hstuck _ _ (Or.inl e))
        have hvd : hash (is.flatMap fun m ↦ values.getD m []) ≠ dstar :=
          fun e ↦ hzv (hstuck _ _ (Or.inr e))
        refine ⟨hx hzd, hnode _ _ hzd, ?_⟩
        simp only [hc, ↓reduceIte]
        exact ⟨hleaf _ hvd, hnode _ _ hzv, hrest⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
        obtain ⟨hzd, hrest⟩ := climbCached_of_fresh dstar hnode hleaf hstuck path _ _ _ z
          (by simpa only [injectWith, hz'] using h)
        refine ⟨hx hzd, hnode _ _ hzd, ?_⟩
        simp only [hc, ↓reduceIte]
        exact hrest

/-- The injected levels of matrices of heights `heights` below `2 ^ K`. -/
def injLevels (K : Nat) (heights : List Nat) : List Nat :=
  (heights.filter (· < 2 ^ K)).map Nat.log2

/-- **Accepted openings of mixed heights open the extracted rows.** In an injective cache, an
accepted opening at `i` of matrices of heights `2 ^ j ≤ 2 ^ K`, some of height `2 ^ K`, whose
leaf hash and climb are cached, opens every group's extracted rows: the opened rows of the
matrices of each height, concatenated, at the index shifted to that height. -/
theorem extractGroup_of_verifyBatch [DecidableEq F] (hinj : cache.Injective) (root : Vector F d)
    (K : Nat) (heights : List Nat) (hpow : ∀ h ∈ heights, ∃ j ≤ K, h = 2 ^ j)
    (htop : 2 ^ K ∈ heights) (i : Nat) (path : List (Vector F d))
    (hv : verifyBatch hash compress root heights i values path = true)
    (hleaf : ∀ g ∈ (heightGroups heights).head?, cache.leaf (g.2.flatMap fun m ↦ values.getD m [])
      (hash (g.2.flatMap fun m ↦ values.getD m [])))
    (hc : ∀ g ∈ (heightGroups heights).head?, ClimbCached cache hash compress values path
      (heightGroups heights).tail i (2 ^ K) (hash (g.2.flatMap fun m ↦ values.getD m []))) :
    ∀ g ∈ heightGroups heights, ∀ l, g.1 = 2 ^ l →
      extractGroup cache (injLevels K heights) K l (i >>> (K - l)) root =
        some (g.2.flatMap fun m ↦ values.getD m []) := by
  obtain ⟨keys, hk, hmem, hG⟩ := heightGroups_eq heights
  obtain ⟨ks, hks⟩ : ∃ ks, keys = 2 ^ K :: ks := by
    rcases keys with _ | ⟨a, ks⟩
    · exact absurd ((hmem _).mpr htop) List.not_mem_nil
    · refine ⟨ks, ?_⟩
      obtain ⟨j, hj, rfl⟩ := hpow a ((hmem a).mp List.mem_cons_self)
      rcases List.mem_cons.mp ((hmem _).mpr htop) with h | h
      · rw [h]
      · have := List.rel_of_pairwise_cons hk h
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj
        omega
  set idx : Nat → List Nat := fun h ↦ (List.range heights.length).filter (heights.getD · 0 == h)
  have hksl : ∀ h ∈ ks, ∃ j < K, h = 2 ^ j := fun h hh ↦ by
    obtain ⟨j, hj, rfl⟩ := hpow h ((hmem h).mp (hks ▸ List.mem_cons_of_mem _ hh))
    have := List.rel_of_pairwise_cons (hks ▸ hk) hh
    exact ⟨j, (Nat.pow_lt_pow_iff_right (by decide)).mp this, rfl⟩
  rw [hG, hks, List.map_cons] at hleaf hc ⊢
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq', List.tail_cons]
    at hleaf hc
  simp only [verifyBatch, hG, hks, List.map_cons, nextPowerOfTwo_two_pow, Nat.log2_two_pow,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨-, -⟩, hpl⟩, hi⟩, hclimb⟩ := hv
  have hinjl : ∀ l < K, l ∈ injLevels K heights ↔
      ∃ g ∈ ks.map (fun h ↦ (h, idx h)), g.1 = 2 ^ l := by
    intro l hl
    simp only [injLevels, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists]
    constructor
    · rintro ⟨h, ⟨hh, hlt⟩, rfl⟩
      obtain ⟨j, -, rfl⟩ := hpow h hh
      rw [Nat.log2_two_pow]
      have hk' : 2 ^ j ∈ keys := (hmem _).mpr hh
      rw [hks] at hk'
      rcases List.mem_cons.mp hk' with e | hk'
      · omega
      · exact ⟨2 ^ j, idx (2 ^ j), ⟨_, hk', rfl⟩, rfl⟩
    · rintro ⟨h, is, hm, rfl⟩
      obtain ⟨h', hh', he⟩ := hm
      rw [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      refine ⟨2 ^ l, ⟨(hmem _).mp (hks ▸ List.mem_cons_of_mem _ hh'),
        Nat.pow_lt_pow_right (by decide) hl⟩, Nat.log2_two_pow⟩
  obtain ⟨hn, hext⟩ := extractGroup_of_climb cache hash compress values hinj (injLevels K heights)
    K root path K (ks.map fun h ↦ (h, idx h)) i _ hpl le_rfl
    (List.pairwise_map.mpr ((hks ▸ hk).of_cons.imp id))
    (fun g hg ↦ by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      exact hksl h hh)
    hinjl hc hclimb
  intro g hg l hgl
  rcases List.mem_cons.mp hg with rfl | hg
  · have hl : l = K := Nat.pow_right_injective (le_refl 2) hgl.symm
    subst hl
    simp only [extractGroup, Nat.sub_self, Nat.shiftRight_zero, hn, Option.bind_some, ↓reduceIte]
    exact pick_eq _ _ hleaf fun row h' ↦ hinj.leaf _ _ _ h' hleaf
  · exact hext g hg l hgl

end Climb

end CompStark.Merkle
