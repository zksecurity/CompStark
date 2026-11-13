/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Bytes
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Masked

/-! Binary Keccak trees and the checked pruned opening path in
`crates/verifier/src/merkle.rs` at the pinned leanMultisig revision. Shared children
are paired before reading hints; all remaining hints must be consumed. -/

namespace CompStark.Keccak.Commit
open CompStark.BinaryFields
open MixedMerkleTree.Knowledge OracleComp
open scoped ENNReal
@[expose] public section

/-- Binary node at a height above the leaves, without injections or a cap. -/
def node (leaves : ℕ → List K) : ℕ → ℕ → Digest
  | 0, i => hashLeaf (leaves i)
  | height + 1, i => compress (node leaves height (2 * i)) (node leaves height (2 * i + 1))

/-- Root-only commitment to `2^height` leaves. -/
def root (height : ℕ) (leaves : ℕ → List K) : Digest := node leaves height 0

/-- The concrete tree is VCVio's mixed tree with no injections. -/
theorem node_eq_mixed (height level index : ℕ) (leaves : ℕ → List K) :
    node leaves level index =
      MixedMerkleTree.node hashLeaf compress height leaves (fun _ ↦ none) level index := by
  induction level generalizing index with
  | zero => rfl
  | succ level ih =>
      simp only [node, MixedMerkleTree.node, Option.map_none, MixedMerkleTree.inject, ih]

/-- A root is the mixed tree's height-zero singleton cap. -/
theorem cap_eq_root (height : ℕ) (leaves : ℕ → List K) :
    MixedMerkleTree.cap hashLeaf compress height leaves (fun _ ↦ none) 0 =
      [root height leaves] := by
  simp only [MixedMerkleTree.cap, Nat.pow_zero, List.range_one, List.map_cons,
    List.map_nil, Nat.sub_zero, ← node_eq_mixed, root]

/-- An expanded wire opening has its original query index and full reconstructed image. -/
structure Path where
  /-- Global leaf position. -/
  index : ℕ
  /-- Full leaf image, including omitted zero prefix. -/
  leaf : List K
  /-- Bottom-up sibling digests. -/
  siblings : List Digest

/-- The VCVio opening represented by a wire path. -/
def Path.toMixed (p : Path) : Opening (List K) Digest :=
  ⟨p.index, p.leaf, fun _ ↦ none, p.siblings⟩

/-- Pruned rows are sorted by distinct query position; siblings are level-first, then left to right. -/
structure Pruned where
  /-- Wire-order rows without the publicly determined zero prefix. -/
  leafData : List (List K)
  /-- Each sibling outside the queried subtree is transmitted once. -/
  siblingHashes : List Digest

/-- Canonical distinct ascending query positions. -/
def positions (queries : List ℕ) : List ℕ := (queries.mergeSort (· ≤ ·)).eraseDups

/-- Deduplication turns a nondecreasing natural list into a strictly increasing list. -/
theorem strict_eraseDups (xs : List ℕ) (hs : xs.Pairwise (· ≤ ·)) :
    xs.eraseDups.Pairwise (· < ·) := by
  suffices aux : ∀ n (ys : List ℕ), ys.length ≤ n → ys.Pairwise (· ≤ ·) →
      ys.eraseDups.Pairwise (· < ·) from aux xs.length xs (Nat.le_refl _) hs
  intro n
  induction n with
  | zero =>
      intro ys length _
      have : ys = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero length)
      subst ys
      exact List.Pairwise.nil
  | succ n ih =>
      intro ys length sorted
      cases ys with
      | nil => exact List.Pairwise.nil
      | cons x ys =>
          rw [List.eraseDups_cons]
          refine List.Pairwise.cons ?_ (ih _ ?_ (sorted.of_cons.filter _))
          · intro y hy
            have mem := List.mem_filter.mp (List.mem_eraseDups.mp hy)
            have := List.rel_of_pairwise_cons sorted mem.1
            have : y ≠ x := by simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using mem.2
            omega
          · have := List.length_filter_le (fun b ↦ !b == x) ys
            simp only [List.length_cons] at length
            omega

/-- Canonical query positions are strictly increasing. -/
theorem positions_sorted (queries : List ℕ) : (positions queries).Pairwise (· < ·) := by
  apply strict_eraseDups
  have sorted := List.pairwise_mergeSort (le := fun a b : ℕ ↦ decide (a ≤ b))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) queries
  exact sorted.imp fun h ↦ of_decide_eq_true h

/-- Successful option traversal relates each input to its corresponding output. -/
theorem mapM_some_rel {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) : List.Forall₂ (fun x y ↦ f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil =>
      have h : ([] : List β) = ys := Option.some.inj h
      subst ys
      exact .nil
  | cons x xs ih =>
      cases hx : f x with
      | none => simp [List.mapM_cons, hx] at h
      | some y =>
          cases hz : xs.mapM f with
          | none => simp [List.mapM_cons, hx, hz] at h
          | some zs =>
              have h : y :: zs = ys := by simpa [List.mapM_cons, hx, hz] using h
              subst ys
              exact .cons hx (ih _ hz)

/-- A pointwise list relation supplies an input for every output. -/
theorem rel_output {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => exact False.elim (List.not_mem_nil hy)
  | cons h hs ih =>
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨x, hx, hr⟩ := ih hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- Pointwise agreement of projections gives equal projected lists. -/
theorem rel_map_eq {α β γ : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (f : α → γ) (g : β → γ)
    (eq : ∀ x y, R x y → f x = g y) : xs.map f = ys.map g := by
  induction h with
  | nil => rfl
  | cons hr hs ih => exact congrArg₂ List.cons (eq _ _ hr) ih

/-- A successful association lookup names an entry of the list. -/
theorem lookup_mem {nodes : List (ℕ × Digest)} {i : ℕ} {x : Digest}
    (h : nodes.lookup i = some x) : (i, x) ∈ nodes := by
  induction nodes with
  | nil => simp only [List.lookup_nil, reduceCtorEq] at h
  | cons e nodes ih =>
      obtain ⟨j, y⟩ := e
      by_cases eq : i = j
      · subst j
        simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at h
        subst y
        exact List.mem_cons_self
      · simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr eq] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- Strictly ordered association lists look up every member at its key. -/
theorem lookup_of_mem {nodes : List (ℕ × Digest)}
    (sorted : nodes.Pairwise fun a b ↦ a.1 < b.1) {e : ℕ × Digest} (he : e ∈ nodes) :
    nodes.lookup e.1 = some e.2 := by
  induction nodes with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons a nodes ih =>
      obtain ⟨i, x⟩ := a
      rcases List.mem_cons.mp he with rfl | he
      · simp only [List.lookup_cons, beq_self_eq_true]
      · have ne := Nat.ne_of_gt (List.rel_of_pairwise_cons sorted he)
        simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr ne] using ih sorted.of_cons he

section Generic
variable (hash : ByteArray → Digest)

/-- One bottom-up level: parents, the sibling of each active node, and unused hints. -/
def expandLevel : ℕ → List (ℕ × Digest) → List Digest →
    Option (List (ℕ × Digest) × List (ℕ × Digest) × List Digest)
  | _, [], hints => some ([], [], hints)
  | 0, _ :: _, _ => none
  | fuel + 1, (i, x) :: rest, hints => do
      match rest with
      | (j, y) :: tail =>
        if i % 2 = 0 ∧ j = i + 1 then
          let (parents, siblings, unused) ← expandLevel fuel tail hints
          pure ((i / 2, (pairWith hash) x y) :: parents, (i, y) :: (j, x) :: siblings, unused)
        else
          let sibling ← hints.head?
          let (parents, siblings, unused) ← expandLevel fuel rest hints.tail
          pure ((i / 2, MixedMerkleTree.pairUp (pairWith hash) i x sibling) :: parents,
            (i, sibling) :: siblings, unused)
      | [] =>
        let sibling ← hints.head?
        pure ([(i / 2, MixedMerkleTree.pairUp (pairWith hash) i x sibling)], [(i, sibling)], hints.tail)

/-- A successful level keeps its parents sorted, records their origins, and assigns each
active child the sibling actually used to form its parent. -/
structure LevelSound (nodes parents siblings : List (ℕ × Digest)) : Prop where
  /-- Parents remain strictly ordered by index. -/
  sorted : parents.Pairwise fun a b ↦ a.1 < b.1
  /-- Every parent originates at an active child. -/
  origins : ∀ p ∈ parents, ∃ e ∈ nodes, p.1 = e.1 / 2
  /-- Every child has a parent formed with its recorded sibling. -/
  children : ∀ e ∈ nodes, ∃ p ∈ parents, p.1 = e.1 / 2 ∧
    ∃ sibling, siblings.lookup e.1 = some sibling ∧
      p.2 = MixedMerkleTree.pairUp (pairWith hash) e.1 e.2 sibling

/-- Successful shared-sibling reconstruction preserves the binary parent relation. -/
theorem expandLevel_sound (fuel : ℕ) (nodes : List (ℕ × Digest)) (hints : List Digest)
    (parents siblings : List (ℕ × Digest)) (unused : List Digest)
    (sorted : nodes.Pairwise fun a b ↦ a.1 < b.1)
    (expanded : expandLevel hash fuel nodes hints = some (parents, siblings, unused)) :
    LevelSound hash nodes parents siblings := by
  induction fuel generalizing nodes hints parents siblings unused with
  | zero =>
      cases nodes with
      | nil =>
          simp only [expandLevel, Option.some.injEq, Prod.mk.injEq] at expanded
          obtain ⟨rfl, rfl, rfl⟩ := expanded
          exact ⟨List.Pairwise.nil, fun _ h ↦ False.elim (List.not_mem_nil h),
            fun _ h ↦ False.elim (List.not_mem_nil h)⟩
      | cons e nodes => simp only [expandLevel, reduceCtorEq] at expanded
  | succ fuel ih =>
      cases nodes with
      | nil =>
          simp only [expandLevel, Option.some.injEq, Prod.mk.injEq] at expanded
          obtain ⟨rfl, rfl, rfl⟩ := expanded
          exact ⟨List.Pairwise.nil, fun _ h ↦ False.elim (List.not_mem_nil h),
            fun _ h ↦ False.elim (List.not_mem_nil h)⟩
      | cons e rest =>
          obtain ⟨i, x⟩ := e
          cases rest with
          | nil =>
              cases hints with
              | nil => simp [expandLevel] at expanded
              | cons sibling hints =>
                  simp only [expandLevel, List.head?_cons, List.tail_cons] at expanded
                  obtain ⟨rfl, rfl, rfl⟩ := expanded
                  refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
                  · intro p hp
                    obtain rfl := List.mem_singleton.mp hp
                    exact ⟨_, List.mem_singleton_self _, rfl⟩
                  · intro e he
                    obtain rfl := List.mem_singleton.mp he
                    exact ⟨_, List.mem_singleton_self _, rfl, sibling, by simp, rfl⟩
          | cons e tail =>
              obtain ⟨j, y⟩ := e
              have hij : i < j := List.rel_of_pairwise_cons sorted List.mem_cons_self
              have htail : ∀ e ∈ tail, j < e.1 :=
                fun e he ↦ List.rel_of_pairwise_cons sorted.of_cons he
              by_cases paired : i % 2 = 0 ∧ j = i + 1
              · cases rec : expandLevel hash fuel tail hints with
                | none => simp [expandLevel, paired, rec] at expanded
                | some result =>
                    obtain ⟨ps, ss, uu⟩ := result
                    simp only [expandLevel, paired, rec] at expanded
                    obtain ⟨rfl, rfl, rfl⟩ := expanded
                    have sound := ih tail hints ps ss uu sorted.of_cons.of_cons rec
                    have above : ∀ p ∈ ps, i / 2 < p.1 := by
                      intro p hp
                      obtain ⟨e, he, origin⟩ := sound.origins p hp
                      have := htail e he
                      have := paired.2
                      omega
                    refine ⟨List.Pairwise.cons above sound.sorted, ?_, ?_⟩
                    · intro p hp
                      rcases List.mem_cons.mp hp with rfl | hp
                      · exact ⟨_, List.mem_cons_self, rfl⟩
                      · obtain ⟨e, he, origin⟩ := sound.origins p hp
                        exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he), origin⟩
                    · intro e he
                      rcases List.mem_cons.mp he with rfl | he
                      · refine ⟨_, List.mem_cons_self, rfl, y, by simp, ?_⟩
                        simp only [MixedMerkleTree.pairUp, paired.1, ↓reduceIte]
                      rcases List.mem_cons.mp he with rfl | he
                      · refine ⟨_, List.mem_cons_self, by dsimp only; omega, x, ?_, ?_⟩
                        · simp only [List.lookup_cons, ← paired.2, beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hij), beq_self_eq_true]
                        · have odd : j % 2 ≠ 0 := by omega
                          simp only [MixedMerkleTree.pairUp, odd, ↓reduceIte]
                      · obtain ⟨p, hp, origin, sibling, lookup, value⟩ := sound.children e he
                        have hji := htail e he
                        have hni : e.1 ≠ i := by omega
                        have hnj : e.1 ≠ j := by omega
                        exact ⟨p, List.mem_cons_of_mem _ hp, origin, sibling,
                          by simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hni,
                            paired.2.symm, beq_eq_false_iff_ne.mpr hnj, Bool.false_eq_true, ↓reduceIte] using lookup,
                          value⟩
              · cases hints with
                | nil => simp [expandLevel, paired] at expanded
                | cons sibling hints =>
                    cases rec : expandLevel hash fuel ((j,y)::tail) hints with
                    | none => simp [expandLevel, paired, rec] at expanded
                    | some result =>
                        obtain ⟨ps, ss, uu⟩ := result
                        simp only [expandLevel, paired, ↓reduceIte, List.head?_cons,
                          List.tail_cons, rec] at expanded
                        obtain ⟨rfl, rfl, rfl⟩ := expanded
                        have sound := ih ((j,y)::tail) hints ps ss uu sorted.of_cons rec
                        have above : ∀ p ∈ ps, i / 2 < p.1 := by
                          intro p hp
                          obtain ⟨e, he, origin⟩ := sound.origins p hp
                          rcases List.mem_cons.mp he with rfl | he
                          · dsimp only at origin; omega
                          · have := htail e he
                            omega
                        refine ⟨List.Pairwise.cons above sound.sorted, ?_, ?_⟩
                        · intro p hp
                          rcases List.mem_cons.mp hp with rfl | hp
                          · exact ⟨_, List.mem_cons_self, rfl⟩
                          · obtain ⟨e, he, origin⟩ := sound.origins p hp
                            exact ⟨e, List.mem_cons_of_mem _ he, origin⟩
                        · intro e he
                          rcases List.mem_cons.mp he with rfl | he
                          · exact ⟨_, List.mem_cons_self, rfl, sibling, by simp, rfl⟩
                          · obtain ⟨p, hp, origin, s, lookup, value⟩ := sound.children e he
                            have hni : e.1 ≠ i :=
                              Nat.ne_of_gt (List.rel_of_pairwise_cons sorted he)
                            exact ⟨p, List.mem_cons_of_mem _ hp, origin, s,
                              by simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hni,
                                Bool.false_eq_true, ↓reduceIte] using lookup, value⟩

/-- Reconstruct all levels and expand each query's path, sharing sibling computations. -/
def expandLevels : ℕ → ℕ → List (ℕ × Digest) → List Path → List Digest →
    Option (List (ℕ × Digest) × List Path × List Digest)
  | 0, _, nodes, paths, hints => some (nodes, paths, hints)
  | remaining + 1, level, nodes, paths, hints => do
      let (parents, siblings, unused) ← expandLevel hash nodes.length nodes hints
      let paths ← paths.mapM fun p ↦ do
        let sibling ← siblings.lookup (p.index >>> level)
        pure { p with siblings := p.siblings ++ [sibling] }
      expandLevels remaining (level + 1) parents paths unused

/-- The digest reached by a reconstructed path without injections. -/
def Path.digest (p : Path) : Digest :=
  MixedMerkleTree.climb (leafWith hash) (pairWith hash) (fun _ ↦ none) p.index ((leafWith hash) p.leaf) p.siblings

/-- Appending one sibling forms the next binary parent. -/
theorem Path.digest_append (p : Path) (s : Digest) :
    ({ p with siblings := p.siblings ++ [s] } : Path).digest hash =
      MixedMerkleTree.pairUp (pairWith hash) (p.index >>> p.siblings.length) (p.digest hash) s := by
  simp only [Path.digest, MixedMerkleTree.climb_append, MixedMerkleTree.climb_cons,
    MixedMerkleTree.inject, MixedMerkleTree.climb_nil]

/-- A frontier relates every partial path to its current ancestor. -/
def Frontier (height level : ℕ) (nodes : List (ℕ × Digest)) (paths : List Path) : Prop :=
  (nodes.Pairwise fun a b ↦ a.1 < b.1) ∧ ∀ p ∈ paths,
    p.siblings.length = level ∧ p.index < 2 ^ height ∧
      nodes.lookup (p.index >>> level) = some (p.digest hash)

/-- Recording a successful level preserves the frontier and the original query positions. -/
theorem advance_frontier (height level : ℕ) (nodes parents siblings : List (ℕ × Digest))
    (paths updated : List Path) (frontier : Frontier hash height level nodes paths)
    (sound : LevelSound hash nodes parents siblings)
    (mapped : paths.mapM (fun p ↦ do
      let sibling ← siblings.lookup (p.index >>> level)
      pure { p with siblings := p.siblings ++ [sibling] }) = some updated) :
    Frontier hash height (level + 1) parents updated ∧ updated.map Path.index = paths.map Path.index := by
  have rel := mapM_some_rel _ _ _ mapped
  have step : ∀ (p q : Path), (do
      let sibling ← siblings.lookup (p.index >>> level)
      pure { p with siblings := p.siblings ++ [sibling] }) = some q →
      ∃ s, siblings.lookup (p.index >>> level) = some s ∧
        q = { p with siblings := p.siblings ++ [s] } := by
    intro p q h
    cases hs : siblings.lookup (p.index >>> level) with
    | none => simp [hs] at h
    | some s => exact ⟨s, rfl, (Option.some.inj (by simpa [hs] using h)).symm⟩
  refine ⟨⟨sound.sorted, ?_⟩, ?_⟩
  · intro q hq
    obtain ⟨p, hp, hr⟩ := rel_output rel hq
    obtain ⟨s, hs, rfl⟩ := step p q hr
    obtain ⟨length, range, lookup⟩ := frontier.2 p hp
    obtain ⟨parent, mem, index, sibling, found, value⟩ :=
      sound.children _ (lookup_mem lookup)
    have same : sibling = s := Option.some.inj (found.symm.trans hs)
    subst sibling
    refine ⟨by simp only [List.length_append, List.length_singleton, length], range, ?_⟩
    have parentLookup := lookup_of_mem sound.sorted mem
    rw [index, value] at parentLookup
    simpa only [Path.digest_append, length, Nat.shiftRight_succ] using parentLookup
  · symm
    exact rel_map_eq rel Path.index Path.index fun p q hr ↦ by
      obtain ⟨s, hs, rfl⟩ := step p q hr
      rfl

/-- Repeated reconstruction preserves every partial path's ancestor relation. -/
theorem expandLevels_sound (remaining level height : ℕ)
    (nodes : List (ℕ × Digest)) (paths : List Path) (hints : List Digest)
    (outNodes : List (ℕ × Digest)) (outPaths : List Path) (unused : List Digest)
    (frontier : Frontier hash height level nodes paths)
    (expanded : expandLevels hash remaining level nodes paths hints = some (outNodes, outPaths, unused)) :
    Frontier hash height (level + remaining) outNodes outPaths ∧
      outPaths.map Path.index = paths.map Path.index := by
  induction remaining generalizing level nodes paths hints with
  | zero =>
      have eq : (nodes, paths, hints) = (outNodes, outPaths, unused) := Option.some.inj expanded
      obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj eq |>.imp_right Prod.mk.inj
      exact ⟨frontier, rfl⟩
  | succ remaining ih =>
      simp only [expandLevels] at expanded
      change (expandLevel hash nodes.length nodes hints).bind _ = _ at expanded
      obtain ⟨⟨parents, siblings, rest⟩, he, expanded⟩ := Option.bind_eq_some_iff.mp expanded
      change Option.bind (paths.mapM (m := Option) _) _ = _ at expanded
      obtain ⟨updated, hm, expanded⟩ := Option.bind_eq_some_iff.mp expanded
      have next := advance_frontier hash height level nodes parents siblings paths updated frontier
        (expandLevel_sound hash _ _ _ _ _ _ frontier.1 he) hm
      obtain ⟨final, indices⟩ := ih (level + 1) parents updated rest next.1 expanded
      exact ⟨by simpa only [Nat.add_assoc, Nat.add_comm 1 remaining] using final,
        indices.trans next.2⟩

/-- In a strictly sorted frontier, a zero-index lookup agrees with its first digest. -/
theorem head_lookup_zero (nodes : List (ℕ × Digest)) (top : ℕ × Digest) (value : Digest)
    (sorted : nodes.Pairwise fun a b ↦ a.1 < b.1) (head : nodes.head? = some top)
    (lookup : nodes.lookup 0 = some value) : top.2 = value := by
  cases nodes with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons e nodes =>
      have eq : e = top := Option.some.inj head
      subst e
      rcases List.mem_cons.mp (lookup_mem lookup) with eq | mem
      · exact (congrArg Prod.snd eq).symm
      · have := List.rel_of_pairwise_cons sorted mem
        exact False.elim (by omega)

/-- Rust's checked shape and expansion, returning paths in the original query order, with duplicates. -/
def expand (height rowWords leafWords : ℕ) (queries : List ℕ) (batch : Pruned) :
    Option (Digest × List Path) := do
  let ps := positions queries
  if ps.isEmpty || !(ps.all (· < 2 ^ height)) || ps.length != batch.leafData.length ||
      rowWords > leafWords || !(batch.leafData.all (fun row ↦ row.length == rowWords)) then none
  else do
    let paths := (ps.zip batch.leafData).map fun (i, row) ↦
      Path.mk i (restoreLeaf leafWords row) []
    let nodes := paths.map fun p ↦ (p.index, (leafWith hash) p.leaf)
    let (nodes, paths, unused) ← expandLevels hash height 0 nodes paths batch.siblingHashes
    if !unused.isEmpty then none else do
      let top ← nodes.head?
      let ordered ← queries.mapM fun i ↦ paths.find? (fun p ↦ p.index == i)
      pure (top.2, ordered)

/-- Acceptance authenticates the reconstructed batch root against the announced commitment. -/
def accepts (height rowWords leafWords : ℕ) (queries : List ℕ) (batch : Pruned)
    (commitment : Digest) : Bool :=
  match expand hash height rowWords leafWords queries batch with
  | none => false
  | some (digest, _) => digest == commitment

/-- Accepted shared-sibling openings transfer to verifying individual VCVio openings. -/
theorem accepted_openings_verify (height rowWords leafWords : ℕ) (queries : List ℕ)
    (batch : Pruned) (commitment : Digest) (paths : List Path)
    (expanded : expand hash height rowWords leafWords queries batch = some (commitment, paths)) :
    paths.map Path.index = queries ∧ ∀ p ∈ paths,
      p.toMixed.Verifies (leafWith hash) (pairWith hash) height 0 (fun _ ↦ false) [commitment] := by
  unfold expand at expanded
  dsimp only at expanded
  split at expanded
  · contradiction
  · rename_i valid
    have checks := valid
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false',
      bne_eq_false_iff_eq, decide_eq_false_iff_not, List.all_eq_true, decide_eq_true_eq,
      beq_iff_eq] at checks
    have range : ∀ i ∈ positions queries, i < 2 ^ height := checks.1.1.1.2
    have count : (positions queries).length = batch.leafData.length := checks.1.1.2
    let initial := ((positions queries).zip batch.leafData).map fun (i, row) ↦
      Path.mk i (restoreLeaf leafWords row) []
    have initialFrontier : Frontier hash height 0
        (initial.map fun p ↦ (p.index, (leafWith hash) p.leaf)) initial := by
      have proj : initial.map Path.index = ((positions queries).zip batch.leafData).map Prod.fst := by
        simp only [initial, List.map_map, Function.comp_def]
      have sorted : initial.Pairwise fun a b ↦ a.index < b.index := by
        rw [← List.pairwise_map]
        rw [proj]
        rw [List.map_fst_zip (Nat.le_of_eq count)]
        exact positions_sorted queries
      have sortedNodes : (initial.map fun p ↦ (p.index, (leafWith hash) p.leaf)).Pairwise
          (fun a b ↦ a.1 < b.1) := by simpa only [List.pairwise_map] using sorted
      refine ⟨sortedNodes, ?_⟩
      intro p hp
      obtain ⟨⟨i, row⟩, mem, rfl⟩ := List.mem_map.mp hp
      refine ⟨rfl, range i (List.of_mem_zip mem).1, ?_⟩
      exact lookup_of_mem sortedNodes
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, mem, rfl⟩, rfl⟩)
    change Option.bind (expandLevels hash height 0 _ initial batch.siblingHashes) _ = _ at expanded
    obtain ⟨⟨nodes, finalPaths, unused⟩, levels, expanded⟩ := Option.bind_eq_some_iff.mp expanded
    have frontier := (expandLevels_sound hash height 0 height _ initial _ nodes finalPaths unused
      initialFrontier levels).1
    simp only [Nat.zero_add] at frontier
    split at expanded
    · contradiction
    · change Option.bind nodes.head? _ = _ at expanded
      obtain ⟨top, head, expanded⟩ := Option.bind_eq_some_iff.mp expanded
      change Option.bind (queries.mapM (fun i ↦ finalPaths.find? (fun p ↦ p.index == i))) _ = _ at expanded
      obtain ⟨ordered, mapped, eq⟩ := Option.bind_eq_some_iff.mp expanded
      have eq : (top.2, ordered) = (commitment, paths) := Option.some.inj eq
      obtain ⟨topValue, rfl⟩ := Prod.mk.inj eq
      have rel := mapM_some_rel _ _ _ mapped
      refine ⟨?_, ?_⟩
      · simpa only [List.map_id] using
          (rel_map_eq rel id Path.index fun i p h ↦ by
            have eq : p.index = i := by simpa only [beq_iff_eq] using List.find?_some h
            exact eq.symm).symm
      · intro p hp
        obtain ⟨i, hi, found⟩ := rel_output rel hp
        obtain ⟨length, inRange, lookup⟩ := frontier.2 p (List.mem_of_find?_eq_some found)
        have shift : p.index >>> height = 0 := by
          rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt inRange]
        have rootValue : commitment = (p.digest hash) := by
          rw [shift] at lookup
          exact topValue ▸ head_lookup_zero nodes top (p.digest hash) frontier.1 head lookup
        refine ⟨Nat.zero_le _, rfl, inRange, length, fun _ _ ↦ rfl, ?_⟩
        simpa only [Path.toMixed, Nat.sub_zero, shift, List.getElem?_cons_zero, Path.digest]
          using congrArg some rootValue


end Generic

/-- An honest individual opening uses the same binary-tree sibling order as the wire paths. -/
def honestOpening (height : ℕ) (leaves : ℕ → List K) (index : ℕ) :
    Opening (List K) Digest :=
  ⟨index, leaves index, fun _ ↦ none,
    (List.range height).map fun level ↦ node leaves level ((index >>> level) ^^^ 1)⟩

/-- Every in-range honest leaf has a verifying VCVio opening against its commitment. -/
theorem honest_opening_verifies (height : ℕ) (leaves : ℕ → List K) (index : ℕ)
    (range : index < 2 ^ height) :
    (honestOpening height leaves index).Verifies hashLeaf compress height 0 (fun _ ↦ false)
      [root height leaves] := by
  have shift : index >>> height = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt range]
  have climb := MixedMerkleTree.climb_cap hashLeaf compress height leaves (fun _ ↦ none) 0 index
    (Nat.zero_le height) range
  have pays : MixedMerkleTree.pays (Payload := List K) height (fun _ ↦ none) index height = (fun _ ↦ none) := rfl
  simp only [Nat.sub_zero, pays, MixedMerkleTree.siblings,
    cap_eq_root, shift, List.getD_cons_zero, ← node_eq_mixed] at climb
  refine ⟨Nat.zero_le height, rfl, range, ?_, ?_, ?_⟩
  · simp only [honestOpening, List.length_map, List.length_range, Nat.sub_zero]
  · intro d _
    rfl
  · simpa only [honestOpening, Nat.sub_zero, shift, List.getElem?_cons_zero] using
      congrArg some climb.symm

/-- Flipping the low bit changes a node but preserves its parent. -/
theorem xor_one_facts (i : ℕ) : i ^^^ 1 ≠ i ∧ (i ^^^ 1) / 2 = i / 2 := by
  rw [MixedMerkleTree.xor_one_eq]
  omega

/-- An honest node paired with its sibling forms its tree parent. -/
theorem pairUp_node (leaves : ℕ → List K) (level i : ℕ) :
    MixedMerkleTree.pairUp compress i (node leaves level i) (node leaves level (i ^^^ 1)) =
      node leaves (level + 1) (i / 2) := by
  rw [node, MixedMerkleTree.xor_one_eq, MixedMerkleTree.pairUp]
  split <;> rename_i h
  · have left : 2 * (i / 2) = i := by omega
    have right : 2 * (i / 2) + (i + 1) % 2 = 2 * (i / 2) + 1 := by omega
    rw [right, left]
  · have right : 2 * (i / 2) + 1 = i := by omega
    have left : 2 * (i / 2) + (i + 1) % 2 = 2 * (i / 2) := by omega
    rw [left, right]

/-- A fresh head survives deduplication ahead of the deduplicated tail. -/
theorem eraseDups_fresh (i : ℕ) (xs : List ℕ) (fresh : i ∉ xs) :
    (i :: xs).eraseDups = i :: xs.eraseDups := by
  rw [List.eraseDups_cons]
  congr 1
  apply congrArg List.eraseDups
  apply List.filter_eq_self.mpr
  intro j hj
  have ne : j ≠ i := fun eq ↦ fresh (eq ▸ hj)
  simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using ne

/-- Removing a duplicate adjacent head does not change deduplication. -/
theorem eraseDups_repeat (i : ℕ) (xs : List ℕ) :
    (i :: i :: xs).eraseDups = (i :: xs).eraseDups := by
  simp only [List.eraseDups_cons, List.filter_cons, beq_self_eq_true, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

/-- Removing nodes with different parents leaves sibling membership unchanged. -/
theorem missing_filter_cons (i : ℕ) (rest : List ℕ)
    (above : ∀ j ∈ rest, i / 2 < j / 2) :
    (rest.filter fun j ↦ !(i :: rest).contains (j ^^^ 1)) =
      (rest.filter fun j ↦ !rest.contains (j ^^^ 1)) := by
  apply List.filter_congr
  intro j hj
  have ne : j ^^^ 1 ≠ i := by
    have := above j hj
    have := (xor_one_facts j).2
    omega
  simp only [List.contains_cons, beq_eq_false_iff_ne.mpr ne, Bool.false_or]

section Generic
variable (hash : ByteArray → Digest)

/-- Hints of the missing siblings reconstruct one level of any node values whose active nodes
pair up to their parents, and every active node is paired with its sibling value. -/
theorem expandLevel_eq (value next : ℕ → Digest) (fuel : ℕ) (active : List ℕ)
    (hints : List Digest) (sorted : active.Pairwise (· < ·)) (length : active.length ≤ fuel)
    (parent : ∀ i ∈ active, MixedMerkleTree.pairUp (pairWith hash) i (value i) (value (i ^^^ 1)) = next (i / 2)) :
    expandLevel hash fuel (active.map fun i ↦ (i, value i))
      (((active.filter fun i ↦ !active.contains (i ^^^ 1)).map fun i ↦ value (i ^^^ 1)) ++ hints) =
      some ((((active.map (· / 2)).eraseDups).map fun i ↦ (i, next i)),
        active.map (fun i ↦ (i, value (i ^^^ 1))), hints) := by
  induction fuel generalizing active hints with
  | zero =>
      have empty : active = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero length)
      subst active
      rfl
  | succ fuel ih =>
      cases active with
      | nil => rfl
      | cons i rest =>
          cases rest with
          | nil =>
              have missing : [i].contains (i ^^^ 1) = false := by
                simp only [List.contains_cons, List.contains_nil, Bool.or_false,
                  beq_eq_false_iff_ne.mpr (xor_one_facts i).1]
              simp only [List.map_cons, List.map_nil, List.filter_cons, missing, Bool.not_false, ↓reduceIte,
                List.filter_nil, List.cons_append, List.nil_append, expandLevel,
                List.head?_cons, List.tail_cons]
              simp only [eraseDups_fresh _ [] (List.not_mem_nil), List.eraseDups_nil,
                List.map_cons, List.map_nil]
              change some ([(i / 2, MixedMerkleTree.pairUp (pairWith hash) i (value i) (value (i ^^^ 1)))], _, _) = some _
              rw [parent i List.mem_cons_self]
          | cons j tail =>
              have hij := List.rel_of_pairwise_cons sorted List.mem_cons_self
              have tailAbove : ∀ k ∈ tail, j < k :=
                fun k hk ↦ List.rel_of_pairwise_cons sorted.of_cons hk
              by_cases paired : i % 2 = 0 ∧ j = i + 1
              · have eqi : i ^^^ 1 = j := by rw [MixedMerkleTree.xor_one_eq]; omega
                have eqj : j ^^^ 1 = i := by rw [MixedMerkleTree.xor_one_eq]; omega
                have above : ∀ k ∈ tail, i / 2 < k / 2 := by
                  intro k hk
                  have := tailAbove k hk
                  omega
                have abovej : ∀ k ∈ tail, j / 2 < k / 2 := by
                  intro k hk
                  have := above k hk
                  omega
                have filter : ((i :: j :: tail).filter fun k ↦ !(i :: j :: tail).contains (k ^^^ 1)) =
                    (tail.filter fun k ↦ !tail.contains (k ^^^ 1)) := by
                  simp only [List.filter_cons, eqi, eqj, List.contains_cons, beq_self_eq_true,
                    Bool.true_or, Bool.or_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  rw [← missing_filter_cons j tail abovej]
                  apply List.filter_congr
                  intro k hk
                  have ne : k ^^^ 1 ≠ i := by
                    have := above k hk
                    have := (xor_one_facts k).2
                    omega
                  simp only [List.contains_cons, beq_eq_false_iff_ne.mpr ne, Bool.false_or]
                have recursive := ih tail hints sorted.of_cons.of_cons
                  (by simp only [List.length_cons] at length; omega)
                  (fun k hk ↦ parent k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk)))
                have parentEq : j / 2 = i / 2 := by omega
                have fresh : i / 2 ∉ tail.map (· / 2) := by
                  rintro mem
                  obtain ⟨k, hk, eq⟩ := List.mem_map.mp mem
                  have := above k hk
                  omega
                rw [filter]
                simp only [List.map_cons]
                rw [expandLevel, ite_eq_left paired, recursive]
                rw [parentEq, eraseDups_repeat, eraseDups_fresh _ _ fresh]
                have pairValue : (pairWith hash) (value i) (value j) = next (i / 2) := by
                  rw [← eqi, ← parent i List.mem_cons_self]
                  simp only [MixedMerkleTree.pairUp, paired.1, ↓reduceIte]
                simp only [List.map_cons, pairValue, eqi, eqj]
                rfl
              · have above : ∀ k ∈ j :: tail, i / 2 < k / 2 := by
                  intro k hk
                  rcases List.mem_cons.mp hk with rfl | hk
                  · omega
                  · have := tailAbove k hk
                    omega
                have missing : (i :: j :: tail).contains (i ^^^ 1) = false := by
                  have absent : i ^^^ 1 ∉ j :: tail := by
                    intro mem
                    have := above _ mem
                    have := (xor_one_facts i).2
                    omega
                  simpa only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_cons,
                    not_or, (xor_one_facts i).1, not_false_eq_true, true_and] using absent
                have filter : ((i :: j :: tail).filter fun k ↦ !(i :: j :: tail).contains (k ^^^ 1)) =
                    i :: ((j :: tail).filter fun k ↦ !(j :: tail).contains (k ^^^ 1)) := by
                  rw [List.filter_cons]
                  simp only [missing, Bool.not_false, ↓reduceIte]
                  rw [missing_filter_cons i (j :: tail) above]
                have recursive := ih (j :: tail) hints sorted.of_cons
                  (by simp only [List.length_cons] at length ⊢; omega)
                  (fun k hk ↦ parent k (List.mem_cons_of_mem _ hk))
                have fresh : i / 2 ∉ (j :: tail).map (· / 2) := by
                  rintro mem
                  obtain ⟨k, hk, eq⟩ := List.mem_map.mp mem
                  have := above k hk
                  omega
                simp only [List.map_cons] at recursive fresh
                rw [filter]
                simp only [List.map_cons, List.cons_append]
                rw [expandLevel, ite_eq_right paired]
                simp only [List.head?_cons, List.tail_cons]
                change (expandLevel hash fuel _ _).bind _ = _
                rw [recursive, eraseDups_fresh _ _ fresh]
                simp only [List.map_cons]
                change some ((i / 2, MixedMerkleTree.pairUp (pairWith hash) i (value i)
                    (value (i ^^^ 1))) :: _, _, _) = some _
                rw [parent i List.mem_cons_self]

/-- Siblings omitted by each remaining pruning level of the node values, in ascending active-node
order. -/
def pruneLevels (height : ℕ) (value : ℕ → ℕ → Digest) : ℕ → List ℕ → List Digest
  | 0, _ => []
  | remaining + 1, active =>
      let level := height - (remaining + 1)
      ((active.filter fun i ↦ !active.contains (i ^^^ 1)).map
        fun i ↦ value level (i ^^^ 1)) ++
      pruneLevels height value remaining ((active.map (· / 2)).eraseDups)

/-- Honest pruned batch for wire-order rows, including shared siblings and omitted zero prefixes. -/
def honestBatch (height leafWords : ℕ) (rows : ℕ → List K) (queries : List ℕ) : Pruned :=
  ⟨(positions queries).map rows,
    pruneLevels height (node fun i ↦ restoreLeaf leafWords (rows i)) height (positions queries)⟩

/-- An option traversal succeeds when it succeeds on every input member. -/
theorem mapM_exists {α β : Type} (f : α → Option β) (xs : List α)
    (total : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨y, hy⟩ := total x List.mem_cons_self
      obtain ⟨ys, hs⟩ := ih (fun z hz ↦ total z (List.mem_cons_of_mem _ hz))
      exact ⟨y :: ys, by simp [List.mapM_cons, hy, hs]⟩

/-- Every result of a successful option traversal is the result of some input member. -/
theorem mapM_mem {α β : Type} (f : α → Option β) :
    (xs : List α) → (ys : List β) → xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h, y, hy => by
      cases h
      exact absurd hy List.not_mem_nil
  | x :: xs, ys, h, y, hy => by
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => simp only [hx] at h; cases h
      | some b =>
          cases hxs : xs.mapM f with
          | none => simp only [hx, hxs] at h; cases h
          | some bs =>
              simp only [hx, hxs] at h
              cases h
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨x, List.mem_cons_self, hx⟩
              · obtain ⟨z, hz, hzy⟩ := mapM_mem f xs bs hxs y hy
                exact ⟨z, List.mem_cons_of_mem _ hz, hzy⟩

/-- An option traversal returns the pointwise results when every step succeeds with them. -/
theorem mapM_eq_some_map {α β : Type} (f : α → Option β) (g : α → β) (xs : List α)
    (total : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, total x List.mem_cons_self,
        ih (fun z hz ↦ total z (List.mem_cons_of_mem _ hz)), List.map_cons]
      rfl

/-- Pruned hints of node values that pair up at every active node reconstruct all remaining
levels: one root value, and every path extended by the values of its siblings. -/
theorem expandLevels_eq (height : ℕ) (value : ℕ → ℕ → Digest) (Active : ℕ → ℕ → Prop)
    (closed : ∀ m i, Active m i → Active (m + 1) (i / 2))
    (parent : ∀ m i, m < height → Active m i →
      MixedMerkleTree.pairUp (pairWith hash) i (value m i) (value m (i ^^^ 1)) = value (m + 1) (i / 2))
    (remaining level : ℕ) (active : List ℕ) (paths : List Path)
    (depth : level + remaining = height) (nonempty : active ≠ [])
    (range : ∀ i ∈ active, i < 2 ^ remaining) (activeAll : ∀ i ∈ active, Active level i)
    (frontier : Frontier hash height level (active.map fun i ↦ (i, value level i)) paths) :
    ∃ finalNodes,
      expandLevels hash remaining level (active.map fun i ↦ (i, value level i)) paths
          (pruneLevels height value remaining active) =
        some (finalNodes, paths.map (fun p ↦ { p with
          siblings := p.siblings ++ (List.range' level remaining).map
            (fun m ↦ value m ((p.index >>> m) ^^^ 1)) }), []) ∧
        finalNodes ≠ [] ∧ ∀ e ∈ finalNodes, e.2 = value height 0 := by
  induction remaining generalizing level active paths with
  | zero =>
      refine ⟨active.map fun i ↦ (i, value level i), ?_, ?_, ?_⟩
      · simp only [expandLevels, pruneLevels, List.range'_zero, List.map_nil, List.append_nil]
        exact congrArg (fun paths ↦ some (_, paths, [])) (List.map_id'' (fun _ ↦ rfl) paths).symm
      · exact fun empty ↦ nonempty (List.map_eq_nil_iff.mp empty)
      · intro e he
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
        have index : i = 0 := by have := range i hi; simp only [Nat.pow_zero] at this; omega
        subst i
        have : level = height := by omega
        subst level
        rfl
  | succ remaining ih =>
      have sorted : active.Pairwise (· < ·) := by
        simpa only [Frontier, List.pairwise_map] using frontier.1
      let parents := (active.map (· / 2)).eraseDups
      have expanded := expandLevel_eq hash (value level) (value (level + 1)) _ active
        (pruneLevels height value remaining parents) sorted (Nat.le_refl _)
        (fun i hi ↦ parent level i (by omega) (activeAll i hi))
      have sound := expandLevel_sound hash _ _ _ _ _ _ frontier.1 expanded
      have siblingsSorted : (active.map fun i ↦ (i, value level (i ^^^ 1))).Pairwise
          (fun a b ↦ a.1 < b.1) := by
        simpa only [List.pairwise_map] using sorted
      let extend := fun p : Path ↦ { p with siblings := p.siblings ++ [value level ((p.index >>> level) ^^^ 1)] }
      have mapped : paths.mapM (fun p ↦ do
          let sibling ← (active.map fun i ↦ (i, value level (i ^^^ 1))).lookup (p.index >>> level)
          pure { p with siblings := p.siblings ++ [sibling] }) = some (paths.map extend) := by
        apply mapM_eq_some_map
        intro p hp
        have member : p.index >>> level ∈ active := by
          obtain ⟨j, hj, eq⟩ := List.mem_map.mp (lookup_mem (frontier.2 p hp).2.2)
          exact (Prod.mk.inj eq).1 ▸ hj
        rw [lookup_of_mem siblingsSorted (e := (p.index >>> level, value level ((p.index >>> level) ^^^ 1)))
          (List.mem_map.mpr ⟨_, member, rfl⟩)]
        rfl
      have next := advance_frontier hash height level _ _ _ paths (paths.map extend) frontier sound mapped
      have parentNonempty : parents ≠ [] := by
        intro empty
        obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ nonempty
        have mem : i / 2 ∈ parents := List.mem_eraseDups.mpr (List.mem_map.mpr ⟨i, hi, rfl⟩)
        rw [empty] at mem
        exact List.not_mem_nil mem
      have parentRange : ∀ i ∈ parents, i < 2 ^ remaining := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hi)
        have bound := range j hj
        rw [Nat.pow_succ] at bound
        omega
      have parentActive : ∀ i ∈ parents, Active (level + 1) i := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hi)
        exact closed level j (activeAll j hj)
      obtain ⟨finalNodes, recursive, ne, values⟩ := ih (level + 1) parents (paths.map extend)
        (by omega) parentNonempty parentRange parentActive next.1
      refine ⟨finalNodes, ?_, ne, values⟩
      have lev : height - (remaining + 1) = level := by omega
      rw [expandLevels, pruneLevels, lev]
      change Option.bind (expandLevel hash _ _ _) _ = _
      simp only [List.length_map]
      rw [expanded]
      change Option.bind (paths.mapM (m := Option) _) _ = _
      rw [mapped]
      refine recursive.trans ?_
      simp only [List.map_map, Function.comp_def, extend, List.append_assoc,
        List.range'_succ, List.map_cons, List.singleton_append]

end Generic

/-- A nonempty in-range honest query batch expands to its honest root, every path carrying its
honest leaf. -/
theorem honest_expand (height rowWords leafWords : ℕ) (rows : ℕ → List K)
    (width : rowWords ≤ leafWords) (shape : ∀ i < 2 ^ height, (rows i).length = rowWords)
    (queries : List ℕ) (nonempty : queries ≠ []) (range : ∀ i ∈ queries, i < 2 ^ height) :
    ∃ paths, expand Keccak.Commit.hash height rowWords leafWords queries
      (honestBatch height leafWords rows queries) =
        some (root height (fun i ↦ restoreLeaf leafWords (rows i)), paths) ∧
      ∀ p ∈ paths, p.leaf = restoreLeaf leafWords (rows p.index) := by
  let leaves := fun i ↦ restoreLeaf leafWords (rows i)
  let initial := (positions queries).map fun i ↦ Path.mk i (leaves i) []
  have positionsMem : ∀ i, i ∈ positions queries ↔ i ∈ queries := by
    intro i
    simp only [positions, List.mem_eraseDups, List.mem_mergeSort]
  have activeNonempty : positions queries ≠ [] := by
    intro empty
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ nonempty
    have mem := (positionsMem i).mpr hi
    rw [empty] at mem
    exact List.not_mem_nil mem
  have activeRange : ∀ i ∈ positions queries, i < 2 ^ height :=
    fun i hi ↦ range i ((positionsMem i).mp hi)
  have initialNodes : (initial.map fun p ↦ (p.index, leafWith Keccak.Commit.hash p.leaf)) =
      ((positions queries).map fun i ↦ (i, node leaves 0 i)) := by
    simp only [initial, List.map_map, Function.comp_def, node]
    rfl
  have initialIndices : initial.map Path.index = positions queries := by
    simp only [initial, List.map_map, Function.comp_def, List.map_id']
  have sortedNodes : ((positions queries).map fun i ↦ (i, node leaves 0 i)).Pairwise
      (fun a b ↦ a.1 < b.1) := by
    simpa only [List.pairwise_map] using positions_sorted queries
  have initialFrontier : Frontier Keccak.Commit.hash height 0
      ((positions queries).map fun i ↦ (i, node leaves 0 i)) initial := by
    refine ⟨sortedNodes, ?_⟩
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    refine ⟨rfl, activeRange i hi, ?_⟩
    exact lookup_of_mem sortedNodes (List.mem_map.mpr ⟨i, hi, rfl⟩)
  obtain ⟨finalNodes, reconstructed, finalNonempty, values⟩ :=
    expandLevels_eq Keccak.Commit.hash height (node leaves) (fun _ _ ↦ True) (fun _ _ _ ↦ trivial)
      (fun m i _ _ ↦ pairUp_node leaves m i) height 0 (positions queries) initial (Nat.zero_add _)
      activeNonempty activeRange (fun _ _ ↦ trivial) initialFrontier
  let finalPaths := initial.map fun p ↦ { p with
    siblings := p.siblings ++ (List.range' 0 height).map
      (fun m ↦ node leaves m ((p.index >>> m) ^^^ 1)) }
  have indices : finalPaths.map Path.index = initial.map Path.index := by
    simp only [finalPaths, List.map_map, Function.comp_def]
  have total : ∀ i ∈ queries, ∃ p, finalPaths.find? (fun p ↦ p.index == i) = some p := by
    intro i hi
    have member : i ∈ finalPaths.map Path.index := by
      rw [indices, initialIndices]
      exact (positionsMem i).mpr hi
    obtain ⟨p, hp, eq⟩ := List.mem_map.mp member
    cases found : finalPaths.find? (fun p ↦ p.index == i) with
    | some p => exact ⟨p, rfl⟩
    | none =>
        have no := List.find?_eq_none.mp found p hp
        exact False.elim (no (by simpa only [beq_iff_eq] using eq))
  obtain ⟨ordered, mapped⟩ := mapM_exists _ queries total
  have zip : (positions queries).zip ((positions queries).map rows) =
      (positions queries).map (fun i ↦ (i, rows i)) := by
    simpa only [List.map_id, id_eq] using (List.zip_map' (f := id) (g := rows) (l := positions queries))
  have firstPaths : ((positions queries).zip ((positions queries).map rows)).map
      (fun (i, row) ↦ Path.mk i (restoreLeaf leafWords row) []) = initial := by
    rw [zip, List.map_map]
    rfl
  have guard : ((positions queries).isEmpty || !((positions queries).all (· < 2 ^ height)) ||
      (positions queries).length != ((positions queries).map rows).length ||
      decide (rowWords > leafWords) ||
      !(((positions queries).map rows).all fun row ↦ row.length == rowWords)) = false := by
    simp only [Bool.or_eq_false_iff, List.isEmpty_eq_false_iff, Bool.not_eq_false',
      List.all_eq_true, decide_eq_true_eq, List.length_map, bne_self_eq_false,
      decide_eq_false_iff_not, List.mem_map, beq_iff_eq]
    refine ⟨⟨⟨⟨activeNonempty, activeRange⟩, True.intro⟩, by omega⟩, ?_⟩
    intro row mem
    obtain ⟨i, hi, rfl⟩ := mem
    exact shape i (activeRange i hi)
  cases finalNodes with
  | nil => exact False.elim (finalNonempty rfl)
  | cons top rest =>
      have value := values top List.mem_cons_self
      have ex : expand Keccak.Commit.hash height rowWords leafWords queries
          (honestBatch height leafWords rows queries) = some (root height leaves, ordered) := by
        unfold expand
        dsimp only [honestBatch]
        simp only [guard, Bool.false_eq_true, ↓reduceIte, firstPaths, initialNodes]
        change Option.bind (expandLevels Keccak.Commit.hash height 0 _ initial _) _ = _
        rw [reconstructed]
        change Option.bind (queries.mapM (fun i ↦ finalPaths.find? (fun p ↦ p.index == i))) _ = _
        rw [mapped]
        exact congrArg (fun d ↦ some (d, ordered)) value
      refine ⟨ordered, ex, ?_⟩
      intro p hp
      obtain ⟨i, _, found⟩ := mapM_mem _ queries ordered mapped p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
      rfl

/-- Every nonempty in-range honest query batch verifies against its honest root. -/
theorem honest_accepts (height rowWords leafWords : ℕ) (rows : ℕ → List K)
    (width : rowWords ≤ leafWords) (shape : ∀ i < 2 ^ height, (rows i).length = rowWords)
    (queries : List ℕ) (nonempty : queries ≠ []) (range : ∀ i ∈ queries, i < 2 ^ height) :
    accepts Keccak.Commit.hash height rowWords leafWords queries (honestBatch height leafWords rows queries)
      (root height (fun i ↦ restoreLeaf leafWords (rows i))) = true := by
  obtain ⟨paths, ex, _⟩ := honest_expand height rowWords leafWords rows width shape queries nonempty range
  simp only [accepts, ex, beq_self_eq_true]



/-- The fixed Keccak primitive includes leaf byte preimages and ordered digest-pair preimages. -/
abbrev Op := MixedMerkleTree.Knowledge.Op (List K) Digest

/-- Keccak's combined leaf/node operation used by the node-knowledge games. -/
def answer : Op → Digest := MixedMerkleTree.Knowledge.answer hashLeaf compress

/-- The combined leaf/node operation under a raw-byte hash. -/
abbrev answerWith (hash : ByteArray → Digest) : Op → Digest :=
  MixedMerkleTree.Knowledge.answer (leafWith hash) (pairWith hash)

/-- The Keccak node operation is the generic operation at Keccak-256. -/
theorem answerWith_hash : answerWith hash = answer := rfl


section Generic
variable (hash : ByteArray → Digest)

/-- Wire adversary output for one fixed public tree/row shape. -/
abbrev Adversary (Coins : Type) := Coins → Digest × List ℕ × Pruned

/-- Expand wire proofs for the same-coins VCVio extractor; malformed batches reveal no openings. -/
def mixedAdversary {Coins : Type} (height rowWords leafWords : ℕ) (A : Adversary Coins) :
    MerkleAdversary Coins (List K) Digest := fun c ↦
  let (commitment, queries, batch) := A c
  ([commitment], match expand hash height rowWords leafWords queries batch with
    | none => []
    | some (_, paths) => paths.map Path.toMixed)

/-- The total natural-index view of the VCVio leaf mask hides out-of-range columns. -/
def maskedLeaves {Coins : Type} (height rowWords leafWords : ℕ) (A : Adversary Coins)
    (X : ExtractorMap Coins (List K) Digest) (c : Coins) (i : ℕ) : Option (List K) :=
  if bound : i < 2 ^ height then
    extractedMask (leafWith hash) (pairWith hash) [] height 0 (fun _ => false)
      (mixedAdversary hash height rowWords leafWords A) X c ⟨i, bound⟩
  else none

/-- Every expanded opening in an accepted wire batch verifies against its transmitted root. -/
theorem accepted_mixed_verifies {Coins : Type} (height rowWords leafWords : ℕ)
    (A : Adversary Coins) (c : Coins)
    (accepted : accepts hash height rowWords leafWords (A c).2.1 (A c).2.2 (A c).1 = true) :
    ∀ o ∈ (mixedAdversary hash height rowWords leafWords A c).2,
      o.Verifies (leafWith hash) (pairWith hash) height 0 (fun _ => false)
        (mixedAdversary hash height rowWords leafWords A c).1 := by
  rcases output : A c with ⟨commitment, queries, batch⟩
  cases expanded : expand hash height rowWords leafWords queries batch with
  | none => simp [accepts, output, expanded] at accepted
  | some pair =>
      obtain ⟨digest, paths⟩ := pair
      have same : digest = commitment := by
        simpa only [accepts, output, expanded, beq_iff_eq] using accepted
      subst digest
      intro opening member
      have member : opening ∈ paths.map Path.toMixed := by
        simpa only [mixedAdversary, output, expanded] using member
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
      simpa only [mixedAdversary, output] using (accepted_openings_verify hash height rowWords leafWords queries batch commitment paths
        expanded).2 p hp

/-- An accepted wire batch disagrees when a supplied leaf is hidden or has a different revealed payload. -/
def Disagree {Coins : Type} (height rowWords leafWords : ℕ) (A : Adversary Coins)
    (X : ExtractorMap Coins (List K) Digest) (c : Coins) : Prop :=
  accepts hash height rowWords leafWords (A c).2.1 (A c).2.2 (A c).1 = true ∧
    ∃ o ∈ (mixedAdversary hash height rowWords leafWords A c).2,
      maskedLeaves hash height rowWords leafWords A X c o.index ≠ some o.payload

/-- Wire disagreement exposes a same-coins node failure at a concrete Merkle position. -/
theorem disagreement_implies_nodeBad {Coins : Type}
    (height rowWords leafWords : ℕ) (A : Adversary Coins)
    (X : ExtractorMap Coins (List K) Digest) (c : Coins)
    (disagree : Disagree hash height rowWords leafWords A X c) :
    ∃ v ∈ MixedMerkleTree.Knowledge.positions height 0 (fun _ ↦ false),
      NodeBad (answerWith hash)
        (derivedAdversary (leafWith hash) (pairWith hash) [] height 0 (fun _ ↦ false)
          (mixedAdversary hash height rowWords leafWords A) X v)
        (X v (derivedAdversary (leafWith hash) (pairWith hash) [] height 0 (fun _ ↦ false)
          (mixedAdversary hash height rowWords leafWords A) X v)) c := by
  obtain ⟨accepted, o, member, mismatch⟩ := disagree
  have verified := accepted_mixed_verifies hash height rowWords leafWords A c accepted o member
  have index := verified.2.2.1
  simp only [maskedLeaves, dite_eq_left index] at mismatch
  exact opening_mask_disagree_implies_nodeBad (leafWith hash) (pairWith hash) [] height 0
    (fun _ => false) (mixedAdversary hash height rowWords leafWords A) X c o member verified mismatch

/-- One Merkle game uses the adversary once and adds extraction across its positions. -/
theorem disagreement_bound_union {Coins : Type} [SampleableType Coins]
    (height rowWords leafWords : ℕ) (A : Adversary Coins)
    (X : ExtractorMap Coins (List K) Digest) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Disagree hash height rowWords leafWords A X c] ≤
      Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
        ∃ v ∈ MixedMerkleTree.Knowledge.positions height 0 (fun _ ↦ false),
          NodeBad (answerWith hash)
            (derivedAdversary (leafWith hash) (pairWith hash) [] height 0 (fun _ ↦ false)
              (mixedAdversary hash height rowWords leafWords A) X v)
            (X v (derivedAdversary (leafWith hash) (pairWith hash) [] height 0 (fun _ ↦ false)
              (mixedAdversary hash height rowWords leafWords A) X v)) c] := by
  exact prEvent_mono _ _ _ (disagreement_implies_nodeBad hash height rowWords leafWords A X)

/-- Keccak-specialized disagreement bound, conditional on the same-coins node extractor assignment.
No collision-resistance or concrete-Keccak knowledge assumption is silently discharged. -/
theorem disagreement_bound {Coins : Type} [SampleableType Coins]
    (height rowWords leafWords : ℕ) (A : Adversary Coins)
    (X : ExtractorMap Coins (List K) Digest) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Disagree hash height rowWords leafWords A X c] ≤
      ∑ v ∈ MixedMerkleTree.Knowledge.positions height 0 (fun _ ↦ false),
        nodeFail (answerWith hash)
          (derivedAdversary (leafWith hash) (pairWith hash) [] height 0 (fun _ ↦ false)
            (mixedAdversary hash height rowWords leafWords A) X v)
          (X v (derivedAdversary (leafWith hash) (pairWith hash) [] height 0 (fun _ ↦ false)
            (mixedAdversary hash height rowWords leafWords A) X v)) := by
  exact (disagreement_bound_union hash height rowWords leafWords A X).trans
    (prEvent_exists_finset_le _ ($ᵗ Coins : ProbComp Coins) _)


end Generic

end
end CompStark.Keccak.Commit
