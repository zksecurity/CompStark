/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.FullWidth
public import CompStark.Keccak.Commit.Masked

/-! Full openings authenticated separately under one root. Without a Keccak collision among their
hash inputs they agree on every shared node, and they are exactly the expansion of their pruned
batch. -/

set_option autoImplicit false
@[expose] public section
namespace CompStark.Keccak.Commit
open CompStark.BinaryFields

/-- The digest a path reaches after its first `level` siblings. -/
def Path.ancestor (p : Path) (level : ℕ) : Digest :=
  MixedMerkleTree.climb hashLeaf compress (fun _ ↦ none) p.index (hashLeaf p.leaf) (p.siblings.take level)

/-- The bytes hashed into the ancestor above `level`: the ancestor and its sibling, in tree order. -/
def Path.input (p : Path) (level : ℕ) : ByteArray :=
  let sibling := p.siblings.getD level (Vector.replicate 32 0)
  if (p.index >>> level) % 2 = 0 then ⟨(p.ancestor level).toArray ++ sibling.toArray⟩
  else ⟨sibling.toArray ++ (p.ancestor level).toArray⟩

/-- Every byte string a path hashes, from its leaf to the root. -/
def Path.inputs (p : Path) : List ByteArray :=
  leafBytes p.leaf :: (List.range p.siblings.length).map p.input

/-- The first Keccak collision among the inputs hashed along the paths. -/
def pathCollision (paths : List Path) : ByteArray × ByteArray :=
  let inputs := paths.flatMap Path.inputs
  findCollision (inputs.flatMap fun a ↦ inputs.map fun b ↦ (a, b))

/-- A path accepted at a height: in range, of that depth, and reaching the root. -/
def Path.Accepted (p : Path) (height : ℕ) (root : Digest) : Prop :=
  p.index < 2 ^ height ∧ p.siblings.length = height ∧ p.digest hash = root

/-- The leaf is the ancestor at level zero. -/
theorem Path.ancestor_zero (p : Path) : p.ancestor 0 = hashLeaf p.leaf := by
  simp only [Path.ancestor, List.take_zero, MixedMerkleTree.climb_nil]

/-- The full climb is the path's digest. -/
theorem Path.ancestor_length (p : Path) : p.ancestor p.siblings.length = p.digest hash := by
  simp only [Path.ancestor, List.take_length, Path.digest, leafWith_hash, pairWith_hash,
    leafWith_hash_apply]

/-- Each ancestor is the hash of the input formed one level below. -/
theorem Path.ancestor_succ (p : Path) (level : ℕ) (bound : level < p.siblings.length) :
    p.ancestor (level + 1) = hash (p.input level) := by
  have take : p.siblings.take (level + 1) = p.siblings.take level ++ [p.siblings[level]] :=
    List.take_succ_eq_append_getElem bound
  have length : (p.siblings.take level).length = level := List.length_take_of_le bound.le
  have sibling : p.siblings.getD level (Vector.replicate 32 0) = p.siblings[level] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]
  rw [Path.ancestor, take]
  simp only [MixedMerkleTree.climb_append, MixedMerkleTree.climb_cons, MixedMerkleTree.inject,
    MixedMerkleTree.climb_nil, length, Path.input, sibling, MixedMerkleTree.pairUp]
  split <;> rfl

/-- The ancestor above a level is the parent of the ancestor and sibling at that level. -/
theorem Path.ancestor_pairUp (p : Path) (level : ℕ) (bound : level < p.siblings.length) :
    MixedMerkleTree.pairUp compress (p.index >>> level) (p.ancestor level) p.siblings[level] =
      p.ancestor (level + 1) := by
  rw [p.ancestor_succ level bound]
  have sibling : p.siblings.getD level (Vector.replicate 32 0) = p.siblings[level] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]
  simp only [Path.input, sibling, MixedMerkleTree.pairUp]
  split <;> rfl

/-- Two accepted paths whose inputs collide nowhere hash equal inputs at a common ancestor. -/
theorem Path.input_eq {p q : Path} {height : ℕ} {root : Digest}
    (hp : p.Accepted height root) (hq : q.Accepted height root)
    (injective : ∀ a ∈ p.inputs, ∀ b ∈ q.inputs, hash a = hash b → a = b) :
    ∀ level < height, p.index >>> (level + 1) = q.index >>> (level + 1) →
      p.ancestor (level + 1) = q.ancestor (level + 1) → p.input level = q.input level := by
  intro level bound _ same
  rw [p.ancestor_succ level (hp.2.1 ▸ bound), q.ancestor_succ level (hq.2.1 ▸ bound)] at same
  apply injective _ _ _ _ same
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨level, List.mem_range.mpr (hp.2.1 ▸ bound), rfl⟩)
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨level, List.mem_range.mpr (hq.2.1 ▸ bound), rfl⟩)

/-- Equal inputs at a level split into equal ancestors and siblings, in tree order. -/
theorem Path.input_parts {p q : Path} {level : ℕ} (same : p.input level = q.input level)
    (pb : level < p.siblings.length) (qb : level < q.siblings.length) :
    (p.index >>> level = q.index >>> level →
      p.ancestor level = q.ancestor level ∧ p.siblings[level] = q.siblings[level]) ∧
    (p.index >>> level = (q.index >>> level) ^^^ 1 →
      p.ancestor level = q.siblings[level] ∧ p.siblings[level] = q.ancestor level) := by
  have ps : p.siblings.getD level (Vector.replicate 32 0) = p.siblings[level] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem pb, Option.getD_some]
  have qs : q.siblings.getD level (Vector.replicate 32 0) = q.siblings[level] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem qb, Option.getD_some]
  simp only [Path.input, ps, qs] at same
  have pair := fun (a b c d : Digest) (h : (⟨a.toArray ++ b.toArray⟩ : ByteArray) = ⟨c.toArray ++ d.toArray⟩) =>
    Prod.ext_iff.mp (pairBytes_injective (a₁ := (a, b)) (a₂ := (c, d)) h)
  constructor
  · intro index
    rw [index] at same
    split at same
    · exact pair _ _ _ _ same
    · obtain ⟨left, right⟩ := pair _ _ _ _ same
      exact ⟨right, left⟩
  · intro index
    have flip : (p.index >>> level) % 2 = 1 - (q.index >>> level) % 2 := by
      rw [index, MixedMerkleTree.xor_one_eq]
      omega
    split at same <;> split at same
    · omega
    · obtain ⟨left, right⟩ := pair _ _ _ _ same
      exact ⟨left, right⟩
    · obtain ⟨left, right⟩ := pair _ _ _ _ same
      exact ⟨right, left⟩
    · omega

/-- Two accepted paths without colliding inputs agree on every common ancestor. -/
theorem Path.ancestor_eq {p q : Path} {height : ℕ} {root : Digest}
    (hp : p.Accepted height root) (hq : q.Accepted height root)
    (injective : ∀ a ∈ p.inputs, ∀ b ∈ q.inputs, hash a = hash b → a = b) :
    ∀ level ≤ height, p.index >>> level = q.index >>> level → p.ancestor level = q.ancestor level := by
  suffices descend : ∀ n level, level + n = height →
      p.index >>> level = q.index >>> level → p.ancestor level = q.ancestor level by
    intro level bound
    exact descend (height - level) level (by omega)
  intro n
  induction n with
  | zero =>
    intro level top _
    rw [Nat.add_zero] at top
    subst top
    rw [← hp.2.1, p.ancestor_length, hp.2.2, ← hq.2.2, ← q.ancestor_length, hq.2.1, hp.2.1]
  | succ n ih =>
    intro level depth index
    have up : p.index >>> (level + 1) = q.index >>> (level + 1) := by
      rw [Nat.shiftRight_succ, Nat.shiftRight_succ, index]
    have input := Path.input_eq hp hq injective level (by omega) up (ih (level + 1) (by omega) up)
    exact ((Path.input_parts input (by rw [hp.2.1]; omega) (by rw [hq.2.1]; omega)).1 index).1

/-- Two accepted paths without colliding inputs agree on the sibling of every common node, and
read each other's nodes as siblings. -/
theorem Path.sibling_eq {p q : Path} {height : ℕ} {root : Digest}
    (hp : p.Accepted height root) (hq : q.Accepted height root)
    (injective : ∀ a ∈ p.inputs, ∀ b ∈ q.inputs, hash a = hash b → a = b)
    (level : ℕ) (bound : level < height) :
    (p.index >>> level = q.index >>> level →
      p.siblings[level]'(hp.2.1 ▸ bound) = q.siblings[level]'(hq.2.1 ▸ bound)) ∧
    (p.index >>> level = (q.index >>> level) ^^^ 1 →
      p.ancestor level = q.siblings[level]'(hq.2.1 ▸ bound)) := by
  have parts := fun (up : p.index >>> (level + 1) = q.index >>> (level + 1)) =>
    Path.input_parts (Path.input_eq hp hq injective level bound up
      (Path.ancestor_eq hp hq injective (level + 1) bound up))
      (hp.2.1 ▸ bound) (hq.2.1 ▸ bound)
  constructor
  · intro index
    exact ((parts (by rw [Nat.shiftRight_succ, Nat.shiftRight_succ, index])).1 index).2
  · intro index
    have up : p.index >>> (level + 1) = q.index >>> (level + 1) := by
      rw [Nat.shiftRight_succ, Nat.shiftRight_succ, index, (xor_one_facts _).2]
    exact ((parts up).2 index).1

/-- Two accepted paths at one position without colliding inputs open the same leaf. -/
theorem Path.leaf_eq {p q : Path} {height : ℕ} {root : Digest}
    (hp : p.Accepted height root) (hq : q.Accepted height root)
    (injective : ∀ a ∈ p.inputs, ∀ b ∈ q.inputs, hash a = hash b → a = b)
    (index : p.index = q.index) : p.leaf = q.leaf := by
  have same := Path.ancestor_eq hp hq injective 0 (Nat.zero_le _)
    (by simp only [Nat.shiftRight_zero, index])
  rw [p.ancestor_zero, q.ancestor_zero] at same
  exact leafBytes_injective (injective _ List.mem_cons_self _ List.mem_cons_self same)

/-- Without a collision among all paths' inputs, Keccak is injective on them. -/
theorem pathCollision_injective (paths : List Path)
    (absent : ¬ Collision hash (pathCollision paths).1 (pathCollision paths).2) :
    ∀ p ∈ paths, ∀ q ∈ paths, ∀ a ∈ p.inputs, ∀ b ∈ q.inputs, hash a = hash b → a = b := by
  intro p hp q hq a ha b hb same
  by_contra different
  apply absent
  refine (findCollision_iff _).mpr ⟨(a, b), ?_, different, same⟩
  exact List.mem_flatMap.mpr ⟨a, List.mem_flatMap.mpr ⟨p, hp, ha⟩,
    List.mem_map.mpr ⟨b, List.mem_flatMap.mpr ⟨q, hq, hb⟩, rfl⟩⟩

/-- The node value at a level and position, read from the first path through it or beside it. -/
def pathValue (paths : List Path) (level index : ℕ) : Digest :=
  match paths.find? (fun p ↦ p.index >>> level == index) with
  | some p => p.ancestor level
  | none => ((paths.find? fun p ↦ (p.index >>> level) ^^^ 1 == index).bind
      fun p ↦ p.siblings[level]?).getD (Vector.replicate 32 0)

/-- The first leaf opened at a position. -/
def pathLeaf (paths : List Path) (index : ℕ) : List K :=
  ((paths.find? fun p ↦ p.index == index).map Path.leaf).getD []

/-- One row per distinct position and the sibling digests the paths carry, in the order
`expand` consumes them. -/
def prune (height : ℕ) (paths : List Path) : Pruned :=
  let active := positions (paths.map Path.index)
  ⟨active.map (pathLeaf paths), pruneLevels height (pathValue paths) height active⟩

/-- Accepted paths of one batch without colliding inputs. -/
structure Consistent (paths : List Path) (height : ℕ) (root : Digest) : Prop where
  /-- Every path is accepted under the root. -/
  accepted : ∀ p ∈ paths, p.Accepted height root
  /-- Keccak is injective on all inputs the paths hash. -/
  injective : ∀ p ∈ paths, ∀ q ∈ paths, ∀ a ∈ p.inputs, ∀ b ∈ q.inputs, hash a = hash b → a = b

/-- A node on a path has that path's ancestor as its value. -/
theorem Consistent.value_through {paths : List Path} {height : ℕ} {root : Digest}
    (consistent : Consistent paths height root) {p : Path} (member : p ∈ paths)
    (level : ℕ) (bound : level ≤ height) :
    pathValue paths level (p.index >>> level) = p.ancestor level := by
  unfold pathValue
  cases found : paths.find? (fun r ↦ r.index >>> level == p.index >>> level) with
  | none =>
    have absent := List.find?_eq_none.mp found p member
    simp only [beq_self_eq_true, not_true_eq_false] at absent
  | some r =>
    have index : r.index >>> level = p.index >>> level := by
      simpa only [beq_iff_eq] using List.find?_some found
    have rm := List.mem_of_find?_eq_some found
    exact Path.ancestor_eq (consistent.accepted r rm) (consistent.accepted p member)
      (consistent.injective r rm p member) level bound index

/-- The sibling of a node on a path has that path's sibling as its value. -/
theorem Consistent.value_beside {paths : List Path} {height : ℕ} {root : Digest}
    (consistent : Consistent paths height root) {p : Path} (member : p ∈ paths)
    (level : ℕ) (bound : level < height) :
    pathValue paths level ((p.index >>> level) ^^^ 1) =
      p.siblings[level]'((consistent.accepted p member).2.1 ▸ bound) := by
  unfold pathValue
  cases found : paths.find? (fun r ↦ r.index >>> level == (p.index >>> level) ^^^ 1) with
  | some r =>
    have index : r.index >>> level = (p.index >>> level) ^^^ 1 := by
      simpa only [beq_iff_eq] using List.find?_some found
    have rm := List.mem_of_find?_eq_some found
    exact (Path.sibling_eq (consistent.accepted r rm) (consistent.accepted p member)
      (consistent.injective r rm p member) level bound).2 index
  | none =>
    cases beside : paths.find? (fun r ↦ (r.index >>> level) ^^^ 1 == (p.index >>> level) ^^^ 1) with
    | none =>
      have absent := List.find?_eq_none.mp beside p member
      simp only [beq_self_eq_true, not_true_eq_false] at absent
    | some r =>
      have flipped : (r.index >>> level) ^^^ 1 = (p.index >>> level) ^^^ 1 := by
        simpa only [beq_iff_eq] using List.find?_some beside
      have index : r.index >>> level = p.index >>> level := by
        have := congrArg (· ^^^ 1) flipped
        simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
      have rm := List.mem_of_find?_eq_some beside
      have rb : level < r.siblings.length := (consistent.accepted r rm).2.1 ▸ bound
      simp only [Option.bind_some, List.getElem?_eq_getElem rb, Option.getD_some]
      exact (Path.sibling_eq (consistent.accepted r rm) (consistent.accepted p member)
        (consistent.injective r rm p member) level bound).1 index

/-- A position opened by a path has that path's leaf as its first leaf. -/
theorem Consistent.leaf_at {paths : List Path} {height : ℕ} {root : Digest}
    (consistent : Consistent paths height root) {p : Path} (member : p ∈ paths) :
    pathLeaf paths p.index = p.leaf := by
  unfold pathLeaf
  cases found : paths.find? (fun r ↦ r.index == p.index) with
  | none =>
    have absent := List.find?_eq_none.mp found p member
    simp only [beq_self_eq_true, not_true_eq_false] at absent
  | some r =>
    have rm := List.mem_of_find?_eq_some found
    exact Path.leaf_eq (consistent.accepted r rm) (consistent.accepted p member)
      (consistent.injective r rm p member) (by simpa only [beq_iff_eq] using List.find?_some found)

/-- The first entry at a position of a list indexed by position is that entry. -/
theorem find?_index (positions : List ℕ) (mk : ℕ → Path) (index : ∀ i, (mk i).index = i)
    (q : ℕ) (member : q ∈ positions) : (positions.map mk).find? (fun p ↦ p.index == q) = some (mk q) := by
  induction positions with
  | nil => exact absurd member List.not_mem_nil
  | cons i rest ih =>
    by_cases same : i = q
    · subst i
      simp only [List.map_cons, List.find?_cons, index, beq_self_eq_true]
    · have tail := ih ((List.mem_cons.mp member).resolve_left (Ne.symm same))
      simp only [List.map_cons, List.find?_cons, index, beq_eq_false_iff_ne.mpr same, tail]

/-- Consistent full-width paths are exactly the expansion of their pruned batch. -/
theorem Consistent.expand_prune {paths : List Path} {height leafWords : ℕ} {root : Digest}
    (consistent : Consistent paths height root) (nonempty : paths ≠ [])
    (width : ∀ p ∈ paths, p.leaf.length = leafWords) :
    expand hash height leafWords leafWords (paths.map Path.index) (prune height paths) = some (root, paths) := by
  have positionsMem : ∀ i, i ∈ positions (paths.map Path.index) ↔ ∃ p ∈ paths, p.index = i := by
    intro i
    simp only [positions, List.mem_eraseDups, List.mem_mergeSort, List.mem_map]
  have sorted := positions_sorted (paths.map Path.index)
  unfold expand prune
  generalize positions (paths.map Path.index) = active at positionsMem sorted ⊢
  have activeNonempty : active ≠ [] := by
    intro empty
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ nonempty
    have mem := (positionsMem p.index).mpr ⟨p, hp, rfl⟩
    rw [empty] at mem
    exact List.not_mem_nil mem
  have activeRange : ∀ i ∈ active, i < 2 ^ height := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := (positionsMem i).mp hi
    exact (consistent.accepted p hp).1
  have leafWidth : ∀ i ∈ active, (pathLeaf paths i).length = leafWords := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := (positionsMem i).mp hi
    rw [consistent.leaf_at hp]
    exact width p hp
  have zip : active.zip (active.map (pathLeaf paths)) = active.map fun i ↦ (i, pathLeaf paths i) := by
    simpa only [List.map_id, id_eq] using (List.zip_map' (f := id) (g := pathLeaf paths) (l := active))
  let initial := active.map fun i ↦ Path.mk i (pathLeaf paths i) []
  have firstPaths : (active.zip (active.map (pathLeaf paths))).map
      (fun (i, row) ↦ Path.mk i (restoreLeaf leafWords row) []) = initial := by
    rw [zip, List.map_map]
    exact List.map_congr_left fun i hi ↦ by
      simp only [Function.comp_apply, restoreLeaf_full (leafWidth i hi)]
  have leafValue : ∀ i ∈ active, hashLeaf (pathLeaf paths i) = pathValue paths 0 i := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := (positionsMem i).mp hi
    have through := consistent.value_through hp 0 (Nat.zero_le _)
    rw [Nat.shiftRight_zero] at through
    rw [through, p.ancestor_zero, consistent.leaf_at hp]
  have initialNodes : (initial.map fun p ↦ (p.index, leafWith hash p.leaf)) =
      active.map fun i ↦ (i, pathValue paths 0 i) := by
    simp only [initial, List.map_map, Function.comp_def]
    exact List.map_congr_left fun i hi ↦ by rw [leafWith_hash_apply, leafValue i hi]
  have sortedNodes : (active.map fun i ↦ (i, pathValue paths 0 i)).Pairwise
      (fun a b ↦ a.1 < b.1) := by
    simpa only [List.pairwise_map] using sorted
  have initialFrontier : Frontier hash height 0 (active.map fun i ↦ (i, pathValue paths 0 i)) initial := by
    refine ⟨sortedNodes, ?_⟩
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    refine ⟨rfl, activeRange i hi, ?_⟩
    have lookup := lookup_of_mem sortedNodes (List.mem_map.mpr ⟨i, hi, rfl⟩)
    simpa only [Nat.shiftRight_zero, Path.digest, MixedMerkleTree.climb_nil, leafWith_hash_apply,
      leafValue i hi] using lookup
  have parent : ∀ m i, m < height → (∃ p ∈ paths, p.index >>> m = i) →
      MixedMerkleTree.pairUp (pairWith hash) i (pathValue paths m i) (pathValue paths m (i ^^^ 1)) =
        pathValue paths (m + 1) (i / 2) := by
    rintro m i bound ⟨p, hp, rfl⟩
    rw [pairWith_hash, consistent.value_through hp m bound.le, consistent.value_beside hp m bound,
      p.ancestor_pairUp m ((consistent.accepted p hp).2.1 ▸ bound), ← Nat.shiftRight_succ,
      consistent.value_through hp (m + 1) bound]
  obtain ⟨finalNodes, reconstructed, finalNonempty, values⟩ :=
    expandLevels_eq hash height (pathValue paths) (fun m i ↦ ∃ p ∈ paths, p.index >>> m = i)
      (fun m i ⟨p, hp, index⟩ ↦ ⟨p, hp, by rw [Nat.shiftRight_succ, index]⟩) parent
      height 0 active initial (Nat.zero_add _) activeNonempty activeRange
      (fun i hi ↦ by
        obtain ⟨p, hp, rfl⟩ := (positionsMem i).mp hi
        exact ⟨p, hp, Nat.shiftRight_zero⟩) initialFrontier
  have rootValue : pathValue paths height 0 = root := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨range, length, digest⟩ := consistent.accepted p hp
    have top : p.index >>> height = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt range]
    rw [← top, consistent.value_through hp height le_rfl, ← length, p.ancestor_length, digest]
  let extend := fun p : Path ↦ { p with
    siblings := p.siblings ++ (List.range' 0 height).map
      (fun m ↦ pathValue paths m ((p.index >>> m) ^^^ 1)) }
  have extended : ∀ p ∈ paths, extend (Path.mk p.index (pathLeaf paths p.index) []) = p := by
    intro p hp
    obtain ⟨range, length, _⟩ := consistent.accepted p hp
    have leaf := consistent.leaf_at hp
    have beside := fun m (bound : m < height) ↦ consistent.value_beside hp m bound
    cases p with
    | mk index leaf siblings =>
      simp only [extend, List.nil_append, Path.mk.injEq, true_and]
      refine ⟨leaf, ?_⟩
      apply List.ext_getElem
      · simp only [List.length_map, List.length_range', length]
      · intro m left _
        simp only [List.length_map, List.length_range'] at left
        simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
        exact beside m left
  have ordered : (paths.map Path.index).mapM
      (fun q ↦ (initial.map extend).find? (fun p ↦ p.index == q)) = some paths := by
    have found : ∀ q ∈ paths.map Path.index, (initial.map extend).find? (fun p ↦ p.index == q) =
        some (extend (Path.mk q (pathLeaf paths q) [])) := by
      intro q hq
      rw [List.map_map]
      exact find?_index active (extend ∘ fun i ↦ Path.mk i (pathLeaf paths i) []) (fun _ ↦ rfl) q
        ((positionsMem q).mpr (List.mem_map.mp hq))
    rw [mapM_eq_some_map _ _ _ found]
    simp only [List.map_map, Function.comp_def]
    exact congrArg some ((List.map_congr_left fun p hp ↦ extended p hp).trans (List.map_id' _))
  have guard : (active.isEmpty || !(active.all (· < 2 ^ height)) ||
      active.length != (active.map (pathLeaf paths)).length ||
      decide (leafWords > leafWords) ||
      !((active.map (pathLeaf paths)).all fun row ↦ row.length == leafWords)) = false := by
    simp only [Bool.or_eq_false_iff, List.isEmpty_eq_false_iff, Bool.not_eq_false',
      List.all_eq_true, decide_eq_true_eq, List.length_map, bne_self_eq_false,
      decide_eq_false_iff_not, List.mem_map, beq_iff_eq]
    refine ⟨⟨⟨⟨activeNonempty, activeRange⟩, trivial⟩, Nat.lt_irrefl _⟩, ?_⟩
    rintro row ⟨i, hi, rfl⟩
    exact leafWidth i hi
  cases finalNodes with
  | nil => exact absurd rfl finalNonempty
  | cons top rest =>
    simp only [guard, Bool.false_eq_true, ↓reduceIte, firstPaths, initialNodes]
    change Option.bind (expandLevels hash height 0 _ initial _) _ = _
    rw [reconstructed]
    change Option.bind ((paths.map Path.index).mapM
      (fun q ↦ (initial.map extend).find? (fun p ↦ p.index == q))) _ = _
    rw [ordered, values top List.mem_cons_self, rootValue]
    rfl

end CompStark.Keccak.Commit
