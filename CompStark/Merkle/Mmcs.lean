/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.Tree

/-! # Merkle openings

Plonky3's `MerkleTreeMmcs::open_batch` and `verify_batch` over the trees of `Tree`:

* An opening at `index` gives, for every matrix in its committed order, the row at `index` shifted
  right by the number of layers the matrix is shorter than the tallest, and the sibling digest of
  every layer below the root.
* Verification sorts the matrices tallest first, hashes the opened rows of the tallest ones,
  compresses with the siblings from the leaves up, and wherever a layer has the padded height of
  the next shorter matrices compresses in the hash of their rows. It accepts if this ends at the
  commitment.

`verifyBatchM` runs the verification with hashes in a monad; with pure hashes it is `verifyBatch`
(`verifyBatchM_pure`).

Plonky3's `open_multi_batch` and `verify_multi_batch` open several indices at once with one
pruned list of siblings (`verifyMultiM`, `prune`):

* The frontier starts at the distinct indices, each led by the first query opening it. Level by
  level, the frontier's nodes are grouped by parent; a parent with both children on the frontier
  takes no sibling, otherwise the absent child is the next sibling of the list. Rows of shorter
  matrices are injected as in a single opening, from the lead's rows.
* Verification first checks the shape: reachable heights, every row's width, indices below the
  height, rows that agree wherever two queries open the same row of a matrix, and the number of
  siblings the walk takes. It accepts if the walk ends at the commitment.
* `prune` collects the siblings a walk takes from the queries' full paths: each absent child is
  the sibling on its group's lead's path.
-/

@[expose] public section
namespace CompStark.Merkle

section Pure
variable {F : Type*} [Zero F] {d : Nat}

/-- `⌈log₂ n⌉`. -/
def log2Ceil (n : Nat) : Nat := Nat.log2 (n.nextPowerOfTwo)

/-- The opening at `index` of the matrices `ms` whose tree has the digest layers `ls`: their rows,
and the sibling path. -/
def openWith (ms : List (Matrix F)) (ls : List (List (Vector F d))) (index : Nat) :
    List (List F) × List (Vector F d) :=
  let maxH := (sortTallest ms |>.headD ⟨0, 0, #[]⟩).height
  let logMax := log2Ceil maxH
  let rows := ms.map fun m ↦ m.row (index >>> (logMax - log2Ceil m.height))
  (rows, (List.range logMax).map fun i ↦ (ls.getD i []).getD ((index >>> i) ^^^ 1) 0)

/-- The opening of the matrices `ms` at `index`: their rows, and the sibling path. -/
def openBatch (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (ms : List (Matrix F)) (index : Nat) : List (List F) × List (Vector F d) :=
  openWith ms (layers hash compress ms) index

/-- The hash of the concatenated opened rows of the matrices at `is`. -/
def hashRows (hash : List F → Vector F d) (values : List (List F)) (is : List Nat) :
    Vector F d :=
  hash (is.flatMap fun i ↦ values.getD i [])

/-- Compress `root` with the siblings from layer `layer` up, injecting the hashes of the groups of
shorter matrices at the layers of their padded heights. `groups` lists the remaining matrices'
indices by height, tallest first, with that height. -/
def climb (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (values : List (List F)) :
    List (Vector F d) → List (Nat × List Nat) → Nat → Nat → Vector F d → Vector F d
  | [], _, _, _, root => root
  | sib :: sibs, groups, index, padded, root =>
    let root := if index % 2 = 0 then compress root sib else compress sib root
    let padded := padded / 2
    match groups with
    | (h, is) :: rest =>
      if h.nextPowerOfTwo = padded then
        climb hash compress values sibs rest (index / 2) padded
          (compress root (hashRows hash values is))
      else climb hash compress values sibs groups (index / 2) padded root
    | [] => climb hash compress values sibs [] (index / 2) padded root

/-- The matrix indices grouped by height, tallest first, in their given order among equal
heights. -/
def heightGroups (heights : List Nat) : List (Nat × List Nat) :=
  let sorted := (List.range heights.length).mergeSort fun a b ↦
    heights.getD b 0 ≤ heights.getD a 0
  sorted.foldr (fun i gs ↦
    match gs with
    | (h, is) :: rest => if heights.getD i 0 = h then (h, i :: is) :: rest
        else (heights.getD i 0, [i]) :: gs
    | [] => [(heights.getD i 0, [i])]) []

/-- Plonky3's `verify_batch`: the opening `values, path` of matrices of the given heights at
`index` against `commit`. -/
def verifyBatch [DecidableEq F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (commit : Vector F d) (heights : List Nat)
    (index : Nat) (values : List (List F)) (path : List (Vector F d)) : Bool :=
  match heightGroups heights with
  | [] => false
  | (maxH, tallest) :: rest =>
    let padded := maxH.nextPowerOfTwo
    let compatible := (heightGroups heights).zip (heightGroups heights).tail |>.all
      fun ((a, _), (b, _)) ↦ a.nextPowerOfTwo != b.nextPowerOfTwo
    compatible && values.length == heights.length && path.length == Nat.log2 padded &&
      index < maxH &&
      climb hash compress values path rest index padded (hashRows hash values tallest) == commit

end Pure

/-! ### With the hashes in a monad

`verifyBatchM` is `verifyBatch` with the hash and compression returning in a monad, so that they
can be oracles. It checks the opening's shape before hashing anything. With pure hashes it is
`verifyBatch` (`verifyBatchM_pure`, `CompStark/Complete/Merkle.lean`). -/

section Monadic
variable {F : Type} [Zero F] {d : Nat} {m : Type → Type} [Monad m]

/-- `climb` with the hashes in `m`. -/
def climbM (hash : List F → m (Vector F d)) (compress : Vector F d → Vector F d → m (Vector F d))
    (values : List (List F)) :
    List (Vector F d) → List (Nat × List Nat) → Nat → Nat → Vector F d → m (Vector F d)
  | [], _, _, _, root => pure root
  | sib :: sibs, groups, index, padded, root => do
    let root ← if index % 2 = 0 then compress root sib else compress sib root
    let padded := padded / 2
    match groups with
    | (h, is) :: rest =>
      if h.nextPowerOfTwo = padded then
        let root ← compress root (← hash (is.flatMap fun i ↦ values.getD i []))
        climbM hash compress values sibs rest (index / 2) padded root
      else climbM hash compress values sibs groups (index / 2) padded root
    | [] => climbM hash compress values sibs [] (index / 2) padded root

/-- `verifyBatch` with the hashes in `m`. -/
def verifyBatchM [DecidableEq F] (hash : List F → m (Vector F d))
    (compress : Vector F d → Vector F d → m (Vector F d)) (commit : Vector F d)
    (heights : List Nat) (index : Nat) (values : List (List F)) (path : List (Vector F d)) :
    m Bool :=
  match heightGroups heights with
  | [] => pure false
  | (maxH, tallest) :: rest => do
    let padded := maxH.nextPowerOfTwo
    let compatible := (heightGroups heights).zip (heightGroups heights).tail |>.all
      fun ((a, _), (b, _)) ↦ a.nextPowerOfTwo != b.nextPowerOfTwo
    if compatible && values.length == heights.length && path.length == Nat.log2 padded &&
        index < maxH then
      let leaf ← hash (tallest.flatMap fun i ↦ values.getD i [])
      return (← climbM hash compress values path rest index padded leaf) == commit
    else return false

end Monadic

/-! ### Multi-openings -/

section Multi
variable {F : Type} [Zero F] {d : Nat} {m : Type → Type} [Monad m]

/-- The distinct indices, sorted, each with its lead: the first query opening it. -/
def frontier (indices : List Nat) : List (Nat × Nat) :=
  (indices.dedup.mergeSort (· ≤ ·)).map fun i ↦ (i, indices.idxOf i)

/-- One level of a walk: the frontier's nodes `(index, lead, digest)`, sorted by index, grouped
by parent; the parent of two nodes compresses them, the parent of one compresses it with the
next sibling of `sibs` on the other side. The parents and the siblings left. -/
def levelM (compress : Vector F d → Vector F d → m (Vector F d)) :
    List (Nat × Nat × Vector F d) → List (Vector F d) →
      m (List (Nat × Nat × Vector F d) × List (Vector F d))
  | [], sibs => pure ([], sibs)
  | [(i, q, x)], sibs => do
    let z ← if i % 2 = 0 then compress x (sibs.headD 0) else compress (sibs.headD 0) x
    return ([(i / 2, q, z)], sibs.tail)
  | (i, q, x) :: (j, q', y) :: rest, sibs => do
    if i % 2 = 0 ∧ j = i + 1 then
      let z ← compress x y
      let (ps, sibs) ← levelM compress rest sibs
      return ((i / 2, q, z) :: ps, sibs)
    else
      let z ← if i % 2 = 0 then compress x (sibs.headD 0) else compress (sibs.headD 0) x
      let (ps, sibs) ← levelM compress ((j, q', y) :: rest) sibs.tail
      return ((i / 2, q, z) :: ps, sibs)

/-- The walk from the frontier `nodes` over `levels` levels, the layer above the leaves of
padded height `padded`, injecting the groups of shorter matrices `groups` (heights, tallest
first, with their indices) from the leads' rows `rows`. -/
def walkM (hash : List F → m (Vector F d)) (compress : Vector F d → Vector F d → m (Vector F d))
    (rows : List (List (List F))) :
    Nat → List (Nat × List Nat) → Nat → List (Nat × Nat × Vector F d) → List (Vector F d) →
      m (List (Nat × Nat × Vector F d) × List (Vector F d))
  | 0, _, _, nodes, sibs => pure (nodes, sibs)
  | levels + 1, groups, padded, nodes, sibs => do
    let (ps, sibs) ← levelM compress nodes sibs
    let padded := padded / 2
    match groups with
    | (h, is) :: rest =>
      if h.nextPowerOfTwo = padded then
        let ps ← ps.mapM fun (i, q, z) ↦ do
          return (i, q, ← compress z (← hash (is.flatMap fun k ↦ (rows.getD q []).getD k [])))
        walkM hash compress rows levels rest padded ps sibs
      else walkM hash compress rows levels groups padded ps sibs
    | [] => walkM hash compress rows levels [] padded ps sibs

/-- One level of the frontier's indices, sorted: the parents, and the number of siblings taken. -/
def countLevel : List Nat → List Nat × Nat
  | [] => ([], 0)
  | [i] => ([i / 2], 1)
  | i :: j :: rest =>
    if i % 2 = 0 ∧ j = i + 1 then
      let (ps, c) := countLevel rest
      (i / 2 :: ps, c)
    else
      let (ps, c) := countLevel (j :: rest)
      (i / 2 :: ps, c + 1)

/-- The number of siblings a walk over `levels` levels from the frontier indices `nodes` takes. -/
def siblingCount : Nat → List Nat → Nat
  | 0, _ => 0
  | levels + 1, nodes => (countLevel nodes).2 + siblingCount levels (countLevel nodes).1

/-- The shape checks of a multi-opening of matrices of dimensions `dims` (height, width) at
`indices` with rows `rows` and siblings `sibs`, the tallest height `maxH` and `levels` levels. -/
def multiShapeOk [DecidableEq F] (dims : List (Nat × Nat)) (maxH levels : Nat)
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Vector F d)) : Bool :=
  let shift (h : Nat) := log2Ceil maxH - log2Ceil h
  (dims.all fun (h, _) ↦ h = (maxH - 1) >>> shift h + 1) && 0 < maxH &&
    rows.length == indices.length &&
    (rows.all fun r ↦
      r.length == dims.length && (r.zip dims).all fun (x, (_, w)) ↦ x.length == w) &&
    (indices.all (· < maxH)) &&
    ((indices.zip rows).all fun (i, r) ↦ (indices.zip rows).all fun (i', r') ↦
      ((dims.zip (r.zip r')).all fun ((h, _), (x, x')) ↦
        i >>> shift h != i' >>> shift h || x == x')) &&
    sibs.length == siblingCount levels ((frontier indices).map (·.1))

/-- Plonky3's `verify_multi_batch`: the multi-opening of matrices of dimensions `dims` (height,
width) at `indices`, with the queries' rows `rows` and the pruned siblings `sibs`, against
`commit`, with the hashes in `m`. -/
def verifyMultiM [DecidableEq F] (hash : List F → m (Vector F d))
    (compress : Vector F d → Vector F d → m (Vector F d)) (commit : Vector F d)
    (dims : List (Nat × Nat)) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Vector F d)) : m Bool :=
  match heightGroups (dims.map (·.1)) with
  | [] => pure false
  | (maxH, tallest) :: rest => do
    let padded := maxH.nextPowerOfTwo
    let levels := Nat.log2 padded
    if multiShapeOk dims maxH levels indices rows sibs then
      let leaves ← (frontier indices).mapM fun (i, q) ↦ do
        return (i, q, ← hash (tallest.flatMap fun k ↦ (rows.getD q []).getD k []))
      let (top, _) ← walkM hash compress rows levels rest padded leaves sibs
      return top.all fun (_, _, x) ↦ x == commit
    else return false

/-- One level of `prune` at `level`: the parents of the frontier `nodes`, each led by its first
child's lead, and the siblings taken, from the leads' paths `paths`. -/
def pruneLevel (paths : List (List (Vector F d))) (level : Nat) :
    List (Nat × Nat) → List (Nat × Nat) × List (Vector F d)
  | [] => ([], [])
  | [(i, q)] => ([(i / 2, q)], [(paths.getD q []).getD level 0])
  | (i, q) :: (j, q') :: rest =>
    if i % 2 = 0 ∧ j = i + 1 then
      let (ps, out) := pruneLevel paths level rest
      ((i / 2, q) :: ps, out)
    else
      let (ps, out) := pruneLevel paths level ((j, q') :: rest)
      ((i / 2, q) :: ps, (paths.getD q []).getD level 0 :: out)

/-- The siblings a walk over `levels` levels from the frontier `nodes` at `level` takes, read off
the queries' full paths `paths`. -/
def pruneWalk (paths : List (List (Vector F d))) :
    Nat → Nat → List (Nat × Nat) → List (Vector F d)
  | 0, _, _ => []
  | levels + 1, level, nodes =>
    let (parents, out) := pruneLevel paths level nodes
    out ++ pruneWalk paths levels (level + 1) parents

/-- The pruned siblings of the openings at `indices` with full paths `paths` (Plonky3's
`open_multi_batch`), over `levels` levels. -/
def prune (levels : Nat) (indices : List Nat) (paths : List (List (Vector F d))) :
    List (Vector F d) :=
  pruneWalk paths levels 0 (frontier indices)

end Multi

section PureHashes
variable {F : Type} {d : Nat} {m : Type → Type} [Monad m] [LawfulMonad m]

/-! ### Pure hashes -/

theorem climbM_pure (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
    (values : List (List F)) :
    ∀ path groups index padded root,
      climbM (m := m) (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values path groups
        index padded root = pure (climb hash compress values path groups index padded root)
  | [], _, _, _, _ => rfl
  | sib :: sibs, groups, index, padded, root => by
    simp only [climbM, climb]
    have step : ∀ root : Vector F d, (do
        let root ← (pure root : m (Vector F d))
        match groups with
        | (h, is) :: rest =>
          if h.nextPowerOfTwo = padded / 2 then do
            let leaf ← pure (hash (is.flatMap fun i ↦ values.getD i []))
            let root ← pure (compress root leaf)
            (climbM (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values sibs rest
              (index / 2) (padded / 2) root)
          else (climbM (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values sibs
            groups (index / 2) (padded / 2) root)
        | [] => (climbM (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) values sibs []
            (index / 2) (padded / 2) root)) =
        pure (match groups with
          | (h, is) :: rest =>
            if h.nextPowerOfTwo = padded / 2 then
              climb hash compress values sibs rest (index / 2) (padded / 2)
                (compress root (hashRows hash values is))
            else climb hash compress values sibs groups (index / 2) (padded / 2) root
          | [] => climb hash compress values sibs [] (index / 2) (padded / 2) root) := by
      intro root
      rw [pure_bind]
      rcases groups with _ | ⟨⟨h, is⟩, rest⟩
      · exact climbM_pure hash compress values sibs _ _ _ _
      · dsimp only
        by_cases hh : h.nextPowerOfTwo = padded / 2
        · simp only [hh, ite_true]
          rw [ pure_bind, pure_bind, hashRows]
          exact climbM_pure hash compress values sibs _ _ _ _
        · simp only [hh, ite_false]
          exact climbM_pure hash compress values sibs _ _ _ _
    by_cases hi : index % 2 = 0
    · simp only [hi, ite_true]; exact step _
    · simp only [hi, ite_false]; exact step _

/-- With pure hashes, `verifyBatchM` is `verifyBatch`. -/
theorem verifyBatchM_pure [DecidableEq F] (hash : List F → Vector F d)
    (compress : Vector F d → Vector F d → Vector F d) (commit : Vector F d) (heights : List Nat)
    (index : Nat) (values : List (List F)) (path : List (Vector F d)) :
    verifyBatchM (m := m) (fun xs ↦ pure (hash xs)) (fun a b ↦ pure (compress a b)) commit
      heights index values path =
      pure (verifyBatch hash compress commit heights index values path) := by
  unfold verifyBatchM verifyBatch
  rcases heightGroups heights with _ | ⟨⟨maxH, tallest⟩, rest⟩
  · rfl
  · dsimp only
    split
    · rename_i h
      rw [h, Bool.true_and, pure_bind, climbM_pure, pure_bind, hashRows]
    · rename_i h
      rw [Bool.not_eq_true] at h
      rw [h, Bool.false_and]

end PureHashes

end CompStark.Merkle
