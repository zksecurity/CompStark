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
