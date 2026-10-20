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

namespace KoalaBear

variable (F : Type*) [Field F]

/-- The KoalaBear Poseidon2 opening of base-field matrices. -/
def openBatch (ms : List (Matrix F)) (index : Nat) : List (List F) × List (Vector F 8) :=
  Merkle.openBatch (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) ms index

/-- The KoalaBear Poseidon2 verification of a base-field opening. -/
def verifyBatch [DecidableEq F] (commit : Vector F 8) (heights : List Nat) (index : Nat)
    (values : List (List F)) (path : List (Vector F 8)) : Bool :=
  Merkle.verifyBatch (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F) commit heights index
    values path

end KoalaBear
end CompStark.Merkle
