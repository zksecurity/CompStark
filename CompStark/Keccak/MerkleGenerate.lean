/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Merkle

/-! # Generated, cache-resident Merkle subtrees -/

@[expose] public section
namespace CompStark.Keccak.Merkle
open BinaryTree InductiveMerkleTree

/-- The left half of a complete power-of-two row family. -/
def leftRows {depth : Nat} (row : Fin (2 ^ (depth + 1)) → Row) : Fin (2 ^ depth) → Row :=
  fun i => row ⟨i.val, by have := i.isLt; rw [pow_succ]; omega⟩

/-- The right half of a complete power-of-two row family. -/
def rightRows {depth : Nat} (row : Fin (2 ^ (depth + 1)) → Row) : Fin (2 ^ depth) → Row :=
  fun i => row ⟨2 ^ depth + i.val, by have := i.isLt; rw [pow_succ]; omega⟩

/-- Complete row families split into adjacent, equally sized halves. -/
theorem splitRows (depth : Nat) (row : Fin (2 ^ (depth + 1)) → Row) :
    List.ofFn row = List.ofFn (leftRows row) ++ List.ofFn (rightRows row) := by
  have count : 2 ^ (depth + 1) = 2 ^ depth + 2 ^ depth := by rw [pow_succ]; omega
  rw [List.ofFn_congr count, List.ofFn_add]
  rfl

/-- Generate each row at its leaf and climb the entire contiguous subtree in cache. -/
def Tree.generate : (depth : Nat) → (Fin (2 ^ depth) → Row) → Tree depth
  | 0, row => Tree.leaf (row 0)
  | depth + 1, row => Tree.join (Tree.generate depth (leftRows row))
      (Tree.generate depth (rightRows row))

/-- Completed subtrees are independent tasks above the 1024-row batch size. -/
def Tree.generateParallel : (depth : Nat) → (Fin (2 ^ depth) → Row) → Tree depth
  | 0, row => Tree.leaf (row 0)
  | depth + 1, row =>
    if depth < 10 then Tree.join (Tree.generate depth (leftRows row))
      (Tree.generate depth (rightRows row))
    else
      let left := Task.spawn fun _ => Tree.generateParallel depth (leftRows row)
      let right := Task.spawn fun _ => Tree.generateParallel depth (rightRows row)
      Tree.join left.get right.get

/-- Parallel subtree construction retains every payload and every cached digest. -/
@[csimp] theorem Tree.generate_code : Tree.generate = Tree.generateParallel := by
  funext depth row
  induction depth with
  | zero => rfl
  | succ depth ih =>
    simp only [Tree.generate, Tree.generateParallel]
    split
    · rfl
    · change Tree.join (Tree.generate depth _) (Tree.generate depth _) =
        Tree.join (Tree.generateParallel depth _) (Tree.generateParallel depth _)
      rw [ih, ih]

/-- A smaller subtree does not collide with a forest of strictly taller trees. -/
theorem carry_below (tree : Tree depth) (forest : List Subtree)
    (taller : ∀ t ∈ forest, depth < t.1) : carry ⟨depth, tree⟩ forest = ⟨depth, tree⟩ :: forest := by
  cases forest with
  | nil => rfl
  | cons t rest =>
    rw [carry, dite_eq_right]
    exact Nat.ne_of_gt (taller t (List.mem_cons_self ..))

/-- Absorbing one complete subtree is the binary carry of its completed tree. -/
theorem absorb_generate (depth : Nat) (row : Fin (2 ^ depth) → Row) (forest : List Subtree)
    (lower : ∀ t ∈ forest, depth ≤ t.1) :
    (Builder.absorb ⟨forest⟩ (Array.ofFn row)).forest = carry ⟨depth, Tree.generate depth row⟩ forest := by
  simp only [Builder.absorb, ← Array.foldl_toList, Array.toList_ofFn]
  induction depth generalizing forest with
  | zero =>
    simp only [Nat.pow_zero, List.ofFn_succ,
      List.ofFn_zero, List.foldl_cons, List.foldl_nil, Builder.absorbRow, Tree.generate]
  | succ depth ih =>
    rw [splitRows, List.foldl_append]
    have left := ih (leftRows row) forest (fun t ht => Nat.le_of_succ_le (lower t ht))
    have below := carry_below (Tree.generate depth (leftRows row)) forest lower
    have first : List.foldl Builder.absorbRow ⟨forest⟩ (List.ofFn (leftRows row)) =
        ⟨⟨depth, Tree.generate depth (leftRows row)⟩ :: forest⟩ := by
      apply congrArg Builder.mk
      exact left.trans below
    rw [first]
    have second := ih (rightRows row) (⟨depth, Tree.generate depth (leftRows row)⟩ :: forest)
      (by intro t ht; rcases List.mem_cons.mp ht with h | h
          · subst t; exact Nat.le_refl _
          · exact Nat.le_of_succ_le (lower t h))
    change _ = _ at second
    rw [show (List.foldl Builder.absorbRow
      ⟨⟨depth, Tree.generate depth (leftRows row)⟩ :: forest⟩ (List.ofFn (rightRows row))).forest =
        carry ⟨depth, Tree.generate depth (rightRows row)⟩
          (⟨depth, Tree.generate depth (leftRows row)⟩ :: forest) from second]
    rw [carry, dite_eq_left rfl]
    rfl

/-- Commit a power-of-two generated row family without materializing a leaf array. -/
def commitGenerated (depth : Nat) (row : Fin (2 ^ depth) → Row) : Except String Subtree :=
  .ok ⟨depth, Tree.generate depth row⟩

/-- Generated subtrees equal the complete certified streaming commitment. -/
theorem commitGenerated_eq (depth : Nat) (row : Fin (2 ^ depth) → Row) :
    commitGenerated depth row = commit (Array.ofFn row) := by
  have forest := absorb_generate depth row [] (by intro t ht; cases ht)
  simp only [carry] at forest
  simp only [commitGenerated, commit, Builder.finish, forest]

end CompStark.Keccak.Merkle
