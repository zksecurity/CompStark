/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Interaction.Oracle.Security.StandardBcs

/-! The challenge keys of a compiled path: a selected prefix is the path's key at its rank, the path's
keys are closed under strict ancestors, and challenge consistency reads the table only at them. -/

set_option autoImplicit false

@[expose] public section
namespace CompStark.Compiled.PathKeys
open Interaction Interaction.Oracle Interaction.Oracle.Security StandardBcs StateRestoration

/-- The prefix selected at a rank is the path's challenge key at that rank. -/
theorem selectedPrefix_key {Com : Type} [DecidableEq Com] {protocol : Protocol} (coin : PublicCoin protocol)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path) (rank : ℕ)
    (selected : (pre : Prefix PUnit (compiledCoin Com coin)) × PrefixMessages coin pre)
    (found : selectedPrefix coin path messages rank = some selected) :
    (prefixKeys (compiledCoin Com coin) (CorrelationIntractable.erasePath _ path))[rank]? = some selected.1 := by
  induction coin generalizing rank with
  | done => cases found
  | sender next ih =>
      obtain ⟨⟨pre, words⟩, inner, rfl⟩ := Option.map_eq_some_iff.mp found
      have recursive := ih path.1 path.2 messages rank ⟨pre, words⟩ inner
      simp only [compiledCoin, CorrelationIntractable.erasePath, prefixKeys]
      erw [List.getElem?_map, recursive]
      rfl
  | oracle next ih =>
      obtain ⟨⟨pre, words⟩, inner, rfl⟩ := Option.map_eq_some_iff.mp found
      have recursive := ih path.2 (fun i => messages (.inr i)) rank ⟨pre, words⟩ inner
      simp only [compiledCoin, CorrelationIntractable.erasePath, prefixKeys]
      erw [List.getElem?_map, recursive]
      rfl
  | challenge next ih =>
      cases rank with
      | zero =>
          cases Option.some.inj found
          rfl
      | succ rank =>
          obtain ⟨⟨pre, words⟩, inner, rfl⟩ := Option.map_eq_some_iff.mp found
          have recursive := ih path.2 messages rank ⟨pre, words⟩ inner
          simp only [compiledCoin, CorrelationIntractable.erasePath, prefixKeys]
          erw [List.getElem?_cons_succ, List.getElem?_map, recursive]
          rfl

/-- The challenge keys of a message sequence are closed under strict ancestors. -/
theorem strictAncestors_mem {protocol : Protocol} (coin : PublicCoin protocol) (messages : Messages PUnit coin)
    (pre : Prefix PUnit coin) (member : pre ∈ prefixKeys coin messages)
    (ancestor : Prefix PUnit coin) (ancestorMember : ancestor ∈ CorrelationIntractable.strictAncestors coin pre) :
    ancestor ∈ prefixKeys coin messages := by
  induction coin with
  | done => exact nomatch pre
  | sender next ih =>
      obtain ⟨move, rest⟩ := messages
      obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp ancestorMember
      exact List.mem_map.mpr ⟨a, ih move rest inner innerMember a aMember, rfl⟩
  | oracle next ih =>
      obtain ⟨message, rest⟩ := messages
      obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp ancestorMember
      exact List.mem_map.mpr ⟨a, ih rest inner innerMember a aMember, rfl⟩
  | challenge next ih =>
      obtain ⟨salt, rest⟩ := messages
      rcases List.mem_cons.mp member with rfl | member
      · cases ancestorMember
      · obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp member
        rcases List.mem_cons.mp ancestorMember with rfl | ancestorMember
        · exact List.mem_cons_self
        · obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp ancestorMember
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, ih rest inner innerMember a aMember, rfl⟩)

/-- Challenge consistency of a path reads the table only at the path's challenge keys. -/
theorem consistent_congr {protocol : Protocol} (coin : PublicCoin protocol) (path : protocol.tree.ExecutionPath)
    (table other : PrefixTable PUnit coin)
    (agree : ∀ pre ∈ prefixKeys coin (CorrelationIntractable.erasePath coin path), table pre = other pre) :
    CorrelationIntractable.Consistent coin table path ↔ CorrelationIntractable.Consistent coin other path := by
  induction coin with
  | done => exact Iff.rfl
  | sender next ih =>
      exact ih path.1 path.2 _ _ (fun pre member => agree ⟨path.1, pre⟩ (List.mem_map.mpr ⟨pre, member, rfl⟩))
  | oracle next ih =>
      exact ih path.2 _ _ (fun pre member => agree ⟨path.1, pre⟩ (List.mem_map.mpr ⟨pre, member, rfl⟩))
  | challenge next ih =>
      exact and_congr (by rw [agree (.inl PUnit.unit) List.mem_cons_self])
        (ih path.2 _ _ (fun pre member => agree (.inr ⟨PUnit.unit, pre⟩)
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨pre, member, rfl⟩))))

end CompStark.Compiled.PathKeys
