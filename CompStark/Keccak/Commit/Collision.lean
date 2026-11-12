/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Bytes

/-! Explicit Keccak-256 collisions and their computable search over candidate pairs. -/

set_option autoImplicit false

@[expose] public section
namespace CompStark.Keccak.Commit

/-- A collision of a raw-byte hash consists of distinct bytes with the same digest. -/
def Collision (hash : ByteArray → Digest) (a b : ByteArray) : Prop := a ≠ b ∧ hash a = hash b

/-- A candidate collision is decided by finite byte and digest equality. -/
instance (hash : ByteArray → Digest) (a b : ByteArray) : Decidable (Collision hash a b) :=
  inferInstanceAs (Decidable (a ≠ b ∧ hash a = hash b))

/-- The first Keccak-colliding candidate pair, or two equal empty strings if there is none. -/
def findCollision (pairs : List (ByteArray × ByteArray)) : ByteArray × ByteArray :=
  (pairs.find? fun pair => decide (Collision hash pair.1 pair.2)).getD
    (ByteArray.empty, ByteArray.empty)

/-- The search returns a collision exactly when some candidate pair collides. -/
theorem findCollision_iff (pairs : List (ByteArray × ByteArray)) :
    Collision hash (findCollision pairs).1 (findCollision pairs).2 ↔
      ∃ pair ∈ pairs, Collision hash pair.1 pair.2 := by
  unfold findCollision
  cases found : pairs.find? (fun pair => decide (Collision hash pair.1 pair.2)) with
  | none =>
    rw [Option.getD_none]
    refine ⟨fun collision => (collision.1 rfl).elim, ?_⟩
    rintro ⟨pair, member, collision⟩
    exact (List.find?_eq_none.mp found pair member (decide_eq_true collision)).elim
  | some pair =>
    have collision : Collision hash pair.1 pair.2 := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    rw [Option.getD_some]
    exact ⟨fun _ => ⟨pair, List.mem_of_find?_eq_some found, collision⟩, fun _ => collision⟩

end CompStark.Keccak.Commit
