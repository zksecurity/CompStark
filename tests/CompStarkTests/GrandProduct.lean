/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.GrandProductDecision
meta import CompStark.Multilinear.GrandProductDecision

/-! Known answers for the grand-product GKR's layer schedule, layer claims and rider decisions. -/

@[expose] public section
namespace CompStarkTests.GrandProduct
open CompStark.BinaryFields CompStark.Multilinear CompStark.Multilinear.GrandProduct

/-- Leaves `k + 1` on every side, eight of them. -/
def leaves : Fin 3 → ℕ → E := fun _ k => ofK (K.ofBits (k + 1))

/-- One rider table of two variables over a witness that is the table itself. -/
def riders : Riders (ℕ → E) where
  Fits := fun _ => True
  count := 1
  height := fun _ => 2
  maxHeight := 2
  height_le := fun _ => le_refl 2
  table := fun q _ => q

instance : DecidablePred riders.Fits := fun _ => inferInstanceAs (Decidable True)

#guard layers 5 = [1, 2, 2]
#guard layers 4 = [2, 2]
#guard decide ((⟨[], fun s => level 3 0 leaves s 0⟩ : Claim).Holds 3 0 leaves)
#guard !decide ((⟨[], fun _ => 0⟩ : Claim).Holds 3 0 leaves)
#guard decide (RidersZero riders fun _ => 0)
#guard !decide (RidersZero riders fun k => if k = 3 then 1 else 0)
#guard !decide (RidersRestricted riders (fun k => if k = 3 then 1 else 0) fun _ => none)
#guard decide (RidersRestricted riders (fun k => if k = 3 then 1 else 0) fun k => if k = 0 then some 0 else none)

end CompStarkTests.GrandProduct
