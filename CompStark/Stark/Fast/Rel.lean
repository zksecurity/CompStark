/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast

/-! # The fast backend's representations

How the fast backend's packed matrices, commitments and vectors of extension elements represent
the specification's: by their encodings, with no bound on sizes. The fast kernels check the sizes
they need and otherwise run the specification on the decoded values.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)

local notation "EF" => KoalaBear.Fast.Ext4

/-- A packed matrix represents the matrix of its encoded values. -/
def RM (pm : PMat) (m : Mat) : Prop :=
  pm.width = m.width ∧ pm.height = m.height ∧ pm.words = encode m.values

/-- Planes represent the elements whose coordinates they encode. -/
def RV (v : EVec) (a : Array EF) : Prop :=
  v.n = a.size ∧ v.c0 = encode (a.map (·.c0)) ∧ v.c1 = encode (a.map (·.c1)) ∧
    v.c2 = encode (a.map (·.c2)) ∧ v.c3 = encode (a.map (·.c3))

/-- A packed commitment represents the specification's of the represented matrices, with the
encoded digest layers. -/
def RC (c : Commit) (s : Committed) : Prop :=
  List.Forall₂ RM c.mats s.mats ∧ c.layers = s.layers.map encodeDigests

end CompStark.Stark.Fast
