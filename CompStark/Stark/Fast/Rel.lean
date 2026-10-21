/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast
public import CompStark.Fri.Assumptions

/-! # The fast backend's representations

How the fast backend's packed matrices, commitments and vectors of extension elements represent
the specification's: by their encodings, with no bound on sizes. The laws of the kernels state the
sizes they need as hypotheses on the specification's values (`CompStark/Fri/Assumptions.lean`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-- A packed matrix represents the matrix of its encoded values. -/
def RM (pm : PMat) (m : Mat F) : Prop :=
  pm.width = m.width ∧ pm.height = m.height ∧ pm.words = encode m.values

/-- Planes represent the elements whose coordinates they encode. -/
def RV (v : EVec p) (a : Array EF) : Prop :=
  v.n = a.size ∧ v.c0 = encode (a.map (·.c0)) ∧ v.c1 = encode (a.map (·.c1)) ∧
    v.c2 = encode (a.map (·.c2)) ∧ v.c3 = encode (a.map (·.c3))

/-- A packed commitment represents the specification's of the represented matrices, with the
encoded digest layers. -/
def RC (c : Commit) (s : Committed F) : Prop :=
  List.Forall₂ RM c.mats s.mats ∧ c.layers = s.layers.map encodeDigests

/-- A packed matrix's matrix is the matrix it represents. -/
theorem toMat_of_RM {pm : PMat} {m : Mat F} (h : RM pm m) : pm.toMat = m := by
  obtain ⟨hw, hh, hv⟩ := h
  rw [PMat.toMat, hw, hh, hv, CompPoly.PackedRepr.decode_encode]

variable [Mont32BaseField p] [Binomial4 p] in
/-- The fast backend's LogUp quotient is the specification's. -/
theorem lookupQuotient_rel (A : Air F) (ext : List (Lookup.ExtExpr F)) (pis : List F)
    (d l : Nat) (chs : List EF) (t alpha : EF) {m : PMat} {s : Mat F} {pm : Option PMat}
    {ps : Option (Mat F)} {rm : PMat} {rs : Mat F} (h : RM m s) (hp : Option.Rel RM pm ps)
    (hr : RM rm rs) :
    lookupQuotient A ext pis d l m pm rm chs t alpha =
      lookupQuotientOfLde A ext pis d l s ps rs chs t alpha := by
  rw [lookupQuotient, toMat_of_RM h, toMat_of_RM hr]
  cases hp with
  | none => rfl
  | some hp => rw [Option.map_some, toMat_of_RM hp]

end CompStark.Stark.Fast
