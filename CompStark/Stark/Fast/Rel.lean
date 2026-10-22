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

/-- A trace of `2 ^ logH` rows and `w` columns in chunks of packed rows represents its values: they
are `2 ^ logH` rows of `w` values, and the trace is their `2 ^ k` chunks of `2 ^ (logH - k)` rows,
for some `k ≤ logH`. -/
def RT (logH w : Nat) (t : Array ByteArray) (m : Array F) : Prop :=
  m.size = 2 ^ logH * w ∧
    ∃ k ≤ logH, t = CompPoly.CPolynomial.NTTFast.Packed.Native.rowChunks m w logH k

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

end CompStark.Stark.Fast
