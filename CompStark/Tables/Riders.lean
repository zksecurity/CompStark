/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Basic
public import CompStark.Multilinear.GrandProduct

/-! The constraint residuals of a set of tables as the riders of the grand-product GKR: one rider
table per table and constraint, of the table's height, holding the constraint's value on each row
in the challenge field. The riders vanish on their Boolean rows exactly when every constraint
holds on every row (`ridersZero_iff`). -/

@[expose] public section

namespace CompStark.Tables

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

namespace System

variable (S : System K) (L : Layout S.tables.length)

/-- Every table and constraint, in table order. -/
def constraintPairs : List (Fin S.tables.length × Expr K) :=
  (List.finRange S.tables.length).flatMap fun t ↦ (S.table t).air.constraints.map (t, ·)

/-- Every table has its height and its rows have its width. -/
def Shaped (w : Witness K S.tables.length) : Prop :=
  ∀ t, (w t).length = 2 ^ L.logHeight t ∧ ∀ row ∈ w t, row.size = (S.table t).air.width

/-- The largest table log-height. -/
def maxLogHeight : ℕ := Finset.univ.sup L.logHeight

/-- The constraint residuals as grand-product riders. -/
def riders : GrandProduct.Riders (Witness K S.tables.length) where
  Fits := S.Shaped L
  count := (S.constraintPairs).length
  height i := L.logHeight (S.constraintPairs[i]).1
  maxHeight := S.maxLogHeight L
  height_le i := Finset.le_sup (f := L.logHeight) (Finset.mem_univ _)
  table w i j := ofK ((S.constraintPairs[i]).2.eval (S.env L w (S.constraintPairs[i]).1 j))

/-- The riders vanish on their Boolean rows exactly when every constraint holds on every row. -/
theorem ridersZero_iff (w : Witness K S.tables.length) :
    GrandProduct.RidersZero (S.riders L) w ↔
      ∀ t, ∀ i < 2 ^ L.logHeight t, ∀ c ∈ (S.table t).air.constraints,
        c.eval (S.env L w t i) = 0 := by
  have zero (x : K) : ofK x = 0 ↔ x = 0 :=
    ⟨fun h ↦ ofK_injective (h.trans (map_zero (algebraMap K E)).symm), fun h ↦ by
      rw [h]; exact map_zero (algebraMap K E)⟩
  constructor
  · intro h t i hi c hc
    have mem : (t, c) ∈ S.constraintPairs :=
      List.mem_flatMap.mpr ⟨t, List.mem_finRange t, List.mem_map.mpr ⟨c, hc, rfl⟩⟩
    obtain ⟨n, hn, he⟩ := List.getElem_of_mem mem
    have := h ⟨n, hn⟩ ⟨i, by simpa only [riders, Fin.getElem_fin, he] using hi⟩
    simp only [riders, Fin.getElem_fin, he] at this
    exact (zero _).mp this
  · intro h n ⟨j, hjn⟩
    have mem := List.getElem_mem (l := S.constraintPairs) n.isLt
    obtain ⟨t, -, hp⟩ := List.mem_flatMap.mp mem
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hp
    have hpair : S.constraintPairs[n.val] = (t, c) := he.symm
    have hj : j < 2 ^ L.logHeight t := by
      simp only [riders, Fin.getElem_fin] at hjn
      rw [hpair] at hjn
      exact hjn
    simp only [riders, Fin.getElem_fin]
    rw [hpair]
    exact (zero _).mpr (h t j hj c hc)

end System

end CompStark.Tables
