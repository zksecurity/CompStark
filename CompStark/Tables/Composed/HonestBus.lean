/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Certificate
public import CompStark.Multilinear.GrandProductHonest

/-! The honest bus phase: the roots of the witness's three trees, the honest GKR descent and the
true boundary values. Against every coin sequence a satisfying, padded witness reaches the bus
endpoint (`honestBus_terminal`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open _root_.Interaction _root_.Interaction.Oracle

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The bus's coins: the fingerprint draw, then the descent's. -/
abbrev BusCoins := ((Fin k → E) × E) × GrandProduct.Coins (GrandProduct.layers (Bus.μ S L)) 0

/-- The leaves on the bus's depth computed once, read off a table. -/
@[macro_inline] def leavesMemo (w : Witness K S.tables.length) (α : Fin k → E) (β : E) : Fin 3 → ℕ → E :=
  let table := Vector.ofFn fun side : Fin 3 ↦ Vector.ofFn fun i : Fin (2 ^ S.depth L) ↦
    S.stackLeaves L k w α β (S.sortedBlocks L side) i.val
  fun side i ↦ if h : i < 2 ^ S.depth L then table[side][i] else
    S.stackLeaves L k w α β (S.sortedBlocks L side) i

/-- Computing the leaves once leaves them. -/
@[csimp] theorem leaves_code : @System.leaves = @leavesMemo := by
  funext S L k w α β side i
  simp only [leavesMemo, Fin.getElem_fin, Vector.getElem_ofFn]
  split <;> rfl

/-- The true boundary values at a point. -/
def honestBoundary (w : Witness K S.tables.length) (z : List E) : S.BoundaryValues L :=
  fun j ↦ S.column L w (S.boundaryColumns L)[j].1 (S.boundaryColumns L)[j].2
    (z.take (L.logHeight (S.boundaryColumns L)[j].1))

/-- The roots of the push and nonzero trees. -/
def honestRoots (w : Witness K S.tables.length) (α : Fin k → E) (β : E) : E × E :=
  (GrandProduct.level (Bus.μ S L) 0 (S.leaves L k w α β) 0 0,
    GrandProduct.level (Bus.μ S L) 0 (S.leaves L k w α β) 2 0)

/-- The honest bus transcript. -/
def honestBusPath (w : Witness K S.tables.length) (coins : BusCoins S L k) :
    (Bus.protocol S L k).tree.ExecutionPath :=
  let roots := honestRoots S L k w coins.1.1 coins.1.2
  ⟨coins.1, roots, GrandProduct.honestPath (Bus.μ S L) (S.leaves L k w coins.1.1 coins.1.2)
    (Bus.terminalProtocol S L) (fun c ↦ ⟨honestBoundary S L w c.point, PUnit.unit⟩)
    (GrandProduct.layers (Bus.μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩ coins.2⟩

/-- A witness whose constraints hold has zero riders at every point. -/
theorem rider_zero (w : Witness K S.tables.length)
    (constraints : ∀ t, ∀ i < 2 ^ L.logHeight t, ∀ c ∈ (S.table t).air.constraints,
      c.eval (S.env L w t i) = 0)
    (i : Fin (S.riders L).count) (z : List E) : GrandProduct.rider (S.riders L) w i z = 0 := by
  have hz := (S.ridersZero_iff L w).mpr constraints
  unfold GrandProduct.rider
  rw [mle_congr_values _ _ (fun _ ↦ 0) z (fun j hj ↦ hz i ⟨j, hj⟩)]
  simp only [mle, zero_mul, Finset.sum_const_zero]

variable {S L k}

/-- Completeness of the bus: against every coin sequence, a satisfying witness whose padding rows
are the padding row reaches the bus endpoint. -/
theorem honestBus_terminal {width : String → ℕ} (hwf : S.WellFormed L) (hshape : S.BusShape k width)
    (w : Witness K S.tables.length) (hsat : S.Satisfied L w) (padded : S.Padded L w)
    (coins : BusCoins S L k) :
    ∃ o, Bus.outputClaim S L k (honestBusPath S L k w coins) = some o ∧ Bus.Terminal S L k o w := by
  have hT : ∀ t, (S.table t).WellFormed := fun t ↦ (hwf.2.2 t).1
  have hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t := fun t ↦ (hwf.2.2 t).2.1
  have hpad := fun t ↦ (hwf.2.2 t).2.2.2.2.2.2
  obtain ⟨shaped, constraints, nonzero, balanced, _⟩ := hsat
  set α := coins.1.1
  set β := coins.1.2
  set leaves := S.leaves L k w α β
  set μ := Bus.μ S L
  have fits := Bus.depth_fits S L
  have hpull : GrandProduct.level μ 0 leaves 0 0 = GrandProduct.level μ 0 leaves 1 0 := by
    have h0 := S.root_eq_sideProduct L k w α β hshape μ fits padded hexec true
    have h1 := S.root_eq_sideProduct L k w α β hshape μ fits padded hexec false
    simp only [↓reduceIte, Bool.false_eq_true] at h0 h1
    rw [h0, h1]
    exact S.balanced_sideProduct hshape L w balanced α β
  have hnz : GrandProduct.level μ 0 leaves 2 0 ≠ 0 :=
    (S.nonzeroRoot_ne_zero_iff L k w α β μ fits padded hexec).mpr nonzero
  have hstart : (⟨[], ![GrandProduct.level μ 0 leaves 0 0, GrandProduct.level μ 0 leaves 0 0,
      GrandProduct.level μ 0 leaves 2 0]⟩ : GrandProduct.Claim).Holds μ 0 leaves := by
    refine ⟨rfl, fun side ↦ ?_⟩
    rw [GrandProduct.mle_zero]
    fin_cases side
    · rfl
    · exact hpull
    · rfl
  obtain ⟨c', hc', hres⟩ := GrandProduct.result_honest μ leaves (Bus.terminalProtocol S L)
    (fun c ↦ ⟨honestBoundary S L w c.point, PUnit.unit⟩) (GrandProduct.layers μ) 0 _ coins.2
    (by rw [Nat.zero_add, GrandProduct.layers_sum]) hstart
  refine ⟨Bus.output S L k α β c' (honestBoundary S L w c'.point) true, ?_, ?_⟩
  · unfold Bus.outputClaim honestBusPath
    simp only [honestRoots]
    rw [decide_eq_true hnz]
    change Option.bind (GrandProduct.result (Bus.terminalProtocol S L) (GrandProduct.layers μ) 0 _ true
      (GrandProduct.honestPath μ leaves (Bus.terminalProtocol S L)
        (fun c ↦ ⟨honestBoundary S L w c.point, PUnit.unit⟩) (GrandProduct.layers μ) 0 _ coins.2)) _ = _
    rw [hres, Option.bind_some]
    rfl
  · have hz : c'.point.length = μ := hc'.1
    let z : Vector E μ := ⟨c'.point.toArray, by simpa only [List.size_toArray] using hz⟩
    have hzl : z.toList = c'.point := rfl
    have hbd : ∀ p ∈ S.boundaryColumns L, S.boundaryValue L (honestBoundary S L w c'.point) p.1 p.2 =
        S.column L w p.1 p.2 (c'.point.take (L.logHeight p.1)) := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
      exact boundaryValue_get S L _ ⟨j, hj⟩
    refine ⟨rfl, shaped, hz, fun i ↦ rider_zero S L w constraints i _, hbd, fun side ↦ ?_⟩
    change c'.values side - S.publicPart L k α β μ (honestBoundary S L w c'.point) side c'.point = _
    have dec := S.leaf_decomposition k α β L w hT hexec hpad μ fits side z
      (honestBoundary S L w c'.point)
      (fun t c hd hr ↦ hbd (t, c) (Bus.mem_boundaryColumns S L hT t c hd hr))
    rw [hzl] at dec
    rw [hc'.2 side, show GrandProduct.level μ μ leaves side = leaves side from
      funext (GrandProduct.level_full μ leaves side), dec]
    simp only [add_sub_cancel_left]
    rfl

end CompStark.Tables.Composed
