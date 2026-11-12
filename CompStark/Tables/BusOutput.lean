/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Bus.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Forms
public import CompStark.Tables.Riders

/-! The endpoint of the bus argument: from the three leaf claims at the GKR's final point to the
values of the directly opened tables' columns and one debt per side for the table sumcheck.

A side's leaf extension is a public part, computed by the verifier from the directly opened
columns' values, the preprocessed columns and the padding rows, plus the sum over the other tables
of their selector-weighted bus forms (`tableForm`), which the table sumcheck owes. -/

@[expose] public section

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

variable (S : System K) (L : Layout S.tables.length)

/-- A table opened directly by the bus: no constraints, no nonzero columns, no padding rows, and
every tuple entry a column, a preprocessed column or a constant. -/
def Direct (t : Fin S.tables.length) : Bool :=
  (S.table t).air.constraints.isEmpty && (S.table t).nonzero.isEmpty &&
    decide (L.executed t = 2 ^ L.logHeight t) &&
    (S.table t).interactions.all fun I ↦ I.tuple.all Expr.atomic

/-- The committed columns the directly opened tables' tuples read, table by table in increasing
order: the bus's boundary values. -/
def boundaryColumns : List (Fin S.tables.length × ℕ) :=
  (List.finRange S.tables.length).flatMap fun t ↦
    if S.Direct L t then
      ((List.range (S.table t).air.width).filter fun c ↦
        (S.table t).interactions.any fun I ↦ I.tuple.contains (.cur c)).map (t, ·)
    else []

/-- One value per boundary column. -/
abbrev BoundaryValues := Fin (S.boundaryColumns L).length → E

/-- The value of column `c` of table `t` among the boundary values, zero if absent. -/
def boundaryValue (vals : S.BoundaryValues L) (t : Fin S.tables.length) (c : ℕ) : E :=
  ((S.boundaryColumns L).finIdxOf? (t, c)).elim 0 vals

/-- The extension of preprocessed column `c` of table `t` at a point. -/
def prepColumn (t : Fin S.tables.length) (c : ℕ) (z : List E) : E :=
  mle (L.logHeight t) (fun i ↦ ofK ((S.table t).air.preprocessed.getD
    (i * (S.table t).air.preprocessedWidth + c) 0)) z

/-- The extension of committed column `c` of table `t` at a point. -/
def column (w : Witness K S.tables.length) (t : Fin S.tables.length) (c : ℕ) (z : List E) : E :=
  mle (L.logHeight t) (fun i ↦ ofK (((w t).getD i #[]).getD c 0)) z

/-- The extension of the padding-row selector of table `t`. -/
def paddingMass (t : Fin S.tables.length) (z : List E) : E :=
  mle (L.logHeight t) (fun i ↦ if L.executed t ≤ i then 1 else 0) z

/-- The number of block leaves of a side. -/
def sideLeaves (side : Fin 3) : ℕ := ((S.blocks side).map fun b ↦ 2 ^ Block.height S L b).sum

/-- The bus's depth: the largest side, the tallest table, and at least one variable. -/
def depth : ℕ :=
  max 1 (max (S.maxLogHeight L) (Nat.clog 2 (max (S.sideLeaves L 0) (max (S.sideLeaves L 1) (S.sideLeaves L 2)))))

variable (k : ℕ) (α : Fin k → E) (β : E)

/-- The public part of a block's leaf extension at its low point: a directly opened table's form
at its boundary values and preprocessed extensions, and every block's padding correction. -/
def blockPublic (vals : S.BoundaryValues L) (b : Block S.tables.length) (z : List E) : E :=
  let t := Block.table S b
  (if S.Direct L t then
    S.formE k α β b (S.boundaryValue L vals t) (fun c ↦ S.prepColumn L t c z) else 0) +
  (1 - S.formE k α β b (fun c ↦ ofK ((S.table t).padding.getD c 0)) (fun _ ↦ 0)) *
    S.paddingMass L t z

/-- The public part of a side's leaf extension at point `ζ`. -/
def publicPart (μ : ℕ) (vals : S.BoundaryValues L) (side : Fin 3) (ζ : List E) : E :=
  S.sumBlocks L μ ζ (fun b ↦ S.blockPublic L k α β vals b (ζ.take (Block.height S L b)))
    (S.sortedBlocks L side) 0 +
  (1 - S.sumBlocks L μ ζ (fun _ ↦ 1) (S.sortedBlocks L side) 0)

/-- The selector-weighted bus form of table `t` on a side, at a row's challenge-field values. -/
def tableForm (μ : ℕ) (side : Fin 3) (t : Fin S.tables.length) (ζ : List E) (v p : ℕ → E) : E :=
  S.sumBlocks L μ ζ (fun b ↦ if Block.table S b = t then S.formE k α β b v p else 0)
    (S.sortedBlocks L side) 0

/-- A side's debt for the table sumcheck: the other tables' bus forms summed over their rows. -/
def tableDebt (μ : ℕ) (w : Witness K S.tables.length) (side : Fin 3) (ζ : List E) : E :=
  ∑ t : Fin S.tables.length, if S.Direct L t then 0 else
    mle (L.logHeight t) (fun i ↦ S.tableForm L k α β μ side t ζ
      (fun c ↦ ofK (((w t).getD i #[]).getD c 0))
      (fun c ↦ ofK ((S.table t).air.preprocessed.getD (i * (S.table t).air.preprocessedWidth + c) 0)))
      (ζ.take (L.logHeight t))

end CompStark.Tables.System
