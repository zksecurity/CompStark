/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Air
public import Mathlib.Data.Multiset.Basic

/-! # Tables connected by buses

A `System` is a list of tables connected by named buses. A table is a `Stark.Air` whose
constraints read only the current row of its trace and of its preprocessed trace, together with
its bus interactions, the columns that must not vanish on its executed rows, and its virtual
columns. On every executed row an interaction pushes or pulls the tuple of its expressions on its
bus; a bus is balanced when the multiset of pushed tuples equals the multiset of pulled ones, each
tuple counted with its natural multiplicity across rows and tables. A table's rows past its
executed count are padding: they satisfy its constraints and take no part in its buses or its
nonzero columns.

Public data is preprocessed: a table may have preprocessed columns, fixed and known to the
verifier, of the table's height. A data source that is not a table of the computation (a public
program, the boundary of a memory) is a table whose tuple coordinates are preprocessed or
committed columns and which may have no constraints. Virtual columns are part of the witness but
not of the commitment; the relation `external` that other arguments establish binds them.

A `Layout` gives each table its executed row count and its power-of-two height; tables have
different heights. `Satisfied` is the relation the proof system proves; `WellFormed` collects the
side conditions on a description and a layout. -/

@[expose] public section

namespace CompStark.Stark.Expr

variable {F : Type}

/-- The expression reads only the current row of the trace and of the preprocessed trace. -/
def rowLocal : Expr F → Bool
  | cur _ | prepCur _ | const _ => true
  | next _ | prepNext _ | periodic _ | pub _ | isFirstRow | isLastRow | isTransition => false
  | add a b | sub a b | mul a b => a.rowLocal && b.rowLocal

end CompStark.Stark.Expr

namespace CompStark.Tables

open CompStark.Stark

/-- On every executed row, push or pull the tuple of the expressions on the named bus. -/
structure Interaction (F : Type) where
  /-- The bus. -/
  bus : String
  /-- `true` to push, `false` to pull. -/
  push : Bool
  /-- The tuple's coordinates. -/
  tuple : List (Expr F)

/-- An AIR with row-local constraints, its bus interactions, its nonzero columns and its virtual
columns. -/
structure Table (F : Type) where
  /-- Width, row-local constraints and preprocessed columns. -/
  air : Air F
  /-- The bus interactions, on every executed row. -/
  interactions : List (Interaction F) := []
  /-- Columns that do not vanish on executed rows. -/
  nonzero : List ℕ := []
  /-- Columns not committed, bound by `System.external`. -/
  virtual : List ℕ := []

/-- One trace per table, as rows. -/
abbrev Witness (F : Type) (n : ℕ) := Fin n → List (Array F)

/-- Tables connected by buses, and the relation other arguments establish on the witness. -/
structure System (F : Type) where
  /-- The tables. -/
  tables : List (Table F)
  /-- The relation of the virtual columns, established by other arguments. -/
  external : Witness F tables.length → Prop := fun _ => True

/-- Each table's executed row count and log-height. -/
structure Layout (n : ℕ) where
  /-- Executed rows; the rest of the table is padding. -/
  executed : Fin n → ℕ
  /-- The table has `2 ^ logHeight` rows. -/
  logHeight : Fin n → ℕ

namespace System

variable {F : Type} (S : System F)

/-- Table `t`. -/
def table (t : Fin S.tables.length) : Table F := S.tables[t]

/-- Every bus that some interaction names, in order of first appearance. -/
def buses : List String :=
  (S.tables.flatMap fun T => T.interactions.map (·.bus)).dedup

variable [Zero F]

/-- The row environment of row `i` of table `t`: its columns, its preprocessed columns, and zero for
every reading that is not row-local. -/
def env (L : Layout S.tables.length) (w : Witness F S.tables.length) (t : Fin S.tables.length)
    (i : ℕ) : Expr.Env F F where
  cur c := ((w t).getD i #[]).getD c 0
  next _ := 0
  prepCur c := (S.table t).air.preprocessed.getD (i * (S.table t).air.preprocessedWidth + c) 0
  prepNext _ := 0
  periodic _ := 0
  pub _ := 0
  const c := c
  isFirstRow := 0
  isLastRow := 0
  isTransition := 0

variable [Add F] [Sub F] [Mul F]

/-- The tuples a table's interactions on bus `b` with direction `push` emit on its executed rows. -/
def tableTuples (L : Layout S.tables.length) (w : Witness F S.tables.length) (b : String)
    (push : Bool) (t : Fin S.tables.length) : List (List F) :=
  (List.range (L.executed t)).flatMap fun i =>
    ((S.table t).interactions.filter fun I => I.bus == b && I.push == push).map fun I =>
      I.tuple.map (Expr.eval (S.env L w t i))

/-- The multiset of tuples pushed (`push = true`) or pulled on bus `b` by all tables. -/
def tuples (L : Layout S.tables.length) (w : Witness F S.tables.length) (b : String)
    (push : Bool) : Multiset (List F) :=
  ((List.finRange S.tables.length).flatMap (S.tableTuples L w b push) : List (List F))

/-- The witness satisfies the description at the layout: shapes, the constraints on every row,
nonzero columns on executed rows, balanced buses and the external relation. -/
def Satisfied (L : Layout S.tables.length) (w : Witness F S.tables.length) : Prop :=
  (∀ t, (w t).length = 2 ^ L.logHeight t ∧ ∀ row ∈ w t, row.size = (S.table t).air.width) ∧
  (∀ t, ∀ i < 2 ^ L.logHeight t, ∀ c ∈ (S.table t).air.constraints,
    c.eval (S.env L w t i) = 0) ∧
  (∀ t, ∀ i < L.executed t, ∀ c ∈ (S.table t).nonzero, ((w t).getD i #[]).getD c 0 ≠ 0) ∧
  (∀ b ∈ S.buses, S.tuples L w b true = S.tuples L w b false) ∧
  S.external w

instance [DecidableEq F] [DecidablePred S.external] (L : Layout S.tables.length)
    (w : Witness F S.tables.length) : Decidable (S.Satisfied L w) := by
  unfold Satisfied; infer_instance

end System

namespace Table

variable {F : Type} (T : Table F)

/-- The table's AIR has row-local constraints, no lookups, periodic columns or public values, and
reads columns inside its widths; its tuples are row-local and its nonzero and virtual columns are
columns of its trace. -/
def WellFormed : Prop :=
  T.air.lookups.isEmpty = true ∧ T.air.periodic.isEmpty = true ∧ T.air.numPublicValues = 0 ∧
  (∀ c ∈ T.air.constraints, c.rowLocal = true ∧
    c.colsBelow T.air.width 0 T.air.preprocessedWidth 0 = true) ∧
  (∀ I ∈ T.interactions, ∀ e ∈ I.tuple, e.rowLocal = true ∧
    e.colsBelow T.air.width 0 T.air.preprocessedWidth 0 = true) ∧
  (∀ c ∈ T.nonzero, c < T.air.width) ∧ (∀ c ∈ T.virtual, c < T.air.width)

instance : Decidable T.WellFormed := by unfold WellFormed; infer_instance

end Table

/-- Every table is well formed, executes at most its height, and its preprocessed trace has the
table's height. -/
def System.WellFormed {F : Type} (S : System F) (L : Layout S.tables.length) : Prop :=
  ∀ t, (S.table t).WellFormed ∧ L.executed t ≤ 2 ^ L.logHeight t ∧
    (S.table t).air.preprocessed.size = 2 ^ L.logHeight t * (S.table t).air.preprocessedWidth

instance {F : Type} (S : System F) (L : Layout S.tables.length) : Decidable (S.WellFormed L) := by
  unfold System.WellFormed; infer_instance

end CompStark.Tables
