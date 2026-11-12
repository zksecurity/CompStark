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

A table carries a public padding row that satisfies its constraints: the bus argument corrects
every padding row by it, so padding rows hold arbitrary data that satisfies the constraints, and a
table with padding rows reads no preprocessed column in its tuples. The `i`-th bus of
`System.buses` is separated from the others by `g ^ i`. A `Layout` gives each table its executed
row count and its power-of-two height; tables have different heights. `Satisfied` is the relation the proof system proves; `WellFormed` collects the
side conditions on a description and a layout. -/

@[expose] public section

namespace CompStark.Stark.Expr

variable {F : Type}

/-- The expression reads only the current row of the trace and of the preprocessed trace. -/
def currentRow : Expr F → Bool
  | cur _ | prepCur _ | const _ => true
  | next _ | prepNext _ | periodic _ | pub _ | isFirstRow | isLastRow | isTransition => false
  | add a b | sub a b | mul a b => a.currentRow && b.currentRow

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

/-- An AIR with current-row constraints, its bus interactions, its nonzero columns, its virtual
columns and its public padding row. -/
structure Table (F : Type) where
  /-- Width, current-row constraints and preprocessed columns. -/
  air : Air F
  /-- The bus interactions, on every executed row. -/
  interactions : List (Interaction F) := []
  /-- Columns that do not vanish on executed rows. -/
  nonzero : List ℕ := []
  /-- Columns not committed, bound by `System.external`. -/
  virtual : List ℕ := []
  /-- The public padding row: the bus argument corrects every padding row by it. -/
  padding : List F := []

/-- One trace per table, as rows. -/
abbrev Witness (F : Type) (n : ℕ) := Fin n → List (Array F)

/-- Tables connected by buses, and the relation other arguments establish on the witness. -/
structure System (F : Type) where
  /-- The tables. -/
  tables : List (Table F)
  /-- The buses; the `i`-th is separated by `g ^ i` in the bus argument. -/
  buses : List String
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

/-- The environment of table `t`'s padding row at row `i`: its public padding row and the
preprocessed row `i`. -/
def paddingEnv (L : Layout S.tables.length) (t : Fin S.tables.length) (i : ℕ) : Expr.Env F F :=
  { S.env L (fun _ => []) t i with cur := fun c => (S.table t).padding.getD c 0 }

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
  (∀ c ∈ T.air.constraints, c.currentRow = true ∧
    c.colsBelow T.air.width 0 T.air.preprocessedWidth 0 = true) ∧
  (∀ I ∈ T.interactions, ∀ e ∈ I.tuple, e.currentRow = true ∧
    e.colsBelow T.air.width 0 T.air.preprocessedWidth 0 = true) ∧
  (∀ c ∈ T.nonzero, c < T.air.width) ∧ (∀ c ∈ T.virtual, c < T.air.width)

instance : Decidable T.WellFormed := by unfold WellFormed; infer_instance

end Table

/-- The buses are distinct, fewer than `2 ^ 64 - 1`, and name every interaction's bus; every table
is well formed and executes at most its height; its preprocessed trace has its height; its padding
row has its width and satisfies its constraints on every padding row; and a table with padding
rows reads no preprocessed column in its tuples. -/
def System.WellFormed {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [DecidableEq F] (S : System F)
    (L : Layout S.tables.length) : Prop :=
  S.buses.Nodup ∧ S.buses.length < 2 ^ 64 - 1 ∧
  ∀ t, (S.table t).WellFormed ∧ L.executed t ≤ 2 ^ L.logHeight t ∧
    (∀ I ∈ (S.table t).interactions, I.bus ∈ S.buses) ∧
    (S.table t).air.preprocessed.size = 2 ^ L.logHeight t * (S.table t).air.preprocessedWidth ∧
    (S.table t).padding.length = (S.table t).air.width ∧
    (∀ i ∈ List.range' (L.executed t) (2 ^ L.logHeight t - L.executed t),
      ∀ c ∈ (S.table t).air.constraints, c.eval (S.paddingEnv L t i) = 0) ∧
    (L.executed t < 2 ^ L.logHeight t → ∀ I ∈ (S.table t).interactions, ∀ e ∈ I.tuple,
      e.colsBelow (S.table t).air.width 0 0 0 = true)

instance {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [DecidableEq F] (S : System F)
    (L : Layout S.tables.length) : Decidable (S.WellFormed L) := by
  unfold System.WellFormed; infer_instance

end CompStark.Tables
