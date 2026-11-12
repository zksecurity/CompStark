/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Basic
public import CompStark.BinaryFields.Generator

/-! Two small sets of tables over `BF64`.

`squares`: a table of four rows pushes `(x, x²)` on bus `sq`; two tables of two rows pull those
tuples, one tuple twice, so the bus balances only with multiplicities; the first puller has a
virtual column `z = y²` that `external` binds.

`program`: a public program of four instruction slots, three of them used, is a non-table source
with preprocessed `(pc, op)` columns; it pushes each instruction with count `1` and pulls it with
its committed final count. An execution table of eight rows, five executed, reads an instruction
by pulling `(pc, op, c)` and pushing `(pc, op, c g)`; its count column is nonzero, and every row,
padding included, has `op = pc + 10`. -/

@[expose] public section

namespace CompStark.Tables.Examples

open CompStark.Stark CompStark.BinaryFields

/-- The field element of a natural number's bits. -/
abbrev k (n : ℕ) : K := K.ofBits n

/-- The pusher of `(x, x²)`. -/
def squareTable : Table K where
  air := { width := 2, numPublicValues := 0, constraints := [.cur 1 - .cur 0 * .cur 0] }
  interactions := [⟨"sq", true, [.cur 0, .cur 1]⟩]

/-- A puller of `(x, y)` with a virtual column `z`. -/
def queryTable : Table K where
  air := { width := 3, numPublicValues := 0, constraints := [] }
  interactions := [⟨"sq", false, [.cur 0, .cur 1]⟩]
  virtual := [2]

/-- A puller of `(x, y)`. -/
def otherTable : Table K where
  air := { width := 2, numPublicValues := 0, constraints := [] }
  interactions := [⟨"sq", false, [.cur 0, .cur 1]⟩]

/-- Every row of the query table has `z = y²`. -/
def squaresExternal (w : Witness K 3) : Bool :=
  (w 1).all fun row => row.getD 2 0 == row.getD 1 0 * row.getD 1 0

/-- Squares pushed by one table and pulled by two, one tuple twice. -/
def squares : System K where
  tables := [squareTable, queryTable, otherTable]
  external w := squaresExternal w = true

instance : DecidablePred squares.external :=
  fun w => inferInstanceAs (Decidable (squaresExternal w = true))

/-- Heights four, two and two, every row executed. -/
def squaresLayout : Layout squares.tables.length :=
  ⟨fun t => [4, 2, 2].getD t.val 0, fun t => [2, 1, 1].getD t.val 0⟩

/-- A row `(x, x²)`. -/
def squareRow (x : ℕ) : Array K := #[k x, k x * k x]

/-- The witness: squares of 2, 3, 3 and 5; the query table pulls 3 twice with `z = y²`. -/
def squaresWitness : Witness K squares.tables.length := fun t =>
  [[2, 3, 3, 5].map squareRow,
    [3, 3].map fun x => (squareRow x).push (k x * k x * (k x * k x)),
    [2, 5].map squareRow].getD t.val []

/-- The program table: preprocessed `(pc, op)` with `op = pc + 10`, and its final count. -/
def programTable : Table K where
  air := { width := 1, numPublicValues := 0, constraints := [], preprocessedWidth := 2,
           preprocessed := #[k 0, k 0 + k 10, k 1, k 1 + k 10, k 2, k 2 + k 10, k 3, k 3 + k 10] }
  interactions := [⟨"code", true, [.prepCur 0, .prepCur 1, .const 1]⟩,
    ⟨"code", false, [.prepCur 0, .prepCur 1, .cur 0]⟩]

/-- The execution table `(pc, op, c)`: reads the instruction at count `c` and returns it at `c g`. -/
def executionTable : Table K where
  air := { width := 3, numPublicValues := 0, constraints := [.cur 1 - .cur 0 - .const (k 10)] }
  interactions := [⟨"code", false, [.cur 0, .cur 1, .cur 2]⟩,
    ⟨"code", true, [.cur 0, .cur 1, .cur 2 * .const g]⟩]
  nonzero := [2]

/-- A public program read by an execution table. -/
def program : System K where
  tables := [programTable, executionTable]

instance : DecidablePred program.external := fun _ => isTrue trivial

/-- Three of four program slots and five of eight execution rows executed. -/
def programLayout : Layout program.tables.length :=
  ⟨fun t => [3, 5].getD t.val 0, fun t => [2, 3].getD t.val 0⟩

/-- An execution row. -/
def executionRow (pc : ℕ) (c : K) : Array K := #[k pc, k pc + k 10, c]

/-- The witness: reads of slots 0, 1, 2, 1, 0 and three padding rows. -/
def programWitness : Witness K program.tables.length := fun t =>
  [[#[g * g], #[g * g], #[g], #[0]],
    [executionRow 0 1, executionRow 1 1, executionRow 2 1, executionRow 1 g, executionRow 0 g,
      executionRow 0 0, executionRow 0 0, executionRow 0 0]].getD t.val []

/-- Both descriptions and layouts are well formed. -/
theorem squares_wellFormed : squares.WellFormed squaresLayout := by decide

/-- The program description and layout are well formed. -/
theorem program_wellFormed : program.WellFormed programLayout := by decide

end CompStark.Tables.Examples
