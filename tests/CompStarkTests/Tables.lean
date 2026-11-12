/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Examples
meta import CompStark.Tables.Examples

/-! The example sets of tables: their witnesses satisfy them, and tampered witnesses do not. -/

@[expose] public section
namespace CompStarkTests.Tables
open CompStark.Tables CompStark.Tables.Examples CompStark.BinaryFields

/-- Replace row `i` of table `t`. -/
def setRow {n : ℕ} (w : Witness K n) (t i : ℕ) (row : Array K) : Witness K n :=
  fun s => if s.val = t then (w s).set i row else w s

#guard squares.buses = ["sq"]
#guard decide (squares.Satisfied squaresLayout squaresWitness)
-- The bus needs the repeated tuple twice: pulling `(5, 25)` in place of the second `(3, 9)`.
#guard !decide (squares.Satisfied squaresLayout (setRow squaresWitness 1 1 ((squareRow 5).push 0)))
-- A row that is not a square breaks the constraint.
#guard !decide (squares.Satisfied squaresLayout (setRow squaresWitness 0 0 #[k 2, k 5]))
-- A wrong virtual value breaks the external relation, nothing else.
#guard !decide (squares.Satisfied squaresLayout
  (setRow squaresWitness 1 0 ((squareRow 3).push (k 7))))

#guard program.buses = ["code"]
#guard decide (program.Satisfied programLayout programWitness)
-- A wrong final count unbalances the bus.
#guard !decide (program.Satisfied programLayout (setRow programWitness 0 0 #[g]))
-- The unread program slot is pulled back at count one.
#guard !decide (program.Satisfied programLayout (setRow programWitness 0 3 #[k 99]))
-- A padding row must still satisfy the constraint.
#guard !decide (program.Satisfied programLayout (setRow programWitness 1 6 #[k 0, k 11, 0]))
-- A padding row may carry any data that does.
#guard decide (program.Satisfied programLayout (setRow programWitness 1 6 (executionRow 3 0)))
/-- Six executed rows: the sixth reads and returns `(0, op, 0)`, which balances. -/
def sixRows : Layout program.tables.length :=
  ⟨fun t => [4, 6].getD t.val 0, fun t => [2, 3].getD t.val 0⟩

-- A zero count on an executed row breaks the nonzero column, with the bus balanced.
#guard decide (∀ b ∈ program.buses,
  program.tuples sixRows programWitness b true = program.tuples sixRows programWitness b false)
#guard !decide (program.Satisfied sixRows programWitness)

end CompStarkTests.Tables
