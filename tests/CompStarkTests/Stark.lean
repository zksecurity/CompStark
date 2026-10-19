/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Stark.Prover
import CompStark.Completeness
import CompStark.Soundness
import CompStark.Security

/-! # STARK known answers

Plonky3 `uni-stark` proofs over KoalaBear (`bench/rust: RAYON_NUM_THREADS=1 compstark-bench stark
AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW`), saved as
`tests/data/AIR_*.json`, for the Fibonacci AIR and the degree-3 `cube` AIR. Each must verify, and
the Lean prover must reproduce it exactly from the same trace.

Lake does not track the data files: check a replaced proof with
`lake env lean tests/CompStarkTests/Stark.lean`.
-/

namespace CompStarkTests.Stark
open CompStark CompStark.Stark

local notation "F" => _root_.KoalaBear.Fast.Field

/-- The Fibonacci trace of `n` rows from `(0, 1)` and its public values. -/
def fibInstance (n : Nat) : Array F × List F :=
  let (t, _, r) := (List.range n).foldl (fun ((t, l, r) : Array F × F × F) _ ↦
    (t.push l |>.push r, r, l + r)) (#[], 0, 1)
  (t, [0, 1, t.getD (2 * n - 1) r])

/-- The `cube` trace of `n` rows from `(2, 0)` and its public values. -/
def cubeInstance (n : Nat) : Array F × List F :=
  let (t, _, _) := (List.range n).foldl (fun ((t, x, y) : Array F × F × F) _ ↦
    (t.push x |>.push y, x * x * x + y, y + 1)) (#[], 2, 0)
  (t, [2, 0, t.getD (2 * n - 2) 0])

/-- Verify and reproduce the saved proof of `air` for parameters `logN logBlowup logFinal
maxLogArity queries commitPow queryPow`. -/
def check (name : String) (A : Air) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit := do
  let [logN, b, f, a, q, cp, qp] := ps | throw (IO.userError "seven parameters")
  let file := s!"{name}_{"_".intercalate (ps.map toString)}"
  let rust ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/data/{file}.json"))
  let P : Fri.Params := ⟨b, f, a, q, cp, qp⟩
  let (trace, pis) := inst (2 ^ logN)
  if let .error e := verify P A rust pis then throw (IO.userError s!"{file}: {e}")
  unless prove P A logN trace pis == rust do throw (IO.userError s!"{file}: proofs differ")

#eval do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [3, 2, 2, 1, 2, 1, 1], [6, 1, 0, 1, 10, 0, 8],
      [6, 1, 1, 3, 8, 2, 4], [5, 2, 0, 2, 5, 0, 0]] do
    check "fib" fibonacci fibInstance ps
  for ps in [[4, 2, 0, 1, 4, 0, 0], [5, 3, 1, 2, 6, 1, 3]] do
    check "cube" cube cubeInstance ps

end CompStarkTests.Stark

/-- info: 'CompStark.Stark.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Stark.completeness

/-- info: 'CompStark.Iop.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.knowledgeSoundness

/-- info: 'CompStark.Iop.fibonacci_knowledgeError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.fibonacci_knowledgeError_le
