/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Stark.Verifier

/-! # STARK known answers

Plonky3 `uni-stark` proofs of the Fibonacci AIR over KoalaBear (`bench/rust:
RAYON_NUM_THREADS=1 compstark-bench stark LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES
COMMIT_POW QUERY_POW`), saved as `tests/data/fib_*.json`, must verify.
-/

namespace CompStarkTests.Stark
open CompStark CompStark.Stark

local notation "F" => _root_.KoalaBear.Fast.Field

/-- The public values of the Fibonacci trace of `n` rows from `(0, 1)`: `0, 1` and its last right
value. -/
def fibPublic (n : Nat) : List F :=
  let (_, r) := (List.range (n - 1)).foldl (fun ((l, r) : F × F) _ ↦ (r, l + r)) (0, 1)
  [0, 1, r]

/-- Verify the saved proof for parameters `logN logBlowup logFinal maxLogArity queries commitPow
queryPow`. -/
def verifyFile (ps : List Nat) : IO Unit := do
  let [logN, b, f, a, q, cp, qp] := ps | throw (IO.userError "seven parameters")
  let name := "_".intercalate (ps.map toString)
  let s ← IO.FS.readFile s!"tests/data/fib_{name}.json"
  let proof ← IO.ofExcept (Json.parse s)
  match verify ⟨b, f, a, q, cp, qp⟩ fibonacci proof (fibPublic (2 ^ logN)) with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"fib_{name}: {e}")

#eval do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [3, 2, 2, 1, 2, 1, 1], [6, 1, 0, 1, 10, 0, 8],
      [6, 1, 1, 3, 8, 2, 4], [5, 2, 0, 2, 5, 0, 0]] do
    verifyFile ps

end CompStarkTests.Stark
