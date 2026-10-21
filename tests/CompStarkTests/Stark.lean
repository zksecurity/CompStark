/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Plonky3.Prover
import CompStark.KoalaBear.Poseidon2
import CompStark.Mont32.Json
import CompStark.Completeness
import CompStark.Soundness
import CompStark.Security
import CompStark.Sound.Rbr

/-! # STARK known answers

Plonky3 `uni-stark` proofs over KoalaBear (`bench/rust: RAYON_NUM_THREADS=1 compstark-bench stark
AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW`), saved as
`tests/data/AIR_*.json`, for the Fibonacci AIR and the degree-3 `cube` AIR. Each must verify, and
the Lean prover must reproduce it exactly from the same trace. Over the quintic extension, the
Lean prover's own proofs must verify.

Lake does not track the data files: check a replaced proof with
`lake env lean tests/CompStarkTests/Stark.lean`.
The interpreter cannot run KoalaBear's packed kernels (CompPoly's inline C stores), so these
checks run Plonky3's primitives on the specification implementation, a local instance;
`KoalaBear.perm16_eq` and `perm24_eq` prove the packed kernels equal to it.
-/

namespace CompStarkTests.Stark
open CompStark CompStark.Stark

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "EF" => _root_.KoalaBear.Fast.Ext4

/-- The specification implementation of KoalaBear's instances, which the interpreter runs. -/
local instance (priority := high) specPoseidon2 : CompStark.Poseidon2Field F :=
  .ofSpec (CompStark.Poseidon2.KoalaBear.width16 _) (CompStark.Poseidon2.KoalaBear.width24 _)

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
def check (name : String) (A : Air F) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit :=
    do
  let [logN, b, f, a, q, cp, qp] := ps | throw (IO.userError "seven parameters")
  let file := s!"{name}_{"_".intercalate (ps.map toString)}"
  let rust : Proof F EF ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/data/{file}.json"))
  let P : Fri.Params := ⟨b, f, a, q, cp, qp⟩
  let (trace, pis) := inst (2 ^ logN)
  if let .error e := verify P A rust pis then throw (IO.userError s!"{file}: {e}")
  unless prove EF P A logN trace pis == rust do throw (IO.userError s!"{file}: proofs differ")

#eval do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [3, 2, 2, 1, 2, 1, 1], [6, 1, 0, 1, 10, 0, 8],
      [6, 1, 1, 3, 8, 2, 4], [5, 2, 0, 2, 5, 0, 0]] do
    check "fib" fibonacci fibInstance ps
  for ps in [[4, 2, 0, 1, 4, 0, 0], [5, 3, 1, 2, 6, 1, 3]] do
    check "cube" cube cubeInstance ps

/-- Prove `air` over the quintic extension `Fast.Ext5` for parameters `logN logBlowup logFinal
maxLogArity queries commitPow queryPow`: the verifier accepts the proof, and rejects it for other
public values. -/
def checkExt5 (A : Air F) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit := do
  let [logN, b, f, a, q, cp, qp] := ps | throw (IO.userError "seven parameters")
  let P : Fri.Params := ⟨b, f, a, q, cp, qp⟩
  let (trace, pis) := inst (2 ^ logN)
  let proof := prove _root_.KoalaBear.Fast.Ext5 P A logN trace pis
  if let .error e := verify P A proof pis then throw (IO.userError s!"Ext5 {ps}: {e}")
  if let .ok () := verify P A proof (pis.map (· + 1)) then
    throw (IO.userError s!"Ext5 {ps}: accepted wrong public values")

#eval do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [5, 2, 0, 2, 5, 0, 3]] do
    checkExt5 fibonacci fibInstance ps
  checkExt5 cube cubeInstance [4, 2, 0, 1, 4, 1, 2]

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

/-- info: 'CompStark.Iop.wide_knowledgeError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide_knowledgeError_le

/-- info: 'CompStark.Iop.wide21_knowledgeError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide21_knowledgeError_le

/-- info: 'CompStark.Iop.wideSp1_roundError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideSp1_roundError_le

/-- info: 'CompStark.Iop.wide5_roundError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5_roundError_le

/-- info: 'CompStark.Iop.wide5i_knowledgeError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5i_knowledgeError_le

/-- info: 'CompStark.Iop.wide5i_knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5i_knowledgeSoundness

/-- info: 'CompStark.Sound.exists_satisfied_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.exists_satisfied_of_safe

/-- info: 'CompStark.Sound.prob_alphaBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_alphaBad_le

/-- info: 'CompStark.Sound.prob_zetaBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_zetaBad_le

/-- info: 'CompStark.Sound.prob_batchBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_batchBad_le

/-- info: 'CompStark.Sound.prob_foldRound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_foldRound_le

/-- info: 'CompStark.Sound.prob_queryBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_queryBad_le
