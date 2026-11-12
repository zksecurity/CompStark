/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStarkFixtures.TablesKeccak

/-! The `hashes` system through the composed honest prover, with the native Keccak-f GKR for its
virtual output lanes, and the fast verifier, compiled: the honest transcript is accepted; a
transcript whose witness has a wrong output lane in both tables, so that the bus balances, is
rejected by the GKR; and a transcript of an unbalanced witness is rejected. -/

@[expose] public section
namespace CompStarkTests.TablesKeccak
open CompStark.Tables CompStark.Tables.Composed CompStark.BinaryFields CompStark.Fixtures.TablesKeccak

/-- Replace cell `c` of row `i` of table `t`. -/
def setCell {n : ℕ} (w : Witness K n) (t i c : ℕ) (x : K) : Witness K n :=
  fun s ↦ if s.val = t then (w s).modify i fun row ↦ row.set! c x else w s

/-- Run the honest, wrong-output and unbalanced transcripts through the fast verifier. -/
def check : IO Unit := do
  let start ← IO.monoMsNow
  unless hashesVerify (hashesProof hashesWitness) do
    throw (IO.userError "tables: the honest hashes transcript is rejected")
  let honest ← IO.monoMsNow
  let wrong := setCell (setCell hashesWitness 0 2 64 (word 7)) 1 2 25 (word 7)
  if hashesVerify (hashesProof wrong) then
    throw (IO.userError "tables: a wrong virtual output lane is accepted")
  let unbalanced := setCell hashesWitness 1 3 0 (word 7)
  if hashesVerify (hashesProof unbalanced) then
    throw (IO.userError "tables: an unbalanced hashes witness is accepted")
  let stop ← IO.monoMsNow
  IO.println s!"tables (Keccak): honest accepted in {honest - start} ms; wrong output lane and unbalanced bus rejected; total {stop - start} ms"

end CompStarkTests.TablesKeccak
