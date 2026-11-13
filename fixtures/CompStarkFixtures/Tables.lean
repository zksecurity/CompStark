/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Verifier
public import CompStark.Tables.Examples
public import CompStark.Pcs.WordEncoding
public import CompStark.Pcs.EvaluatedLadder
public import CompStark.Pcs.Multiplicity
public import CompStark.Tables.Compiled.Prover
public import CompStark.Tables.Compiled.Completeness

/-! The `program` system as a composed proof system: its setup, a small opening schedule and fixed
verifier coins, for the tests and the performance gate. -/

@[expose] public section
namespace CompStark.Fixtures.Tables
open CompStark.Tables CompStark.Tables.Examples CompStark.Tables.Composed CompStark.BinaryFields
open CompStark.Multilinear

/-- Distinct challenge-field values, computed. -/
def valueSpec (n : ℕ) : E := ofK (gpow n) + ofK (gpow (n + 7)) * ofK g

/-- The first 256 values, computed once. -/
def values : Array E := Array.ofFn fun i : Fin 256 ↦ valueSpec i.val

/-- Distinct challenge-field values, read from the table below 256. -/
def value (n : ℕ) : E := if n < 256 then values[n]! else valueSpec n

/-- The bus's tuples: the separator and three entries. -/
def width : String → ℕ := fun _ ↦ 3

/-- The program's buses have one width and fit four entries. -/
theorem programShape : program.BusShape 2 width := by decide

/-- The program's stack fits five variables. -/
theorem programFits : (program.stackBlocks programLayout).total ≤ 2 ^ 5 := by
  rw [System.stackBlocks_total]
  decide

/-- The program's composed setup: no virtual columns, no external relation. -/
def programSetup : Setup program programLayout 2 5 where
  width := width
  wellFormed := program_wellFormed
  busShape := programShape
  fits := programFits
  boundary := by decide
  degree_le := by decide
  external := External.none program programLayout 2 5 programFits (by decide) (fun _ ↦ trivial)

/-- The program's external honest prover: an empty transcript. -/
def programHonest : programSetup.external.Honest :=
  External.none.honest program programLayout 2 5 programFits (by decide) (fun _ ↦ trivial)

/-- A four-variable terminal table after one folded coordinate. -/
def schedule : CompStark.Pcs.EvaluatedSchedule 5 := .last 1 4 (CompStark.Pcs.evaluatedEncoding 4 1 (by decide)) 3

/-- Fixed verifier coins. -/
def coins : Coins (S := program) (L := programLayout) (k := 2) schedule.schedule where
  bus := ((fun i ↦ value (i.val + 1), value 3), GrandProduct.Coins.fill (fun n ↦ value (n + 11)) _ 0 0)
  table := (value 5, fun i ↦ value (i.val + 41))
  opening := (value 61, fun _ ↦ value 67, fun i ↦ ⟨i.val, by change i.val < 32; omega⟩, value 73,
    fun i ↦ value (i.val + 79))

/-- The honest transcript of a witness of the program. -/
def programProof (w : Witness K program.tables.length) :
    (composedProtocol programSetup schedule.schedule).tree.ExecutionPath :=
  honestPath programSetup schedule.schedule (fun o q ↦ programHonest.honest o q PUnit.unit) w coins

/-- The fast verifier on a transcript of the program. -/
def programVerify (path : (composedProtocol programSetup schedule.schedule).tree.ExecutionPath) : Bool :=
  verifyWith programSetup schedule path

/-- The duplex's initialization vector of the fixtures. -/
def iv : CompStark.Keccak.Commit.Digest := Vector.replicate 32 1

/-- The statement digest of the fixtures. -/
def statement : CompStark.Keccak.Commit.Digest := Vector.replicate 32 2

/-- The program's certified opening: one folded coordinate, then a four-variable last level. -/
def programLadder : CompStark.Pcs.CertifiedEvaluated 5 1 :=
  CompStark.Pcs.evaluatedLadder CompStark.Pcs.productionChoices (fun _ ↦ 3) 5 1 1
    (by decide) (by decide) (by decide) (by decide)

/-- The program's compiled verifier data. -/
def programData : Compiled.Data program programLayout 2 5 :=
  ⟨programSetup, programLadder.evaluated, .done, iv, statement⟩

/-- The program's compiled parameters. -/
noncomputable def programParams : Compiled.Parameters program programLayout 2 5 where
  toSetup := programSetup
  evaluated := programLadder.evaluated
  johnson := programLadder.johnson
  valid := programLadder.valid
  decoder := programLadder.decoder
  correct := programLadder.correct
  decoders := programLadder.decoders
  familyCorrect := programLadder.familyCorrect
  reductions := External.none.reductions program programLayout 2 5 programFits (by decide) (fun _ ↦ trivial)
  externalPresentation := .done
  externalUnannounced := trivial
  externalShapes := rfl
  externalFramed := trivial
  externalCount := 0
  externalCounted := rfl
  iv := iv
  statement := statement

/-- The parameters' verifier data is the program's. -/
theorem programParams_data : programParams.data = programData := rfl

/-- The honest compiled proof of a witness of the program. -/
def programCompiledProof (w : Witness K program.tables.length) : Option programData.Proof :=
  programData.prove (fun _ _ ↦ PUnit.unit) w

/-- Every compiled proof the honest prover produces for a satisfying, padded program witness is
accepted. -/
theorem programCompiled_complete (w : Witness K program.tables.length) (hsat : program.Satisfied programLayout w)
    (padded : program.Padded programLayout w) (proof : programData.Proof)
    (proved : programCompiledProof w = some proof) : Compiled.verify programParams proof :=
  Compiled.completeness programParams programHonest (fun _ _ ↦ PUnit.unit)
    (fun _ _ _ _ _ _ _ _ ↦ ⟨PUnit.unit, rfl⟩) (by decide +kernel) w hsat padded proof proved

end CompStark.Fixtures.Tables
