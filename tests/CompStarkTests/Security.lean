/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Security

/-! # The security calculator

The reports of the concrete setups and statements, the analyses of `CompStark/Security.lean` as
the ones the search (`bestAnalysis`, `bestAnalysisRo`) finds, a check on an AIR of `4096`
constraints in the kernel, and the calculator theorems' axioms.
-/

namespace CompStarkTests.Security
open CompStark CompStark.Iop CompStark.Stark

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize

/-- The interactive statements at their longest admitted lengths, where their errors are
largest. -/
def fibonacci20 : Setup KoalaBear.Fast.Ext4 := fibonacciStatement.setupOf _ 20 (by decide +kernel)
def wide22 : Setup KoalaBear.Fast.Ext4 := wideStatement.setupOf _ 22 (by decide +kernel)
def wide5i22 : Setup KoalaBear.Fast.Ext5 := wide5iStatement.setupOf _ 22 (by decide +kernel)

/-- A report reaches between `lo` and `hi` bits in total, the analysis fitting. -/
def within (r : Report) (lo hi : Float) : Bool := r.fits && lo ≤ r.total && r.total < hi

#guard within (fibonacci20.knowledgeErrorReport 2130706433 .uniqueDecoding fibonacciAnalysis)
  98.95 98.96
#guard within (wide22.knowledgeErrorReport 2130706433 .uniqueDecoding wideAnalysis)
  98.70 98.71
#guard within (wide5i22.knowledgeErrorReport 2130706433 .uniqueDecoding wide5iAnalysis)
  128.21 128.22
#guard within (wideSp1Setup.roundErrorReport 2130706433 .uniqueDecoding wideSp1Analysis) 99.95 99.96
#guard within (wideGrindSetup.roundErrorReport 2130706433 .uniqueDecoding wideGrindAnalysis) 117.37 117.38
#guard within (wide5Setup.roundErrorReport 2130706433 .uniqueDecoding wide5Analysis) 128.49 128.50
#guard within (wideBatchStatement.knowledgeErrorReport KoalaBear.Fast.Ext5 2130706433
  .uniqueDecoding wideBatchAnalysis) 127.10 127.11
#guard within (wideBatch5Statement.roundErrorReport KoalaBear.Fast.Ext5 2130706433 .uniqueDecoding
  wideBatch5Analysis) 128.03 128.04
#guard within (wideBatchGrindStatement.roundErrorReport KoalaBear.Fast.Ext4 2130706433
  .uniqueDecoding wideBatchGrindAnalysis) 115.04 115.05
-- The analyses are the ones the search finds, the statements' at their longest admitted length.
#guard fibonacci20.bestAnalysis 2130706433 .uniqueDecoding = fibonacciAnalysis
#guard wide22.bestAnalysis 2130706433 .uniqueDecoding = wideAnalysis
#guard wide5i22.bestAnalysis 2130706433 .uniqueDecoding = wide5iAnalysis
#guard wideSp1Setup.bestAnalysisRo 2130706433 .uniqueDecoding = wideSp1Analysis
#guard wideGrindSetup.bestAnalysisRo 2130706433 .uniqueDecoding = wideGrindAnalysis
#guard wide5Setup.bestAnalysisRo 2130706433 .uniqueDecoding = wide5Analysis
-- The extractor beyond the unique-decoding radius `3/8` fits up to the Johnson radius `1/2`.
#guard (wide22.knowledgeErrorReport 2130706433 .uniqueDecoding
  ⟨3 / 8 - 1 / 2 ^ 12, 3 / 8, 1 / 2 ^ 17⟩).fits
#guard !(wide22.knowledgeErrorReport 2130706433 .uniqueDecoding
  ⟨3 / 8 - 1 / 2 ^ 12, 1 / 2, 1 / 2 ^ 17⟩).fits
-- FRI's radius beyond the unique-decoding radius does not fit.
#guard !(wide22.knowledgeErrorReport 2130706433 .uniqueDecoding
  ⟨3 / 8 + 1 / 2 ^ 12, 7 / 16, 1 / 2 ^ 17⟩).fits

/-- The kernel runs the search itself. -/
example :
    wide22.Secure 2130706433 .uniqueDecoding
      (wide22.bestAnalysis 2130706433 .uniqueDecoding) 98 := by
  decide +kernel

/-- `wide 4096` on `2 ^ 20` rows over the quintic extension with `wide5iParams`. -/
def wide4096Setup : Setup KoalaBear.Fast.Ext5 where
  params := wide5iParams
  air := wide 4096
  logN := 20
  valid := (wide_valid wide5iParams rfl (by decide) rfl (by decide) 4096 (by decide) 20
    (by decide)).sound


set_option maxRecDepth 100000 in
/-- The kernel evaluates the `4096` constraints' degrees, about `2 ^ (-127.81)`; the lists of
constraints recurse deeper than the default depth. -/
example : wide4096Setup.Secure 2130706433 .uniqueDecoding wide5iAnalysis 127 := by decide +kernel

/-- info: 'CompStark.Iop.knowledgeSoundness_of_secure' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms knowledgeSoundness_of_secure

/-- info: 'CompStark.Iop.knowledgeSoundness_ro_of_secureRo' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms knowledgeSoundness_ro_of_secureRo

/-- info: 'CompStark.Iop.batchKnowledgeSoundness_of_secure' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batchKnowledgeSoundness_of_secure

/-- info: 'CompStark.Iop.Batch.batchKnowledgeSoundness_ro_of_secureRo' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Batch.batchKnowledgeSoundness_ro_of_secureRo

/-- info: 'CompStark.Iop.wideBatchGrind_knowledgeSoundness_ro' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wideBatchGrind_knowledgeSoundness_ro

/-- info: 'CompStark.Iop.Batch.Statement.roundError_le_of_secureRo' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Batch.Statement.roundError_le_of_secureRo

/-- info: 'CompStark.Iop.Batch.Statement.secureRo_setupAt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Batch.Statement.secureRo_setupAt

/-- info: 'CompStark.Iop.Statement.knowledgeError_le_of_secure' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Statement.knowledgeError_le_of_secure

/-- info: 'CompStark.Iop.Batch.Statement.knowledgeError_le_of_secure' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Batch.Statement.knowledgeError_le_of_secure

/-- info: 'CompStark.Iop.Batch.Statement.secure_setupAt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Batch.Statement.secure_setupAt

/-- info: 'CompStark.Sound.McaBound.uniqueOrJohnson_holds' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.McaBound.uniqueOrJohnson_holds

end CompStarkTests.Security
