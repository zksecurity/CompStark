/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Security

/-! # The security calculator

The reports of the concrete setups, the analyses of `CompStark/Security.lean` as the ones the
search (`bestAnalysis`, `bestAnalysisRo`) finds, a check on an AIR of `4096` constraints in the
kernel, and the calculator theorems' axioms.
-/

namespace CompStarkTests.Security
open CompStark CompStark.Iop CompStark.Stark

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize

/-- A report reaches between `lo` and `hi` bits in total, the analysis fitting. -/
def within (r : Report) (lo hi : Float) : Bool := r.fits && lo ≤ r.total && r.total < hi

#guard within (fibonacciSetup.knowledgeErrorReport 2130706433 .uniqueDecoding fibonacciAnalysis) 100.36 100.37
#guard within (wideSetup.knowledgeErrorReport 2130706433 .uniqueDecoding wideAnalysis) 100.16 100.17
#guard within (wide21Setup.knowledgeErrorReport 2130706433 .uniqueDecoding wide21Analysis) 99.50 99.51
#guard within (wide5iSetup.knowledgeErrorReport 2130706433 .uniqueDecoding wide5iAnalysis) 128.46 128.47
#guard within (wideSp1Setup.roundErrorReport 2130706433 .uniqueDecoding wideSp1Analysis) 99.95 99.96
#guard within (wideGrindSetup.roundErrorReport 2130706433 .uniqueDecoding wideGrindAnalysis) 117.37 117.38
#guard within (wide5Setup.roundErrorReport 2130706433 .uniqueDecoding wide5Analysis) 128.49 128.50
#guard within (wideBatchSetup.knowledgeErrorReport 2130706433 .uniqueDecoding wide5iAnalysis) 128.33 128.34
#guard within (wideBatch5Statement.roundErrorReport KoalaBear.Fast.Ext5 2130706433 .uniqueDecoding
  wideBatch5Analysis) 128.03 128.04
#guard within (wideBatchGrindStatement.roundErrorReport KoalaBear.Fast.Ext4 2130706433
  .uniqueDecoding wideBatchGrindAnalysis) 115.04 115.05
-- The analyses are the ones the search finds.
#guard fibonacciSetup.bestAnalysis 2130706433 .uniqueDecoding = fibonacciAnalysis
#guard wideSetup.bestAnalysis 2130706433 .uniqueDecoding = wideAnalysis
#guard wide21Setup.bestAnalysis 2130706433 .uniqueDecoding = wide21Analysis
#guard wide5iSetup.bestAnalysis 2130706433 .uniqueDecoding = wide5iAnalysis
#guard wideSp1Setup.bestAnalysisRo 2130706433 .uniqueDecoding = wideSp1Analysis
#guard wideGrindSetup.bestAnalysisRo 2130706433 .uniqueDecoding = wideGrindAnalysis
#guard wide5Setup.bestAnalysisRo 2130706433 .uniqueDecoding = wide5Analysis
#guard wideBatchSetup.bestAnalysis 2130706433 .uniqueDecoding = wide5iAnalysis
-- The extractor beyond the unique-decoding radius `3/8` fits up to the Johnson radius `1/2`.
#guard (wideSetup.knowledgeErrorReport 2130706433 .uniqueDecoding ⟨3 / 8 - 1 / 2 ^ 12, 3 / 8, 1 / 2 ^ 17⟩).fits
#guard !(wideSetup.knowledgeErrorReport 2130706433 .uniqueDecoding ⟨3 / 8 - 1 / 2 ^ 12, 1 / 2, 1 / 2 ^ 17⟩).fits
-- FRI's radius beyond the unique-decoding radius does not fit.
#guard !(wideSetup.knowledgeErrorReport 2130706433 .uniqueDecoding ⟨3 / 8 + 1 / 2 ^ 12, 7 / 16, 1 / 2 ^ 17⟩).fits

/-- The kernel runs the search itself. -/
example : wideSetup.Secure 2130706433 .uniqueDecoding (wideSetup.bestAnalysis 2130706433 .uniqueDecoding) 100 := by
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

/-- info: 'CompStark.Sound.McaBound.uniqueOrJohnson_holds' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.McaBound.uniqueOrJohnson_holds

end CompStarkTests.Security
