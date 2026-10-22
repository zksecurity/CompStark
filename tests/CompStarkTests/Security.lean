/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Security

/-! # The security calculator

The reports of the concrete setups, a check on an AIR of `4096` constraints in the kernel, and
the calculator theorems' axioms.
-/

namespace CompStarkTests.Security
open CompStark CompStark.Iop CompStark.Stark

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize

/-- A report reaches between `lo` and `hi` bits in total, the analysis fitting. -/
def within (r : Report) (lo hi : Float) : Bool := r.fits && lo ≤ r.total && r.total < hi

#guard within (fibonacciSetup.knowledgeErrorReport 2130706433 fibonacciAnalysis) 100.29 100.30
#guard within (wideSetup.knowledgeErrorReport 2130706433 wideAnalysis) 100.26 100.27
#guard within (wide5iSetup.knowledgeErrorReport 2130706433 wide5iAnalysis) 128.58 128.59
#guard within (wideSp1Setup.roundErrorReport 2130706433 wideSp1Analysis) 100.07 100.08
#guard within (wideGrindSetup.roundErrorReport 2130706433 wideGrindAnalysis) 117.10 117.11
#guard within (wideBatchSetup.knowledgeErrorReport 2130706433 wide5iAnalysis) 128.39 128.40
#guard within (wideBatchGrindSetup.roundErrorReport 2130706433 wideGrindAnalysis) 117.11 117.12
-- `δ'` at the unique-decoding radius does not fit.
#guard !(wideSetup.knowledgeErrorReport 2130706433 ⟨3 / 8 - 1 / 2 ^ 12, 3 / 8, 1 / 2 ^ 17, 16⟩).fits

/-- `wide 4096` on `2 ^ 20` rows over the quintic extension with `wide5iParams`. -/
def wide4096Setup : Setup KoalaBear.Fast.Ext5 where
  params := wide5iParams
  air := wide 4096
  logN := 20
  valid := wide_valid wide5iParams rfl (by decide) rfl (by decide) 4096 (by decide) 20
    (by decide)
  folds := by decide

set_option maxRecDepth 100000 in
/-- The kernel evaluates the `4096` constraints' degrees, about `2 ^ (-127.81)`; the lists of
constraints recurse deeper than the default depth. -/
example : wide4096Setup.Secure 2130706433 wide5iAnalysis 127 := by decide +kernel

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

end CompStarkTests.Security
