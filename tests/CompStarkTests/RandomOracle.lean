/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Ni.Parse
import CompStark.Ni.Setup
import CompStark.Security
import CompStark.BatchNonInteractive
import CompStark.LookupInclusion

/-! Axiom guards for the random-oracle model: the verifier's query bound, the verifier on answer
tables, parsing its rounds, the setup on answer tables, and knowledge soundness, of the STARK and
of the batch STARK. -/

namespace CompStarkTests.RandomOracle

/-- info: 'CompStark.Stark.verifyWith_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Stark.verifyWith_map

/-- info: 'CompStark.RandomOracle.evalWithAnswerFn_verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.RandomOracle.evalWithAnswerFn_verifyWith

/-- info: 'CompStark.RandomOracle.tableQueryLog_verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.RandomOracle.tableQueryLog_verifyWith

/-- info: 'CompStark.Iop.Setup.isTotalQueryBound_verifyRo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Setup.isTotalQueryBound_verifyRo

/-- info: 'CompStark.Ni.parse_keyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.parse_keyAt

/-- info: 'CompStark.Ni.parse_verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.parse_verifyWith

/-- info: 'CompStark.Iop.Setup.isTotalQueryBound_setupRo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Setup.isTotalQueryBound_setupRo

/-- info: 'CompStark.Ni.evalWithAnswerFn_setupRo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.evalWithAnswerFn_setupRo

/-- info: 'CompStark.Ni.exists_root_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.exists_root_mem

/-- info: 'CompStark.Ni.committedColumn_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.committedColumn_setup

/-- info: 'CompStark.Iop.knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.knowledgeSoundness_ro

/-- info: 'CompStark.Iop.wideSp1_knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideSp1_knowledgeSoundness_ro

/-- info: 'CompStark.Iop.wide5_knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5_knowledgeSoundness_ro

/-- info: 'CompStark.Iop.wideSp1Setup_verifierQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideSp1Setup_verifierQueries

/-- info: 'CompStark.Iop.wide5Setup_verifierQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5Setup_verifierQueries

/-- info: 'CompStark.Iop.wideGrind_knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideGrind_knowledgeSoundness_ro

/-- info: 'CompStark.Iop.wideGrindSetup_verifierQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideGrindSetup_verifierQueries

/-- info: 'CompStark.Batch.verifyBatchWith_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Batch.verifyBatchWith_map

/-- info: 'CompStark.RandomOracle.evalWithAnswerFn_verifyBatchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.RandomOracle.evalWithAnswerFn_verifyBatchWith

/-- info: 'CompStark.Iop.Batch.Setup.isTotalQueryBound_verifyBatchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.Setup.isTotalQueryBound_verifyBatchWith

/-- info: 'CompStark.Iop.Batch.Setup.isTotalQueryBound_setupRo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.Setup.isTotalQueryBound_setupRo

/-- info: 'CompStark.Ni.hasRounds_verifyBatchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.hasRounds_verifyBatchWith

/-- info: 'CompStark.Ni.bcsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.bcsB

/-- info: 'CompStark.Ni.matColumn_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.matColumn_setup

/-- info: 'CompStark.Ni.exists_badAtB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.exists_badAtB

/-- info: 'CompStark.Iop.Batch.batchKnowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.batchKnowledgeSoundness_ro

/-- info: 'CompStark.Iop.Batch.batchKnowledgeSoundness_ro_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.batchKnowledgeSoundness_ro_inclusion

/-- info: 'CompStark.Iop.rangeKnowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.rangeKnowledgeSoundness_ro

/-- info: 'CompStark.Iop.wideBatch5_knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideBatch5_knowledgeSoundness_ro

/-- info: 'CompStark.Iop.wideBatchGrind_knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideBatchGrind_knowledgeSoundness_ro

end CompStarkTests.RandomOracle
