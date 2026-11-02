/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Ni.Parse
import CompStark.Ni.Setup
import CompStark.Security
import CompStark.LookupInclusion

/-! Axiom guards for the verifier on its random oracles: naturality in its primitives, its query
bounds, the trace lengths of accepted proofs, the setup on answer tables, BCS consistency, and the
range check on Plonky3's batch verifier, of the STARK and of the batch STARK. -/

namespace CompStarkTests.RandomOracle

/-- info: 'CompStark.Stark.verifyWith_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Stark.verifyWith_map

/-- info: 'CompStark.Iop.Setup.isTotalQueryBound_verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Setup.isTotalQueryBound_verifyWith

/-- info: 'CompStark.DomainSeparator.starkSeedOf_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.DomainSeparator.starkSeedOf_inj

/-- info: 'CompStark.Iop.Statement.admits_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Statement.admits_of_ok

/-- info: 'CompStark.Ni.committedColumn_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.committedColumn_setup

/-- info: 'CompStark.Iop.wideSp1Statement_verifierQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideSp1Statement_verifierQueries

/-- info: 'CompStark.Iop.wide5Statement_verifierQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5Statement_verifierQueries

/-- info: 'CompStark.Iop.wideGrindStatement_verifierQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideGrindStatement_verifierQueries

/-- info: 'CompStark.Batch.verifyBatchWith_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Batch.verifyBatchWith_map

/-- info: 'CompStark.Iop.Batch.Statement.isTotalQueryBound_verifyBatchWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.Statement.isTotalQueryBound_verifyBatchWith

/-- info: 'CompStark.Iop.Batch.Statement.isTotalQueryBound_commonWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.Statement.isTotalQueryBound_commonWith

/-- info: 'CompStark.Ni.bcsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.bcsB

/-- info: 'CompStark.Ni.matColumn_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Ni.matColumn_setup

/-- info: 'CompStark.Iop.Batch.Statement.admits_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.Statement.admits_of_ok

/-- info: 'CompStark.Iop.Batch.Statement.rangeKnowledgeSoundness_bcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Batch.Statement.rangeKnowledgeSoundness_bcs

/-- info: 'CompStark.Iop.wideBatch5Statement_verifierQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideBatch5Statement_verifierQueries_le

/-- info: 'CompStark.Iop.wideBatchGrindStatement_verifierQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideBatchGrindStatement_verifierQueries_le

end CompStarkTests.RandomOracle
