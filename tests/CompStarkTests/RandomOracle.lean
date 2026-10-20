/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Ni.Parse
import CompStark.Security

/-! Axiom guards for the random-oracle model: the verifier's query bound, the verifier on answer
tables, parsing its rounds, and knowledge soundness. -/

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

/-- info: 'CompStark.Iop.knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.knowledgeSoundness_ro

/-- info: 'CompStark.Iop.wideSp1_knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideSp1_knowledgeSoundness_ro

/-- info: 'CompStark.Iop.wide5_knowledgeSoundness_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5_knowledgeSoundness_ro

end CompStarkTests.RandomOracle
