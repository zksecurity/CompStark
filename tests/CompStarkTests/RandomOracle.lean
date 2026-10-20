/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Ni.Parse

/-! Axiom guards for the random-oracle model: the verifier's query bound, the verifier on answer
tables, and parsing its rounds. -/

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

end CompStarkTests.RandomOracle
