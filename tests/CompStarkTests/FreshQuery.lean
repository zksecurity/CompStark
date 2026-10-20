/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Fs.DigestClash

/-! Axiom guards for the fresh bad-query bounds. -/

namespace CompStarkTests.FreshQuery

/-- info: 'OracleComp.prEvent_exists_fresh_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OracleComp.prEvent_exists_fresh_bad_le

/-- info: 'OracleComp.prEvent_exists_fresh_digestClash_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OracleComp.prEvent_exists_fresh_digestClash_le

end CompStarkTests.FreshQuery
