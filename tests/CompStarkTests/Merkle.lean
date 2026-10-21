/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Merkle.RootCorrectness
import CompStark.Merkle.Extract

/-! # Merkle axioms

The Merkle trees' known answers run compiled (`CompStarkNativeTests`), on the packed kernels.
-/

/-- info: 'CompStark.Merkle.Packed.root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Merkle.Packed.root_eq

/-- info: 'CompStark.Merkle.extractRow_eq_of_verifyBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Merkle.extractRow_eq_of_verifyBatch

/-- info: 'CompStark.Merkle.extractRow_eq_of_noPrediction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Merkle.extractRow_eq_of_noPrediction

