/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Completeness
import CompStark.Soundness
import CompStark.Security
import CompStark.LookupInclusion
import CompStark.Sound.Rbr
import CompStark.KoalaBear.Fast
import CompStark.KoalaBear.Completeness

/-! # STARK axioms

The STARK known answers run compiled (`CompStarkNativeTests`), on the packed kernels.
-/

/-- info: 'CompStark.Stark.completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CompStark.Stark.completeness

/-- info: 'CompStark.KoalaBear.completeness' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.KoalaBear.completeness

/-- info: 'CompStark.Batch.completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CompStark.Batch.completeness

/-- info: 'CompStark.KoalaBear.batchCompleteness' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.KoalaBear.batchCompleteness

/-- info: 'CompStark.Stark.Fast.prove_fast' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Stark.Fast.prove_fast

/-- info: 'CompStark.KoalaBear.prove_fast' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.KoalaBear.prove_fast

/-- info: 'CompStark.KoalaBear.proveBatch_fast' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.KoalaBear.proveBatch_fast

/-- info: 'CompStark.Lookup.logUpConstraints_honest' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Lookup.logUpConstraints_honest

/-- info: 'CompStark.Batch.terminals_sum_eq_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Batch.terminals_sum_eq_zero

/-- info: 'CompStark.Batch.instanceCheck_honest' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Batch.instanceCheck_honest

/-- info: 'CompStark.Iop.knowledgeSoundness' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.knowledgeSoundness

/-- info: 'CompStark.Iop.fibonacci_knowledgeError_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.fibonacci_knowledgeError_le

/-- info: 'CompStark.Iop.wide_knowledgeError_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide_knowledgeError_le

/-- info: 'CompStark.Iop.wideSp1_roundError_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideSp1_roundError_le

/-- info: 'CompStark.Iop.wide5_roundError_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5_roundError_le

/-- info: 'CompStark.Iop.wideGrind_roundError_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideGrind_roundError_le

/-- info: 'CompStark.Iop.wide5i_knowledgeError_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5i_knowledgeError_le

/-- info: 'CompStark.Iop.wide5i_knowledgeSoundness' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wide5i_knowledgeSoundness

/-- info: 'CompStark.Iop.friErrorWith_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.friErrorWith_eq

/-- info: 'CompStark.Iop.Prover.strategy_accepts' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.Prover.strategy_accepts

/-- info: 'CompStark.Iop.batchKnowledgeSoundness' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.batchKnowledgeSoundness

/-- info: 'CompStark.Sound.Batch.included_of_balanced' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.Batch.included_of_balanced

/-- info: 'CompStark.Iop.batchKnowledgeSoundness_inclusion' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.batchKnowledgeSoundness_inclusion

/-- info: 'CompStark.Sound.Batch.countsBounded_of_countsChecked' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.Batch.countsBounded_of_countsChecked

/-- info: 'CompStark.Iop.wideBus_countsChecked' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideBus_countsChecked

/-- info: 'CompStark.Iop.rangeKnowledgeSoundness' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.rangeKnowledgeSoundness

/-- info: 'CompStark.Iop.wideBatch_knowledgeError_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideBatch_knowledgeError_le

/-- info: 'CompStark.Iop.wideBatch_knowledgeSoundness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Iop.wideBatch_knowledgeSoundness

/-- info: 'CompStark.Sound.exists_satisfied_of_safe' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.exists_satisfied_of_safe

/-- info: 'CompStark.Sound.prob_alphaBad_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_alphaBad_le

/-- info: 'CompStark.Sound.prob_zetaBad_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_zetaBad_le

/-- info: 'CompStark.Sound.prob_batchBad_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_batchBad_le

/-- info: 'CompStark.Sound.prob_foldRound_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_foldRound_le

/-- info: 'CompStark.Sound.prob_queryBad_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Sound.prob_queryBad_le
