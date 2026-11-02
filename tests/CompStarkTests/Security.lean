/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Security
import CompStark.Fs.Secure

/-! # The security calculator

The reports of the concrete setups and statements, the analyses of `CompStark/Security.lean` as
the ones the search (`bestAnalysis`, `bestAnalysisRo`) finds, a check on an AIR of `4096`
constraints in the kernel, the calculator theorems' axioms, and the calculator's certificates on
Plonky3's verifiers with Merkle commitments with their bounds at `2 ^ 64` calls (`bcsBound`).
-/

namespace CompStarkTests.Security
open CompStark CompStark.Iop CompStark.Stark

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize
local notation "Ext4" => KoalaBear.Fast.Ext4

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

/-- info: 'CompStark.Iop.batchKnowledgeSoundness_of_secure' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batchKnowledgeSoundness_of_secure

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

section MerkleCommitments
open OracleComp OracleSpec CompStark.Fs CompStark.RandomOracle
open _root_.Interaction.Oracle.Security _root_.Interaction.Oracle.Security.HashChain

/-- **117 bits per duplex call** for `wideGrindStatement` on Plonky3's verifier with Merkle
commitments: the calculator's certificate per oracle answer (`wideGrindStatement_secureRo`) bounds
the knowledge soundness theorem, against an adversary making `Q` duplex calls and `q` oracle calls
with samples of `K` elements per squeeze, by `chainError Q' + hashBadError + (Q' + maxChallenges) ·
2 ^ (-117)`, `Q' = Q + verifierQueries + 3 verifierChainQueries`. -/
theorem wideGrind_knowledgeSoundness_bcs {K : ℕ} (hK : 0 < K)
    (adversary : OracleComp (spec F K) (List F × Proof F Ext4)) {Q q : ℕ}
    (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (wideGrindStatement.starkGame Ext4 K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧ ∀ h : wideGrindStatement.Admits z.1.2.2.1.degreeBits,
        ∀ trace ∈ closeTraces (wideGrindStatement.setupAt Ext4 _ h)
          ((3 / 8 - 2 ^ (-13 : ℤ) : NNReal) : ℝ)
          ((wideGrindStatement.setupAt Ext4 _ h).traceWords
            ((wideGrindStatement.setupAt Ext4 _ h).traceMessageOf
              (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.traceCommit)),
        ¬ wideGrindStatement.air.Satisfied z.1.2.2.1.degreeBits trace z.1.2.1] ≤
      chainError (Digest F) (Q + wideGrindStatement.verifierQueries Ext4 +
          3 * wideGrindStatement.verifierChainQueries Ext4 K) +
        hashBadError F (2 ^ wideGrindStatement.params.capHeight)
          (wideGrindStatement.capOffsets Ext4).length
          (q + wideGrindStatement.verifierQueries Ext4) +
        (Q + wideGrindStatement.verifierQueries Ext4 +
            3 * wideGrindStatement.verifierChainQueries Ext4 K + @Statement.maxChallenges F _) *
          (2 ^ 117)⁻¹ :=
  Statement.knowledgeSoundness_bcs_of_secureRo _ KoalaBear.card_eq
    Sound.McaBound.uniqueDecoding_holds
    wideGrindAnalysis wideGrindStatement_secureRo (by rw [KoalaBear.card_eq]; norm_num) (by decide)
    hK (3 / 8 - 2 ^ (-13 : ℤ) : NNReal)
    (by rw [Sound.coe_sub_two_zpow _ (-13) 13 rfl (by norm_num)]; norm_num [wideGrindAnalysis])
    (by decide +kernel) adversary hQ hq

/-- info: 'CompStarkTests.Security.wideGrind_knowledgeSoundness_bcs' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wideGrind_knowledgeSoundness_bcs

/-- **115 bits per duplex call** for `wideBatchGrindStatement` on Plonky3's batch verifier with
Merkle commitments: the calculator's certificate per oracle answer
(`wideBatchGrindStatement_secureRo`) bounds the knowledge soundness theorem, against an adversary
making `Q` duplex calls and `q` oracle calls with samples of `K` elements per squeeze, by
`chainError Q' + hashBadError + (Q' + maxChallenges) · 2 ^ (-115)`,
`Q' = Q + verifierQueries + 3 verifierChainQueries`. -/
theorem wideBatchGrind_knowledgeSoundness_bcs {K : ℕ} (hK : 0 < K)
    (adversary : OracleComp (spec F K)
      ((Fin wideBatchGrindStatement.k → List F) × CompStark.Batch.BatchProof F Ext4)) {Q q : ℕ}
    (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (wideBatchGrindStatement.batchGame Ext4 K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧
        ∀ h : wideBatchGrindStatement.Admits (wideBatchGrindStatement.lengthsOf z.1.2.2.1),
          ∀ traces ∈ Batch.closeTraces (wideBatchGrindStatement.setupAt Ext4 _ h)
            ((3 / 8 - 2 ^ (-14 : ℤ) : NNReal) : ℝ)
            ((wideBatchGrindStatement.setupAt Ext4 _ h).traceWords
              ((wideBatchGrindStatement.setupAt Ext4 _ h).traceMessageOf
                (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.mainCommit)),
          ¬ (wideBatchGrindStatement.setupAt Ext4 _ h).Satisfied traces z.1.2.1] ≤
      chainError (Digest F) (Q + wideBatchGrindStatement.verifierQueries Ext4 +
          3 * wideBatchGrindStatement.verifierChainQueries Ext4 K) +
        hashBadError F (2 ^ wideBatchGrindStatement.params.capHeight)
          (wideBatchGrindStatement.capOffsets Ext4).length
          (q + wideBatchGrindStatement.verifierQueries Ext4) +
        (Q + wideBatchGrindStatement.verifierQueries Ext4 +
            3 * wideBatchGrindStatement.verifierChainQueries Ext4 K +
            @Batch.Statement.maxChallenges F _) * (2 ^ 115)⁻¹ :=
  Batch.Statement.knowledgeSoundness_bcs_of_secureRo _ KoalaBear.card_eq
    Sound.McaBound.uniqueDecoding_holds wideBatchGrindAnalysis wideBatchGrindStatement_secureRo hK
    (3 / 8 - 2 ^ (-14 : ℤ) : NNReal)
    (by rw [Sound.coe_sub_two_zpow _ (-14) 14 rfl (by norm_num)]; norm_num [wideBatchGrindAnalysis])
    adversary hQ hq

/--
info: 'CompStarkTests.Security.wideBatchGrind_knowledgeSoundness_bcs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wideBatchGrind_knowledgeSoundness_bcs

/-- A float in `[lo, hi)`. -/
def between (x lo hi : Float) : Bool := lo ≤ x && x < hi

-- The bounds at `Q = q = 2 ^ 64` duplex and oracle calls with squeezes of `8` samples, the round
-- error's bound per duplex call: about `2 ^ (-53.37)` and `2 ^ (-51.05)`.
#guard between (securityBits (wideGrindStatement.bcsBound Ext4 2130706433 8 (2 ^ 64) (2 ^ 64)
  .uniqueDecoding wideGrindAnalysis)) 53.36 53.37
#guard between (securityBits (wideBatchGrindStatement.bcsBound Ext4 2130706433 8 (2 ^ 64) (2 ^ 64)
  .uniqueDecoding wideBatchGrindAnalysis)) 51.04 51.05

end MerkleCommitments

end CompStarkTests.Security
