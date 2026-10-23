/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Security
import CompStark.Complete.Quotient
import CompStarkFixtures.Keccak
import CompStarkTests.Keccak

/-! # The proven security of Plonky3's Keccak example

Plonky3's `KeccakAir` (3182 constraints of degree `3`, 2633 columns, every column opened at the
next row) on `2 ^ 15` to `2 ^ 18` rows, with Plonky3's example configuration
(`CompStarkTests.Keccak.exampleParams`): blowup `2`, FRI folding by arity `8` down to a
constant, `87` queries, `16` bits of query grinding and `10` of batching grinding, caps of height
`3`, over KoalaBear's quartic extension. The kernel reads the AIR once (`keccak_facts`: its
columns, its degree, its constraint count and its constraints' degree profiles), which fixes the
calculator's shape of every setup (`shape_setup`), so each certificate below only evaluates the
calculator's rationals.

| configuration | field | random-oracle bits | interactive bits |
| --- | --- | --- | --- |
| Plonky3's example, blowup `2`, `87` queries | quartic | `52` | `36` |
| blowup `2`, `203` / `244` queries | quartic | `100` | `100` |
| blowup `4`, `124` / `149` queries | quartic | `100` | `100` |
| blowup `2`, `270` / `310` queries | quintic | `128` | `128` |
| blowup `4`, `166` / `190` queries | quintic | `128` | `128` |

Each query count is the smallest that reaches the bits with these bounds on all four heights; the
random-oracle bits are per oracle answer (`SecureRo`), with Plonky3's grinding. The analyses are
the ones `bestAnalysis` and `bestAnalysisRo` find on `2 ^ 15` rows. FRI's proximity `δ` stays
below the unique-decoding radius `1/4` (blowup `2`) or `3/8` (blowup `4`), where the proven
correlated-agreement bounds hold, so each query is worth at most `log₂ (4/3) ≈ 0.415` or
`log₂ (8/5) ≈ 0.678` bits; Plonky3's `87` queries and `16` bits of grinding give `52` bits per
oracle answer. Over the quartic extension the out-of-domain term `(3n + n) / |𝕂|` caps the bits
near `124 - (logN + 2)`, `104` to `107` here, so `128` bits need the quintic extension.
-/

namespace CompStarkTests.KeccakSecurity
open CompStark CompStark.Iop CompStark.Stark CompStark.Sound

local notation "F" => _root_.KoalaBear.Fast.Field

/-- Plonky3's Keccak AIR. -/
abbrev keccak : Air F := CompStark.Fixtures.Keccak.air

set_option maxRecDepth 100000 in
/-- The kernel's reading of the Keccak AIR: its constraints read its columns, have degree `3`,
number `3182`, and have degree profiles that fit two quotient chunks at every height. -/
theorem keccak_facts : keccak.ColsInWidth ∧ keccak.maxDegree = 3 ∧
    keccak.constraints.length = 3182 ∧ keccak.ProfileFits 1 := by
  unfold Air.ColsInWidth
  decide +kernel

/-- The Keccak AIR's quotient has two chunks at every height. -/
theorem keccak_logQuotientChunks (logN : ℕ) : keccak.logQuotientChunks logN = 1 :=
  logQuotientChunks_of _ _ 1 rfl (by rw [keccak_facts.2.1]; rfl)

/-- The Keccak AIR on `2 ^ logN` rows with FRI parameters of a positive blowup and a constant
final polynomial, on a two-adic domain. -/
theorem keccak_valid (P : Fri.Params) (hb : 0 < P.logBlowup) (ha : 0 < P.maxLogArity)
    (hf : P.logFinalPolyLen = 0) (hq : 0 < P.numQueries) (logN : ℕ)
    (h : logN + P.logBlowup ≤ 24) : ValidConfig P keccak logN where
  colsInWidth := keccak_facts.1
  preprocessedSize := rfl
  periodicFits := rfl
  degreeFits := by
    unfold Air.DegreeFits
    rw [keccak_logQuotientChunks]
    exact Air.degreeFitsAt_of_profileFits _ _ _ keccak_facts.2.2.2
  twoAdic := h
  chunksFit := by rw [keccak_logQuotientChunks]; exact hb
  folds := ha
  finalPolyFits := by rw [hf]; exact Nat.zero_le _
  queries := hq
  blowup := hb

/-- Plonky3's example configuration at blowup `2 ^ (blowup + 1)` with `numQueries` queries. -/
def params (blowup : Fin 2) (numQueries : ℕ+) : Fri.Params where
  logBlowup := blowup + 1
  logFinalPolyLen := 0
  maxLogArity := 3
  numQueries := numQueries
  commitPowBits := 0
  queryPowBits := 16
  batchPowBits := 10
  capHeight := 3

/-- `params 0 87` is Plonky3's example configuration. -/
example : params 0 87 = CompStarkTests.Keccak.exampleParams := rfl

/-- The Keccak AIR on `2 ^ (height + 15)` rows with `params blowup numQueries`. -/
def setup (EF : Type) [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+) (height : Fin 4) :
    Setup EF where
  params := params blowup numQueries
  air := keccak
  logN := height + 15
  valid := keccak_valid _ (Nat.succ_pos _) (Nat.succ_pos 2) rfl numQueries.pos _
    (by change (height : ℕ) + 15 + (blowup + 1) ≤ 24; omega)
  folds := by change 0 < (height : ℕ) + 15; omega
  capFits := by change 3 ≤ (height : ℕ) + 15 + (blowup + 1) - 3; omega

/-- The calculator's shape of a Keccak setup. -/
theorem shape_setup (EF : Type) [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+)
    (height : Fin 4) :
    (setup EF blowup numQueries height).shape =
      ⟨3182, 2 ^ (height + 15 : ℕ) * 3, 5266 + Challenge.d EF * 2, false, height + 15⟩ := by
  have hc : (setup EF blowup numQueries height).chunks = 2 := by
    rw [Setup.chunks_nil]
    change 2 ^ keccak.logQuotientChunks (height + 15) = 2
    rw [keccak_logQuotientChunks]
    rfl
  rw [shape_eq_of_profileFits _ (by
      change keccak.ProfileFits (keccak.logQuotientChunks (height + 15))
      rw [keccak_logQuotientChunks]
      exact keccak_facts.2.2.2), hc, Setup.numOpened_nil, hc]
  change Shape.mk keccak.constraints.length _ _ _ _ = _
  rw [keccak_facts.2.2.1]
  rfl

local notation "Ext4" => _root_.KoalaBear.Fast.Ext4
local notation "Ext5" => _root_.KoalaBear.Fast.Ext5

/-! ### Plonky3's example configuration -/

/-- The analysis `bestAnalysisRo` finds for the example on `2 ^ 15` rows. -/
def exampleRoAnalysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 14, 1 / 4 - 1 / 2 ^ 16, 1 / 2 ^ 60⟩

/-- The analysis `bestAnalysis` finds for the example on `2 ^ 15` rows. -/
def exampleAnalysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 14, 1 / 4 - 1 / 2 ^ 26, 1 / 2 ^ 60⟩

/-- **52 bits per oracle answer** for Plonky3's Keccak example on `2 ^ 15` to `2 ^ 18` rows. -/
theorem example_secureRo (height : Fin 4) :
    (setup Ext4 0 87 height).SecureRo 2130706433 exampleRoAnalysis 52 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

/-- **36 bits, interactively,** for Plonky3's Keccak example on `2 ^ 15` to `2 ^ 18` rows. -/
theorem example_secure (height : Fin 4) :
    (setup Ext4 0 87 height).Secure 2130706433 exampleAnalysis 36 := by
  refine secure_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

/-! ### 100 bits over the quartic extension -/

/-- The analysis for blowup `2`, `203` queries, per oracle answer. -/
def roAnalysis2 : Analysis := ⟨1 / 4 - 1 / 2 ^ 14, 1 / 4 - 1 / 2 ^ 16, 1 / 2 ^ 60⟩

/-- The analysis for blowup `2`, `244` queries. -/
def analysis2 : Analysis := ⟨1 / 4 - 1 / 2 ^ 10, 1 / 4 - 1 / 2 ^ 12, 1 / 2 ^ 60⟩

/-- The analysis for blowup `4`, `124` queries, per oracle answer. -/
def roAnalysis4 : Analysis := ⟨3 / 8 - 1 / 2 ^ 15, 3 / 8 - 1 / 2 ^ 17, 1 / 2 ^ 60⟩

/-- The analysis for blowup `4`, `149` queries. -/
def analysis4 : Analysis := ⟨3 / 8 - 1 / 2 ^ 10, 3 / 8 - 1 / 2 ^ 13, 1 / 2 ^ 60⟩

theorem secureRo100_blowup2 (height : Fin 4) :
    (setup Ext4 0 203 height).SecureRo 2130706433 roAnalysis2 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure100_blowup2 (height : Fin 4) :
    (setup Ext4 0 244 height).Secure 2130706433 analysis2 100 := by
  refine secure_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

theorem secureRo100_blowup4 (height : Fin 4) :
    (setup Ext4 1 124 height).SecureRo 2130706433 roAnalysis4 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure100_blowup4 (height : Fin 4) :
    (setup Ext4 1 149 height).Secure 2130706433 analysis4 100 := by
  refine secure_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

/-! ### 128 bits over the quintic extension -/

/-- The analysis for blowup `2`, `310` queries. -/
def analysis2q : Analysis := ⟨1 / 4 - 1 / 2 ^ 12, 1 / 4 - 1 / 2 ^ 14, 1 / 2 ^ 60⟩

/-- The analysis for blowup `4`, `190` queries. -/
def analysis4q : Analysis := ⟨3 / 8 - 1 / 2 ^ 12, 3 / 8 - 1 / 2 ^ 15, 1 / 2 ^ 60⟩

theorem secureRo128_blowup2 (height : Fin 4) :
    (setup Ext5 0 270 height).SecureRo 2130706433 roAnalysis2 128 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure128_blowup2 (height : Fin 4) :
    (setup Ext5 0 310 height).Secure 2130706433 analysis2q 128 := by
  refine secure_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

theorem secureRo128_blowup4 (height : Fin 4) :
    (setup Ext5 1 166 height).SecureRo 2130706433 roAnalysis4 128 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure128_blowup4 (height : Fin 4) :
    (setup Ext5 1 190 height).Secure 2130706433 analysis4q 128 := by
  refine secure_of_shape _ (shape_setup _ _ _ height) ?_
  revert height
  decide +kernel

/-! ### The search and the query counts -/

/-- The best bits the calculator finds for a setup, in the random-oracle model or interactively. -/
def bestBits {EF : Type} [Challenge F EF] (S : Setup EF) (ro : Bool) : Float :=
  if ro then (S.roundErrorReport 2130706433 (S.bestAnalysisRo 2130706433)).total
  else (S.knowledgeErrorReport 2130706433 (S.bestAnalysis 2130706433)).total

#guard (setup Ext4 0 87 0).bestAnalysisRo 2130706433 = exampleRoAnalysis
#guard (setup Ext4 0 87 0).bestAnalysis 2130706433 = exampleAnalysis
#guard (setup Ext4 0 203 0).bestAnalysisRo 2130706433 = roAnalysis2
#guard (setup Ext4 0 244 0).bestAnalysis 2130706433 = analysis2
#guard (setup Ext4 1 124 0).bestAnalysisRo 2130706433 = roAnalysis4
#guard (setup Ext4 1 149 0).bestAnalysis 2130706433 = analysis4
#guard (setup Ext5 0 270 0).bestAnalysisRo 2130706433 = roAnalysis2
#guard (setup Ext5 0 310 0).bestAnalysis 2130706433 = analysis2q
#guard (setup Ext5 1 166 0).bestAnalysisRo 2130706433 = roAnalysis4
#guard (setup Ext5 1 190 0).bestAnalysis 2130706433 = analysis4q
-- One query fewer does not reach the bits on `2 ^ 18` rows, at any analysis the search finds.
#guard bestBits (setup Ext4 0 202 3) true < 100 ∧ bestBits (setup Ext4 0 243 3) false < 100
#guard bestBits (setup Ext4 1 123 3) true < 100 ∧ bestBits (setup Ext4 1 148 3) false < 100
#guard bestBits (setup Ext5 0 269 3) true < 128 ∧ bestBits (setup Ext5 0 309 3) false < 128
#guard bestBits (setup Ext5 1 165 3) true < 128 ∧ bestBits (setup Ext5 1 189 3) false < 128

/-- info: 'CompStarkTests.KeccakSecurity.example_secureRo' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms example_secureRo

end CompStarkTests.KeccakSecurity
