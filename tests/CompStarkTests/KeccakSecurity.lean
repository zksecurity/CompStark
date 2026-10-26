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
the ones `bestAnalysis` and `bestAnalysisRo` find on `2 ^ 15` rows, with the MCA bound within the
unique-decoding radius (`McaBound.uniqueDecoding`). FRI's proximity `δ` stays below the
unique-decoding radius `1/4` (blowup `2`) or `3/8` (blowup `4`), so each query is worth at most
`log₂ (4/3) ≈ 0.415` or `log₂ (8/5) ≈ 0.678` bits; Plonky3's `87` queries and `16` bits of
grinding give `52` bits per oracle answer. Over the quartic extension the out-of-domain term
`(3n + n) / |𝕂|` caps the bits near `124 - (logN + 2)`, `104` to `107` here, so `128` bits need
the quintic extension.

Up to the Johnson radius (`McaBound.uniqueOrJohnson`, on the Johnson bound for power curves
`McaBound.johnson`), FRI's `δ` goes up to `1 - √ρ` and the queries drop:

| configuration | field | grinding | random-oracle bits | interactive bits |
| --- | --- | --- | --- | --- |
| blowup `2`, `169` / `205` queries | quintic | Plonky3's | `100` | `100` |
| blowup `4`, `85` / `102` queries | quintic | Plonky3's | `100` | `100` |
| blowup `2`, `230` queries | quintic | `johnsonGrinding5` | `128` | |
| blowup `4`, `115` queries | quintic | `johnsonGrinding5` | `128` | |
| blowup `2`, `172` queries | quartic | `johnsonGrinding4` | `100` | |
| blowup `4`, `86` queries | quartic | `johnsonGrinding4` | `100` | |

The analyses are the ones the search finds on `2 ^ 18` rows. Interactively, without credit for
grinding, the quartic extension and `128` bits stay at the unique-decoding counts, and so does the
quartic extension per oracle answer with Plonky3's grinding: the batching term, the Johnson count
times the batching curve's degree `5273`, needs `30` bits of grinding there.
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

/-- The bits of grinding before `ζ`, the batching challenge and each fold. -/
structure Grinding where
  ood : ℕ
  batch : ℕ
  commit : ℕ

/-- Plonky3's example grinding: `10` bits before the batching challenge. -/
def Grinding.plonky3 : Grinding := ⟨0, 10, 0⟩

/-- Plonky3's example configuration at blowup `2 ^ (blowup + 1)` with `numQueries` queries and the
grinding `g`, `16` bits before the queries. -/
def params (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding) : Fri.Params where
  logBlowup := blowup + 1
  logFinalPolyLen := 0
  maxLogArity := 3
  numQueries := numQueries
  commitPowBits := g.commit
  queryPowBits := 16
  batchPowBits := g.batch
  oodPowBits := g.ood
  capHeight := 3

/-- `params 0 87 .plonky3` is Plonky3's example configuration. -/
example : params 0 87 .plonky3 = CompStarkTests.Keccak.exampleParams := rfl

/-- The Keccak AIR on `2 ^ (height + 15)` rows with `params blowup numQueries g`. -/
def setup (EF : Type) [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding)
    (height : Fin 4) : Setup EF where
  params := params blowup numQueries g
  air := keccak
  logN := height + 15
  valid := keccak_valid _ (Nat.succ_pos _) (Nat.succ_pos 2) rfl numQueries.pos _
    (by change (height : ℕ) + 15 + (blowup + 1) ≤ 24; omega)
  folds := by change 0 < (height : ℕ) + 15; omega
  capFits := by change 3 ≤ (height : ℕ) + 15 + (blowup + 1) - 3; omega

/-- The calculator's shape of a Keccak setup. -/
theorem shape_setup (EF : Type) [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding)
    (height : Fin 4) :
    (setup EF blowup numQueries g height).shape =
      ⟨3182, 2 ^ (height + 15 : ℕ) * 3, 5266 + Challenge.d EF * 2, false, height + 15⟩ := by
  have hc : (setup EF blowup numQueries g height).chunks = 2 := by
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
    (setup Ext4 0 87 .plonky3 height).SecureRo 2130706433 .uniqueDecoding exampleRoAnalysis 52 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

/-- **36 bits, interactively,** for Plonky3's Keccak example on `2 ^ 15` to `2 ^ 18` rows. -/
theorem example_secure (height : Fin 4) :
    (setup Ext4 0 87 .plonky3 height).Secure 2130706433 .uniqueDecoding exampleAnalysis 36 := by
  refine secure_of_shape _ (shape_setup _ _ _ _ height) ?_
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
    (setup Ext4 0 203 .plonky3 height).SecureRo 2130706433 .uniqueDecoding roAnalysis2 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure100_blowup2 (height : Fin 4) :
    (setup Ext4 0 244 .plonky3 height).Secure 2130706433 .uniqueDecoding analysis2 100 := by
  refine secure_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem secureRo100_blowup4 (height : Fin 4) :
    (setup Ext4 1 124 .plonky3 height).SecureRo 2130706433 .uniqueDecoding roAnalysis4 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure100_blowup4 (height : Fin 4) :
    (setup Ext4 1 149 .plonky3 height).Secure 2130706433 .uniqueDecoding analysis4 100 := by
  refine secure_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

/-! ### 128 bits over the quintic extension -/

/-- The analysis for blowup `2`, `310` queries. -/
def analysis2q : Analysis := ⟨1 / 4 - 1 / 2 ^ 12, 1 / 4 - 1 / 2 ^ 14, 1 / 2 ^ 60⟩

/-- The analysis for blowup `4`, `190` queries. -/
def analysis4q : Analysis := ⟨3 / 8 - 1 / 2 ^ 12, 3 / 8 - 1 / 2 ^ 15, 1 / 2 ^ 60⟩

theorem secureRo128_blowup2 (height : Fin 4) :
    (setup Ext5 0 270 .plonky3 height).SecureRo 2130706433 .uniqueDecoding roAnalysis2 128 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure128_blowup2 (height : Fin 4) :
    (setup Ext5 0 310 .plonky3 height).Secure 2130706433 .uniqueDecoding analysis2q 128 := by
  refine secure_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem secureRo128_blowup4 (height : Fin 4) :
    (setup Ext5 1 166 .plonky3 height).SecureRo 2130706433 .uniqueDecoding roAnalysis4 128 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem secure128_blowup4 (height : Fin 4) :
    (setup Ext5 1 190 .plonky3 height).Secure 2130706433 .uniqueDecoding analysis4q 128 := by
  refine secure_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

/-! ### Beyond the unique-decoding radius

With the MCA bound up to the Johnson radius (`McaBound.uniqueOrJohnson`), FRI's proximity `δ`
goes up to `1 - √ρ`: about `0.2925` at blowup `2` and `0.4995` at blowup `4`, so a query is worth
up to `0.4985` or `0.9986` bits. The batching curve has degree `5273` (`5275` over the quintic
extension), which the Johnson count multiplies, so the quartic extension and `128` bits need
grinding before the batching challenge: `johnsonGrinding5` (`16`, `30` and `12` bits before `ζ`,
the batching challenge and each fold) and `johnsonGrinding4` (`20`, `30`, `16`). -/

/-- Grinding for `128` bits over the quintic extension up to the Johnson radius. -/
def johnsonGrinding5 : Grinding := ⟨16, 30, 12⟩

/-- Grinding for `100` bits over the quartic extension up to the Johnson radius. -/
def johnsonGrinding4 : Grinding := ⟨20, 30, 16⟩

/-- Quintic extension, blowup `2`, `169` queries, Plonky3's grinding, per oracle answer. -/
def johnsonRo5b2 : Analysis := ⟨2454149 / 8388608, 9819407 / 33554432, 1 / 2 ^ 60⟩

/-- Quintic extension, blowup `4`, `85` queries, Plonky3's grinding, per oracle answer. -/
def johnsonRo5b4 : Analysis := ⟨134086401 / 268435456, 536476675 / 1073741824, 1 / 2 ^ 60⟩

/-- Quintic extension, blowup `2`, `205` queries. -/
def johnson5b2 : Analysis := ⟨605807 / 2097152, 38780081 / 134217728, 1 / 2 ^ 60⟩

/-- Quintic extension, blowup `4`, `102` queries. -/
def johnson5b4 : Analysis := ⟨33161155 / 67108864, 4245021053 / 8589934592, 1 / 2 ^ 60⟩

/-- `128` bits over the quintic extension, blowup `2`, `230` queries, per oracle answer. -/
def johnsonRo128b2 : Analysis := ⟨1203181 / 4194304, 4838023 / 16777216, 1 / 2 ^ 16⟩

/-- `128` bits over the quintic extension, blowup `4`, `115` queries, per oracle answer. -/
def johnsonRo128b4 : Analysis := ⟨8257521 / 16777216, 33161155 / 67108864, 1 / 2 ^ 60⟩

/-- Quartic extension, blowup `2`, `172` queries, per oracle answer. -/
def johnsonRo4b2 : Analysis := ⟨150749 / 524288, 605807 / 2097152, 1 / 2 ^ 60⟩

/-- Quartic extension, blowup `4`, `86` queries, per oracle answer. -/
def johnsonRo4b4 : Analysis := ⟨33161155 / 67108864, 133037833 / 268435456, 1 / 2 ^ 16⟩

theorem johnson_secureRo100_quintic_blowup2 (height : Fin 4) :
    (setup Ext5 0 169 .plonky3 height).SecureRo 2130706433 .uniqueOrJohnson johnsonRo5b2 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem johnson_secureRo100_quintic_blowup4 (height : Fin 4) :
    (setup Ext5 1 85 .plonky3 height).SecureRo 2130706433 .uniqueOrJohnson johnsonRo5b4 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem johnson_secure100_quintic_blowup2 (height : Fin 4) :
    (setup Ext5 0 205 .plonky3 height).Secure 2130706433 .uniqueOrJohnson johnson5b2 100 := by
  refine secure_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem johnson_secure100_quintic_blowup4 (height : Fin 4) :
    (setup Ext5 1 102 .plonky3 height).Secure 2130706433 .uniqueOrJohnson johnson5b4 100 := by
  refine secure_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem johnson_secureRo128_blowup2 (height : Fin 4) :
    (setup Ext5 0 230 johnsonGrinding5 height).SecureRo 2130706433 .uniqueOrJohnson
      johnsonRo128b2 128 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem johnson_secureRo128_blowup4 (height : Fin 4) :
    (setup Ext5 1 115 johnsonGrinding5 height).SecureRo 2130706433 .uniqueOrJohnson
      johnsonRo128b4 128 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem johnson_secureRo100_quartic_blowup2 (height : Fin 4) :
    (setup Ext4 0 172 johnsonGrinding4 height).SecureRo 2130706433 .uniqueOrJohnson
      johnsonRo4b2 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

theorem johnson_secureRo100_quartic_blowup4 (height : Fin 4) :
    (setup Ext4 1 86 johnsonGrinding4 height).SecureRo 2130706433 .uniqueOrJohnson
      johnsonRo4b4 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _ _ height) ?_
  revert height
  decide +kernel

/-- **100 bits per oracle answer with `85` queries**, Plonky3's grinding, over the quintic
extension at blowup `4`, FRI beyond the unique-decoding radius at `δ ≈ 0.4995`, if the Johnson
bound holds. -/
theorem johnson_roundError_le_quintic (hJ : McaBound.johnson.Holds) (height : Fin 4) :
    roundError (setup Ext5 1 85 .plonky3 height) (134086401 / 268435456)
      (536476675 / 1073741824) ≤ (2 ^ 100)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq
    (McaBound.min_holds McaBound.uniqueDecoding_holds hJ) _
    (johnson_secureRo100_quintic_blowup4 height) _ _ (by norm_num [johnsonRo5b4])
    (by norm_num [johnsonRo5b4])

/-- **100 bits per oracle answer with `86` queries over the quartic extension** at blowup `4`,
with `johnsonGrinding4`, FRI at `δ ≈ 0.4941`, if the Johnson bound holds. -/
theorem johnson_roundError_le_quartic (hJ : McaBound.johnson.Holds) (height : Fin 4) :
    roundError (setup Ext4 1 86 johnsonGrinding4 height) (33161155 / 67108864)
      (133037833 / 268435456) ≤ (2 ^ 100)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq
    (McaBound.min_holds McaBound.uniqueDecoding_holds hJ) _
    (johnson_secureRo100_quartic_blowup4 height) _ _ (by norm_num [johnsonRo4b4])
    (by norm_num [johnsonRo4b4])

/-! ### The search and the query counts -/

/-- The best bits the calculator finds for a setup with the MCA bound `B`, in the random-oracle
model or interactively. -/
def bestBits (B : McaBound) {EF : Type} [Challenge F EF] (S : Setup EF) (ro : Bool) : Float :=
  if ro then (S.roundErrorReport 2130706433 B (S.bestAnalysisRo 2130706433 B)).total
  else (S.knowledgeErrorReport 2130706433 B (S.bestAnalysis 2130706433 B)).total

#guard (setup Ext4 0 87 .plonky3 0).bestAnalysisRo 2130706433 .uniqueDecoding = exampleRoAnalysis
#guard (setup Ext4 0 87 .plonky3 0).bestAnalysis 2130706433 .uniqueDecoding = exampleAnalysis
#guard (setup Ext4 0 203 .plonky3 0).bestAnalysisRo 2130706433 .uniqueDecoding = roAnalysis2
#guard (setup Ext4 0 244 .plonky3 0).bestAnalysis 2130706433 .uniqueDecoding = analysis2
#guard (setup Ext4 1 124 .plonky3 0).bestAnalysisRo 2130706433 .uniqueDecoding = roAnalysis4
#guard (setup Ext4 1 149 .plonky3 0).bestAnalysis 2130706433 .uniqueDecoding = analysis4
#guard (setup Ext5 0 270 .plonky3 0).bestAnalysisRo 2130706433 .uniqueDecoding = roAnalysis2
#guard (setup Ext5 0 310 .plonky3 0).bestAnalysis 2130706433 .uniqueDecoding = analysis2q
#guard (setup Ext5 1 166 .plonky3 0).bestAnalysisRo 2130706433 .uniqueDecoding = roAnalysis4
#guard (setup Ext5 1 190 .plonky3 0).bestAnalysis 2130706433 .uniqueDecoding = analysis4q
-- One query fewer does not reach the bits on `2 ^ 18` rows, at any analysis the search finds.
#guard bestBits .uniqueDecoding (setup Ext4 0 202 .plonky3 3) true < 100
#guard bestBits .uniqueDecoding (setup Ext4 0 243 .plonky3 3) false < 100
#guard bestBits .uniqueDecoding (setup Ext4 1 123 .plonky3 3) true < 100
#guard bestBits .uniqueDecoding (setup Ext4 1 148 .plonky3 3) false < 100
#guard bestBits .uniqueDecoding (setup Ext5 0 269 .plonky3 3) true < 128
#guard bestBits .uniqueDecoding (setup Ext5 0 309 .plonky3 3) false < 128
#guard bestBits .uniqueDecoding (setup Ext5 1 165 .plonky3 3) true < 128
#guard bestBits .uniqueDecoding (setup Ext5 1 189 .plonky3 3) false < 128

#guard (setup Ext5 0 169 .plonky3 3).bestAnalysisRo 2130706433 .uniqueOrJohnson = johnsonRo5b2
#guard (setup Ext5 1 85 .plonky3 3).bestAnalysisRo 2130706433 .uniqueOrJohnson = johnsonRo5b4
#guard (setup Ext5 0 205 .plonky3 3).bestAnalysis 2130706433 .uniqueOrJohnson = johnson5b2
#guard (setup Ext5 1 102 .plonky3 3).bestAnalysis 2130706433 .uniqueOrJohnson = johnson5b4
#guard (setup Ext5 0 230 johnsonGrinding5 3).bestAnalysisRo 2130706433 .uniqueOrJohnson =
  johnsonRo128b2
#guard (setup Ext5 1 115 johnsonGrinding5 3).bestAnalysisRo 2130706433 .uniqueOrJohnson =
  johnsonRo128b4
#guard (setup Ext4 0 172 johnsonGrinding4 3).bestAnalysisRo 2130706433 .uniqueOrJohnson =
  johnsonRo4b2
#guard (setup Ext4 1 86 johnsonGrinding4 3).bestAnalysisRo 2130706433 .uniqueOrJohnson =
  johnsonRo4b4
#guard bestBits .uniqueOrJohnson (setup Ext5 0 168 .plonky3 3) true < 100
#guard bestBits .uniqueOrJohnson (setup Ext5 1 84 .plonky3 3) true < 100
#guard bestBits .uniqueOrJohnson (setup Ext5 0 204 .plonky3 3) false < 100
#guard bestBits .uniqueOrJohnson (setup Ext5 1 101 .plonky3 3) false < 100
#guard bestBits .uniqueOrJohnson (setup Ext5 0 229 johnsonGrinding5 3) true < 128
#guard bestBits .uniqueOrJohnson (setup Ext5 1 114 johnsonGrinding5 3) true < 128
#guard bestBits .uniqueOrJohnson (setup Ext4 0 171 johnsonGrinding4 3) true < 100
#guard bestBits .uniqueOrJohnson (setup Ext4 1 85 johnsonGrinding4 3) true < 100

/-- info: 'CompStarkTests.KeccakSecurity.example_secureRo' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms example_secureRo

end CompStarkTests.KeccakSecurity
