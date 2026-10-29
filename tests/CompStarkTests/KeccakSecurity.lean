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
next row) as a statement (`statement`): the verifier takes the trace length from the proof and
admits `2 ^ n` rows for `n + logBlowup ≤ 24` (`admits_iff`), `2 ^ 0` to `2 ^ 23` rows at blowup
`2` and to `2 ^ 22` at blowup `4`, and every certificate below covers every admitted length. The
configuration is Plonky3's example (`CompStarkTests.Keccak.exampleParams`): blowup `2`, FRI
folding by arity `8` down to a constant, `87` queries, `16` bits of query grinding and `10` of
batching grinding, caps of height `3`, over KoalaBear's quartic extension; and variants. The
kernel reads the AIR once (`keccak_facts`: its columns, its degree, its constraint count and its
constraints' degree profiles), which fixes the calculator's shape at every length
(`shape_setup`), so each certificate only evaluates the calculator's rationals, at one analysis
for all lengths (`secureRo_of_lengths`, `secure_of_lengths`).

| configuration | field | random-oracle bits | interactive bits |
| --- | --- | --- | --- |
| Plonky3's example, blowup `2`, `87` queries | quartic | `52` | `36` |
| blowup `2`, `203` / `244` queries | quartic | `98` | `98` |
| blowup `4`, `124` / `149` queries | quartic | `98` | `98` |
| blowup `2`, `270` / `310` queries | quintic | `128` | `127` |
| blowup `4`, `166` / `190` queries | quintic | `128` | `128` |

The random-oracle bits are per oracle answer (`Statement.SecureRo`), with Plonky3's grinding. The
analyses are the ones `bestAnalysis` and `bestAnalysisRo` find at the longest admitted length,
with the MCA bound within the unique-decoding radius (`McaBound.uniqueDecoding`). FRI's proximity
`δ` stays below the unique-decoding radius `1/4` (blowup `2`) or `3/8` (blowup `4`), so each query
is worth at most `log₂ (4/3) ≈ 0.415` or `log₂ (8/5) ≈ 0.678` bits; Plonky3's `87` queries and
`16` bits of grinding give `52` bits per oracle answer. Over the quartic extension the
out-of-domain term `(3n + n + N) / |𝕂|` caps the bits near `124 - (logN + 2.6)` at blowup `2` and
`124 - (logN + 3)` at blowup `4`: about `98.4` on `2 ^ 23` rows and `99.0` on `2 ^ 22` rows, the
longest lengths the verifier admits, so no query count reaches `100` bits there, and `128` bits
need the quintic extension.

Up to the Johnson radius (`McaBound.uniqueOrJohnson`, proved by `McaBound.uniqueOrJohnson_holds`
on ArkLib's Johnson-regime MCA for power curves), FRI's `δ` goes up to `1 - √ρ` and the queries
drop:

| configuration | field | grinding | random-oracle bits | interactive bits |
| --- | --- | --- | --- | --- |
| blowup `2`, `169` / `205` queries | quintic | Plonky3's | `100` | `98` |
| blowup `4`, `85` / `102` queries | quintic | Plonky3's | `100` | `99` |
| blowup `2`, `230` queries | quintic | `johnsonGrinding5` | `125` | |
| blowup `4`, `115` queries | quintic | `johnsonGrinding5` | `126` | |
| blowup `2`, `172` queries | quartic | `johnsonGrinding4` | `96` | |
| blowup `4`, `86` queries | quartic | `johnsonGrinding4` | `97` | |

Beyond the unique-decoding radius the batching term, the Johnson count times the batching
curve's degree `5273`, grows with the trace length, so the longest admitted lengths decide these
bits. The out-of-domain term is linear in the list size, so `ζ` needs no grinding over the quintic
extension and `1` bit over the quartic one.
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

/-- The Keccak AIR with `params blowup numQueries g`, at the trace length its proofs claim. -/
def statement (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding) : Statement F :=
  ⟨params blowup numQueries g, keccak, keccak_facts.1⟩

/-- The verifier admits Keccak proofs of `2 ^ n` rows for `n + 2 ^ (blowup + 1)`'s log to fit
KoalaBear's two-adicity: `n + blowup + 1 ≤ 24`. -/
theorem admits_iff (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding) (n : ℕ) :
    (statement blowup numQueries g).admits n = true ↔ n + ((blowup : ℕ) + 1) ≤ 24 := by
  rw [Statement.admits_iff]
  constructor
  · intro h
    exact h.sound.twoAdic
  · intro h
    exact ⟨(keccak_valid _ (Nat.succ_pos _) (Nat.succ_pos 2) rfl numQueries.pos _ h).sound,
      fun hw ↦ absurd hw (lt_irrefl 0)⟩

/-- The Keccak AIR on `2 ^ n` rows with `params blowup numQueries g`. -/
def setup (EF : Type) [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding) (n : ℕ)
    (hn : n + ((blowup : ℕ) + 1) ≤ 24) : Setup EF where
  params := params blowup numQueries g
  air := keccak
  logN := n
  valid := (keccak_valid _ (Nat.succ_pos _) (Nat.succ_pos 2) rfl numQueries.pos _ hn).sound

theorem setupOf_eq (EF : Type) [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding)
    (n : ℕ) (h : (statement blowup numQueries g).admits n = true) :
    (statement blowup numQueries g).setupOf EF n h =
      setup EF blowup numQueries g n ((admits_iff blowup numQueries g n).mp h) := rfl

/-- The calculator's shape of the Keccak AIR on `2 ^ n` rows. -/
abbrev shapeAt (EF : Type) [Challenge F EF] (n : ℕ) : Shape :=
  ⟨3182, 2 ^ n * 3, 5266 + Challenge.d EF * 2, false, n⟩

/-- The calculator's shape of a Keccak setup. -/
theorem shape_setup (EF : Type) [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+) (g : Grinding)
    (n : ℕ) (hn : n + ((blowup : ℕ) + 1) ≤ 24) :
    (setup EF blowup numQueries g n hn).shape = shapeAt EF n := by
  have hc : (setup EF blowup numQueries g n hn).chunks = 2 := by
    rw [Setup.chunks_nil]
    change 2 ^ keccak.logQuotientChunks n = 2
    rw [keccak_logQuotientChunks]
    rfl
  rw [shape_eq_of_profileFits _ (by
      change keccak.ProfileFits (keccak.logQuotientChunks n)
      rw [keccak_logQuotientChunks]
      exact keccak_facts.2.2.2), hc, Setup.numOpened_nil, hc]
  change Shape.mk keccak.constraints.length _ _ _ _ = _
  rw [keccak_facts.2.2.1]
  rfl

/-- A Keccak statement's certificate per oracle answer from every admitted length's check on its
shape: the kernel never reads the AIR. -/
theorem secureRo_of_lengths {EF : Type} [Challenge F EF] {blowup : Fin 2} {numQueries : ℕ+}
    {g : Grinding} {B : McaBound} {A : Analysis} {bits : ℕ}
    (h : ∀ n : ℕ, n < 25 → ∀ hn : n + ((blowup : ℕ) + 1) ≤ 24,
      (setup EF blowup numQueries g n hn).Fits B A ∧
        maxTerms ((setup EF blowup numQueries g n hn).roundErrorTermsOf (shapeAt EF n)
          2130706433 B A) ≤ 1 / 2 ^ bits) :
    (statement blowup numQueries g).SecureRo EF 2130706433 B A bits := by
  intro n hn ha
  have hn' := (admits_iff blowup numQueries g n).mp ha
  rw [setupOf_eq]
  exact secureRo_of_shape _ (shape_setup _ _ _ _ _ _) (h n (by omega) hn')

/-- A Keccak statement's certificate from every admitted length's check on its shape. -/
theorem secure_of_lengths {EF : Type} [Challenge F EF] {blowup : Fin 2} {numQueries : ℕ+}
    {g : Grinding} {B : McaBound} {A : Analysis} {bits : ℕ}
    (h : ∀ n : ℕ, n < 25 → ∀ hn : n + ((blowup : ℕ) + 1) ≤ 24,
      (setup EF blowup numQueries g n hn).Fits B A ∧
        sumTerms ((setup EF blowup numQueries g n hn).knowledgeErrorTermsOf (shapeAt EF n)
          2130706433 B A) ≤ 1 / 2 ^ bits) :
    (statement blowup numQueries g).Secure EF 2130706433 B A bits := by
  intro n hn ha
  have hn' := (admits_iff blowup numQueries g n).mp ha
  rw [setupOf_eq]
  exact secure_of_shape _ (shape_setup _ _ _ _ _ _) (h n (by omega) hn')

local notation "Ext4" => _root_.KoalaBear.Fast.Ext4
local notation "Ext5" => _root_.KoalaBear.Fast.Ext5

/-! ### Plonky3's example configuration -/

/-- The analysis `bestAnalysisRo` finds for the example on `2 ^ 23` rows. -/
def exampleRoAnalysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 40, 1 / 4 - 1 / 2 ^ 42, 1 / 2 ^ 60⟩

/-- The analysis `bestAnalysis` finds for the example on `2 ^ 23` rows. -/
def exampleAnalysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 40, 1 / 4 - 1 / 2 ^ 42, 1 / 2 ^ 60⟩

/-- **52 bits per oracle answer** for Plonky3's Keccak example at every trace length. -/
theorem example_secureRo :
    (statement 0 87 .plonky3).SecureRo Ext4 2130706433 .uniqueDecoding exampleRoAnalysis 52 :=
  secureRo_of_lengths (by decide +kernel)

/-- **36 bits, interactively,** for Plonky3's Keccak example at every trace length. -/
theorem example_secure :
    (statement 0 87 .plonky3).Secure Ext4 2130706433 .uniqueDecoding exampleAnalysis 36 :=
  secure_of_lengths (by decide +kernel)

/-! ### Over the quartic extension -/

/-- The analysis for blowup `2`, `203` queries, per oracle answer. -/
def roAnalysis2 : Analysis := ⟨1 / 4 - 1 / 2 ^ 8, 1 / 4 - 1 / 2 ^ 10, 1 / 2 ^ 16⟩

/-- The analysis for blowup `2`, `244` queries. -/
def analysis2 : Analysis := ⟨1 / 4 - 1 / 2 ^ 10, 1 / 4 - 1 / 2 ^ 12, 1 / 2 ^ 16⟩

/-- The analysis for blowup `4`, `124` queries, per oracle answer. -/
def roAnalysis4 : Analysis := ⟨3 / 8 - 1 / 2 ^ 9, 3 / 8 - 1 / 2 ^ 11, 1 / 2 ^ 16⟩

/-- The analysis for blowup `4`, `149` queries. -/
def analysis4 : Analysis := ⟨3 / 8 - 1 / 2 ^ 10, 3 / 8 - 1 / 2 ^ 12, 1 / 2 ^ 16⟩

theorem secureRo98_blowup2 :
    (statement 0 203 .plonky3).SecureRo Ext4 2130706433 .uniqueDecoding roAnalysis2 98 :=
  secureRo_of_lengths (by decide +kernel)

theorem secure98_blowup2 :
    (statement 0 244 .plonky3).Secure Ext4 2130706433 .uniqueDecoding analysis2 98 :=
  secure_of_lengths (by decide +kernel)

theorem secureRo98_blowup4 :
    (statement 1 124 .plonky3).SecureRo Ext4 2130706433 .uniqueDecoding roAnalysis4 98 :=
  secureRo_of_lengths (by decide +kernel)

theorem secure98_blowup4 :
    (statement 1 149 .plonky3).Secure Ext4 2130706433 .uniqueDecoding analysis4 98 :=
  secure_of_lengths (by decide +kernel)

/-! ### Over the quintic extension -/

/-- The analysis for blowup `2`, `270` queries, per oracle answer. -/
def roAnalysis2q : Analysis := ⟨1 / 4 - 1 / 2 ^ 40, 1 / 4 - 1 / 2 ^ 42, 1 / 2 ^ 60⟩

/-- The analysis for blowup `2`, `310` queries. -/
def analysis2q : Analysis := ⟨1 / 4 - 1 / 2 ^ 12, 1 / 4 - 1 / 2 ^ 14, 1 / 2 ^ 18⟩

/-- The analysis for blowup `4`, `166` queries, per oracle answer. -/
def roAnalysis4q : Analysis := ⟨3 / 8 - 1 / 2 ^ 40, 3 / 8 - 1 / 2 ^ 42, 1 / 2 ^ 60⟩

/-- The analysis for blowup `4`, `190` queries. -/
def analysis4q : Analysis := ⟨3 / 8 - 1 / 2 ^ 12, 3 / 8 - 1 / 2 ^ 14, 1 / 2 ^ 18⟩

theorem secureRo128_blowup2 :
    (statement 0 270 .plonky3).SecureRo Ext5 2130706433 .uniqueDecoding roAnalysis2q 128 :=
  secureRo_of_lengths (by decide +kernel)

theorem secure127_blowup2 :
    (statement 0 310 .plonky3).Secure Ext5 2130706433 .uniqueDecoding analysis2q 127 :=
  secure_of_lengths (by decide +kernel)

theorem secureRo128_blowup4 :
    (statement 1 166 .plonky3).SecureRo Ext5 2130706433 .uniqueDecoding roAnalysis4q 128 :=
  secureRo_of_lengths (by decide +kernel)

theorem secure128_blowup4 :
    (statement 1 190 .plonky3).Secure Ext5 2130706433 .uniqueDecoding analysis4q 128 :=
  secure_of_lengths (by decide +kernel)

/-! ### Beyond the unique-decoding radius

With the MCA bound up to the Johnson radius (`McaBound.uniqueOrJohnson`), FRI's proximity `δ`
goes up to `1 - √ρ`: about `0.2925` at blowup `2` and `0.4995` at blowup `4`, so a query is worth
up to `0.4985` or `0.9986` bits. The batching curve has degree `5273` (`5275` over the quintic
extension), which the Johnson count multiplies, so the quartic extension and the quintic one at
`128` bits need grinding before the batching challenge: `johnsonGrinding5` (`0`, `30` and `12`
bits before `ζ`, the batching challenge and each fold) and `johnsonGrinding4` (`1`, `30`, `16`). -/

/-- Grinding up to the Johnson radius over the quintic extension. -/
def johnsonGrinding5 : Grinding := ⟨0, 30, 12⟩

/-- Grinding up to the Johnson radius over the quartic extension. -/
def johnsonGrinding4 : Grinding := ⟨1, 30, 16⟩

/-- Quintic extension, blowup `2`, `169` queries, Plonky3's grinding, per oracle answer. -/
def johnsonRo5b2 : Analysis := ⟨611429 / 2097152, 2448527 / 8388608, 1 / 2 ^ 60⟩

/-- Quintic extension, blowup `4`, `85` queries, Plonky3's grinding, per oracle answer. -/
def johnsonRo5b4 : Analysis := ⟨66977665 / 134217728, 268041731 / 536870912, 1 / 2 ^ 60⟩

/-- Quintic extension, blowup `2`, `205` queries. -/
def johnson5b2 : Analysis := ⟨1197559 / 4194304, 76674697 / 268435456, 1 / 2 ^ 60⟩

/-- Quintic extension, blowup `4`, `102` queries. -/
def johnson5b4 : Analysis := ⟨8257521 / 16777216, 1057093759 / 2147483648, 1 / 2 ^ 60⟩

/-- Quintic extension, blowup `2`, `230` queries, `johnsonGrinding5`, per oracle answer. -/
def johnsonRo128b2 : Analysis := ⟨73969 / 262144, 298687 / 1048576, 1 / 2 ^ 16⟩

/-- Quintic extension, blowup `4`, `115` queries, `johnsonGrinding5`, per oracle answer. -/
def johnsonRo128b4 : Analysis := ⟨32636871 / 67108864, 131464981 / 268435456, 1 / 2 ^ 60⟩

/-- Quartic extension, blowup `2`, `172` queries, `johnsonGrinding4`, per oracle answer. -/
def johnsonRo4b2 : Analysis := ⟨583319 / 2097152, 18697129 / 67108864, 1 / 2 ^ 60⟩

/-- Quartic extension, blowup `4`, `86` queries, `johnsonGrinding4`, per oracle answer. -/
def johnsonRo4b4 : Analysis := ⟨32374729 / 67108864, 16577040887 / 34359738368, 1 / 2 ^ 16⟩

theorem johnson_secureRo100_quintic_blowup2 :
    (statement 0 169 .plonky3).SecureRo Ext5 2130706433 .uniqueOrJohnson johnsonRo5b2 100 :=
  secureRo_of_lengths (by decide +kernel)

theorem johnson_secureRo100_quintic_blowup4 :
    (statement 1 85 .plonky3).SecureRo Ext5 2130706433 .uniqueOrJohnson johnsonRo5b4 100 :=
  secureRo_of_lengths (by decide +kernel)

theorem johnson_secure98_quintic_blowup2 :
    (statement 0 205 .plonky3).Secure Ext5 2130706433 .uniqueOrJohnson johnson5b2 98 :=
  secure_of_lengths (by decide +kernel)

theorem johnson_secure99_quintic_blowup4 :
    (statement 1 102 .plonky3).Secure Ext5 2130706433 .uniqueOrJohnson johnson5b4 99 :=
  secure_of_lengths (by decide +kernel)

theorem johnson_secureRo125_blowup2 :
    (statement 0 230 johnsonGrinding5).SecureRo Ext5 2130706433 .uniqueOrJohnson
      johnsonRo128b2 125 :=
  secureRo_of_lengths (by decide +kernel)

theorem johnson_secureRo126_blowup4 :
    (statement 1 115 johnsonGrinding5).SecureRo Ext5 2130706433 .uniqueOrJohnson
      johnsonRo128b4 126 :=
  secureRo_of_lengths (by decide +kernel)

theorem johnson_secureRo96_quartic_blowup2 :
    (statement 0 172 johnsonGrinding4).SecureRo Ext4 2130706433 .uniqueOrJohnson
      johnsonRo4b2 96 :=
  secureRo_of_lengths (by decide +kernel)

theorem johnson_secureRo97_quartic_blowup4 :
    (statement 1 86 johnsonGrinding4).SecureRo Ext4 2130706433 .uniqueOrJohnson
      johnsonRo4b4 97 :=
  secureRo_of_lengths (by decide +kernel)

/-- **100 bits per oracle answer with `85` queries at every trace length**, Plonky3's grinding,
over the quintic extension at blowup `4`, FRI beyond the unique-decoding radius at `δ ≈ 0.499`. -/
theorem johnson_roundError_le_quintic :
    (statement 1 85 .plonky3).roundError Ext5 (fun _ ↦ 66977665 / 134217728)
      (fun _ ↦ 268041731 / 536870912) ≤ (2 ^ 100)⁻¹ :=
  Statement.roundError_le_of_secureRo _ KoalaBear.card_eq McaBound.uniqueOrJohnson_holds _
    johnson_secureRo100_quintic_blowup4 _ _ (by norm_num [johnsonRo5b4])
    (by norm_num [johnsonRo5b4])

/-! ### The search -/

/-- The analysis the search finds on `2 ^ n` rows for a Keccak configuration, in the
random-oracle model or interactively. -/
def bestAt (B : McaBound) {EF : Type} [Challenge F EF] (blowup : Fin 2) (numQueries : ℕ+)
    (g : Grinding) (n : ℕ) (hn : n + ((blowup : ℕ) + 1) ≤ 24) (ro : Bool) : Analysis :=
  let S := setup EF blowup numQueries g n hn
  if ro then S.bestAnalysisRo 2130706433 B else S.bestAnalysis 2130706433 B

-- The analyses are the ones the search finds at the longest admitted trace length.
#guard bestAt .uniqueDecoding (EF := Ext4) 0 87 .plonky3 23 (by decide) true = exampleRoAnalysis
#guard bestAt .uniqueDecoding (EF := Ext4) 0 87 .plonky3 23 (by decide) false = exampleAnalysis
#guard bestAt .uniqueDecoding (EF := Ext4) 0 203 .plonky3 23 (by decide) true = roAnalysis2
#guard bestAt .uniqueDecoding (EF := Ext4) 0 244 .plonky3 23 (by decide) false = analysis2
#guard bestAt .uniqueDecoding (EF := Ext4) 1 124 .plonky3 22 (by decide) true = roAnalysis4
#guard bestAt .uniqueDecoding (EF := Ext4) 1 149 .plonky3 22 (by decide) false = analysis4
#guard bestAt .uniqueDecoding (EF := Ext5) 0 270 .plonky3 23 (by decide) true = roAnalysis2q
#guard bestAt .uniqueDecoding (EF := Ext5) 0 310 .plonky3 23 (by decide) false = analysis2q
#guard bestAt .uniqueDecoding (EF := Ext5) 1 166 .plonky3 22 (by decide) true = roAnalysis4q
#guard bestAt .uniqueDecoding (EF := Ext5) 1 190 .plonky3 22 (by decide) false = analysis4q
#guard bestAt .uniqueOrJohnson (EF := Ext5) 0 169 .plonky3 23 (by decide) true = johnsonRo5b2
#guard bestAt .uniqueOrJohnson (EF := Ext5) 1 85 .plonky3 22 (by decide) true = johnsonRo5b4
#guard bestAt .uniqueOrJohnson (EF := Ext5) 0 205 .plonky3 23 (by decide) false = johnson5b2
#guard bestAt .uniqueOrJohnson (EF := Ext5) 1 102 .plonky3 22 (by decide) false = johnson5b4
#guard bestAt .uniqueOrJohnson (EF := Ext5) 0 230 johnsonGrinding5 23 (by decide) true =
  johnsonRo128b2
#guard bestAt .uniqueOrJohnson (EF := Ext5) 1 115 johnsonGrinding5 22 (by decide) true =
  johnsonRo128b4
#guard bestAt .uniqueOrJohnson (EF := Ext4) 0 172 johnsonGrinding4 23 (by decide) true =
  johnsonRo4b2
#guard bestAt .uniqueOrJohnson (EF := Ext4) 1 86 johnsonGrinding4 22 (by decide) true =
  johnsonRo4b4
