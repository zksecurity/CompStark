/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Stark
public import CompStark.Fs.HashChain
public import ArkLib.Interaction.Oracle.Security.HashChainSqueeze

/-! # The STARK's challenges on Plonky3's duplex challenger: counts

The counts the theorems on Plonky3's verifier take: the STARK's paths have at most
`maxChallenges = twoAdicity F + 4` challenges (`Setup.challengesLE_publicCoin`: `α`, `ζ`, the
batching challenge, FRI's folds, at most the domain's log size, `numFolds_friSchedule_le`, and the
queries), each drawn from at most `coinCount` squeezes, so the verifier's completion makes at most
`verifierChainQueries` duplex calls.
-/

@[expose] public section
namespace CompStark.Fs
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin

/-- A bound on the challenges of every path holds for every larger bound. -/
theorem challengesLE_mono : {protocol : Protocol} → (coin : PublicCoin protocol) → {N N' : ℕ} →
    coin.ChallengesLE N → N ≤ N' → coin.ChallengesLE N'
  | _, .done, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, _, _, h, hle => fun move ↦
      challengesLE_mono (next move) (h move) hle
  | _, @PublicCoin.oracle _ _ _ _ next, _, _, h, hle => challengesLE_mono next h hle
  | _, @PublicCoin.challenge _ _ _ next, _, _, h, hle =>
      ⟨Nat.lt_of_lt_of_le h.1 hle, challengesLE_mono next h.2 (Nat.sub_le_sub_right hle 1)⟩

/-- FRI's paths have a challenge per fold and the query challenge. -/
theorem challengesLE_friPublicCoin {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [SampleableType K] (top d t : ℕ) : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    (Fri.Interaction.publicCoin K top d t s).ChallengesLE (s.numFolds + 1)
  | _, .final => fun _ ↦ ⟨Nat.one_pos, trivial⟩
  | _, .fold _ _ _ rest => ⟨Nat.succ_pos _, challengesLE_friPublicCoin top d t rest⟩

/-- Plonky3's schedule folds at most `fuel` times. -/
theorem numFolds_plonky3_le (maxLogArity logFinal : ℕ) : (fuel n : ℕ) → (heights : List ℕ) →
    (Fri.Interaction.Schedule.plonky3 maxLogArity logFinal fuel n heights).numFolds ≤ fuel
  | 0, _, _ => le_rfl
  | fuel + 1, n, [] => by
      rw [Fri.Interaction.Schedule.plonky3]
      split_ifs
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (numFolds_plonky3_le maxLogArity logFinal fuel _ _)
  | fuel + 1, n, m :: rest => by
      rw [Fri.Interaction.Schedule.plonky3]
      dsimp only
      split_ifs
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (numFolds_plonky3_le maxLogArity logFinal fuel _ _)
      · exact Nat.succ_le_succ (numFolds_plonky3_le maxLogArity logFinal fuel _ _)

end CompStark.Fs

namespace CompStark.Iop.Setup
open CompStark.Fs _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- FRI's schedule folds at most the log size of its domain times. -/
theorem numFolds_friSchedule_le {lookups : List (Stark.Lookup F)} (S : Setup EF lookups)
    (heights : List ℕ) : (S.friSchedule heights).numFolds ≤ twoAdicity F :=
  (numFolds_plonky3_le _ _ _ _ heights).trans S.valid.twoAdic

/-- The STARK's paths have at most `twoAdicity F + 4` challenges: `α`, `ζ`, the batching challenge,
FRI's folds, at most the domain's log size, and the queries. -/
theorem challengesLE_publicCoin (S : Setup EF) : S.publicCoin.ChallengesLE (twoAdicity F + 4) := by
  have hf := S.numFolds_friSchedule_le []
  exact ⟨by omega, by omega, fun _ ↦ ⟨by omega, challengesLE_mono _
    (challengesLE_friPublicCoin _ _ _ (S.friSchedule [])) (by omega)⟩⟩

end CompStark.Iop.Setup

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs CompStark.RandomOracle OracleComp OracleSpec
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security _root_.Interaction.Oracle.Security.StateRestoration
open _root_.Interaction.Oracle.Security.HashChain
open _root_.Interaction.Oracle.TypeTree
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- The challenges on a path of the STARK at any admitted length: `α`, `ζ`, the batching challenge,
at most `twoAdicity F` folds and the queries. -/
def maxChallenges : ℕ := twoAdicity F + 4

/-- The duplex calls of the verifier's completion: at each of its at most `maxChallenges`
challenges, at most `coinCount` squeezes, each absorbing at most the inputs of the earlier
challenges' squeezes and its own. -/
def verifierChainQueries : ℕ :=
  maxChallenges (F := F) * (C.coinCount EF K * (maxChallenges (F := F) * C.coinCount EF K +
    C.coinCount EF K))

end CompStark.Iop.Statement
