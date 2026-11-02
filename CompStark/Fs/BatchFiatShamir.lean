/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Batch
public import CompStark.Fs.StarkFiatShamir

/-! # The batch STARK's challenges on Plonky3's duplex challenger: counts

The counts the duplex-challenger theorems of the batch STARK take: the batch's paths have at most
`maxChallenges = twoAdicity F + 5` challenges (`Setup.challengesLE_publicCoin`: the lookup
challenges, `α`, `ζ`, the batching challenge, FRI's folds, at most the tallest domain's log size,
`numFolds_friSchedule_le`, and the queries), each drawn from at most `coinCount` squeezes
(`FsCoins`, `fsCoin`), so the verifier's completion makes at most `verifierChainQueries` duplex
calls.
-/

@[expose] public section
namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Sound CompStark.Fs _root_.Interaction.Oracle
open _root_.Interaction.Oracle.PublicCoin _root_.Interaction.Oracle.Security

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The batch's paths have at most `twoAdicity F + 5` challenges: the lookup challenges, `α`, `ζ`,
the batching challenge, FRI's folds, at most the tallest domain's log size, and the queries. -/
theorem challengesLE_publicCoin {withLookups : Bool} (S : Setup EF withLookups) :
    S.publicCoin.ChallengesLE (twoAdicity F + 5) := by
  have hf := S.domainSetup.numFolds_friSchedule_le S.friHeights
  exact ⟨by omega, fun _ ↦ ⟨by omega, by omega, fun _ ↦ ⟨by omega, challengesLE_mono _
    (challengesLE_friPublicCoin _ _ _ (S.domainSetup.friSchedule S.friHeights)) (by omega)⟩⟩⟩

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security _root_.Interaction.Oracle.Security.StateRestoration

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- The coins of the batch's challenges: `coinCount` squeezes of `K` samples. -/
abbrev FsCoins : Type := Coins F K (C.coinCount EF K)

/-- The batch's decoded presentation, every challenge drawn from Plonky3's squeezes. -/
noncomputable abbrev fsCoin : PublicCoin (decodedProtocol (C.FsCoins EF K) (C.publicCoin EF)
    (C.decoder EF K (C.coinCount EF K))) :=
  decoded (C.FsCoins EF K) (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))

/-- The challenges on a path of the batch at any admitted lengths: the lookup challenges, `α`,
`ζ`, the batching challenge, at most `twoAdicity F` folds and the queries. -/
def maxChallenges : ℕ := twoAdicity F + 5

/-- The duplex calls of the verifier's completion: at each of its at most `maxChallenges`
challenges, at most `coinCount` squeezes, each absorbing at most the inputs of the earlier
challenges' squeezes and its own. -/
def verifierChainQueries : ℕ :=
  maxChallenges (F := F) * (C.coinCount EF K * (maxChallenges (F := F) * C.coinCount EF K +
    C.coinCount EF K))

end CompStark.Iop.Batch.Statement
