/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Batch
public import CompStark.Fs.StarkFiatShamir

/-! # Knowledge soundness of the batch STARK on Plonky3's duplex challenger

The batch STARK's verifier as Plonky3 runs it on its duplex challenger, with the commitments as
oracles: the duplex is a random oracle on its capacity and the elements observed since the last
squeeze, answering a new capacity and `K` samples (`Fs.duplexSpec F K`), and the verifier draws
every challenge of the batch's public-coin presentation from the squeezes Plonky3 makes for it
(`Batch.Statement.decoder`, `Batch.Statement.observer`): the duplex starts at the zero capacity,
absorbs what Plonky3 observes before each challenge, the committed words in full where Plonky3
observes their Merkle caps, and the public values (`Batch.C.tail`) at the first squeeze,
and squeezes as often as the challenge's samples take, with the empty input after the first
squeeze (`HashChain.squeezeExecution`).

`Batch.Statement.knowledgeSoundness_fs`: an adversary making at most `Q` duplex calls chooses the
public values of the checked lengths and every prover message; the verifier's checks pass on the
path its coins decode to while no tuple of traces of the claimed lengths close to the committed
ones satisfies the batch with probability at most `chainError (Digest F) q + maxError · q +
sumError` of the node errors (`Batch.Statement.nodeErrors`) each multiplied by its draw's ratio
(`Batch.Statement.ratio`), `q = Q + verifierChainQueries` the duplex calls of the adversary and
the verifier together.
-/

@[expose] public section
namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Sound CompStark.Fs _root_.Interaction.Oracle
open _root_.Interaction.Oracle.PublicCoin _root_.Interaction.Oracle.Security

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

/-- The batch's paths have at most `twoAdicity F + 5` challenges: the lookup challenges, `α`, `ζ`,
the batching challenge, FRI's folds, at most the tallest domain's log size, and the queries. -/
theorem challengesLE_publicCoin {withLookups : Bool} (S : Setup EF withLookups) :
    S.publicCoin.ChallengesLE (twoAdicity F + 5) := by
  have hf := S.domainSetup.numFolds_friSchedule_le S.friHeights
  exact ⟨by omega, fun _ ↦ ⟨by omega, by omega, fun _ ↦ ⟨by omega, challengesLE_mono _
    (challengesLE_friPublicCoin _ _ _ (S.domainSetup.friSchedule S.friHeights)) (by omega)⟩⟩⟩

/-- The batch's draws read only their squeezes. -/
theorem reads_decoder (S : Setup EF) (hK : 0 < K) :
    HashChain.Decoder.Reads S.publicCoin (S.decoder K m)
      ((S.observer K m).squeezes S.publicCoin (S.decoder K m)) :=
  fun _ ↦ ⟨fun c c' h ↦ reads_lookupDraw hK _ _ c c' h, fun _ _ ↦
    ⟨fun c c' h ↦ reads_extDraw hK 0 c c' h, fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK _ c c' h,
      fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK _ c c' h,
        reads_friDecoder K m hK (S.domainSetup.friSchedule S.friHeights) _⟩⟩⟩⟩

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs CompStark.RandomOracle OracleComp OracleSpec
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security _root_.Interaction.Oracle.Security.StateRestoration
open _root_.Interaction.Oracle.Security.HashChain
open _root_.Interaction.Oracle.TypeTree
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

variable {C EF K} in
/-- Each draw reads only its squeezes. -/
theorem reads_decoder (m : ℕ) (hK : 0 < K) :
    HashChain.Decoder.Reads (C.publicCoin EF) (C.decoder EF K m)
      ((C.observer EF K m).squeezes (C.publicCoin EF) (C.decoder EF K m)) :=
  fun n ↦ (C.setup EF n).reads_decoder hK

/-- The coins of the batch's challenges: `coinCount` squeezes of `K` samples. -/
abbrev FsCoins : Type := Coins F K (C.coinCount EF K)

/-- The batch's decoded presentation, every challenge drawn from Plonky3's squeezes. -/
noncomputable abbrev fsCoin : PublicCoin (decodedProtocol (C.FsCoins EF K) (C.publicCoin EF)
    (C.decoder EF K (C.coinCount EF K))) :=
  decoded (C.FsCoins EF K) (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))

/-- The number of squeezes at each challenge of the batch. -/
noncomputable abbrev fsSqueezes : Prefix PUnit (C.publicCoin EF) → ℕ :=
  (C.observer EF K (C.coinCount EF K)).squeezes (C.publicCoin EF)
    (C.decoder EF K (C.coinCount EF K))

/-- The chain inputs of a key: what Plonky3's verifier absorbs before the key's first squeeze, the
public values after the main trace, and the inputs of the squeezes before it. -/
noncomputable abbrev fsEncode (key : Key C.PublicValues PUnit fun _ ↦ C.fsCoin EF K) :
    List F × List (List F) :=
  (C.observer EF K (C.coinCount EF K)).encode C.tail key

/-- The Fiat–Shamir game of the batch STARK on Plonky3's duplex challenger: the adversary queries
the duplex and selects public values and messages, and the verifier squeezes each challenge's
coins from the duplex, starting at the zero capacity. -/
noncomputable def fsGame (adversary : OracleComp (unifSpec + (duplexSpec F K + []ₒ))
    (Option (Selection C.PublicValues PUnit PUnit fun _ ↦ C.fsCoin EF K))) :
    OracleComp (unifSpec + (duplexSpec F K + []ₒ))
      (Option (Outcome C.PublicValues PUnit fun _ ↦ decodedProtocol (C.FsCoins EF K)
        (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K)))) :=
  squeezeExecution initCap [] (fun _ ↦ C.decoder EF K (C.coinCount EF K))
    (fun _ ↦ C.fsSqueezes EF K) (C.fsEncode EF K) adversary

/-- The challenges on a path of the batch at any admitted lengths: the lookup challenges, `α`,
`ζ`, the batching challenge, at most `twoAdicity F` folds and the queries. -/
def maxChallenges : ℕ := twoAdicity F + 5

/-- The duplex calls of the verifier's completion: at each of its at most `maxChallenges`
challenges, at most `coinCount` squeezes, each absorbing at most the inputs of the earlier
challenges' squeezes and its own. -/
def verifierChainQueries : ℕ :=
  maxChallenges (F := F) * (C.coinCount EF K * (maxChallenges (F := F) * C.coinCount EF K +
    C.coinCount EF K))

variable (δ δ' : (Fin C.k → ℕ) → ℝ≥0)

/-- **Knowledge soundness of the batch STARK on Plonky3's duplex challenger.** Against an
adversary making at most `Q` duplex calls that chooses the public values of the checked lengths
and every prover message, the verifier's checks pass on the path its coins decode to while no
tuple of traces of the claimed lengths close to the committed ones satisfies the batch with
probability at most `chainError (Digest F) q` plus `maxError * q + sumError` of the node errors,
each times its draw's ratio, `q = Q + verifierChainQueries`: FRI tests proximity `δ n` and the
extractor list-decodes at `δ' n` below `1 - rate`, at proximity loss `loss n`. -/
theorem knowledgeSoundness_fs (hK : 0 < K) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0)
    (adversary : OracleComp (unifSpec + (duplexSpec F K + []ₒ))
      (Option (Selection C.PublicValues PUnit PUnit fun _ ↦ C.fsCoin EF K)))
    {Q : ℕ} (hQ : IsQueryBoundP adversary (fun t ↦ isChain t = true) Q) :
    Pr{let result ← (simulateQ (duplexSpec F K + []ₒ).romImpl
        (C.fsGame EF K adversary)).run' ∅}[
      ∃ publicValues path, result = some ⟨publicValues, path, PUnit.unit⟩ ∧
        ∃ p, decodePath (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K)) path = some p ∧
          evalWithAnswerFn (p.closingImpl (C.protocol EF).oracles noAccess noImpl)
            (C.terminal EF publicValues.1 p.toBranchPath) = true ∧
          C.Far EF publicValues.1 δ' p] ≤
      HashChain.chainError (Digest F) (Q + C.verifierChainQueries EF K) +
        (maxError (fun (_ : C.PublicValues) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss node) *
            (Q + C.verifierChainQueries EF K) +
          sumError (fun (_ : C.PublicValues) node ↦
            C.ratio EF node * C.nodeErrors EF δ δ' loss node)) := by
  have : NeZero (C.coinCount EF K) := ⟨fun h0 ↦ by
    have := le_squeezesFor_mul hK (2 * Challenge.d EF + C.params.numQueries + 1)
    unfold coinCount at h0
    rw [h0, Nat.zero_mul] at this
    omega⟩
  have hN : ∀ _ : C.PublicValues, (C.publicCoin EF).ChallengesLE (maxChallenges (F := F)) :=
    fun _ n ↦ (C.setup EF n).challengesLE_publicCoin
  have hq : IsQueryBoundP (C.fsGame EF K adversary) (fun t ↦ isChain t = true)
      (Q + C.verifierChainQueries EF K) :=
    isQueryBoundP_squeezeExecution initCap [] (fun _ ↦ C.decoder EF K (C.coinCount EF K))
      (fun _ ↦ C.fsSqueezes EF K) (C.fsEncode EF K) adversary hN
      (fun _ node ↦ squeezes_le node)
      (fun key ↦ Observer.length_encode_le _ (hN key.1) squeezes_le C.tail key) hQ
  have h := KnowledgeCertificate.chainSqueeze_knowledge_soundness initCap []
    (fun _ ↦ C.publicCoin EF) (fun _ ↦ C.decoder EF K (C.coinCount EF K)) (fun _ ↦ C.ratio EF)
    (fun _ ↦ bounded_decoder hK) (fun _ ↦ C.fsSqueezes EF K) (fun _ node ↦ squeezes_le node)
    (fun _ ↦ reads_decoder _ hK) (C.fsEncode EF K)
    (fun key key' hk hk' he ↦ Observer.encode_injective _ (observer_prefixFree _)
      C.tail tail_injective key key' hk hk' he)
    (fun key hk ↦ Observer.encode_fst_ne_nil _ (observer_fills _) C.tail key hk)
    (fun publicValues ↦ C.rootState EF publicValues.1 δ')
    (fun publicValues ↦ certificate EF publicValues.1 δ δ' hδ' loss)
    (fun publicValues ↦ uniformChallenges_certificate EF publicValues.1 δ δ' hδ' loss)
    adversary hq
  have hle (publicValues : C.PublicValues) (node : Prefix PUnit (C.publicCoin EF)) :
      C.ratio EF node * supErrors (C.publicCoin EF)
        (certificate EF publicValues.1 δ δ' hδ' loss).challenges node ≤
        C.ratio EF node * C.nodeErrors EF δ δ' loss node := by
    gcongr
    exact (C.setup EF node.1).supErrors_certificate_le publicValues.1 (δ node.1.1) (δ' node.1.1)
      _ (loss node.1) node.2
  simp only [Nat.cast_add] at h
  refine (prEvent_mono _ _ _ fun result hres ↦ ?_).trans (h.trans ?_)
  · obtain ⟨publicValues, path, rfl, p, hp, hacc, hfar⟩ := hres
    obtain ⟨w, hw⟩ := (C.setup EF p.1).terminal_holds_of_eval publicValues.1 (δ p.1.1)
      (δ' p.1.1) (hδ' p.1.1 p.1.2) (loss p.1) p.2 hacc
    exact ⟨publicValues, path, PUnit.unit, rfl, p, hp, w, hw, fun hroot ↦ hfar _ hroot.1 hroot.2⟩
  · gcongr
    · exact maxError_mono hle
    · exact sumError_mono hle

end CompStark.Iop.Batch.Statement
