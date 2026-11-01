/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Stark
public import CompStark.Fs.HashChain
public import ArkLib.Interaction.Oracle.Security.HashChainSqueeze

/-! # Knowledge soundness of the STARK on Plonky3's duplex challenger

The STARK's verifier as Plonky3 runs it on its duplex challenger, with the commitments as oracles:
the duplex is a random oracle on its capacity and the elements observed since the last squeeze,
answering a new capacity and `K` samples (`Fs.duplexSpec F K`), and the verifier draws every
challenge of the STARK's public-coin presentation from the squeezes Plonky3 makes for it
(`Statement.decoder`, `Statement.observer`): the duplex starts at the zero capacity, absorbs what
Plonky3 observes before each challenge, the committed words in full where Plonky3 observes their
Merkle caps, and squeezes as often as the challenge's samples take, with the empty input after the
first squeeze (`HashChain.squeezeExecution`).

`Statement.knowledgeSoundness_fs`: an adversary making at most `Q` duplex calls chooses the public
values and every prover message; the verifier's checks pass on the path its coins decode to while
no trace of the claimed length close to the committed one satisfies the AIR with probability at
most `chainError (Digest F) q + maxError · q + sumError` of the node errors (`Statement.nodeErrors`,
the calculator's terms) each multiplied by its draw's ratio (`Statement.ratio`: the grinding's
`powFraction` after `α`, and the query positions' bias), `q = Q + verifierChainQueries` the duplex
calls of the adversary and the verifier together. It needs `2 ^ 8 ≤ |F|` and two-adicity below
`2 ^ 64`, so that the domain separator tells the lengths apart.
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

/-- The coins of the STARK's challenges: `coinCount` squeezes of `K` samples. -/
abbrev FsCoins : Type := Coins F K (C.coinCount EF K)

/-- The STARK's decoded presentation, every challenge drawn from Plonky3's squeezes. -/
noncomputable abbrev fsCoin : PublicCoin (decodedProtocol (C.FsCoins EF K) (C.publicCoin EF)
    (C.decoder EF K (C.coinCount EF K))) :=
  decoded (C.FsCoins EF K) (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))

/-- The number of squeezes at each challenge of the STARK. -/
noncomputable abbrev fsSqueezes : Prefix PUnit (C.publicCoin EF) → ℕ :=
  (C.observer EF K (C.coinCount EF K)).squeezes (C.publicCoin EF)
    (C.decoder EF K (C.coinCount EF K))

/-- The chain inputs of a key: what Plonky3's verifier absorbs before the key's first squeeze, the
public values after the trace, and the inputs of the squeezes before it. -/
noncomputable abbrev fsEncode (key : Key (List F) PUnit fun _ ↦ C.fsCoin EF K) :
    List F × List (List F) :=
  (C.observer EF K (C.coinCount EF K)).encode id key

/-- The Fiat–Shamir game of the STARK on Plonky3's duplex challenger: the adversary queries the
duplex and selects public values and messages, and the verifier squeezes each challenge's coins
from the duplex, starting at the zero capacity. -/
noncomputable def fsGame (adversary : OracleComp (unifSpec + (duplexSpec F K + []ₒ))
    (Option (Selection (List F) PUnit PUnit fun _ ↦ C.fsCoin EF K))) :
    OracleComp (unifSpec + (duplexSpec F K + []ₒ))
      (Option (Outcome (List F) PUnit fun _ ↦ decodedProtocol (C.FsCoins EF K) (C.publicCoin EF)
        (C.decoder EF K (C.coinCount EF K)))) :=
  squeezeExecution initCap [] (fun _ ↦ C.decoder EF K (C.coinCount EF K))
    (fun _ ↦ C.fsSqueezes EF K) (C.fsEncode EF K) adversary

/-- The challenges on a path of the STARK at any admitted length: `α`, `ζ`, the batching challenge,
at most `twoAdicity F` folds and the queries. -/
def maxChallenges : ℕ := twoAdicity F + 4

/-- The duplex calls of the verifier's completion: at each of its at most `maxChallenges`
challenges, at most `coinCount` squeezes, each absorbing at most the inputs of the earlier
challenges' squeezes and its own. -/
def verifierChainQueries : ℕ :=
  maxChallenges (F := F) * (C.coinCount EF K * (maxChallenges (F := F) * C.coinCount EF K +
    C.coinCount EF K))

variable (δ δ' : ℕ → ℝ≥0)

/-- **Knowledge soundness of the STARK on Plonky3's duplex challenger.** On a base field of at
least `2 ^ 8` elements with two-adicity below `2 ^ 64`, against an adversary making at most `Q`
duplex calls that chooses the public values and every prover message, the verifier's checks pass
on the path its coins decode to while no trace of the claimed length close to the committed one
satisfies the AIR with probability at most `chainError (Digest F) q` plus `maxError * q + sumError`
of the node errors, each times its draw's ratio, `q = Q + verifierChainQueries`: FRI tests
proximity `δ n` and the extractor list-decodes at `δ' n` below `1 - rate`, at proximity loss
`loss n`. -/
theorem knowledgeSoundness_fs (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64)
    (hK : 0 < K) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (loss : C.Length → ℝ≥0)
    (adversary : OracleComp (unifSpec + (duplexSpec F K + []ₒ))
      (Option (Selection (List F) PUnit PUnit fun _ ↦ C.fsCoin EF K)))
    {Q : ℕ} (hQ : IsQueryBoundP adversary (fun t ↦ isChain t = true) Q) :
    Pr{let result ← (simulateQ (duplexSpec F K + []ₒ).romImpl
        (C.fsGame EF K adversary)).run' ∅}[
      ∃ publicValues path, result = some ⟨publicValues, path, PUnit.unit⟩ ∧
        ∃ p, decodePath (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K)) path = some p ∧
          evalWithAnswerFn (p.closingImpl (C.protocol EF).oracles noAccess noImpl)
            (C.terminal EF publicValues p.toBranchPath) = true ∧
          C.Far EF publicValues δ' p] ≤
      HashChain.chainError (Digest F) (Q + C.verifierChainQueries EF K) +
        (maxError (fun (_ : List F) node ↦ C.ratio EF node * C.nodeErrors EF δ δ' loss node) *
            (Q + C.verifierChainQueries EF K) +
          sumError (fun (_ : List F) node ↦ C.ratio EF node * C.nodeErrors EF δ δ' loss node)) := by
  have : NeZero (C.coinCount EF K) := ⟨fun h0 ↦ by
    have := le_squeezesFor_mul hK (Challenge.d EF + C.params.numQueries + 1)
    unfold coinCount at h0
    rw [h0, Nat.zero_mul] at this
    omega⟩
  have hN : ∀ _ : List F, (C.publicCoin EF).ChallengesLE (maxChallenges (F := F)) :=
    fun _ n ↦ (C.setup EF n).challengesLE_publicCoin
  have hq : IsQueryBoundP (C.fsGame EF K adversary) (fun t ↦ isChain t = true)
      (Q + C.verifierChainQueries EF K) :=
    isQueryBoundP_squeezeExecution initCap [] (fun _ ↦ C.decoder EF K (C.coinCount EF K))
      (fun _ ↦ C.fsSqueezes EF K) (C.fsEncode EF K) adversary hN
      (fun _ node ↦ squeezes_le node)
      (fun key ↦ Observer.length_encode_le _ (hN key.1) squeezes_le id key) hQ
  have h := KnowledgeCertificate.chainSqueeze_knowledge_soundness initCap []
    (fun _ ↦ C.publicCoin EF) (fun _ ↦ C.decoder EF K (C.coinCount EF K)) (fun _ ↦ C.ratio EF)
    (fun _ ↦ bounded_decoder hK) (fun _ ↦ C.fsSqueezes EF K) (fun _ node ↦ squeezes_le node)
    (fun _ ↦ reads_decoder _ hK) (C.fsEncode EF K)
    (fun key key' hk hk' he ↦ Observer.encode_injective _ (observer_prefixFree _ h8 h64) id
      Function.injective_id key key' hk hk' he)
    (fun key hk ↦ Observer.encode_fst_ne_nil _ (observer_fills _) id key hk)
    (fun publicValues ↦ C.rootState EF publicValues δ')
    (fun publicValues ↦ certificate EF publicValues δ δ' hδ' loss)
    (fun publicValues ↦ uniformChallenges_certificate EF publicValues δ δ' hδ' loss)
    adversary hq
  have herr (publicValues : List F) (node : Prefix PUnit (C.publicCoin EF)) :
      supErrors (C.publicCoin EF) (certificate EF publicValues δ δ' hδ' loss).challenges node =
        C.nodeErrors EF δ δ' loss node :=
    congrFun ((C.setup EF node.1).supErrors_certificate publicValues (δ node.1.1) (δ' node.1.1) _
      (loss node.1)) node.2
  simp only [herr, Nat.cast_add] at h
  refine (prEvent_mono _ _ _ fun result hres ↦ ?_).trans h
  obtain ⟨publicValues, path, rfl, p, hp, hacc, hfar⟩ := hres
  obtain ⟨w, hw⟩ := (C.setup EF p.1).terminal_holds_of_eval publicValues (δ p.1.1) (δ' p.1.1) _
    (loss p.1) p.2 hacc
  exact ⟨publicValues, path, PUnit.unit, rfl, p, hp, w, hw, fun hroot ↦ hfar _ hroot.1 hroot.2⟩

end CompStark.Iop.Statement
