/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.RandomOracle
public import CompStark.Iop.StarkError
public import CompStark.Fs.Samples
public import ArkLib.Interaction.Oracle.Security.HashChain

/-! # Plonky3's duplex challenger is a hash chain

The verifier's duplex oracle (`RandomOracle.Query.duplex`) is a chain oracle in the sense of
ArkLib's `HashChain`: the state is the capacity, the input is the list of elements observed
since the last squeeze, and the output is the squeeze's `K` samples (`duplexSpec`). The
challenger starts at the zero capacity and queries each squeeze at the capacity the previous
squeeze answered: its capacity after the squeezes of the blocks `bs` is `capOf answer bs`.

`merkleSpec`, `translate`: the verifier's other oracles, the leaf hash and the compression, are
the extra oracles next to the chain (`sumSpec`); `translate` reads every query of `spec F K` as a
chain query or a Merkle hash, and keeps a bound on the duplex calls (`isDuplex`,
`isQueryBoundP_translate`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp
open Interaction.Oracle.Security
open scoped ENNReal

variable {F : Type} {K : Nat}

/-! ### The challenger's capacities -/

/-- The capacity after squeezing the blocks `bs`, latest first, on the duplex answers
`answer`: the zero capacity for none, the capacity answered at the latest squeeze otherwise. -/
def capOf [Zero F] (answer : (q : Query F) → Answer K q) : List (List F) → Digest F
  | [] => initCap
  | b :: bs => (answer (.duplex (capOf answer bs) b)).1

/-! ### The verifier's oracles as a chain and Merkle hashes -/

/-- The duplex oracle as a chain oracle: the capacity is the state, the elements observed since
the last squeeze are the input, and the squeeze's samples the output. -/
abbrev duplexSpec (F : Type) (K : Nat) : OracleSpec (Digest F × List F) :=
  HashChain.chainSpec (Digest F) (List F) (Vector F K)

/-- The Merkle hashes: a row's leaf hash, and the compression of two digests. -/
abbrev merkleSpec (F : Type) : OracleSpec (List F ⊕ (Digest F × Digest F)) :=
  (List F ⊕ (Digest F × Digest F)) →ₒ Digest F

/-- The duplex calls and the Merkle hashes. -/
abbrev sumSpec (F : Type) (K : Nat) := duplexSpec F K + merkleSpec F

/-- The verifier's oracle calls as chain queries and Merkle hashes. -/
def translate : QueryImpl (spec F K) (OracleComp (unifSpec + sumSpec F K))
  | .duplex cap input => liftM ((unifSpec + sumSpec F K).query (.inr (.inl (cap, input))))
  | .leaf row => liftM ((unifSpec + sumSpec F K).query (.inr (.inr (.inl row))))
  | .node left right => liftM ((unifSpec + sumSpec F K).query (.inr (.inr (.inr (left, right)))))

/-- Whether a call is a duplex call. -/
def isDuplex : Query F → Bool
  | .duplex .. => true
  | _ => false

variable [BaseField F]

omit [BaseField F] in
/-- A program making at most `Q` duplex calls makes at most `Q` chain queries through
`translate`. -/
theorem isQueryBoundP_translate {α : Type} {A : OracleComp (spec F K) α} {Q : ℕ}
    (hQ : IsQueryBoundP A (fun q => isDuplex q = true) Q) :
    IsQueryBoundP (simulateQ translate A) (fun t => HashChain.isChain t = true) Q := by
  refine hQ.simulateQ_of_step (fun q hq => ?_) (fun q hq => ?_)
  · rcases q with ⟨cap, input⟩ | row | ⟨left, right⟩
    · simp only [translate]
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · cases hq
    · cases hq
  · rcases q with ⟨cap, input⟩ | row | ⟨left, right⟩
    · exact absurd rfl hq
    · simp only [translate]
      rw [isQueryBoundP_query_iff]
      simp [HashChain.isChain]
    · simp only [translate]
      rw [isQueryBoundP_query_iff]
      simp [HashChain.isChain]

end CompStark.Fs
