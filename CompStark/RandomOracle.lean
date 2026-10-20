/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Verifier
public import CompStark.Iop
public import CompStark.Merkle.Extract
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-! # The random-oracle model

`verify` uses Poseidon2 three ways: as the duplex challenger, the Merkle leaf hash and the Merkle
compression. Here each is a random oracle with 8-element digests, and the verifier runs on them
through its primitives interface (`Primitives`, `Stark.verifyWith`):

* `Query`, `spec K`: a duplex call takes the capacity and the elements observed since the last
  squeeze, and answers a new capacity and a stream of `K` samples. The leaf hash takes a row and
  the compression two digests; both answer a digest.
* `ideal K`: the primitives on these oracles. The challenger keeps a capacity, the pending input
  and the samples left; observing appends to the input and drops the samples, and a sample with
  none left queries the duplex oracle. `idealOf answer` is the same on a fixed answer function.
* `Setup.streamLen`: the stream is long enough that every challenge round takes one answer, the
  query round's grinding sample and indices included.
* `NIProver`, `run`: a prover is an oracle computation that outputs a proof. The game runs it,
  logging its queries, and then the verifier on its proof, against one lazy random oracle. The
  verifier trusts `proof.degreeBits`, and its oracle calls grow with it, so the game rejects proofs
  for other trace lengths up front (`Setup.verifyRo`); it makes at most `Setup.verifierQueries`
  calls.
* `committedTrace`: the trace words a proof commits to, read off the prover's hash queries.
-/

@[expose] public section
namespace CompStark.RandomOracle
open CompStark.Stark OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field

/-- The verifier's oracle calls: the challenger's duplexing (the capacity and the input since the
last squeeze), the Merkle leaf hash of a row, and the compression of two digests. -/
inductive Query where
  | duplex (cap : Digest) (input : List F)
  | leaf (row : List F)
  | node (left right : Digest)
deriving DecidableEq

/-- The answers: a new capacity and `K` samples for a duplex call, a digest for a hash. -/
abbrev Answer (K : Nat) : Query → Type
  | .duplex .. => Digest × Vector F K
  | .leaf _ | .node .. => Digest

/-- The random oracles of the verifier, with streams of `K` samples. -/
abbrev spec (K : Nat) : OracleSpec Query := OracleSpec.ofFn (Answer K)

/-- The challenger's state: the capacity, the elements observed since the last squeeze, and the
samples of the last squeeze not taken yet. -/
structure Sponge where
  cap : Digest
  input : List F
  samples : List F

/-- The initial capacity. -/
def initCap : Digest := Vector.replicate 8 0

/-- The primitives on oracle answers `ask` in a monad `m`. -/
abbrev withAnswers {m : Type → Type} [Monad m] (K : Nat) (ask : (q : Query) → m (Answer K q)) :
    Primitives m where
  State := Sponge
  init := ⟨initCap, [], []⟩
  observe s x := ⟨s.cap, s.input ++ [x], []⟩
  sample s := match s.samples with
    | x :: rest => pure (x, ⟨s.cap, s.input, rest⟩)
    | [] => do
      let (cap, stream) ← ask (.duplex s.cap s.input)
      return (stream.toList.headD 0, ⟨cap, [], stream.toList.tail⟩)
  hash row := ask (.leaf row)
  compress left right := ask (.node left right)

/-- The verifier's primitives on the random oracles. -/
abbrev ideal (K : Nat) : Primitives (OracleComp (spec K)) :=
  withAnswers K fun q ↦ liftM ((spec K).query q)

/-- The verifier's primitives on a fixed answer to every query. -/
abbrev idealOf {K : Nat} (answer : (q : Query) → Answer K q) : Primitives Id :=
  withAnswers K fun q ↦ pure (answer q)

noncomputable instance : Fintype F := Fintype.ofEquiv _ KoalaBear.Fast.ringEquiv.symm.toEquiv

noncomputable instance : SampleableType F := SampleableType.ofFintype F

/-- Uniform answers. -/
noncomputable instance (K : Nat) : ∀ q, SampleableType ((spec K).Range q)
  | .duplex .. | .leaf _ | .node .. => inferInstance

end RandomOracle

namespace Iop
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

local notation "𝔽" => KoalaBear.Field
local notation "F" => KoalaBear.Fast.Field

variable {EF : Type} [Challenge EF]

namespace Setup
variable (S : Setup EF)

/-- The samples in one duplex answer, enough for every round: a fold takes a grinding sample and
`d` for `β`, the query round a grinding sample and one index per query. -/
def streamLen : Nat := S.params.numQueries + Challenge.d EF + 1

/-- Plonky3's fold arities for `S`, as the verifier checks them. -/
abbrev friArities : List Nat :=
  Fri.foldArities S.params.maxLogArity (S.logN - S.params.logFinalPolyLen)

/-- The oracle calls of one Merkle opening on `L`: the leaf hash and one compression per layer. -/
def openingQueries : Nat := 1 + (S.logN + S.params.logBlowup)

/-- The verifier's oracle calls on a proof for `S`, at most one per sample (`α`, `ζ` and the
batching challenge take `d` samples each, every fold a grinding sample and `d` for `β`, the
query round a grinding sample), and per query its index and the openings of the trace, the
quotient and every fold. -/
def verifierQueries : Nat :=
  3 * Challenge.d EF + 1 + (Challenge.d EF + 1) * S.friArities.length +
    S.params.numQueries * (1 + (S.friArities.length + 2) * S.openingQueries)

/-- The verifier in the random-oracle model, on proofs for `2 ^ logN` rows. -/
def verifyRo (proof : Proof EF) (publicValues : List F) :
    OracleComp (spec S.streamLen) (Except String Unit) :=
  if proof.degreeBits = S.logN then
    verifyWith (ideal S.streamLen) S.params S.air proof publicValues
  else pure (.error "degree bits")

end Setup

/-- A non-interactive prover for `S`: a computation with oracle access to the hashes that outputs
a proof. Provers are deterministic; a randomized prover is a mixture of deterministic ones. -/
abbrev NIProver (S : Setup EF) := OracleComp (spec S.streamLen) (Proof EF)

/-- Run `prover`, logging its queries, then the verifier on its proof, against one random
oracle. -/
noncomputable def run (S : Setup EF) (publicValues : List F) (prover : NIProver S) :
    ProbComp (Proof EF × QueryLog (spec S.streamLen) × Except String Unit) :=
  (simulateQ randomOracle do
    let (proof, log) ← (simulateQ loggingOracle prover).run
    return (proof, log, ← S.verifyRo proof publicValues)).run' ∅

/-- The hash queries of a log, as a Merkle cache. -/
def logCache {K : Nat} (log : QueryLog (spec K)) : Merkle.Cache F Digest where
  leaf row y := ⟨.leaf row, y⟩ ∈ log
  node left right y := ⟨.node left right, y⟩ ∈ log

/-- The trace words committed under `proof.traceCommit`, read off the hash queries of `log`: the
row of the tree on `L` at the leaf of each point (Plonky3's bit-reversed order), zero where `log`
holds no preimage. -/
noncomputable def committedTrace (S : Setup EF) (log : QueryLog (spec S.streamLen))
    (proof : Proof EF) :
    Fin S.air.width → S.Point → 𝔽 := fun column point ↦
  let depth := S.logN + S.params.logBlowup
  match Merkle.extractRow (logCache log) depth (reverseBits point depth) proof.traceCommit with
  | some row => KoalaBear.Fast.ringEquiv (row.getD column 0)
  | none => 0

end CompStark.Iop
