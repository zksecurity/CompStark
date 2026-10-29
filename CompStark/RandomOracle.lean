/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Verifier
public import CompStark.Stark.Setup
public import CompStark.Iop
public import CompStark.Merkle.Extract
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-! # The random-oracle model

The verifier uses hashes three ways: as the duplex challenger, the Merkle leaf hash and the Merkle
compression (Poseidon2 in Plonky3). Here each is a random oracle with 8-element digests, and the
verifier runs on them through its primitives interface (`Primitives`, `Stark.verifyWith`):

* `Query`, `spec K`: a duplex call takes the capacity and the elements observed since the last
  squeeze, and answers a new capacity and a stream of `K` samples. The leaf hash takes a row and
  the compression two digests; both answer a digest.
* `ideal K`: the primitives on these oracles. The challenger keeps a capacity, the pending input
  and the samples left; observing appends to the input and drops the samples, and a sample with
  none left queries the duplex oracle. `idealOf answer` is the same on a fixed answer function.
* `Setup.streamLen`, `Statement.streamLen`: the stream is long enough that every challenge round
  takes one answer, the query round's grinding sample and indices included, at every trace length.
* `Statement.NIProver`, `Statement.run`: a prover is an oracle computation that outputs a proof,
  of the trace length it chooses. The game computes the verifying key of the AIR's preprocessed
  trace on the oracles (`Statement.setupRo`), runs the prover, logging both's queries, and then
  Plonky3's verifier on the prover's proof against that key, against one lazy random oracle. The
  verifier takes the trace length from the proof, and makes at most `verifierCallsAt` oracle
  calls at that length; the setup and the verifier together make at most
  `Statement.verifierQueries` calls.
* `committedTrace`: the trace words a proof commits to, read off the logged hash queries.
-/

@[expose] public section
namespace CompStark.RandomOracle
open CompStark.Stark OracleSpec OracleComp

/-- The verifier's oracle calls: the challenger's duplexing (the capacity and the input since the
last squeeze), the Merkle leaf hash of a row, and the compression of two digests. -/
inductive Query (F : Type) where
  | duplex (cap : Digest F) (input : List F)
  | leaf (row : List F)
  | node (left right : Digest F)
deriving DecidableEq

/-- The answers: a new capacity and `K` samples for a duplex call, a digest for a hash. -/
abbrev Answer {F : Type} (K : Nat) : Query F → Type
  | .duplex .. => Digest F × Vector F K
  | .leaf _ | .node .. => Digest F

/-- The random oracles of the verifier, with streams of `K` samples. -/
abbrev spec (F : Type) (K : Nat) : OracleSpec (Query F) := OracleSpec.ofFn (Answer K)

/-- The challenger's state: the capacity, the elements observed since the last squeeze, and the
samples of the last squeeze not taken yet. -/
structure Sponge (F : Type) where
  cap : Digest F
  input : List F
  samples : List F

/-- The initial capacity. -/
def initCap {F : Type} [Zero F] : Digest F := Vector.replicate 8 0

/-- The primitives on oracle answers `ask` in a monad `m`. -/
abbrev withAnswers {F : Type} [Zero F] {m : Type → Type} [Monad m] (K : Nat)
    (ask : (q : Query F) → m (Answer K q)) : Primitives F m where
  State := Sponge F
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
abbrev ideal (F : Type) [Zero F] (K : Nat) : Primitives F (OracleComp (spec F K)) :=
  withAnswers K fun q ↦ liftM ((spec F K).query q)

/-- The verifier's primitives on a fixed answer to every query. -/
abbrev idealOf {F : Type} [Zero F] {K : Nat} (answer : (q : Query F) → Answer K q) :
    Primitives F Id :=
  withAnswers K fun q ↦ pure (answer q)

/-- Uniform answers. -/
noncomputable instance {F : Type} [BaseField F] (K : Nat) : ∀ q, SampleableType ((spec F K).Range q)
  | .duplex .. | .leaf _ | .node .. => inferInstance

end RandomOracle

namespace Iop
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The committed rounds the verifier opens at every query: the trace, the quotient, and the
preprocessed trace if the AIR has one. -/
def inputRoundsOf (A : Air F) : Nat := if A.preprocessedWidth = 0 then 2 else 3

variable (EF) in
/-- The verifier's oracle calls on a proof for `2 ^ n` rows, at most one per sample (`α`, `ζ` and
the batching challenge take `d` samples each, the out-of-domain and batching grinding one each,
every fold a grinding sample and `d` for `β`, the query round a grinding sample), and per query
its index and its paths, a leaf hash and a compression per layer of `L`, in the multi-openings of
the committed rounds and every fold. -/
def verifierCallsAt (P : Fri.Params) (A : Air F) (n : Nat) : Nat :=
  let arities := Fri.foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
    (n + P.logBlowup) [n + P.logBlowup]
  3 * Challenge.d EF + 3 + (Challenge.d EF + 1) * arities.length +
    P.numQueries * (1 + (arities.length + inputRoundsOf A) * (1 + (n + P.logBlowup)))

namespace Setup
variable (S : Setup EF)

/-- The samples in one duplex answer, enough for every round: the rounds of `ζ`, of the batching
challenge and of every fold take a grinding sample and `d` for the challenge, the query round a
grinding sample and one index per query. -/
def streamLen : Nat := S.params.numQueries + Challenge.d EF + 1

/-- The oracle calls of the verifying key's computation: a leaf hash per row of the preprocessed
trace's extension and a compression per inner node, none without preprocessed columns. -/
def setupQueries : Nat := if S.air.preprocessedWidth = 0 then 0 else 2 * S.size - 1

/-- The verifying key of the AIR's preprocessed trace for `2 ^ logN` rows on the random
oracles. -/
def setupRo : OracleComp (spec F S.streamLen) (Option (PreprocessedKey F)) :=
  preprocessedKeyWith (ideal F S.streamLen) S.params S.air S.logN

end Setup

namespace Statement
variable (C : Statement F)

variable (EF) in
/-- The samples in one duplex answer (`Setup.streamLen`), at every trace length. -/
def streamLen : Nat := C.params.numQueries + Challenge.d EF + 1

/-- The oracle calls of the verifying key's computation, at the preprocessed trace's length: none
without preprocessed columns. -/
def setupQueries : Nat :=
  if C.air.preprocessedWidth = 0 then 0
  else 2 * 2 ^ (C.preprocessedLogN + C.params.logBlowup) - 1

variable (EF) in
/-- The verifier's oracle calls on a proof of any length: none on a proof whose quotient domain
is not below the two-adicity, so at most `verifierCallsAt` at one of the lengths up to it. -/
def verifierCallsMax : Nat :=
  ((List.range (twoAdicity F + 1)).map (verifierCallsAt EF C.params C.air)).foldr max 0

variable (EF) in
/-- The oracle calls of the verifying key's computation and of the verifier. -/
def verifierQueries : Nat := C.setupQueries + C.verifierCallsMax EF

variable (EF) in
/-- The verifying key of the AIR's preprocessed trace on the random oracles. -/
def setupRo : OracleComp (spec F (C.streamLen EF)) (Option (PreprocessedKey F)) :=
  preprocessedKeyWith (ideal F (C.streamLen EF)) C.params C.air C.preprocessedLogN

variable (EF) in
/-- A non-interactive prover: a computation with oracle access to the hashes that outputs a proof,
of the trace length it chooses. Provers are deterministic; a randomized prover is a mixture of
deterministic ones. -/
abbrev NIProver := OracleComp (spec F (C.streamLen EF)) (Proof F EF)

/-- Compute the verifying key and run `prover`, logging their queries, then Plonky3's verifier on
the proof against the key, against one random oracle. -/
noncomputable def run (publicValues : List F) (prover : C.NIProver EF) :
    ProbComp (Proof F EF × QueryLog (spec F (C.streamLen EF)) × Except String Unit) :=
  (simulateQ randomOracle do
    let ((vk, proof), log) ← (simulateQ loggingOracle do
      let vk ← C.setupRo EF
      return (vk, ← prover)).run
    return (proof, log,
      ← verifyWith (ideal F (C.streamLen EF)) C.params C.air vk proof publicValues)).run' ∅

end Statement

/-- The hash queries of a log, as a Merkle cache. -/
def logCache {K : Nat} (log : QueryLog (spec F K)) : Merkle.Cache F (Digest F) where
  leaf row y := ⟨.leaf row, y⟩ ∈ log
  node left right y := ⟨.node left right, y⟩ ∈ log

/-- The trace words committed under `proof.traceCommit`, read off the hash queries of `log`: the
row of the tree on `L` under the cap at the leaf of each point (Plonky3's bit-reversed order), zero
where `log` holds no preimage. -/
noncomputable def committedTrace (S : Setup EF) (log : QueryLog (spec F S.streamLen))
    (proof : Proof F EF) :
    Fin S.air.width → S.Point → F := fun column point ↦
  let depth := S.logN + S.params.logBlowup
  match Merkle.extractCapRow (logCache log) depth S.params.capHeight (reverseBits point depth)
      proof.traceCommit.toList with
  | some row => row.getD column 0
  | none => 0

end CompStark.Iop
