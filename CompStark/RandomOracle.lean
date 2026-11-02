/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Verifier
public import CompStark.Stark.Setup
public import CompStark.Interaction.StarkSetup
public import CompStark.Merkle.Extract
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-! # The verifier's random oracles

The verifier uses hashes three ways: as the duplex challenger, the Merkle leaf hash and the Merkle
compression (Poseidon2 in Plonky3). Here each is a random oracle with 8-element digests, and the
verifier runs on them through its primitives interface (`Primitives`, `Stark.verifyWith`):

* `Query`, `spec K`: a duplex call takes the capacity and the elements observed since the last
  squeeze, and answers a new capacity and a stream of `K` samples. The leaf hash takes a row and
  the compression two digests; both answer a digest.
* `ideal K`: the primitives on these oracles. The challenger keeps a capacity, the pending input
  and the samples left; observing appends to the input and drops the samples, and a sample with
  none left queries the duplex oracle. `withAnswers` is the same on answers in any monad, and
  `idealOf answer` on a fixed answer function.
* `verifierCallsAt`: the verifier makes at most so many oracle calls on a proof for `2 ^ n` rows;
  with the verifying key's computation (`Statement.setupQueries`), at most
  `Statement.verifierQueries` calls on a proof of any length.
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

end Setup

namespace Statement
variable (C : Statement F)

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

end Statement

end CompStark.Iop
