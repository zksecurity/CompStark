/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Challenger
public import CompStark.Stark.Proof

/-! # The verifier's primitives

The STARK verifier (`Stark.verifyWith`) uses three hash functions: a Fiat–Shamir challenger and
the Merkle leaf hash and compression. `Primitives m` gives all three, with results in a monad `m`,
so that the same verifier code runs on Poseidon2 (`poseidon2`, `m = Id`) and on random oracles
(`m` an oracle computation).

* `observe` absorbs one base element into the challenger's state. It is pure: an implementation
  that permutes on a full buffer does so deterministically.
* `sample` squeezes one base element. Extension elements, query indices and grinding checks are
  built from it by the verifier (`Fri.sampleExt`, `Fri.sampleBits`, `Fri.checkWitness`).
* `hash` and `compress` are the Merkle tree's leaf hash and two-to-one compression.
-/

@[expose] public section
namespace CompStark
open CompStark.Stark (Digest)

local notation "F" => KoalaBear.Fast.Field

/-- The primitives the verifier runs on, with results in a monad `m`: a challenger over KoalaBear
with its state, and the Merkle leaf hash and compression. -/
structure Primitives (m : Type → Type) where
  /-- The challenger's state. -/
  State : Type
  /-- The challenger before any observation. -/
  init : State
  /-- Absorb one element. -/
  observe : State → F → State
  /-- Squeeze one element. -/
  sample : State → m (F × State)
  /-- The Merkle leaf hash of a row. -/
  hash : List F → m Digest
  /-- The Merkle compression of two digests. -/
  compress : Digest → Digest → m Digest

/-- Plonky3's primitives over KoalaBear: the duplex challenger on the width-24 Poseidon2
permutation, as in the transcript the prover shares (its grinder is not used by the verifier), and
the Poseidon2 Merkle hash and compression. -/
abbrev poseidon2 : Primitives Id where
  State := KoalaBear.Transcript
  init := KoalaBear.Transcript.init
  observe := KoalaBear.Transcript.observe
  sample t := pure t.sample
  hash xs := pure (Hash.KoalaBear.hash F xs)
  compress a b := pure (Hash.KoalaBear.compress F a b)

end CompStark
