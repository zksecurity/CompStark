/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Proof

/-! # The verifier's primitives

The STARK verifier (`Stark.verifyWith`) uses three hash functions: a Fiat–Shamir challenger and
the Merkle leaf hash and compression. `Primitives m` gives all three, with results in a monad `m`,
so that the same verifier code runs on concrete hashes (Plonky3's Poseidon2, `m = Id`) and on
random oracles (`m` an oracle computation).

* `observe` absorbs one base element into the challenger's state. It is pure: an implementation
  that permutes on a full buffer does so deterministically.
* `sample` squeezes one base element. Extension elements, query indices and grinding checks are
  built from it by the verifier (`Fri.sampleExt`, `Fri.sampleBits`, `Fri.checkWitness`).
* `hash` and `compress` are the Merkle tree's leaf hash and two-to-one compression.
-/

@[expose] public section
namespace CompStark
open CompStark.Stark (Digest)

/-- The primitives the verifier runs on, with results in a monad `m`: a challenger over the base
field `F` with its state, and the Merkle leaf hash and compression. -/
structure Primitives (F : Type) (m : Type → Type) where
  /-- The challenger's state. -/
  State : Type
  /-- The challenger before any observation. -/
  init : State
  /-- Absorb one element. -/
  observe : State → F → State
  /-- Squeeze one element. -/
  sample : State → m (F × State)
  /-- The Merkle leaf hash of a row. -/
  hash : List F → m (Digest F)
  /-- The Merkle compression of two digests. -/
  compress : Digest F → Digest F → m (Digest F)

end CompStark
