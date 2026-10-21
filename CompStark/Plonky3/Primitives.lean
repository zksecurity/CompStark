/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Challenger
public import CompStark.Plonky3.Hash
public import CompStark.Primitives
public import CompStark.Stark.Verifier

/-! # Plonky3's primitives

Over a base field with Plonky3's Poseidon2 instances (`Poseidon2Field`): the duplex challenger
`DuplexChallenger<F, Poseidon2<24>, 24, 16>` and its transcript, the verifier's primitives
`poseidon2` on it and the Poseidon2 Merkle hashes, and Plonky3's verifier `verify`, `verifyWith`
on them.
-/

@[expose] public section
namespace CompStark

variable {F : Type} [BaseField F] [Poseidon2Field F]

namespace Poseidon2

/-- Plonky3's `DuplexChallenger<F, Poseidon2<24>, 24, 16>`. -/
def duplex : Duplex F 24 where
  perm := (Poseidon2Field.perm24 (F := F)).perm
  rate := 16
  canon := CompPoly.CanonicalNat.toNat

/-- The empty specification transcript: the duplex challenger, and grinding by search. -/
def initTranscript : Transcript F 24 :=
  Transcript.initWith duplex fun c bits ↦ grindFrom duplex c bits (CompPoly.CanonicalNat.bound F) 0

end Poseidon2

open CompStark.Stark (Digest)

variable (F) in
/-- Plonky3's primitives: the duplex challenger on the width-24 Poseidon2 permutation, as in the
transcript the prover shares (its grinder is not used by the verifier), and the Poseidon2 Merkle
hash and compression. -/
abbrev poseidon2 : Primitives F Id where
  State := Transcript F 24
  init := Poseidon2.initTranscript
  observe := Transcript.observe
  sample t := pure t.sample
  hash xs := pure (Hash.Poseidon2.hash F xs)
  compress a b := pure (Hash.Poseidon2.compress F a b)

namespace Stark

variable {EF : Type} [Challenge F EF]

/-- Plonky3's verifier: `verifyWith` on Poseidon2. -/
def verify (P : Fri.Params) (A : Air F) (proof : Proof F EF) (pis : List F) :
    Except String Unit :=
  verifyWith (poseidon2 F) P A proof pis

end Stark
end CompStark
