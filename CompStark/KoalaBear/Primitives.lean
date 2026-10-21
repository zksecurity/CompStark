/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Challenger
public import CompStark.KoalaBear.Field
public import CompStark.KoalaBear.Hash
public import CompStark.Stark.Verifier

/-! # Plonky3's primitives over KoalaBear

The duplex challenger `DuplexChallenger<KoalaBear, Poseidon2KoalaBear<24>, 24, 16>` and its
transcript, the verifier's primitives `poseidon2` on it and the Poseidon2 Merkle hashes, and
Plonky3's verifier `verify`, `verifyWith` on them.
-/

@[expose] public section
namespace CompStark

namespace KoalaBear

local notation "F" => _root_.KoalaBear.Fast.Field

/-- Plonky3's `DuplexChallenger<KoalaBear, Poseidon2KoalaBear<24>, 24, 16>`. -/
def duplex : Duplex F 24 where
  perm := Poseidon2.permute (Poseidon2.KoalaBear.width24 F)
  rate := 16
  canon := CompPoly.CanonicalNat.toNat

/-- The empty specification transcript: the spec permutation, and grinding by search. -/
def initTranscript : Transcript F 24 :=
  Transcript.initWith duplex fun c bits ↦ grindFrom duplex c bits (CompPoly.CanonicalNat.bound F) 0

end KoalaBear

open CompStark.Stark (Digest)

local notation "F" => _root_.KoalaBear.Fast.Field

/-- Plonky3's primitives over KoalaBear: the duplex challenger on the width-24 Poseidon2
permutation, as in the transcript the prover shares (its grinder is not used by the verifier), and
the Poseidon2 Merkle hash and compression. -/
abbrev poseidon2 : Primitives F Id where
  State := Transcript F 24
  init := KoalaBear.initTranscript
  observe := Transcript.observe
  sample t := pure t.sample
  hash xs := pure (Hash.KoalaBear.hash F xs)
  compress a b := pure (Hash.KoalaBear.compress F a b)

namespace Stark

variable {EF : Type} [Challenge F EF]

/-- Plonky3's verifier: `verifyWith` on Poseidon2. -/
def verify (P : Fri.Params) (A : Air F) (proof : Proof F EF) (pis : List F) :
    Except String Unit :=
  verifyWith poseidon2 P A proof pis

end Stark
end CompStark
