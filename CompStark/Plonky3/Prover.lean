/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Plonky3.Primitives
public import CompStark.Stark.Prover
public import CompStark.Stark.Setup

/-! # Plonky3's prover

The specification backend on Plonky3's transcript and Poseidon2 Merkle tree (`specBackend`), the
prover `prove` on it, and the verifying key of an AIR's preprocessed trace (`setup`), over a base
field with Plonky3's Poseidon2 instances.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

variable {F : Type} [BaseField F] [Poseidon2Field F]

/-- The specification backend on Plonky3's transcript and Poseidon2 Merkle tree. -/
abbrev specBackend (EF : Type) [Challenge F EF] : Backend F EF 24 :=
  Backend.spec EF Poseidon2.initTranscript (Hash.Poseidon2.hash F) (Hash.Poseidon2.compress F)

/-- The verifying key of `A`'s preprocessed trace for `2 ^ logN` rows (Plonky3's
`setup_preprocessed`): its width and height and the Poseidon2 Merkle root of its low-degree
extension, if it has columns (`preprocessedKeyWith`). -/
def setup (P : Params) (A : Air F) (logN : Nat) : Option (PreprocessedKey F) :=
  preprocessedKeyWith (poseidon2 F) P A logN

/-- The out-of-domain point `ζ` of the specification's proof: the challenge, sampled after the
trace and quotient commitments, at which the prover opens the traces and the quotient's chunks
and the verifier checks the constraints. -/
def outOfDomainPoint (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat)
    (trace : Array F) (pis : List F) : EF :=
  ((commitAndSample (specBackend EF) P A logN (setupWith (specBackend EF) P A logN) trace
    pis).run (specBackend EF).transcript).1.2.2.2.2.1

/-- A proof of `A` for the row-major trace of `2 ^ logN` rows and public values `pis`, by the
specification backend. -/
def prove (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (pis : List F) : Proof F EF :=
  proveWith (specBackend EF) P A logN trace pis

/-- The specification prover's transcript at the end of `prove`. Its `grindFailed` flag records
whether a grinding search found no witness. -/
def proveTranscript (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat)
    (trace : Array F) (pis : List F) : Transcript F 24 :=
  let prep := setupWith (specBackend EF) P A logN
  ((commitAndSample (specBackend EF) P A logN prep trace pis >>=
    openAndAssemble (specBackend EF) P A logN prep).run Poseidon2.initTranscript).2

end CompStark.Stark
