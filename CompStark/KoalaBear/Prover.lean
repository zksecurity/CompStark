/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.KoalaBear.Primitives
public import CompStark.Stark.Prover

/-! # Plonky3's prover over KoalaBear

The specification backend on Plonky3's KoalaBear transcript and Poseidon2 Merkle tree
(`specBackend`), and the prover `prove` on it.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

local notation "F" => _root_.KoalaBear.Fast.Field

/-- The specification backend on Plonky3's KoalaBear transcript and Poseidon2 Merkle tree. -/
abbrev specBackend (EF : Type) [Challenge F EF] : Backend F EF 24 :=
  Backend.spec EF KoalaBear.initTranscript (Hash.KoalaBear.hash F) (Hash.KoalaBear.compress F)

/-- The out-of-domain point `ζ` of the specification's proof: the challenge, sampled after the
trace and quotient commitments, at which the prover opens the trace and the quotient's chunks and
the verifier checks the constraints. -/
def outOfDomainPoint (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat)
    (trace : Array F) (pis : List F) : EF :=
  ((commitAndSample (specBackend EF) P A logN trace pis).run
    (specBackend EF).transcript).1.2.2.2.2

/-- A proof of `A` for the row-major trace of `2 ^ logN` rows and public values `pis`, by the
specification backend. -/
def prove (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (pis : List F) : Proof F EF :=
  proveWith (specBackend EF) P A logN trace pis

/-- The specification prover's transcript at the end of `prove`. Its `grindFailed` flag records
whether a grinding search found no witness. -/
def proveTranscript (EF : Type) [Challenge F EF] (P : Params) (A : Air F) (logN : Nat)
    (trace : Array F) (pis : List F) : Transcript F 24 :=
  ((commitAndSample (specBackend EF) P A logN trace pis >>=
    openAndAssemble (specBackend EF) P logN).run KoalaBear.initTranscript).2

end CompStark.Stark
