/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Stark
public import CompStark.Stark.Config

/-! # Completeness of the STARK verifier

If a trace satisfies an AIR, the honest prover's proof of it verifies (`completeness`). Besides
that premise, the theorem assumes two things, each a structure with one documented field per
condition:

* `ValidConfig` (`CompStark/Stark/Config.lean`): the configuration is one the prover supports.
  These conditions are checkable before proving and do not depend on the trace.
* `NoBadLuck`: the honest run avoids two events of negligible probability that make it fail:
  the out-of-domain point lands in the base field, or a proof-of-work search finds no witness.

The proof is in `CompStark/Complete/`.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

local notation "F" => _root_.KoalaBear.Fast.Field

variable {EF : Type} [Challenge F EF]

variable (EF) in
/-- The honest run over the extension `EF` avoids two unlikely events in which it fails. -/
structure NoBadLuck (params : Params) (air : Air F) (logN : Nat) (trace : Array F)
    (publicValues : List F) : Prop where
  /-- The out-of-domain point `ζ` (`outOfDomainPoint`), a random element of the extension of
  degree `d`, does not lie in the base field. It does with probability `fieldSize ^ (1 - d)`, about
  `2 ^ -93` for `d = 4` and `2 ^ -124` for `d = 5`; then `ζ - x` vanishes for some point `x` of the
  domains and the openings divide by zero. -/
  outOfDomain : Ext.OutsideBase (outOfDomainPoint EF params air logN trace publicValues)
  /-- Every proof-of-work search of the honest run finds a witness (`proveTranscript` records a
  failed search, where Plonky3's grinder would panic). A search for `b` bits tries every field
  element, each a witness with probability `2 ^ -b`, so it fails with probability about
  `exp (-2 ^ (31 - b))`. -/
  grinding : (proveTranscript EF params air logN trace publicValues).grindFailed = false

/-- **Completeness.** For a valid configuration and an honest run over any challenge field `EF`
without bad luck, if the trace satisfies the AIR, the honest prover's proof verifies. -/
theorem completeness {params : Params} {air : Air F} {logN : Nat} {trace : Array F}
    {publicValues : List F} (config : ValidConfig params air logN)
    (luck : NoBadLuck EF params air logN trace publicValues) :
    air.Satisfied logN trace publicValues →
      verify params air (prove EF params air logN trace publicValues) publicValues = .ok () :=
  fun sat ↦ verify_prove_of params air logN trace publicValues
    ⟨sat.size, config.colsInWidth, config.twoAdic, config.chunksFit⟩ sat.vanish config.degreeFits
    config.folds config.queries config.finalPolyFits luck.grinding luck.outOfDomain

end CompStark.Stark
