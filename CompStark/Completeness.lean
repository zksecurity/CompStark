/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Stark

/-! # Completeness of the STARK verifier

If a trace satisfies an AIR, the honest prover's proof of it verifies (`completeness`). Besides
that premise, the theorem assumes two things, each a structure with one documented field per
condition:

* `ValidConfig`: the configuration is one the prover supports. These conditions are checkable
  before proving and do not depend on the trace.
* `NoBadLuck`: the honest run avoids two events of negligible probability that make it fail:
  the out-of-domain point lands in the base field, or a proof-of-work search finds no witness.

The proof is in `CompStark/Complete/`.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

local notation "F" => KoalaBear.Fast.Field

/-- A configuration the prover supports: an AIR, FRI parameters and traces of `2 ^ logN` rows. -/
structure ValidConfig (params : Params) (air : Air) (logN : Nat) : Prop where
  /-- The constraints read only the AIR's columns. -/
  colsInWidth : air.ColsInWidth
  /-- The constraints divided by the trace domain's vanishing polynomial fit the quotient's
  chunks (`Air.DegreeFits`). -/
  degreeFits : air.DegreeFits logN
  /-- The extended trace domain is a subgroup of KoalaBear, whose two-adicity is 24. -/
  twoAdic : logN + params.logBlowup ≤ 24
  /-- The quotient's chunks fit the blowup. -/
  chunksFit : air.logQuotientChunks ≤ params.logBlowup
  /-- FRI folds at least once per round. -/
  folds : 0 < params.maxLogArity
  /-- FRI's final polynomial is no longer than the trace. -/
  finalPolyFits : params.logFinalPolyLen ≤ logN
  /-- FRI makes at least one query. -/
  queries : 0 < params.numQueries

/-- The honest run avoids two unlikely events in which it fails. -/
structure NoBadLuck (params : Params) (air : Air) (logN : Nat) (trace : Array F)
    (publicValues : List F) : Prop where
  /-- The out-of-domain point `ζ` (`outOfDomainPoint`), a random element of the quartic
  extension, does not lie in the base field. It does with probability about `2 ^ -93`; then
  `ζ - x` vanishes for some point `x` of the domains and the openings divide by zero. -/
  outOfDomain : Ext.OutsideBase (outOfDomainPoint params air logN trace publicValues)
  /-- Every proof-of-work search of the honest run finds a witness (`proveTranscript` records a
  failed search, where Plonky3's grinder would panic). A search for `b` bits tries every field
  element, each a witness with probability `2 ^ -b`, so it fails with probability about
  `exp (-2 ^ (31 - b))`. -/
  grinding : (proveTranscript params air logN trace publicValues).grindFailed = false

/-- **Completeness.** For a valid configuration and an honest run without bad luck, if the trace
satisfies the AIR, the honest prover's proof verifies. -/
theorem completeness {params : Params} {air : Air} {logN : Nat} {trace : Array F}
    {publicValues : List F} (config : ValidConfig params air logN)
    (luck : NoBadLuck params air logN trace publicValues) :
    air.Satisfied logN trace publicValues →
      verify params air (prove params air logN trace publicValues) publicValues = .ok () :=
  fun sat ↦ verify_prove_of params air logN trace publicValues
    ⟨sat.size, config.colsInWidth, config.twoAdic, config.chunksFit⟩ sat.vanish config.degreeFits
    config.folds config.queries config.finalPolyFits luck.grinding luck.outOfDomain

end CompStark.Stark
