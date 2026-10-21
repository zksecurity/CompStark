/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Verifier
public import CompStark.Stark.Satisfied

/-! # Valid configurations

`ValidConfig`: the configurations the prover supports, checkable before proving and independent of
the trace.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri

/-- A configuration the prover supports: an AIR, FRI parameters and traces of `2 ^ logN` rows. -/
structure ValidConfig {F : Type} [BaseField F] (params : Params) (air : Air F) (logN : Nat) :
    Prop where
  /-- The constraints read only the AIR's columns, and the next preprocessed row only if the
  AIR declares it reads it. -/
  colsInWidth : air.ColsInWidth
  /-- The preprocessed trace has `2 ^ logN` rows of the AIR's preprocessed width. -/
  preprocessedSize : air.preprocessed.size = 2 ^ logN * air.preprocessedWidth
  /-- Each periodic column's period is a power of two dividing `2 ^ logN`. -/
  periodicFits : air.periodicFits logN = true
  /-- The constraints divided by the trace domain's vanishing polynomial fit the quotient's
  chunks (`Air.DegreeFits`). -/
  degreeFits : air.DegreeFits logN
  /-- The extended trace domain is a two-adic subgroup of the base field. -/
  twoAdic : logN + params.logBlowup ≤ twoAdicity F
  /-- The quotient's chunks fit the blowup. -/
  chunksFit : air.logQuotientChunks logN ≤ params.logBlowup
  /-- FRI folds at least once per round. -/
  folds : 0 < params.maxLogArity
  /-- FRI's final polynomial is no longer than the trace. -/
  finalPolyFits : params.logFinalPolyLen ≤ logN
  /-- FRI makes at least one query. -/
  queries : 0 < params.numQueries
  /-- The trace is extended to at least twice its length. -/
  blowup : 0 < params.logBlowup

end CompStark.Stark
