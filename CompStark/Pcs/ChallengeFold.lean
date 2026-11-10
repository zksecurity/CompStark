/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.DirectSums

/-! Shared-challenge restrictions without byte-table setup for short rounds. -/
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
@[expose] public section
namespace CompStark.Pcs
open BF64

/-- Restrict blocked pairs with direct scalar products and no prepared lookup tables. -/
def foldScalar (r : WordExt3) (rows width : Nat) (table : Vector WordExt3 (2*rows*width)) :
    Vector WordExt3 (rows*width) :=
  Vector.ofFn fun i =>
    let a := table[roundLow rows width i]
    let b := table[roundHigh rows width i]
    WordExt3.add a (roundProduct r (WordExt3.add a b))

/-- Scalar restrictions agree with every coordinate of the prepared challenge fold. -/
theorem foldScalar_eq (r : WordExt3) (rows width : Nat) (table : Vector WordExt3 (2*rows*width)) :
    foldScalar r rows width table = Sumcheck.fold (Sumcheck.prepare r) rows width table := by
  unfold foldScalar Sumcheck.fold
  congr 1
  funext i
  simp only [roundLow, roundHigh, Fin.getElem_fin, Sumcheck.Prepared.interpolate,
    Sumcheck.prepared_mul_eq, roundProduct_eq]

/-- Fold witness and weight together, preparing byte maps only above 256 output pairs. -/
def foldPairChallenge (r : WordExt3) (rows width : Nat)
    (table weight : Vector WordExt3 (2*rows*width)) :
    Vector WordExt3 (rows*width) × Vector WordExt3 (rows*width) :=
  if rows*width ≤ 256 then (foldScalar r rows width table, foldScalar r rows width weight)
  else
    let shared := Sumcheck.prepare r
    (Sumcheck.fold shared rows width table, Sumcheck.fold shared rows width weight)

/-- Size-directed challenge preparation preserves both complete restricted tables. -/
theorem foldPairChallenge_eq (r : WordExt3) (rows width : Nat)
    (table weight : Vector WordExt3 (2*rows*width)) :
    foldPairChallenge r rows width table weight =
      (Sumcheck.fold (Sumcheck.prepare r) rows width table,
        Sumcheck.fold (Sumcheck.prepare r) rows width weight) := by
  unfold foldPairChallenge
  split
  · simp only [foldScalar_eq]
  · rfl

end CompStark.Pcs
