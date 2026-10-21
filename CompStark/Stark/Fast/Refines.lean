/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Refines
public import CompStark.Stark.Fast.Transcript
public import CompStark.Stark.Fast.Lde
public import CompStark.Stark.Fast.Commit
public import CompStark.Stark.Fast.Vectors
public import CompStark.Stark.Fast.Quotient
public import CompStark.Stark.Fast.Openings

/-! # The fast prover proves what the specification proves

The fast backend refines the specification (`backendFor_refines`), so its proofs are the
specification's (`prove_fast`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "EF" => _root_.KoalaBear.Fast.Ext4

/-- The fast backend refines the specification. -/
def backendFor_refines (logN logBlowup logChunks : Nat) :
    Refines (backendFor logN logBlowup logChunks) where
  RM := RM
  RC := RC
  RV := RV
  transcript := transcript_eq
  lde := ldeWith_rel _ (ldePlans_valid logN logBlowup logChunks)
  commit := commit_rel
  root := root_rel
  openAt := openAt_rel
  logHeight h := congrArg Nat.log2 (maxHeight_rel h)
  quotient A pis d l _ _ alpha h hs hh hc := by
    show (if d == logN && l == logChunks then _ else _) = _
    split
    · rename_i hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      rw [hd.1, hd.2]
      rw [hd.1, hd.2] at hh
      exact quotientWith_rel A pis _ _ alpha h hs hh hc
    · exact quotientWith_rel A pis _ _ alpha h hs hh hc
  openedAt b zs _ _ h hs hz := openedAt_rel b zs h hs hz
  toArray := toArray_rel
  ofArray := ofArray_rel
  size h := h.1
  reduce alpha _ _ h hok := reduce_rel alpha h hok
  fold2 beta k _ _ h ha hk := fold2_rel beta k h ha hk
  addScaled x _ _ _ _ hv hw hab ha := addScaled_rel x hv hw hab ha
  leaves k _ _ h ha := leaves_rel k h ha

/-- **The fast prover is correct.** For an input of the shapes the prover supports (`InputOk`),
it produces the specification's proof, unless the out-of-domain point `ζ` lands in the base field
(probability about `2 ^ -93`), where both provers divide by zero and compute different garbage. -/
theorem prove_fast {params : Params} {air : Air F} {logN : Nat} {trace : Array F}
    (publicValues : List F) (input : InputOk params air logN trace)
    (outOfDomain : Ext.OutsideBase (outOfDomainPoint EF params air logN trace publicValues)) :
    proveWith (backendFor logN params.logBlowup air.logQuotientChunks) params air logN trace
        publicValues =
      prove EF params air logN trace publicValues :=
  proveWith_refines (backendFor_refines _ _ _) publicValues input outOfDomain

end CompStark.Stark.Fast
