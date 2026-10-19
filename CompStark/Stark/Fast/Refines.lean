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

local notation "F" => KoalaBear.Fast.Field

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

/-- **The fast prover is correct.** For a trace of the AIR's shape within KoalaBear's two-adic
subgroups whose extension and quotient are addressable (`InputOk`), it produces the
specification's proof whenever that proof's opening point `ζ` lies outside the base field. -/
theorem prove_fast {P : Params} {A : Air} {logN : Nat} {trace : Array F} (pis : List F)
    (hin : InputOk P A logN trace) (hz : Ext.OutsideBase (outOfDomainPoint P A logN trace pis)) :
    proveWith (backendFor logN P.logBlowup A.logQuotientChunks) P A logN trace pis =
      prove P A logN trace pis :=
  proveWith_refines (backendFor_refines _ _ _) pis hin hz

end CompStark.Stark.Fast
