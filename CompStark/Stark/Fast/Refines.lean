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
  quotient A pis d l _ _ alpha h := by
    show (if d == logN && l == logChunks then _ else _) = _
    split
    · rename_i hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      rw [hd.1, hd.2]
      exact quotientWith_rel A pis _ _ alpha h
    · exact quotientWith_rel A pis _ _ alpha h
  openedAt b zs _ _ h := openedAt_rel b zs h
  toArray := toArray_rel
  ofArray := ofArray_rel
  size h := h.1
  reduce alpha _ _ h := reduce_rel alpha h
  fold2 beta k _ _ h := fold2_rel beta k h
  addScaled x _ _ _ _ hv hw := addScaled_rel x hv hw
  leaves k _ _ h := leaves_rel k h

/-- **The fast prover is correct.** It produces the specification's proof. -/
theorem prove_fast (P : Params) (A : Air) (logN : Nat) (trace : Array F) (pis : List F) :
    proveWith (backendFor logN P.logBlowup A.logQuotientChunks) P A logN trace pis =
      prove P A logN trace pis :=
  proveWith_refines (backendFor_refines _ _ _) P A logN trace pis

end CompStark.Stark.Fast
