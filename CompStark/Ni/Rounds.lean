/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsChallenges

/-! # The PCS's claimed evaluation counts

`pcsCountsS`: the claimed evaluation counts of a proof for a setup, the static layout in which the
PCS observes the opened values.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Fri.Spec OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The transcript of a prefix -/

section Prefix
variable (S : Iop.Setup EF) [S.Folds]

/-- The claimed evaluation counts of a proof for `S`. -/
def pcsCountsS : List (List (List Nat)) :=
  [[S.air.width :: if S.air.mainNextRow then [S.air.width] else []],
    List.replicate S.chunks [Challenge.d EF]] ++
    if S.air.preprocessedWidth = 0 then [] else
      [[S.air.preprocessedWidth ::
        if S.air.opensPreprocessedNext then [S.air.preprocessedWidth] else []]]

variable (publicValues : List F) (δ δ' loss : NNReal)

end Prefix

end CompStark.Ni
