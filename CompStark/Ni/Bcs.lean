/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsDeep

/-! # The challenges of a run

The challenger states and the challenges of the verifier's run on pure primitives: the challenger
when FRI's commit loop starts (`friStart`), the folding challenges (`betasOf`), and each query's
sample, whose low bits are its index (`queryState`, `querySampleOf`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop Polynomial
open Fri.Spec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The run's challenges -/

section Challenges
variable (H : Primitives F Id) (P : Params) (A : Air F) (vk : Option (PreprocessedKey F))
  (proof : Proof F EF) (pis : List F)

/-- The challenger when FRI's commit loop starts, after FRI's domain separator. -/
def friStart : H.State := obsList H (stateFri H P A vk proof pis) (friSeedOf P proof)

/-- The commit loop's folding challenges. -/
def betasOf : List EF :=
  (commitReplay H P (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    (friStart H P A vk proof pis)).1

/-- The challenger before the query grinding check: after the commit loop and the final
polynomial. -/
def queryState : H.State :=
  obsExts H (commitReplay (EF := EF) H P
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
    (friStart H P A vk proof pis)).2 proof.fri.finalPoly.toList

/-- Query `j`'s sample, whose low bits are its index. -/
def querySampleOf (j : Nat) : F :=
  (H.sample (sampleStates H
    (chkWit H P.queryPowBits proof.fri.queryWitness (queryState H P A vk proof pis)).2 j)).1

end Challenges

end CompStark.Ni
