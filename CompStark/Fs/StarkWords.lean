/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Iop.Stark
public import CompStark.Fs.StarkDeep

/-! # The STARK's oracle messages under a commitment

The oracle messages of the STARK on ArkLib's interaction layer (`CompStark/Iop/Stark.lean`)
read off a cache of hash queries under a Merkle cap: the trace message (`Setup.traceMessageOf`)
and the quotient message (`Setup.quotientMessageOf`), whose column `j` at the point of `L` of
index `z` is entry `j` of the extracted leaf `rev z` (`Fs.committedColumn`), and a FRI layer's
word (`friWordOf`), whose leaf `r` is the group of `2 ^ k` values at the bit-reversed indices
`r 2 ^ k + q` (`Fs.friWordAt`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Fri

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The word of a FRI layer of `2 ^ m` points folded by `2 ^ k`, committed under the cap `cap` of
height `capHeight`: its value at the point of index `z` is entry `rev z % 2 ^ k` of leaf
`rev z >>> k`, read off `cache`. -/
noncomputable def friWordOf (cache : Merkle.Cache F (Digest F)) (capHeight : ℕ) (cap : Cap F)
    (m k : ℕ) : Fri.Interaction.Word 𝕂 m :=
  fun z ↦ Fs.friWordAt cache cap capHeight m k z.val

namespace Setup
variable (S : Setup EF) (cache : Merkle.Cache F (Digest F))

/-- The trace message committed under the cap `cap`: column `j` at a point of `L` is column `j`
of the extracted rows there. -/
noncomputable def traceMessageOf (cap : Cap F) : S.TraceMessage :=
  fun jx ↦ Fs.committedColumn S cache cap jx.1.val jx.2

/-- The quotient message committed under the cap `cap`: coordinate `e` of chunk `c` at a point of
`L` is column `d c + e` of the extracted rows there. -/
noncomputable def quotientMessageOf (cap : Cap F) : S.QuotientMessage :=
  fun cex ↦ Fs.committedColumn S cache cap (Challenge.d EF * cex.1.1.val + cex.1.2.val) cex.2

end Setup

end CompStark.Iop
