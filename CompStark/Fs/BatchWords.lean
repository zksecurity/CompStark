/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Batch
public import CompStark.Fs.StarkWords
public import CompStark.Fs.StarkTerminal
public import CompStark.Ni.BatchBcs

/-! # The batch STARK's oracle messages under a commitment

The oracle messages of the batch STARK on ArkLib's interaction layer
(`CompStark/Interaction/Batch.lean`) read off a cache of hash queries under a Merkle cap, with
Plonky3's layout of matrices of mixed heights in one tree (`Merkle.matColumnCap`): an instance's
column at the point of its domain of index `z` is the column of its matrix at row `rev z`, the
matrix's columns at its offset among the matrices of its height.

* `Setup.traceMessageOf`: the main tree's matrices are every instance's extended trace, the tree
  as deep as the tallest (`mainHeights`, `mainWidths`, depth `logTop`);
* `Setup.permMessageOf`: the permutation tree's matrices are the permutation traces of the
  instances with lookups, coordinate `e` of column `c` the matrix's column `c d + e` (`permIndex`,
  `permHeights`, `permWidths`, depth `permLog`);
* `Setup.quotientMessageOf`: the quotient tree's matrices are every instance's chunks, each of `d`
  columns (`quotOffset`, `quotHeights`, `quotWidths`, depth `logTop`);
* FRI's layers are read as in the STARK (`friWordOf`).

`Setup.proofPath` is the batch's execution path read off a proof: these messages under the proof's
commitments, the proof's terminals and opened values, the challenges of the run of Plonky3's batch
verifier on pure primitives, and FRI's path (`friPath`) on the tallest domain.
-/

@[expose] public section
namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Ni

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
variable (S : Setup EF) (cache : Merkle.Cache F (Digest F))

/-- Every instance's trace committed under the main cap `cap`: column `j` of instance `i` at the
point `x` of its domain is column `j` of matrix `i` at row `rev x`. -/
noncomputable def traceMessageOf (cap : Cap F) : S.TraceMessage :=
  fun ijx ↦ Merkle.matColumnCap cache cap.toList S.params.capHeight S.logTop S.mainHeights
    S.mainWidths ijx.1.val ijx.2.1.val (S.logN ijx.1 + S.params.logBlowup)
    (reverseBits ijx.2.2.val (S.logN ijx.1 + S.params.logBlowup))

/-- Every instance's permutation trace committed under the permutation cap `cap`: coordinate `e`
of column `c` of instance `i` at the point `x` is column `c d + e` of the instance's matrix among
those of the instances with lookups, at row `rev x`. -/
noncomputable def permMessageOf (cap : Cap F) : S.PermMessage :=
  fun icex ↦ Merkle.matColumnCap cache cap.toList S.params.capHeight (permLog S) (permHeights S)
    (permWidths S) (permIndex S icex.1) (icex.2.1.1.val * Challenge.d EF + icex.2.1.2.val)
    (S.logN icex.1 + S.params.logBlowup)
    (reverseBits icex.2.2.val (S.logN icex.1 + S.params.logBlowup))

/-- Every instance's quotient chunks committed under the quotient cap `cap`: coordinate `e` of
chunk `c` of instance `i` at the point `x` is column `e` of the instance's chunk `c` among all
instances' chunks, at row `rev x`. -/
noncomputable def quotientMessageOf (cap : Cap F) : S.QuotientMessage :=
  fun icex ↦ Merkle.matColumnCap cache cap.toList S.params.capHeight S.logTop (quotHeights S)
    (quotWidths S) (quotOffset S icex.1 + icex.2.1.1.val) icex.2.1.2.val
    (S.logN icex.1 + S.params.logBlowup)
    (reverseBits icex.2.2.val (S.logN icex.1 + S.params.logBlowup))

/-- The terminals of a proof: those of the instances with lookups, `0` where the proof has none. -/
noncomputable def terminalsOf (proof : CompStark.Batch.BatchProof F EF) : S.Terminals :=
  fun i ↦ Challenge.toSpec ((proof.lookupTerminals.getD i.1 none).getD 0)

/-- The claimed values of a proof: every instance's opened values with its permutation trace's
rows at `ζ` and `ζ ω`. -/
noncomputable def openingsOf (proof : CompStark.Batch.BatchProof F EF) : S.OpeningsMessage :=
  fun i ↦ Ni.openingsOf (S.instanceSetup i) (proof.opened.toList.getD i noOpenings)
    (proof.permutationLocal.getD i #[]) (proof.permutationNext.getD i #[])

/-- The batch's execution path read off a proof, at the setup of its lengths: every instance's
trace, permutation trace and quotient chunks under the proof's main, permutation and quotient
commitments, extracted from `cache` (`traceMessageOf`, `permMessageOf`, `quotientMessageOf`), the
lookup challenges, `α`, `ζ` and the batching challenge of the run on `H` against the common data
`common` with the public values `pis`, the proof's terminals (`terminalsOf`) and claimed values
(`openingsOf`), and FRI's path (`friPath`): the layers' words under the proof's FRI commitments,
the run's folding challenges, the proof's final polynomial and the run's query positions. -/
noncomputable def proofPath (H : Primitives F Id) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F)) :
    S.protocol.tree.ExecutionPath :=
  ⟨S.traceMessageOf cache proof.mainCommit,
    (Challenge.toSpec (lookupRunB H S.params S.instances common proof pis).1,
      Challenge.toSpec (lookupRunB H S.params S.instances common proof pis).2),
    S.permMessageOf cache (permRoot proof),
    S.terminalsOf proof,
    Challenge.toSpec (alphaOfB H S.params S.instances common proof pis),
    S.quotientMessageOf cache proof.quotientCommit,
    Challenge.toSpec (zetaOfB H S.params S.instances common proof pis),
    S.openingsOf proof,
    Challenge.toSpec (batchOfB H S.params S.instances common proof pis),
    friPath cache S.params.capHeight proof.fri.commits.toList
      (commitReplayB H S common proof pis).1
      (fun i : Fin (2 ^ S.params.logFinalPolyLen) ↦
        Challenge.toSpec (proof.fri.finalPoly.getD i 0))
      (fun j ↦ Sound.queryPoint S.domainSetup (querySampleOfB H S common proof pis j))
      (S.domainSetup.friSchedule S.friHeights) 0⟩

end CompStark.Iop.Batch.Setup
