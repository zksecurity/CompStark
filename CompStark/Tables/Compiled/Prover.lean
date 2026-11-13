/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Verifier
public import CompStark.Tables.Composed.Honest
public import CompStark.Compiled.WhirProver
public import CompStark.Compiled.GrandProductProver

/-! The honest non-interactive prover of the compiled composed system: it commits the stack's
encoded word, runs the honest bus, table sumcheck, external argument and WHIR opening against the
Keccak duplex, and opens every committed word at its WHIR query positions. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

section
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

variable (S L k) in
/-- The honest bus: the roots at the drawn fingerprint, the honest descent, the true boundary
values. -/
def busProver (w : Witness K S.tables.length) : (busPresentation S L k).Prover := fun _ αβ =>
  let leaves := S.leaves L k w αβ.1 αβ.2
  let roots := honestRoots S L k w αβ.1 αβ.2
  fun _ => ⟨roots, grandProductProver (Bus.μ S L) leaves (boundaryStep S L)
    (fun c => fun _ => ⟨honestBoundary S L w c.point, PUnit.unit⟩)
    (GrandProduct.layers (Bus.μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩⟩

variable (S L k) in
/-- The honest table rounds after the draws `χ`, then the true values at the final point. -/
def tableRoundsProver (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    (count : ℕ) → List E → (tableRounds S L count).Prover
  | 0, χ => fun _ => ⟨honestValues S L w χ.reverse, PUnit.unit⟩
  | count + 1, χ => fun _ => (honestTableMessage S L k o ξ w χ, fun _ r =>
      tableRoundsProver o ξ w count (χ ++ [r]))

variable (S L k) in
/-- The honest table sumcheck at the drawn batching challenge. -/
def tableProver (o : Bus.Output S L k) (w : Witness K S.tables.length) : (tablePresentation S L).Prover :=
  fun _ ξ => tableRoundsProver S L k o ξ w (TableSumcheck.maxHeight S L) []

end

namespace Data

variable (d : Data S L k M)

section
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- An external argument's honest prover from the table sumcheck's output and the stack. -/
abbrev ExternalProver := TableSumcheck.Output S L k → Whir.Table K M → d.externalPresentation.Prover

/-- The outer presentation of the data. -/
def outerPresentation : Presentation (outerProtocol d.setup) :=
  ((busPresentation S L k).append (tablePresentation S L)).append d.externalPresentation

/-- The honest prover of the outer protocol. -/
def outerProver (external : d.ExternalProver) (w : Witness K S.tables.length) (q : Whir.Table K M) :
    d.outerPresentation.Prover :=
  Presentation.Prover.append _ _
    (Presentation.Prover.append _ _ (busProver S L k w) fun busPath =>
      tableProver S L k ((Bus.outputClaim S L k busPath).getD rejectedBus) w)
    fun first =>
      let parts := splitPath (Bus.protocol S L k) (TableSumcheck.protocol S L) first
      let bus := (Bus.outputClaim S L k parts.1).getD rejectedBus
      external ((TableSumcheck.outputClaim S L k bus parts.2).getD rejectedOutput) q

/-- The honest prover of the compiled presentation. -/
def prover (external : d.ExternalProver) (w : Witness K S.tables.length) : d.presentation.Prover :=
  let q := Pcs.tableOf M (S.stackValues L M w)
  let word : Whir.oracleMessage K d.evaluated.schedule := wordOfRows (headRowsBase d.evaluated q)
  let cache := Whir.TableCache.ofTable fun u => ofK (q u)
  fun _ => (word, baseRows word, Presentation.Prover.append d.outerPresentation
    (whirPresentation d.evaluated.schedule) (d.outerProver external w q) fun outer =>
      whirProver d.evaluated cache.get (openingClaims d.setup (outerOutput d.setup outer)))

end

/-- Attach to a compiled path the honest openings of the committed rows at their WHIR query
positions. -/
def attachOpenings (path : (StandardBcs.compile Commit.Digest d.presentation.coin).tree.ExecutionPath)
    (rows : List (ℕ → List K)) : d.Proof :=
  let opened := d.presentation.openedPath Commit.hash path []
  let parts := splitPath (outerProtocol d.setup) (Whir.opening E d.evaluated.schedule) opened.2
  let queries := whirQueries d.evaluated.schedule parts.2
  let trees := d.presentation.trees path [] 0
  ⟨PUnit.unit, path, (trees.zip (rows.zip queries)).map fun entry =>
    ⟨entry.2.2, Commit.honestBatch entry.1.height entry.1.leafWords entry.2.1 entry.2.2⟩⟩

/-- The honest compiled proof of a witness: the driven path, then every committed word opened at
its WHIR query positions; `none` if a grinding search fails. -/
def prove (external : d.ExternalProver) (w : Witness K S.tables.length) : Option d.Proof :=
  match d.presentation.run (d.prover external w) (Transcript.seedDigests d.iv d.statement) with
  | none => none
  | some result => some (d.attachOpenings result.1 result.2)

end Data

end CompStark.Tables.Compiled
