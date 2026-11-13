/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Prover
public import CompStark.Compiled.GrandProductRun

/-! The ideal runs of the compiled bus and table-sumcheck provers are the composed honest
transcripts at the coins the duplex draws (`bus_idealRun`, `table_idealRun`). -/

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

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The bus prover's ideal run is the honest bus transcript at the drawn coins. -/
theorem bus_idealRun (w : Witness K S.tables.length) (state : Transcript.State) :
    ∃ coins final, (busPresentation S L k).idealRun (busProver S L k w) state =
      some (honestBusPath S L k w coins, final) := by
  let fingerprint : Draw ((Fin k → E) × E) :=
    ⟨k + 1, (fun values ↦ ((fun i ↦ values[i.val]), values[k])), inferInstance⟩
  let αβ := (fingerprint.run state).1
  let roots := honestRoots S L k w αβ.1 αβ.2
  obtain ⟨coins, final, descent⟩ := grandProduct_idealRun (Bus.μ S L) (S.leaves L k w αβ.1 αβ.2)
    (boundaryStep S L) (fun c => fun _ => ⟨boundaryOf S L (boundaryImage S L w c.point), PUnit.unit⟩)
    (fun c => ⟨honestBoundary S L w c.point, PUnit.unit⟩)
    (fun c state => ⟨_, by rw [boundaryOf_image]; rfl⟩) (GrandProduct.layers (Bus.μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩
    (Transcript.replay (fingerprint.run state).2 (fieldEvents ![roots.1, roots.2]))
  refine ⟨(αβ, coins), final, ?_⟩
  have unfolded : (busPresentation S L k).idealRun (busProver S L k w) state =
      (((grandProduct (boundaryStep S L) (GrandProduct.layers (Bus.μ S L)) 0).idealRun
        (grandProductProver (Bus.μ S L) (S.leaves L k w αβ.1 αβ.2) (boundaryStep S L)
          (fun c => fun _ => ⟨boundaryOf S L (boundaryImage S L w c.point), PUnit.unit⟩) (GrandProduct.layers (Bus.μ S L)) 0
          ⟨[], ![roots.1, roots.1, roots.2]⟩)
        (Transcript.replay (fingerprint.run state).2 (fieldEvents ![roots.1, roots.2]))).map
          (fun result => (⟨roots, result.1⟩, result.2))).map (fun result => (⟨αβ, result.1⟩, result.2)) := rfl
  rw [unfolded, descent]
  rfl

/-- The table rounds prover's ideal run is the honest table rounds at the drawn challenges. -/
theorem tableRounds_idealRun (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    (n : ℕ) → (χ : List E) → (state : Transcript.State) → ∃ rs final,
      (tableRounds S L n).idealRun (tableRoundsProver S L k o ξ w n χ) state =
        some (honestTableRounds S L k o ξ w n χ rs, final)
  | 0, χ, state => ⟨Fin.elim0, _, by
      change some ((⟨valuesOf S L (valuesImage S L w χ.reverse), PUnit.unit⟩ :
        (TableSumcheck.roundsProtocol S L 0).tree.ExecutionPath), _) = _
      rw [valuesOf_image]
      rfl⟩
  | n + 1, χ, state => by
      let message := honestTableMessage S L k o ξ w χ
      let drawn := scalarDraw.run (Transcript.replay state (fieldEvents (Fin.cons message.1 message.2)))
      obtain ⟨rs, final, h⟩ := tableRounds_idealRun o ξ w n (χ ++ [drawn.1]) drawn.2
      refine ⟨Fin.cons drawn.1 rs, final, ?_⟩
      have unfolded : (tableRounds S L (n + 1)).idealRun (tableRoundsProver S L k o ξ w (n + 1) χ) state =
          Option.map (fun result => (⟨message, result.1⟩, result.2))
            (Option.map (fun result => (⟨some drawn.1, result.1⟩, result.2))
              ((tableRounds S L n).idealRun (tableRoundsProver S L k o ξ w n (χ ++ [drawn.1])) drawn.2)) :=
        rfl
      have rounds : honestTableRounds S L k o ξ w (n + 1) χ (Fin.cons drawn.1 rs) =
          ⟨message, some drawn.1, honestTableRounds S L k o ξ w n (χ ++ [drawn.1]) rs⟩ := by
        have raw : honestTableRounds S L k o ξ w (n + 1) χ (Fin.cons drawn.1 rs) =
            ⟨message, some (Fin.cons (α := fun _ => E) drawn.1 rs 0), honestTableRounds S L k o ξ w n
              (χ ++ [Fin.cons (α := fun _ => E) drawn.1 rs 0])
              (Fin.tail (Fin.cons (α := fun _ => E) drawn.1 rs))⟩ := rfl
        rw [raw, Fin.cons_zero, Fin.tail_cons]
      rw [unfolded, h, rounds]
      rfl

/-- The table prover's ideal run is the honest table transcript at the drawn coins. -/
theorem table_idealRun (o : Bus.Output S L k) (w : Witness K S.tables.length) (state : Transcript.State) :
    ∃ coins final, (tablePresentation S L).idealRun (tableProver S L k o w) state =
      some (honestTablePath S L k o w coins, final) := by
  let ξ := (scalarDraw.run state).1
  obtain ⟨rs, final, h⟩ := tableRounds_idealRun S L k o ξ w (TableSumcheck.maxHeight S L) []
    (scalarDraw.run state).2
  refine ⟨(ξ, rs), final, ?_⟩
  have unfolded : (tablePresentation S L).idealRun (tableProver S L k o w) state =
      ((tableRounds S L (TableSumcheck.maxHeight S L)).idealRun
        (tableRoundsProver S L k o ξ w (TableSumcheck.maxHeight S L) []) (scalarDraw.run state).2).map
          (fun result => (⟨ξ, result.1⟩, result.2)) := rfl
  rw [unfolded, h]
  rfl

end CompStark.Tables.Compiled
