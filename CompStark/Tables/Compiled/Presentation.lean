/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Whir
public import CompStark.Tables.Composed.Certificate

/-! The public-coin presentation of the composed system: the stack's initial word as a Merkle root,
then the bus, the table sumcheck and the external argument with their coefficient messages
revealed, then the WHIR opening. -/

set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The bus: the fingerprint's `k + 1` draws, the two roots, the product descent and the boundary
values. -/
def busPresentation : Presentation (Bus.protocol S L k) :=
  .challenge id (fun _ ↦ rfl)
    ⟨k + 1, (fun values ↦ ((fun i ↦ values[i.val]), values[k])), inferInstance⟩
    (.sender (fun roots ↦ fieldEvents ![roots.1, roots.2]) fun _ ↦
      grandProduct (.sender (fun values ↦ fieldEvents values) fun _ ↦ .done)
        (GrandProduct.layers (Bus.μ S L)) 0)

/-- The transmitted values, active table by active table in increasing order. -/
def valuesEvents (values : TableSumcheck.Values S L) : List Transcript.Event :=
  ((List.finRange S.tables.length).flatMap fun t ↦
    if h : S.Direct L t = false then List.ofFn (values ⟨t, h⟩) else []).map
      fun value ↦ .absorb (.scalar value)

/-- The table sumcheck's compressed messages and live draws, then the transmitted values. -/
def tableRounds : (count : ℕ) → Presentation (TableSumcheck.roundsProtocol S L count)
  | 0 => .sender (valuesEvents S L) fun _ ↦ .done
  | count + 1 => .reveal (fun message ↦ fieldEvents (Fin.cons message.1 message.2))
      (.challenge some (fun _ ↦ rfl) scalarDraw (tableRounds count))

/-- The batching draw, then the table sumcheck's rounds. -/
def tablePresentation : Presentation (TableSumcheck.protocol S L) :=
  .challenge id (fun _ ↦ rfl) scalarDraw (tableRounds S L (TableSumcheck.maxHeight S L))

end CompStark.Tables.Compiled
