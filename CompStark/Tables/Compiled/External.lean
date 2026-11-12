/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Soundness
public import CompStark.Tables.Composed.Keccak.External

/-! The compiled presentations of the external arguments: none for a system without virtual
columns, and for a Keccak table the GKR's coefficient messages and draws, then the six
ring-switching draws. Each commits no word, has prefix-free encodings and counts its draws. -/

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

section
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- The GKR's steps with their fixed-width coefficient messages revealed. -/
def gkrPresentation : (steps : List Keccak.Gkr.WireStep) →
    Presentation ⟨Keccak.Gkr.wireTree E steps, Keccak.Gkr.wireRoles E steps, gkrProtocol.noOracles steps⟩
  | [] => .done
  | .message n :: rest => .sender (rest := fun _ : Fin n → E =>
        ⟨Keccak.Gkr.wireTree E rest, Keccak.Gkr.wireRoles E rest, gkrProtocol.noOracles rest⟩)
        fieldEvents fun _ => gkrPresentation rest
  | .challenge _ :: rest =>
      .challenge (rest := fun _ : E =>
        ⟨Keccak.Gkr.wireTree E rest, Keccak.Gkr.wireRoles E rest, gkrProtocol.noOracles rest⟩)
        id (fun _ => rfl) scalarDraw (gkrPresentation rest)

end

/-- The number of challenge steps of a GKR schedule. -/
def wireRankCount (steps : List Keccak.Gkr.WireStep) : ℕ :=
  (steps.filterMap fun | .message _ => none | .challenge _ => some ()).length

/-- The GKR commits no word. -/
theorem gkrPresentation_shapes (steps : List Keccak.Gkr.WireStep) : (gkrPresentation steps).HasShapes [] := by
  induction steps with
  | nil => rfl
  | cons step rest ih => cases step with
    | message _ => exact fun _ => ih
    | challenge _ => exact ih

/-- The GKR's encodings are prefix free and its draws squeeze. -/
theorem gkrPresentation_framed (steps : List Keccak.Gkr.WireStep) : (gkrPresentation steps).Framed := by
  induction steps with
  | nil => trivial
  | cons step rest ih => cases step with
    | message _ => exact ⟨fieldEvents_framed id Function.injective_id, fun _ => ih⟩
    | challenge _ => exact ⟨by decide, ih⟩

/-- The GKR announces nothing. -/
theorem gkrPresentation_unannounced (steps : List Keccak.Gkr.WireStep) :
    (gkrPresentation steps).Unannounced := by
  induction steps with
  | nil => trivial
  | cons step rest ih => cases step with
    | message _ => exact fun _ => ih
    | challenge _ => exact ih

/-- Ring switching announces nothing. -/
theorem ringPresentation_unannounced (count : ℕ) : (ringPresentation count).Unannounced := by
  induction count with
  | zero => trivial
  | succ count ih => exact ih

/-- The GKR has one rank per challenge step. -/
theorem gkrPresentation_counted (steps : List Keccak.Gkr.WireStep) :
    (gkrPresentation steps).Counted (wireRankCount steps) := by
  induction steps with
  | nil => rfl
  | cons step rest ih => cases step with
    | message _ => exact fun _ => ih
    | challenge _ => exact ⟨_, rfl, ih⟩

/-- Ring switching commits no word. -/
theorem ringPresentation_shapes (count : ℕ) : (ringPresentation count).HasShapes [] := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- Ring switching's draws squeeze. -/
theorem ringPresentation_framed (count : ℕ) : (ringPresentation count).Framed := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨by decide, ih⟩

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

variable (kt : KeccakTable S L M)

/-- The Keccak table's argument's presentation. -/
def keccakPresentation : Presentation (KeccakTable.protocol kt.p) :=
  (gkrPresentation (gkrSteps kt.p)).append (ringPresentation 6)

/-- The Keccak table's argument commits no word. -/
theorem keccakPresentation_shapes : (keccakPresentation kt).HasShapes [] :=
  Presentation.HasShapes.append _ _ (gkrPresentation_shapes _) (ringPresentation_shapes 6)

/-- The Keccak table's argument's encodings are prefix free and its draws squeeze. -/
theorem keccakPresentation_framed : (keccakPresentation kt).Framed :=
  Presentation.Framed.append _ _ (gkrPresentation_framed _) (ringPresentation_framed 6)

/-- The Keccak table's argument announces nothing. -/
theorem keccakPresentation_unannounced : (keccakPresentation kt).Unannounced :=
  Presentation.Unannounced.append _ _ (gkrPresentation_unannounced _) (ringPresentation_unannounced 6)

/-- The Keccak table's argument's draws: the GKR's after its instance draws, then six. -/
theorem keccakPresentation_counted :
    (keccakPresentation kt).Counted (wireRankCount (gkrSteps kt.p) + 6) :=
  Presentation.Counted.append _ _ (gkrPresentation_counted _) (ringPresentation_counted 6)

end CompStark.Tables.Compiled
