/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Schedule
public import CompStark.Pcs.WordEncoding

/-! The folding ladder of `Schedule.ladder` with certified evaluators of its query weights: an
evaluated schedule with its Johnson choices, encoding contracts and certified decoders. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

@[expose] public section

namespace CompStark.Pcs

open CompStark.BinaryFields

/-- An evaluated schedule with certified decoders at every level. -/
structure CertifiedEvaluated (vars rate : ℕ) where
  /-- The schedule with its query-weight evaluators. -/
  evaluated : EvaluatedSchedule vars
  /-- Integer Johnson choice at every level. -/
  johnson : Pcs.JohnsonParameters evaluated.schedule
  /-- All encoded levels satisfy WHIR's contracts. -/
  valid : evaluated.schedule.Valid (algebraMap K E) (Pcs.johnsonSecurity evaluated.schedule johnson)
  /-- The initial inverse-rate exponent. -/
  headRate : scheduleRate evaluated.schedule = rate
  /-- Certified decoder at the first encoded level. -/
  decoder : Whir.InitialDecoder evaluated.schedule
  /-- Its coverage and list bound. -/
  correct : Whir.InitialDecoder.Correct decoder (Pcs.johnsonSecurity evaluated.schedule johnson)
  /-- Extension-field decoders at every encoded level. -/
  decoders : Whir.DecoderFamily (E := E) evaluated.schedule
  /-- Their coverage and list bounds. -/
  familyCorrect : Whir.DecoderFamily.Correct (algebraMap K E) evaluated.schedule decoders
    (Pcs.johnsonSecurity evaluated.schedule johnson)

/-- The folding ladder with evaluated encodings: one level per `fold` coordinates, then four at a
time with the inverse rate increased by three, until at most five variables remain. -/
def evaluatedLadder (choices : JohnsonChoices) (queries : ℕ → ℕ) (vars fold rate : ℕ)
    (hvars : fold + 2 ≤ vars) (hfold : 0 < fold) (hrate : 0 < rate)
    (hdim : vars - fold + rate ≤ 63) : CertifiedEvaluated vars rate := by
  let tail := vars - fold
  have htail : 2 ≤ tail := by dsimp [tail]; omega
  have heq : fold + tail = vars := by dsimp [tail]; omega
  have hd : tail + rate ≤ 64 := by dsimp [tail]; omega
  let enc := evaluatedEncoding tail rate hd
  let choice := choices tail rate htail hrate
  have hv := choice.valid (by omega) hrate hd
  have hb := Pcs.baseEncodingContract tail rate hd hrate
  have he := Pcs.extensionEncodingContract tail rate hd hrate
  let cutoff := Pcs.agreementCutoff (2 ^ tail) (2 ^ (tail + rate)) choice.m
  let decoder := Pcs.checkedBaseDecoder tail rate fold hd cutoff
  let decoders := fun lanes => Pcs.gsListDecoder (algebraMap K E) tail rate lanes hd
    Pcs.extensionGsContext cutoff
  have familyCorrect (lanes : ℕ) : (decoders lanes).Correct (algebraMap K E)
      (Whir.radius enc.encoding choice.security) (Whir.listBound enc.encoding choice.security) := by
    let : Fintype E := Fintype.ofFinite E
    let : Algebra (ZMod 2) E := ZMod.algebra E 2
    exact choice.decoder_correct htail hrate hd (algebraMap K E) Pcs.extensionGsContext lanes
  by_cases last : tail ≤ 5
  · have result : CertifiedEvaluated (fold + tail) rate :=
      { evaluated := .last fold tail enc (queries rate)
        johnson := choice.m
        valid := ⟨hfold, hv, hb, he⟩
        headRate := rfl
        decoder := decoder
        correct := choice.checked_decoder_correct htail hrate hd fold
        decoders := decoders
        familyCorrect := familyCorrect }
    exact heq ▸ result
  · have nextdim : tail - 4 + (rate + 3) ≤ 63 := by dsimp [tail] at *; omega
    let next := evaluatedLadder choices queries tail 4 (rate + 3) (by omega) (by decide) (by omega) nextdim
    have result : CertifiedEvaluated (fold + tail) rate :=
      { evaluated := .more fold enc (queries rate) next.evaluated
        johnson := (choice.m, next.johnson)
        valid := ⟨hfold, hv, hb, he, next.valid⟩
        headRate := rfl
        decoder := decoder
        correct := choice.checked_decoder_correct htail hrate hd fold
        decoders := (decoders, next.decoders)
        familyCorrect := ⟨familyCorrect, next.familyCorrect⟩ }
    exact heq ▸ result
termination_by vars
decreasing_by omega

end CompStark.Pcs
