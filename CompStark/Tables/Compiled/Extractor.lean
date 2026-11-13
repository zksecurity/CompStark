/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Soundness
public import CompStark.Tables.Composed.Extractor

/-! The compiled system's extractor as a computable definition: the composed extractor pulled back
along the presentation (`extractor`); the compiled certificate extracts with it
(`certificate_extractor`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.BinaryFields
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- The compiled system's extractor. -/
def extractor (params : Parameters S L k M) :
    RoundExtractor (presentation params).protocol.tree (Composed.inputState params.toParameters) :=
  (presentation params).extractor (Composed.extractor params.toParameters)

/-- The compiled certificate extracts with `extractor`. -/
theorem certificate_extractor (params : Parameters S L k M) :
    (certificate params).extractor = extractor params := by
  change (presentation params).extractor (Composed.certificate params.toParameters).extractor = _
  rw [Composed.certificate_extractor]
  rfl

end CompStark.Tables.Compiled
