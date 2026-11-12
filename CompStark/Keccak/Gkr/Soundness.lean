/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.ProtocolSoundness

/-! # Soundness of the fixed-table Keccak GKR reduction -/

@[expose] public section
open Polynomial OracleComp
open scoped ENNReal
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- Annex C soundness for a fixed committed table, conditioned only on true terminal openings.
The prover may depend on the whole fixed table and public statement. -/
theorem soundness {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (hx : IndependentLanePowers x)
    (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) (prover : Prover E)
    (wrong : ¬ InputRelation x output q) :
    Pr{let messages ← runWire E prover (steps p) []}[
      ∃ t : Transcript E p, transcriptMessages t = messages ∧
        Accepts x output t ∧ TerminalRelation x q t] ≤
      (37*(p+4)+902 : ENNReal) / Fintype.card E := by
  rw [← runProtocol_encoding p prover,prEvent_map]
  refine (prEvent_mono _ _ _ (fun sampled h => ?_)).trans
    (runProtocol_soundness x hx output q prover wrong)
  obtain ⟨t,he,checks,terminal⟩ := h
  have ht := transcriptMessages_injective he
  subst t
  exact ⟨checks,terminal⟩

end CompStark.Keccak.Gkr
