/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Refines
public import CompStark.Stark.Prover

/-! # Provers on refining backends

A backend that refines the specification (`Fri.Refines`) proves exactly what the specification
proves.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri CompStark.KoalaBear

local notation "F" => KoalaBear.Fast.Field

theorem proveWith_refines {B : Backend} (h : Refines B) (P : Params) (A : Air) (logN : Nat)
    (trace : Array F) (pis : List F) : proveWith B P A logN trace pis = prove P A logN trace pis := by
  unfold prove proveWith
  dsimp only
  rw [h.transcript]
  refine ((?_ : RelM Eq _ _) _).1
  have hext := h.lde logN P.logBlowup gen A.width trace
  have hct := h.commit (.cons hext .nil)
  rw [h.root hct]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦ RelM.bind_eq fun _ ↦
    RelM.bind_eq fun _ ↦ RelM.bind_eq fun alpha ↦ ?_
  rw [h.quotient _ _ _ _ _ hext]
  generalize Backend.spec.quotient _ _ _ _ _ _ = qs
  have hch : List.Forall₂ h.RM
      ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
        B.lde logN P.logBlowup (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
          (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN)))
      ((List.range (2 ^ A.logQuotientChunks)).map fun c ↦
        Backend.spec.lde logN P.logBlowup
          (gen * (gen * powF (twoAdicGen (logN + A.logQuotientChunks)) c)⁻¹) 4
          (chunkValues qs (2 ^ A.logQuotientChunks) c (2 ^ logN))) :=
    forall₂_map (fun _ _ hc ↦ hc ▸ h.lde _ _ _ _ _) (List.forall₂_same.2 fun _ _ ↦ rfl)
  have hqc := h.commit hch
  rw [h.root hqc]
  refine RelM.bind_eq fun _ ↦ RelM.bind_eq fun zeta ↦ ?_
  refine RelM.bind (openPcs_refines h P ?_) fun _ _ hx ↦ hx ▸ RelM.pure rfl
  exact .cons ⟨hct, .cons ⟨hext, rfl⟩ .nil⟩
    (.cons ⟨hqc, forall₂_map (fun _ _ hm ↦ ⟨hm, rfl⟩) hch⟩ .nil)

end CompStark.Stark
