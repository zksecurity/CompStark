/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.Knowledge
public import CompStark.Multilinear.Algebra.ExecutableCoefficients

/-! Executable evaluations of the fixed-table GKR residuals. -/

@[expose] public section
namespace CompStark.Keccak.Gkr.Executable

/-- Evaluate the packed linear layer directly in the field, using the sixteen public embedding weights. -/
def linearAtPack {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (s : F) (r : Fin (p + 1) → F) (j : Fin 1600) : F :=
  ∑ m : Fin 2, ∑ b : Fin (2 ^ p), eqWeight r (b.val + 2 ^ p * m.val) *
    ∑ i : Fin 16, muAt s i * ZMod.castHom (dvd_refl 2) F
      (linear (segmentState q (packInstance i b) m (11 - d.val) (by omega)) j)

/-- Direct field evaluation agrees with the polynomial packed-linear specification. -/
theorem linearAtPack_eq {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (s : F) (r : Fin (p + 1) → F) (j : Fin 1600) :
    linearAtPack q d s r j = Gkr.linearAtPack q d s r j := by
  simp only [linearAtPack, Gkr.linearAtPack, packedLinear, kemb_eval]

/-- Compute the cubic pack summand from direct packed-linear field evaluations. -/
def packSummand {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F) (r : Fin (p + 1) → F) : F :=
  let one := ∑ i, muAt s i
  let a := linearAtPack q d s r
  eqEval c.point r * ∑ j, c.weights j * (one * a j + (one + a (along j 1)) * a (along j 2))

/-- The executable pack summand evaluates the same cubic as the knowledge certificate. -/
theorem packSummand_eq {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (s : F) (r : Fin (p + 1) → F) :
    packSummand q d c s r = Gkr.packSummand q d c s r := by
  simp only [packSummand, Gkr.packSummand, linearAtPack_eq]

/-- Evaluate a shifted position using the zero-padded 2048-entry position table. -/
def shiftedEvaluation {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (s : F) (r : Fin (p + 1) → F)
    (z : Fin 11 → F) (shift : ℕ) : F :=
  mle (fun j : Fin 2048 => if h : j.val < 1600 then
    linearAtPack q d s r (along ⟨j.val, h⟩ shift) else 0) z

/-- Executable shifted interpolation agrees with its polynomial specification. -/
theorem shiftedEvaluation_eq {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (s : F) (r : Fin (p + 1) → F)
    (z : Fin 11 → F) (shift : ℕ) :
    shiftedEvaluation q d s r z shift = Gkr.shiftedEvaluation q d s r z shift := by
  simp only [shiftedEvaluation, Gkr.shiftedEvaluation, linearAtPack_eq]

/-- The position summand combines the equality weight, position weight, and three shifted values. -/
def positionSummand {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (t : LayerTranscript F p)
    (z : Fin 11 → F) : F :=
  let one := ∑ i, muAt t.point i
  let a := shiftedEvaluation q d t.point t.packPoint z
  eqEval c.point t.packPoint *
    mle (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val, h⟩ else 0) z *
      (one * a 0 + (one + a 1) * a 2)

/-- The executable position summand agrees with the degree-three analytical summand. -/
theorem positionSummand_eq {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (d : Fin 12) (c : Claim F p) (t : LayerTranscript F p)
    (z : Fin 11 → F) : positionSummand q d c t z = Gkr.positionSummand q d c t z := by
  simp only [positionSummand, Gkr.positionSummand, shiftedEvaluation_eq]

/-- Compute the quadratic input-opening summand from the retained bit table and final layer claim. -/
def inputSummand {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (t : Transcript F p) (r : Fin 10 → F) : F :=
  let c := nextClaim (t.layers (Fin.last 11))
  let low : Fin 4 → F := fun i => r ⟨i.val, by omega⟩
  let slot : Fin 6 → F := fun i => r ⟨i.val + 4, by omega⟩
  let inst : Fin (p + 4) → F := fun i => if h : i.val < 4 then low ⟨i.val, h⟩
    else c.point ⟨i.val - 4, by omega⟩
  mle c.mu low * ∑ z : Fin 64,
    mle (fun s => inputWeight c s z) slot *
      mle (fun s => mle (fun b => ZMod.castHom (dvd_refl 2) F (q b s z)) inst) slot

/-- The executable input-opening summand agrees definitionally with the analytical one. -/
theorem inputSummand_eq {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (q : Witness p) (t : Transcript F p) (r : Fin 10 → F) :
    inputSummand q t r = Gkr.inputSummand q t r := rfl

end CompStark.Keccak.Gkr.Executable
