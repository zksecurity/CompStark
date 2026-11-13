/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Prover
public import CompStark.Multilinear.GrandProductHonest

/-! The honest prover of the grand-product GKR's presentation: the honest normalized messages at
every round, the honest child values, then the next layer at the interpolated claim. -/

set_option Elab.async false
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Multilinear CompStark.Multilinear.GrandProduct
open Interaction Interaction.Oracle Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- The rounds of a layer: the message at each prefix, the continuation at the full prefix. -/
def grandRoundsProver {tail : Protocol} (suffix : Presentation tail) (degree : ℕ)
    (message : List E → Message degree) (after : List E → suffix.Prover) :
    (count : ℕ) → List E → (grandRounds degree suffix count).Prover
  | 0, χ => after χ
  | count + 1, χ => fun _ =>
      let values := Vector.ofFn (message χ)
      (fun i => values[i], fun _ r => grandRoundsProver suffix degree message after count (χ ++ [r]))

/-- The child coordinates, then the continuation at the full child point. -/
def interpolationProver {tail : Protocol} (suffix : Presentation tail) (after : List E → suffix.Prover) :
    (count : ℕ) → List E → (interpolation suffix count).Prover
  | 0, u => after u
  | count + 1, u => fun _ x => interpolationProver suffix after count (u ++ [x])

/-- The child values' sender, then interpolation into the next layer. -/
def childrenStep {tail : Protocol} (suffix : Presentation tail) (rest : List ℕ) (used lanes : ℕ) :
    Presentation (.public .sender (Fin 3 → Fin (2 ^ lanes) → E) fun _ =>
      interpolationProtocol (protocol tail rest (used + lanes)) lanes) :=
  .sender (fun values => fieldEvents fun i : Fin (3 * 2 ^ lanes) =>
      values ⟨i.val / 2 ^ lanes, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr i.isLt⟩
        ⟨i.val % 2 ^ lanes, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
    (fun _ => interpolation (grandProduct suffix rest (used + lanes)) lanes)

variable (μ : ℕ) (leaves : Fin 3 → ℕ → E)

/-- The honest prover of the descent from a layer claim, then the suffix at the final claim. -/
def grandProductProver {tail : Protocol} (suffix : Presentation tail) (tailProver : Claim → suffix.Prover) :
    (steps : List ℕ) → (used : ℕ) → Claim → (grandProduct suffix steps used).Prover
  | [], _, c => tailProver c
  | ρ :: rest, m, c => fun _ lam =>
      grandRoundsProver (childrenStep suffix rest m ρ) (2 ^ ρ)
        (fun χ => honestMessage μ m ρ leaves lam c.point χ)
        (fun χ => fun _ =>
          let children := Vector.ofFn fun s => Vector.ofFn (honestChildren μ leaves m ρ χ s)
          let values : Fin 3 → Fin (2 ^ ρ) → E := fun s i => children[s][i]
          ⟨values, interpolationProver (grandProduct suffix rest (m + ρ))
            (fun u => grandProductProver suffix tailProver rest (m + ρ)
              (let point := u ++ χ
               let claimed := Vector.ofFn fun s => interpolated ρ values u s 0
               ⟨point, fun s => claimed[s]⟩)) ρ []⟩)
        m []

end CompStark.Compiled
