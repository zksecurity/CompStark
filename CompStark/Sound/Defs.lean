/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Soundness
public import CompStark.Sound.FriSchedule
public import CompStark.Stark.Config
public import CompStark.Stark.Points

/-! # Constructions behind the IOP model

The domain `L` as an ArkLib smooth coset FFT domain and Plonky3's folding schedule for a single
input. `CompStark/Interaction/StarkSetup.lean` states the protocol with them and FRI with injected inputs
(`CompStark/Sound/FriGame.lean`).
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark Polynomial Domain OracleSpec OracleComp ProtocolSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

noncomputable instance : NonBinaryField 𝕂 where
  char_neq_2 := by
    have h : (2 : 𝕂) = algebraMap F 𝕂 2 := by rw [map_ofNat]
    rw [h, ne_eq, map_eq_zero_iff _ (algebraMap F 𝕂).injective]
    exact BaseField.two_ne_zero

/-- Uniform sampling from `F`. -/
noncomputable instance : SampleableType F := SampleableType.ofFintype F

/-- Uniform sampling from `𝕂`. -/
noncomputable instance : SampleableType 𝕂 := SampleableType.ofFintype 𝕂

/-- A base element in `𝕂`. -/
noncomputable abbrev lift (x : F) : 𝕂 := algebraMap F 𝕂 x

theorem isPrimitiveRoot_lift (n : Nat) (hn : n ≤ twoAdicity F) :
    IsPrimitiveRoot (lift (EF := EF) (twoAdicGen n)) (2 ^ n) :=
  isPrimitiveRoot_algebraMap n hn

/-- The point `g ω^i` of the coset `g · ⟨ω⟩` of order `2 ^ n`, in `F`. -/
def basePoint (n : Nat) (i : Nat) : F := gen * twoAdicGen n ^ i

/-- The subgroup `⟨ω⟩` of order `2 ^ n`, `ω = lift (twoAdicGen n)`, as a hom from the indices. -/
noncomputable def subgroupHom (n : Nat) (hn : n ≤ twoAdicity F) :
    Multiplicative (Fin (2 ^ n)) →* 𝕂ˣ where
  toFun i := ((isPrimitiveRoot_lift (EF := EF) n hn).isUnit (Nat.two_pow_pos n).ne').unit ^
    (Multiplicative.toAdd i).val
  map_one' := by simp only [toAdd_one, Fin.val_zero, pow_zero]
  map_mul' a b := by
    have hp := isPrimitiveRoot_lift (EF := EF) n hn
    have hu := (hp.isUnit (Nat.two_pow_pos n).ne')
    rw [toAdd_mul, Fin.val_add, ← pow_add]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val)
      (2 ^ n), pow_add, pow_mul, hp.pow_eq_one, one_pow, mul_one]

/-- The coset `g · ⟨ω⟩` of order `2 ^ n`, `n ≤ twoAdicity`, as an ArkLib domain. -/
noncomputable def cosetDomain (n : Nat) (hn : n ≤ twoAdicity F) : SmoothCosetFftDomain n 𝕂 where
  subgroupDomain := subgroupHom n hn
  subgroupDomain_inj := by
    intro a b h
    have hp := isPrimitiveRoot_lift (EF := EF) n hn
    have h' := congrArg Units.val h
    simp only [subgroupHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec] at h'
    exact Multiplicative.toAdd.injective (Fin.ext (hp.pow_inj (Multiplicative.toAdd a).isLt
      (Multiplicative.toAdd b).isLt h'))
  cosetGenerator := Units.mk0 (lift gen) (by
    rw [lift, ne_eq, map_eq_zero_iff _ (algebraMap F 𝕂).injective]
    exact BaseField.gen_ne_zero)

/-- The subgroup `⟨ω⟩` of order `2 ^ n`, `n ≤ twoAdicity`, as an ArkLib domain: FRI's domain in
Plonky3's coordinate, where it interpolates its folds and evaluates its final polynomial. -/
noncomputable def subgroupDomain (n : Nat) (hn : n ≤ twoAdicity F) : SmoothCosetFftDomain n 𝕂 where
  subgroupDomain := subgroupHom n hn
  subgroupDomain_inj := (cosetDomain (EF := EF) n hn).subgroupDomain_inj
  cosetGenerator := 1

/-- Plonky3's folding arities (`foldSchedule` with a single input): fold by
`min maxLogArity remaining` until `remaining = 0`, with at least `1` per fold. -/
def folds (maxLogArity : Nat) : Nat → List ℕ+
  | 0 => []
  | remaining + 1 =>
    let la := max 1 (min maxLogArity (remaining + 1))
    ⟨la, by omega⟩ :: folds maxLogArity (remaining + 1 - la)
  decreasing_by omega

/-- FRI's final degree bound `2 ^ logFinal`. -/
def finalDegree (logFinal : Nat) : ℕ+ := ⟨2 ^ logFinal, Nat.two_pow_pos logFinal⟩

end CompStark.Sound
