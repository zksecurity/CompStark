/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Soundness
public import CompStark.Completeness

/-! # Constructions behind the IOP model

The domain `L` as an ArkLib smooth coset FFT domain, Plonky3's folding schedule, and the
acceptance probability of ArkLib's FRI oracle reduction against its best prover.
`CompStark/Iop.lean` states the protocol with them.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark Polynomial Domain Montgomery.Native32 OracleSpec OracleComp ProtocolSpec

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4
local notation "F" => KoalaBear.Fast.Field

noncomputable instance : NonBinaryField 𝕂 where
  char_neq_2 := by
    have h : (2 : 𝕂) = algebraMap 𝔽 𝕂 2 := by rw [map_ofNat]
    rw [h, ne_eq, map_eq_zero_iff _ (algebraMap 𝔽 𝕂).injective]
    decide

/-- Uniform sampling from `𝕂`. -/
noncomputable instance : SampleableType 𝕂 := SampleableType.ofFintype 𝕂

/-- A Montgomery element in `𝕂`. -/
noncomputable abbrev lift (x : F) : 𝕂 := algebraMap 𝔽 𝕂 (FastField.toField x)

theorem isPrimitiveRoot_lift (n : Nat) (hn : n ≤ 24) :
    IsPrimitiveRoot (lift (twoAdicGen n)) (2 ^ n) :=
  CompStark.Complete.isPrimitiveRoot_emb n hn

/-- The point `g ω^i` of the coset `g · ⟨ω⟩` of order `2 ^ n`, in `𝔽`. -/
noncomputable def basePoint (n : Nat) (i : Nat) : 𝔽 :=
  FastField.toField gen * FastField.toField (twoAdicGen n) ^ i

/-- The subgroup `⟨ω⟩` of order `2 ^ n`, `ω = lift (twoAdicGen n)`, as a hom from the indices. -/
noncomputable def subgroupHom (n : Nat) (hn : n ≤ 24) : Multiplicative (Fin (2 ^ n)) →* 𝕂ˣ where
  toFun i := ((isPrimitiveRoot_lift n hn).isUnit (Nat.two_pow_pos n).ne').unit ^
    (Multiplicative.toAdd i).val
  map_one' := by simp only [toAdd_one, Fin.val_zero, pow_zero]
  map_mul' a b := by
    have hp := isPrimitiveRoot_lift n hn
    have hu := (hp.isUnit (Nat.two_pow_pos n).ne')
    rw [toAdd_mul, Fin.val_add, ← pow_add]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val)
      (2 ^ n), pow_add, pow_mul, hp.pow_eq_one, one_pow, mul_one]

/-- The coset `g · ⟨ω⟩` of order `2 ^ n`, `n ≤ 24`, `g = 3`, as an ArkLib domain. -/
noncomputable def cosetDomain (n : Nat) (hn : n ≤ 24) : SmoothCosetFftDomain n 𝕂 where
  subgroupDomain := subgroupHom n hn
  subgroupDomain_inj := by
    intro a b h
    have hp := isPrimitiveRoot_lift n hn
    have h' := congrArg Units.val h
    simp only [subgroupHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec] at h'
    exact Multiplicative.toAdd.injective (Fin.ext (hp.pow_inj (Multiplicative.toAdd a).isLt
      (Multiplicative.toAdd b).isLt h'))
  cosetGenerator := Units.mk0 (lift gen) (by
    rw [lift, ne_eq, map_eq_zero_iff _ (algebraMap 𝔽 𝕂).injective]
    decide)

/-- Plonky3's folding arities (`logArityFor` with a single input): fold by
`min maxLogArity remaining` until `remaining = 0`, with at least `1` per fold. -/
def folds (maxLogArity : Nat) : Nat → List ℕ+
  | 0 => []
  | remaining + 1 =>
    let la := max 1 (min maxLogArity (remaining + 1))
    ⟨la, by omega⟩ :: folds maxLogArity (remaining + 1 - la)
  decreasing_by omega

/-- The challenges of ArkLib's FRI protocol, sampled uniformly. -/
noncomputable instance friChallenges {n k : Nat} (ω : SmoothCosetFftDomain n 𝕂)
    (s : Fin (k + 1) → ℕ+) (l : Nat) :
    ∀ j, SampleableType ((Fri.Spec.pSpec k (ω := ω) s l).Challenge j) :=
  @ProtocolSpec.instSampleableTypeChallengeAppend _ _ _ _
    (@ProtocolSpec.instSampleableTypeChallengeAppend _ _ _ _
      (@ProtocolSpec.instSampleableTypeChallengeSeqCompose _ _ _
        (fun _ _ ↦ SampleableType.ofFintype _))
      (fun _ ↦ SampleableType.ofFintype _))
    (fun _ ↦ SampleableType.ofFintype _)

/-- The folding arities of a nonempty list, indexed by `Fin (k + 1)`. -/
def foldsAt (f : ℕ+) (fs : List ℕ+) (j : Fin (fs.length + 1)) : ℕ+ := (f :: fs).get j

/-- FRI's final degree bound `2 ^ logFinal`. -/
def finalDegree (logFinal : Nat) : ℕ+ := ⟨2 ^ logFinal, Nat.two_pow_pos logFinal⟩

/-- FRI's input statement: no challenges yet, and `word` as the one initial oracle, a function on
the domain's points. -/
noncomputable def friInput {n k : Nat} (ω : SmoothCosetFftDomain n 𝕂) (s : Fin (k + 1) → ℕ+)
    (word : Fin (2 ^ n) → 𝕂) :
    Fri.Spec.Statement 𝕂 (0 : Fin (k + 1)) × ∀ j, Fri.Spec.OracleStatement s ω 0 j :=
  (Fin.elim0, fun j ↦ cast (by
    rw [Fin.fin_one_eq_zero j]
    simp only [Fri.Spec.OracleStatement, finRangeTo, Fin.val_zero, List.take_zero,
      List.toFinset_nil, Finset.sum_empty]
    rfl)
    fun x : (ω.subdomain 0).toFinset ↦ word ((ω.subdomain 0).equivToFinset.symm x))

/-- The trivial implementation of the empty oracle set. -/
def emptyImpl : QueryImpl (OracleSpec.emptySpec.{0, 0}) (StateT Unit ProbComp) := fun q ↦ q.elim

/-- The probability that ArkLib's FRI oracle reduction on the domain `ω` accepts `word`, against
its best prover: folding by `folds`, a final polynomial of degree below `2 ^ logFinal`, and
`numQueries` queries. `1` without folds. -/
noncomputable def friAcceptanceOf {n : Nat} (ω : SmoothCosetFftDomain n 𝕂) (folds : List ℕ+)
    (logFinal numQueries : Nat) (word : Fin (2 ^ n) → 𝕂) : ENNReal :=
  match folds with
  | [] => 1
  | f :: fs =>
    let s := foldsAt f fs
    let d := finalDegree logFinal
    if hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n then
      ⨆ (WitIn : Type) (WitOut : Type) (witIn : WitIn)
        (prover : Prover []ₒ (Fri.Spec.Statement 𝕂 (0 : Fin (fs.length + 1)) ×
          ∀ j, Fri.Spec.OracleStatement s ω 0 j) WitIn
          (Fri.Spec.FinalStatement 𝕂 fs.length × ∀ j, Fri.Spec.FinalOracleStatement s ω j)
          WitOut (Fri.Spec.pSpec fs.length (ω := ω) s numQueries)),
        let pImpl : QueryImpl ([]ₒ + [(Fri.Spec.pSpec fs.length (ω := ω) s numQueries).Challenge]ₒ)
            (StateT Unit ProbComp) := emptyImpl.addLift ProtocolSpec.challengeQueryImpl
        letI reduction := Reduction.mk prover
          (Fri.Spec.reduction fs.length s d hdom numQueries).verifier.toVerifier
        Pr{let ⟨_, stmtOut⟩ ← OptionT.mk do
          (simulateQ pImpl (reduction.run (friInput ω s word) witIn).run).run'
            (← (pure () : ProbComp Unit))}[stmtOut ∈ Set.univ]
    else 1

/-- FRI's soundness error (`Fri.Spec.soundnessError`) for the reduction of `friAcceptanceOf`, at
proximity `δ`: one correlated-agreement error per fold and `(1 - δ) ^ numQueries`. `1` without
folds. -/
noncomputable def friErrorOf {n : Nat} (ω : SmoothCosetFftDomain n 𝕂) (folds : List ℕ+)
    (logFinal numQueries : Nat) (δ : NNReal) : ENNReal :=
  match folds with
  | [] => 1
  | f :: fs =>
    let s := foldsAt f fs
    let d := finalDegree logFinal
    if 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n then
      Fri.Spec.soundnessError (ω := ω) s d numQueries δ δ
    else 1

end CompStark.Sound
