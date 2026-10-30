/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Batch
public import CompStark.Sound.BatchAssembly

/-! # Completeness of the batch STARK on the interaction layer

A batch `Prover`, every instance's words and messages as functions of the challenges before them,
plays the batch protocol (`Prover.strategy`), with FRI's honest prover on the tallest domain's
batched DEEP word, injecting the shorter domains' batched DEEP words as the schedule reaches them.
It is accepted whenever the checks in the clear pass and every domain's batched DEEP word is a
codeword on that domain `g ⟨ω_m⟩`, of degree below the trace length of the instances of that size
(`Prover.strategy_accepts`).

FRI runs on the tallest domain's subgroup and injects a shorter word on the subgroup its folds
reach. A codeword on a coset is one on every coset of the same subgroup (`code_le_of_isLevel`), so
each injected word is in its code where FRI injects it (ArkLib's `inputsInCode_plonky3`).
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound CompStark.Interaction _root_.Interaction
open _root_.Interaction.Oracle OracleComp OracleSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable {withLookups : Bool}

namespace Prover
variable {S : Setup EF withLookups} (p : Prover S)

/-- The strategy's FRI: FRI's honest prover on the batched DEEP words. -/
noncomputable def friStrategy (l : 𝕂 × 𝕂) (α ζ a : 𝕂) :
    _root_.Interaction.Oracle.Prover.Strategy unifSpec S.friProtocol.tree S.friProtocol.roles
      (fun _ ↦ Unit) :=
  Fri.Interaction.honestProver unifSpec (S.logN S.top + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries (groupDeepWord p l.1 l.2 α ζ a)
    S.domainSetup.friDomain (groupDeepWord p l.1 l.2 α ζ a _)
    (S.domainSetup.friSchedule S.friHeights)

/-- The strategy after `ζ`: the claimed values, then FRI after `a`. -/
noncomputable def afterZetaStrategy (l : 𝕂 × 𝕂) (α ζ : 𝕂) :
    _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterZeta.tree S.afterZeta.roles
      (fun _ ↦ Unit) :=
  pure ⟨p.openings l.1 l.2 α ζ, fun a ↦ pure (p.friStrategy l α ζ a)⟩

/-- The strategy after `α`: the quotient chunks, then the rest after `ζ`. -/
noncomputable def afterAlphaStrategy (l : 𝕂 × 𝕂) (α : 𝕂) :
    _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterAlpha.tree S.afterAlpha.roles
      (fun _ ↦ Unit) :=
  pure ⟨fun x ↦ p.quotient l.1 l.2 α x.1 x.2.1.1 x.2.1.2 x.2.2, fun ζ ↦
    pure (p.afterZetaStrategy l α ζ)⟩

/-- The strategy after the lookup challenges: the permutation traces and the terminals, then the
rest after `α`. -/
noncomputable def afterLookupStrategy (l : 𝕂 × 𝕂) :
    _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterLookup.tree S.afterLookup.roles
      (fun _ ↦ Unit) :=
  pure ⟨fun x ↦ p.perm l.1 l.2 x.1 x.2.1.1 x.2.1.2 x.2.2, pure ⟨p.terminal l.1 l.2, fun α ↦
    pure (p.afterAlphaStrategy l α)⟩⟩

/-- The strategy of a batch prover's words and messages, as functions of the challenges before
them: it sends them, and runs FRI's honest prover on the batched DEEP words. -/
noncomputable def strategy :
    _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree S.protocol.roles
      (fun _ ↦ Unit) :=
  pure ⟨fun x ↦ p.trace x.1 x.2.1 x.2.2, fun l ↦ pure (p.afterLookupStrategy l)⟩

end Prover

namespace Setup
variable (S : Setup EF withLookups)

/-- The lookup challenges of an execution. -/
def lookupOf (path : S.protocol.tree.ExecutionPath) : 𝕂 × 𝕂 := path.2.1

/-- The constraint-folding challenge of an execution. -/
def alphaOf (path : S.protocol.tree.ExecutionPath) : 𝕂 := path.2.2.2.2.1

/-- The out-of-domain point of an execution. -/
def zetaOf (path : S.protocol.tree.ExecutionPath) : 𝕂 := path.2.2.2.2.2.2.1

/-- The batching challenge of an execution. -/
def batchOf (path : S.protocol.tree.ExecutionPath) : 𝕂 := path.2.2.2.2.2.2.2.2.1

/-- FRI's inputs are in their codes where its schedule injects them, if every domain's batched
DEEP word is a codeword on that domain. -/
theorem inputsInCode_friSchedule (w : (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (hw : ∀ i, w (S.logN i + S.params.logBlowup) ∈
      ReedSolomon.code ((S.instanceSetup i).domain : Fin (2 ^ (S.logN i + S.params.logBlowup)) ↪ 𝕂)
        (S.instanceSetup i).n) :
    (S.domainSetup.friSchedule S.friHeights).InputsInCode w (2 ^ S.params.logFinalPolyLen)
      S.domainSetup.friDomain := by
  have hft : S.domainSetup.params.logFinalPolyLen ≤ S.domainSetup.logN :=
    (S.valid S.top).finalPolyFits
  refine Fri.Interaction.Schedule.inputsInCode_plonky3 S.domainSetup.valid.folds w _
    (fun E ↦ IsLevel E) (fun E k hE ↦ isLevel_subdomain E k hE) _ _ _ S.friHeights (by omega)
    (Nat.sub_le _ _) (fits_friHeights S) (isLevel_subgroupDomain _ _) fun m hm D hD ↦ ?_
  obtain ⟨i, rfl, -⟩ := (mem_friHeights S m).mp hm
  have hf := (S.valid i).finalPolyFits
  have hdeg : 2 ^ (S.logN i + S.params.logBlowup -
      (S.params.logFinalPolyLen + S.params.logBlowup)) * 2 ^ S.params.logFinalPolyLen =
      2 ^ S.logN i := by
    rw [← pow_add]
    congr 1
    omega
  rw [hdeg]
  exact code_le_of_isLevel (isLevel_cosetDomain _ (S.valid i).twoAdic) hD _ (hw i)

end Setup

set_option backward.isDefEq.respectTransparency false in
/-- The strategy from the claimed values on is accepted on every execution where the checks in the
clear pass and every domain's batched DEEP word is a codeword on that domain. -/
theorem Prover.afterZeta_accepts {S : Setup EF withLookups} (p : Prover S)
    (publicValues : Fin S.k → List F) (l : 𝕂 × 𝕂) (α ζ : 𝕂) :
    ∀ result ∈ support (executeStrategies unifSpec S.afterZeta.tree S.afterZeta.roles
      S.afterZeta.oracles S.quotientAccess
      (S.messagesImpl (fun x ↦ p.trace x.1 x.2.1 x.2.2)
        (fun x ↦ p.perm l.1 l.2 x.1 x.2.1.1 x.2.1.2 x.2.2)
        (fun x ↦ p.quotient l.1 l.2 α x.1 x.2.1.1 x.2.1.2 x.2.2))
      (p.afterZetaStrategy l α ζ)
      (S.verifierAfterZeta publicValues l.1 l.2 (p.terminal l.1 l.2) α ζ)),
      S.Checks publicValues l.1 l.2 (p.terminal l.1 l.2) α ζ (p.openings l.1 l.2 α ζ) →
      (∀ i, groupDeepWord p l.1 l.2 α ζ result.1.2.1 (S.logN i + S.params.logBlowup) ∈
        ReedSolomon.code
          ((S.instanceSetup i).domain : Fin (2 ^ (S.logN i + S.params.logBlowup)) ↪ 𝕂)
          (S.instanceSetup i).n) →
      result.2.2 = true := by
  intro result hres hcheck hcode
  rw [Setup.execute_afterZeta] at hres
  obtain ⟨chosen, hchosen, hres⟩ := support_bind_exists hres
  rw [Prover.afterZetaStrategy, mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r1, hr1, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  rw [Setup.execute_afterOpenings] at hr1
  obtain ⟨a, -, hr1⟩ := support_bind_exists hr1
  obtain ⟨p1, hp1, hr1⟩ := support_bind_exists hr1
  rw [mem_support_pure_iff] at hp1
  subst hp1
  obtain ⟨r2, hr2, hr1⟩ := support_bind_exists hr1
  rw [mem_support_pure_iff] at hr1
  subst hr1
  rw [Setup.execute_fri, support_map] at hr2
  obtain ⟨r3, hr3, rfl⟩ := hr2
  change ∀ i, groupDeepWord p l.1 l.2 α ζ a (S.logN i + S.params.logBlowup) ∈ _ at hcode
  have hw : S.deepWords (fun x ↦ p.trace x.1 x.2.1 x.2.2) l.1 l.2
      (fun x ↦ p.perm l.1 l.2 x.1 x.2.1.1 x.2.1.2 x.2.2) (p.terminal l.1 l.2) α
      (fun x ↦ p.quotient l.1 l.2 α x.1 x.2.1.1 x.2.1.2 x.2.2) ζ (p.openings l.1 l.2 α ζ) a =
      groupDeepWord p l.1 l.2 α ζ a :=
    funext fun m ↦ funext fun x ↦ groupDeepWord_congr_at _ _ l.1 l.2 α ζ a m x
      (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) fun _ ↦ rfl
  have hreads := S.reads_deepReader (fun x ↦ p.trace x.1 x.2.1 x.2.2) l.1 l.2
    (fun x ↦ p.perm l.1 l.2 x.1 x.2.1.1 x.2.1.2 x.2.2) (p.terminal l.1 l.2) α
    (fun x ↦ p.quotient l.1 l.2 α x.1 x.2.1.1 x.2.1.2 x.2.2) ζ (p.openings l.1 l.2 α ζ) a
  rw [hw] at hreads
  have hfit := fits_friHeights S
  have hacc := Fri.Interaction.honest_accepts unifSpec (S.logN S.top + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries _ _ (groupDeepWord p l.1 l.2 α ζ a)
    (Nat.two_pow_pos _) (S.domainSetup.friSchedule S.friHeights) S.domainSetup.friDomain _ _ _ _
    (S.domainSetup.arityPos_friSchedule _ hfit) (S.inputsInCode_friSchedule _ hcode)
    (by
      rw [S.domainSetup.degree_friSchedule _ hfit]
      exact code_le_of_isLevel (isLevel_cosetDomain (EF := EF) _ (S.valid S.top).twoAdic)
        (isLevel_subgroupDomain (EF := EF) _ (S.valid S.top).twoAdic) _ (hcode S.top)) hreads
    (fun _ ↦ rfl) r3 hr3
  change (@decide _ (Classical.propDecidable _) && r3.2.2) = true
  rw [hacc, Bool.and_true]
  exact @decide_eq_true _ (Classical.propDecidable _) hcheck

set_option backward.isDefEq.respectTransparency false in
/-- **Completeness.** A batch prover's strategy is accepted on every execution where the checks in
the clear pass on its terminals and claimed values, and every domain's batched DEEP word is a
codeword on that domain of degree below the trace length of the instances of that size. -/
theorem Prover.strategy_accepts {S : Setup EF withLookups} (p : Prover S)
    (publicValues : Fin S.k → List F) :
    ∀ result ∈ support (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl p.strategy (S.verifier publicValues)),
      S.Checks publicValues (S.lookupOf result.1).1 (S.lookupOf result.1).2
        (p.terminal (S.lookupOf result.1).1 (S.lookupOf result.1).2) (S.alphaOf result.1)
        (S.zetaOf result.1)
        (p.openings (S.lookupOf result.1).1 (S.lookupOf result.1).2 (S.alphaOf result.1)
          (S.zetaOf result.1)) →
      (∀ i, groupDeepWord p (S.lookupOf result.1).1 (S.lookupOf result.1).2 (S.alphaOf result.1)
          (S.zetaOf result.1) (S.batchOf result.1) (S.logN i + S.params.logBlowup) ∈
        ReedSolomon.code
          ((S.instanceSetup i).domain : Fin (2 ^ (S.logN i + S.params.logBlowup)) ↪ 𝕂)
          (S.instanceSetup i).n) →
      result.2.2 = true := by
  intro result hres hcheck hcode
  rw [Setup.execute_protocol] at hres
  obtain ⟨chosen, hchosen, hres⟩ := support_bind_exists hres
  rw [Prover.strategy, mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r1, hr1, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  rw [Setup.execute_afterTrace] at hr1
  obtain ⟨l, -, hr1⟩ := support_bind_exists hr1
  obtain ⟨p1, hp1, hr1⟩ := support_bind_exists hr1
  rw [mem_support_pure_iff] at hp1
  subst hp1
  obtain ⟨r2, hr2, hr1⟩ := support_bind_exists hr1
  rw [mem_support_pure_iff] at hr1
  subst hr1
  rw [Setup.execute_afterLookup] at hr2
  obtain ⟨chosen, hchosen, hr2⟩ := support_bind_exists hr2
  rw [Prover.afterLookupStrategy, mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r3, hr3, hr2⟩ := support_bind_exists hr2
  rw [mem_support_pure_iff] at hr2
  subst hr2
  rw [Setup.execute_afterPerm] at hr3
  obtain ⟨chosen, hchosen, hr3⟩ := support_bind_exists hr3
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r4, hr4, hr3⟩ := support_bind_exists hr3
  rw [mem_support_pure_iff] at hr3
  subst hr3
  rw [Setup.execute_afterTerminals] at hr4
  obtain ⟨α, -, hr4⟩ := support_bind_exists hr4
  obtain ⟨p2, hp2, hr4⟩ := support_bind_exists hr4
  rw [mem_support_pure_iff] at hp2
  subst hp2
  obtain ⟨r5, hr5, hr4⟩ := support_bind_exists hr4
  rw [mem_support_pure_iff] at hr4
  subst hr4
  rw [Setup.execute_afterAlpha] at hr5
  obtain ⟨chosen, hchosen, hr5⟩ := support_bind_exists hr5
  rw [Prover.afterAlphaStrategy, mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r6, hr6, hr5⟩ := support_bind_exists hr5
  rw [mem_support_pure_iff] at hr5
  subst hr5
  rw [Setup.execute_afterQuotient] at hr6
  obtain ⟨ζ, -, hr6⟩ := support_bind_exists hr6
  obtain ⟨p3, hp3, hr6⟩ := support_bind_exists hr6
  rw [mem_support_pure_iff] at hp3
  subst hp3
  obtain ⟨r7, hr7, hr6⟩ := support_bind_exists hr6
  rw [mem_support_pure_iff] at hr6
  subst hr6
  exact p.afterZeta_accepts publicValues l α ζ r7 hr7 hcheck hcode

end CompStark.Iop.Batch
