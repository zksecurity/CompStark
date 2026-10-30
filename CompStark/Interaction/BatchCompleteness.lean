/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Batch
public import CompStark.Interaction.StarkCompleteness
public import CompStark.Sound.BatchAssembly
public import CompStark.Ni.BatchCheck
public import CompStark.BatchCompleteness

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

The honest prover of a batch's traces (`Setup.honestProver`) sends what the specification's batch
prover (`proveBatch`) commits to and opens: every instance's extended trace; after the lookup
challenges, its extended permutation trace and terminal (`permutationTrace`, under the
specification's layout of the challenges, `challengeLayout`); after `α`, its quotient chunks
extended onto its domain (`honestChunks`); and after `ζ`, the values of their polynomials at `ζ`
and `ζ ω_n`. If the traces satisfy the batch in a valid configuration (`Batch.ValidConfig`, as for
the specification's `Batch.completeness`), its strategy is accepted on every execution whose `ζ`
lies off the base field and under whose lookup challenges no denominator vanishes
(`Setup.NoPole`) (`Setup.completeness`), discharging both conditions of
`Prover.strategy_accepts`:

* the checks in the clear pass: the terminals sum to zero as every bus balances
  (`terminals_sum_eq_zero`), and every instance's honest openings pass its check at `ζ`
  (`instanceCheck_honest`), which is `ConstraintsHoldAt` in the spec field
  (`constraintsHoldAt_of_instanceCheck`);
* every domain's batched DEEP word is a codeword: every word opened on it is the values of a
  polynomial of degree below the trace length, claimed at its value there (`OpensLow`), and DEEP
  quotients of such words are codewords (`deepQuotient_mem_code`).
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

namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound CompStark.Ni CompStark.Fri CompStark.Lookup Polynomial
open _root_.Interaction _root_.Interaction.Oracle OracleComp OracleSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Batched DEEP words of words that open low -/

section Deep

/-- A sum `∑ⱼ aʲ (yⱼ - fⱼ(x)) / (zⱼ - x)` over words that open low, the powers of `a` from any
start, is a codeword of their degree bound. -/
theorem deepSum_mem_code {m n : ℕ} (D : Domain.SmoothCosetFftDomain m 𝕂)
    (hD : ∀ x, D x = algebraMap F 𝕂 (basePoint m x)) (a : 𝕂) :
    ∀ (ws : List ((Fin (2 ^ m) → F) × 𝕂 × 𝕂)) (k : ℕ), (∀ w ∈ ws, OpensLow m n w) →
      (fun x ↦ ((ws.zipIdx k).map fun ((f, z, y), j) ↦
        a ^ j * (y - algebraMap F 𝕂 (f x)) / (z - lift (basePoint m x))).sum) ∈
        ReedSolomon.code (D : Fin (2 ^ m) ↪ 𝕂) n
  | [], _, _ => by
    simp only [List.zipIdx_nil, List.map_nil, List.sum_nil]
    exact zero_mem _
  | (f, z, y) :: ws, k, h => by
    have hrest := deepSum_mem_code D hD a ws (k + 1) fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
    have hw := deepQuotient_mem_code D hD (h _ List.mem_cons_self)
    have hsplit : (fun x ↦ ((((f, z, y) :: ws).zipIdx k).map fun ((f, z, y), j) ↦
        a ^ j * (y - algebraMap F 𝕂 (f x)) / (z - lift (basePoint m x))).sum) =
        a ^ k • (fun x ↦ (y - algebraMap F 𝕂 (f x)) / (z - D x)) +
          fun x ↦ ((ws.zipIdx (k + 1)).map fun ((f, z, y), j) ↦
            a ^ j * (y - algebraMap F 𝕂 (f x)) / (z - lift (basePoint m x))).sum := by
      funext x
      simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hD x, mul_div_assoc]
    rw [hsplit]
    exact add_mem (Submodule.smul_mem _ _ hw) hrest

variable {withLookups : Bool} {S : Setup EF withLookups}

/-- **Batched DEEP words of words that open low are codewords.** If every word opened on the domain
`g ⟨ω_m⟩` opens low, its batched DEEP word is a codeword of their degree bound. -/
theorem groupDeepWord_mem_code (p : Prover S) (lα lβ α ζ a : 𝕂) {m n : ℕ}
    (D : Domain.SmoothCosetFftDomain m 𝕂) (hD : ∀ x, D x = algebraMap F 𝕂 (basePoint m x))
    (h : ∀ w ∈ groupOpened p lα lβ α ζ m, OpensLow m n w) :
    groupDeepWord p lα lβ α ζ a m ∈ ReedSolomon.code (D : Fin (2 ^ m) ↪ 𝕂) n :=
  deepSum_mem_code D hD a _ 0 h

/-- An instance's words that open low on its domain open low read on a domain of its size. -/
theorem onSize_opensLow (i : Fin S.k) (m : ℕ)
    (words : List (((S.instanceSetup i).Point → F) × 𝕂 × 𝕂))
    (h : ∀ w ∈ words, OpensLow (S.logN i + S.params.logBlowup) (2 ^ S.logN i) w) :
    ∀ w ∈ onSize i m words, OpensLow m (2 ^ (m - S.params.logBlowup)) w := by
  intro w hw
  unfold onSize at hw
  split_ifs at hw with hm
  · subst hm
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    obtain ⟨hz, P, hP, hf, hy⟩ := h w' hw'
    refine ⟨hz, P, by rwa [Nat.add_sub_cancel], fun x ↦ ?_, hy⟩
    simp only [Fin.cast_eq_self]
    exact hf x
  · exact absurd hw List.not_mem_nil

end Deep

/-- A sum over the present entries of a vector of options. -/
theorem sum_filterMap_ofFn {α β : Type*} [AddCommMonoid β] (g : α → β) :
    ∀ {k : ℕ} (f : Fin k → Option α),
      (((List.ofFn f).filterMap id).map g).sum = ∑ i, ((f i).map g).getD 0
  | 0, _ => by
    simp only [List.ofFn_zero, List.filterMap_nil, List.map_nil, List.sum_nil,
      Finset.univ_eq_empty, Finset.sum_empty]
  | k + 1, f => by
    rw [List.ofFn_succ, Fin.sum_univ_succ, ← sum_filterMap_ofFn g (fun i ↦ f i.succ)]
    rcases hf : f 0 with _ | x
    · simp only [List.filterMap_cons, id, Option.map_none, Option.getD_none, zero_add]
    · simp only [List.filterMap_cons, id, List.map_cons, List.sum_cons, Option.map_some,
        Option.getD_some]

/-! ### The honest prover -/

namespace Setup
variable (S : Setup EF) (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F)

/-- Instance `i` as an instance of the specification's batch: its AIR, trace length and
lookups. -/
abbrev specInstance (i : Fin S.k) : CompStark.Batch.Instance F := ⟨S.air i, S.logN i, S.lookups i⟩

/-- Instance `i` is one of the batch's instances. -/
theorem specInstance_mem (i : Fin S.k) : S.specInstance i ∈ S.instances :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Instance `i`'s lookup challenges after `(α_L, β_L)` in the challenge field: the
specification's layout of the pair (`challengeLayout`). -/
noncomputable def lookupChallenges (lα lβ : 𝕂) (i : Fin S.k) : List EF :=
  (challengeLayout (S.instances.map (·.lookups)) (Challenge.toSpec.symm lα)
    (Challenge.toSpec.symm lβ)).getD i []

/-- Under the lookup challenges `(α_L, β_L)`, no lookup denominator vanishes: on no row of any
instance does a tuple of non-zero multiplicity have a zero denominator (`NoPoleAt`). -/
def NoPole (lα lβ : 𝕂) : Prop :=
  ∀ i, ∀ r < 2 ^ S.logN i, NoPoleAt (S.air i) (S.lookups i) (S.logN i) (traces i)
    (publicValues i) (S.lookupChallenges lα lβ i) r

/-- Instance `i`'s honest permutation trace and terminal after `(α_L, β_L)`
(`permutationTrace`). -/
noncomputable def honestPermutation (lα lβ : 𝕂) (i : Fin S.k) : Array EF × EF :=
  permutationTrace (S.air i) (S.lookups i) (S.logN i) (traces i) (publicValues i)
    (S.lookupChallenges lα lβ i)

/-- Instance `i`'s honest permutation trace extended onto its domain, in base coordinates, `d`
per column: coordinate `e` of column `c` is column `c d + e`. -/
noncomputable def honestPermExt (lα lβ : 𝕂) (i : Fin S.k) : Stark.Mat F :=
  ldeRef (S.logN i) S.params.logBlowup gen (((S.lookups i).length + 1) * Challenge.d EF)
    (flatten (S.honestPermutation traces publicValues lα lβ i).1)

/-- The values at `z` of instance `i`'s honest permutation trace's columns, in base coordinates;
none without lookups. -/
noncomputable def honestPermOpened (lα lβ : 𝕂) (i : Fin S.k) (z : EF) : Array EF :=
  if (S.lookups i).isEmpty then #[]
  else Fri.openedAt S.params.logBlowup (S.honestPermExt traces publicValues lα lβ i) z

/-- Instance `i`'s honest permutation trace's extension is a low-degree extension of as many
polynomials as its columns' coordinates. -/
theorem honestPermExt_isLde (lα lβ : 𝕂) (i : Fin S.k) : ∃ ps : List F[X],
    Mat.IsLde S.params.logBlowup (S.logN i + S.params.logBlowup)
      (S.honestPermExt traces publicValues lα lβ i) ps ∧
      ps.length = ((S.lookups i).length + 1) * Challenge.d EF :=
  let ⟨ps, hlde, _⟩ := matrix_lde S.params.logBlowup (S.logN i)
    (((S.lookups i).length + 1) * Challenge.d EF)
    (flatten (S.honestPermutation traces publicValues lα lβ i).1) (S.valid i).twoAdic
  ⟨ps, hlde, hlde.1.symm⟩

/-- The batch's lookup messages are the specification's messages of its instances. -/
theorem messages_instances :
    CompStark.Batch.messages S.instances (List.ofFn traces) (List.ofFn publicValues) =
      S.messages traces publicValues := by
  rw [CompStark.Batch.messages, Setup.messages, map_lookups_instances, Setup.instances,
    List.ofFn_eq_map, List.ofFn_eq_map (f := traces), List.ofFn_eq_map (f := publicValues),
    List.zip_map', List.zip_map', List.zip_map_left, List.flatMap_map]
  rfl

/-- **The honest terminals sum to zero** when every bus balances (`terminals_sum_eq_zero`). -/
theorem terminals_honest (hbal : S.Balanced traces publicValues) (lα lβ : 𝕂) :
    (∑ i with S.lookups i ≠ [],
      Challenge.toSpec (S.honestPermutation traces publicValues lα lβ i).2) = 0 := by
  have hk : S.instances.length = S.k := List.length_ofFn
  have h := CompStark.Batch.terminals_sum_eq_zero S.instances (List.ofFn traces)
    (List.ofFn publicValues) (by rw [List.length_ofFn, hk]) (by rw [List.length_ofFn, hk])
    (fun key ↦ by rw [messages_instances]; exact hbal key) (Challenge.toSpec.symm lα)
    (Challenge.toSpec.symm lβ)
  have hperm : CompStark.Batch.permutations S.instances (List.ofFn traces) (List.ofFn publicValues)
      (challengeLayout (S.instances.map (·.lookups)) (Challenge.toSpec.symm lα)
        (Challenge.toSpec.symm lβ)) = List.ofFn fun i ↦
        if (S.lookups i).isEmpty then none
        else some (S.honestPermutation traces publicValues lα lβ i) := by
    refine List.ext_getElem ?_ fun j h1 h2 ↦ ?_
    · simp only [CompStark.Batch.permutations, List.length_map, List.length_zip, List.length_ofFn,
        length_challengeLayout, hk, Nat.min_self]
    · simp only [CompStark.Batch.permutations, List.getElem_map, List.getElem_zip,
        List.getElem_ofFn, Setup.instances]
      rw [honestPermutation, lookupChallenges, List.getD_eq_getElem]
      rfl
  have h' := congrArg Challenge.toSpec h
  rw [hperm, List.map_ofFn, Lookup.toSpec_foldl_add, Challenge.toSpec_zero, zero_add,
    sum_filterMap_ofFn] at h'
  refine (Finset.sum_filter _ _).trans (Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h')
  by_cases he : (S.lookups i).isEmpty
  · simp only [List.isEmpty_iff.mp he, ne_eq, not_true_eq_false, ↓reduceIte, Function.comp_apply,
      List.isEmpty_nil, Option.map_none, Option.getD_none]
  · simp only [ne_eq, List.isEmpty_iff.not.mp he, not_false_eq_true, ↓reduceIte,
      Function.comp_apply, he, Bool.false_eq_true, Option.map_some, Option.getD_some]

variable [Poseidon2Field F]

/-- Instance `i`'s honest quotient chunks after `α`, extended onto its domain
(`honestChunks`). -/
noncomputable def honestChunks (lα lβ α : 𝕂) (i : Fin S.k) : List (Stark.Mat F) :=
  CompStark.Batch.honestChunks S.params (S.specInstance i) (traces i) (publicValues i)
    (S.lookupChallenges lα lβ i) (Challenge.toSpec.symm α)

/-- Instance `i`'s honest opened values after `α` and `ζ` (`honestOpened`). -/
noncomputable def honestOpenedValues (lα lβ α ζ : 𝕂) (i : Fin S.k) : OpenedValues EF :=
  honestOpened S.params.logBlowup (S.air i) (S.logN i) ((S.instanceSetup i).honestExt (traces i))
    (S.honestChunks traces publicValues lα lβ α i) (Challenge.toSpec.symm ζ)

/-- The honest prover of a batch's traces: every instance's trace, permutation trace and quotient
chunks extended onto its domain, its terminal, and the values of their polynomials at `ζ` and
`ζ ω_n`. -/
noncomputable def honestProver : Prover S where
  trace i j x := rowValue ((S.instanceSetup i).honestExt (traces i)) _ j x
  perm lα lβ i c e x :=
    rowValue (S.honestPermExt traces publicValues lα lβ i) _ (c * Challenge.d EF + e) x
  terminal lα lβ i := Challenge.toSpec (S.honestPermutation traces publicValues lα lβ i).2
  quotient lα lβ α i c e x :=
    rowValue ((S.honestChunks traces publicValues lα lβ α i).getD c ⟨0, 0, #[]⟩) _ e x
  openings lα lβ α ζ i := openingsOf (S.instanceSetup i)
    (S.honestOpenedValues traces publicValues lα lβ α ζ i)
    (S.honestPermOpened traces publicValues lα lβ i (Challenge.toSpec.symm ζ))
    (S.honestPermOpened traces publicValues lα lβ i
      (Challenge.toSpec.symm ζ * Ext.ofBase (twoAdicGen (S.logN i))))

variable {S traces publicValues}

/-! ### The honest prover's words -/

/-- Instance `i`'s honest quotient chunks: the extensions of a quotient's values on the cosets of
its quotient domain. -/
theorem honestChunks_eq (lα lβ α : 𝕂) (i : Fin S.k) : ∃ qs : Array EF,
    S.honestChunks traces publicValues lα lβ α i =
      (List.range (2 ^ (S.specInstance i).logQuotientChunks)).map fun c ↦
        ldeRef (S.logN i) S.params.logBlowup
          (gen * (gen * powF (twoAdicGen (S.logN i + (S.specInstance i).logQuotientChunks)) c)⁻¹)
          (Challenge.d EF) (chunkValues qs (2 ^ (S.specInstance i).logQuotientChunks) c
            (2 ^ S.logN i)) :=
  ⟨_, rfl⟩

variable (lα lβ α ζ : Challenge.Spec EF) (i : Fin S.k)

/-- The honest trace words open low. -/
theorem mainOpened_honest (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    ∀ w ∈ mainOpened ((S.honestProver traces publicValues).instanceProver lα lβ i) α ζ,
      OpensLow (S.logN i + S.params.logBlowup) (2 ^ S.logN i) w := by
  intro w hw
  simp only [mainOpened, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hw
  rcases hw with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (S.instanceSetup i).traceAt_opensLow (traces i) _ _ _ hζ j
  · exact (S.instanceSetup i).traceNext_opensLow (traces i) _ _ _ hζ j

/-- The honest quotient chunks open low. -/
theorem quotientOpened_honest (config : CompStark.Batch.ValidConfig S.params S.instances)
    (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    ∀ w ∈ quotientOpened ((S.honestProver traces publicValues).instanceProver lα lβ i) α ζ,
      OpensLow (S.logN i + S.params.logBlowup) (2 ^ S.logN i) w := by
  intro w hw
  simp only [quotientOpened, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hw
  obtain ⟨c, e, rfl⟩ := hw
  have hc : c.val < 2 ^ (S.specInstance i).logQuotientChunks := lt_of_lt_of_eq c.isLt (by
    show 2 ^ (S.instanceSetup i).logChunks = _
    rw [logChunks_eq S i])
  obtain ⟨qs, hqs⟩ := S.honestChunks_eq (traces := traces) (publicValues := publicValues) lα lβ α i
  obtain ⟨cps, hcl, hclen⟩ := chunk_isLde (EF := EF) S.params (S.logN i) _ qs (S.valid i).twoAdic
    (config.chunksFit _ (S.specInstance_mem i)) c
  have h := Iop.Setup.lde_opensLow (S := S.instanceSetup i) hcl (j := e) (by omega)
    (outsideBase_symm hζ)
  rw [RingEquiv.apply_symm_apply] at h
  simp only [Prover.instanceProver, honestProver, openingsOf, honestOpenedValues, honestOpened,
    hqs, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hc, Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD]
  rw [Array.getD_eq_getD_getElem?] at h
  exact h

/-- The preprocessed words open low. -/
theorem preprocessedOpened_honest (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    ∀ w ∈ preprocessedOpened ((S.honestProver traces publicValues).instanceProver lα lβ i) α ζ,
      OpensLow (S.logN i + S.params.logBlowup) (2 ^ S.logN i) w := by
  intro w hw
  simp only [preprocessedOpened, List.mem_append, List.mem_map, List.mem_finRange, true_and]
    at hw
  rcases hw with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (S.instanceSetup i).preprocessedAt_opensLow (traces i) _ _ _ hζ j
  · exact (S.instanceSetup i).preprocessedNext_opensLow (traces i) _ _ _ hζ j

/-- The honest permutation words open low. -/
theorem permOpened_honest (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    ∀ w ∈ permOpened ((S.honestProver traces publicValues).instanceProver lα lβ i) α ζ,
      OpensLow (S.logN i + S.params.logBlowup) (2 ^ S.logN i) w := by
  intro w hw
  simp only [permOpened, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and] at hw
  have hlook : ∀ c : Fin (S.instanceSetup i).permWidth, (S.lookups i).isEmpty = false ∧
      c.val < (S.lookups i).length + 1 := fun c ↦ by
    have hc := lt_of_lt_of_eq c.isLt (permWidth_eq (S.instanceSetup i))
    split_ifs at hc with he
    · omega
    · exact ⟨Bool.eq_false_iff.mpr he, hc⟩
  obtain ⟨ps, hlde, hlen⟩ := honestPermExt_isLde S traces publicValues lα lβ i
  have hidx : ∀ (c : Fin (S.instanceSetup i).permWidth) (e : Fin (Challenge.d EF)),
      c.val * Challenge.d EF + e.val < ps.length := fun c e ↦ by
    rw [hlen]
    have := (hlook c).2
    have := e.isLt
    nlinarith
  rcases hw with ⟨c, e, rfl⟩ | ⟨c, e, rfl⟩
  · have h := Iop.Setup.lde_opensLow (S := S.instanceSetup i) hlde (hidx c e)
      (outsideBase_symm hζ)
    rw [RingEquiv.apply_symm_apply] at h
    simp only [Prover.instanceProver, honestProver, openingsOf, honestPermOpened, (hlook c).1,
      Bool.false_eq_true, ↓reduceIte]
    exact h
  · obtain ⟨hzn, hzn'⟩ := (S.instanceSetup i).outsideBase_next hζ
    have h := Iop.Setup.lde_opensLow (S := S.instanceSetup i) hlde (hidx c e) hzn
    rw [hzn'] at h
    simp only [Prover.instanceProver, honestProver, openingsOf, honestPermOpened, (hlook c).1,
      Bool.false_eq_true, ↓reduceIte]
    exact h

/-- Every word the honest prover opens on a domain of `2 ^ m` points opens low. -/
theorem groupOpened_honest (config : CompStark.Batch.ValidConfig S.params S.instances)
    (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) (m : ℕ) :
    ∀ w ∈ groupOpened (S.honestProver traces publicValues) lα lβ α ζ m,
      OpensLow m (2 ^ (m - S.params.logBlowup)) w := by
  intro w hw
  simp only [groupOpened, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and] at hw
  rcases hw with (((⟨i, hw⟩ | ⟨i, hw⟩) | ⟨i, hw⟩) | ⟨i, hw⟩)
  · exact onSize_opensLow i m _ (mainOpened_honest lα lβ α ζ i hζ) w hw
  · exact onSize_opensLow i m _ (quotientOpened_honest lα lβ α ζ i config hζ) w hw
  · exact onSize_opensLow i m _ (preprocessedOpened_honest lα lβ α ζ i hζ) w hw
  · exact onSize_opensLow i m _ (permOpened_honest lα lβ α ζ i hζ) w hw

/-- **The honest batched DEEP words are codewords**, for `ζ` off the base field: on every
instance's domain, of degree below its trace length. -/
theorem groupDeepWord_honest_mem_code (config : CompStark.Batch.ValidConfig S.params S.instances)
    (a : 𝕂) (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    groupDeepWord (S.honestProver traces publicValues) lα lβ α ζ a
      (S.logN i + S.params.logBlowup) ∈
      ReedSolomon.code ((S.instanceSetup i).domain :
        Fin (2 ^ (S.logN i + S.params.logBlowup)) ↪ 𝕂) (S.instanceSetup i).n := by
  have h := groupOpened_honest (traces := traces) (publicValues := publicValues) lα lβ α ζ config
    hζ (S.logN i + S.params.logBlowup)
  rw [Nat.add_sub_cancel] at h
  exact groupDeepWord_mem_code _ lα lβ α ζ a _ (S.instanceSetup i).domain_apply h

/-! ### Completeness -/

/-- **The honest openings pass every instance's check at `ζ`**, for traces satisfying the batch,
`ζ` off the base field and no lookup denominator vanishing. -/
theorem constraintsHoldAt_honest (config : CompStark.Batch.ValidConfig S.params S.instances)
    (hsat : S.Satisfied traces publicValues) (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y)
    (hpole : S.NoPole traces publicValues lα lβ) :
    ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
      ((S.honestProver traces publicValues).openings lα lβ α ζ i) (S.challenges lα lβ i)
      ((S.honestProver traces publicValues).terminal lα lβ i) := by
  have hmem := S.specInstance_mem i
  have hfit : Fits S.params (S.air i) (S.logN i) (traces i) :=
    ⟨(hsat.air i).size, (S.valid i).colsInWidth, (S.valid i).twoAdic,
      (config.valid _ hmem).chunksFit, (S.valid i).periodicFits⟩
  have hz := outsideBase_symm hζ
  obtain ⟨hzn, -⟩ := (S.instanceSetup i).outsideBase_next hζ
  obtain ⟨ps, hlde, hlen⟩ := honestPermExt_isLde S traces publicValues lα lβ i
  have hsize : ∀ z : EF, Ext.OutsideBase z →
      (S.honestPermOpened traces publicValues lα lβ i z).size =
        Challenge.d EF * (S.instanceSetup i).permWidth := by
    intro z hz
    rw [permWidth_eq, honestPermOpened]
    split_ifs with he
    · rfl
    · rw [(openedAt_isLde _ _ _ ps z hlde hz).1, hlen, mul_comm]
  have hperm : ∀ m ∈ CompStark.Batch.permLde S.params.logBlowup (S.specInstance i) (traces i)
      (publicValues i) (S.lookupChallenges lα lβ i),
      S.honestPermOpened traces publicValues lα lβ i (Challenge.toSpec.symm ζ) =
          Fri.openedAt S.params.logBlowup m (Challenge.toSpec.symm ζ) ∧
        S.honestPermOpened traces publicValues lα lβ i
            (Challenge.toSpec.symm ζ * Ext.ofBase (twoAdicGen (S.logN i))) =
          Fri.openedAt S.params.logBlowup m
            (Challenge.toSpec.symm ζ * Ext.ofBase (twoAdicGen (S.logN i))) ∧
        (S.honestPermutation traces publicValues lα lβ i).2 =
          (permutationTrace (S.air i) (S.lookups i) (S.logN i) (traces i) (publicValues i)
            (S.lookupChallenges lα lβ i)).2 := by
    intro m hm
    unfold CompStark.Batch.permLde at hm
    split_ifs at hm with he
    · exact absurd hm (Option.not_mem_none _)
    · rw [Option.mem_def, Option.some_inj] at hm
      subst hm
      have ho : ∀ z, S.honestPermOpened traces publicValues lα lβ i z =
          Fri.openedAt S.params.logBlowup (S.honestPermExt traces publicValues lα lβ i) z :=
        fun z ↦ by rw [honestPermOpened, ite_eq_right_of_eq_false _ _ (eq_false he)]
      exact ⟨ho _, ho _, rfl⟩
  have hcheck := CompStark.Batch.instanceCheck_honest S.params (S.specInstance i) (traces i)
    (publicValues i) (S.lookupChallenges lα lβ i) (Challenge.toSpec.symm α)
    (Challenge.toSpec.symm ζ) hfit (config.chunksFit _ hmem) (hsat.air i).vanish
    (config.degreeFits _ hmem) (config.lookupDegreeFits _ hmem) (config.lookupsFit _ hmem)
    (hpole i) hz _ _ _ hperm
  have hqc : (S.honestOpenedValues traces publicValues lα lβ α ζ i).quotientChunks.size =
      (S.instanceSetup i).chunks := by
    obtain ⟨qs, hqs⟩ := S.honestChunks_eq (traces := traces) (publicValues := publicValues)
      lα lβ α i
    simp only [honestOpenedValues, honestOpened, hqs, List.size_toArray, List.length_map,
      List.length_range]
    show _ = 2 ^ (S.instanceSetup i).logChunks
    rw [logChunks_eq S i]
  have h := constraintsHoldAt_of_instanceCheck S i (publicValues i) _ _ _ _ _ _ _ hqc
    (hsize _ hz) (hsize _ hzn) hcheck
  have hchs : (S.lookupChallenges lα lβ i).map Challenge.toSpec = S.challenges lα lβ i := by
    have := challenges_eq S (Challenge.toSpec.symm lα) (Challenge.toSpec.symm lβ) i
    rwa [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at this
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hchs] at h
  exact h

/-- **Completeness.** For a valid batch and traces satisfying it, the honest prover's strategy is
accepted on every execution whose out-of-domain point `ζ` lies off the base field, so off every
trace domain and every instance's domain, and under whose lookup challenges no lookup denominator
vanishes. -/
theorem completeness (config : CompStark.Batch.ValidConfig S.params S.instances)
    (hsat : S.Satisfied traces publicValues) :
    ∀ result ∈ support (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl (S.honestProver traces publicValues).strategy
      (S.verifier publicValues)),
      (∀ y : F, S.zetaOf result.1 ≠ algebraMap F 𝕂 y) →
      S.NoPole traces publicValues (S.lookupOf result.1).1 (S.lookupOf result.1).2 →
      result.2.2 = true :=
  fun result hres hζ hpole ↦ Prover.strategy_accepts _ publicValues result hres
    ⟨terminals_honest S traces publicValues hsat.balanced _ _,
      fun i ↦ constraintsHoldAt_honest _ _ _ _ i config hsat hζ hpole⟩
    fun i ↦ groupDeepWord_honest_mem_code _ _ _ _ i config _ hζ

end Setup

end CompStark.Iop.Batch
