/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.FriInject

/-! # FRI with injected inputs, as an interactive protocol

Plonky3's FRI over inputs of several heights, on a domain `ω` of `2 ^ n` points: the prover
commits to the tallest input again as its first word `f₀`; each round the verifier samples `β`,
and the prover commits to the next word, meant to be `f` folded by `2 ^ k` at `β`, plus `β ^ 2 ^ k`
times the input of the folded domain's height if there is one (`Rounds`: the folds and the
injected inputs); after the last round it sends the final polynomial, a codeword
(`Messages`). The verifier samples `t` query positions of `ω`; each passes if the first word
agrees with the tallest input there and every fold above it is consistent (`InjectTrace.accepting`
of the realized `trace`). `acceptance` is the probability that every query passes, against the
best prover.

`acceptance_le`: if the tallest input or an injected input is `δ`-far from its code, the
acceptance is at most `error`: each fold's lossy MCA error (`foldError`; the powers of `β` over
`2 ^ k` coefficient words, and the injected input with them) and `(1 - δ + m · loss) ^ t` for the
queries, `m` folds, at the best proximity loss. Each fold is bad with probability at most its
error whatever the prover committed before it (`FriInject.lossyInjectFailure_prob_le`, ArkLib's
`lossyFoldingAgreementFailure_prob_le_powers`); on a run without a bad fold, the passing
positions are few (`FriInject.InjectTrace.consistent_density_le`).
-/

@[expose] public section

namespace CompStark.Sound.FriGame

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions Fri FriInject
open OracleComp
open scoped BigOperators ProbabilityTheory NNReal

variable {K : Type}

/-- FRI's rounds from a domain of `2 ^ n` points: each folds by `2 ^ k` and may inject an input
word of the folded domain's size. -/
inductive Rounds (K : Type) : ℕ → Type
  | final {n : ℕ} : Rounds K n
  | fold {n : ℕ} (k : ℕ) (hk : k ≤ n) (input : Option (Fin (2 ^ (n - k)) → K))
      (rest : Rounds K (n - k)) : Rounds K n

namespace Rounds

/-- The number of folds. -/
def numFolds : {n : ℕ} → Rounds K n → ℕ
  | _, .final => 0
  | _, .fold _ _ _ rest => rest.numFolds + 1

/-- The degree bound of the code before the rounds, for a final degree bound `d`. -/
def degree (d : ℕ) : {n : ℕ} → Rounds K n → ℕ
  | _, .final => d
  | _, .fold k _ _ rest => 2 ^ k * rest.degree d

theorem degree_pos {d : ℕ} (hd : 0 < d) : ∀ {n : ℕ} (r : Rounds K n), 0 < r.degree d
  | _, .final => hd
  | _, .fold _ _ _ rest => Nat.mul_pos (Nat.two_pow_pos _) (degree_pos hd rest)

/-- A sum over challenge vectors splits into the first challenge and the rest. -/
theorem sum_split [Fintype K] {m : ℕ} (g : (Fin (m + 1) → K) → ENNReal) :
    ∑ βs : Fin (m + 1) → K, g βs = ∑ β : K, ∑ βs : Fin m → K, g (Fin.cons β βs) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ ↦ K).symm _ _ fun βs ↦ by
    simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.cons_self_tail])

variable [Field K]

/-- Every injected input agrees with a codeword of its code on a set of at least `ρ` of its
domain. -/
def InputsAgree (d : ℕ) (ρ : ℝ) : {n : ℕ} → SmoothCosetFftDomain n K → Rounds K n → Prop
  | _, _, .final => True
  | _, ω, .fold k _ none rest => rest.InputsAgree d ρ (ω.subdomain k)
  | _, ω, .fold k _ (some g) rest =>
      Agrees (ω.subdomain k) (rest.degree d) ρ g ∧ rest.InputsAgree d ρ (ω.subdomain k)

/-- The prover's messages: the word it commits to at each round, each after the challenges before
it, and the final codeword. -/
inductive Messages (d : ℕ) : {n : ℕ} → SmoothCosetFftDomain n K → Rounds K n → Type
  | final {n : ℕ} {ω : SmoothCosetFftDomain n K} (w : Fin (2 ^ n) → K) (hw : w ∈ code ω d) :
      Messages d ω .final
  | fold {n k : ℕ} {ω : SmoothCosetFftDomain n K} {hk : k ≤ n}
      {input : Option (Fin (2 ^ (n - k)) → K)} {rest : Rounds K (n - k)}
      (f : Fin (2 ^ n) → K) (next : K → Messages d (ω.subdomain k) rest) :
      Messages d ω (.fold k hk input rest)

/-- The run of the rounds on the prover's messages and the folding challenges `βs`, as the data the
queries read. -/
def trace (d : ℕ) (hd : 0 < d) : {n : ℕ} → {ω : SmoothCosetFftDomain n K} → {r : Rounds K n} →
    Messages d ω r → (Fin r.numFolds → K) → InjectTrace ω (r.degree d)
  | _, _, .final, .final w _, _ => .terminal w
  | _, _, .fold _ hk none rest, .fold f next, βs =>
      .fold hk (degree_pos hd rest) f (βs ⟨0, Nat.succ_pos _⟩)
        (trace d hd (next (βs ⟨0, Nat.succ_pos _⟩)) fun j ↦ βs j.succ)
  | _, _, .fold _ hk (some g) rest, .fold f next, βs =>
      .inject hk (degree_pos hd rest) f (βs ⟨0, Nat.succ_pos _⟩) g
        (trace d hd (next (βs ⟨0, Nat.succ_pos _⟩)) fun j ↦ βs j.succ)

/-- The realized trace has the rounds' number of folds. -/
theorem numFolds_trace {d : ℕ} (hd : 0 < d) : ∀ {n : ℕ} {ω : SmoothCosetFftDomain n K} {r : Rounds K n}
    (m : Messages d ω r) (βs : Fin r.numFolds → K), (trace d hd m βs).numFolds = r.numFolds
  | _, _, .final, .final _ _, _ => rfl
  | _, _, .fold _ _ none _, .fold _ next, _ => congrArg (· + 1) (numFolds_trace hd (next _) _)
  | _, _, .fold _ _ (some _) _, .fold _ next, _ => congrArg (· + 1) (numFolds_trace hd (next _) _)

/-- The realized trace's final word is a codeword. -/
theorem finalInCode_trace {d : ℕ} (hd : 0 < d) : ∀ {n : ℕ} {ω : SmoothCosetFftDomain n K} {r : Rounds K n}
    (m : Messages d ω r) (βs : Fin r.numFolds → K), (trace d hd m βs).FinalInCode
  | _, _, .final, .final _ hw, _ => hw
  | _, _, .fold _ _ none _, .fold _ next, _ => finalInCode_trace hd (next _) _
  | _, _, .fold _ _ (some _) _, .fold _ next, _ => finalInCode_trace hd (next _) _

/-- The realized trace's injected words are the rounds' inputs. -/
theorem inputsAgree_trace {d : ℕ} (hd : 0 < d) (ρ : ℝ) : ∀ {n : ℕ} {ω : SmoothCosetFftDomain n K} {r : Rounds K n}
    (m : Messages d ω r) (βs : Fin r.numFolds → K),
      (trace d hd m βs).InputsAgree ρ ↔ r.InputsAgree d ρ ω
  | _, _, .final, .final _ _, _ => Iff.rfl
  | _, _, .fold _ _ none _, .fold _ next, _ => inputsAgree_trace hd ρ (next _) _
  | _, _, .fold _ _ (some _) _, .fold _ next, _ =>
      and_congr Iff.rfl (inputsAgree_trace hd ρ (next _) _)

/-- The folds' errors at proximity `θ` and loss `loss`: the lossy MCA error of the powers of `β`
over the fold's `2 ^ k` coefficient words, and its injected input. -/
noncomputable def foldError [Fintype K] [DecidableEq K] [SampleableType K] (d : ℕ) (θ loss : ℝ) :
    {n : ℕ} → SmoothCosetFftDomain n K → Rounds K n → ENNReal
  | _, _, .final => 0
  | n, ω, .fold k _ none rest =>
      lossyMcaError (univariatePowersGenerator K (2 ^ k - 1))
        (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss +
      rest.foldError d θ loss (ω.subdomain k)
  | n, ω, .fold k _ (some _) rest =>
      lossyMcaError (univariatePowersGenerator K (2 ^ k))
        (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss +
      rest.foldError d θ loss (ω.subdomain k)

end Rounds

open Rounds

variable [Field K] [Fintype K] [DecidableEq K]

/-- The probability that FRI's queries all pass against the best prover: over uniform folding
challenges and `t` uniform query positions, every query lands where every fold is consistent and
the prover's first word agrees with the tallest input `word`. -/
noncomputable def acceptance {n : ℕ} (ω : SmoothCosetFftDomain n K) (r : Rounds K n) (d t : ℕ)
    (hd : 0 < d) (word : Fin (2 ^ n) → K) : ENNReal :=
  ⨆ messages : Messages d ω r, (Fintype.card K : ENNReal)⁻¹ ^ r.numFolds *
    ∑ βs : Fin r.numFolds → K,
      Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[∀ j, xs j ∈ (trace d hd messages βs).accepting ∧
        (trace d hd messages βs).initial (xs j) = word (xs j)]

/-- FRI's soundness error at proximity `δ`, at the best proximity loss: the folds' errors and
`(1 - δ + m · loss) ^ t` for the queries. -/
noncomputable def error [SampleableType K] {n : ℕ} (ω : SmoothCosetFftDomain n K) (r : Rounds K n) (d t : ℕ)
    (δ : ℝ) : ENNReal :=
  ⨅ loss : ℝ≥0, r.foldError d δ loss ω + ENNReal.ofReal (1 - δ + r.numFolds * loss) ^ t

/-! ### Soundness -/

namespace Rounds

variable {d : ℕ} (hd : 0 < d)

open Classical in
/-- A run has a bad fold with probability at most the folds' errors, whatever the prover. -/
theorem prob_unsafe_le [SampleableType K] (θ loss : ℝ) : ∀ {n : ℕ} {ω : SmoothCosetFftDomain n K}
    {r : Rounds K n} (m : Messages d ω r),
      (Fintype.card K : ENNReal)⁻¹ ^ r.numFolds * ∑ βs : Fin r.numFolds → K,
        (if (trace d hd m βs).SafeLossy θ loss then 0 else 1) ≤ r.foldError d θ loss ω
  | _, _, .final, .final _ _ => by
    simp only [trace, InjectTrace.SafeLossy, ↓reduceIte, Finset.sum_const_zero, mul_zero,
      foldError, le_refl]
  | n, ω, .fold k hk input rest, .fold f next => by
    have hK : (Fintype.card K : ENNReal) ≠ 0 := by simp
    have hKt : (Fintype.card K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- The fold's bad event, for the first challenge.
    set Fail : K → Prop := fun β ↦ match input with
      | none => LossyFoldingAgreementFailure ω f k (rest.degree d) θ loss β
      | some g => LossyInjectFailure ω f k (rest.degree d) g θ loss β
    set ε : ENNReal := match input with
      | none => lossyMcaError (univariatePowersGenerator K (2 ^ k - 1))
          (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss
      | some _ => lossyMcaError (univariatePowersGenerator K (2 ^ k))
          (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d)) θ loss
    have hε : ((Finset.univ.filter Fail).card : ENNReal) / Fintype.card K ≤ ε := by
      rw [← SampleableType.prEvent_uniformSample]
      cases input
      · exact lossyFoldingAgreementFailure_prob_le_powers ω f (degree_pos hd rest) θ loss
      · exact lossyInjectFailure_prob_le ω f _ (degree_pos hd rest) θ loss
    have herr : (fold k hk input rest).foldError d θ loss ω =
        ε + rest.foldError d θ loss (ω.subdomain k) := by
      cases input <;> rfl
    have hsafe (β : K) (βs : Fin rest.numFolds → K) :
        (trace d hd (Messages.fold (hk := hk) (input := input) f next)
          (Fin.cons β βs)).SafeLossy θ loss ↔
          ¬ Fail β ∧ (trace d hd (next β) βs).SafeLossy θ loss := by
      cases input <;> exact Iff.rfl
    have hpoint (β : K) (βs : Fin rest.numFolds → K) :
        (if (trace d hd (Messages.fold (hk := hk) (input := input) f next)
          (Fin.cons β βs)).SafeLossy θ loss then (0 : ENNReal) else 1) ≤
        (if Fail β then 1 else 0) +
          if (trace d hd (next β) βs).SafeLossy θ loss then 0 else 1 := by
      rw [if_congr (hsafe β βs) rfl rfl]
      by_cases h1 : Fail β <;> by_cases h2 : (trace d hd (next β) βs).SafeLossy θ loss <;>
        simp only [h1, h2, not_true_eq_false, not_false_eq_true, and_true, and_false,
          ↓reduceIte, zero_add, add_zero] <;>
        first | exact le_rfl | exact le_self_add
    change (Fintype.card K : ENNReal)⁻¹ ^ (rest.numFolds + 1) *
        ∑ βs : Fin (rest.numFolds + 1) → K, _ ≤ _
    rw [sum_split, herr, pow_succ']
    calc (Fintype.card K : ENNReal)⁻¹ * (Fintype.card K : ENNReal)⁻¹ ^ rest.numFolds *
          ∑ β : K, ∑ βs : Fin rest.numFolds → K,
            (if (trace d hd (Messages.fold (hk := hk) (input := input) f next)
              (Fin.cons β βs)).SafeLossy θ loss then (0 : ENNReal) else 1)
        ≤ (Fintype.card K : ENNReal)⁻¹ * ∑ β : K, ((if Fail β then 1 else 0) +
            (Fintype.card K : ENNReal)⁻¹ ^ rest.numFolds * ∑ βs : Fin rest.numFolds → K,
              if (trace d hd (next β) βs).SafeLossy θ loss then 0 else 1) := by
          rw [mul_assoc, Finset.mul_sum]
          refine mul_le_mul_right (Finset.sum_le_sum fun β _ ↦ ?_) _
          refine (mul_le_mul_right (Finset.sum_le_sum fun βs _ ↦ hpoint β βs) _).trans ?_
          rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ,
            Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
          refine add_le_add (le_of_eq ?_) le_rfl
          rw [Nat.cast_pow, ← mul_pow, ENNReal.inv_mul_cancel hK hKt, one_pow, one_mul]
      _ ≤ (Fintype.card K : ENNReal)⁻¹ * ∑ β : K, ((if Fail β then 1 else 0) +
            rest.foldError d θ loss (ω.subdomain k)) :=
          mul_le_mul_right (Finset.sum_le_sum fun β _ ↦
            add_le_add le_rfl (prob_unsafe_le θ loss (next β))) _
      _ = ((Finset.univ.filter Fail).card : ENNReal) / Fintype.card K +
            rest.foldError d θ loss (ω.subdomain k) := by
          rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hK hKt, one_mul,
            ENNReal.div_eq_inv_mul]
      _ ≤ ε + rest.foldError d θ loss (ω.subdomain k) := add_le_add hε le_rfl

end Rounds

open Classical in
/-- **FRI with injected inputs is sound.** If the tallest input `word` or an injected input is
`δ`-far from its code, FRI accepts with probability at most its error. -/
theorem acceptance_le [SampleableType K] {n : ℕ} (ω : SmoothCosetFftDomain n K) (r : Rounds K n) (d t : ℕ)
    (hd : 0 < d) (word : Fin (2 ^ n) → K) (δ : ℝ)
    (hfar : ¬ (Agrees ω (r.degree d) (1 - δ) word ∧ r.InputsAgree d (1 - δ) ω)) :
    acceptance ω r d t hd word ≤ error ω r d t δ := by
  refine le_iInf fun loss ↦ iSup_le fun m ↦ ?_
  have hK : (Fintype.card K : ENNReal) ≠ 0 := by simp
  have hKt : (Fintype.card K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  set q : ENNReal := ENNReal.ofReal (1 - δ + r.numFolds * loss) ^ t
  -- Each run: `1` if a fold is bad, the query term otherwise.
  have hrun (βs : Fin r.numFolds → K) :
      Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[∀ j, xs j ∈ (trace d hd m βs).accepting ∧
        (trace d hd m βs).initial (xs j) = word (xs j)] ≤
      (if (trace d hd m βs).SafeLossy δ loss then 0 else 1) + q := by
    set tr := trace d hd m βs
    set A := tr.accepting.filter fun i ↦ tr.initial i = word i
    have hA : Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[∀ j, xs j ∈ tr.accepting ∧
        tr.initial (xs j) = word (xs j)] = ((A.card : ENNReal) / Fintype.card (Fin (2 ^ n))) ^ t := by
      rw [← Probability.prob_uniform_pi_mem_finset_eq A t]
      simp only [A, Finset.mem_filter]
    by_cases hs : tr.SafeLossy δ loss
    · rw [ite_eq_left hs, zero_add, hA]
      refine pow_le_pow_left' ?_ t
      have hdens := tr.consistent_density_le word δ δ loss loss.coe_nonneg hs
        (Rounds.finalInCode_trace hd m βs) (by rwa [Rounds.inputsAgree_trace hd _ m βs])
      rw [Rounds.numFolds_trace hd m βs] at hdens
      have hmin : min ((δ : ℝ) - ((r.numFolds : ℝ) - 1) * loss) (δ - r.numFolds * loss) =
          δ - r.numFolds * loss := min_eq_right (by nlinarith [loss.coe_nonneg])
      rw [hmin] at hdens
      have hcast : (A.card : ENNReal) / Fintype.card (Fin (2 ^ n)) =
          ENNReal.ofReal ((A.card : ℝ) / 2 ^ n) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, Fintype.card_fin,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
      rw [hcast]
      exact ENNReal.ofReal_le_ofReal (hdens.trans (le_of_eq (by ring)))
    · rw [ite_eq_right hs]
      exact (prEvent_le_one _).trans le_self_add
  calc (Fintype.card K : ENNReal)⁻¹ ^ r.numFolds * ∑ βs : Fin r.numFolds → K,
        Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[∀ j, xs j ∈ (trace d hd m βs).accepting ∧
          (trace d hd m βs).initial (xs j) = word (xs j)]
      ≤ (Fintype.card K : ENNReal)⁻¹ ^ r.numFolds * ∑ βs : Fin r.numFolds → K,
          ((if (trace d hd m βs).SafeLossy δ loss then 0 else 1) + q) :=
        mul_le_mul_right (Finset.sum_le_sum fun βs _ ↦ hrun βs) _
    _ = (Fintype.card K : ENNReal)⁻¹ ^ r.numFolds * ∑ βs : Fin r.numFolds → K,
          (if (trace d hd m βs).SafeLossy δ loss then 0 else 1) + q := by
        rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ,
          Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, Nat.cast_pow,
          ← mul_pow, ENNReal.inv_mul_cancel hK hKt, one_pow, one_mul]
    _ ≤ r.foldError d δ loss ω + q := add_le_add (Rounds.prob_unsafe_le hd δ loss m) le_rfl

/-- FRI accepts with probability at most `1`. -/
theorem acceptance_le_one {n : ℕ} (ω : SmoothCosetFftDomain n K) (r : Rounds K n) (d t : ℕ)
    (hd : 0 < d) (word : Fin (2 ^ n) → K) : acceptance ω r d t hd word ≤ 1 := by
  refine iSup_le fun m ↦ ?_
  have hK : (Fintype.card K : ENNReal) ≠ 0 := by simp
  have hKt : (Fintype.card K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (Fintype.card K : ENNReal)⁻¹ ^ r.numFolds * ∑ βs : Fin r.numFolds → K,
        Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[∀ j, xs j ∈ (trace d hd m βs).accepting ∧
          (trace d hd m βs).initial (xs j) = word (xs j)]
      ≤ (Fintype.card K : ENNReal)⁻¹ ^ r.numFolds * ∑ _βs : Fin r.numFolds → K, 1 :=
        mul_le_mul_right (Finset.sum_le_sum fun _ _ ↦ prEvent_le_one _) _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          mul_one, Nat.cast_pow, ← mul_pow, ENNReal.inv_mul_cancel hK hKt, one_pow]

end CompStark.Sound.FriGame
