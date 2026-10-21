/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoichi Hirai, Pietro Monticone, Aristotle (Harmonic), Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.QuerySoundness

/-! # FRI's query soundness with words injected mid-folding

ArkLib's FRI query soundness (`Fri.FoldTrace`, `ArkLib/ProofSystem/Fri/QuerySoundness.lean`),
generalized to the folding of Plonky3's FRI over inputs of several heights: a fold may add a word
`g` of the folded domain's size, scaled by `α ^ 2 ^ k`, to the folded word (`InjectTrace.inject`;
Plonky3 rolls the reduced opening of the next height in with `β ^ arity`). The definitions and
the proof follow ArkLib's; only the injected fold is new.

An injected fold combines the `2 ^ k` coefficient words of the fold and `g` by the powers of `α`,
so its bad event (`LossyInjectFailure`) is the lossy MCA event of the powers generator of
`2 ^ k + 1` words (`lossyInjectFailure_prob_le`). On a lossily safe trace, a large set of
accepting queries yields, going down from the final word as in ArkLib, a codeword of the initial
code agreeing with the initial word on most of it, and a codeword of each injected word's code
agreeing with it on a set of at least the accepting density less the losses
(`exists_codeword_agree_on_lossy`). So if any input, the initial word or an injected one, is
`δ`-far from its code, the accepting density is at most
`1 - min (θ - (m - 1) · loss) (δ - m · loss)` for `m` folds (`accepting_density_le_lossy`).

Vendored for CompStark, to be upstreamed to ArkLib with the rest of the injected FRI.
-/

@[expose] public section

namespace CompStark.Sound.FriInject

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions Fri
open CosetFftDomainClass (sqFoldMapGen)
open OracleComp
open scoped BigOperators ProbabilityTheory

variable {F : Type} [Field F]

/-- A word agrees with a codeword of `code domain d` on a set of at least `ρ` of the domain. -/
def Agrees {m : ℕ} (domain : Fin (2 ^ m) ↪ F) (d : ℕ) (ρ : ℝ) (w : Fin (2 ^ m) → F) : Prop :=
  ∃ T : Finset (Fin (2 ^ m)), ρ * 2 ^ m ≤ T.card ∧ ∃ v ∈ code domain d, ∀ x ∈ T, v x = w x

/-- Agreement at a density gives agreement at every smaller density. -/
theorem Agrees.mono {m : ℕ} {domain : Fin (2 ^ m) ↪ F} {d : ℕ} {ρ ρ' : ℝ} (h : ρ' ≤ ρ)
    {w : Fin (2 ^ m) → F} (hw : Agrees domain d ρ w) : Agrees domain d ρ' w := by
  obtain ⟨T, hT, hv⟩ := hw
  exact ⟨T, le_trans (mul_le_mul_of_nonneg_right h (by positivity)) hT, hv⟩

/-! ### Traces with injected words -/

/-- The algebraic data read by FRI's query phase (ArkLib's `FoldTrace`), with folds that may add
an injected word: at each step the degree bound and domain shrink by the folding factor; the last
word is checked for membership in its RS code. -/
inductive InjectTrace : {n : ℕ} → SmoothCosetFftDomain n F → ℕ → Type
  | terminal {n : ℕ} {domain : SmoothCosetFftDomain n F} {d : ℕ}
      (f : Fin (2 ^ n) → F) : InjectTrace domain d
  | fold {n k d : ℕ} {domain : SmoothCosetFftDomain n F}
      (hk : k ≤ n) (hd : 0 < d) (f : Fin (2 ^ n) → F) (α : F)
      (tail : InjectTrace (domain.subdomain k) d) : InjectTrace domain (2 ^ k * d)
  | inject {n k d : ℕ} {domain : SmoothCosetFftDomain n F}
      (hk : k ≤ n) (hd : 0 < d) (f : Fin (2 ^ n) → F) (α : F) (g : Fin (2 ^ (n - k)) → F)
      (tail : InjectTrace (domain.subdomain k) d) : InjectTrace domain (2 ^ k * d)

namespace InjectTrace

variable {n d : ℕ} {domain : SmoothCosetFftDomain n F}

/-- The word at the beginning of a trace. -/
def initial : InjectTrace domain d → (Fin (2 ^ n) → F)
  | .terminal f => f
  | .fold _ _ f _ _ => f
  | .inject _ _ f _ _ _ => f

/-- The final code-membership check. -/
def FinalInCode : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    InjectTrace domain d → Prop
  | _, d, domain, .terminal f => f ∈ code domain d
  | _, _, _, .fold _ _ _ _ tail => tail.FinalInCode
  | _, _, _, .inject _ _ _ _ _ tail => tail.FinalInCode

/-- The number of folds. -/
def numFolds : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} → InjectTrace domain d → ℕ
  | _, _, _, .terminal _ => 0
  | _, _, _, .fold _ _ _ _ tail => tail.numFolds + 1
  | _, _, _, .inject _ _ _ _ _ tail => tail.numFolds + 1

/-- Every injected word agrees with a codeword of its code on a set of at least `ρ` of its
domain. -/
def InputsAgree (ρ : ℝ) : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    InjectTrace domain d → Prop
  | _, _, _, .terminal _ => True
  | _, _, _, .fold _ _ _ _ tail => tail.InputsAgree ρ
  | _, _, domain, .inject (k := k) (d := d) _ _ _ _ g tail =>
      Agrees (domain.subdomain k) d ρ g ∧ tail.InputsAgree ρ

/-- Agreement at a density gives agreement at every smaller density. -/
theorem InputsAgree.mono {ρ ρ' : ℝ} (h : ρ' ≤ ρ) :
    ∀ {n d : ℕ} {domain : SmoothCosetFftDomain n F} (tr : InjectTrace domain d),
      tr.InputsAgree ρ → tr.InputsAgree ρ'
  | _, _, _, .terminal _, _ => trivial
  | _, _, _, .fold _ _ _ _ tail, ht => InputsAgree.mono h tail ht
  | _, _, _, .inject _ _ _ _ _ tail, ht => by
    unfold InputsAgree at ht ⊢
    exact ⟨ht.1.mono h, InputsAgree.mono h tail ht.2⟩

end InjectTrace

variable [DecidableEq F]

/-! ### The injected fold's bad event -/

/-- An injected fold is lossily bad if some large set admits a codeword of the folded word plus
`α ^ 2 ^ k g`, but on no subset of it missing at most `loss · |L'|` points do both the word before
folding lift to a codeword above it and `g` agree with a codeword on it. -/
def LossyInjectFailure {n : ℕ} (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
    (k d : ℕ) (g : Fin (2 ^ (n - k)) → F) (θ loss : ℝ) (α : F) : Prop :=
  ∃ T : Finset (Fin (2 ^ (n - k))),
    (Fintype.card (Fin (2 ^ (n - k))) : ℝ) * (1 - θ) ≤ T.card ∧
    projectedWord (fun x ↦ foldWord domain f k α x + α ^ 2 ^ k * g x) T ∈
      projectedCodeSubmod (code (domain.subdomain k) d) T ∧
    ∀ T' ⊆ T, (T'.card : ℝ) ≥ T.card - loss * Fintype.card (Fin (2 ^ (n - k))) →
      ¬ ((∃ u ∈ code domain (2 ^ k * d),
          ∀ i x, x ∈ T' → domain i ^ (2 ^ k) = domain.subdomain k x → u i = f i) ∧
        projectedWord g T' ∈ projectedCodeSubmod (code (domain.subdomain k) d) T')

/-- The words an injected fold combines by the powers of `α`: the fold's coefficient words, then
`g`. -/
noncomputable def injectWords {n : ℕ} (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
    (k : ℕ) (g : Fin (2 ^ (n - k)) → F) : Fin (2 ^ k + 1) → Fin (2 ^ (n - k)) → F :=
  Fin.lastCases g fun j x ↦ foldWordAuxCoeff domain f k j (domain.subdomain k x)

/-- The powers of `α` combine the injected fold's words into the folded word plus `α ^ 2 ^ k g`. -/
theorem sum_injectWords {n : ℕ} (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
    (k : ℕ) (g : Fin (2 ^ (n - k)) → F) (α : F) (x : Fin (2 ^ (n - k))) :
    ∑ j, univariatePowersGenerator F (2 ^ k) α j • injectWords domain f k g j x =
      foldWord domain f k α x + α ^ 2 ^ k * g x := by
  rw [Fin.sum_univ_castSucc]
  simp only [injectWords, Fin.lastCases_castSucc, Fin.lastCases_last,
    smul_eq_mul, foldWord, foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The injected fold's bad event is contained in the lossy MCA event of its words. -/
theorem isLossyMCA_of_lossyInjectFailure [Fintype F] {n k d : ℕ}
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (g : Fin (2 ^ (n - k)) → F)
    (hd : 0 < d) (θ loss : ℝ) (α : F) (h : LossyInjectFailure domain f k d g θ loss α) :
    IsLossyMCA (univariatePowersGenerator F (2 ^ k)) (code (domain.subdomain k) d) α
      (injectWords domain f k g) θ loss := by
  classical
  obtain ⟨T, hT, hfold, hbad⟩ := h
  refine ⟨T, hT, ?_, fun T' hT' hcard ↦ ?_⟩
  · convert hfold using 2
    exact funext fun x ↦ sum_injectWords domain f k g α x
  · by_contra! hall
    refine hbad T' hT' hcard ⟨exists_codeword_agree_of_coefficients domain f hd T' fun j ↦ ?_, ?_⟩
    · have := hall j.castSucc
      simpa only [injectWords, Fin.lastCases_castSucc] using this
    · have := hall (Fin.last _)
      simpa only [injectWords, Fin.lastCases_last] using this

/-- An injected fold is lossily bad with probability at most the lossy MCA error of the powers
generator of `2 ^ k + 1` words, uniformly over the words. -/
theorem lossyInjectFailure_prob_le [Fintype F] [SampleableType F] {n k d : ℕ}
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (g : Fin (2 ^ (n - k)) → F)
    (hd : 0 < d) (θ loss : ℝ) :
    Pr{let α ←$ᵗ F}[LossyInjectFailure domain f k d g θ loss α] ≤
      lossyMcaError (univariatePowersGenerator F (2 ^ k))
        (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) θ loss := by
  apply le_trans (prEvent_mono _ _ _
    (isLossyMCA_of_lossyInjectFailure domain f g hd θ loss))
  exact le_iSup (fun U ↦ Pr{let α ←$ᵗ F}[
    IsLossyMCA (univariatePowersGenerator F (2 ^ k))
      (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) α U θ loss]) _

namespace InjectTrace

variable {n d : ℕ} {domain : SmoothCosetFftDomain n F}

/-- No fold is lossily bad. -/
def SafeLossy (θ loss : ℝ) : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    InjectTrace domain d → Prop
  | _, _, _, .terminal _ => True
  | _, _, domain, .fold (k := k) (d := d) _ _ f α tail =>
      ¬ LossyFoldingAgreementFailure domain f k d θ loss α ∧ tail.SafeLossy θ loss
  | _, _, domain, .inject (k := k) (d := d) _ _ f α g tail =>
      ¬ LossyInjectFailure domain f k d g θ loss α ∧ tail.SafeLossy θ loss

/-- Initial positions at which every local folding check accepts. -/
noncomputable def accepting : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    InjectTrace domain d → Finset (Fin (2 ^ n))
  | _, _, _, .terminal _ => Finset.univ
  | _, _, domain, .fold (k := k) _ _ f α tail => by
      classical
      exact Finset.univ.filter fun i ↦
        let x := sqFoldMapGen (i := k) i
        foldWord domain f k α x = tail.initial x ∧ x ∈ tail.accepting
  | _, _, domain, .inject (k := k) _ _ f α g tail => by
      classical
      exact Finset.univ.filter fun i ↦
        let x := sqFoldMapGen (i := k) i
        foldWord domain f k α x + α ^ 2 ^ k * g x = tail.initial x ∧ x ∈ tail.accepting

/-- On a lossily safe trace with a valid final word, a large subset `S` of accepting queries
agrees with one original codeword off at most `numFolds · loss · 2 ^ n` of its positions, and
every injected word agrees with a codeword of its code on a set of at least `|S| / 2 ^ n -
numFolds · loss` of its domain. ArkLib's `FoldTrace.exists_codeword_agree_on_lossy`, with the
injected words. -/
theorem exists_codeword_agree_on_lossy (tr : InjectTrace domain d) (θ loss : ℝ)
    (hloss : 0 ≤ loss) (hsafe : tr.SafeLossy θ loss) (hfinal : tr.FinalInCode)
    (S : Finset (Fin (2 ^ n))) (hS : S ⊆ tr.accepting)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) + ((tr.numFolds : ℝ) - 1) * loss * 2 ^ n ≤ S.card) :
    (∃ u ∈ code domain d, ∃ S' ⊆ S, (S.card : ℝ) ≤ S'.card + tr.numFolds * loss * 2 ^ n ∧
      ∀ i ∈ S', u i = tr.initial i) ∧
    tr.InputsAgree (S.card / 2 ^ n - tr.numFolds * loss) := by
  classical
  induction tr with
  | terminal f =>
    exact ⟨⟨f, hfinal, S, subset_rfl, by simp [numFolds], fun _ _ ↦ rfl⟩, trivial⟩
  | @fold n k d domain hk hd f α tail ih =>
    simp only [numFolds, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hlarge ⊢
    set m : ℝ := (tail.numFolds : ℝ)
    let T := S.image (sqFoldMapGen (i := k))
    have hT : T ⊆ tail.accepting := by
      rintro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp (hS hi)).2.2
    set N : ℝ := 2 ^ (n - k)
    have hn : (2 : ℝ) ^ n = 2 ^ k * N := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    have hkpos : (0 : ℝ) < 2 ^ k := by positivity
    have hNpos : (0 : ℝ) < N := by positivity
    have hc : (S.card : ℝ) ≤ 2 ^ k * (T.card : ℝ) := by
      exact_mod_cast card_le_mul_card_sqFoldMapGen_image domain k S
    have hTlarge : N * (1 - θ) + m * loss * N ≤ T.card := by
      rw [hn] at hlarge
      have : 2 ^ k * (N * (1 - θ) + m * loss * N) ≤ 2 ^ k * T.card := by linarith
      exact le_of_mul_le_mul_left this hkpos
    have hmloss : 0 ≤ loss * N := by positivity
    obtain ⟨⟨u, hu, T₂, hT₂, hT₂card, hagree⟩, hin⟩ :=
      ih hsafe.2 hfinal T hT (by nlinarith)
    have hdens : (S.card : ℝ) / 2 ^ n ≤ T.card / N := by
      rw [hn, div_le_div_iff₀ (by positivity) hNpos]
      nlinarith
    refine ⟨?_, InputsAgree.mono (by nlinarith) tail hin⟩
    have hfold : projectedWord (foldWord domain f k α) T₂ ∈
        projectedCodeSubmod (code (domain.subdomain k) d) T₂ := by
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨u, hu, ?_⟩
      funext x
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hT₂ x.property)
      have hcheck := (Finset.mem_filter.mp (hS hi)).2.1
      exact (hix ▸ hcheck).trans (hagree x x.property).symm
    obtain ⟨T₃, hT₃, hT₃card, v, hv, hvagree⟩ : ∃ T₃ ⊆ T₂,
        (T₃.card : ℝ) ≥ T₂.card - loss * Fintype.card (Fin (2 ^ (n - k))) ∧
        ∃ v ∈ code domain (2 ^ k * d),
          ∀ i x, x ∈ T₃ → domain i ^ (2 ^ k) = domain.subdomain k x → v i = f i := by
      by_contra h
      exact hsafe.1 ⟨T₂, by simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]; linarith,
        hfold, fun T' hT' hc hex ↦ h ⟨T', hT', hc, hex⟩⟩
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hT₃card
    refine ⟨v, hv, S.filter fun i ↦ sqFoldMapGen (i := k) i ∈ T₃, Finset.filter_subset _ _,
      ?_, fun i hi ↦ hvagree i _ (Finset.mem_filter.mp hi).2
        (CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := domain) i).symm⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (fun i ↦ sqFoldMapGen (i := k) i ∈ T₃)
    have hrest : (S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card ≤
        2 ^ k * (T \ T₃).card := by
      refine le_trans (Finset.card_le_card ?_) (card_filter_sqFoldMapGen_mem_le domain k S _)
      intro i hi
      obtain ⟨hiS, hiT⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hiS, Finset.mem_sdiff.mpr
        ⟨Finset.mem_image_of_mem _ hiS, hiT⟩⟩
    have hsdiff : ((T \ T₃).card : ℝ) = T.card - T₃.card := by
      rw [Finset.card_sdiff_of_subset (hT₃.trans hT₂)]
      exact Nat.cast_sub (Finset.card_le_card (hT₃.trans hT₂))
    have hrest' : ((S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card : ℝ) ≤
        2 ^ k * (T.card - T₃.card) := by
      rw [← hsdiff]
      exact_mod_cast hrest
    have hsplit' : (S.card : ℝ) = (S.filter fun i ↦ sqFoldMapGen (i := k) i ∈ T₃).card +
        (S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card := by
      exact_mod_cast hsplit.symm
    rw [hn]
    have : 2 ^ k * ((T.card : ℝ) - T₃.card) ≤ 2 ^ k * ((m + 1) * loss * N) :=
      mul_le_mul_of_nonneg_left (by linarith) hkpos.le
    nlinarith
  | @inject n k d domain hk hd f α g tail ih =>
    simp only [numFolds, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hlarge ⊢
    set m : ℝ := (tail.numFolds : ℝ)
    let T := S.image (sqFoldMapGen (i := k))
    have hT : T ⊆ tail.accepting := by
      rintro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp (hS hi)).2.2
    set N : ℝ := 2 ^ (n - k)
    have hn : (2 : ℝ) ^ n = 2 ^ k * N := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    have hkpos : (0 : ℝ) < 2 ^ k := by positivity
    have hNpos : (0 : ℝ) < N := by positivity
    have hc : (S.card : ℝ) ≤ 2 ^ k * (T.card : ℝ) := by
      exact_mod_cast card_le_mul_card_sqFoldMapGen_image domain k S
    have hTlarge : N * (1 - θ) + m * loss * N ≤ T.card := by
      rw [hn] at hlarge
      have : 2 ^ k * (N * (1 - θ) + m * loss * N) ≤ 2 ^ k * T.card := by linarith
      exact le_of_mul_le_mul_left this hkpos
    have hmloss : 0 ≤ loss * N := by positivity
    obtain ⟨⟨u, hu, T₂, hT₂, hT₂card, hagree⟩, hin⟩ :=
      ih hsafe.2 hfinal T hT (by nlinarith)
    have hdens : (S.card : ℝ) / 2 ^ n ≤ T.card / N := by
      rw [hn, div_le_div_iff₀ (by positivity) hNpos]
      nlinarith
    have hfold : projectedWord (fun x ↦ foldWord domain f k α x + α ^ 2 ^ k * g x) T₂ ∈
        projectedCodeSubmod (code (domain.subdomain k) d) T₂ := by
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨u, hu, ?_⟩
      funext x
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hT₂ x.property)
      have hcheck := (Finset.mem_filter.mp (hS hi)).2.1
      exact (hix ▸ hcheck).trans (hagree x x.property).symm
    obtain ⟨T₃, hT₃, hT₃card, ⟨v, hv, hvagree⟩, hg⟩ : ∃ T₃ ⊆ T₂,
        (T₃.card : ℝ) ≥ T₂.card - loss * Fintype.card (Fin (2 ^ (n - k))) ∧
        (∃ v ∈ code domain (2 ^ k * d),
          ∀ i x, x ∈ T₃ → domain i ^ (2 ^ k) = domain.subdomain k x → v i = f i) ∧
        projectedWord g T₃ ∈ projectedCodeSubmod (code (domain.subdomain k) d) T₃ := by
      by_contra h
      exact hsafe.1 ⟨T₂, by simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]; linarith,
        hfold, fun T' hT' hc hex ↦ h ⟨T', hT', hc, hex⟩⟩
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hT₃card
    refine ⟨?_, ?_, InputsAgree.mono (by nlinarith) tail hin⟩
    · refine ⟨v, hv, S.filter fun i ↦ sqFoldMapGen (i := k) i ∈ T₃, Finset.filter_subset _ _,
        ?_, fun i hi ↦ hvagree i _ (Finset.mem_filter.mp hi).2
          (CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := domain) i).symm⟩
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := S) (fun i ↦ sqFoldMapGen (i := k) i ∈ T₃)
      have hrest : (S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card ≤
          2 ^ k * (T \ T₃).card := by
        refine le_trans (Finset.card_le_card ?_) (card_filter_sqFoldMapGen_mem_le domain k S _)
        intro i hi
        obtain ⟨hiS, hiT⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hiS, Finset.mem_sdiff.mpr
          ⟨Finset.mem_image_of_mem _ hiS, hiT⟩⟩
      have hsdiff : ((T \ T₃).card : ℝ) = T.card - T₃.card := by
        rw [Finset.card_sdiff_of_subset (hT₃.trans hT₂)]
        exact Nat.cast_sub (Finset.card_le_card (hT₃.trans hT₂))
      have hrest' : ((S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card : ℝ) ≤
          2 ^ k * (T.card - T₃.card) := by
        rw [← hsdiff]
        exact_mod_cast hrest
      have hsplit' : (S.card : ℝ) = (S.filter fun i ↦ sqFoldMapGen (i := k) i ∈ T₃).card +
          (S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card := by
        exact_mod_cast hsplit.symm
      rw [hn]
      have : 2 ^ k * ((T.card : ℝ) - T₃.card) ≤ 2 ^ k * ((m + 1) * loss * N) :=
        mul_le_mul_of_nonneg_left (by linarith) hkpos.le
      nlinarith
    · obtain ⟨w, hw, hwg⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp hg
      refine ⟨T₃, ?_, w, hw, fun x hx ↦ (congrFun hwg ⟨x, hx⟩).symm⟩
      have h1 : (S.card : ℝ) / 2 ^ n * N ≤ T.card := by
        have := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n) hNpos).mp hdens
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
        nlinarith
      nlinarith

/-- If the initial word `word` (which the trace's first word must agree with at every query) or an
injected word is `δ`-far from its code, the density of the accepting positions where the first
word agrees with `word` is at most `1 - min (θ - (m - 1) · loss) (δ - m · loss)` for `m` folds. -/
theorem consistent_density_le (tr : InjectTrace domain d) (word : Fin (2 ^ n) → F)
    (θ δ loss : ℝ) (hloss : 0 ≤ loss) (hsafe : tr.SafeLossy θ loss) (hfinal : tr.FinalInCode)
    (hfar : ¬ (Agrees domain d (1 - δ) word ∧ tr.InputsAgree (1 - δ))) :
    ((tr.accepting.filter fun i ↦ tr.initial i = word i).card : ℝ) / 2 ^ n ≤
      1 - min (θ - ((tr.numFolds : ℝ) - 1) * loss) (δ - tr.numFolds * loss) := by
  classical
  set S := tr.accepting.filter fun i ↦ tr.initial i = word i
  set m : ℝ := (tr.numFolds : ℝ)
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ hn]
  by_cases hlarge : (2 ^ n : ℝ) * (1 - θ) + (m - 1) * loss * 2 ^ n ≤ S.card
  · obtain ⟨⟨u, hu, S', hS', hcard, hagree⟩, hin⟩ := tr.exists_codeword_agree_on_lossy θ loss
      hloss hsafe hfinal S (Finset.filter_subset _ _) hlarge
    by_contra hlt
    have hδ : (1 - δ + m * loss) * 2 ^ n < S.card := by
      have := min_le_right (θ - (m - 1) * loss) (δ - m * loss)
      nlinarith
    refine hfar ⟨⟨S', ?_, u, hu, fun x hx ↦ ?_⟩, InputsAgree.mono ?_ tr hin⟩
    · nlinarith
    · rw [hagree x hx]
      exact (Finset.mem_filter.mp (hS' hx)).2
    · rw [le_sub_iff_add_le, le_div_iff₀ hn]
      nlinarith
  · have := min_le_left (θ - (m - 1) * loss) (δ - m * loss)
    push Not at hlarge
    nlinarith

end InjectTrace

end CompStark.Sound.FriInject
