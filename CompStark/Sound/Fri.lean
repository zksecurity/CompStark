/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Steps

/-! # FRI rejects far words

`friStep`: FRI accepts a word that is not `δ`-near the code with probability at most
`friError S δ`. This is ArkLib's `Fri.Spec.soundness_proximity_lossy`, which bounds every
prover's acceptance by `soundnessErrorLossy` at every proximity loss, for inputs outside
`proximityLanguage s d δ`, the words at relative distance below `δ` from the Reed–Solomon code of
degree `2 ^ (∑ s) * d` on the domain.

For the STARK, Plonky3's arities `folds maxLogArity (logN - logFinalPolyLen)` sum to
`logN - logFinalPolyLen` (`sum_folds`), so ArkLib's code has degree `2 ^ logN = S.n` and is
`S.code`. A word at relative distance below `δ` from a codeword agrees with it on more than
`(1 - δ) N` points, so it is `δ`-near (`near_of_relHammingDist_lt`).

`friAtMostOne`: acceptance is a supremum of probabilities.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial Domain OracleSpec OracleComp ProtocolSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF


/-- Plonky3's arities sum to the number of halvings they fold away. -/
theorem sum_folds (m : Nat) : ∀ r, ((folds m r).map (fun x : ℕ+ ↦ x.val)).sum = r
  | 0 => by rw [folds]; rfl
  | r + 1 => by
    have h := sum_folds m (r + 1 - max 1 (min m (r + 1)))
    rw [folds]
    change max 1 (min m (r + 1)) +
      ((folds m (r + 1 - max 1 (min m (r + 1)))).map (fun x : ℕ+ ↦ x.val)).sum = r + 1
    rw [h]
    omega

theorem sum_foldsAt (f : ℕ+) (fs : List ℕ+) :
    ∑ j, (foldsAt f fs j).val = ((f :: fs).map (fun x : ℕ+ ↦ x.val)).sum :=
  Fin.sum_univ_fun_getElem (f :: fs) PNat.val

/-- The initial oracle of `friInput` is the word. -/
theorem initialOracle_friInput {n k : Nat} (ω : SmoothCosetFftDomain n 𝕂) (s : Fin (k + 1) → ℕ+)
    (word : Fin (2 ^ n) → 𝕂) (z : Fin (2 ^ n)) :
    Fri.Spec.initialOracle s (friInput ω s word) (Fri.Spec.initialQuery z) = word z := by
  have he : (ω.subdomain 0).equivToFinset z = Fri.Spec.initialQuery z := by
    apply Subtype.ext
    simp only [Nat.sub_zero, CosetFftDomain.equivToFinset_apply,
      CosetFftDomain.subdomain_zero_eq_self, Fri.Spec.initialQuery]
  simp only [Fri.Spec.initialOracle, friInput, cast_cast, cast_eq, ← he, Equiv.symm_apply_apply]

/-- FRI's acceptance of a word outside the proximity language is at most its error. -/
theorem friAcceptanceOf_le {n : Nat} (ω : SmoothCosetFftDomain n 𝕂) (f : ℕ+) (fs : List ℕ+)
    (logFinal l : Nat) (word : Fin (2 ^ n) → 𝕂) (δ : NNReal)
    (hdom : 2 ^ (∑ j, (foldsAt f fs j).val) * (finalDegree logFinal).val ≤ 2 ^ n)
    (hfar : Fri.Spec.initialOracle (foldsAt f fs) (friInput ω (foldsAt f fs) word) ∉
      Fri.Spec.proximityLanguage (foldsAt f fs) (finalDegree logFinal) δ) :
    friAcceptanceOf ω (f :: fs) logFinal l word ≤ friErrorOf ω (f :: fs) logFinal l δ := by
  simp only [friAcceptanceOf, friErrorOf, hdom, ↓reduceDIte, ↓reduceIte]
  refine le_iInf fun loss ↦ iSup_le fun WitIn ↦ iSup_le fun WitOut ↦ iSup_le fun witIn ↦
    iSup_le fun prover ↦ ?_
  exact Fri.Spec.soundness_proximity_lossy (foldsAt f fs) (finalDegree logFinal) l hdom δ δ loss
    loss.coe_nonneg (pure ()) emptyImpl WitIn WitOut witIn prover _ hfar

/-- A word at relative distance below `δ` from a codeword is `δ`-near the code. -/
theorem near_of_relHammingDist_lt (S : Setup EF) (δ : ℝ) (w u : S.Point → 𝕂) (hu : u ∈ S.code)
    (h : (Code.relHammingDist w u : ℝ) < δ) : Near S δ w := by
  classical
  refine ⟨Finset.univ.filter fun i ↦ w i = u i, ?_, u, hu, fun i hi ↦ (Finset.mem_filter.mp hi).2⟩
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : S.Point ↦ w i = u i)
  have hd : hammingDist w u = (Finset.univ.filter fun i ↦ ¬ w i = u i).card := rfl
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hpos : (0 : ℝ) < S.size := by exact_mod_cast Nat.two_pow_pos _
  simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast, Fintype.card_fin] at h
  rw [← hd] at hcard
  have hpos' : (0 : ℝ) < (2 ^ (S.logN + S.params.logBlowup) : Nat) := hpos
  rw [div_lt_iff₀ hpos'] at h
  have hcard' : (({i | w i = u i} : Finset S.Point).card : ℝ) + (hammingDist w u : ℝ) =
      (2 ^ (S.logN + S.params.logBlowup) : Nat) := by exact_mod_cast hcard
  change _ ≥ ((2 ^ (S.logN + S.params.logBlowup) : Nat) : ℝ) * (1 - δ)
  linarith

/-- Plonky3's arities for a positive number of halvings are nonempty. -/
theorem folds_cons (m r : Nat) (hr : r ≠ 0) : ∃ f fs, folds m r = f :: fs := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [folds]
  exact ⟨_, _, rfl⟩

/-- FRI accepts a word that is not `δ`-near the code with probability at most `friError`. -/
theorem friStep (S : Setup EF) : FriStep S := by
  intro δ w hw
  have hlt := S.folds
  obtain ⟨f, fs, hL⟩ := folds_cons S.params.maxLogArity (S.logN - S.params.logFinalPolyLen)
    (by omega)
  have hsum : ∑ j, (foldsAt f fs j).val = S.logN - S.params.logFinalPolyLen := by
    rw [sum_foldsAt, ← hL, sum_folds]
  have hdeg : 2 ^ (∑ j, (foldsAt f fs j).val) * (finalDegree S.params.logFinalPolyLen).val =
      S.n := by
    rw [hsum, finalDegree, PNat.mk_coe, ← pow_add, Nat.sub_add_cancel hlt.le]
  have hdom : 2 ^ (∑ j, (foldsAt f fs j).val) * (finalDegree S.params.logFinalPolyLen).val ≤
      2 ^ (S.logN + S.params.logBlowup) := by
    rw [hdeg]
    exact Nat.pow_le_pow_right two_pos (Nat.le_add_right _ _)
  rw [friAcceptance, friError, hL]
  apply friAcceptanceOf_le _ _ _ _ _ _ _ hdom
  rintro ⟨u, hu, hd⟩
  have hw' : (fun z ↦ Fri.Spec.initialOracle (foldsAt f fs) (friInput S.domain (foldsAt f fs) w)
      (Fri.Spec.initialQuery z)) = w := funext (initialOracle_friInput _ _ _)
  rw [hw'] at hd
  rw [hdeg] at hu
  exact hw (near_of_relHammingDist_lt S δ w u hu hd)

/-- FRI's acceptance is at most `1`. -/
theorem friAcceptanceOf_le_one {n : Nat} (ω : SmoothCosetFftDomain n 𝕂) (folds : List ℕ+)
    (logFinal l : Nat) (word : Fin (2 ^ n) → 𝕂) : friAcceptanceOf ω folds logFinal l word ≤ 1 := by
  match folds with
  | [] => exact le_rfl
  | f :: fs =>
    simp only [friAcceptanceOf]
    split
    · exact iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦
      OptionT.prEvent_le_one _ _
    · exact le_rfl

/-- FRI accepts with probability at most `1`. -/
theorem friAtMostOne (S : Setup EF) : FriAtMostOne S := fun w ↦ friAcceptanceOf_le_one _ _ _ _ w

end CompStark.Sound
