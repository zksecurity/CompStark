/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.PowersMca
public import CompStark.Sound.Johnson
public import CompStark.Sound.Fri
public import CompStark.Sound.Batching

/-! # Bounds on the knowledge error's terms below the unique-decoding radius

At FRI arity `2`, with the extractor's radius below the unique-decoding radius `(1 - rate) / 2`,
each term of the knowledge error is an integer over `|𝕂|`, except FRI's queries and the curve
bound on batching:

* the candidate lists have at most one element (`listSize_le_one`), so the constraint-folding and
  out-of-domain terms are at most `#constraints - 1` and `identityDegree + n`;
* every code involved, the trace's and each folded FRI code, has the rate `1 / 2 ^ logBlowup`, so
  a radius below `(1 - rate) / 2` is within its relative unique-decoding radius (`le_relUDR`), and
  the powers MCA bound `mcaError_powers_le` gives `(numOpened - 1) N` for batching at a single
  radius (`batchingError_le_mcaError`, and so at every larger one, `batchingError_anti`) and `|L'|`
  for a fold onto the domain `L'`; the halving
  domains of FRI's folds sum to at most `N` (`friError_le_of_le`);
* batching at `δ < δ'' = δ' - 2/N` is at most `(numOpened - 1) max(T₁, T₂)`
  (`batchingError_le_curve`);
* the queries contribute `(1 - δ) ^ numQueries`.

`knowledgeError_le_of_le` (the MCA bound) and `knowledgeError_le_curve` (the curve bound) collect
the terms;
`numbers_le` and `numbers_wide_le` close the arithmetic for `CompStark/Security.lean`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal ProximityGap CoreDefinitions Code

local notation "𝕂" => KoalaBear.Ext4

/-- At rate at most `1/c`, a radius `θ ≤ (1 - 1/c) / 2` is within the relative unique-decoding
radius of a Reed–Solomon code. -/
theorem le_relUDR {ι : Type} [Fintype ι] {F : Type} [Field F] [DecidableEq F]
    {domain : ι ↪ F} {deg : ℕ} [NeZero deg] (c : ℕ) (h : c * deg ≤ Fintype.card ι) (θ : ℝ≥0)
    (hθ : (θ : ℝ) * (2 * c) ≤ c - 1) :
    θ ≤ relativeUniqueDecodingRadius (ReedSolomon.code domain deg : Set (ι → F)) := by
  have hdeg := NeZero.pos deg
  have hc : 1 ≤ c := by
    by_contra hc0
    have : c = 0 := by omega
    subst this
    have := θ.coe_nonneg
    norm_num at hθ
  have hcard : (0 : ℝ≥0) < Fintype.card ι := by
    exact_mod_cast (show 0 < Fintype.card ι from lt_of_lt_of_le (by positivity) h)
  have hle : deg ≤ Fintype.card ι := le_trans (Nat.le_mul_of_pos_left _ hc) h
  rw [relativeUniqueDecodingRadius, dist_eq_minDist, ReedSolomon.minDist_of_le hle,
    Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, div_div, le_div_iff₀ (by positivity),
    ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_sub hle]
  push_cast
  have h' : (c * deg : ℝ) ≤ Fintype.card ι := by exact_mod_cast h
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hθ hk
  nlinarith

/-- The degree of FRI's code after fold `i` is at most a `c`-th of its domain when the initial
code's is. -/
theorem mul_foldingDegree_le {N k : ℕ} (c : ℕ) (hc : 0 < c) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
    (i : Fin (k + 1)) (h : c * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ N) :
    c * Fri.Spec.foldingDegree s d i.succ ≤
      2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) := by
  have hq := Fri.Spec.foldingPrefix_le s i.succ
  rw [Fri.Spec.foldingPrefix_succ] at hq
  have hsN : ∑ j, (s j).val ≤ N := by
    by_contra hlt
    have : 2 ^ N < 2 ^ (∑ j, (s j).val) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ (∑ j, (s j).val) ≤ c * (2 ^ (∑ j, (s j).val) * d.val) :=
      (Nat.le_mul_of_pos_right _ d.pos).trans (Nat.le_mul_of_pos_left _ hc)
    omega
  set q := Fri.Spec.foldingPrefix s i.castSucc + (s i).val
  have hpq : N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val = N - q := by omega
  rw [hpq, Fri.Spec.foldingDegree, Fri.Spec.foldingPrefix_succ]
  refine Nat.le_of_mul_le_mul_right (c := 2 ^ q) ?_ (Nat.two_pow_pos q)
  rw [← pow_add, Nat.sub_add_cancel (by omega)]
  calc c * (2 ^ (∑ j, (s j).val - q) * d.val) * 2 ^ q
      = c * (2 ^ (∑ j, (s j).val - q + q) * d.val) := by rw [pow_add]; ring
    _ = c * (2 ^ (∑ j, (s j).val) * d.val) := by rw [Nat.sub_add_cancel hq]
    _ ≤ 2 ^ N := h

/-- One FRI fold's error at rate at most `1/c` and a radius `θ ≤ (1 - 1/c) / 2`: the powers MCA
bound `(2 ^ s - 1) |L'| / |𝕂|` on the folded domain `L'`. -/
theorem foldingError_le {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂} (c : ℕ) (hc : 0 < c)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1))
    (h : c * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ N) (θ : ℝ≥0) (hθ : (θ : ℝ) * (2 * c) ≤ c - 1) :
    (Fri.Spec.foldingError (ω := ω) s d (θ : ℝ) i : ENNReal) ≤
      ((2 ^ (s i).val - 1) * 2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) : ℕ) /
        (Fintype.card 𝕂 : ENNReal) := by
  have hc' := mul_foldingDegree_le c hc s d i h
  have : NeZero (Fri.Spec.foldingDegree s d i.succ) := ⟨(Fri.Spec.foldingDegree_pos s d _).ne'⟩
  have hle : Fri.Spec.foldingDegree s d i.succ ≤
      2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) :=
    (Nat.le_mul_of_pos_left _ hc).trans hc'
  unfold Fri.Spec.foldingError
  rw [ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact mcaError_powers_le (Fri.Spec.foldingDegree_pos s d _) hle _
    (le_relUDR c (by rw [Fintype.card_fin]; exact hc') θ hθ)

/-- Folding by arity `2` halves `r` times. -/
theorem folds_one : ∀ r, folds 1 r = List.replicate r 1
  | 0 => by rw [folds]; rfl
  | r + 1 => by
    rw [folds, List.replicate_succ]
    congr 1
    rw [show r + 1 - max 1 (min 1 (r + 1)) = r by omega]
    exact folds_one r

theorem foldsAt_replicate (m : ℕ) (j : Fin ((List.replicate m (1 : ℕ+)).length + 1)) :
    foldsAt 1 (List.replicate m 1) j = 1 := by
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    simp only [foldsAt, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
      List.getElem_replicate]

/-- At arity `2`, `i` folds precede fold `i`. -/
theorem foldingPrefix_replicate (m : ℕ) (i : Fin ((List.replicate m (1 : ℕ+)).length + 2)) :
    Fri.Spec.foldingPrefix (foldsAt 1 (List.replicate m 1)) i = i := by
  induction i using Fin.induction with
  | zero => rw [Fri.Spec.foldingPrefix_zero, Fin.val_zero]
  | succ i ih =>
    rw [Fri.Spec.foldingPrefix_succ, ih, foldsAt_replicate, PNat.one_coe, Fin.val_succ,
      Fin.val_castSucc]

/-- The halving domains of `r ≤ N` folds: `2 ^ (N - 1) + ⋯ + 2 ^ (N - r) = 2 ^ N - 2 ^ (N - r)`. -/
theorem sum_two_pow_add (N : ℕ) : ∀ r, r ≤ N →
    ∑ j ∈ Finset.range r, 2 ^ (N - j - 1) + 2 ^ (N - r) = 2 ^ N
  | 0, _ => by rw [Finset.sum_range_zero, zero_add, Nat.sub_zero]
  | r + 1, h => by
    rw [Finset.sum_range_succ, ← sum_two_pow_add N r (by omega), add_assoc]
    obtain ⟨t, ht⟩ : ∃ t, N - r = t + 1 := ⟨N - r - 1, by omega⟩
    rw [show N - r - 1 = t by omega, show N - (r + 1) = t by omega, ht, pow_succ]
    ring

/-- FRI's error with arity `2` and `m + 1` folds, at rate at most `1/c` and a radius
`δ ≤ (1 - 1/c) / 2`: the folds on the halving domains sum to at most `|L| / |𝕂|`. -/
theorem friErrorOf_replicate_le {N : ℕ} (ω : Domain.SmoothCosetFftDomain N 𝕂) (m : ℕ)
    (logFinal l : ℕ) (c : ℕ) (hc : 0 < c) (δ : ℝ≥0) (hδ : (δ : ℝ) * (2 * c) ≤ c - 1)
    (h : c * 2 ^ (m + 1 + logFinal) ≤ 2 ^ N) :
    friErrorOf ω (List.replicate (m + 1) 1) logFinal l δ ≤
      (2 ^ N : ℕ) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ) ^ l : ℝ≥0) : ENNReal) := by
  have hsum : ∑ j, (foldsAt 1 (List.replicate m 1) j).val = m + 1 := by
    simp only [foldsAt_replicate, PNat.one_coe, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, List.length_replicate, smul_eq_mul, mul_one]
  have hh : c * (2 ^ (∑ j, (foldsAt 1 (List.replicate m 1) j).val) *
      (finalDegree logFinal).val) ≤ 2 ^ N := by
    change c * (2 ^ _ * 2 ^ logFinal) ≤ 2 ^ N
    rw [hsum, ← pow_add]
    exact h
  have hdom : 2 ^ (∑ j, (foldsAt 1 (List.replicate m 1) j).val) * (finalDegree logFinal).val ≤
      2 ^ N := (Nat.le_mul_of_pos_left _ hc).trans hh
  have hmN : m + 1 ≤ N := by
    by_contra hlt
    have : 2 ^ N < 2 ^ (m + 1 + logFinal) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := Nat.le_mul_of_pos_left (2 ^ (m + 1 + logFinal)) hc
    omega
  rw [List.replicate_succ]
  simp only [friErrorOf, hdom, ↓reduceIte, Fri.Spec.soundnessError, min_self, ENNReal.coe_add,
    ENNReal.ofNNReal_finsetSum]
  refine add_le_add ((Finset.sum_le_sum fun j _ ↦ foldingError_le c hc _ _ j hh δ hδ).trans ?_)
    le_rfl
  rw [← ENNReal.sum_div, ← Nat.cast_sum]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  simp only [foldsAt_replicate, foldingPrefix_replicate, PNat.one_coe, pow_one,
    Nat.add_one_sub_one, one_mul, Fin.val_castSucc]
  have := sum_two_pow_add N (m + 1) hmN
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ 2 ^ (N - i - 1)), List.length_replicate]
  exact this ▸ Nat.le_add_right _ _

/-! ### The terms of a setup -/

/-- The rate is `1 / 2 ^ logBlowup`. -/
theorem rate_eq (S : Setup) : S.rate = 1 / 2 ^ S.params.logBlowup := by
  rw [Setup.rate, Setup.n, Setup.size, pow_add]
  push_cast
  field_simp

/-- Below the unique-decoding radius `(1 - rate) / 2`, with `c = 2 ^ logBlowup`. -/
theorem mul_le_of_le_udr (S : Setup) (δ : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) :
    (δ : ℝ) * (2 * (2 ^ S.params.logBlowup : ℕ)) ≤ (2 ^ S.params.logBlowup : ℕ) - 1 := by
  rw [rate_eq, le_div_iff₀ two_pos] at hδ
  have hc : (0 : ℝ) < 2 ^ S.params.logBlowup := by positivity
  have h1 := mul_le_mul_of_nonneg_right hδ hc.le
  have h2 : (1 - 1 / (2 : ℝ) ^ S.params.logBlowup) * 2 ^ S.params.logBlowup =
      2 ^ S.params.logBlowup - 1 := by field_simp
  push_cast
  nlinarith

/-- Below the unique-decoding radius, the lists have at most one element. -/
theorem foldingError_le_of_le (S : Setup) (δ : ℝ≥0) (hδ : (δ : ℝ) < (1 - S.rate) / 2) :
    foldingError S δ ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  calc S.listSize (Fin S.air.width) δ * (S.air.constraints.length - 1)
      ≤ 1 * (S.air.constraints.length - 1) :=
        Nat.mul_le_mul_right _ (listSize_le_one S _ δ hδ)
    _ = _ := one_mul _

/-- The out-of-domain term below the unique-decoding radius. -/
theorem outOfDomainError_le_of_le (S : Setup) (δ : ℝ≥0) (hδ : (δ : ℝ) < (1 - S.rate) / 2) :
    outOfDomainError S δ ≤
      (S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  have h := Nat.mul_le_mul_right S.identityDegree (Nat.mul_le_mul
    (listSize_le_one S (Fin S.air.width) δ hδ) (listSize_le_one S (Fin S.chunks × Fin 4) δ hδ))
  omega

/-- The batching term at a single radius below the unique-decoding radius: the powers MCA bound
`(numOpened - 1) N / |𝕂|`. -/
theorem batchingError_le_of_le (S : Setup) (δ : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) :
    batchingError S δ δ ≤ ((S.numOpened - 1) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  have hN : 2 ^ S.params.logBlowup * S.n ≤ S.size := by
    rw [Setup.n, Setup.size, pow_add, mul_comm]
  have hb := S.blowup
  have : NeZero S.n := ⟨(Nat.two_pow_pos _).ne'⟩
  refine (batchingError_le_mcaError S δ).trans ?_
  exact mcaError_powers_le (Nat.two_pow_pos _)
    ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans hN) _
    (le_relUDR _ (by rw [Fintype.card_fin]; exact hN) δ (mul_le_of_le_udr S δ hδ))

/-- FRI's term at arity `2` below the unique-decoding radius: the folds on the halving domains,
at most `N / |𝕂|` together, and the queries. -/
theorem friError_le_of_le (S : Setup) (harity : S.params.maxLogArity = 1) (δ : ℝ≥0)
    (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) :
    friError S δ ≤ (S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) +
      ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hlt := S.folds
  obtain ⟨m, hm⟩ : ∃ m, S.logN - S.params.logFinalPolyLen = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  rw [friError, harity, hm, folds_one]
  apply friErrorOf_replicate_le _ _ _ _ _ (Nat.two_pow_pos _) _ (mul_le_of_le_udr S δ hδ)
  rw [show m + 1 + S.params.logFinalPolyLen = S.logN by omega, pow_add, mul_comm]

/-- The knowledge error at arity `2` with FRI at `δ` and the extractor at `δ' ≥ δ + 2/N` below
the unique-decoding radius, with the MCA bound for batching: one integer over `|𝕂|`, and
`(1 - δ) ^ numQueries`. -/
theorem knowledgeError_le_of_le (S : Setup) (harity : S.params.maxLogArity = 1) (δ δ' : ℝ≥0)
    (hδ : (δ : ℝ) ≤ δ' - 2 / S.size) (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) :
    knowledgeError S δ δ' ≤
      ((S.air.constraints.length - 1) + (S.identityDegree + S.n) +
        (S.numOpened - 1) * S.size + S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hδu : (δ : ℝ) ≤ (1 - S.rate) / 2 :=
    hδ.trans ((sub_le_self _ (by positivity)).trans hδ'.le)
  calc knowledgeError S δ δ'
      ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          (S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          ((S.numOpened - 1) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          ((S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) +
            ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal)) :=
        add_le_add (add_le_add (add_le_add (foldingError_le_of_le S δ' hδ')
          (outOfDomainError_le_of_le S δ' hδ')) ((batchingError_anti S δ hδ).trans
            (batchingError_le_of_le S δ hδu))) (friError_le_of_le S harity δ hδu)
    _ = _ := by
        simp only [← add_assoc, ENNReal.div_add_div_same, Nat.cast_add]

/-- The knowledge error at arity `2` with FRI at `δ` and the extractor at `δ'` below the
unique-decoding radius, `δ < δ' - 2/N`, with the curve bound for batching at `δ' - 2/N`
(`batchingError_le_curve`). -/
theorem knowledgeError_le_curve (S : Setup) (harity : S.params.maxLogArity = 1) (δ δ' : ℝ≥0)
    (h_ud : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / S.size) (h_pos : 0 < δ)
    (h_lt : (δ : ℝ) < δ' - 2 / S.size) (hδ' : (δ' : ℝ) < (1 - S.rate) / 2) :
    knowledgeError S δ δ' ≤
      ((S.air.constraints.length - 1) + (S.identityDegree + S.n) + S.size : ℕ) /
          (Fintype.card 𝕂 : ENNReal) +
        ENNReal.ofReal ((S.numOpened - 1 : ℕ) *
          max ((1 - S.rate - δ) / (δ * (1 - S.rate - 2 * δ)))
            ((δ' - 2 / S.size) / (δ' - 2 / S.size - δ))) /
          Fintype.card 𝕂 +
        ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hδ : (δ : ℝ) ≤ (1 - S.rate) / 2 := h_ud.trans (sub_le_self _ (by positivity))
  calc knowledgeError S δ δ'
      ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          (S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          ENNReal.ofReal ((S.numOpened - 1 : ℕ) *
            max ((1 - S.rate - δ) / (δ * (1 - S.rate - 2 * δ)))
              ((δ' - 2 / S.size) / (δ' - 2 / S.size - δ))) /
            Fintype.card 𝕂 +
          ((S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) +
            ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal)) :=
        add_le_add (add_le_add (add_le_add (foldingError_le_of_le S δ' hδ')
          (outOfDomainError_le_of_le S δ' hδ'))
            (batchingError_le_curve S δ _ h_ud h_pos h_lt))
          (friError_le_of_le S harity δ hδ)
    _ = _ := by
        simp only [Nat.cast_add, ← ENNReal.div_add_div_same]
        ring

/-! ### The numbers -/

/-- `|𝕂| = p ^ 4 ≥ 2 ^ 123`. -/
theorem two_pow_le_card : (2 ^ 123 : ℝ) ≤ Fintype.card 𝕂 := by
  rw [KoalaBear.card_ext4, KoalaBear.fieldSize]
  norm_num

/-- At most `2 ^ 19` over `|𝕂|`, plus `(563/1000) ^ 123`, is at most `2 ^ (-100)`. -/
theorem numbers_le (A : ℕ) (hA : A ≤ 2 ^ 19) :
    (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - ((437 / 1000 : ℝ≥0) : ℝ)) ^ 123 : ℝ≥0) : ENNReal) ≤
      (2 ^ 100 : ENNReal)⁻¹ := by
  have hK := two_pow_le_card
  have hKpos : (0 : ℝ) < Fintype.card 𝕂 := lt_of_lt_of_le (by positivity) hK
  have hq : Real.toNNReal (1 - ((437 / 1000 : ℝ≥0) : ℝ)) = 563 / 1000 := by
    rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have hAK : (A : ℝ) / Fintype.card 𝕂 ≤ 2 ^ 19 / 2 ^ 123 := by
    rw [div_le_div_iff₀ hKpos (by positivity)]
    have hA' : (A : ℝ) ≤ 2 ^ 19 := by exact_mod_cast hA
    nlinarith
  rw [hq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (Fintype.card 𝕂),
    ← ENNReal.ofReal_div_of_pos hKpos, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_inv_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  calc (A : ℝ) / Fintype.card 𝕂 + (563 / 1000) ^ 123 ≤ 2 ^ 19 / 2 ^ 123 + (563 / 1000) ^ 123 := by
        linarith
    _ ≤ (2 ^ 100)⁻¹ := by norm_num

/-- At most `2 · 2 ^ 22 + 64` and `4996` over `|𝕂| = p ^ 4`, plus `(16/25) ^ 159`, is at most
`2 ^ (-100)`. -/
theorem numbers_wide_le (A : ℕ) (hA : A ≤ 2 * 2 ^ 22 + 64) (B : ℝ) (hB : B ≤ 4996) :
    (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) + ENNReal.ofReal B / Fintype.card 𝕂 +
        ((Real.toNNReal (1 - ((9 / 25 : ℝ≥0) : ℝ)) ^ 159 : ℝ≥0) : ENNReal) ≤
      (2 ^ 100 : ENNReal)⁻¹ := by
  have hK : (Fintype.card 𝕂 : ℝ) = 2130706433 ^ 4 := by
    rw [KoalaBear.card_ext4, KoalaBear.fieldSize]
    norm_num
  have hKpos : (0 : ℝ) < Fintype.card 𝕂 := by rw [hK]; positivity
  have hq : Real.toNNReal (1 - ((9 / 25 : ℝ≥0) : ℝ)) = 16 / 25 := by
    rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by norm_num)]
    norm_num
  calc (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) + ENNReal.ofReal B / Fintype.card 𝕂 +
        ((Real.toNNReal (1 - ((9 / 25 : ℝ≥0) : ℝ)) ^ 159 : ℝ≥0) : ENNReal)
      ≤ ((2 * 2 ^ 22 + 64 : ℕ) : ENNReal) / Fintype.card 𝕂 + ENNReal.ofReal 4996 / Fintype.card 𝕂 +
          (((16 / 25 : ℝ≥0) ^ 159 : ℝ≥0) : ENNReal) := by
        rw [hq]
        gcongr
    _ = ENNReal.ofReal ((2 * 2 ^ 22 + 64 + 4996) / Fintype.card 𝕂 + (16 / 25) ^ 159) := by
        rw [ENNReal.div_add_div_same, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num),
          ← ENNReal.ofReal_natCast (Fintype.card 𝕂), ← ENNReal.ofReal_div_of_pos hKpos,
          ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
    _ ≤ (2 ^ 100 : ENNReal)⁻¹ := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_inv_of_pos (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hK]
        norm_num

end CompStark.Sound
