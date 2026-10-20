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

At FRI arity `2`, a blowup of at least `16` and a proximity `δ ≤ 7/16` for both FRI and the
extractor, each term of `knowledgeError S δ δ` is an integer over `|𝕂|`, except FRI's queries
(`knowledgeError_le_of_le`):

* `δ` is below the unique-decoding radius `(1 - rate) / 2 ≥ 15/32`, so the candidate lists have
  at most one element (`listSize_le_one`), and the constraint-folding and out-of-domain terms are
  at most `#constraints - 1` and `identityDegree + N + n`;
* every code involved, the trace's and each folded FRI code, has rate at most `1/8`, so `7/16` is
  within its relative unique-decoding radius (`seven_sixteenths_le_relUDR`), and the powers MCA
  bound `mcaError_powers_le` gives, through `batchingError_le_mcaError`, `(numOpened - 1) N` for
  batching and at most `N` for each of
  FRI's `logN - logFinalPolyLen` folds (`friError_le_of_le`);
* the queries contribute `(1 - δ) ^ numQueries`.

`numbers_le` closes the arithmetic for `CompStark/Security.lean`: at most `2 ^ 19` over
`|𝕂| ≥ 2 ^ 123`, plus `(9/16) ^ 123`, is at most `2 ^ (-100)`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal ProximityGap CoreDefinitions Code

local notation "𝕂" => KoalaBear.Ext4

/-- At rate at most `1/8`, `7/16` is within the relative unique-decoding radius of a
Reed–Solomon code. -/
theorem seven_sixteenths_le_relUDR {ι : Type} [Fintype ι] {F : Type} [Field F] [DecidableEq F]
    {domain : ι ↪ F} {deg : ℕ} [NeZero deg] (h : 8 * deg ≤ Fintype.card ι) :
    (7 / 16 : ℝ≥0) ≤
      relativeUniqueDecodingRadius (ReedSolomon.code domain deg : Set (ι → F)) := by
  have hdeg := NeZero.pos deg
  have hcard : (0 : ℝ≥0) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  rw [relativeUniqueDecodingRadius, dist_eq_minDist, ReedSolomon.minDist_of_le (by omega),
    Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, div_div, le_div_iff₀ (by positivity),
    ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_sub (show deg ≤ Fintype.card ι by omega)]
  push_cast
  have h' : (8 * deg : ℝ) ≤ Fintype.card ι := by exact_mod_cast h
  linarith

/-- The degree of FRI's code after fold `i` is at most an eighth of its domain when the initial
code's is. -/
theorem eight_mul_foldingDegree_le {N k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1))
    (h : 8 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ N) :
    8 * Fri.Spec.foldingDegree s d i.succ ≤
      2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) := by
  have hq := Fri.Spec.foldingPrefix_le s i.succ
  rw [Fri.Spec.foldingPrefix_succ] at hq
  have hsN : ∑ j, (s j).val ≤ N := by
    by_contra hlt
    have : 2 ^ N < 2 ^ (∑ j, (s j).val) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ (∑ j, (s j).val) ≤ 8 * (2 ^ (∑ j, (s j).val) * d.val) :=
      (Nat.le_mul_of_pos_right _ d.pos).trans (Nat.le_mul_of_pos_left _ (by norm_num))
    omega
  set q := Fri.Spec.foldingPrefix s i.castSucc + (s i).val
  have hpq : N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val = N - q := by omega
  rw [hpq, Fri.Spec.foldingDegree, Fri.Spec.foldingPrefix_succ]
  refine Nat.le_of_mul_le_mul_right (c := 2 ^ q) ?_ (Nat.two_pow_pos q)
  rw [← pow_add, Nat.sub_add_cancel (by omega)]
  calc 8 * (2 ^ (∑ j, (s j).val - q) * d.val) * 2 ^ q
      = 8 * (2 ^ (∑ j, (s j).val - q + q) * d.val) := by rw [pow_add]; ring
    _ = 8 * (2 ^ (∑ j, (s j).val) * d.val) := by rw [Nat.sub_add_cancel hq]
    _ ≤ 2 ^ N := h

/-- One FRI fold's error at a radius at most `7/16`, at rate at most `1/8`: the powers MCA bound
`(2 ^ s - 1) |L'| / |𝕂|`, with `|L'| ≤ 2 ^ N`. -/
theorem foldingError_le {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂} (s : Fin (k + 1) → ℕ+)
    (d : ℕ+) (i : Fin (k + 1)) (h : 8 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ N)
    (θ : ℝ≥0) (hθ : θ ≤ 7 / 16) :
    (Fri.Spec.foldingError (ω := ω) s d (θ : ℝ) i : ENNReal) ≤
      ((2 ^ (s i).val - 1) * 2 ^ N : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  have h8 := eight_mul_foldingDegree_le s d i h
  have : NeZero (Fri.Spec.foldingDegree s d i.succ) := ⟨(Fri.Spec.foldingDegree_pos s d _).ne'⟩
  unfold Fri.Spec.foldingError
  rw [ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  refine (mcaError_powers_le (Fri.Spec.foldingDegree_pos s d _) (by omega) _
    (hθ.trans (seven_sixteenths_le_relUDR (by rw [Fintype.card_fin]; exact h8)))).trans ?_
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ ?_)) _
  exact Nat.pow_le_pow_right two_pos (by omega)

/-- FRI's error at a radius at most `7/16`, at rate at most `1/8`: the powers MCA bound for each
fold and `(1 - δ) ^ numQueries` for the queries. -/
theorem friErrorOf_le {N : ℕ} (ω : Domain.SmoothCosetFftDomain N 𝕂) (f : ℕ+) (fs : List ℕ+)
    (logFinal l : ℕ) (δ : ℝ≥0) (hδ : δ ≤ 7 / 16)
    (h : 8 * (2 ^ (∑ j, (foldsAt f fs j).val) * 2 ^ logFinal) ≤ 2 ^ N) :
    friErrorOf ω (f :: fs) logFinal l δ ≤
      ∑ j, ((2 ^ (foldsAt f fs j).val - 1) * 2 ^ N : ℕ) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ) ^ l : ℝ≥0) : ENNReal) := by
  have hdom : 2 ^ (∑ j, (foldsAt f fs j).val) * (finalDegree logFinal).val ≤ 2 ^ N := by
    change 2 ^ (∑ j, (foldsAt f fs j).val) * 2 ^ logFinal ≤ 2 ^ N
    omega
  simp only [friErrorOf, hdom, ↓reduceIte, Fri.Spec.soundnessError, min_self, ENNReal.coe_add,
    ENNReal.ofNNReal_finsetSum]
  refine add_le_add (Finset.sum_le_sum fun j _ ↦ foldingError_le _ _ j h δ hδ) le_rfl

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

/-- FRI's error with arity `2`, `r` folds and rate at most `1/8`, at a radius at most `7/16`. -/
theorem friErrorOf_replicate_le {N : ℕ} (ω : Domain.SmoothCosetFftDomain N 𝕂) (m : ℕ)
    (logFinal l : ℕ) (δ : ℝ≥0) (hδ : δ ≤ 7 / 16) (h : 8 * 2 ^ (m + 1 + logFinal) ≤ 2 ^ N) :
    friErrorOf ω (List.replicate (m + 1) 1) logFinal l δ ≤
      ((m + 1) * 2 ^ N : ℕ) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ) ^ l : ℝ≥0) : ENNReal) := by
  have hsum : ∑ j, (foldsAt 1 (List.replicate m 1) j).val = m + 1 := by
    simp only [foldsAt_replicate, PNat.one_coe, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, List.length_replicate, smul_eq_mul, mul_one]
  rw [List.replicate_succ]
  refine (friErrorOf_le ω 1 _ logFinal l δ hδ (by rw [hsum, ← pow_add, mul_comm]; omega)).trans ?_
  simp only [foldsAt_replicate, PNat.one_coe, pow_one, Nat.add_one_sub_one, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, List.length_replicate, nsmul_eq_mul]
  rw [← mul_div_assoc, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-! ### The terms of a setup with blowup at least `16` at `δ ≤ 7/16` -/

/-- `16 n ≤ N` for a blowup of at least `16`. -/
theorem sixteen_mul_n_le_size (S : Setup) (hb : 4 ≤ S.params.logBlowup) : 16 * S.n ≤ S.size := by
  rw [Setup.n, Setup.size, pow_add, mul_comm]
  exact Nat.mul_le_mul_left _ (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ S.params.logBlowup := Nat.pow_le_pow_right two_pos hb)

/-- Below `7/16` at a blowup of at least `16`, the lists have at most one element. -/
theorem listSize_le_one_of_le (S : Setup) (hb : 4 ≤ S.params.logBlowup) (ι : Type) [Fintype ι]
    [DecidableEq ι] (δ : ℝ≥0) (hδ : δ ≤ 7 / 16) : S.listSize ι δ ≤ 1 := by
  apply listSize_le_one
  have h16 : (16 * S.n : ℝ) ≤ S.size := by exact_mod_cast sixteen_mul_n_le_size S hb
  have hpos : (0 : ℝ) < S.size := by exact_mod_cast Nat.two_pow_pos _
  have hrate : S.rate ≤ 1 / 16 := by
    rw [Setup.rate, div_le_iff₀ hpos]
    linarith
  have hδ' : (δ : ℝ) ≤ 7 / 16 := by exact_mod_cast hδ
  linarith

/-- The constraint-folding term with lists of at most one element. -/
theorem foldingError_le_of_le (S : Setup) (hb : 4 ≤ S.params.logBlowup) (δ : ℝ≥0)
    (hδ : δ ≤ 7 / 16) :
    foldingError S δ ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  calc S.listSize (Fin S.air.width) δ * (S.air.constraints.length - 1)
      ≤ 1 * (S.air.constraints.length - 1) :=
        Nat.mul_le_mul_right _ (listSize_le_one_of_le S hb _ δ hδ)
    _ = _ := one_mul _

/-- The out-of-domain term with lists of at most one element. -/
theorem outOfDomainError_le_of_le (S : Setup) (hb : 4 ≤ S.params.logBlowup) (δ : ℝ≥0)
    (hδ : δ ≤ 7 / 16) :
    outOfDomainError S δ ≤
      (S.identityDegree + S.size + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  have h := Nat.mul_le_mul_right S.identityDegree (Nat.mul_le_mul
    (listSize_le_one_of_le S hb (Fin S.air.width) δ hδ)
    (listSize_le_one_of_le S hb (Fin S.chunks × Fin 4) δ hδ))
  omega

/-- The batching term at a single radius: the powers MCA bound `(numOpened - 1) N / |𝕂|`. -/
theorem batchingError_le_of_le (S : Setup) (hb : 4 ≤ S.params.logBlowup) (δ : ℝ≥0)
    (hδ : δ ≤ 7 / 16) :
    batchingError S δ δ ≤ ((S.numOpened - 1) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  have h16 : 16 * 2 ^ S.logN ≤ 2 ^ (S.logN + S.params.logBlowup) := sixteen_mul_n_le_size S hb
  have : NeZero S.n := ⟨(Nat.two_pow_pos _).ne'⟩
  refine (batchingError_le_mcaError S δ).trans ?_
  exact mcaError_powers_le (Nat.two_pow_pos _) (by omega) _
    (hδ.trans (seven_sixteenths_le_relUDR (by rw [Fintype.card_fin]; omega)))

/-- FRI's term at arity `2`: `logN - logFinalPolyLen` folds, each at most `N / |𝕂|`, and the
queries. -/
theorem friError_le_of_le (S : Setup) (hb : 4 ≤ S.params.logBlowup)
    (harity : S.params.maxLogArity = 1) (δ : ℝ≥0) (hδ : δ ≤ 7 / 16) :
    friError S δ ≤ ((S.logN - S.params.logFinalPolyLen) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal)
      + ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hlt := S.folds
  obtain ⟨m, hm⟩ : ∃ m, S.logN - S.params.logFinalPolyLen = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  rw [friError, harity, hm, folds_one]
  apply friErrorOf_replicate_le _ _ _ _ _ hδ
  rw [show m + 1 + S.params.logFinalPolyLen = S.logN by omega, pow_add]
  calc 8 * 2 ^ S.logN ≤ 2 ^ S.logN * 2 ^ S.params.logBlowup := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (by
          calc 8 ≤ 2 ^ 4 := by norm_num
            _ ≤ 2 ^ S.params.logBlowup := Nat.pow_le_pow_right two_pos hb)
    _ = _ := rfl

/-- The knowledge error at arity `2`, blowup at least `16` and `δ ≤ 7/16` for both FRI and the
extractor: one integer over
`|𝕂|`, and `(1 - δ) ^ numQueries`. -/
theorem knowledgeError_le_of_le (S : Setup) (hb : 4 ≤ S.params.logBlowup)
    (harity : S.params.maxLogArity = 1) (δ : ℝ≥0) (hδ : δ ≤ 7 / 16) :
    knowledgeError S δ δ ≤
      ((S.air.constraints.length - 1) + (S.identityDegree + S.size + S.n) +
        (S.numOpened - 1) * S.size + (S.logN - S.params.logFinalPolyLen) * S.size : ℕ) /
          (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal) := by
  calc knowledgeError S δ δ
      ≤ (S.air.constraints.length - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          (S.identityDegree + S.size + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          ((S.numOpened - 1) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) +
          (((S.logN - S.params.logFinalPolyLen) * S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) +
            ((Real.toNNReal (1 - δ) ^ S.params.numQueries : ℝ≥0) : ENNReal)) :=
        add_le_add (add_le_add (add_le_add (foldingError_le_of_le S hb δ hδ)
          (outOfDomainError_le_of_le S hb δ hδ)) (batchingError_le_of_le S hb δ hδ))
          (friError_le_of_le S hb harity δ hδ)
    _ = _ := by
        simp only [← add_assoc, ENNReal.div_add_div_same, Nat.cast_add]

/-! ### The numbers -/

/-- `|𝕂| = p ^ 4 ≥ 2 ^ 123`. -/
theorem two_pow_le_card : (2 ^ 123 : ℝ) ≤ Fintype.card 𝕂 := by
  rw [KoalaBear.card_ext4, KoalaBear.fieldSize]
  norm_num

/-- At most `2 ^ 19` over `|𝕂|`, plus `(9/16) ^ 123`, is at most `2 ^ (-100)`. -/
theorem numbers_le (A : ℕ) (hA : A ≤ 2 ^ 19) :
    (A : ENNReal) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - ((7 / 16 : ℝ≥0) : ℝ)) ^ 123 : ℝ≥0) : ENNReal) ≤
      (2 ^ 100 : ENNReal)⁻¹ := by
  have hK := two_pow_le_card
  have hKpos : (0 : ℝ) < Fintype.card 𝕂 := lt_of_lt_of_le (by positivity) hK
  have hq : Real.toNNReal (1 - ((7 / 16 : ℝ≥0) : ℝ)) = 9 / 16 := by
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
  calc (A : ℝ) / Fintype.card 𝕂 + (9 / 16) ^ 123 ≤ 2 ^ 19 / 2 ^ 123 + (9 / 16) ^ 123 := by
        linarith
    _ ≤ (2 ^ 100)⁻¹ := by norm_num

end CompStark.Sound
