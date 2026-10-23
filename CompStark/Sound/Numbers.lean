/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.PowersMca
public import CompStark.Sound.Johnson
public import CompStark.Sound.Fri
public import CompStark.Sound.Batching
public import CompStark.Sound.LossyMca
public import CompStark.BatchSoundnessError

/-! # Bounds on the knowledge error's terms

At any FRI arity, with FRI's radius at most the unique-decoding radius `(1 - rate) / 2`, each term
of the knowledge error is an integer over `|𝕂|`, except FRI's queries and the curve and lossy
bounds:

* with the candidate lists at the extractor's radius of at most `ℓ` elements (`listSize_le_one`
  below the unique-decoding radius, `listSize_le_johnson` up to the Johnson radius), the
  constraint-folding and out-of-domain terms are at most `ℓ ℓₚ (#constraints - 1)` and
  `ℓ ℓₚ ℓ identityDegree + n` (`foldingError_le_of_listSize`, `outOfDomainError_le_of_listSize`);
* every code involved, the trace's and each folded FRI code, has the rate `1 / 2 ^ logBlowup`, so
  a radius at most `(1 - rate) / 2` is within its relative unique-decoding radius (`le_relUDR`),
  and the powers MCA bound `mcaError_powers_le` gives `(numOpened - 1) N` for batching at a
  single radius (`batchingError_le_mcaError`, and so at every larger one, `batchingError_anti`)
  and `M |L'|` for a fold onto the domain `L'` batching `M + 1` words;
* batching at `δ < δ'' = δ' - 2/N` is at most `(numOpened - 1) max(T₁, T₂)`
  (`batchingError_le_curve`);
* FRI at a proximity loss `loss > 0` (`friErrorWith_le`): Plonky3's schedule as a plan of folds
  (`FriGame.Rounds.plan`), each fold by `2 ^ k` onto a domain `L'` batching `M = 2 ^ k - 1` words
  besides the first (one more if it injects an input) and costing `levelBound`:
  `M min(B, |L'|) / |𝕂|` if `δ ≤ (1 - rate) / 2 - 1 / |L'|`, `B = max(T₁, T₂, δ_int / loss)` the
  lossy bound (`lossyMcaError_le`, any `δ_int > δ`), independent of `|L'|`, and `M |L'| / |𝕂|`
  otherwise (`levelError_le`, `foldError_schedule_le`); the queries contribute
  `(1 - δ + #folds · loss) ^ numQueries`.

`CompStark/Sound/Calculator.lean` casts them to the security calculator's rationals.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal ProximityGap CoreDefinitions Code

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
variable {lookups : List (Lookup F)}

local notation "𝕂" => Challenge.Spec EF

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

/-- The degree of FRI's code after fold `i` is a `c`-th of its domain when the initial code's
is. -/
theorem mul_foldingDegree_eq {N k : ℕ} (c : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
    (i : Fin (k + 1)) (h : c * (2 ^ (∑ j, (s j).val) * d.val) = 2 ^ N) :
    c * Fri.Spec.foldingDegree s d i.succ =
      2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) := by
  have hq := Fri.Spec.foldingPrefix_le s i.succ
  rw [Fri.Spec.foldingPrefix_succ] at hq
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · rw [zero_mul] at h
      exact absurd h.symm (Nat.two_pow_pos N).ne'
    · exact hc
  have hsN : ∑ j, (s j).val ≤ N := by
    by_contra hlt
    have : 2 ^ N < 2 ^ (∑ j, (s j).val) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ (∑ j, (s j).val) ≤ c * (2 ^ (∑ j, (s j).val) * d.val) :=
      (Nat.le_mul_of_pos_right _ d.pos).trans (Nat.le_mul_of_pos_left _ hc)
    omega
  set q := Fri.Spec.foldingPrefix s i.castSucc + (s i).val
  have hpq : N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val = N - q := by omega
  rw [hpq, Fri.Spec.foldingDegree, Fri.Spec.foldingPrefix_succ]
  refine Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos q) ?_
  rw [← pow_add, Nat.sub_add_cancel (by omega)]
  calc c * (2 ^ (∑ j, (s j).val - q) * d.val) * 2 ^ q
      = c * (2 ^ (∑ j, (s j).val - q + q) * d.val) := by rw [pow_add]; ring
    _ = c * (2 ^ (∑ j, (s j).val) * d.val) := by rw [Nat.sub_add_cancel hq]
    _ = 2 ^ N := h

/-- One FRI fold's error at rate `1/c` and a radius `θ ≤ (1 - 1/c) / 2`: the powers MCA bound
`(2 ^ s - 1) |L'| / |𝕂|` on the folded domain `L'`. -/
theorem foldingError_le {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂} (c : ℕ) (hc : 0 < c)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1))
    (h : c * (2 ^ (∑ j, (s j).val) * d.val) = 2 ^ N) (θ : ℝ≥0) (hθ : (θ : ℝ) * (2 * c) ≤ c - 1) :
    (Fri.Spec.foldingError (ω := ω) s d (θ : ℝ) i : ENNReal) ≤
      ((2 ^ (s i).val - 1) * 2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) : ℕ) /
        (Fintype.card 𝕂 : ENNReal) := by
  have hc' := (mul_foldingDegree_eq c s d i h).le
  have : NeZero (Fri.Spec.foldingDegree s d i.succ) := ⟨(Fri.Spec.foldingDegree_pos s d _).ne'⟩
  have hle : Fri.Spec.foldingDegree s d i.succ ≤
      2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) :=
    (Nat.le_mul_of_pos_left _ hc).trans hc'
  unfold Fri.Spec.foldingError
  rw [ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact mcaError_powers_le (Fri.Spec.foldingDegree_pos s d _) hle _
    (le_relUDR c (by rw [Fintype.card_fin]; exact hc') θ hθ)

/-- A nonnegative proximity loss can only lower a fold's error. -/
theorem foldingErrorLossy_le_foldingError {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1)) (θ loss : ℝ) (hloss : 0 ≤ loss) :
    (Fri.Spec.foldingErrorLossy (ω := ω) s d θ loss i : ENNReal) ≤
      Fri.Spec.foldingError (ω := ω) s d θ i := by
  unfold Fri.Spec.foldingErrorLossy Fri.Spec.foldingError
  rw [ENNReal.coe_toNNReal (lossyMcaError_ne_top _ _ _ _),
    ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact lossyMcaError_le_mcaError _ _ _ hloss

/-- `lossyBound` depends on the code only through its rate. -/
theorem lossyBound_congr {k n k' n' : ℕ} (h : (k : ℝ) / n = (k' : ℝ) / n') (δ_fld δ_int : ℝ≥0)
    (loss : ℝ) :
    LossyMca.lossyBound k n δ_fld δ_int loss = LossyMca.lossyBound k' n' δ_fld δ_int loss := by
  rw [LossyMca.lossyBound, LossyMca.lossyBound, h]

/-- One FRI fold's error at rate `1/c` on a folded domain `L'` with
`θ ≤ (1 - 1/c) / 2 - 1 / |L'|`: the lossy bound `(2 ^ s - 1) max(T₁, T₂, δ_int / loss) / |𝕂|`,
independent of `|L'|`. -/
theorem foldingErrorLossy_le {N k : ℕ} {ω : Domain.SmoothCosetFftDomain N 𝕂} (c : ℕ)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1))
    (h : c * (2 ^ (∑ j, (s j).val) * d.val) = 2 ^ N) (θ δ_int : ℝ≥0) (loss : ℝ)
    (hθ : (θ : ℝ) ≤ (1 - 1 / c) / 2 -
      1 / (2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val) : ℕ))
    (h_pos : 0 < θ) (h_lt : θ < δ_int) (h_loss : 0 < loss) :
    (Fri.Spec.foldingErrorLossy (ω := ω) s d θ loss i : ENNReal) ≤
      ENNReal.ofReal ((2 ^ (s i).val - 1) * LossyMca.lossyBound 1 c θ δ_int loss /
        Fintype.card 𝕂) := by
  have hc' := mul_foldingDegree_eq c s d i h
  have hc : 0 < c := Nat.pos_of_ne_zero fun hc ↦ by
    rw [hc, zero_mul] at hc'
    exact (Nat.two_pow_pos _).ne' hc'.symm
  have hrate : (Fri.Spec.foldingDegree s d i.succ : ℝ) /
      (Fintype.card (Fin (2 ^ (N - Fri.Spec.foldingPrefix s i.castSucc - (s i).val))) : ℝ) =
      ((1 : ℕ) : ℝ) / (c : ℕ) := by
    rw [Fintype.card_fin, ← hc', Nat.cast_mul, Nat.cast_one]
    have : (0 : ℝ) < c := by exact_mod_cast hc
    have : (0 : ℝ) < Fri.Spec.foldingDegree s d i.succ := by
      exact_mod_cast Fri.Spec.foldingDegree_pos s d _
    field_simp
  unfold Fri.Spec.foldingErrorLossy
  rw [ENNReal.coe_toNNReal (lossyMcaError_ne_top _ _ _ _), ← lossyBound_congr hrate]
  refine LossyMca.lossyMcaError_fold_le _ _ _ θ δ_int loss ?_ h_pos h_lt h_loss
  rw [hrate, Fintype.card_fin, Nat.cast_one]
  exact hθ

/-- A fold's error onto a domain of `2 ^ m` points at rate `1/c` over `M + 1` words, times `|𝕂|`:
`M min(B, 2 ^ m)` if `δ ≤ (1 - 1/c) / 2 - 2 ^ (-m)`, with `B = max(T₁, T₂, δ_int / loss)` the
lossy bound, and the powers MCA bound `M 2 ^ m` otherwise. -/
noncomputable def levelBound (c : ℕ) (δ δ_int : ℝ≥0) (loss : ℝ) (M m : ℕ) : ℝ :=
  M * if (δ : ℝ) ≤ (1 - 1 / c) / 2 - 1 / 2 ^ m then
    min (LossyMca.lossyBound 1 c δ δ_int loss) (2 ^ m) else 2 ^ m

theorem levelBound_nonneg (c : ℕ) (δ δ_int : ℝ≥0) {loss : ℝ} (h_loss : 0 < loss) (M m : ℕ) :
    0 ≤ levelBound c δ δ_int loss M m := by
  have hB : 0 ≤ LossyMca.lossyBound 1 c δ δ_int loss :=
    le_trans (div_nonneg δ_int.coe_nonneg h_loss.le) (le_max_right _ _)
  unfold levelBound
  split_ifs <;> positivity

/-- A fold's error onto a domain `D` of `2 ^ m` points at rate `1/c`, over `M + 1` words, for
`δ ≤ (1 - 1/c) / 2`: at most `levelBound` over `|𝕂|`, by lossy correlated agreement
(`lossyMcaError_le`) when `δ ≤ (1 - 1/c) / 2 - 2 ^ (-m)`, and by the powers MCA bound. -/
theorem levelError_le {m : ℕ} (D : Domain.SmoothCosetFftDomain m 𝕂) (M c deg : ℕ) (hc : 0 < c)
    (hdeg : c * deg = 2 ^ m) (δ δ_int : ℝ≥0) (loss : ℝ) (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2)
    (h_pos : 0 < δ) (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    lossyMcaError (univariatePowersGenerator 𝕂 M) (ReedSolomon.code (D : Fin (2 ^ m) ↪ 𝕂) deg)
        δ loss ≤ ENNReal.ofReal (levelBound c δ δ_int loss M m / Fintype.card 𝕂) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  have hdegpos : 0 < deg := Nat.pos_of_ne_zero fun h ↦ by
    rw [h, mul_zero] at hdeg
    exact (Nat.two_pow_pos m).ne' hdeg.symm
  have hrate : (deg : ℝ) / (Fintype.card (Fin (2 ^ m)) : ℝ) = ((1 : ℕ) : ℝ) / (c : ℕ) := by
    rw [Fintype.card_fin, ← hdeg, Nat.cast_mul, Nat.cast_one]
    have : (0 : ℝ) < deg := by exact_mod_cast hdegpos
    field_simp
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have : NeZero deg := ⟨hdegpos.ne'⟩
  have hudr : (δ : ℝ) * (2 * c) ≤ c - 1 := by
    have h3 : ((1 - 1 / c) / 2 : ℝ) * (2 * c) = c - 1 := by field_simp
    nlinarith
  have hmca : lossyMcaError (univariatePowersGenerator 𝕂 M)
      (ReedSolomon.code (D : Fin (2 ^ m) ↪ 𝕂) deg) δ loss ≤
        ENNReal.ofReal (M * 2 ^ m / Fintype.card 𝕂) := by
    refine (lossyMcaError_le_mcaError _ _ _ h_loss.le).trans ?_
    refine (mcaError_powers_le hdegpos (by rw [← hdeg]; exact Nat.le_mul_of_pos_left _ hc) M
      (le_relUDR c (by rw [Fintype.card_fin, hdeg]) δ hudr)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_div_of_pos hK, ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast]
    push_cast
    rfl
  unfold levelBound
  split_ifs with hl
  · have hlossy := LossyMca.lossyMcaError_le (F := 𝕂) (D : Fin (2 ^ m) ↪ 𝕂) deg M δ δ_int loss
      (by rw [hrate, Fintype.card_fin, Nat.cast_one]; push_cast; exact hl) h_pos h_lt h_loss
    rw [lossyBound_congr hrate] at hlossy
    rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg M), ← min_div_div_right hK.le, ENNReal.ofReal_min]
    exact le_min hlossy hmca
  · exact hmca

/-- `ofReal (x / K) + ofReal (y / K) = ofReal ((x + y) / K)` for `x, y ≥ 0`. -/
theorem ofReal_div_add_ofReal_div {x y : ℝ} (K : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hK : 0 < K) :
    ENNReal.ofReal (x / K) + ENNReal.ofReal (y / K) = ENNReal.ofReal ((x + y) / K) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]

/-- The level bounds of a plan's folds at rate `1/c`, summed. -/
noncomputable def planBound (c : ℕ) (δ δ_int : ℝ≥0) (loss : ℝ) (plan : List (ℕ × ℕ × Bool)) :
    ℝ :=
  (plan.map fun f ↦ levelBound c δ δ_int loss (FriGame.Rounds.foldWords f) f.2.1).sum

theorem planBound_nonneg (c : ℕ) (δ δ_int : ℝ≥0) {loss : ℝ} (h_loss : 0 < loss) :
    ∀ plan : List (ℕ × ℕ × Bool), 0 ≤ planBound c δ δ_int loss plan
  | [] => le_rfl
  | _ :: plan => by
    rw [planBound, List.map_cons, List.sum_cons]
    exact add_nonneg (levelBound_nonneg c δ δ_int h_loss _ _)
      (planBound_nonneg c δ δ_int h_loss plan)

/-- A fold by `2 ^ la` batches `2 ^ la - 1` words besides the first, and one more if it injects. -/
theorem foldWords_false (la m : ℕ) : FriGame.Rounds.foldWords (la, m, false) = 2 ^ la - 1 := rfl

theorem foldWords_true (la m : ℕ) : FriGame.Rounds.foldWords (la, m, true) = 2 ^ la :=
  Nat.sub_add_cancel Nat.one_le_two_pow

open FriGame in
/-- The folds' errors of Plonky3's schedule at any arity and rate `1/c` (`c d = 2 ^ logFinal`), for
`δ ≤ (1 - 1/c) / 2`: the plan's level bounds over `|𝕂|`. -/
theorem foldError_schedule_le (c : ℕ) (hc : 0 < c) (a : ℕ) (ha : 0 < a) (d logFinal : ℕ)
    (hd : c * d = 2 ^ logFinal) (δ δ_int : ℝ≥0) (loss : ℝ) (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2)
    (h_pos : 0 < δ) (h_lt : δ < δ_int) (h_loss : 0 < loss) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂) :
    ∀ (fuel n : ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂) (heights : List ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Rounds.Fits logFinal n heights →
      (Rounds.schedule a logFinal words fuel n heights).foldError d δ loss ω ≤
        ENNReal.ofReal (planBound c δ δ_int loss (Rounds.plan a logFinal fuel n heights) /
          Fintype.card 𝕂)
  | 0, n, ω, heights, hn, hfuel, hfit => by
    rw [Rounds.schedule, Rounds.foldError]
    exact bot_le
  | fuel + 1, n, ω, heights, hn, hfuel, hfit => by
    by_cases hfin : n ≤ logFinal
    · rw [Rounds.schedule, ite_eq_left hfin, Rounds.foldError]
      exact bot_le
    have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
    have h1 := Rounds.one_le_logArity ha (by omega) hfit
    have h2 := Rounds.logArity_le a logFinal n heights
    -- one fold onto `2 ^ (n - la)` points, and the rest
    have hstep (la : ℕ) (hla1 : 1 ≤ la) (hla2 : la ≤ n - logFinal) (M : ℕ) (inj : Bool)
        (hM : M = Rounds.foldWords (la, n - la, inj)) (h : List ℕ)
        (hf : Rounds.Fits logFinal (n - la) h) :
        lossyMcaError (univariatePowersGenerator 𝕂 M)
            (ReedSolomon.code ((ω.subdomain la : Domain.SmoothCosetFftDomain (n - la) 𝕂) :
              Fin (2 ^ (n - la)) ↪ 𝕂) ((Rounds.schedule a logFinal words fuel (n - la) h).degree d))
            δ loss + (Rounds.schedule a logFinal words fuel (n - la) h).foldError d δ loss
              (ω.subdomain la) ≤
          ENNReal.ofReal (planBound c δ δ_int loss
            ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h) / Fintype.card 𝕂) := by
      have hdeg : c * (Rounds.schedule a logFinal words fuel (n - la) h).degree d =
          2 ^ (n - la) := by
        rw [Rounds.degree_schedule ha words d fuel _ h (by omega) (by omega) hf, mul_left_comm,
          hd, ← pow_add]
        congr 1
        omega
      have hlevel := levelError_le (ω.subdomain la) M c _ hc hdeg δ δ_int loss hδ h_pos h_lt
        h_loss
      have ih := foldError_schedule_le c hc a ha d logFinal hd δ δ_int loss hδ h_pos h_lt h_loss
        words fuel (n - la) (ω.subdomain la) h (by omega) (by omega) hf
      refine (add_le_add hlevel ih).trans (le_of_eq ?_)
      rw [ofReal_div_add_ofReal_div _ (levelBound_nonneg c δ δ_int h_loss _ _)
        (planBound_nonneg c δ δ_int h_loss _) hK, hM]
      simp only [planBound, List.map_cons, List.sum_cons]
    rw [Rounds.schedule, ite_eq_right hfin]
    match heights, hfit, h1, h2 with
    | [], hfit, h1, h2 =>
      simp only [Rounds.foldError, Rounds.plan, ite_eq_right hfin]
      exact hstep _ h1 h2 _ false (foldWords_false _ _).symm [] (Rounds.fits_nil _ _)
    | m :: rest, hfit, h1, h2 =>
      have h3 := Rounds.logArity_le_cons a logFinal n m rest
      by_cases hm : m = n - Rounds.logArity a logFinal n (m :: rest)
      · simp only [ite_eq_left hm, Rounds.foldError, Rounds.plan, ite_eq_right hfin]
        exact hstep _ h1 h2 _ true (foldWords_true _ _).symm rest (Rounds.fits_of_eq hfit hm)
      · simp only [ite_eq_right hm, Rounds.foldError, Rounds.plan, ite_eq_right hfin]
        exact hstep _ h1 h2 _ false (foldWords_false _ _).symm _
          (Rounds.fits_cons_of_ne hfit h3 hm)

/-! ### The terms of a setup -/

/-- The rate is `1 / 2 ^ logBlowup`. -/
theorem rate_eq (S : Setup EF lookups) : S.rate = 1 / 2 ^ S.params.logBlowup := by
  rw [Setup.rate, Setup.n, Setup.size, pow_add]
  push_cast
  field_simp

/-- Below the unique-decoding radius `(1 - rate) / 2`, with `c = 2 ^ logBlowup`. -/
theorem mul_le_of_le_udr (S : Setup EF lookups) (δ : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) :
    (δ : ℝ) * (2 * (2 ^ S.params.logBlowup : ℕ)) ≤ (2 ^ S.params.logBlowup : ℕ) - 1 := by
  rw [rate_eq, le_div_iff₀ two_pos] at hδ
  have hc : (0 : ℝ) < 2 ^ S.params.logBlowup := by positivity
  have h1 := mul_le_mul_of_nonneg_right hδ hc.le
  have h2 : (1 - 1 / (2 : ℝ) ^ S.params.logBlowup) * 2 ^ S.params.logBlowup =
      2 ^ S.params.logBlowup - 1 := by field_simp
  push_cast
  nlinarith

/-- With the candidate lists at `δ` of at most `ℓ` elements and the permutation trace's of at most
`ℓp`, the constraint-folding term is at most `ℓ ℓp (#constraints - 1)` over `|𝕂|`. -/
theorem foldingError_le_of_listSize (S : Setup EF lookups) (δ : ℝ≥0) (ℓ ℓp : ℕ)
    (hℓ : S.listSize (Fin S.air.width) δ ≤ ℓ) (hℓp : S.permListSize δ ≤ ℓp) :
    foldingError S δ ≤ (ℓ * ℓp * (S.numConstraints - 1) : ℕ) / (Fintype.card 𝕂 : ENNReal) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.mul_le_mul hℓ hℓp))) _

/-- With the candidate lists at `δ` of at most `ℓ` elements and the permutation trace's of at most
`ℓp`, the out-of-domain term is at most `ℓ ℓp ℓ identityDegree + n` over `|𝕂|`. -/
theorem outOfDomainError_le_of_listSize (S : Setup EF lookups) (δ : ℝ≥0) (ℓ ℓp : ℕ)
    (hℓ : S.listSize (Fin S.air.width) δ ≤ ℓ) (hℓp : S.permListSize δ ≤ ℓp)
    (hℓq : S.listSize (Fin S.chunks × Fin (Challenge.d EF)) δ ≤ ℓ) :
    outOfDomainError S δ ≤
      (ℓ * ℓp * ℓ * S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul hℓ hℓp) hℓq)) _)) _

/-- FRI's term at any arity, for `δ ≤ (1 - rate) / 2` and a proximity loss `loss > 0`: the level
bounds of its folds' plan over `|𝕂|` (`foldError_schedule_le`, any `δ_int > δ`), and the queries
`(1 - δ + #folds · loss) ^ numQueries`. -/
theorem friErrorWith_le (S : Setup EF lookups) (heights : List ℕ)
    (hfit : FriGame.Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights)
    (δ δ_int loss : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2) (h_pos : 0 < δ) (h_lt : δ < δ_int)
    (h_loss : 0 < loss) :
    friErrorWith S heights δ ≤
      ENNReal.ofReal (planBound (2 ^ S.params.logBlowup) δ δ_int loss
          (FriGame.Rounds.plan S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
            (S.logN + S.params.logBlowup) (S.logN + S.params.logBlowup) heights) /
          Fintype.card 𝕂) +
        ((Real.toNNReal (1 - δ + (FriGame.Rounds.plan S.params.maxLogArity
          (S.params.logFinalPolyLen + S.params.logBlowup) (S.logN + S.params.logBlowup)
          (S.logN + S.params.logBlowup) heights).length * loss) ^
            S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hf := S.valid.finalPolyFits
  refine (iInf_le _ loss).trans (add_le_add ?_ (le_of_eq ?_))
  · rw [Setup.friRounds]
    refine foldError_schedule_le (2 ^ S.params.logBlowup) (Nat.two_pow_pos _) _ S.valid.folds _ _
      (by rw [← pow_add, add_comm]) δ δ_int loss ?_ h_pos h_lt h_loss _ _ _ S.domain heights
      (by omega) (Nat.sub_le _ _) hfit
    rw [rate_eq] at hδ
    push_cast
    exact hδ
  · rw [Setup.friRounds, FriGame.Rounds.numFolds_schedule, ENNReal.coe_pow]
    rfl

/-! ### The numbers -/

/-- `|𝕂| = p ^ d`. -/
theorem card_eq : (Fintype.card 𝕂 : ℝ) = (Nat.card F : ℝ) ^ Challenge.d EF := by
  rw [Challenge.card_spec, Nat.cast_pow]

/-- `2 ^ (-bits)` as a real number. -/
theorem inv_two_pow_eq (bits : ℕ) : (2 ^ bits : ENNReal)⁻¹ = ENNReal.ofReal (2 ^ bits)⁻¹ := by
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_inv_of_pos (by positivity)]

end CompStark.Sound
