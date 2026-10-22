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

/-! # Bounds on the knowledge error's terms below the unique-decoding radius

At FRI arity `2`, with the extractor's radius below the unique-decoding radius `(1 - rate) / 2`,
each term of the knowledge error is an integer over `|𝕂|`, except FRI's queries and the curve
bounds on batching and FRI's large folds:

* the candidate lists have at most one element (`listSize_le_one`), so the constraint-folding and
  out-of-domain terms are at most `#constraints - 1` and `identityDegree + n`;
* every code involved, the trace's and each folded FRI code, has the rate `1 / 2 ^ logBlowup`, so
  a radius below `(1 - rate) / 2` is within its relative unique-decoding radius (`le_relUDR`), and
  the powers MCA bound `mcaError_powers_le` gives `(numOpened - 1) N` for batching at a single
  radius (`batchingError_le_mcaError`, and so at every larger one, `batchingError_anti`) and `|L'|`
  for a fold onto the domain `L'`;
* batching at `δ < δ'' = δ' - 2/N` is at most `(numOpened - 1) max(T₁, T₂)`
  (`batchingError_le_curve`);
* FRI at a proximity loss `loss > 0` (`friErrorWith_le_lossy`): a fold onto a domain `L'` with
  `δ ≤ (1 - rate) / 2 - 1 / |L'|` has lossy MCA error at most `max(T₁, T₂, δ_int / loss)`
  (`lossyMcaError_line_le`, any `δ_int > δ`), independent of `|L'|`; the smaller domains, below a
  threshold `2 ^ t`, take the lossless bound `|L'|` and sum to at most `2 ^ t`; the queries
  contribute `(1 - δ + #folds · loss) ^ numQueries`.

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

/-- Folding by arity `2` halves `r` times. -/
theorem folds_one : ∀ r, folds 1 r = List.replicate r 1
  | 0 => by rw [folds]; rfl
  | r + 1 => by
    rw [folds, List.replicate_succ]
    congr 1
    rw [show r + 1 - max 1 (min 1 (r + 1)) = r by omega]
    exact folds_one r

/-- An arity-`2` fold's error onto a domain `D` of `2 ^ m` points at rate `1/c`, over `M + 1`
words (the fold's two coefficient words, and an injected input): `M · max(T₁, T₂, δ_int / loss)`
over `|𝕂|` if `D` has at least `2 ^ t` points (`lossyMcaError_le`), and the powers MCA bound
`M · 2 ^ m` over `|𝕂|` otherwise. -/
theorem levelError_le {m : ℕ} (D : Domain.SmoothCosetFftDomain m 𝕂) (M c t deg : ℕ) (hc : 0 < c)
    (hdeg : c * deg = 2 ^ m) (δ δ_int loss : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2 - 1 / 2 ^ t)
    (h_pos : 0 < δ) (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    lossyMcaError (univariatePowersGenerator 𝕂 M) (ReedSolomon.code (D : Fin (2 ^ m) ↪ 𝕂) deg)
        δ loss ≤
      if t ≤ m then ENNReal.ofReal (M * LossyMca.lossyBound 1 c δ δ_int loss / Fintype.card 𝕂)
      else ((M * 2 ^ m : ℕ) : ENNReal) / Fintype.card 𝕂 := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hdegpos : 0 < deg := Nat.pos_of_ne_zero fun h ↦ by
    rw [h, mul_zero] at hdeg
    exact (Nat.two_pow_pos m).ne' hdeg.symm
  have hrate : (deg : ℝ) / (Fintype.card (Fin (2 ^ m)) : ℝ) = ((1 : ℕ) : ℝ) / (c : ℕ) := by
    rw [Fintype.card_fin, ← hdeg, Nat.cast_mul, Nat.cast_one]
    have : (0 : ℝ) < deg := by exact_mod_cast hdegpos
    field_simp
  split_ifs with ht
  · rw [← lossyBound_congr hrate]
    refine LossyMca.lossyMcaError_le _ _ _ δ δ_int loss ?_ h_pos h_lt h_loss
    rw [hrate, Fintype.card_fin, Nat.cast_one]
    have hpow : (2 : ℝ) ^ t ≤ ((2 ^ m : ℕ) : ℝ) := by
      push_cast
      exact pow_le_pow_right₀ (by norm_num) ht
    have := one_div_le_one_div_of_le (by positivity) hpow
    push_cast at this ⊢
    linarith
  · have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
    have : NeZero deg := ⟨hdegpos.ne'⟩
    have hudr : (δ : ℝ) * (2 * c) ≤ c - 1 := by
      have h2 : (0 : ℝ) < 1 / 2 ^ t := by positivity
      have h3 : ((1 - 1 / c) / 2 : ℝ) * (2 * c) = c - 1 := by field_simp
      nlinarith
    refine (lossyMcaError_le_mcaError _ _ _ loss.coe_nonneg).trans ?_
    exact mcaError_powers_le hdegpos (by rw [← hdeg]; exact Nat.le_mul_of_pos_left _ hc) M
      (le_relUDR c (by rw [Fintype.card_fin, hdeg]) δ hudr)

/-- `ofReal (a x / K) + ofReal (b x / K) = ofReal ((a + b) x / K)`. -/
theorem ofReal_add_mul_div (a b : ℕ) (x K : ℝ) (hx : 0 ≤ x) (hK : 0 < K) :
    ENNReal.ofReal (a * x / K) + ENNReal.ofReal (b * x / K) =
      ENNReal.ofReal ((a + b : ℕ) * x / K) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  push_cast
  ring

/-- One fold's error `e` and the rest's: a large fold adds `M` bounds `B`, a small one `2 ^ (n - 1)`
to the small folds' `2 ^ min (n - 1) t`. -/
theorem fold_add_le (n t len M L : ℕ) (hn : 1 ≤ n) (hM : M = 1 ∨ (M = 2 ∧ t ≤ n - 1))
    (hL : n - t + (len + (M - 1)) = L) (B : ℝ) (K : ℕ) (hB : 0 ≤ B) (hK : 0 < K) (e rest : ENNReal)
    (he : e ≤ if t ≤ n - 1 then ENNReal.ofReal (M * B / K)
      else ((M * 2 ^ (n - 1) : ℕ) : ENNReal) / K)
    (hrest : rest ≤ ENNReal.ofReal ((n - 1 - t + len : ℕ) * B / K) +
      ((2 ^ min (n - 1) t : ℕ) : ENNReal) / K) :
    e + rest ≤ ENNReal.ofReal ((L : ℕ) * B / K) + ((2 ^ min n t : ℕ) : ENNReal) / K := by
  subst hL
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  split_ifs at he with h
  · have hcount : M + (n - 1 - t + len) = n - t + (len + (M - 1)) := by omega
    calc e + rest
        ≤ ENNReal.ofReal (M * B / K) + (ENNReal.ofReal ((n - 1 - t + len : ℕ) * B / K) +
            ((2 ^ min (n - 1) t : ℕ) : ENNReal) / K) := add_le_add he hrest
      _ = ENNReal.ofReal ((n - t + (len + (M - 1)) : ℕ) * B / K) +
            ((2 ^ min (n - 1) t : ℕ) : ENNReal) / K := by
          rw [← add_assoc, ofReal_add_mul_div _ _ _ _ hB hK', hcount]
      _ ≤ _ := by
          gcongr
          omega
  · have hM1 : M = 1 := by omega
    subst hM1
    have hsmall : 2 ^ min (n - 1) t + 2 ^ (n - 1) ≤ 2 ^ min n t := by
      rw [min_eq_left (by omega), min_eq_left (by omega), ← two_mul, ← pow_succ']
      exact Nat.pow_le_pow_right two_pos (by omega)
    have hcount : n - 1 - t + len = n - t + (len + (1 - 1)) := by omega
    calc e + rest
        ≤ ((1 * 2 ^ (n - 1) : ℕ) : ENNReal) / K +
            (ENNReal.ofReal ((n - 1 - t + len : ℕ) * B / K) +
              ((2 ^ min (n - 1) t : ℕ) : ENNReal) / K) := add_le_add he hrest
      _ = ENNReal.ofReal ((n - t + (len + (1 - 1)) : ℕ) * B / K) +
            ((2 ^ min (n - 1) t + 2 ^ (n - 1) : ℕ) : ENNReal) / K := by
          rw [hcount, one_mul, Nat.cast_add (2 ^ min (n - 1) t), ENNReal.add_div]
          ring
      _ ≤ _ := by
          gcongr

open FriGame in
/-- The folds' errors of Plonky3's schedule at arity `2` and rate `1/c` (`c d = 2 ^ logFinal`), with
inputs injected at heights of at least `2 ^ t` points: the at most `n - t` folds onto domains of
at least `2 ^ t` points contribute `max(T₁, T₂, δ_int / loss) / |𝕂|` each, and each injected input
one more; the smaller ones the powers MCA bound on their halving domains, `2 ^ t` together. -/
theorem foldError_schedule_one_le (c t : ℕ) (hc : 0 < c) (d logFinal : ℕ)
    (hd : c * d = 2 ^ logFinal) (δ δ_int loss : ℝ≥0)
    (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ) (h_lt : δ < δ_int)
    (h_loss : 0 < loss) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂) :
    ∀ (fuel n : ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂) (heights : List ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Rounds.Fits logFinal n heights →
      (∀ m ∈ heights, t ≤ m) →
      (Rounds.schedule 1 logFinal words fuel n heights).foldError d δ loss ω ≤
        ENNReal.ofReal ((n - t + heights.length : ℕ) * LossyMca.lossyBound 1 c δ δ_int loss /
          Fintype.card 𝕂) + ((2 ^ min n t : ℕ) : ENNReal) / Fintype.card 𝕂
  | 0, n, ω, heights, hn, hfuel, hfit, ht => by
    rw [Rounds.schedule, Rounds.foldError]
    exact bot_le
  | fuel + 1, n, ω, heights, hn, hfuel, hfit, ht => by
    by_cases hfin : n ≤ logFinal
    · rw [Rounds.schedule, ite_eq_left hfin, Rounds.foldError]
      exact bot_le
    have hB : 0 ≤ LossyMca.lossyBound 1 c δ δ_int loss :=
      le_trans (by positivity) (le_max_right _ _)
    have hla := Rounds.logArity_one (by omega) hfit
    have hdeg (h : List ℕ) (hf : Rounds.Fits logFinal (n - 1) h) :
        c * (Rounds.schedule 1 logFinal words fuel (n - 1) h).degree d = 2 ^ (n - 1) := by
      rw [Rounds.degree_schedule Nat.one_pos words d fuel _ h (by omega) (by omega) hf,
        mul_left_comm, hd, ← pow_add]
      congr 1
      omega
    have hlevel (M : ℕ) (h : List ℕ) (hf : Rounds.Fits logFinal (n - 1) h) :=
      levelError_le (ω.subdomain 1) M c t _ hc (hdeg h hf) δ δ_int loss hδ h_pos h_lt h_loss
    have ih (h : List ℕ) (hf : Rounds.Fits logFinal (n - 1) h) (ht' : ∀ m ∈ h, t ≤ m) :=
      foldError_schedule_one_le c t hc d logFinal hd δ δ_int loss hδ h_pos h_lt h_loss words
        fuel (n - 1) (ω.subdomain 1) h (by omega) (by omega) hf ht'
    have hK := Fintype.card_pos (α := 𝕂)
    rw [Rounds.schedule, ite_eq_right hfin]
    match heights, hfit, ht, hla with
    | [], hfit, ht, hla =>
      simp only [Rounds.foldError]
      rw [hla]
      exact fold_add_le n t 0 (2 ^ 1 - 1) _ (by omega) (Or.inl rfl) (by simp) _ _ hB hK _ _
        (hlevel _ [] (Rounds.fits_nil _ _))
        (ih [] (Rounds.fits_nil _ _) fun _ h ↦ absurd h List.not_mem_nil)
    | m :: rest, hfit, ht, hla =>
      have h3 := Rounds.logArity_le_cons 1 logFinal n m rest
      by_cases hm : m = n - Rounds.logArity 1 logFinal n (m :: rest)
      · simp only [ite_eq_left hm, Rounds.foldError]
        rw [hla] at hm ⊢
        have hfr := Rounds.fits_of_eq hfit hm
        exact fold_add_le n t rest.length (2 ^ 1) _ (by omega)
          (Or.inr ⟨rfl, hm ▸ ht m List.mem_cons_self⟩) (by simp) _ _ hB hK _ _ (hlevel _ rest hfr)
          (ih rest hfr fun m' h ↦ ht m' (List.mem_cons_of_mem _ h))
      · simp only [ite_eq_right hm, Rounds.foldError]
        rw [hla] at hm ⊢
        have hfr := Rounds.fits_cons_of_ne hfit (by omega) hm
        exact fold_add_le n t (rest.length + 1) (2 ^ 1 - 1) _ (by omega) (Or.inl rfl) (by simp) _ _
          hB hK _ _ (hlevel _ _ hfr) (ih _ hfr ht)

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

/-- Below the unique-decoding radius, the permutation trace's list has at most one element. -/
theorem permListSize_le_one (S : Setup EF lookups) (δ : ℝ) (hδ : δ < (1 - S.rate) / 2) :
    S.permListSize δ ≤ 1 := by
  cases lookups with
  | nil => exact le_rfl
  | cons l ls => exact listSize_le_one S _ δ hδ

/-- Below the unique-decoding radius, the lists have at most one element. -/
theorem foldingError_le_of_le (S : Setup EF lookups) (δ : ℝ≥0)
    (hδ : (δ : ℝ) < (1 - S.rate) / 2) :
    foldingError S δ ≤ (S.numConstraints - 1 : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  calc S.listSize (Fin S.air.width) δ * S.permListSize δ * (S.numConstraints - 1)
      ≤ 1 * 1 * (S.numConstraints - 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (listSize_le_one S _ δ hδ)
          (permListSize_le_one S δ hδ))
    _ = _ := by rw [one_mul, one_mul]

/-- The out-of-domain term below the unique-decoding radius. -/
theorem outOfDomainError_le_of_le (S : Setup EF lookups) (δ : ℝ≥0)
    (hδ : (δ : ℝ) < (1 - S.rate) / 2) :
    outOfDomainError S δ ≤
      (S.identityDegree + S.n : ℕ) / (Fintype.card 𝕂 : ENNReal) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  have h := Nat.mul_le_mul_right S.identityDegree (Nat.mul_le_mul (Nat.mul_le_mul
    (listSize_le_one S (Fin S.air.width) δ hδ) (permListSize_le_one S δ hδ))
    (listSize_le_one S (Fin S.chunks × Fin (Challenge.d EF)) δ hδ))
  omega

/-- FRI's term at arity `2` from lossy correlated agreement, at a proximity loss `loss > 0` and a
radius `δ ≤ (1 - rate) / 2 - 1 / 2 ^ t`, with inputs injected at heights of at least `2 ^ t`
points: the at most `log₂ N - t` folds onto domains of at least `2 ^ t` points contribute
`max(T₁, T₂, δ_int / loss) / |𝕂|` each (`lossyMcaError_line_le`, any `δ_int > δ`), and each
injected input one more; the smaller ones `2 ^ t / |𝕂|` together, and the queries
`(1 - δ + #folds · loss) ^ numQueries`. -/
theorem friErrorWith_le_lossy (S : Setup EF lookups) (harity : S.params.maxLogArity = 1) (t : ℕ)
    (heights : List ℕ)
    (hfit : FriGame.Rounds.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights) (ht : ∀ m ∈ heights, t ≤ m)
    (δ δ_int loss : ℝ≥0) (hδ : (δ : ℝ) ≤ (1 - S.rate) / 2 - 1 / 2 ^ t) (h_pos : 0 < δ)
    (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    friErrorWith S heights δ ≤
      ENNReal.ofReal ((S.logN + S.params.logBlowup - t + heights.length : ℕ) *
          LossyMca.lossyBound 1 (2 ^ S.params.logBlowup) δ δ_int loss) /
          (Fintype.card 𝕂 : ENNReal) +
        (2 ^ t : ℕ) / (Fintype.card 𝕂 : ENNReal) +
        ((Real.toNNReal (1 - δ + (S.logN - S.params.logFinalPolyLen : ℕ) * loss) ^
          S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hf := S.valid.finalPolyFits
  have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
  refine (iInf_le _ loss).trans (add_le_add ?_ (le_of_eq ?_))
  · rw [Setup.friRounds, harity]
    refine (foldError_schedule_one_le (2 ^ S.params.logBlowup) t (Nat.two_pow_pos _) _ _
      (by rw [← pow_add, add_comm]) δ δ_int loss ?_ h_pos h_lt h_loss _ _ _ S.domain heights
      (by omega) (Nat.sub_le _ _) hfit ht).trans ?_
    · rw [rate_eq] at hδ
      push_cast
      exact hδ
    · rw [ENNReal.ofReal_div_of_pos hK, ENNReal.ofReal_natCast]
      gcongr
      exact min_le_right _ _
  · rw [Setup.friRounds, harity, FriGame.Rounds.numFolds_schedule_one _ _ _ _ (by omega)
      (Nat.sub_le _ _) hfit, ENNReal.coe_pow,
      show S.logN + S.params.logBlowup - (S.params.logFinalPolyLen + S.params.logBlowup) =
        S.logN - S.params.logFinalPolyLen by omega]
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
