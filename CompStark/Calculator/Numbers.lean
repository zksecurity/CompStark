/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Johnson
public import CompStark.Sound.Fri
public import CompStark.Sound.Batching
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.UniqueDecoding.LossyCurves
public import CompStark.Calculator.McaBound
public import CompStark.Iop.BatchError

/-! # Bounds on the knowledge error's terms

At any FRI arity and any radius, each term of the knowledge error is an integer over `|𝕂|`, except
FRI's queries and the bounds on correlated agreement:

* with the candidate lists at the extractor's radius of at most `ℓ` elements (`listSize_le_one`
  below the unique-decoding radius, `listSize_le_johnson` up to the Johnson radius), the
  constraint-folding and out-of-domain terms are at most `ℓ ℓₚ (#constraints - 1)` and
  `ℓ identityDegree + n + N`, the latter's list that of the committed words as one family
  (`foldingError_le_of_listSize`, `outOfDomainError_le_of_listSize`);
* batching at a single radius is at most the MCA error of the powers (`batchingError_le_mcaError`,
  and so at every larger one, `batchingError_anti`), which an MCA bound (`McaBound.Holds`) bounds;
  batching at `δ < δ'` with `δ ≤ (1 - rate) / 2 - 1/N` is at most
  `(numOpened - 1) max(T₁, T₂)` (`batchingError_le_curve`);
* FRI at a proximity loss (`friErrorWith_le`): Plonky3's schedule as a list of folds
  (`Fri.Interaction.Schedule.folds`), each fold by `2 ^ k` onto a domain `L'` batching
  `M = 2 ^ k - 1` words besides the first (one more if it injects an input) bounded on its own
  (`FoldBounds`, `foldError_schedule_le`): by an MCA bound's count (`mcaLevel_le`) and, if
  `δ ≤ (1 - rate) / 2 - 1 / |L'|`, by the lossy bound `M max(T₁, T₂, δ_int / loss)`
  (`lossyLevel_le`, `lossyMcaError_le`, any `δ_int > δ`), independent of `|L'|`; the queries
  contribute `(1 - δ + #folds · loss) ^ numQueries`.

`CompStark/Calculator/Sound.lean` casts them to the security calculator's rationals.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop NNReal ProximityGap CoreDefinitions Code CodingTheory

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
variable {lookups : List (Lookup F)}

local notation "𝕂" => Challenge.Spec EF

/-- `lossyBound` depends on the code only through its rate. -/
theorem lossyBound_congr {k n k' n' : ℕ} (h : (k : ℝ) / n = (k' : ℝ) / n') (δ_fld δ_int : ℝ≥0)
    (loss : ℝ) :
    UniqueDecoding.lossyBound k n δ_fld δ_int loss =
      UniqueDecoding.lossyBound k' n' δ_fld δ_int loss := by
  rw [UniqueDecoding.lossyBound, UniqueDecoding.lossyBound, h]

/-- A fold's error onto a domain of `2 ^ m` points at rate `1/c`, over `M + 1` words, for
`δ ≤ (1 - 1/c) / 2 - 2 ^ (-m)`: the lossy bound `M max(T₁, T₂, δ_int / loss) / |𝕂|`
(`lossyMcaError_le`), independent of `2 ^ m`. -/
theorem lossyLevel_le {m : ℕ} (D : Fin (2 ^ m) ↪ 𝕂) (M c deg : ℕ) (hdeg : c * deg = 2 ^ m)
    (δ δ_int : ℝ≥0) (loss : ℝ) (hδ : (δ : ℝ) ≤ (1 - 1 / c) / 2 - 1 / 2 ^ m) (h_pos : 0 < δ)
    (h_lt : δ < δ_int) (h_loss : 0 < loss) :
    lossyMcaError (univariatePowersGenerator 𝕂 M) (ReedSolomon.code D deg) δ loss ≤
      ENNReal.ofReal (M * UniqueDecoding.lossyBound 1 c δ δ_int loss / Fintype.card 𝕂) := by
  have hc : 0 < c := Nat.pos_of_ne_zero fun h ↦ by
    rw [h, zero_mul] at hdeg
    exact (Nat.two_pow_pos m).ne' hdeg.symm
  have hdegpos : 0 < deg := Nat.pos_of_ne_zero fun h ↦ by
    rw [h, mul_zero] at hdeg
    exact (Nat.two_pow_pos m).ne' hdeg.symm
  have hrate : (deg : ℝ) / (Fintype.card (Fin (2 ^ m)) : ℝ) = ((1 : ℕ) : ℝ) / (c : ℕ) := by
    rw [Fintype.card_fin, ← hdeg, Nat.cast_mul, Nat.cast_one]
    have : (0 : ℝ) < deg := by exact_mod_cast hdegpos
    have : (0 : ℝ) < c := by exact_mod_cast hc
    field_simp
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have hlossy := UniqueDecoding.lossyMcaError_le (F := 𝕂) D deg M δ δ_int loss
    (by rw [hrate, Fintype.card_fin, Nat.cast_one]; push_cast; exact hδ) h_pos h_lt h_loss
  rwa [lossyBound_congr hrate] at hlossy

/-- A fold's error onto a domain of `2 ^ m` points, over `M + 1` words, at a radius `δ` that an MCA
bound `B` admits for its code: at most `B`'s count over `|𝕂|`, the loss only lowering it. -/
theorem mcaLevel_le (B : McaBound) (hB : B.Holds) {m : ℕ} (D : Fin (2 ^ m) ↪ 𝕂) (M deg : ℕ)
    (δq : ℚ) (δ loss : ℝ) (hδ : δ = δq) (h_loss : 0 ≤ loss)
    (hadm : B.admits (2 ^ m) deg δq) :
    lossyMcaError (univariatePowersGenerator 𝕂 M) (ReedSolomon.code D deg) δ loss ≤
      ENNReal.ofReal (B.count (2 ^ m) deg M δq / Fintype.card 𝕂) := by
  rw [hδ]
  exact (lossyMcaError_le_mcaError _ _ _ h_loss).trans (hB 𝕂 _ _ _ D δq hadm)

/-- `g` bounds the folds of `plan` at rate `1/c` over `K`, times `|K|`: for each fold by `2 ^ k`
onto `2 ^ m` points, batching `M` words besides the first, `g` is nonnegative and bounds the lossy
MCA error of the powers `1, z, …, z^M` for the code of rate `1/c` on every domain of `2 ^ m`
points. -/
def FoldBounds (K : Type) [Field K] [Fintype K] [DecidableEq K] [SampleableType K] (c : ℕ)
    (δ loss : ℝ) (g : ℕ × ℕ × Bool → ℝ) (plan : List (ℕ × ℕ × Bool)) : Prop :=
  ∀ f ∈ plan, 0 ≤ g f ∧ ∀ (D : Fin (2 ^ f.2.1) ↪ K) (deg : ℕ), c * deg = 2 ^ f.2.1 →
    lossyMcaError (univariatePowersGenerator K (Fri.Interaction.Schedule.foldWords f))
      (ReedSolomon.code D deg) δ loss ≤ ENNReal.ofReal (g f / Fintype.card K)

/-- `ofReal (x / K) + ofReal (y / K) = ofReal ((x + y) / K)` for `x, y ≥ 0`. -/
theorem ofReal_div_add_ofReal_div {x y : ℝ} (K : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hK : 0 < K) :
    ENNReal.ofReal (x / K) + ENNReal.ofReal (y / K) = ENNReal.ofReal ((x + y) / K) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]

/-- A fold by `2 ^ la` batches `2 ^ la - 1` words besides the first, and one more if it injects. -/
theorem foldWords_false (la m : ℕ) :
    Fri.Interaction.Schedule.foldWords (la, m, false) = 2 ^ la - 1 := rfl

theorem foldWords_true (la m : ℕ) : Fri.Interaction.Schedule.foldWords (la, m, true) = 2 ^ la :=
  Nat.sub_add_cancel Nat.one_le_two_pow

open Fri.Interaction Schedule in
/-- The folds' errors of Plonky3's schedule at any arity and rate `1/c` (`c d = 2 ^ logFinal`):
the sum over its folds of bounds `g` on each fold, over `|𝕂|`. -/
theorem foldError_schedule_le (c : ℕ) (a : ℕ) (ha : 0 < a) (d logFinal : ℕ)
    (hd : c * d = 2 ^ logFinal) (δ loss : ℝ) (g : ℕ × ℕ × Bool → ℝ) :
    ∀ (fuel n : ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂) (heights : List ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Fits logFinal n heights →
      FoldBounds 𝕂 c δ loss g (plonky3 a logFinal fuel n heights).folds →
      (plonky3 a logFinal fuel n heights).foldError d δ loss ω ≤
        ENNReal.ofReal (((plonky3 a logFinal fuel n heights).folds.map g).sum / Fintype.card 𝕂)
  | 0, n, ω, heights, hn, hfuel, hfit, _ => by
    rw [plonky3, foldError]
    exact bot_le
  | fuel + 1, n, ω, heights, hn, hfuel, hfit, hg => by
    by_cases hfin : n ≤ logFinal
    · rw [plonky3, ite_eq_left hfin, foldError]
      exact bot_le
    have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le a logFinal n heights
    -- one fold onto `2 ^ (n - la)` points, and the rest
    have hstep (la : ℕ) (hla1 : 1 ≤ la) (hla2 : la ≤ n - logFinal) (M : ℕ) (inj : Bool)
        (hM : M = foldWords (la, n - la, inj)) (h : List ℕ)
        (hf : Fits logFinal (n - la) h)
        (hg : FoldBounds 𝕂 c δ loss g
          ((la, n - la, inj) :: (plonky3 a logFinal fuel (n - la) h).folds)) :
        lossyMcaError (univariatePowersGenerator 𝕂 M)
            (ReedSolomon.code ((ω.subdomain la : Domain.SmoothCosetFftDomain (n - la) 𝕂) :
              Fin (2 ^ (n - la)) ↪ 𝕂) ((plonky3 a logFinal fuel (n - la) h).degree d))
            δ loss + (plonky3 a logFinal fuel (n - la) h).foldError d δ loss
              (ω.subdomain la) ≤
          ENNReal.ofReal ((((la, n - la, inj) :: (plonky3 a logFinal fuel (n - la) h).folds).map
            g).sum / Fintype.card 𝕂) := by
      have hdeg : c * (plonky3 a logFinal fuel (n - la) h).degree d = 2 ^ (n - la) := by
        rw [degree_plonky3 ha d fuel _ h (by omega) (by omega) hf, mul_left_comm, hd, ← pow_add]
        congr 1
        omega
      obtain ⟨hg0, hlevel⟩ := hg _ List.mem_cons_self
      have ih := foldError_schedule_le c a ha d logFinal hd δ loss g fuel (n - la)
        (ω.subdomain la) h (by omega) (by omega) hf fun f hf ↦ hg f (List.mem_cons_of_mem _ hf)
      refine (add_le_add (hM ▸ hlevel _ _ hdeg) ih).trans (le_of_eq ?_)
      rw [ofReal_div_add_ofReal_div _ hg0 (List.sum_nonneg fun x hx ↦ by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
        exact (hg f (List.mem_cons_of_mem _ hf)).1) hK]
      simp only [List.map_cons, List.sum_cons]
    rw [plonky3, ite_eq_right hfin] at hg ⊢
    match heights, hfit, h1, h2, hg with
    | [], hfit, h1, h2, hg =>
      simp only [foldError, roundError] at hg ⊢
      exact hstep _ h1 h2 _ false (foldWords_false _ _).symm [] (fits_nil _ _) hg
    | m :: rest, hfit, h1, h2, hg =>
      have h3 := logArity_le_cons a logFinal n m rest
      by_cases hm : m = n - logArity a logFinal n (m :: rest)
      · simp only [ite_eq_left hm, foldError, roundError] at hg ⊢
        exact hstep _ h1 h2 _ true (foldWords_true _ _).symm rest (fits_of_eq hfit hm) hg
      · simp only [ite_eq_right hm, foldError, roundError] at hg ⊢
        exact hstep _ h1 h2 _ false (foldWords_false _ _).symm _
          (fits_cons_of_ne hfit h3 hm) hg

/-! ### The terms of a setup -/

/-- The rate is `1 / 2 ^ logBlowup`. -/
theorem rate_eq (S : Setup EF lookups) : S.rate = 1 / 2 ^ S.params.logBlowup := by
  rw [Setup.rate, Setup.n, Setup.size, pow_add]
  push_cast
  field_simp

/-- With the candidate lists at `δ` of at most `ℓ` elements and the permutation trace's of at most
`ℓp`, the constraint-folding term is at most `ℓ ℓp (#constraints - 1)` over `|𝕂|`. -/
theorem foldingError_le_of_listSize (S : Setup EF lookups) (δ : ℝ≥0) (ℓ ℓp : ℕ)
    (hℓ : S.listSize (Fin S.air.width) δ ≤ ℓ) (hℓp : S.permListSize δ ≤ ℓp) :
    foldingError S δ ≤ (ℓ * ℓp * (S.numConstraints - 1) : ℕ) / (Fintype.card 𝕂 : ENNReal) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.mul_le_mul hℓ hℓp))) _

/-- With the candidate list of the committed words at `δ` of at most `ℓ` elements, the
out-of-domain term is at most `ℓ identityDegree + n + N` over `|𝕂|`. -/
theorem outOfDomainError_le_of_listSize (S : Setup EF lookups) (δ : ℝ≥0) (ℓ : ℕ)
    (hℓ : S.listSize S.Committed δ ≤ ℓ) :
    outOfDomainError S δ ≤
      (ℓ * S.identityDegree + S.n + S.size : ℕ) / (Fintype.card 𝕂 : ENNReal) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ hℓ) _) _)) _

/-- FRI's term at any arity and proximity loss: the sum of bounds `g` on its folds over `|𝕂|`
(`foldError_schedule_le`), and the queries `(1 - δ + #folds · loss) ^ numQueries`. -/
theorem friErrorWith_le (S : Setup EF lookups) (heights : List ℕ)
    (hfit : Fri.Interaction.Schedule.Fits (S.params.logFinalPolyLen + S.params.logBlowup)
      (S.logN + S.params.logBlowup) heights)
    (δ loss : ℝ≥0) (g : ℕ × ℕ × Bool → ℝ)
    (hg : FoldBounds 𝕂 (2 ^ S.params.logBlowup) δ loss g (S.friSchedule heights).folds) :
    friErrorWith S heights δ ≤
      ENNReal.ofReal (((S.friSchedule heights).folds.map g).sum / Fintype.card 𝕂) +
        ((Real.toNNReal (1 - δ + (S.friSchedule heights).folds.length * loss) ^
            S.params.numQueries : ℝ≥0) : ENNReal) := by
  have hf := S.valid.finalPolyFits
  refine (iInf_le _ loss).trans (add_le_add ?_ (le_of_eq ?_))
  · exact foldError_schedule_le (2 ^ S.params.logBlowup) _ S.valid.folds _ _
      (by rw [← pow_add, add_comm]) δ loss g _ _ S.domain heights (by omega) (Nat.sub_le _ _)
      hfit hg
  · rw [Fri.Interaction.Schedule.length_folds, ENNReal.coe_pow]
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
