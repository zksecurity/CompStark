/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.NonInteractiveError
public import Mathlib.Data.Int.CardIntervalMod

/-! # Low bits of uniform base elements

`sampleBits b` keeps the residue `x mod 2 ^ b` of a sample's canonical value `x < p`, `p = |F|`
(`CanonicalNat`, a bijection onto `[0, p)`), and a grinding check passes when the residue of `bits`
bits is zero. For `2 ^ b ∣ p - 1`, every nonzero residue has `(p - 1) / 2 ^ b` preimages and zero
one more (`card_val_mod_eq`). Hence:

* `prob_val_mod_mem_le`: for `2 ^ b ∣ p - 1`, a residue lands in a set `G` with probability at
  most `|G| / 2 ^ b + 1 / p`;
* `prob_val_mod_eq_zero_le`: `bits` low bits vanish with probability at most `powFraction bits`,
  the `(p - 1) / 2 ^ bits + 1` multiples of `2 ^ bits` below `p`, for every `bits`.

The grinding sample and the challenge of a round come from one oracle answer, independent
coordinates: `prob_pow_and_le` multiplies the challenge's bad probability by `powFraction`, and
`prob_queryRound_le` bounds the query round, a grinding sample and `t` query samples whose
residues must all land in `G`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Iop OracleComp CompPoly

/-- `|F|` as an extended real. -/
noncomputable abbrev cardF (F : Type) : ENNReal := Nat.card F

theorem cardF_ne_top (F : Type) : cardF F ≠ ⊤ := ENNReal.natCast_ne_top _

variable {F : Type} [BaseField F]

/-- The elements whose canonical values satisfy `P` number the values below `p` satisfying `P`. -/
theorem card_filter_val (P : Nat → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : F ↦ P (CanonicalNat.toNat x)).card =
      Nat.count P (Nat.card F) := by
  rw [Nat.count_eq_card_filter_range, Nat.card_eq_fintype_card, CanonicalNat.card_eq]
  refine Finset.card_bij (fun x _ ↦ CanonicalNat.toNat x) (fun x hx ↦ ?_)
    (fun x _ y _ h ↦ CanonicalNat.toNat_injective h) fun n hn ↦ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨CanonicalNat.toNat_lt x, hx⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨CanonicalNat.ofNat n, ?_, CanonicalNat.toNat_ofNat_of_lt hn.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, CanonicalNat.toNat_ofNat_of_lt hn.1,
      hn.2]

/-- The multiples of `m > 0` below `p > 0` number `(p - 1) / m + 1`. -/
theorem count_mod_eq_zero (m p : Nat) (hm : 0 < m) (hp : 0 < p) :
    Nat.count (fun n ↦ n % m = 0) p = (p - 1) / m + 1 := by
  have hcount : Nat.count (fun n ↦ n % m = 0) p = Nat.count (· ≡ 0 [MOD m]) p := by
    congr 1
  rw [hcount, Nat.count_modEq_card _ hm, Nat.zero_mod]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_div]
  by_cases hd : m ∣ q + 1
  · rw [ite_eq_left hd, ite_eq_right (by rw [Nat.mod_eq_zero_of_dvd hd]; omega)]
  · rw [ite_eq_right hd, ite_eq_left (Nat.pos_of_ne_zero fun h ↦ hd (Nat.dvd_of_mod_eq_zero h))]

/-- For `2 ^ b ∣ p - 1`, a residue `r < 2 ^ b` has `(p - 1) / 2 ^ b` preimages, one more for
`r = 0`. -/
theorem card_val_mod_eq (b : Nat) (hb : 2 ^ b ∣ Nat.card F - 1) (r : Nat) (hr : r < 2 ^ b) :
    (Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ b = r).card =
      (Nat.card F - 1) / 2 ^ b + if r = 0 then 1 else 0 := by
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  obtain ⟨k, hk⟩ := hb
  have hp : 0 < Nat.card F := Nat.card_pos
  have hsplit : Nat.card F = 1 + 2 ^ b * k := by omega
  have hcount : Nat.count (fun n ↦ n % 2 ^ b = r) (Nat.card F) =
      Nat.count (· ≡ r [MOD 2 ^ b]) (Nat.card F) := by
    congr 1
    funext n
    rw [Nat.ModEq, Nat.mod_eq_of_lt hr]
  rw [card_filter_val (fun n ↦ n % 2 ^ b = r), hcount, Nat.count_modEq_card _ hpos,
    Nat.mod_eq_of_lt hr, hk, Nat.mul_div_cancel_left _ hpos, hsplit,
    Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
  rcases Nat.lt_or_ge 1 (2 ^ b) with h1 | h1
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.zero_add]
    simp only [Nat.lt_one_iff]
  · have hb0 : 2 ^ b = 1 := by omega
    have hr0 : r = 0 := by omega
    simp only [hb0, Nat.div_one, Nat.mod_one, hr0, lt_self_iff_false, ↓reduceIte]
    omega

/-- For `2 ^ b ∣ p - 1`, at most `|G| · (p - 1) / 2 ^ b + 1` elements have their residue mod
`2 ^ b` in `G`. -/
theorem card_val_mod_mem_le (b : Nat) (hb : 2 ^ b ∣ Nat.card F - 1) (G : Finset Nat) :
    (Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ b ∈ G).card ≤
      G.card * ((Nat.card F - 1) / 2 ^ b) + 1 := by
  classical
  set G' := G.filter (· < 2 ^ b)
  have hsub : (Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ b ∈ G) ⊆
      G'.biUnion fun r ↦ Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ b = r := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, G']
    exact ⟨_, ⟨hx, Nat.mod_lt _ (Nat.two_pow_pos b)⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hsum : ∑ r ∈ G',
      (Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ b = r).card =
      ∑ r ∈ G', ((Nat.card F - 1) / 2 ^ b + if r = 0 then 1 else 0) :=
    Finset.sum_congr rfl fun r hr ↦ card_val_mod_eq b hb r (Finset.mem_filter.mp hr).2
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite_eq']
  have hG' : G'.card ≤ G.card := Finset.card_filter_le _ _
  have hle : (if 0 ∈ G' then 1 else 0) ≤ 1 := by split_ifs <;> omega
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hG') hle

/-- `(p - 1) / 2 ^ bits + 1` elements have `bits` vanishing low bits, for every `bits`. -/
theorem card_val_mod_eq_zero (bits : Nat) :
    (Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ bits = 0).card =
      (Nat.card F - 1) / 2 ^ bits + 1 := by
  rw [card_filter_val (fun n ↦ n % 2 ^ bits = 0)]
  exact count_mod_eq_zero _ _ (Nat.two_pow_pos bits) Nat.card_pos

theorem cardF_ne_zero : cardF F ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'


/-- `((p - 1) / 2 ^ b) / p ≤ 1 / 2 ^ b`: the preimages of one nonzero residue. -/
theorem preimages_div_le (b : Nat) :
    (((Nat.card F - 1) / 2 ^ b : Nat) : ENNReal) / cardF F ≤ 1 / 2 ^ b := by
  rw [ENNReal.div_le_iff cardF_ne_zero (cardF_ne_top F), one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
  have h : (Nat.card F - 1) / 2 ^ b * 2 ^ b ≤ Nat.card F :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  exact_mod_cast h

/-- For `2 ^ b ∣ p - 1`, a uniform element's residue mod `2 ^ b` lies in `G` with probability at
most `|G| / 2 ^ b + 1 / p`: `sampleBits`' bias. -/
theorem prob_val_mod_mem_le (b : Nat) (hb : 2 ^ b ∣ Nat.card F - 1) (G : Finset Nat) :
    Pr{let x ← $ᵗ F}[CanonicalNat.toNat x % 2 ^ b ∈ G] ≤ G.card / 2 ^ b + 1 / cardF F := by
  classical
  rw [SampleableType.prEvent_uniformSample, ← Nat.card_eq_fintype_card]
  calc ((Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ b ∈ G).card : ENNReal) /
        cardF F
      ≤ ((G.card * ((Nat.card F - 1) / 2 ^ b) + 1 : Nat) : ENNReal) / cardF F := by
        gcongr
        exact_mod_cast card_val_mod_mem_le b hb G
    _ = G.card * ((((Nat.card F - 1) / 2 ^ b : Nat) : ENNReal) / cardF F) + 1 / cardF F := by
        rw [Nat.cast_add, ENNReal.add_div, Nat.cast_mul, mul_div_assoc, Nat.cast_one]
    _ ≤ G.card * (1 / 2 ^ b) + 1 / cardF F :=
        add_le_add_left (mul_le_mul_right (preimages_div_le b) _) _
    _ = G.card / 2 ^ b + 1 / cardF F := by rw [← mul_div_assoc, mul_one]

/-- `bits` low bits of a uniform element vanish with probability at most `powFraction bits`. -/
theorem prob_val_mod_eq_zero_le (bits : Nat) :
    Pr{let x ← $ᵗ F}[CanonicalNat.toNat x % 2 ^ bits = 0] ≤ powFraction F bits := by
  classical
  rw [SampleableType.prEvent_uniformSample, powFraction, card_val_mod_eq_zero,
    Nat.card_eq_fintype_card]

/-- No grinding: a proof-of-work sample of `0` bits always vanishes. -/
theorem powFraction_zero : powFraction F 0 = 1 := by
  have hp : 0 < Nat.card F := Nat.card_pos
  rw [powFraction, pow_zero, Nat.div_one, Nat.sub_add_cancel hp]
  exact ENNReal.div_self (by simp only [ne_eq, Nat.cast_eq_zero]; omega) (ENNReal.natCast_ne_top _)

/-- An event on a uniform pair of independent coordinates, `P` on the first and `Q` on the second,
has the product of their probabilities. -/
theorem prob_prod_and {α β : Type} [Fintype α] [Fintype β] [SampleableType α]
    [SampleableType β] (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q] :
    Pr{let z ← $ᵗ (α × β)}[P z.1 ∧ Q z.2] = Pr{let x ← $ᵗ α}[P x] * Pr{let y ← $ᵗ β}[Q y] := by
  classical
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample]
  have hfilter : (Finset.univ.filter fun z : α × β ↦ P z.1 ∧ Q z.2) =
      (Finset.univ.filter P) ×ˢ (Finset.univ.filter Q) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [hfilter, Finset.card_product, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_div_mul_comm (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- A grinding sample with `bits` vanishing low bits and an event `Q` on the challenge drawn in
the same answer: at most `powFraction bits` times the probability of `Q`. -/
theorem prob_pow_and_le {β : Type} [Fintype β] [SampleableType β] (bits : Nat) (Q : β → Prop)
    [DecidablePred Q] :
    Pr{let z ← $ᵗ (F × β)}[CanonicalNat.toNat z.1 % 2 ^ bits = 0 ∧ Q z.2] ≤
      powFraction F bits * Pr{let y ← $ᵗ β}[Q y] := by
  classical
  rw [prob_prod_and (fun x : F ↦ CanonicalNat.toNat x % 2 ^ bits = 0) Q]
  gcongr
  exact prob_val_mod_eq_zero_le bits

/-- The query round: a grinding sample with `bits` vanishing low bits and `t` query samples whose
residues mod `2 ^ b` all lie in `G`, with `|G| ≤ 2 ^ b · c` and `2 ^ b ∣ p - 1`, has probability
at most `powFraction bits · (c + 1/p) ^ t`. -/
theorem prob_queryRound_le (bits b t : Nat) (hb : 2 ^ b ∣ Nat.card F - 1) (G : Finset Nat)
    (c : ℝ) (hG : (G.card : ℝ) ≤ 2 ^ b * c) :
    Pr{let z ← $ᵗ (F × (Fin t → F))}[CanonicalNat.toNat z.1 % 2 ^ bits = 0 ∧
        ∀ j, CanonicalNat.toNat (z.2 j) % 2 ^ b ∈ G] ≤
      powFraction F bits * ENNReal.ofReal (c + 1 / Nat.card F) ^ t := by
  classical
  refine (prob_pow_and_le (β := Fin t → F) bits
    (fun xs ↦ ∀ j, CanonicalNat.toNat (xs j) % 2 ^ b ∈ G)).trans (mul_le_mul_right ?_ _)
  set A := Finset.univ.filter fun x : F ↦ CanonicalNat.toNat x % 2 ^ b ∈ G
  have hA : ∀ xs : Fin t → F, (∀ j, CanonicalNat.toNat (xs j) % 2 ^ b ∈ G) ↔ ∀ j, xs j ∈ A :=
    fun xs ↦ by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [hA]
  rw [Probability.prob_uniform_pi_mem_finset_eq]
  gcongr
  have h := prob_val_mod_mem_le b hb G
  rw [SampleableType.prEvent_uniformSample] at h
  refine h.trans ?_
  have hc : 0 ≤ c := by
    have : (0 : ℝ) ≤ 2 ^ b * c := (Nat.cast_nonneg _).trans hG
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 2 ^ b)
  rw [ENNReal.ofReal_add hc (by positivity),
    ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr Nat.card_pos),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  gcongr
  have hdiv : (G.card : ℝ) / 2 ^ b ≤ c := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc (G.card : ENNReal) / 2 ^ b = ENNReal.ofReal ((G.card : ℝ) / 2 ^ b) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hdiv

end CompStark.Sound
