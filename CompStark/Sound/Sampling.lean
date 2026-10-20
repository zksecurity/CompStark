/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.NonInteractiveError
public import Mathlib.Data.Int.CardIntervalMod

/-! # Low bits of uniform KoalaBear elements

`sampleBits b` keeps the residue `x mod 2 ^ b` of a sample's canonical value `x < p`, and a
grinding check passes when the residue of `bits` bits is zero. KoalaBear's `p = 127 · 2^24 + 1`,
so for `b ≤ 24` every nonzero residue has `127 · 2^(24 - b)` preimages and zero one more
(`card_val_mod_eq`). Hence:

* `prob_val_mod_mem_le`: a residue lands in a set `G` with probability at most
  `|G| / 2 ^ b + 1 / p`;
* `prob_val_mod_eq_zero_le`: `bits` low bits vanish with probability at most `powFraction bits`,
  for every `bits`.

The grinding sample and the challenge of a round come from one oracle answer, independent
coordinates: `prob_pow_and_le` multiplies the challenge's bad probability by `powFraction`, and
`prob_queryRound_le` bounds the query round, a grinding sample and `t` query samples whose
residues must all land in `G`.

The canonical value of a Montgomery element is that of its field element
(`FastField.toNat_eq_val_toField`), so these bounds hold for samples of the fast field.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Iop OracleComp

local notation "𝔽" => KoalaBear.Field

theorem fieldSize_eq : KoalaBear.fieldSize = 127 * 2 ^ 24 + 1 := by
  rw [KoalaBear.fieldSize]
  norm_num

/-- `p = |𝔽|`. -/
theorem card_field : Fintype.card 𝔽 = 127 * 2 ^ 24 + 1 := by
  rw [ZMod.card, fieldSize_eq]

/-- The elements whose canonical values satisfy `P` number the values below `p` satisfying `P`. -/
theorem card_filter_val (P : Nat → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : 𝔽 ↦ P x.val).card = Nat.count P (127 * 2 ^ 24 + 1) := by
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun x _ ↦ x.val) (fun x hx ↦ ?_) (fun x _ y _ h ↦ ZMod.val_injective _ h)
    fun n hn ↦ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fieldSize_eq ▸ ZMod.val_lt x, hx⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hn
    have hlt : n < KoalaBear.fieldSize := fieldSize_eq ▸ hn.1
    refine ⟨(n : 𝔽), by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ZMod.val_natCast_of_lt hlt, hn.2], ZMod.val_natCast_of_lt hlt⟩

/-- For `b ≤ 24`, a residue `r < 2 ^ b` has `127 · 2^(24 - b)` preimages, one more for `r = 0`. -/
theorem card_val_mod_eq (b : Nat) (hb : b ≤ 24) (r : Nat) (hr : r < 2 ^ b) :
    (Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ b = r).card =
      127 * 2 ^ (24 - b) + if r = 0 then 1 else 0 := by
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  have hsplit : 127 * 2 ^ 24 + 1 = 1 + 2 ^ b * (127 * 2 ^ (24 - b)) := by
    rw [Nat.mul_left_comm, ← pow_add, Nat.add_sub_cancel' hb, Nat.add_comm]
  have hcount : Nat.count (fun n ↦ n % 2 ^ b = r) (127 * 2 ^ 24 + 1) =
      Nat.count (· ≡ r [MOD 2 ^ b]) (127 * 2 ^ 24 + 1) := by
    congr 1
    funext n
    rw [Nat.ModEq, Nat.mod_eq_of_lt hr]
  rw [card_filter_val (fun n ↦ n % 2 ^ b = r), hcount, Nat.count_modEq_card _ hpos,
    Nat.mod_eq_of_lt hr, hsplit, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
  rcases Nat.lt_or_ge 1 (2 ^ b) with h1 | h1
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.zero_add]
    simp only [Nat.lt_one_iff]
  · have hb0 : 2 ^ b = 1 := by omega
    have hr0 : r = 0 := by omega
    simp only [hb0, Nat.div_one, Nat.mod_one, hr0, lt_self_iff_false, ↓reduceIte]
    omega

/-- At most `|G| · 127 · 2^(24 - b) + 1` elements have their residue mod `2 ^ b` in `G`. -/
theorem card_val_mod_mem_le (b : Nat) (hb : b ≤ 24) (G : Finset Nat) :
    (Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ b ∈ G).card ≤
      G.card * (127 * 2 ^ (24 - b)) + 1 := by
  classical
  set G' := G.filter (· < 2 ^ b)
  have hsub : (Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ b ∈ G) ⊆
      G'.biUnion fun r ↦ Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ b = r := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, G']
    exact ⟨_, ⟨hx, Nat.mod_lt _ (Nat.two_pow_pos b)⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hsum : ∑ r ∈ G', (Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ b = r).card =
      ∑ r ∈ G', (127 * 2 ^ (24 - b) + if r = 0 then 1 else 0) :=
    Finset.sum_congr rfl fun r hr ↦ card_val_mod_eq b hb r (Finset.mem_filter.mp hr).2
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite_eq']
  have hG' : G'.card ≤ G.card := Finset.card_filter_le _ _
  have hle : (if 0 ∈ G' then 1 else 0) ≤ 1 := by split_ifs <;> omega
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hG') hle

/-- At most `127 · 2^(24 - bits) + 1` elements have `bits` vanishing low bits, for every
`bits`. -/
theorem card_val_mod_eq_zero_le (bits : Nat) :
    (Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ bits = 0).card ≤ 127 * 2 ^ (24 - bits) + 1 := by
  rcases le_or_gt bits 24 with hb | hb
  · rw [card_val_mod_eq bits hb 0 (Nat.two_pow_pos bits)]
    simp only [↓reduceIte, le_refl]
  · have hcount : Nat.count (fun n ↦ n % 2 ^ bits = 0) (127 * 2 ^ 24 + 1) =
        Nat.count (· ≡ 0 [MOD 2 ^ bits]) (127 * 2 ^ 24 + 1) := by
      congr 1
    rw [card_filter_val (fun n ↦ n % 2 ^ bits = 0), hcount,
      Nat.count_modEq_card _ (Nat.two_pow_pos bits),
      Nat.sub_eq_zero_of_le hb.le, pow_zero, Nat.mul_one]
    have hdiv : (127 * 2 ^ 24 + 1) / 2 ^ bits ≤ 127 := by
      refine (Nat.div_le_div_left (Nat.pow_le_pow_right two_pos hb) (Nat.two_pow_pos _)).trans ?_
      norm_num
    split_ifs <;> omega

/-- `|𝔽|` as an extended real. -/
noncomputable abbrev card𝔽 : ENNReal := Fintype.card 𝔽

theorem card𝔽_ne_zero : card𝔽 ≠ 0 := by
  simp only [card𝔽, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]

theorem card𝔽_ne_top : card𝔽 ≠ ⊤ := ENNReal.natCast_ne_top _

/-- `127 · 2^(24 - b) / p ≤ 1 / 2 ^ b` for `b ≤ 24`: the preimages of one nonzero residue. -/
theorem preimages_div_le (b : Nat) (hb : b ≤ 24) :
    ((127 * 2 ^ (24 - b) : Nat) : ENNReal) / card𝔽 ≤ 1 / 2 ^ b := by
  rw [ENNReal.div_le_iff card𝔽_ne_zero card𝔽_ne_top, one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
  have h : 127 * 2 ^ (24 - b) * 2 ^ b ≤ Fintype.card 𝔽 := by
    rw [card_field, Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hb]
    omega
  exact_mod_cast h

/-- A uniform element's residue mod `2 ^ b`, `b ≤ 24`, lies in `G` with probability at most
`|G| / 2 ^ b + 1 / p`: `sampleBits`' bias. -/
theorem prob_val_mod_mem_le (b : Nat) (hb : b ≤ 24) (G : Finset Nat) :
    Pr{let x ← $ᵗ 𝔽}[x.val % 2 ^ b ∈ G] ≤ G.card / 2 ^ b + 1 / card𝔽 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  calc ((Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ b ∈ G).card : ENNReal) / card𝔽
      ≤ ((G.card * (127 * 2 ^ (24 - b)) + 1 : Nat) : ENNReal) / card𝔽 := by
        gcongr
        exact_mod_cast card_val_mod_mem_le b hb G
    _ = G.card * (((127 * 2 ^ (24 - b) : Nat) : ENNReal) / card𝔽) + 1 / card𝔽 := by
        rw [Nat.cast_add, ENNReal.add_div, Nat.cast_mul, mul_div_assoc, Nat.cast_one]
    _ ≤ G.card * (1 / 2 ^ b) + 1 / card𝔽 :=
        add_le_add_left (mul_le_mul_right (preimages_div_le b hb) _) _
    _ = G.card / 2 ^ b + 1 / card𝔽 := by rw [← mul_div_assoc, mul_one]

/-- `bits` low bits of a uniform element vanish with probability at most `powFraction bits`. -/
theorem prob_val_mod_eq_zero_le (bits : Nat) :
    Pr{let x ← $ᵗ 𝔽}[x.val % 2 ^ bits = 0] ≤ powFraction bits := by
  classical
  rw [SampleableType.prEvent_uniformSample, powFraction]
  gcongr
  exact_mod_cast card_val_mod_eq_zero_le bits

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
    Pr{let z ← $ᵗ (𝔽 × β)}[z.1.val % 2 ^ bits = 0 ∧ Q z.2] ≤
      powFraction bits * Pr{let y ← $ᵗ β}[Q y] := by
  classical
  rw [prob_prod_and (fun x : 𝔽 ↦ x.val % 2 ^ bits = 0) Q]
  gcongr
  exact prob_val_mod_eq_zero_le bits

/-- The query round: a grinding sample with `bits` vanishing low bits and `t` query samples whose
residues mod `2 ^ b` all lie in `G`, with `|G| ≤ 2 ^ b · c`, has probability at most
`powFraction bits · (c + 1/p) ^ t`. -/
theorem prob_queryRound_le (bits b t : Nat) (hb : b ≤ 24) (G : Finset Nat) (c : ℝ)
    (hG : (G.card : ℝ) ≤ 2 ^ b * c) :
    Pr{let z ← $ᵗ (𝔽 × (Fin t → 𝔽))}[z.1.val % 2 ^ bits = 0 ∧ ∀ j, (z.2 j).val % 2 ^ b ∈ G] ≤
      powFraction bits * ENNReal.ofReal (c + 1 / Fintype.card 𝔽) ^ t := by
  classical
  refine (prob_pow_and_le (β := Fin t → 𝔽) bits
    (fun xs ↦ ∀ j, (xs j).val % 2 ^ b ∈ G)).trans (mul_le_mul_right ?_ _)
  set A := Finset.univ.filter fun x : 𝔽 ↦ x.val % 2 ^ b ∈ G
  have hA : ∀ xs : Fin t → 𝔽, (∀ j, (xs j).val % 2 ^ b ∈ G) ↔ ∀ j, xs j ∈ A := fun xs ↦ by
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
  rw [ENNReal.ofReal_add hc (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
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
