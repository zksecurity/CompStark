/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Stark
public import CompStark.Interaction.BatchStateRestoration
public import CompStark.Ni.BatchRounds
public import CompStark.Ni.BatchLengths

/-! # The batch STARK's challenges as Plonky3's duplex challenger draws them

Plonky3's batch verifier (`verifyInstancesWith`) draws the batch's challenges from its duplex
challenger with `K` samples per squeeze (`Draws.lean`): the lookup challenges `(α_L, β_L)`, if some
instance has lookups, from the first squeeze after the batch's domain separator, every instance's
degree bits, the main trace, the public values and the lookup grinding witness, both from one
squeeze's samples; `α` after the permutation trace and the terminals; `ζ` after the quotients and
the out-of-domain grinding witness; the batching challenge after the PCS's domain separator, the
claimed values and the batching witness; FRI's challenges as in the STARK (`friDecoder`). Without
lookups, Plonky3 neither squeezes nor observes a witness at the lookup challenges, which are
`(0, 0)`. Here the commitments are the oracle messages themselves: a committed word is observed
in full where Plonky3 observes its Merkle cap, and the preprocessed commitment, part of the
statement, is not observed. The terminals are those of the instances with lookups, observed in
instance order after the permutation trace (`terminalsElems`), as Plonky3 observes them. The public
values are observed last before the first squeeze: with lookups before the lookup challenges, and
without lookups, where there are no terminals and the permutation trace is empty, before `α`.

* `pairDraw`, `lookupDraw`: the lookup challenges, two extension elements after a grinding sample,
  or `(0, 0)` without lookups, bounded by `powFraction F bits` (`bounded_pairDraw`) or by
  `|𝕂| ^ 2` (`bounded_lookupDraw`);
* `Setup.decoder`, `Statement.decoder`: the draws at every challenge;
* `Setup.ratio`, `Statement.ratio`: the draws' ratios, bounding the draws
  (`Statement.bounded_decoder`);
* `Setup.observer`, `Statement.observer`: what the verifier observes and how often it squeezes,
  which tell the keys apart (`Statement.observer_prefixFree`, the degree bits telling the admitted
  lengths apart on every base field) and are never empty (`Statement.observer_fills`);
* `Statement.tail`: the public values, flattened in instance order, the statement's elements,
  injective on the public values of the lengths the verifier checks (`Statement.tail_injective`);
* `Statement.coinCount`: the squeezes of the most demanding challenge, the coins' size.
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Sound CompStark.Iop CompStark.Ni OracleComp OracleSpec CompPoly
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

local notation "𝕂" => Challenge.Spec EF

/-! ### The lookup challenges -/

/-- Two extension elements from `2 d` samples, the first `d` first. -/
noncomputable def pairEquiv : (Fin (Challenge.d EF + Challenge.d EF) → F) ≃ 𝕂 × 𝕂 :=
  ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)).trans (Equiv.prodCongr extEquiv extEquiv)

theorem pairEquiv_apply (x : Fin (Challenge.d EF + Challenge.d EF) → F) :
    pairEquiv x = (extEquiv fun j ↦ x (Fin.castAdd _ j), extEquiv fun j ↦ x (Fin.natAdd _ j)) :=
  rfl

/-- The lookup challenges `(α_L, β_L)` drawn with `bits` bits of grinding: two extension
elements from consecutive samples, after a grinding sample with `bits` vanishing low bits if
`bits ≠ 0` (Plonky3's `check_witness` then two `sample_ext`), with no witness at `bits = 0`. -/
noncomputable def pairDraw : ℕ → Draw (Coins F K m) (𝕂 × 𝕂)
  | 0 => Draw.plain fun c ↦ (extOf c 0, extOf c (0 + Challenge.d EF))
  | bits + 1 => Draw.grind F (bits + 1) powSample fun c ↦ (extOf c 1, extOf c (1 + Challenge.d EF))

/-- The samples the lookup challenges with `bits` bits of grinding read. -/
def pairSamples (bits : ℕ) : ℕ := 2 * Challenge.d EF + if bits = 0 then 0 else 1

/-- The lookup challenges as Plonky3 draws them: with lookups, `pairDraw bits`; without, no
squeeze, no witness and `(0, 0)`. -/
noncomputable def lookupDraw : Bool → ℕ → Draw (Coins F K m) (𝕂 × 𝕂)
  | true, bits => pairDraw bits
  | false, _ => Draw.plain fun _ ↦ (0, 0)

/-- The squeezes of the lookup challenges: those of their samples with lookups, none without. -/
def lookupSqueezes (K : ℕ) : Bool → ℕ → ℕ
  | true, bits => squeezesFor K (pairSamples (EF := EF) bits)
  | false, _ => 0

/-- The grinding witness of the lookup challenges, observed if they grind. -/
def lookupWitnessElems :
    (b : Bool) → (bits : ℕ) → (lookupDraw (F := F) (EF := EF) (K := K) (m := m) b bits).Witness →
      List F
  | true, 0, _ => []
  | true, _ + 1, w => [w]
  | false, _, _ => []

variable (F EF) in
/-- The ratio of the lookup challenges: the grinding's `powFraction F bits` with lookups;
`|𝕂| ^ 2` without, as the constant `(0, 0)` hits an event only if a uniform pair does with
probability at least `1 / |𝕂| ^ 2`. -/
noncomputable def lookupRatio : Bool → ℕ → ℝ≥0∞
  | true, bits => Iop.powFraction F bits
  | false, _ => (Fintype.card 𝕂 : ℝ≥0∞) ^ 2

/-- The lookup challenges with `bits` bits of grinding are bounded by `powFraction F bits` against
the uniform law, when their samples fit the coins. -/
theorem bounded_pairDraw (bits : ℕ) (hs : pairSamples (EF := EF) bits ≤ m * K) :
    (pairDraw (F := F) (EF := EF) (K := K) (m := m) bits).Bounded ($ᵗ (𝕂 × 𝕂))
      (Iop.powFraction F bits) := by
  classical
  cases bits with
  | zero =>
    have hd : Challenge.d EF + Challenge.d EF ≤ m * K := by
      simp only [pairSamples, ↓reduceIte, Nat.add_zero] at hs
      omega
    rw [Sound.powFraction_zero, pairDraw]
    refine Draw.Bounded.plain fun E ↦ ?_
    rw [one_mul]
    refine le_of_eq ?_
    calc _ = Pr{let c ← $ᵗ (Coins F K m)}[(fun x ↦ E (pairEquiv x)) fun j ↦ sampleAt c j] :=
          prEvent_congr_iff _ fun c ↦ by
            simp only [pairEquiv_apply, extOf, Fin.val_castAdd, Fin.val_natAdd, Nat.zero_add]
      _ = _ := (prob_samples hd _).trans (SampleableType.prEvent_uniformSample_equiv pairEquiv E)
  | succ b =>
    have hd : Challenge.d EF + Challenge.d EF + 1 ≤ m * K := by
      simp only [pairSamples, Nat.add_one_ne_zero, ↓reduceIte] at hs
      omega
    intro E
    simp only [pairDraw, Draw.grind, beq_iff_eq]
    let e : (Fin (Challenge.d EF + Challenge.d EF + 1) → F) ≃ F × (𝕂 × 𝕂) :=
      (Fin.consEquiv fun _ ↦ F).symm.trans (Equiv.prodCongr (Equiv.refl F) pairEquiv)
    calc _ = Pr{let c ← $ᵗ (Coins F K m)}[(fun x ↦
          CanonicalNat.toNat (e x).1 % 2 ^ (b + 1) = 0 ∧ E (e x).2) fun j ↦ sampleAt c j] :=
          prEvent_congr_iff _ fun c ↦ by
            have hp : (extOf c 1, extOf c (1 + Challenge.d EF)) =
                (e fun j ↦ sampleAt c j).2 := by
              simp only [e, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
                pairEquiv_apply, Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail, extOf]
              refine Prod.ext (congrArg extEquiv (funext fun j ↦ congrArg (sampleAt c) ?_))
                (congrArg extEquiv (funext fun j ↦ congrArg (sampleAt c) ?_))
              · simp only [Fin.val_succ, Fin.val_castAdd]
                omega
              · simp only [Fin.val_succ, Fin.val_natAdd]
                omega
            rw [hp]
            rfl
      _ = Pr{let z ← $ᵗ (F × (𝕂 × 𝕂))}[CanonicalNat.toNat z.1 % 2 ^ (b + 1) = 0 ∧ E z.2] :=
          (prob_samples hd _).trans (SampleableType.prEvent_uniformSample_equiv e
            (fun z ↦ CanonicalNat.toNat z.1 % 2 ^ (b + 1) = 0 ∧ E z.2))
      _ ≤ _ := prob_pow_and_le (b + 1) E

/-- The lookup challenges are bounded by their ratio against the uniform law, when their samples
fit the coins. -/
theorem bounded_lookupDraw (b : Bool) (bits : ℕ) (hs : pairSamples (EF := EF) bits ≤ m * K) :
    (lookupDraw (F := F) (EF := EF) (K := K) (m := m) b bits).Bounded ($ᵗ (𝕂 × 𝕂))
      (lookupRatio F EF b bits) := by
  classical
  cases b with
  | true => exact bounded_pairDraw bits hs
  | false =>
    refine Draw.Bounded.plain fun E ↦ ?_
    show _ ≤ (Fintype.card 𝕂 : ℝ≥0∞) ^ 2 * _
    by_cases hE : E (0, 0)
    · refine (prEvent_le_one _).trans ?_
      rw [SampleableType.prEvent_uniformSample, Fintype.card_prod, Nat.cast_mul, ← sq]
      have hc : (Fintype.card 𝕂 : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero _ (by simp)
      have hc' : (Fintype.card 𝕂 : ℝ≥0∞) ^ 2 ≠ ⊤ := by simp
      have h1 : (1 : ℝ≥0∞) ≤ (Finset.univ.filter E).card :=
        Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨(0, 0), by simp only [Finset.mem_filter,
          Finset.mem_univ, true_and, hE]⟩)
      calc (1 : ℝ≥0∞) = (Fintype.card 𝕂 : ℝ≥0∞) ^ 2 * (1 / (Fintype.card 𝕂 : ℝ≥0∞) ^ 2) := by
            rw [one_div, ENNReal.mul_inv_cancel hc hc']
        _ ≤ _ := by
            gcongr
    · have h0 : Pr{let c ← $ᵗ (Coins F K m)}[E (0, 0)] = 0 :=
        prEvent_eq_zero_of_forall_not _ _ fun _ ↦ hE
      rw [h0]
      exact bot_le

/-- The lookup challenges with `bits` bits of grinding read only the squeezes of their
samples. -/
theorem reads_pairDraw (hK : 0 < K) (bits : ℕ) (c c' : Coins F K m)
    (h : ∀ j : Fin m, (j : ℕ) < squeezesFor K (pairSamples (EF := EF) bits) → c j = c' j) :
    (pairDraw (EF := EF) bits).accept c = (pairDraw (EF := EF) bits).accept c' ∧
      (pairDraw (EF := EF) bits).decode c = (pairDraw (EF := EF) bits).decode c' := by
  have hs (i : ℕ) (hi : i < pairSamples (EF := EF) bits) : sampleAt c i = sampleAt c' i :=
    reads_sampleAt hK h hi
  cases bits with
  | zero =>
    refine ⟨rfl, ?_⟩
    simp only [pairDraw, Draw.plain, extOf]
    refine Prod.ext (congrArg extEquiv (funext fun j ↦ hs _ ?_))
      (congrArg extEquiv (funext fun j ↦ hs _ ?_)) <;>
    · have := j.isLt
      simp only [pairSamples, ↓reduceIte]
      omega
  | succ b =>
    simp only [pairDraw, Draw.grind, powSample, extOf]
    refine ⟨by rw [hs 0 (by simp only [pairSamples, Nat.add_one_ne_zero, ↓reduceIte]; omega)],
      Prod.ext (congrArg extEquiv (funext fun j ↦ hs _ ?_))
        (congrArg extEquiv (funext fun j ↦ hs _ ?_))⟩ <;>
    · have := j.isLt
      simp only [pairSamples, Nat.add_one_ne_zero, ↓reduceIte]
      omega

/-- The lookup challenges read only the squeezes they take. -/
theorem reads_lookupDraw (hK : 0 < K) (b : Bool) (bits : ℕ) (c c' : Coins F K m)
    (h : ∀ j : Fin m, (j : ℕ) < lookupSqueezes (EF := EF) K b bits → c j = c' j) :
    (lookupDraw (EF := EF) b bits).accept c = (lookupDraw (EF := EF) b bits).accept c' ∧
      (lookupDraw (EF := EF) b bits).decode c = (lookupDraw (EF := EF) b bits).decode c' := by
  cases b with
  | true => exact reads_pairDraw hK bits c c' h
  | false => exact ⟨rfl, rfl⟩

theorem lookupWitnessElems_injective (b : Bool) (bits : ℕ) :
    Function.Injective (lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) b bits) := by
  cases b with
  | false => exact fun _ _ _ ↦ rfl
  | true =>
    cases bits with
    | zero => exact fun _ _ _ ↦ rfl
    | succ _ => exact fun x y h ↦ (List.cons.inj (show ([x] : List F) = [y] from h)).1

theorem length_lookupWitnessElems (b : Bool) (bits : ℕ) (w w') :
    (lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) b bits w).length =
      (lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) b bits w').length := by
  cases b <;> cases bits <;> rfl

/-- The lookup challenges' witness observation is prefix-free and suffix-free. -/
theorem fixFree_lookupWitnessElems (b : Bool) (bits : ℕ) :
    PrefixFree (lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) b bits) ∧
      SuffixFree (lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) b bits) :=
  ⟨prefixFree_of_length (lookupWitnessElems_injective b bits) (length_lookupWitnessElems b bits),
    suffixFree_of_length (lookupWitnessElems_injective b bits) (length_lookupWitnessElems b bits)⟩

theorem pairSamples_le (bits : ℕ) : pairSamples (EF := EF) bits ≤ 2 * Challenge.d EF + 1 := by
  simp only [pairSamples]
  split <;> omega

/-- The lookup challenges squeeze at most as often as `s` samples take, when their samples are at
most `s`. -/
theorem lookupSqueezes_le (b : Bool) (bits : ℕ) {s : ℕ} (h : pairSamples (EF := EF) bits ≤ s) :
    lookupSqueezes (EF := EF) K b bits ≤ squeezesFor K s := by
  cases b with
  | true => exact squeezesFor_mono h
  | false => exact Nat.zero_le _

/-! ### Blocks over the instances -/

omit [BaseField F] in
/-- Blocks over the instances, each of a length fixed by its instance, concatenate to equal lists
only if every block is equal. -/
theorem eq_of_flatMap_finRange_eq {k : ℕ} {β : Fin k → Type} {g : (i : Fin k) → β i → List F}
    {x y : (i : Fin k) → β i} (hl : ∀ i, (g i (x i)).length = (g i (y i)).length)
    (h : (List.finRange k).flatMap (fun i ↦ g i (x i)) =
      (List.finRange k).flatMap (fun i ↦ g i (y i))) (i : Fin k) : g i (x i) = g i (y i) := by
  have key : ∀ l : List (Fin k), l.flatMap (fun i ↦ g i (x i)) = l.flatMap (fun i ↦ g i (y i)) →
      ∀ i ∈ l, g i (x i) = g i (y i) := by
    intro l
    induction l with
    | nil => exact fun _ i hi ↦ absurd hi List.not_mem_nil
    | cons j l ih =>
      intro hl' i hi
      simp only [List.flatMap_cons] at hl'
      obtain ⟨h1, h2⟩ := List.append_inj hl' (hl j)
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h1
      · exact ih h2 i hi
  exact key _ h i (List.mem_finRange i)

omit [BaseField F] in
theorem length_flatMap_finRange_eq {k : ℕ} {β : Fin k → Type} {g : (i : Fin k) → β i → List F}
    {x y : (i : Fin k) → β i} (hl : ∀ i, (g i (x i)).length = (g i (y i)).length) :
    ((List.finRange k).flatMap (fun i ↦ g i (x i))).length =
      ((List.finRange k).flatMap (fun i ↦ g i (y i))).length := by
  rw [List.length_flatMap, List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left fun i _ ↦ hl i)

theorem length_flattenExts {n k : ℕ} (q : Fin n → Fin k → 𝕂) :
    ((List.ofFn fun c ↦ extsElems (F := F) (q c)).flatten).length = n * (k * Challenge.d EF) := by
  rw [Iop.Setup.flatten_ofFn_extsElems, length_flatMap_const length_extsElems, List.length_ofFn]

theorem flattenExts_injective {n k : ℕ} :
    Function.Injective fun q : Fin n → Fin k → 𝕂 ↦
      (List.ofFn fun c ↦ extsElems (F := F) (q c)).flatten := fun q q' h ↦ by
  simp only [Iop.Setup.flatten_ofFn_extsElems] at h
  exact List.ofFn_injective (flatMap_inj length_extsElems extsElems_injective _ _
    (by simp only [List.length_ofFn]) h)

end CompStark.Fs

/-! ### The batch at its lengths -/

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Sound CompStark.Fs CompStark.Ni
open Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
variable (K m : ℕ) (S : Setup EF)

local notation "𝕂" => Challenge.Spec EF

section Openings
variable {lookups : List (Stark.Lookup F)} {T : Iop.Setup EF lookups}

/-- An instance's trace values as Plonky3 observes them: at `ζ` and `ζ ω`. -/
noncomputable def traceElems (o : Openings T) : List F :=
  extsElems o.traceAt ++ extsElems o.traceNext

/-- An instance's quotient chunks as Plonky3 observes them: each chunk's coordinates. -/
noncomputable def quotientElems (o : Openings T) : List F :=
  (List.ofFn fun c ↦ extsElems (o.quotientAt c)).flatten

/-- An instance's preprocessed values as Plonky3 observes them: at `ζ` and `ζ ω`. -/
noncomputable def preprocessedElems (o : Openings T) : List F :=
  extsElems o.preprocessedAt ++ extsElems o.preprocessedNext

/-- An instance's permutation values as Plonky3 observes them: each column's coordinates at `ζ`,
then at `ζ ω`. -/
noncomputable def permElems (o : Openings T) : List F :=
  (List.ofFn fun c ↦ extsElems (o.permAt c)).flatten ++
    (List.ofFn fun c ↦ extsElems (o.permNext c)).flatten

theorem openings_ext {o o' : Openings T} (h1 : o.traceAt = o'.traceAt)
    (h2 : o.traceNext = o'.traceNext) (h3 : o.quotientAt = o'.quotientAt)
    (h4 : o.preprocessedAt = o'.preprocessedAt) (h5 : o.preprocessedNext = o'.preprocessedNext)
    (h6 : o.permAt = o'.permAt) (h7 : o.permNext = o'.permNext) : o = o' := by
  cases o
  cases o'
  simp only [Openings.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem length_traceElems (o o' : Openings T) :
    (traceElems (F := F) o).length = (traceElems o').length := by
  simp only [traceElems, List.length_append, length_extsElems]

theorem length_quotientElems (o o' : Openings T) :
    (quotientElems (F := F) o).length = (quotientElems o').length := by
  simp only [quotientElems, length_flattenExts]

theorem length_preprocessedElems (o o' : Openings T) :
    (preprocessedElems (F := F) o).length = (preprocessedElems o').length := by
  simp only [preprocessedElems, List.length_append, length_extsElems]

theorem length_permElems (o o' : Openings T) :
    (permElems (F := F) o).length = (permElems o').length := by
  simp only [permElems, List.length_append, length_flattenExts]

end Openings

/-- The claimed values as Plonky3's PCS observes them on the batch's rounds
(`Ni.roundValues_batchRounds_eq`): every instance's trace values, every instance's quotient
chunks, every instance's preprocessed values, every instance's permutation values. -/
noncomputable def openingsElems (o : S.OpeningsMessage) : List F :=
  (List.finRange S.k).flatMap (fun i ↦ traceElems (o i)) ++
    (List.finRange S.k).flatMap (fun i ↦ quotientElems (o i)) ++
    (List.finRange S.k).flatMap (fun i ↦ preprocessedElems (o i)) ++
    (List.finRange S.k).flatMap (fun i ↦ permElems (o i))

theorem length_openingsElems (o o' : S.OpeningsMessage) :
    (S.openingsElems (F := F) o).length = (S.openingsElems o').length := by
  simp only [openingsElems, List.length_append,
    length_flatMap_finRange_eq (g := fun i (x : Openings (S.instanceSetup i)) ↦ traceElems x)
      (x := o) (y := o') fun i ↦ length_traceElems _ _,
    length_flatMap_finRange_eq (g := fun i (x : Openings (S.instanceSetup i)) ↦ quotientElems x)
      (x := o) (y := o') fun i ↦ length_quotientElems _ _,
    length_flatMap_finRange_eq
      (g := fun i (x : Openings (S.instanceSetup i)) ↦ preprocessedElems x)
      (x := o) (y := o') fun i ↦ length_preprocessedElems _ _,
    length_flatMap_finRange_eq (g := fun i (x : Openings (S.instanceSetup i)) ↦ permElems x)
      (x := o) (y := o') fun i ↦ length_permElems _ _]

theorem openingsElems_injective : Function.Injective (S.openingsElems (F := F)) := by
  intro o o' h
  have hA := length_flatMap_finRange_eq
    (g := fun i (x : Openings (S.instanceSetup i)) ↦ traceElems (F := F) x)
    (x := o) (y := o') fun i ↦ length_traceElems _ _
  have hB := length_flatMap_finRange_eq
    (g := fun i (x : Openings (S.instanceSetup i)) ↦ quotientElems (F := F) x)
    (x := o) (y := o') fun i ↦ length_quotientElems _ _
  have hC := length_flatMap_finRange_eq
    (g := fun i (x : Openings (S.instanceSetup i)) ↦ preprocessedElems (F := F) x)
    (x := o) (y := o') fun i ↦ length_preprocessedElems _ _
  simp only [openingsElems] at h
  obtain ⟨h, hD⟩ := List.append_inj h (by simp only [List.length_append, hA, hB, hC])
  obtain ⟨h, hC'⟩ := List.append_inj h (by simp only [List.length_append, hA, hB])
  obtain ⟨hA', hB'⟩ := List.append_inj h hA
  funext i
  have ht := eq_of_flatMap_finRange_eq (g := fun i (x : Openings (S.instanceSetup i)) ↦
    traceElems (F := F) x) (fun i ↦ length_traceElems _ _) hA' i
  have hq := eq_of_flatMap_finRange_eq (g := fun i (x : Openings (S.instanceSetup i)) ↦
    quotientElems (F := F) x) (fun i ↦ length_quotientElems _ _) hB' i
  have hp := eq_of_flatMap_finRange_eq (g := fun i (x : Openings (S.instanceSetup i)) ↦
    preprocessedElems (F := F) x) (fun i ↦ length_preprocessedElems _ _) hC' i
  have hr := eq_of_flatMap_finRange_eq (g := fun i (x : Openings (S.instanceSetup i)) ↦
    permElems (F := F) x) (fun i ↦ length_permElems _ _) hD i
  simp only [traceElems, preprocessedElems, permElems] at ht hp hr
  obtain ⟨ht1, ht2⟩ := List.append_inj ht (by simp only [length_extsElems])
  obtain ⟨hp1, hp2⟩ := List.append_inj hp (by simp only [length_extsElems])
  obtain ⟨hr1, hr2⟩ := List.append_inj hr (by simp only [length_flattenExts])
  exact openings_ext (extsElems_injective ht1) (extsElems_injective ht2)
    (flattenExts_injective hq) (extsElems_injective hp1) (extsElems_injective hp2)
    (flattenExts_injective hr1) (flattenExts_injective hr2)

/-- FRI on the batch, on the tallest domain through the shorter domains' sizes. -/
noncomputable abbrev friDecoderB : Decoder (Coins F K m)
    (Fri.Interaction.publicCoin 𝕂 (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries
      (S.domainSetup.friSchedule S.friHeights)) :=
  friDecoder K m (S.logN S.top + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
    S.params.numQueries S.params.commitPowBits S.params.queryPowBits
    (S.domainSetup.friSchedule S.friHeights)

/-- The batch's draws: the lookup challenges, `α` without grinding, `ζ`, the batching challenge,
FRI's. -/
noncomputable def decoder : Decoder (Coins F K m) S.publicCoin :=
  (lookupDraw S.hasLookups S.params.lookupPowBits, fun _ ↦ (extDraw 0,
    (extDraw S.params.oodPowBits, fun _ ↦ (extDraw S.params.batchPowBits, S.friDecoderB K m))))

/-- The terminals as Plonky3 observes them: those of the instances with lookups, in instance
order. -/
noncomputable def terminalsElems (τ : S.Terminals) : List F :=
  extsElems (τ ∘ S.lookupInstances.orderIsoOfFin rfl)

/-- The observed terminals tell the terminals apart. -/
theorem terminalsElems_injective : Function.Injective (S.terminalsElems (F := F)) :=
  extsElems_injective.comp (S.lookupInstances.orderIsoOfFin rfl).surjective.injective_comp_right

/-- The observed terminals are `d` elements per instance with lookups. -/
theorem length_terminalsElems (τ : S.Terminals) :
    (S.terminalsElems (F := F) τ).length = S.lookupInstances.card * Challenge.d EF :=
  length_extsElems _

/-- With lookups, the terminals are observed: some instance has lookups. -/
theorem terminalsElems_ne_nil (hl : S.hasLookups = true) (τ : S.Terminals) :
    S.terminalsElems (F := F) τ ≠ [] := by
  obtain ⟨_, hmem, hne⟩ := List.any_eq_true.mp hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
  have hi : i ∈ S.lookupInstances := by
    simpa only [lookupInstances, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] using hne
  exact List.ne_nil_of_length_pos (by
    rw [length_terminalsElems]
    exact Nat.mul_pos (Finset.card_pos.mpr ⟨i, hi⟩) (Challenge.params EF).d_pos)

/-- The batch's observations: the trace, the permutation trace and the terminals, the quotient,
the PCS's domain separator and the claimed values, FRI's with its domain separator, with the
draws' witnesses, and the draws' squeezes. -/
noncomputable def observer : Observer F S.publicCoin (S.decoder K m) :=
  (wordElems, (lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits,
    lookupWitnessElems S.hasLookups S.params.lookupPowBits,
    (wordElems, (S.terminalsElems, fun _ ↦
      (squeezesFor K (extSamples (EF := EF) 0), extWitnessElems 0,
      (wordElems, (squeezesFor K (extSamples (EF := EF) S.params.oodPowBits),
        extWitnessElems S.params.oodPowBits,
        (fun o ↦ pcsSeedB S ++ S.openingsElems o, fun _ ↦
          (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits),
            extWitnessElems S.params.batchPowBits,
            friObserver K m (S.logN S.top + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
              S.params.numQueries S.params.commitPowBits S.params.queryPowBits
              (S.domainSetup.friSchedule S.friHeights) (friSeedB S))))))))))

/-- The draws' ratios: the lookup challenges' (`lookupRatio`), `1` at `α`, the grinding's
`powFraction` at `ζ` and the batching challenge, FRI's. -/
noncomputable def ratio : Errors S.publicCoin := fun node ↦
  match (node : S.PrefixShape) with
  | ⟨_, .inl _⟩ => lookupRatio F EF S.hasLookups S.params.lookupPowBits
  | ⟨_, .inr ⟨_, _, _, .inl _⟩⟩ => 1
  | ⟨_, .inr ⟨_, _, _, .inr ⟨_, _, .inl _⟩⟩⟩ => Iop.powFraction F S.params.oodPowBits
  | ⟨_, .inr ⟨_, _, _, .inr ⟨_, _, .inr ⟨_, _, .inl _⟩⟩⟩⟩ =>
      Iop.powFraction F S.params.batchPowBits
  | ⟨_, .inr ⟨_, _, _, .inr ⟨_, _, .inr ⟨_, _, .inr ⟨_, node⟩⟩⟩⟩⟩ =>
      friRatio (F := F) (S.logN S.top + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries S.params.commitPowBits S.params.queryPowBits
        (S.domainSetup.friSchedule S.friHeights) node

variable {K m S}

set_option backward.isDefEq.respectTransparency false in
/-- The batch's draws are bounded by their ratios against the laws of its certificate with
Plonky3's query positions, when the coins hold the most demanding challenge's samples. -/
theorem bounded_decoder (hs : 2 * Challenge.d EF + S.params.numQueries + 1 ≤ m * K)
    (publicValues : Fin S.k → List F) (δ δ' : ℝ≥0) (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    Decoder.Bounded S.publicCoin (S.decoder K m) (S.ratio (F := F))
      (S.certificate publicValues δ δ' hδ' loss S.domainSetup.queryPositions).challenges := by
  have he (bits : ℕ) : extSamples (EF := EF) bits ≤ m * K := by
    have := Iop.Setup.extSamples_le (EF := EF) bits
    omega
  have h0 := bounded_extDraw (F := F) (EF := EF) (K := K) (m := m) 0 (he 0)
  rw [Sound.powFraction_zero] at h0
  exact fun _ ↦ ⟨bounded_lookupDraw _ _ ((pairSamples_le _).trans (by omega)),
    fun _ _ _ ↦ ⟨h0, fun _ _ ↦ ⟨bounded_extDraw _ (he _), fun _ _ ↦ ⟨bounded_extDraw _ (he _),
      fun _ ↦ bounded_friDecoder K m (he _)
        ((Iop.Setup.querySamples_le S.params.numQueries _).trans (by omega)) _ _ _ _ _ _ _ _ _ _
          _ _⟩⟩⟩⟩

/-- No challenge of the batch squeezes more often than the most demanding challenge's samples
take. -/
theorem observer_squeezes_le (node : Prefix PUnit S.publicCoin) :
    (S.observer K m).squeezes S.publicCoin (S.decoder K m) node ≤
      squeezesFor K (2 * Challenge.d EF + S.params.numQueries + 1) := by
  have he (bits : ℕ) :
      extSamples (EF := EF) bits ≤ 2 * Challenge.d EF + S.params.numQueries + 1 :=
    (Iop.Setup.extSamples_le bits).trans (by omega)
  obtain ⟨_, _ | ⟨_, _, _, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, node⟩⟩⟩⟩⟩ := (node : S.PrefixShape)
  · exact lookupSqueezes_le _ _ ((pairSamples_le _).trans (by omega))
  · exact squeezesFor_mono (he 0)
  · exact squeezesFor_mono (he _)
  · exact squeezesFor_mono (he _)
  · exact friObserver_squeezes_le K m (he _)
      ((Iop.Setup.querySamples_le S.params.numQueries _).trans (by omega)) _ _ node

/-- The batch's observations are prefix-free. -/
theorem observer_prefixFree :
    (S.observer K m).PrefixFree S.publicCoin (S.decoder (F := F) K m) :=
  ⟨prefixFree_wordElems, (fixFree_lookupWitnessElems _ _).1,
    (fixFree_lookupWitnessElems _ _).2, prefixFree_wordElems,
    prefixFree_of_length S.terminalsElems_injective fun a b ↦
      (S.length_terminalsElems a).trans (S.length_terminalsElems b).symm,
    fun _ ↦ ⟨(fixFree_extWitnessElems 0).1, (fixFree_extWitnessElems 0).2,
      prefixFree_wordElems, (fixFree_extWitnessElems _).1, (fixFree_extWitnessElems _).2,
      prefixFree_of_length (fun _ _ h ↦ S.openingsElems_injective (List.append_cancel_left h))
        (fun a b ↦ by
          show (pcsSeedB S ++ S.openingsElems a).length = (pcsSeedB S ++ S.openingsElems b).length
          rw [List.length_append, List.length_append, S.length_openingsElems a b]),
      fun _ ↦ ⟨(fixFree_extWitnessElems _).1, (fixFree_extWitnessElems _).2,
        prefixFree_friObserver K m _ _⟩⟩⟩

/-- Every challenge of the batch that squeezes has observations since the last squeeze, when
`filled` holds before the trace. -/
theorem observer_fills {filled : Prop} (hf : filled) :
    (S.observer K m).Fills S.publicCoin (S.decoder (F := F) K m) filled := by
  have hQ (Q : S.QuotientMessage) : wordElems Q ≠ [] := by
    have : Nonempty ((i : Fin S.k) × ((Fin (S.instanceSetup i).chunks × Fin (Challenge.d EF)) ×
        (S.instanceSetup i).Point)) :=
      ⟨⟨⟨0, S.nonempty⟩, (⟨0, Nat.two_pow_pos _⟩, ⟨0, (Challenge.params EF).d_pos⟩),
        ⟨0, Nat.two_pow_pos _⟩⟩⟩
    exact List.ne_nil_of_length_pos (by
      simp only [wordElems, List.length_ofFn]
      exact Fintype.card_pos)
  have hpcs : pcsSeedB (F := F) S ≠ [] := by
    simp only [pcsSeedB, DomainSeparator.pcsSeed, DomainSeparator.toElems]
    exact List.cons_ne_nil _ _
  refine fun _ ↦ ⟨fun _ _ ↦ Or.inl (Or.inl hf), fun _ _ t ↦ ⟨fun _ _ ↦ Or.inl ?_,
    fun _ Q ↦ ⟨fun _ _ ↦ Or.inl (Or.inr (hQ Q)),
      fun _ _ ↦ ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_left_ne_nil hpcs _)),
        fun _ ↦ friObserver_fills K m (Nat.two_pow_pos _) _ _ _⟩⟩⟩⟩
  by_cases hl : S.hasLookups = true
  · exact Or.inr (S.terminalsElems_ne_nil hl t)
  · have h0 : (S.observer (F := F) K m).2.1 = 0 := by
      show lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits = 0
      rw [Bool.eq_false_iff.mpr hl]
      rfl
    refine Or.inl (Or.inl ?_)
    split
    · exact Or.inl (Or.inl hf)
    · exact absurd h0 ‹_›

end CompStark.Iop.Batch.Setup

/-! ### The batch for a statement -/

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs CompStark.Ni
open Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] (C : Statement F)

/-- The public values the verifier admits: one list per instance, as many as its AIR declares. -/
abbrev PublicValues : Type :=
  {pis : Fin C.k → List F // ∀ i, (pis i).length = (C.air i).numPublicValues}

/-- The statement's elements: the public values, flattened in instance order, which Plonky3
observes after the main trace. -/
def tail (pis : C.PublicValues) : List F := (List.ofFn pis.1).flatten

variable {C} in
theorem tail_injective : Function.Injective C.tail := fun pis pis' h ↦ by
  have hf (x : C.PublicValues) :
      (List.ofFn x.1).flatten = (List.finRange C.k).flatMap fun i ↦ id (x.1 i) := by
    rw [List.ofFn_eq_map, List.flatMap_def]
    rfl
  simp only [tail, hf] at h
  exact Subtype.ext (funext (eq_of_flatMap_finRange_eq (g := fun _ ↦ id)
    (fun i ↦ by simp only [id, pis.2 i, pis'.2 i]) h))

variable (EF : Type) [Challenge F EF] (K : ℕ)

local notation "𝕂" => Challenge.Spec EF

/-- The squeezes of the most demanding challenge: the lookup challenges after a grinding sample,
or the query positions after theirs. -/
def coinCount : ℕ := squeezesFor K (2 * Challenge.d EF + C.params.numQueries + 1)

/-- The lengths as Plonky3 observes them: every instance's degree bits as an extension element
(`Ext.ofBase`, `Challenge.toSpec_ofBase'`). -/
noncomputable def lengthElems (n : C.Length) : List F :=
  extsElems fun i ↦ algebraMap F 𝕂 ((n.1 i : ℕ) : F)

variable (m : ℕ)

/-- The draws: at the lengths the prover sends, the batch's. -/
noncomputable def decoder : Decoder (Coins F K m) (C.publicCoin EF) :=
  fun n ↦ (C.setup EF n).decoder K m

/-- The observations: the batch's domain separator and the lengths the prover sends, then the
batch's at those lengths. -/
noncomputable def observer : Observer F (C.publicCoin EF) (C.decoder EF K m) :=
  (fun n ↦ C.batchSeed EF ++ C.lengthElems EF n, fun n ↦ (C.setup EF n).observer K m)

/-- The draws' ratios: at each vector of lengths, the batch's. -/
noncomputable def ratio : Errors (C.publicCoin EF) := fun node ↦ (C.setup EF node.1).ratio node.2

variable {C EF K}

/-- Each draw is bounded by its ratio against the laws of the statement's certificate with
Plonky3's query positions, when the coins hold the most demanding challenge. -/
theorem bounded_decoder (hK : 0 < K) (publicValues : Fin C.k → List F)
    (δ δ' : (Fin C.k → ℕ) → ℝ≥0) (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate)
    (loss : C.Length → ℝ≥0) :
    Decoder.Bounded (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K)) (C.ratio EF)
      (certificate EF publicValues δ δ' hδ' loss
        fun n ↦ (C.setup EF n).domainSetup.queryPositions).challenges :=
  fun n ↦ (C.setup EF n).bounded_decoder (le_squeezesFor_mul hK _) _ _ _ _ _

/-- No challenge squeezes more often than the coins hold. -/
theorem squeezes_le (node : Prefix PUnit (C.publicCoin EF)) :
    (C.observer EF K (C.coinCount EF K)).squeezes (C.publicCoin EF)
      (C.decoder EF K (C.coinCount EF K)) node ≤ C.coinCount EF K :=
  (C.setup EF node.1).observer_squeezes_le node.2

/-- The degree bits tell the admitted lengths apart: each is at most the two-adicity, below
`p`. -/
theorem lengthElems_injective : Function.Injective (C.lengthElems EF) := fun n n' h ↦ by
  have hlt := twoAdicity_lt_card (F := F)
  refine Subtype.ext (funext fun i ↦ ?_)
  have hi := congrFun (extsElems_injective h) i
  have := (n.2.sound i).twoAdic
  have := (n'.2.sound i).twoAdic
  exact natCast_inj_of_lt (by omega) (by omega) ((algebraMap F 𝕂).injective hi)

/-- The observations are prefix-free: the degree bits tell the admitted lengths apart. -/
theorem observer_prefixFree :
    (C.observer EF K m).PrefixFree (C.publicCoin EF) (C.decoder EF K m) :=
  ⟨prefixFree_of_length (fun _ _ h ↦ lengthElems_injective (List.append_cancel_left h))
    (fun a b ↦ by
      show (C.batchSeed EF ++ C.lengthElems EF a).length =
        (C.batchSeed EF ++ C.lengthElems EF b).length
      simp only [lengthElems, List.length_append, length_extsElems]),
    fun n ↦ (C.setup EF n).observer_prefixFree⟩

/-- Every challenge that squeezes has observations since the last squeeze. -/
theorem observer_fills :
    (C.observer EF K m).Fills (C.publicCoin EF) (C.decoder EF K m) False := by
  refine fun n ↦ (C.setup EF n).observer_fills (Or.inr ?_)
  simp only [observer, batchSeed, DomainSeparator.batchSeed, DomainSeparator.toElems]
  exact List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _

end CompStark.Iop.Batch.Statement
