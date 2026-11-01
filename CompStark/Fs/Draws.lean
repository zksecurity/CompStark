/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.RoundBounds
public import CompStark.Sound.Sampling
public import ArkLib.Interaction.Oracle.Security.DecodedChallenges

/-! # Plonky3's challenges drawn from duplex squeezes

Plonky3's duplex challenger answers a squeeze with a new capacity and `K` samples. A challenge
reads its samples off the squeezes of its node, `m` of them at most (`Coins F K m`): sample `i` is
sample `i % K` of squeeze `i / K` (`sampleAt`). A challenge needing `s` samples squeezes
`⌈s / K⌉` times (`squeezesFor`), and reads only those squeezes (`reads_sampleAt`).

The draws (`ArkLib`'s `PublicCoin.Draw`):

* `extDraw bits`: an element of the challenge field `𝕂` from `d` samples, after a grinding sample
  with `bits` vanishing low bits if `bits ≠ 0` (Plonky3's `check_witness` then `sample_ext`), and
  with no witness at `bits = 0`;
* `queryDraw bits top t`: `t` positions of the domain of `2 ^ top` points, each the low `top` bits
  of one sample (`sample_bits`), after the grinding sample.

Uniform coins give uniform samples (`prob_samples`), so an extension element is uniform and
`extDraw bits` is bounded by `powFraction F bits` (`bounded_extDraw`). A position is the residue
of a uniform element of `F`, which hits each residue with probability at most
`powFraction F top`, `2 ^ top` times the uniform probability: `queryDraw bits top t` is bounded by
`powFraction F bits * (2 ^ top * powFraction F top) ^ t` (`bounded_queryDraw`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Sound CompStark.Ni OracleComp OracleSpec CompPoly
open Interaction.Oracle Interaction.Oracle.PublicCoin
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The coins of a challenge: the answers of at most `m` squeezes of `K` samples. -/
abbrev Coins (F : Type) (K m : ℕ) : Type := Fin m → Digest F × Vector F K

/-- The zero capacity, the default answer's capacity: the padding of coins past a challenge's
squeezes. -/
instance : Inhabited (Digest F) := ⟨RandomOracle.initCap⟩

/-- The zero samples, the default answer's samples. -/
instance (K : ℕ) : Inhabited (Vector F K) := ⟨Vector.replicate K 0⟩

variable {K m : ℕ}

/-- Sample `i` of the coins: sample `i % K` of squeeze `i / K`, `0` past the last squeeze. -/
def sampleAt (c : Coins F K m) (i : ℕ) : F :=
  if h : i / K < m then (c ⟨i / K, h⟩).2.toList.getD (i % K) 0 else 0

/-- The squeezes of `K` samples that `s` samples take: `⌈s / K⌉`. -/
def squeezesFor (K s : ℕ) : ℕ := (s + K - 1) / K

/-- The first `s` samples read only the first `⌈s / K⌉` squeezes. -/
theorem reads_sampleAt (hK : 0 < K) {s : ℕ} {c c' : Coins F K m}
    (h : ∀ j : Fin m, (j : ℕ) < squeezesFor K s → c j = c' j) {i : ℕ} (hi : i < s) :
    sampleAt c i = sampleAt c' i := by
  have hlt : i / K < squeezesFor K s := by
    have h1 : i / K ≤ (s - 1) / K := Nat.div_le_div_right (by omega)
    have h2 : (s + K - 1) / K = (s - 1) / K + 1 := by
      rw [show s + K - 1 = s - 1 + K * 1 by omega, Nat.add_mul_div_left _ _ hK]
    simp only [squeezesFor, h2]
    omega
  unfold sampleAt
  split_ifs with hm
  · rw [h ⟨i / K, hm⟩ hlt]
  · rfl

/-- The coins as their digests and their samples, sample `j` at `j`. -/
def coinsEquiv : Coins F K m ≃ (Fin m → Digest F) × (Fin (m * K) → F) :=
  (Equiv.arrowProdEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.arrowCongr (Equiv.refl _) (arrayVectorEquivFin F K)).trans
      ((Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl F)))))

/-- Sample `j` of the coins is coordinate `j` of their samples. -/
theorem coinsEquiv_snd (c : Coins F K m) (j : Fin (m * K)) :
    (coinsEquiv c).2 j = sampleAt c j := by
  have hK : 0 < K := Nat.pos_of_ne_zero fun h ↦ by simp only [h, Nat.mul_zero] at j; exact j.elim0
  have hj : (j : ℕ) / K < m := (Nat.div_lt_iff_lt_mul hK).mpr j.isLt
  have hr : (j : ℕ) % K < K := Nat.mod_lt _ hK
  simp only [coinsEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
    Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.curry_symm_apply, Function.uncurry_apply_pair, arrayVectorEquivFin, Equiv.coe_fn_mk,
    Equiv.arrowProdEquivProdArrow_apply, sampleAt, hj, ↓reduceDIte, finProdFinEquiv_symm_apply,
    Fin.coe_modNat, List.getD_eq_getElem?_getD, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem hr, Option.getD_some]
  rfl

/-- The first `s ≤ m K` samples of uniform coins are uniform. -/
theorem prob_samples {s : ℕ} (hs : s ≤ m * K) (P : (Fin s → F) → Prop) :
    Pr{let c ← $ᵗ (Coins F K m)}[P fun j ↦ sampleAt c j] = Pr{let x ← $ᵗ (Fin s → F)}[P x] := by
  let e : (Fin (m * K) → F) ≃ (Fin s → F) × (Fin (m * K - s) → F) :=
    (Equiv.arrowCongr (finCongr (by omega : m * K = s + (m * K - s))) (Equiv.refl F)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _))
  have he (c : Coins F K m) : (e (coinsEquiv c).2).1 = fun j : Fin s ↦ sampleAt c j := by
    funext j
    simp only [e, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst, Function.comp_apply,
      Equiv.arrowCongr_apply, Equiv.symm_symm, finSumFinEquiv_apply_left, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, coinsEquiv_snd, Fin.val_cast, Fin.val_castAdd]
  calc _ = Pr{let c ← $ᵗ (Coins F K m)}[(fun z : (Fin m → Digest F) × (Fin (m * K) → F) ↦
        P (e z.2).1) (coinsEquiv c)] := prEvent_congr_iff _ fun c ↦ by dsimp only; rw [he]
    _ = Pr{let z ← $ᵗ ((Fin m → Digest F) × (Fin (m * K) → F))}[P (e z.2).1] :=
        SampleableType.prEvent_uniformSample_equiv (coinsEquiv (F := F) (K := K) (m := m))
          (fun z ↦ P (e z.2).1)
    _ = Pr{let y ← $ᵗ (Fin (m * K) → F)}[P (e y).1] := by
        have h := SampleableType.prEvent_uniformSample_equiv
          (Equiv.prodComm (Fin m → Digest F) (Fin (m * K) → F)) (fun z ↦ P (e z.1).1)
        simp only [Equiv.prodComm_apply, Prod.fst_swap] at h
        rw [h]
        exact SampleableType.prEvent_uniformSample_fst (fun y ↦ P (e y).1)
    _ = Pr{let z ← $ᵗ ((Fin s → F) × (Fin (m * K - s) → F))}[P z.1] :=
        SampleableType.prEvent_uniformSample_equiv e (fun z ↦ P z.1)
    _ = _ := SampleableType.prEvent_uniformSample_fst P

/-- The extension element of the `d` samples from `o` on. -/
noncomputable def extOf (c : Coins F K m) (o : ℕ) : 𝕂 :=
  extEquiv fun j ↦ sampleAt c (o + j)

/-- The grinding sample's canonical value: sample `0`. -/
def powSample (c : Coins F K m) : ℕ := CanonicalNat.toNat (sampleAt c 0)

/-- An extension challenge drawn with `bits` bits of grinding: after the grinding witness, the
grinding sample must have `bits` vanishing low bits and the challenge is read after it; without
grinding, there is no witness and the challenge is read from sample `0`. -/
noncomputable def extDraw : ℕ → Draw (Coins F K m) 𝕂
  | 0 => Draw.plain (extOf · 0)
  | bits + 1 => Draw.grind F (bits + 1) powSample (extOf · 1)

/-- The position of the domain of `2 ^ top` points read off a sample: its low `top` bits. -/
def positionOf (top : ℕ) (x : F) : Fin (2 ^ top) :=
  ⟨CanonicalNat.toNat x % 2 ^ top, Nat.mod_lt _ (Nat.two_pow_pos top)⟩

/-- `t` query positions drawn with `bits` bits of grinding, each the low `top` bits of one
sample, after the grinding sample if `bits ≠ 0`. -/
noncomputable def queryDraw (top t : ℕ) : ℕ → Draw (Coins F K m) (Fin t → Fin (2 ^ top))
  | 0 => Draw.plain fun c i ↦ positionOf top (sampleAt c i)
  | bits + 1 => Draw.grind F (bits + 1) powSample fun c i ↦ positionOf top (sampleAt c (1 + i))

/-- The samples an extension challenge with `bits` bits of grinding reads. -/
def extSamples (bits : ℕ) : ℕ := Challenge.d EF + if bits = 0 then 0 else 1

/-- The samples the query draw with `bits` bits of grinding reads. -/
def querySamples (t bits : ℕ) : ℕ := t + if bits = 0 then 0 else 1

/-- An extension draw with `bits` bits of grinding is bounded by `powFraction F bits`, when its
samples fit the coins. -/
theorem bounded_extDraw (bits : ℕ) (hs : extSamples (EF := EF) bits ≤ m * K) :
    (extDraw (F := F) (EF := EF) (K := K) (m := m) bits).Bounded (Iop.powFraction F bits) := by
  classical
  cases bits with
  | zero =>
    have hd : Challenge.d EF ≤ m * K := by
      simpa only [extSamples, ↓reduceIte, Nat.add_zero] using hs
    rw [Sound.powFraction_zero, extDraw]
    refine Draw.Bounded.plain fun E ↦ ?_
    rw [one_mul]
    refine le_of_eq ?_
    calc _ = Pr{let c ← $ᵗ (Coins F K m)}[(fun x ↦ E (extEquiv x)) fun j ↦ sampleAt c j] :=
          prEvent_congr_iff _ fun c ↦ by simp only [extOf, Nat.zero_add]
      _ = _ := (prob_samples hd _).trans (SampleableType.prEvent_uniformSample_equiv extEquiv E)
  | succ b =>
    have hd : Challenge.d EF + 1 ≤ m * K := by
      simpa only [extSamples, Nat.add_one_ne_zero, ↓reduceIte] using hs
    intro E
    simp only [extDraw, Draw.grind, beq_iff_eq]
    calc _ = Pr{let c ← $ᵗ (Coins F K m)}[(fun x ↦
          CanonicalNat.toNat (powExtEquiv x).1 % 2 ^ (b + 1) = 0 ∧ E (powExtEquiv x).2)
            fun j ↦ sampleAt c j] :=
          prEvent_congr_iff _ fun c ↦ by
            simp only [powExtEquiv_apply, powSample, extOf, Fin.val_zero, Fin.val_succ]
            simp only [Nat.add_comm 1]
      _ = Pr{let z ← $ᵗ (F × 𝕂)}[CanonicalNat.toNat z.1 % 2 ^ (b + 1) = 0 ∧ E z.2] :=
          (prob_samples hd _).trans (SampleableType.prEvent_uniformSample_equiv powExtEquiv
            (fun z ↦ CanonicalNat.toNat z.1 % 2 ^ (b + 1) = 0 ∧ E z.2))
      _ ≤ _ := prob_pow_and_le (b + 1) E

/-- A residue below `2 ^ top` has at most `(p - 1) / 2 ^ top + 1` preimages in `F`. -/
theorem card_positionOf_le (top : ℕ) (r : Fin (2 ^ top)) :
    (Finset.univ.filter fun x : F ↦ positionOf top x = r).card ≤
      (Nat.card F - 1) / 2 ^ top + 1 := by
  have hp : Nat.card F = CanonicalNat.bound F := by
    rw [Nat.card_eq_fintype_card, CanonicalNat.card_eq]
  refine (Finset.card_le_card_of_injOn (fun x ↦ CanonicalNat.toNat x / 2 ^ top) ?_ ?_).trans
    (Finset.card_range _).le
  · intro x _
    have hx := CanonicalNat.toNat_lt x
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    have hx' := congrArg Fin.val hx
    have hy' := congrArg Fin.val hy
    simp only [positionOf] at hx' hy' hxy
    apply CanonicalNat.toNat_injective
    rw [← Nat.div_add_mod (CanonicalNat.toNat x) (2 ^ top),
      ← Nat.div_add_mod (CanonicalNat.toNat y) (2 ^ top), hx', hy', hxy]

/-- The tuples of `F` whose positions satisfy `E` number at most `((p - 1) / 2 ^ top + 1) ^ t`
for each tuple of positions satisfying `E`. -/
theorem card_positions_le (top t : ℕ) (E : (Fin t → Fin (2 ^ top)) → Prop) [DecidablePred E] :
    (Finset.univ.filter fun x : Fin t → F ↦ E fun i ↦ positionOf top (x i)).card ≤
      ((Nat.card F - 1) / 2 ^ top + 1) ^ t * (Finset.univ.filter E).card := by
  classical
  have hsub : (Finset.univ.filter fun x : Fin t → F ↦ E fun i ↦ positionOf top (x i)) ⊆
      (Finset.univ.filter E).biUnion fun y ↦
        Fintype.piFinset fun i ↦ Finset.univ.filter fun a : F ↦ positionOf top a = y i := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    exact ⟨_, hx, fun _ ↦ rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_card_nsmul _ _ _ fun y _ ↦ ?_).trans_eq (by rw [smul_eq_mul, mul_comm])
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_pow_card _ _ _ fun i _ ↦ card_positionOf_le top (y i)).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_fin]

/-- `t` uniform positions of `F` satisfy `E` with probability at most
`(2 ^ top * powFraction F top) ^ t` times that of `t` uniform positions. -/
theorem prob_positions_le (top t : ℕ) (E : (Fin t → Fin (2 ^ top)) → Prop) :
    Pr{let x ← $ᵗ (Fin t → F)}[E fun i ↦ positionOf top (x i)] ≤
      (2 ^ top * Iop.powFraction F top) ^ t * Pr{let y ← $ᵗ (Fin t → Fin (2 ^ top))}[E y] := by
  classical
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample,
    Iop.powFraction, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    ← Nat.card_eq_fintype_card]
  have h2 : ((2 : ℝ≥0∞) ^ top) ^ t * (((2 : ℝ≥0∞) ^ top) ^ t)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by positivity) (by simp)
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr (card_positions_le (F := F) top t E))
    _).trans_eq ?_
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow, ENNReal.inv_pow]
  generalize ((2 : ℝ≥0∞) ^ top) ^ t = a at h2 ⊢
  refine ((mul_one _).symm.trans (congrArg (HMul.hMul _) h2.symm)).trans ?_
  ring

/-- The query draw with `bits` bits of grinding is bounded by
`powFraction F bits * (2 ^ top * powFraction F top) ^ t`, when its samples fit the coins. -/
theorem bounded_queryDraw (top t bits : ℕ) (hs : querySamples t bits ≤ m * K) :
    (queryDraw (F := F) (K := K) (m := m) top t bits).Bounded
      (Iop.powFraction F bits * (2 ^ top * Iop.powFraction F top) ^ t) := by
  classical
  cases bits with
  | zero =>
    have ht : t ≤ m * K := by simpa only [querySamples, ↓reduceIte, Nat.add_zero] using hs
    rw [Sound.powFraction_zero, one_mul, queryDraw]
    refine Draw.Bounded.plain fun E ↦ ?_
    exact (prob_samples ht fun x ↦ E fun i ↦ positionOf top (x i)).trans_le
      (prob_positions_le top t E)
  | succ b =>
    have ht : t + 1 ≤ m * K := by
      simpa only [querySamples, Nat.add_one_ne_zero, ↓reduceIte] using hs
    intro E
    simp only [queryDraw, Draw.grind, beq_iff_eq]
    calc _ = Pr{let c ← $ᵗ (Coins F K m)}[(fun x : Fin (t + 1) → F ↦
          CanonicalNat.toNat ((Fin.consEquiv fun _ ↦ F).symm x).1 % 2 ^ (b + 1) = 0 ∧
            E fun i ↦ positionOf top (((Fin.consEquiv fun _ ↦ F).symm x).2 i))
            fun j ↦ sampleAt c j] :=
          prEvent_congr_iff _ fun c ↦ by
            simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail, powSample, Fin.val_zero,
              Fin.val_succ]
            simp only [Nat.add_comm 1]
      _ = Pr{let z ← $ᵗ (F × (Fin t → F))}[CanonicalNat.toNat z.1 % 2 ^ (b + 1) = 0 ∧
            E fun i ↦ positionOf top (z.2 i)] :=
          (prob_samples ht _).trans (SampleableType.prEvent_uniformSample_equiv
            (Fin.consEquiv fun _ ↦ F).symm (fun z : F × (Fin t → F) ↦
              CanonicalNat.toNat z.1 % 2 ^ (b + 1) = 0 ∧ E fun i ↦ positionOf top (z.2 i)))
      _ ≤ Iop.powFraction F (b + 1) *
            Pr{let x ← $ᵗ (Fin t → F)}[E fun i ↦ positionOf top (x i)] :=
          prob_pow_and_le (β := Fin t → F) (b + 1) fun x ↦ E fun i ↦ positionOf top (x i)
      _ ≤ _ := by
          rw [mul_assoc]
          exact mul_le_mul_right (prob_positions_le top t E) _

/-- An extension draw reads only the squeezes of its samples. -/
theorem reads_extDraw (hK : 0 < K) (bits : ℕ) (c c' : Coins F K m)
    (h : ∀ j : Fin m, (j : ℕ) < squeezesFor K (extSamples (EF := EF) bits) → c j = c' j) :
    (extDraw (EF := EF) bits).accept c = (extDraw (EF := EF) bits).accept c' ∧
      (extDraw (EF := EF) bits).decode c = (extDraw (EF := EF) bits).decode c' := by
  have hs (i : ℕ) (hi : i < extSamples (EF := EF) bits) : sampleAt c i = sampleAt c' i :=
    reads_sampleAt hK h hi
  cases bits with
  | zero =>
    refine ⟨rfl, ?_⟩
    simp only [extDraw, Draw.plain, extOf]
    congr 1
    funext j
    exact hs _ (by simp only [extSamples, ↓reduceIte]; omega)
  | succ b =>
    simp only [extDraw, Draw.grind, powSample, extOf]
    refine ⟨by rw [hs 0 (by simp only [extSamples, Nat.add_one_ne_zero, ↓reduceIte]; omega)], ?_⟩
    congr 1
    funext j
    exact hs _ (by simp only [extSamples, Nat.add_one_ne_zero, ↓reduceIte]; omega)

/-- The query draw reads only the squeezes of its samples. -/
theorem reads_queryDraw (hK : 0 < K) (top t bits : ℕ) (c c' : Coins F K m)
    (h : ∀ j : Fin m, (j : ℕ) < squeezesFor K (querySamples t bits) → c j = c' j) :
    (queryDraw (F := F) top t bits).accept c = (queryDraw top t bits).accept c' ∧
      (queryDraw (F := F) top t bits).decode c = (queryDraw top t bits).decode c' := by
  have hs (i : ℕ) (hi : i < querySamples t bits) : sampleAt c i = sampleAt c' i :=
    reads_sampleAt hK h hi
  cases bits with
  | zero =>
    refine ⟨rfl, ?_⟩
    simp only [queryDraw, Draw.plain]
    funext i
    rw [hs i (by simp only [querySamples, ↓reduceIte]; omega)]
  | succ b =>
    simp only [queryDraw, Draw.grind, powSample]
    refine ⟨by rw [hs 0 (by simp only [querySamples, Nat.add_one_ne_zero, ↓reduceIte]; omega)],
      ?_⟩
    funext i
    rw [hs (1 + i) (by simp only [querySamples, Nat.add_one_ne_zero, ↓reduceIte]; omega)]

end CompStark.Fs
