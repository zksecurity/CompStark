/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.RoundBounds
public import CompStark.Sound.Sampling
public import ArkLib.Interaction.Oracle.Security.DecodedChallenges
public import ArkLib.ProofSystem.Fri.Interaction.QueryKnowledge

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
`extDraw bits` is bounded by `powFraction F bits` against the uniform law (`bounded_extDraw`). The
query positions are the residues of `t` uniform elements of `F` (`positionLaw`), and
`queryDraw bits top t` is bounded by `powFraction F bits` against that law
(`bounded_queryDraw`). With `2 ^ top ∣ p - 1`, a residue lands in a set of `c` positions with
probability at most `c / 2 ^ top + 1 / p`: only the residue `0` has an extra preimage. So the
law's positions all land in a set of density `ρ` with probability at most `(ρ + 1/p) ^ t`
(`queryLaw`, FRI's `QueryLaw` with slack `1/p`).
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

/-- An extension draw with `bits` bits of grinding is bounded by `powFraction F bits` against the
uniform law, when its samples fit the coins. -/
theorem bounded_extDraw (bits : ℕ) (hs : extSamples (EF := EF) bits ≤ m * K) :
    (extDraw (F := F) (EF := EF) (K := K) (m := m) bits).Bounded ($ᵗ 𝕂)
      (Iop.powFraction F bits) := by
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

/-- The law of `t` query positions on the domain of `2 ^ top` points, each the low `top` bits of a
uniform element of `F`. -/
noncomputable def positionLaw (top t : ℕ) : ProbComp (Fin t → Fin (2 ^ top)) :=
  (fun x : Fin t → F ↦ fun i ↦ positionOf top (x i)) <$> ($ᵗ (Fin t → F))

/-- An event on the positions of `positionLaw` is the event on the residues of uniform elements. -/
theorem prob_positionLaw (top t : ℕ) (E : (Fin t → Fin (2 ^ top)) → Prop) :
    Pr{let y ← (positionLaw (F := F) top t)}[E y] =
      Pr{let x ← $ᵗ (Fin t → F)}[E fun i ↦ positionOf top (x i)] := by
  rw [positionLaw, prEvent_map]

/-- **The positions' law.** With `2 ^ top ∣ p - 1`, the positions of `positionLaw` all land in a
set of `c` positions with probability at most `(c / 2 ^ top + 1/p) ^ t`: FRI's query law with
slack `1/p`. -/
noncomputable def queryLaw (top t : ℕ) (hb : 2 ^ top ∣ Nat.card F - 1) :
    Fri.Interaction.QueryLaw top t where
  law := positionLaw (F := F) top t
  slack := 1 / (Nat.card F : ENNReal)
  bound C := by
    classical
    rw [prob_positionLaw]
    set A := Finset.univ.filter fun x : F ↦ positionOf top x ∈ C
    have hA : ∀ x : Fin t → F, (∀ i, positionOf top (x i) ∈ C) ↔ ∀ i, x i ∈ A := fun x ↦ by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hA]
    rw [Probability.prob_uniform_pi_mem_finset_eq]
    gcongr
    have h := prob_val_mod_mem_le top hb (C.map Fin.valEmbedding)
    rw [SampleableType.prEvent_uniformSample, Finset.card_map] at h
    refine le_of_eq_of_le ?_ h
    have hmem (x : F) :
        positionOf top x ∈ C ↔ CanonicalNat.toNat x % 2 ^ top ∈ C.map Fin.valEmbedding := by
      rw [Finset.mem_map]
      refine ⟨fun hx ↦ ⟨_, hx, rfl⟩, fun ⟨y, hy, he⟩ ↦ ?_⟩
      have hy' : positionOf top x = y := Fin.ext he.symm
      rwa [hy']
    congr 3
    ext x
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmem x

@[simp] theorem slack_queryLaw (top t : ℕ) (hb : 2 ^ top ∣ Nat.card F - 1) :
    (queryLaw (F := F) top t hb).slack = 1 / (Nat.card F : ENNReal) := rfl

/-- The query draw with `bits` bits of grinding is bounded by `powFraction F bits` against the
positions' law, when its samples fit the coins. -/
theorem bounded_queryDraw (top t bits : ℕ) (hs : querySamples t bits ≤ m * K) :
    (queryDraw (F := F) (K := K) (m := m) top t bits).Bounded (positionLaw (F := F) top t)
      (Iop.powFraction F bits) := by
  classical
  cases bits with
  | zero =>
    have ht : t ≤ m * K := by simpa only [querySamples, ↓reduceIte, Nat.add_zero] using hs
    rw [Sound.powFraction_zero, queryDraw]
    refine Draw.Bounded.plain fun E ↦ ?_
    rw [one_mul, prob_positionLaw]
    exact (prob_samples ht fun x ↦ E fun i ↦ positionOf top (x i)).le
  | succ b =>
    have ht : t + 1 ≤ m * K := by
      simpa only [querySamples, Nat.add_one_ne_zero, ↓reduceIte] using hs
    intro E
    simp only [queryDraw, Draw.grind, beq_iff_eq]
    rw [prob_positionLaw]
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
      _ ≤ _ :=
          prob_pow_and_le (β := Fin t → F) (b + 1) fun x ↦ E fun i ↦ positionOf top (x i)

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
