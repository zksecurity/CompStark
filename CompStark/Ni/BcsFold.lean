/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Rbr
public import CompStark.Complete.Fold

/-! # Plonky3's folds as ArkLib's

Plonky3's `foldRow` interpolates a group of `2 ^ arity` committed values through points of the
subgroup `⟨ω⟩`, while ArkLib's `foldValue` interpolates through the points of the coset
`s · ⟨ω⟩` the word lives on. The two interpolants differ by the substitution `X ↦ s X`, so
Plonky3's fold at `β` is ArkLib's fold at `s β` (`toSpec_foldRow_eq_foldValue`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound Polynomial Montgomery.Native32
open KoalaBear.Fast (Ext4)

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4
local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => Challenge.Spec KoalaBear.Fast.Ext4

/-- The points of the coset domain of order `2 ^ n`, in natural order. -/
theorem cosetDomain_apply (n : Nat) (hn : n ≤ 24) (k : Fin (2 ^ n)) :
    @cosetDomain EF _ n hn k = @lift EF _ gen * @lift EF _ (twoAdicGen n) ^ k.val := by
  simp only [cosetDomain,
    Domain.CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    Domain.CosetFftDomain.subgroupUnit, subgroupHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_mk0, Units.val_pow_eq_pow_val, IsUnit.unit_spec, toAdd_ofAdd]

/-- `lift` at `Fast.Ext4` is `Complete.emb`. -/
theorem lift_eq_emb (x : F) : @lift EF _ x = Complete.emb x := rfl

theorem lift_ne_zero {x : F} (hx : x ≠ 0) : @lift EF _ x ≠ 0 := by
  rw [lift, ne_eq, map_eq_zero_iff _ (algebraMap 𝔽 𝕂).injective]
  intro h
  exact hx (toField_injective (by rw [h, toField_zero]))

theorem lift_gen_ne_zero : @lift EF _ gen ≠ 0 := lift_ne_zero CompStark.gen_ne_zero

/-- The points of the `p`-th subdomain of the coset domain: `g ^ 2 ^ p · ω_{n - p} ^ k`. -/
theorem subdomain_apply (n : Nat) (hn : n ≤ 24) (p : Nat) (hp : p ≤ n)
    (k : Fin (2 ^ (n - p))) :
    (@cosetDomain EF _ n hn).subdomain p k =
      @lift EF _ gen ^ 2 ^ p * @lift EF _ (twoAdicGen (n - p)) ^ k.val := by
  rw [Domain.CosetFftDomainClass.subdomain_apply]
  rw [cosetDomain_apply, Fin.val_zero, pow_zero, mul_one]
  congr 1
  show (@cosetDomain EF _ n hn 0)⁻¹ * @cosetDomain EF _ n hn _ = _
  rw [cosetDomain_apply, cosetDomain_apply, Fin.val_zero, pow_zero, mul_one,
    inv_mul_cancel_left₀ lift_gen_ne_zero]
  unfold Domain.CosetFftDomainClass.subdomain_embed
  by_cases hpn : p ≥ n
  · have hp' : p = n := by omega
    subst hp'
    have hk : k.val = 0 := by have := k.isLt; simp only [Nat.sub_self, pow_zero] at this; omega
    simp only [ge_iff_le, le_refl, ↓reduceDIte, Fin.val_zero, pow_zero, hk]
  · simp only [hpn, ↓reduceDIte]
    have h := Fast.twoAdicGen_pow (n - p) p (by omega)
    rw [Nat.sub_add_cancel hp] at h
    rw [pow_mul, lift, lift, ← map_pow, ← map_pow, ← toField_npow, ← toField_npow, h,
      toField_npow, map_pow]

/-- An index below `2 ^ m`, reduced. -/
def finMod (m r : Nat) : Fin (2 ^ m) := ⟨r % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- The points of the `p`-th subdomain at an index below its size. -/
theorem subdomain_finMod (n : Nat) (hn : n ≤ 24) (p : Nat) (hp : p ≤ n) (r : Nat)
    (hr : r < 2 ^ (n - p)) :
    (@cosetDomain EF _ n hn).subdomain p (finMod (n - p) r) =
      @lift EF _ gen ^ 2 ^ p * Complete.emb (twoAdicGen (n - p) ^ r) := by
  rw [subdomain_apply n hn p hp, finMod, Fin.val_mk, Nat.mod_eq_of_lt hr, Complete.emb_pow]
  rfl

theorem natDegree_comp_C_mul_X (q : 𝕂[X]) (s : 𝕂) :
    (q.comp (Polynomial.C s * Polynomial.X)).natDegree ≤ q.natDegree :=
  natDegree_comp_le.trans ((Nat.mul_le_mul_left _
    ((natDegree_C_mul_le _ _).trans natDegree_X_le)).trans (Nat.mul_one _).le)

/-- **Plonky3's fold is ArkLib's.** A group of `2 ^ la` values at the folded index `i` of a word
`f` on the `p`-th subdomain, of size `2 ^ (lF + la)`, in bit-reversed order (entry `k` of the group
is the word at `rev (i 2 ^ la + k)`), folds by `foldRow` at `β` to ArkLib's fold of `f` at
`s β`, `s = g ^ 2 ^ p` the subdomain's shift, at the group's `2 ^ la`-th power. -/
theorem toSpec_foldRow_eq_foldValue (n : Nat) (hn : n ≤ 24) (p lF la : Nat)
    (hm : n - p = lF + la) (hp : p ≤ n) (f : Fin (2 ^ (n - p)) → 𝕂) (i : Nat)
    (beta : EF) (gy : Nat → EF)
    (hgy : ∀ k < 2 ^ la, Ext4.toSpec (gy k) =
      f (finMod (n - p) (reverseBits (i * 2 ^ la + k) (n - p))))
    (pos : Nat) (hpos : pos < 2 ^ la) :
    Ext4.toSpec (foldRow i lF la beta ((List.range (2 ^ la)).map gy)) =
      ProximityGap.foldValue ((@cosetDomain EF _ n hn).subdomain p) f la
        (@lift EF _ gen ^ 2 ^ p * Ext4.toSpec beta)
        ((@cosetDomain EF _ n hn).subdomain p
          (finMod (n - p) (reverseBits (i * 2 ^ la + pos) (n - p))) ^ 2 ^ la) := by
  set D := (@cosetDomain EF _ n hn).subdomain p
  set s : 𝕂 := @lift EF _ gen ^ 2 ^ p
  set start := powF (twoAdicGen (lF + la)) (reverseBits i lF) with hstart
  have h24 : lF + la ≤ 24 := by omega
  have hgx : ∀ k < 2 ^ la, start * powF (twoAdicGen la) (reverseBits k la) =
      twoAdicGen (lF + la) ^ reverseBits (i * 2 ^ la + k) (lF + la) := fun k hk ↦ by
    rw [hstart, Fast.powF_eq, Fast.powF_eq, Complete.twoAdicGen_pow_concat la lF i k h24 hk]
  -- The group's points on the subdomain.
  have hpt : ∀ k < 2 ^ la, D (finMod (n - p) (reverseBits (i * 2 ^ la + k) (n - p))) =
      s * Complete.emb (start * powF (twoAdicGen la) (reverseBits k la)) := fun k hk ↦ by
    rw [subdomain_finMod n hn p hp _ (by rw [hm]; exact Complete.reverseBits_lt _ _), hm,
      hgx k hk]
  have hpow : ∀ k < 2 ^ la, D (finMod (n - p) (reverseBits (i * 2 ^ la + k) (n - p))) ^ 2 ^ la =
      (s * Complete.emb start) ^ 2 ^ la := fun k hk ↦ by
    rw [hpt k hk, Complete.emb_mul, ← mul_assoc, mul_pow, Fast.powF_eq,
      Complete.emb_pow, ← pow_mul, Nat.mul_comm, pow_mul,
      (Complete.isPrimitiveRoot_emb la (by omega)).pow_eq_one, one_pow, mul_one]
  set y := D (finMod (n - p) (reverseBits (i * 2 ^ la + pos) (n - p))) ^ 2 ^ la with hy
  set I := Lagrange.interpolate (Domain.CosetFftDomainClass.blockIdx D la y) (⇑D) f
  have hinjD : Set.InjOn (⇑D) (Domain.CosetFftDomainClass.blockIdx D la y : Set _) :=
    fun a _ b _ h ↦ Domain.CosetFftDomainClass.injective D h
  rw [ProximityGap.foldValue_def']
  have hs0 : s ≠ 0 := pow_ne_zero _ lift_gen_ne_zero
  have hstart0 : start ≠ 0 := by
    rw [hstart, Fast.powF_eq]; exact Complete.twoAdicGen_ne_zero' _ (by omega) _
  unfold foldRow
  dsimp only
  rw [Complete.toSpec_lagrange (2 ^ la) (fun k ↦ start * powF (twoAdicGen la) (reverseBits k la))
    gy beta (I.comp (Polynomial.C s * Polynomial.X))]
  · rw [eval_comp, eval_mul, eval_C, eval_X]
  · exact Complete.groupPoints_injective la start (by omega) hstart0
  · refine (degree_le_natDegree).trans_lt ?_
    exact_mod_cast (natDegree_comp_C_mul_X I s).trans_lt
      (ProximityGap.foldWordAux_natDegree (domain := D) (f := f))
  · intro k hk
    rw [hgy k hk, eval_comp, eval_mul, eval_C, eval_X, ← hpt k hk]
    refine (Lagrange.eval_interpolate_at_node _ hinjD ?_).symm
    rw [Domain.CosetFftDomainClass.mem_blockIdx, hy, hpow k hk, hpow pos hpos]

/-! ### The query's point at each fold -/

/-- The low `n - p` bits of the reversal of `I` in `n` bits are the reversal of `I`'s high bits. -/
theorem reverseBits_mod (I n p : Nat) (hp : p ≤ n) :
    reverseBits I n % 2 ^ (n - p) = reverseBits (I >>> p) (n - p) := by
  have hsplit : I = (I >>> p) * 2 ^ p + I % 2 ^ p := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]; exact (Nat.div_add_mod I (2 ^ p)).symm
  have h := Complete.reverseBits_concat p (n - p) (I >>> p) (I % 2 ^ p)
    (Nat.mod_lt _ (Nat.two_pow_pos p))
  rw [← hsplit, Nat.sub_add_cancel hp] at h
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt (Complete.reverseBits_lt _ _)]

/-- The `2 ^ p`-th power of the point of `L` at `rev I` is the point of the `p`-th subdomain at the
reversal of `I`'s high bits: Plonky3's index `I >>> p` at height `n - p`. -/
theorem domain_pow_eq (n : Nat) (hn : n ≤ 24) (p : Nat) (hp : p ≤ n) (I : Nat) :
    @cosetDomain EF _ n hn (finMod n (reverseBits I n)) ^ 2 ^ p =
      (@cosetDomain EF _ n hn).subdomain p (finMod (n - p) (reverseBits (I >>> p) (n - p))) := by
  rw [subdomain_finMod n hn p hp _ (Complete.reverseBits_lt _ _), cosetDomain_apply, finMod,
    Fin.val_mk, Nat.mod_eq_of_lt (Complete.reverseBits_lt _ _), ← reverseBits_mod I n p hp,
    mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  congr 1
  have h := Fast.twoAdicGen_pow (n - p) p (by omega)
  rw [Nat.sub_add_cancel hp] at h
  have hord := (Complete.isPrimitiveRoot_emb (n - p) (by omega)).pow_eq_one
  rw [lift_eq_emb, ← Complete.emb_pow, h, Complete.emb_pow]
  conv_lhs => rw [← Nat.div_add_mod (reverseBits I n) (2 ^ (n - p)), pow_add, pow_mul, hord,
    one_pow, one_mul]


end CompStark.Ni
