/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Rbr
public import CompStark.Stark.Points

/-! # Plonky3's folds as ArkLib's

Plonky3's `foldRow` interpolates a group of `2 ^ arity` committed values through points of the
subgroup `⟨ω⟩`, while ArkLib's `foldValue` interpolates through the points of the coset
`s · ⟨ω⟩` the word lives on. The two interpolants differ by the substitution `X ↦ s X`, so
Plonky3's fold at `β` is ArkLib's fold at `s β` (`toSpec_foldRow_eq_foldValue`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound Polynomial


variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The points of the coset domain of order `2 ^ n`, in natural order. -/
theorem cosetDomain_apply (n : Nat) (hn : n ≤ twoAdicity F) (k : Fin (2 ^ n)) :
    cosetDomain (EF := EF) n hn k = lift gen * lift (twoAdicGen n) ^ k.val := by
  simp only [cosetDomain,
    Domain.CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    Domain.CosetFftDomain.subgroupUnit, subgroupHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_mk0, Units.val_pow_eq_pow_val, IsUnit.unit_spec, toAdd_ofAdd]

theorem lift_mul (x y : F) : (lift (x * y) : 𝕂) = lift x * lift y := by
  rw [lift, lift, lift, map_mul]

theorem lift_pow (x : F) (n : Nat) : (lift (x ^ n) : 𝕂) = lift x ^ n := by
  rw [lift, lift, map_pow]

theorem lift_ne_zero {x : F} (hx : x ≠ 0) : (lift x : 𝕂) ≠ 0 := by
  rw [lift, ne_eq, map_eq_zero_iff _ (algebraMap F 𝕂).injective]
  exact hx

theorem lift_gen_ne_zero : (lift gen : 𝕂) ≠ 0 := lift_ne_zero BaseField.gen_ne_zero

/-- The points of the `p`-th subdomain of the coset domain: `g ^ 2 ^ p · ω_{n - p} ^ k`. -/
theorem subdomain_apply (n : Nat) (hn : n ≤ twoAdicity F) (p : Nat) (hp : p ≤ n)
    (k : Fin (2 ^ (n - p))) :
    (cosetDomain (EF := EF) n hn).subdomain p k =
      lift gen ^ 2 ^ p * lift (twoAdicGen (n - p)) ^ k.val := by
  rw [Domain.CosetFftDomainClass.subdomain_apply]
  rw [cosetDomain_apply, Fin.val_zero, pow_zero, mul_one]
  congr 1
  show (cosetDomain (EF := EF) n hn 0)⁻¹ * cosetDomain (EF := EF) n hn _ = _
  rw [cosetDomain_apply, cosetDomain_apply, Fin.val_zero, pow_zero, mul_one,
    inv_mul_cancel_left₀ lift_gen_ne_zero]
  unfold Domain.CosetFftDomainClass.subdomain_embed
  by_cases hpn : p ≥ n
  · have hp' : p = n := by omega
    subst hp'
    have hk : k.val = 0 := by have := k.isLt; simp only [Nat.sub_self, pow_zero] at this; omega
    simp only [ge_iff_le, le_refl, ↓reduceDIte, Fin.val_zero, pow_zero, hk]
  · simp only [hpn, ↓reduceDIte]
    have h := BaseField.twoAdicGen_pow (F := F) (n - p) p (by omega)
    rw [Nat.sub_add_cancel hp] at h
    rw [pow_mul, lift, lift, ← map_pow, ← map_pow, ← pow_mul, pow_mul, h, map_pow]

/-- An index below `2 ^ m`, reduced. -/
def finMod (m r : Nat) : Fin (2 ^ m) := ⟨r % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- The points of the `p`-th subdomain at an index below its size. -/
theorem subdomain_finMod (n : Nat) (hn : n ≤ twoAdicity F) (p : Nat) (hp : p ≤ n) (r : Nat)
    (hr : r < 2 ^ (n - p)) :
    (cosetDomain (EF := EF) n hn).subdomain p (finMod (n - p) r) =
      lift gen ^ 2 ^ p * lift (twoAdicGen (n - p) ^ r) := by
  rw [subdomain_apply n hn p hp, finMod, Fin.val_mk, Nat.mod_eq_of_lt hr, lift_pow]

theorem natDegree_comp_C_mul_X (q : 𝕂[X]) (s : 𝕂) :
    (q.comp (Polynomial.C s * Polynomial.X)).natDegree ≤ q.natDegree :=
  natDegree_comp_le.trans ((Nat.mul_le_mul_left _
    ((natDegree_C_mul_le _ _).trans natDegree_X_le)).trans (Nat.mul_one _).le)

/-- **Plonky3's fold is ArkLib's.** A group of `2 ^ la` values at the folded index `i` of a word
`f` on the `p`-th subdomain, of size `2 ^ (lF + la)`, in bit-reversed order (entry `k` of the group
is the word at `rev (i 2 ^ la + k)`), folds by `foldRow` at `β` to ArkLib's fold of `f` at
`s β`, `s = g ^ 2 ^ p` the subdomain's shift, at the group's `2 ^ la`-th power. -/
theorem toSpec_foldRow_eq_foldValue (n : Nat) (hn : n ≤ twoAdicity F) (p lF la : Nat)
    (hm : n - p = lF + la) (hp : p ≤ n) (f : Fin (2 ^ (n - p)) → 𝕂) (i : Nat)
    (beta : EF) (gy : Nat → EF)
    (hgy : ∀ k < 2 ^ la, Challenge.toSpec (gy k) =
      f (finMod (n - p) (reverseBits (i * 2 ^ la + k) (n - p))))
    (pos : Nat) (hpos : pos < 2 ^ la) :
    Challenge.toSpec (foldRow i lF la beta ((List.range (2 ^ la)).map gy)) =
      ProximityGap.foldValue ((cosetDomain (EF := EF) n hn).subdomain p) f la
        (lift gen ^ 2 ^ p * Challenge.toSpec beta)
        ((cosetDomain (EF := EF) n hn).subdomain p
          (finMod (n - p) (reverseBits (i * 2 ^ la + pos) (n - p))) ^ 2 ^ la) := by
  set D := (cosetDomain (EF := EF) n hn).subdomain p
  set s : 𝕂 := lift gen ^ 2 ^ p
  set start := powF (twoAdicGen (F := F) (lF + la)) (reverseBits i lF) with hstart
  have h24 : lF + la ≤ twoAdicity F := by omega
  have hgx : ∀ k < 2 ^ la, start * powF (twoAdicGen la) (reverseBits k la) =
      twoAdicGen (lF + la) ^ reverseBits (i * 2 ^ la + k) (lF + la) := fun k hk ↦ by
    rw [hstart, powF_eq, powF_eq, twoAdicGen_pow_concat la lF i k h24 hk]
  -- The group's points on the subdomain.
  have hpt : ∀ k < 2 ^ la, D (finMod (n - p) (reverseBits (i * 2 ^ la + k) (n - p))) =
      s * lift (start * powF (twoAdicGen la) (reverseBits k la)) := fun k hk ↦ by
    rw [subdomain_finMod n hn p hp _ (by rw [hm]; exact reverseBits_lt _ _), hm,
      hgx k hk]
  have hpow : ∀ k < 2 ^ la, D (finMod (n - p) (reverseBits (i * 2 ^ la + k) (n - p))) ^ 2 ^ la =
      (s * lift start) ^ 2 ^ la := fun k hk ↦ by
    rw [hpt k hk, lift_mul, ← mul_assoc, mul_pow, powF_eq, lift_pow, ← pow_mul, Nat.mul_comm,
      pow_mul,
      (isPrimitiveRoot_algebraMap (EF := EF) la (by omega)).pow_eq_one, one_pow,
      mul_one]
  set y := D (finMod (n - p) (reverseBits (i * 2 ^ la + pos) (n - p))) ^ 2 ^ la with hy
  set I := Lagrange.interpolate (Domain.CosetFftDomainClass.blockIdx D la y) (⇑D) f
  have hinjD : Set.InjOn (⇑D) (Domain.CosetFftDomainClass.blockIdx D la y : Set _) :=
    fun a _ b _ h ↦ Domain.CosetFftDomainClass.injective D h
  rw [ProximityGap.foldValue_def']
  have hs0 : s ≠ 0 := pow_ne_zero _ lift_gen_ne_zero
  have hstart0 : start ≠ 0 := by
    rw [hstart, powF_eq]; exact twoAdicGen_pow_ne_zero _ (by omega) _
  unfold foldRow
  dsimp only
  rw [toSpec_lagrange (2 ^ la) (fun k ↦ start * powF (twoAdicGen la) (reverseBits k la))
    gy beta (I.comp (Polynomial.C s * Polynomial.X))]
  · rw [eval_comp, eval_mul, eval_C, eval_X]
  · exact groupPoints_injective la start (by omega) hstart0
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
  have h := reverseBits_concat p (n - p) (I >>> p) (I % 2 ^ p)
    (Nat.mod_lt _ (Nat.two_pow_pos p))
  rw [← hsplit, Nat.sub_add_cancel hp] at h
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt (reverseBits_lt _ _)]

/-- The `2 ^ p`-th power of the point of `L` at `rev I` is the point of the `p`-th subdomain at the
reversal of `I`'s high bits: Plonky3's index `I >>> p` at height `n - p`. -/
theorem domain_pow_eq (n : Nat) (hn : n ≤ twoAdicity F) (p : Nat) (hp : p ≤ n) (I : Nat) :
    cosetDomain (EF := EF) n hn (finMod n (reverseBits I n)) ^ 2 ^ p =
      (cosetDomain (EF := EF) n hn).subdomain p
        (finMod (n - p) (reverseBits (I >>> p) (n - p))) := by
  rw [subdomain_finMod n hn p hp _ (reverseBits_lt _ _), cosetDomain_apply, finMod,
    Fin.val_mk, Nat.mod_eq_of_lt (reverseBits_lt _ _), ← reverseBits_mod I n p hp,
    mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  congr 1
  have h := BaseField.twoAdicGen_pow (F := F) (n - p) p (by omega)
  rw [Nat.sub_add_cancel hp] at h
  have hord := (isPrimitiveRoot_algebraMap (EF := EF) (n - p) (by omega)).pow_eq_one
  rw [← lift_pow, h, lift_pow]
  conv_lhs => rw [← Nat.div_add_mod (reverseBits I n) (2 ^ (n - p)), pow_add, pow_mul, hord,
    one_pow, one_mul]


end CompStark.Ni
