/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Rbr
public import CompStark.Complete.Quotient

/-! # The verifier's constraint check in the spec field

The verifier checks the constraints at `ζ` over Plonky3's fast extension (`checkConstraints`,
`recompose`). The interactive oracle proof states the same check over the spec field
(`ConstraintsHoldAt`). `constraintsHoldAt_of_check`: the verifier's check on the proof's opened
values gives `ConstraintsHoldAt` on them (`openingsOf`), at the spec images of `α` and `ζ`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop Polynomial Montgomery.Native32
open KoalaBear.Fast (Ext4)

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4
local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => Challenge.Spec KoalaBear.Fast.Ext4

/-- The opened values of a proof as the interactive oracle proof's openings, in the spec field. -/
noncomputable def openingsOf (S : Iop.Setup KoalaBear.Fast.Ext4) (o : OpenedValues) :
    Openings S where
  traceAt j := Ext4.toSpec (o.traceLocal.getD j 0)
  traceNext j := Ext4.toSpec (o.traceNext.getD j 0)
  quotientAt c e := Ext4.toSpec ((o.quotientChunks.getD c #[]).getD e 0)

/-- A product over the chunks other than `c`, as a product over the range. -/
theorem prod_fin_ne {M : Type*} [CommMonoid M] (n : Nat) (f : Nat → M) (c : Fin n) :
    ∏ d : Fin n with d ≠ c, f d.val = ∏ d ∈ (Finset.range n).erase c.val, f d := by
  rw [Finset.prod_filter, ← Finset.filter_ne' (Finset.range n) c.val, Finset.prod_filter]
  rw [← Fin.prod_univ_eq_prod_range (fun d ↦ if d ≠ c.val then f d else 1) n]
  refine Finset.prod_congr rfl fun d _ ↦ ?_
  simp only [ne_eq, Fin.val_eq_val]

/-- The spec selector of chunk `c` is the verifier's (`chunkSel`). -/
theorem selectorAt_eq (S : Iop.Setup KoalaBear.Fast.Ext4) (ζ : 𝕂) (c : Fin S.chunks) :
    selectorAt S ζ c = chunkSel S.logN S.air.logQuotientChunks c.val ζ := by
  have hs : ∀ d : Nat, chunkShift S d =
      algebraMap 𝔽 𝕂 (qpt (S.logN + S.air.logQuotientChunks) d) := fun d ↦ by
    rw [chunkShift, rootOfUnity, lift, lift, qpt, map_mul, map_pow]
  have hv : ∀ (d : Nat) (x : 𝕂), vanishing (chunkShift S d) S.n x =
      vanish S.logN (qpt (S.logN + S.air.logQuotientChunks) d) x := fun d x ↦ by
    rw [vanishing, vanish, hs, div_eq_mul_inv, map_inv₀]
    rfl
  unfold selectorAt chunkSel
  rw [← prod_fin_ne]
  refine Finset.prod_congr rfl fun d _ ↦ ?_
  rw [hv, hv, hs, div_eq_mul_inv]
  rfl

/-- The spec value of chunk `c` is the verifier's (`chunkInner`). -/
theorem chunkAt_openingsOf (S : Iop.Setup KoalaBear.Fast.Ext4) (o : OpenedValues)
    (c : Fin S.chunks) :
    chunkAt (openingsOf S o) c = Ext4.toSpec (chunkInner (o.quotientChunks.getD c #[])) := by
  rw [toSpec_chunkInner, chunkAt, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [← KoalaBear.toSpec_ext4, Ext.toSpec_basis e.isLt]
  rfl

/-- **The constraint check.** If the verifier's check at `ζ` passes on opened values with
`2 ^ logQuotientChunks` chunks, the constraints hold at `ζ` in the spec field. -/
theorem constraintsHoldAt_of_check (S : Iop.Setup KoalaBear.Fast.Ext4) (pis : List F)
    (o : OpenedValues)
    (zeta alpha : EF) (hqc : o.quotientChunks.size = S.chunks)
    (h : checkConstraints S.air pis o S.logN zeta alpha
      (recompose (chunkDomains S.logN S.air.logQuotientChunks) o.quotientChunks.toList zeta) =
        true) :
    ConstraintsHoldAt S pis (Ext4.toSpec alpha) (Ext4.toSpec zeta) (openingsOf S o) := by
  rw [checkConstraints_eq_fun] at h
  have h' := congrArg Ext4.toSpec (beq_iff_eq.mp h)
  have hlist : o.quotientChunks.toList =
      (List.range S.chunks).map fun c ↦ o.quotientChunks.getD c #[] := by
    refine List.ext_getElem (by rw [List.length_map, List.length_range, Array.length_toList, hqc])
      fun i h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rwa [← Array.length_toList]), Option.getD_some]
  have h24 : S.logN + S.air.logQuotientChunks ≤ 24 := by
    have := S.valid.twoAdic; have := S.valid.chunksFit; omega
  rw [hlist, toSpec_recompose S.logN _ h24] at h'
  rw [constraintsHoldAt_iff, ← Fin.sum_univ_eq_sum_range] at *
  rw [Ext4.toSpec_mul, toSpec_foldedConstraints, Ext4.toSpec_inv, Ext4.toSpec_sub,
    toSpec_extPowTwo, Ext4.toSpec_one] at h'
  have hzh : @vanishing EF _ 1 S.n (Ext4.toSpec zeta) = Ext4.toSpec zeta ^ 2 ^ S.logN - 1 := by
    rw [vanishing, div_one]
  have henv : (S.air.constraints.map fun c ↦ Ext4.toSpec (c.eval {
      cur := fun i ↦ o.traceLocal.getD i 0
      next := fun i ↦ o.traceNext.getD i 0
      pub := fun i ↦ Ext.ofBase (pis.getD i 0)
      const := Ext.ofBase
      isFirstRow := (Ext.powTwo zeta S.logN - 1) * (zeta - 1)⁻¹
      isLastRow := (Ext.powTwo zeta S.logN - 1) * (zeta - Ext.ofBase (twoAdicGen S.logN)⁻¹)⁻¹
      isTransition := zeta - Ext.ofBase (twoAdicGen S.logN)⁻¹ })) =
      S.air.constraints.map fun c ↦ c.eval (envAt S pis (Ext4.toSpec zeta) (openingsOf S o)) := by
    refine List.map_congr_left fun c hc ↦ ?_
    have hlast : Ext4.toSpec (Ext.ofBase (twoAdicGen S.logN)⁻¹) = (@rootOfUnity EF _ S.logN)⁻¹ := by
      rw [KoalaBear.toSpec_ofBase_ext4, toField_inv, ← CompPoly.Extension.Ext.algebraMap_eq_ofBase,
        map_inv₀]
      rfl
    refine Expr.eval_hom Ext4.toSpec Ext4.toSpec_add Ext4.toSpec_sub Ext4.toSpec_mul S.air.width
      _ _ (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j ↦ ?_) (fun x ↦ ?_) ?_ ?_ ?_ c
      (S.valid.colsInWidth c hc)
    · simp only [envAt, hj, ↓reduceDIte]; rfl
    · simp only [envAt, hj, ↓reduceDIte]; rfl
    · simp only [envAt, KoalaBear.toSpec_ofBase_ext4]; rfl
    · simp only [envAt, KoalaBear.toSpec_ofBase_ext4]; rfl
    · simp only [envAt, Ext4.toSpec_mul, Ext4.toSpec_inv, Ext4.toSpec_sub,
        toSpec_extPowTwo, Ext4.toSpec_one, hzh, div_eq_mul_inv]
    · simp only [envAt, Ext4.toSpec_mul, Ext4.toSpec_inv, Ext4.toSpec_sub,
        toSpec_extPowTwo, Ext4.toSpec_one, hzh, div_eq_mul_inv, hlast]
    · simp only [envAt, Ext4.toSpec_sub, hlast]
  rw [henv, horner, List.foldl_map] at h'
  rw [hzh, div_eq_mul_inv]
  refine h'.trans (Finset.sum_congr rfl fun c _ ↦ ?_)
  rw [selectorAt_eq, chunkAt_openingsOf]

end CompStark.Ni
