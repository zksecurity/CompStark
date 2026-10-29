/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsCheck
public import CompStark.Ni.BatchDeep

/-! # The batch verifier's instance check in the spec field

The batch verifier checks every instance's constraints and then its LogUp constraints at `ζ`
(`instanceCheck`), over Plonky3's fast extension, the permutation trace's columns recombined from
their opened base coordinates (`unflattenAt`), with the instance's lookup challenges from the
batch's pair (`challengeLayout`) and its terminal. `constraintsHoldAt_of_instanceCheck`: it gives
`ConstraintsHoldAt` of the instance, with the lookup challenges `Setup.challenges` of the spec
images of `(α_L, β_L)` (`challenges_eq`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.Lookup Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

section Env
variable {lookups : List (Stark.Lookup F)} (T : Iop.Setup EF lookups) (pis : List F)
  (o : OpenedValues EF) (cur next : Array EF) (zeta : EF)

/-- A constraint's value on the verifier's environment at `ζ` is its value on the spec
environment of the openings. -/
theorem toSpec_eval_outOfDomainEnv (e : Expr F)
    (he : e.colsBelow T.air.width T.air.mainNextWidth T.air.preprocessedWidth
      T.air.preprocessedNextWidth = true) :
    Challenge.toSpec (e.eval (outOfDomainEnv T.air pis o T.logN zeta)) =
      e.eval (envAt T pis (Challenge.toSpec zeta) (openingsOf T o cur next)) := by
  have hzh : vanishing 1 T.n (Challenge.toSpec zeta) = Challenge.toSpec zeta ^ 2 ^ T.logN - 1 := by
    rw [vanishing, div_one]
  have hlast : Challenge.toSpec (Ext.ofBase (twoAdicGen T.logN)⁻¹ : EF) =
      (rootOfUnity T.logN : 𝕂)⁻¹ := by
    rw [Challenge.toSpec_ofBase, ← CompPoly.Extension.Ext.algebraMap_eq_ofBase, map_inv₀]
    rfl
  refine Expr.eval_hom Challenge.toSpec Challenge.toSpec_add Challenge.toSpec_sub
    Challenge.toSpec_mul T.air.width T.air.mainNextWidth T.air.preprocessedWidth
    T.air.preprocessedNextWidth _ _ (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
    (fun j hj ↦ ?_) (fun j ↦ ?_) (fun j ↦ ?_) (fun x ↦ ?_) ?_ ?_ ?_ e he
  · simp only [envAt, hj, ↓reduceDIte]; rfl
  · simp only [envAt, hj, ↓reduceDIte]; rfl
  · simp only [envAt, hj, ↓reduceDIte]; rfl
  · simp only [envAt, hj, ↓reduceDIte]; rfl
  · exact toSpec_periodicAt _ T.logN (periodShape_of_fits T.air T.logN T.valid.periodicFits j)
      ((Nat.le_add_right _ _).trans T.valid.twoAdic) zeta
  · simp only [envAt, outOfDomainEnv, Challenge.toSpec_ofBase]; rfl
  · simp only [envAt, outOfDomainEnv, Challenge.toSpec_ofBase]; rfl
  · simp only [envAt, outOfDomainEnv, Challenge.toSpec_mul, Challenge.toSpec_inv,
      Challenge.toSpec_sub, toSpec_extPowTwo, Challenge.toSpec_one, hzh, div_eq_mul_inv]
  · simp only [envAt, outOfDomainEnv, Challenge.toSpec_mul, Challenge.toSpec_inv,
      Challenge.toSpec_sub, toSpec_extPowTwo, Challenge.toSpec_one, hzh, div_eq_mul_inv, hlast]
  · simp only [envAt, outOfDomainEnv, Challenge.toSpec_sub, hlast]

/-- A permutation column recombined from its opened coordinates is the spec column's value. -/
theorem toSpec_unflattenAt (row : Array EF) (hrow : row.size = Challenge.d EF * T.permWidth)
    (c : ℕ) :
    Challenge.toSpec (unflattenAt row c) =
      permValue (w := T.permWidth) (fun (c : Fin T.permWidth) (e : Fin (Challenge.d EF)) ↦
        Challenge.toSpec (row.getD (c.val * Challenge.d EF + e.val) 0)) c := by
  have hsum : Challenge.toSpec (unflattenAt row c) = ∑ e : Fin (Challenge.d EF),
      CompPoly.Extension.Ext.gen ^ (e : ℕ) *
        Challenge.toSpec (row.getD (c * Challenge.d EF + e) 0) := by
    rw [unflattenAt, Fin.sum_univ_def, map_finRange_eq_range (Challenge.d EF) (fun e ↦
      CompPoly.Extension.Ext.gen ^ e * Challenge.toSpec (row.getD (c * Challenge.d EF + e) 0))]
    suffices h : ∀ (l : List ℕ) (x : EF), (∀ e ∈ l, e < Challenge.d EF) →
        Challenge.toSpec (l.foldl (fun s e ↦ s + Ext.basis e * row.getD (c * Challenge.d EF + e)
          0) x) = Challenge.toSpec x + (l.map fun e ↦ CompPoly.Extension.Ext.gen ^ e *
            Challenge.toSpec (row.getD (c * Challenge.d EF + e) 0)).sum by
      rw [h _ 0 fun e he ↦ List.mem_range.mp he, Challenge.toSpec_zero, zero_add]
    intro l
    induction l with
    | nil => intro x _; simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    | cons e l ih =>
      intro x hl
      rw [List.foldl_cons, ih _ fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he'),
        Challenge.toSpec_add, Challenge.toSpec_mul, Ext.toSpec_basis (hl e List.mem_cons_self),
        List.map_cons, List.sum_cons, add_assoc]
  rw [hsum, permValue]
  split
  · rfl
  · rename_i hc
    refine Finset.sum_eq_zero fun e _ ↦ ?_
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
      rw [hrow]
      have := e.isLt
      nlinarith), Option.getD_none, Challenge.toSpec_zero, mul_zero]

/-- A LogUp constraint's value on the verifier's environment and permutation rows at `ζ` is its
value on the spec environment of the openings. -/
theorem toSpec_eval_ext (hcur : cur.size = Challenge.d EF * T.permWidth)
    (hnext : next.size = Challenge.d EF * T.permWidth) (chs : List EF) (t : EF)
    (g : ExtExpr F) (hg : g ∈ T.extConstraints) :
    Challenge.toSpec (g.eval (outOfDomainEnv T.air pis o T.logN zeta)
      ⟨unflattenAt cur, unflattenAt next, (chs.getD · 0), t⟩) =
      g.eval (envAt T pis (Challenge.toSpec zeta) (openingsOf T o cur next))
        (auxAt (chs.map Challenge.toSpec) (Challenge.toSpec t) (openingsOf T o cur next)) := by
  refine ExtExpr.eval_hom Challenge.toSpec Challenge.toSpec_add Challenge.toSpec_sub
    Challenge.toSpec_mul T.air.width T.air.mainNextWidth T.air.preprocessedWidth
    T.air.preprocessedNextWidth T.permWidth _ _ _ _
    (fun e he ↦ toSpec_eval_outOfDomainEnv T pis o cur next zeta e he) (fun c _ ↦ ?_)
    (fun c _ ↦ ?_) (fun j ↦ ?_) rfl g (colsBelow_extConstraints T g hg)
  · exact toSpec_unflattenAt T cur hcur c
  · exact toSpec_unflattenAt T next hnext c
  · show Challenge.toSpec (chs.getD j 0) = (chs.map Challenge.toSpec).getD j 0
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases chs[j]? with
    | none => exact Challenge.toSpec_zero
    | some x => rfl

end Env

theorem foldl_congr_mem {α β : Type*} {f g : α → β → α} {a b : α} :
    ∀ (l : List β), a = b → (∀ acc, ∀ x ∈ l, f acc x = g acc x) → l.foldl f a = l.foldl g b
  | [], hab, _ => hab
  | x :: l, hab, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_congr_mem l (by rw [hab, h b x List.mem_cons_self])
      fun acc y hy ↦ h acc y (List.mem_cons_of_mem _ hy)

/-- A fold by `α` in the fast extension is the fold in the spec field of the values' images. -/
theorem toSpec_foldl_horner {β : Type} (v : β → EF) (alpha : EF) :
    ∀ (l : List β) (x : EF), Challenge.toSpec (l.foldl (fun acc c ↦ acc * alpha + v c) x) =
      l.foldl (fun acc c ↦ acc * Challenge.toSpec alpha + Challenge.toSpec (v c))
        (Challenge.toSpec x)
  | [], _ => rfl
  | c :: l, x => by
    rw [List.foldl_cons, List.foldl_cons, toSpec_foldl_horner v alpha l, Challenge.toSpec_add,
      Challenge.toSpec_mul]

/-- **The instance check.** If the batch verifier's check of an instance at `ζ` passes on opened
values with its chunks and permutation rows of its permutation trace's width, its constraints
and LogUp constraints hold at `ζ` in the spec field, with the spec images of its lookup
challenges and terminal. -/
theorem constraintsHoldAt_of_instanceCheck (S : Iop.Batch.Setup EF) [S.CapFits] (i : Fin S.k) (pis : List F)
    (o : OpenedValues EF) (cur next : Array EF) (chs : List EF) (t zeta alpha : EF)
    (hqc : o.quotientChunks.size = (S.instanceSetup i).chunks)
    (hcur : cur.size = Challenge.d EF * (S.instanceSetup i).permWidth)
    (hnext : next.size = Challenge.d EF * (S.instanceSetup i).permWidth)
    (h : CompStark.Batch.instanceCheck ⟨S.air i, S.logN i, S.lookups i⟩ o pis cur next chs t zeta
        alpha =
      true) :
    ConstraintsHoldAt (S.instanceSetup i) pis (Challenge.toSpec alpha) (Challenge.toSpec zeta)
      (openingsOf (S.instanceSetup i) o cur next) (chs.map Challenge.toSpec)
      (Challenge.toSpec t) := by
  set T := S.instanceSetup i
  have hlc : (⟨S.air i, S.logN i, S.lookups i⟩ : CompStark.Batch.Instance F).logQuotientChunks =
      T.logChunks :=
    (logChunks_eq S i).symm
  rw [CompStark.Batch.instanceCheck, hlc, beq_iff_eq] at h
  have h' := congrArg Challenge.toSpec h
  have hlist : o.quotientChunks.toList =
      (List.range T.chunks).map fun c ↦ o.quotientChunks.getD c #[] := by
    refine List.ext_getElem (by rw [List.length_map, List.length_range, Array.length_toList, hqc])
      fun j h1 h2 ↦ ?_
    rw [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rwa [← Array.length_toList]), Option.getD_some]
  have h24 : T.logN + T.logChunks ≤ twoAdicity F := logN_add_logChunks_le T
  dsimp only at h'
  rw [hlist, toSpec_recompose T.logN _ h24] at h'
  rw [constraintsHoldAt_iff, ← Fin.sum_univ_eq_sum_range] at *
  rw [Challenge.toSpec_mul, toSpec_foldl_horner, foldedConstraints, toSpec_foldl_horner,
    Challenge.toSpec_inv, Challenge.toSpec_sub, toSpec_extPowTwo, Challenge.toSpec_one,
    Challenge.toSpec_zero] at h'
  have hzh : vanishing 1 T.n (Challenge.toSpec zeta) = Challenge.toSpec zeta ^ 2 ^ T.logN - 1 := by
    rw [vanishing, div_one]
  rw [hzh, div_eq_mul_inv]
  refine Eq.trans ?_ (h'.trans (Finset.sum_congr rfl fun c _ ↦ ?_))
  · congr 1
    rw [← extConstraints_eq S i]
    refine foldl_congr_mem _ (foldl_congr_mem _ rfl fun acc c hc ↦ ?_)
      fun acc g hg ↦ ?_
    · rw [toSpec_eval_outOfDomainEnv T pis o cur next zeta c (T.valid.colsInWidth c hc)]
    · rw [toSpec_eval_ext T pis o cur next zeta hcur hnext chs t g hg]
  · rw [selectorAt_eq, chunkAt_openingsOf]

end CompStark.Ni

namespace CompStark.Ni
open CompStark.Stark CompStark.Lookup

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The statement's lookups are the instances'. -/
theorem map_lookups_instances (S : Iop.Batch.Setup EF) [S.CapFits] :
    S.instances.map (·.lookups) = List.ofFn S.lookups := by
  rw [Iop.Batch.Setup.instances, List.map_ofFn]
  rfl

/-- **The lookup challenges.** The verifier's challenges of instance `i` from the pair `(α_L, β_L)`
are, in the spec field, the instance's challenges of the spec images of the pair. -/
theorem challenges_eq (S : Iop.Batch.Setup EF) [S.CapFits] (a b : EF) (i : Fin S.k) :
    ((challengeLayout (S.instances.map (·.lookups)) a b).getD i []).map Challenge.toSpec =
      S.challenges (Challenge.toSpec a) (Challenge.toSpec b) i := by
  rw [map_lookups_instances, challengeLayout, Iop.Batch.Setup.challenges]
  have hget : ((busIds (List.ofFn S.lookups)).map fun ids ↦ ids.flatMap fun b' ↦
      [a + Ext.ofBase ((b' + 1 : ℕ) : F) * Ext.pow b (maxWidth (List.ofFn S.lookups).flatten), b]
      ).getD i [] = ((busIds (List.ofFn S.lookups)).getD i []).flatMap fun b' ↦
      [a + Ext.ofBase ((b' + 1 : ℕ) : F) * Ext.pow b (maxWidth (List.ofFn S.lookups).flatten),
        b] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases (busIds (List.ofFn S.lookups))[i.val]? with
    | none => rfl
    | some ids => rfl
  rw [hget, List.map_flatMap]
  refine List.flatMap_congr fun b' _ ↦ ?_
  simp only [List.map_cons, List.map_nil, Challenge.toSpec_add, Challenge.toSpec_mul,
    Challenge.toSpec_ofBase', Ext.toSpec_pow]

end CompStark.Ni
