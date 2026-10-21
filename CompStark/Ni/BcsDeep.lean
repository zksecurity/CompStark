/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsFri
public import CompStark.Ni.BcsCheck

/-! # The batched DEEP word at a query

The trace and quotient words extracted from a cache (`traceWords`, `quotientWords`: column `j`
at the point of `L` of index `z` is entry `j` of leaf `rev z`), and `deepWord_eq`: if a query's
input rows at `index` pass the verifier's checks against binding commitments, `reduceQuery`'s
batched quotient is the DEEP word of the extracted words and the proof's opened values at the
query's point `rev index`, with the verifier's batching challenge.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable (S : Iop.Setup EF) (cache : Merkle.Cache F (Digest F))

/-- Column `j` of the base-field matrices committed under `root`, at the point of `L` of index
`z`: entry `j` of the extracted leaf `rev z`, zero where nothing is extracted. -/
noncomputable def committedColumn (root : Digest F) (j : Nat) (z : S.Point) : F :=
  ((leafRow cache S.logSize (reverseBits z.val S.logSize) root).getD j 0)

/-- The trace words committed under the proof's trace commitment. -/
noncomputable def traceWords (proof : Proof F EF) : Fin S.air.width → S.Point → F :=
  fun j ↦ committedColumn S cache proof.traceCommit j

/-- The quotient chunks' coordinate words committed under the proof's quotient commitment: chunk
`c`'s coordinate `e` is column `d c + e`. -/
noncomputable def quotientWords (proof : Proof F EF) :
    Fin S.chunks → Fin (Challenge.d EF) → S.Point → F :=
  fun c e ↦ committedColumn S cache proof.quotientCommit (Challenge.d EF * c.val + e.val)

/-! ### Sums -/

/-- `∑ₖ aᵏ vₖ` from index `i` on is `aⁱ` times Horner's rule. -/
theorem sum_zipIdx_pow (a : 𝕂) :
    ∀ (l : List 𝕂) (i : Nat), ((l.zipIdx i).map fun p ↦ a ^ p.2 * p.1).sum =
      a ^ i * l.foldr (fun v acc ↦ v + a * acc) 0
  | [], _ => by simp only [List.zipIdx_nil, List.map_nil, List.sum_nil, List.foldr_nil, mul_zero]
  | v :: l, i => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_pow a l (i + 1),
      List.foldr_cons, pow_succ]
    ring

/-- `reduceQuery`'s accumulation is Horner's rule over the terms. -/
theorem toSpec_accTerms (alpha : EF) (x : F) :
    ∀ (terms : List ((F × EF) × EF)) (ap acc : EF),
      Challenge.toSpec (accTerms alpha x terms (ap, acc)).2 =
        Challenge.toSpec acc + Challenge.toSpec ap *
          (terms.map fun t ↦ (Challenge.toSpec t.1.2 - lift t.1.1) *
            (Challenge.toSpec t.2 - lift x)⁻¹).foldr
              (fun v acc ↦ v + Challenge.toSpec alpha * acc) 0
  | [], ap, acc => by
    simp only [accTerms, List.foldl_nil, List.map_nil, List.foldr_nil, mul_zero, add_zero]
  | t :: terms, ap, acc => by
    have h := toSpec_accTerms alpha x terms (ap * alpha)
      (acc + ap * (t.1.2 - Ext.ofBase t.1.1) * (t.2 - Ext.ofBase x)⁻¹)
    simp only [accTerms, List.foldl_cons, ptBody] at h ⊢
    rw [h, List.map_cons, List.foldr_cons]
    simp only [Challenge.toSpec_add, Challenge.toSpec_mul, Challenge.toSpec_sub,
      Challenge.toSpec_inv, Challenge.toSpec_ofBase']
    ring

/-! ### Lists -/

theorem map_zip_eq_range {α β γ : Type*} (a : List α) (b : List β) (w : Nat)
    (ha : a.length = w) (hb : b.length = w) (f : α × β → γ) (da : α) (db : β) :
    (a.zip b).map f = (List.range w).map fun j ↦ f (a.getD j da, b.getD j db) := by
  refine List.ext_getElem (by rw [List.length_map, List.length_zip, List.length_map,
    List.length_range, ha, hb, Nat.min_self]) fun i h1 h2 ↦ ?_
  have hi : i < w := by rw [List.length_map, List.length_range] at h2; exact h2
  rw [List.getElem_map, List.getElem_zip, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem flatMap_zip_eq_range {α β γ : Type*} (a : List α) (b : List β) (w : Nat)
    (ha : a.length = w) (hb : b.length = w) (f : α × β → List γ) (da : α) (db : β) :
    (a.zip b).flatMap f = (List.range w).flatMap fun j ↦ f (a.getD j da, b.getD j db) := by
  rw [List.flatMap_def, List.flatMap_def, map_zip_eq_range a b w ha hb f da db]

theorem map_finRange_eq_range {γ : Type*} (w : Nat) (f : Nat → γ) :
    (List.finRange w).map (fun j ↦ f j.val) = (List.range w).map f := by
  refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_finRange,
    List.length_range]) fun i h1 h2 ↦ ?_
  rw [List.getElem_map, List.getElem_map, List.getElem_finRange, List.getElem_range]
  rfl

theorem toList_getD {α : Type*} (a : Array α) (j : Nat) (d : α) :
    a.toList.getD j d = a.getD j d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

theorem flatMap_finRange_eq_range {γ : Type*} (w : Nat) (f : Nat → List γ) :
    (List.finRange w).flatMap (fun j ↦ f j.val) = (List.range w).flatMap f := by
  rw [List.flatMap_def, List.flatMap_def, map_finRange_eq_range]

theorem getD_flatten_of_length (w : Nat) (L : List (List F)) (hL : ∀ l ∈ L, l.length = w) :
    ∀ (c e : Nat), c < L.length → e < w →
      L.flatten.getD (w * c + e) 0 = (L.getD c []).getD e 0 := by
  induction L with
  | nil => intro c e hc; exact absurd hc (Nat.not_lt_zero _)
  | cons l L ih =>
    intro c e hc he
    have hl := hL l List.mem_cons_self
    rw [List.flatten_cons]
    cases c with
    | zero =>
      rw [List.getD_append _ _ _ _ (by rw [hl]; omega), List.getD_cons_zero, Nat.mul_zero,
        Nat.zero_add]
    | succ c =>
      rw [List.getD_append_right _ _ _ _ (by rw [hl, Nat.mul_succ]; omega), hl,
        show w * (c + 1) + e - w = w * c + e by rw [Nat.mul_succ]; omega, List.getD_cons_succ]
      exact ih (fun l' h ↦ hL l' (List.mem_cons_of_mem _ h)) c e
        (by simp only [List.length_cons] at hc; omega) he

/-! ### The DEEP word -/

/-- An opened row at `index` that binds is the committed column at the query's point. -/
theorem committedColumn_eq (root : Digest F) (index : Nat) (hidx : index < 2 ^ S.logSize)
    (row : List F) (h : Merkle.extractRow cache S.logSize index root = some row) (j : Nat) :
    committedColumn S cache root j (finMod S.logSize (reverseBits index S.logSize)) =
      (row.getD j 0) := by
  rw [committedColumn, finMod_val (reverseBits_lt _ _),
    reverseBits_reverseBits hidx, leafRow, h, Option.getD_some]

/-- The point of `L` of index `rev index` is the verifier's query point. -/
theorem domain_finMod (index : Nat) :
    S.domain (finMod S.logSize (reverseBits index S.logSize)) =
      lift (gen * powF (twoAdicGen S.logSize) (reverseBits index S.logSize)) := by
  rw [show S.domain = cosetDomain S.logSize S.valid.twoAdic from rfl, cosetDomain_apply,
    finMod_val (reverseBits_lt _ _), lift_mul, powF_eq, lift_pow]

/-- **The batched DEEP word at a query.** If a query's input rows at `index` against the
verifier's rounds pass their checks (`BatchOk`), on a proof of the expected shape whose trace and
quotient commitments bind, `reduceQuery`'s batched quotient at the batching challenge `a` is the
DEEP word of the extracted trace and quotient words and the opened values at `rev index`. -/
theorem deepWord_eq (H : Primitives F Id) (proof : Proof F EF) (zeta a : EF) (α : 𝕂)
    (hdb : proof.degreeBits = S.logN)
    (htl : proof.opened.traceLocal.size = S.air.width)
    (htn : proof.opened.traceNext.size = S.air.width)
    (hqc : proof.opened.quotientChunks.size = S.chunks)
    (hq4 : ∀ ch ∈ proof.opened.quotientChunks, ch.size = Challenge.d EF)
    (hbT : Binding cache H proof.traceCommit) (hbQ : Binding cache H proof.quotientCommit)
    (inputs : List (List (Array F))) (index : Nat) (hidx : index < 2 ^ S.logSize)
    (hlen : inputs.length = (vRounds proof zeta).length)
    (hok : ∀ x ∈ inputs.zip (vRounds proof zeta), BatchOk H S.logSize index x) :
    Iop.deepWord (fixedProver (traceWords S cache proof) (quotientWords S cache proof)
        (openingsOf S proof.opened)) α (Challenge.toSpec zeta) (Challenge.toSpec a)
        (finMod S.logSize (reverseBits index S.logSize)) =
      Challenge.toSpec (accTerms a (gen * powF (twoAdicGen S.logSize) (reverseBits index S.logSize))
        (inputTerms (inputs.zip (vRounds proof zeta))) (1, 0)).2 := by
  set n := S.logSize
  set x : F := gen * powF (twoAdicGen n) (reverseBits index n)
  set z0 : S.Point := finMod n (reverseBits index n)
  set o := proof.opened
  set td : Domain F := ⟨1, proof.degreeBits⟩
  set mT : List (Domain F × List (EF × List EF)) := [(td, [(zeta, o.traceLocal.toList),
    (zeta * Ext.ofBase (twoAdicGen proof.degreeBits), o.traceNext.toList)])] with hmT
  set mQ : List (Domain F × List (EF × List EF)) :=
    o.quotientChunks.toList.map fun ch ↦ (td, [(zeta, ch.toList)]) with hmQ
  have hrounds : vRounds proof zeta = [(proof.traceCommit, mT), (proof.quotientCommit, mQ)] :=
    rfl
  rw [hrounds] at hlen hok ⊢
  obtain ⟨bT, bQ, rfl⟩ : ∃ bT bQ, inputs = [bT, bQ] := by
    match inputs, hlen with
    | [bT, bQ], _ => exact ⟨bT, bQ, rfl⟩
  have hz : [bT, bQ].zip [(proof.traceCommit, mT), (proof.quotientCommit, mQ)] =
      [(bT, (proof.traceCommit, mT)), (bQ, (proof.quotientCommit, mQ))] := rfl
  rw [hz] at hok ⊢
  obtain ⟨-, ⟨pT, hvT⟩, hsT, hwT⟩ := hok _ List.mem_cons_self
  obtain ⟨hneQ, ⟨pQ, hvQ⟩, hsQ, hwQ⟩ := hok _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at hvT hsT hwT hneQ hvQ hsQ hwQ
  -- The trace batch: one row of the trace's width, extracted.
  obtain ⟨rowT, hrowT⟩ : ∃ rowT, bT = [rowT] :=
    List.length_eq_one_iff.mp (by rw [hsT]; rfl)
  rw [hrowT] at hvT hwT
  have hwidth : rowT.size = S.air.width := by
    have := hwT (rowT, mT.head (List.cons_ne_nil _ _)) List.mem_cons_self
      (zeta, o.traceLocal.toList) List.mem_cons_self
    rw [← this, Array.length_toList, htl]
  have hexT := hbT _ _ _ _ _ Nat.one_pos hvT
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil] at hexT
  -- The quotient batch: a row of `d` coordinates per chunk, extracted.
  have hlenQ : bQ.length = S.chunks := by
    rw [hsQ, hmQ, List.length_map, Array.length_toList, hqc]
  have h4 : ∀ c < S.chunks, (bQ.getD c #[]).size = Challenge.d EF := by
    intro c hc
    have hc' : c < bQ.length := by rw [hlenQ]; exact hc
    have hcq : c < o.quotientChunks.size := by rw [hqc]; exact hc
    have hcm : c < mQ.length := by rw [hmQ, List.length_map, Array.length_toList]; exact hcq
    have hmem : (bQ[c], mQ[c]) ∈ bQ.zip mQ := by
      rw [List.mem_iff_getElem]
      exact ⟨c, by rw [List.length_zip]; omega, by rw [List.getElem_zip]⟩
    have := hwQ _ hmem (zeta, (o.quotientChunks[c]'hcq).toList) (by
      simp only [hmQ, List.getElem_map, Array.getElem_toList, List.mem_cons, List.not_mem_nil,
        or_false])
    rw [List.getD_eq_getElem _ _ hc', ← this, Array.length_toList]
    exact hq4 _ (Array.getElem_mem hcq)
  have hexQ := hbQ _ _ _ _ _ (List.length_pos_of_ne_nil hneQ) hvQ
  -- The extracted words at the query's point.
  have hTw : ∀ j, traceWords S cache proof j z0 = (rowT.toList.getD j 0) :=
    fun j ↦ committedColumn_eq S cache _ index hidx _ hexT j
  have hQw : ∀ (c : Fin S.chunks) (e : Fin (Challenge.d EF)), quotientWords S cache proof c e z0 =
      ((bQ.getD c #[]).toList.getD e 0) := by
    intro c e
    have hc : c.val < bQ.length := by rw [hlenQ]; exact c.isLt
    have hmap : (bQ.map (·.toList)).getD c [] =
        (bQ.getD c #[]).toList := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hc), List.getElem_map,
        List.getD_eq_getElem _ #[] hc]
    have hall : ∀ l ∈ bQ.map (·.toList), l.length = Challenge.d EF := by
      intro l hl
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      rw [Array.length_toList, ← List.getD_eq_getElem _ #[] hi]
      exact h4 i (by rw [← hlenQ]; exact hi)
    rw [quotientWords, committedColumn_eq S cache _ index hidx _ hexQ,
      getD_flatten_of_length _ _ hall _ _ (by rw [List.length_map]; exact hc) e.isLt, hmap]
  -- Both sides by Horner's rule in the batching challenge.
  have hlhs : ∀ l : List ((S.Point → F) × 𝕂 × 𝕂), (l.zipIdx.map fun ((f, z, y), k) ↦
      Challenge.toSpec a ^ k * (y - algebraMap F 𝕂 (f z0)) / (z - S.domain z0)).sum =
      (l.map fun w ↦ (w.2.2 - algebraMap F 𝕂 (w.1 z0)) / (w.2.1 - S.domain z0)).foldr
        (fun v acc ↦ v + Challenge.toSpec a * acc) 0 := by
    intro l
    rw [← one_mul (List.foldr _ 0 _), ← pow_zero (Challenge.toSpec a), ← sum_zipIdx_pow _ _ 0,
      List.zipIdx_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun p _ ↦ ?_)
    obtain ⟨⟨f, z, y⟩, k⟩ := p
    simp only [Function.comp_apply, Prod.map, id, mul_div_assoc]
  rw [Iop.deepWord, hlhs, toSpec_accTerms, Challenge.toSpec_zero, Challenge.toSpec_one, zero_add,
    one_mul]
  refine congrArg (List.foldr _ 0) ?_
  have hD : S.domain z0 = lift x := domain_finMod S index
  have hterms : inputTerms [(bT, (proof.traceCommit, mT)), (bQ, (proof.quotientCommit, mQ))] =
      ((rowT.toList.zip o.traceLocal.toList).map fun pp ↦ (pp, zeta)) ++
      ((rowT.toList.zip o.traceNext.toList).map fun pp ↦
        (pp, zeta * Ext.ofBase (twoAdicGen proof.degreeBits))) ++
      batchTerms (bQ.zip mQ) := by
    simp only [inputTerms, batchTerms, hrowT, hmT, List.zip_cons_cons, List.zip_nil_right,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rw [hterms, openedWords]
  simp only [List.map_append]
  have hw1 : rowT.toList.length = S.air.width := by rw [Array.length_toList, hwidth]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
  · rw [List.map_map, List.map_map, map_zip_eq_range _ _ S.air.width hw1
      (by rw [Array.length_toList, htl]) _ 0 0,
      ← map_finRange_eq_range]
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp_apply, fixedProver, openingsOf, hTw, toList_getD, hD,
      div_eq_mul_inv]
  · rw [List.map_map, List.map_map, map_zip_eq_range _ _ S.air.width hw1
      (by rw [Array.length_toList, htn]) _ 0 0,
      ← map_finRange_eq_range]
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp_apply, fixedProver, openingsOf, hTw, toList_getD, hD,
      div_eq_mul_inv, Challenge.toSpec_mul, Challenge.toSpec_ofBase', hdb]
    rfl
  · rw [List.map_flatMap, batchTerms, List.map_flatMap,
      flatMap_zip_eq_range _ _ S.chunks hlenQ
        (by rw [hmQ, List.length_map, Array.length_toList, hqc]) _ #[] (td, [])]
    rw [show (fun c : Fin S.chunks ↦ ((List.finRange (Challenge.d EF)).map fun e ↦
        ((fixedProver (traceWords S cache proof) (quotientWords S cache proof)
          (openingsOf S o)).quotient α c e, Challenge.toSpec zeta,
          ((fixedProver (traceWords S cache proof) (quotientWords S cache proof)
          (openingsOf S o)).openings α (Challenge.toSpec zeta)).quotientAt c e)).map
        fun w ↦ (w.2.2 - algebraMap F 𝕂 (w.1 z0)) / (w.2.1 - S.domain z0)) =
      fun c : Fin S.chunks ↦ (List.range (Challenge.d EF)).map fun e ↦
        (Challenge.toSpec (((o.quotientChunks.getD c #[]).getD e 0)) - algebraMap F 𝕂
          (((bQ.getD c #[]).toList.getD e 0))) /
          (Challenge.toSpec zeta - S.domain z0) from funext fun c ↦ by
        rw [List.map_map, ← map_finRange_eq_range]
        refine List.map_congr_left fun e _ ↦ ?_
        simp only [Function.comp_apply, fixedProver, openingsOf, hQw]]
    refine (flatMap_finRange_eq_range S.chunks (fun c ↦ (List.range (Challenge.d EF)).map fun e ↦
        (Challenge.toSpec (((o.quotientChunks.getD c #[]).getD e 0)) - algebraMap F 𝕂
          (((bQ.getD c #[]).toList.getD e 0))) /
          (Challenge.toSpec zeta - S.domain z0))).trans ?_
    rw [List.flatMap_def, List.flatMap_def]
    refine congrArg List.flatten (List.map_congr_left fun c hc ↦ ?_)
    have hc := List.mem_range.mp hc
    have hcq : c < o.quotientChunks.size := by rw [hqc]; exact hc
    have hmc : mQ.getD c (td, []) = (td, [(zeta, (o.quotientChunks.getD c #[]).toList)]) := by
      rw [hmQ, List.getD_eq_getElem _ _ (by rw [List.length_map, Array.length_toList]; exact hcq),
        List.getElem_map, Array.getElem_toList, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hcq, Option.getD_some]
    rw [hmc]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    rw [map_zip_eq_range _ _ (Challenge.d EF) (by rw [Array.length_toList]; exact h4 c hc)
      (by rw [Array.length_toList]; exact hq4 _ (by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hcq, Option.getD_some]
        exact Array.getElem_mem hcq)) _ 0 0]
    refine List.map_congr_left fun e _ ↦ ?_
    simp only [Function.comp_apply, toList_getD, hD, div_eq_mul_inv]

end CompStark.Ni
