/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Telescope
public import CompStark.Sound.LogUp
public import CompStark.Sound.Assembly
public import CompStark.BatchSoundnessError

/-! # The lookup challenges of the batch

The round of the lookup challenges `(α_L, β_L)` of the batch STARK:

* `LookupBad`: for some tuple of candidate traces satisfying every AIR but unbalanced, the pair
  makes a denominator of the batch's lookup messages vanish, or their sum of fractions
  (`LogUp.PairBad`). Every tuple of candidate traces has at most `T + (T - 1) W` bad pairs per
  `|𝕂|` (`LogUp.card_pairBad_le`), `T` the number of interactions, so the round's error is
  `lookupError` (`card_lookupBad_le`).
* `sum_terminals_eq`: if every instance's candidate trace and permutation trace satisfy all its
  constraints (`Holds`) at the pair's challenges and no message's denominator vanishes, the
  terminals of the instances with lookups sum to the sum of fractions of all messages: each
  terminal is the sum of its instance's fractions (`terminal_eq_sum`), whose denominators are
  the messages' (`instanceFractions_eq`).
-/

@[expose] public section
namespace CompStark.Sound.Batch
open CompStark.Stark CompStark.Iop CompStark.Lookup Polynomial

theorem length_flatMap_zip {F : Type} {β : Type*} (L : List (Stark.Lookup F)) (ids : List Nat)
    (h : ids.length = L.length) (f : Stark.Lookup F × Nat → List β)
    (hf : ∀ x, (f x).length = x.1.tuples.length) :
    ((L.zip ids).flatMap f).length = (L.map (·.tuples.length)).sum := by
  induction L generalizing ids with
  | nil => rfl
  | cons l L ih =>
    obtain ⟨b, ids, rfl⟩ : ∃ b ids', ids = b :: ids' := by
      cases ids with
      | nil => exact absurd h (by simp only [List.length_nil, List.length_cons]; omega)
      | cons b ids => exact ⟨b, ids, rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.flatMap_cons, List.length_append, ih ids h, hf, List.map_cons,
      List.sum_cons]

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)

/-! ### The messages, instance by instance -/

/-- The bus numbers of instance `i`'s lookups (`busIds`). -/
abbrev busNumbers (i : Fin S.k) : List Nat := (busIds (List.ofFn S.lookups)).getD i []

theorem length_busIds : (busIds (List.ofFn S.lookups)).length = S.k := by
  rw [busIds, length_busIdsFrom, List.length_ofFn]

theorem length_busNumbers (i : Fin S.k) : (busNumbers S i).length = (S.lookups i).length := by
  have hx : i.val < (busIdsFrom [] 0 (List.ofFn S.lookups)).length := by
    rw [length_busIdsFrom, List.length_ofFn]; exact i.isLt
  have hy : i.val < (List.ofFn S.lookups).length := by rw [List.length_ofFn]; exact i.isLt
  have h := (busIdsFrom_lengths [] 0 (List.ofFn S.lookups)).get hx hy
  simp only [List.get_eq_getElem, List.getElem_ofFn] at h
  rw [busNumbers, List.getD_eq_getElem _ _ (by rw [length_busIds]; exact i.isLt)]
  exact h

/-- Instance `i`'s lookup messages: for every row, lookup and tuple in turn, the lookup's bus
with the tuple's values on the row, and the tuple's multiplicity there. -/
def instanceMessages (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F)
    (i : Fin S.k) : List ((Nat × List F) × F) :=
  (List.range (2 ^ S.logN i)).flatMap fun r ↦
    ((S.lookups i).zip (busNumbers S i)).flatMap fun (l, b) ↦ l.tuples.map fun (es, m) ↦
      ((b, es.map (·.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))),
        m.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))

theorem zip_finRange {α : Type*} {k : Nat} (l : List α) (hl : l.length = k) (d : α) :
    (List.finRange k).zip l = (List.finRange k).map fun i ↦ (i, l.getD i.val d) := by
  refine List.ext_getElem (by simp only [List.length_zip, List.length_finRange, hl,
    Nat.min_self, List.length_map]) fun j h1 h2 ↦ ?_
  simp only [List.getElem_zip, List.getElem_finRange, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_finRange] at h2; omega)]
  rfl

theorem messages_eq (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F) :
    S.messages traces publicValues =
      (List.finRange S.k).flatMap (instanceMessages S traces publicValues) := by
  rw [Iop.Batch.Setup.messages, zip_finRange _ (length_busIds S) [], List.flatMap_map]
  rfl

theorem length_instanceMessages (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F)
    (i : Fin S.k) :
    (instanceMessages S traces publicValues i).length =
      2 ^ S.logN i * ((S.lookups i).map (·.tuples.length)).sum := by
  rw [instanceMessages, List.length_flatMap, List.sum_eq_length_nsmul _
    (((S.lookups i).map (·.tuples.length)).sum) fun x hx ↦ ?_, List.length_map,
    List.length_range, smul_eq_mul]
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
  exact length_flatMap_zip _ _ (length_busNumbers S i) _ fun x ↦ List.length_map _

/-- The batch's lookup messages number its interactions. -/
theorem length_messages (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F) :
    (S.messages traces publicValues).length = S.numInteractions := by
  rw [messages_eq, List.length_flatMap, Iop.Batch.Setup.numInteractions, ← Fin.sum_univ_def]
  exact Finset.sum_congr rfl fun i _ ↦ length_instanceMessages S traces publicValues i

/-- Every message is a tuple of a lookup with its bus. -/
theorem exists_of_mem_messages (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F)
    (x : (Nat × List F) × F) (hx : x ∈ S.messages traces publicValues) :
    ∃ l b, (b, l) ∈ Iop.Batch.busLookups (List.ofFn S.lookups) ∧ b = x.1.1 ∧
      ∃ t ∈ l.tuples, x.1.2.length = t.1.length := by
  rw [messages_eq] at hx
  obtain ⟨i, -, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨r, -, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨⟨l, b⟩, hlb, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨⟨es, m⟩, ht, rfl⟩ := List.mem_map.mp hx
  refine ⟨l, b, ?_, rfl, (es, m), ht, List.length_map _⟩
  rw [Iop.Batch.busLookups]
  refine List.mem_flatMap.mpr ⟨(S.lookups i, busNumbers S i), ?_, ?_⟩
  · have hi : i.val < (List.ofFn S.lookups).length := by rw [List.length_ofFn]; exact i.isLt
    have hb : i.val < (busIds (List.ofFn S.lookups)).length := by
      rw [length_busIds]; exact i.isLt
    have := List.getElem_mem (l := (List.ofFn S.lookups).zip (busIds (List.ofFn S.lookups)))
      (n := i.val) (by rw [List.length_zip]; omega)
    rw [List.getElem_zip, List.getElem_ofFn] at this
    rwa [busNumbers, List.getD_eq_getElem _ _ hb]
  · show (b, l) ∈ (busNumbers S i).zip (S.lookups i)
    rw [← List.zip_swap]
    exact List.mem_map.mpr ⟨(l, b), hlb, rfl⟩

/-- The widest tuple bounds every tuple of the batch. -/
theorem width_le_lookupWidth (l : Stark.Lookup F) (hl : l ∈ (List.ofFn S.lookups).flatten) :
    l.width ≤ S.lookupWidth := by
  show l.width ≤ maxWidth _
  rw [maxWidth]
  exact le_foldl_max_of_mem (fun l ↦ l.width) _ 1 l hl

theorem mem_flatten_of_busLookups (x : Nat × Stark.Lookup F)
    (hx : x ∈ Iop.Batch.busLookups (List.ofFn S.lookups)) :
    x.2 ∈ (List.ofFn S.lookups).flatten := by
  obtain ⟨⟨L, ids⟩, hL, hx⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatten.mpr ⟨L, (List.of_mem_zip hL).1, (List.of_mem_zip hx).2⟩

/-! ### The round of the lookup challenges -/

section Round
variable (publicValues : Fin S.k → List F)

/-- The lookup challenges `(α_L, β_L)` are bad: for some tuple of candidate traces of the trace
words at `δ'`, each satisfying its AIR, the buses do not balance but the pair makes a message's
denominator or the sum of the messages' fractions vanish (`LogUp.PairBad`). -/
def LookupBad (δ' : ℝ)
    (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
    (lookupAlpha lookupBeta : 𝕂) : Prop :=
  ∃ P : (i : Fin S.k) → Fin (S.air i).width → F[X],
    (∀ i, P i ∈ candidates (S.instanceSetup i) δ' (traces i)) ∧
    (∀ i, (S.air i).Satisfied (S.logN i) (traceOf (S.instanceSetup i) (P i)) (publicValues i)) ∧
    ¬ S.Balanced (fun i ↦ traceOf (S.instanceSetup i) (P i)) publicValues ∧
    LogUp.PairBad S.lookupWidth
      (S.messages (fun i ↦ traceOf (S.instanceSetup i) (P i)) publicValues) lookupAlpha lookupBeta

open Classical in
/-- **The lookup round.** At most `ℓ (T + (T - 1) W) |𝕂|` pairs are bad, `ℓ` the number of tuples
of candidate traces. -/
theorem card_lookupBad_le (δ' : ℝ)
    (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F) :
    (Finset.univ.filter fun z : 𝕂 × 𝕂 ↦ LookupBad S publicValues δ' traces z.1 z.2).card ≤
      S.traceListSize δ' * (S.numInteractions + (S.numInteractions - 1) * S.lookupWidth) *
        Fintype.card 𝕂 := by
  set C := Fintype.piFinset fun i ↦ (candidates_finite (S.instanceSetup i) δ' (traces i)).toFinset
  set T := S.numInteractions
  set W := S.lookupWidth
  have hW : 1 ≤ W := by
    show 1 ≤ maxWidth _
    rw [maxWidth]
    exact le_foldl_max (fun l : Stark.Lookup F ↦ l.width) _ 1
  have hsub : (Finset.univ.filter fun z : 𝕂 × 𝕂 ↦ LookupBad S publicValues δ' traces z.1 z.2) ⊆
      (C.filter fun P ↦ (∀ i, (S.air i).Satisfied (S.logN i) (traceOf (S.instanceSetup i) (P i))
        (publicValues i)) ∧ ¬ S.Balanced (fun i ↦ traceOf (S.instanceSetup i) (P i))
          publicValues).biUnion fun P ↦ Finset.univ.filter fun z : 𝕂 × 𝕂 ↦
        LogUp.PairBad W (S.messages (fun i ↦ traceOf (S.instanceSetup i) (P i)) publicValues)
          z.1 z.2 := by
    intro z hz
    obtain ⟨P, hP, hsat, hbal, hbad⟩ := (Finset.mem_filter.mp hz).2
    refine Finset.mem_biUnion.mpr ⟨P, Finset.mem_filter.mpr ⟨?_, hsat, hbal⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩
    exact Fintype.mem_piFinset.mpr fun i ↦ (Set.Finite.mem_toFinset _).mpr (hP i)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hone : ∀ P ∈ C.filter fun P ↦ (∀ i, (S.air i).Satisfied (S.logN i)
      (traceOf (S.instanceSetup i) (P i)) (publicValues i)) ∧
        ¬ S.Balanced (fun i ↦ traceOf (S.instanceSetup i) (P i)) publicValues,
      (Finset.univ.filter fun z : 𝕂 × 𝕂 ↦ LogUp.PairBad W
        (S.messages (fun i ↦ traceOf (S.instanceSetup i) (P i)) publicValues) z.1 z.2).card ≤
      (T + (T - 1) * W) * Fintype.card 𝕂 := by
    intro P hP
    set traces' := fun i ↦ traceOf (S.instanceSetup i) (P i)
    obtain ⟨key, hkey⟩ : ∃ key : Nat × List F, ¬ (((S.messages traces' publicValues).filter
        (·.1 = key)).map (·.2)).sum = 0 := by
      by_contra h
      push Not at h
      exact (Finset.mem_filter.mp hP).2.2 h
    have hb := S.buses
    have hlen := length_messages S traces' publicValues
    refine (LogUp.card_pairBad_le W hW _ (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_)
      (fun x hx y hy hxy ↦ ?_) key hkey).trans_eq (by rw [hlen])
    · obtain ⟨l, b, hlb, -, t, ht, hlen⟩ := exists_of_mem_messages S traces' publicValues x hx
      have hl := mem_flatten_of_busLookups S _ hlb
      rw [hlen, hb.tupleWidths l hl t ht]
      exact width_le_lookupWidth S l hl
    · obtain ⟨l, b, hlb, rfl, t, ht, hlen⟩ := exists_of_mem_messages S traces' publicValues x hx
      obtain ⟨l', b', hlb', rfl, t', ht', hlen'⟩ :=
        exists_of_mem_messages S traces' publicValues y hy
      rw [hlen, hlen', hb.tupleWidths l (mem_flatten_of_busLookups S _ hlb) t ht,
        hb.tupleWidths l' (mem_flatten_of_busLookups S _ hlb') t' ht']
      exact hb.busWidths _ hlb _ hlb' hxy
    · obtain ⟨l, b, hlb, rfl, -⟩ := exists_of_mem_messages S traces' publicValues x hx
      obtain ⟨l', b', hlb', rfl, -⟩ := exists_of_mem_messages S traces' publicValues y hy
      exact hb.distinct _ hlb _ hlb' hxy
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_const, smul_eq_mul, ← Nat.mul_assoc]
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans ?_))
  rw [Fintype.card_piFinset, Iop.Batch.Setup.traceListSize]
  exact Finset.prod_le_prod fun i _ ↦ card_candidates_le _ δ' _

/-- Without lookups, the buses balance and no pair of challenges is bad. -/
theorem not_lookupBad (hl : ∀ i, S.lookups i = []) (δ' : ℝ)
    (traces : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F)
    (lookupAlpha lookupBeta : 𝕂) :
    ¬ LookupBad S publicValues δ' traces lookupAlpha lookupBeta := by
  rintro ⟨P, -, -, hnb, -⟩
  refine hnb fun key ↦ ?_
  rw [messages_eq]
  have hnil : ∀ i, instanceMessages S (fun i ↦ traceOf (S.instanceSetup i) (P i)) publicValues
      i = [] := fun i ↦ by
    unfold instanceMessages
    rw [hl i]
    exact List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl
  rw [List.flatMap_eq_nil_iff.mpr fun i _ ↦ hnil i]
  rfl

end Round

end CompStark.Sound.Batch

/-! ### The terminals -/

namespace CompStark.Sound.Batch
open CompStark.Stark CompStark.Iop CompStark.Lookup Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Valid lookups are row-local and read the AIR's columns. -/
theorem fits_of_lookupsValid {params : Fri.Params} {air : Air F} {logN : Nat}
    {L : List (Stark.Lookup F)} (h : LookupsValid params air logN L) :
    ∀ l ∈ L, l.Fits air.width air.mainNextWidth air.preprocessedWidth
      air.preprocessedNextWidth := by
  cases L with
  | nil => exact fun l hl ↦ absurd hl List.not_mem_nil
  | cons l L => exact h.2

theorem zip_eq_map_zipIdx {α : Type*} (L : List α) (ids : List Nat) (h : ids.length = L.length) :
    L.zip ids = L.zipIdx.map fun x ↦ (x.1, ids.getD x.2 0) := by
  refine List.ext_getElem (by simp only [List.length_zip, h, Nat.min_self, List.length_map,
    List.length_zipIdx]) fun j h1 h2 ↦ ?_
  simp only [List.getElem_zip, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zip] at h1; omega)]

variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)

theorem challenges_getD (lookupAlpha lookupBeta : 𝕂) (i : Fin S.k) (c : Nat)
    (hc : c < (S.lookups i).length) :
    (S.challenges lookupAlpha lookupBeta i).getD (2 * c) 0 = lookupAlpha +
        algebraMap F 𝕂 (((busNumbers S i).getD c 0 + 1 : ℕ) : F) * lookupBeta ^ S.lookupWidth ∧
      (S.challenges lookupAlpha lookupBeta i).getD (2 * c + 1) 0 = lookupBeta := by
  have hc' : c < (busNumbers S i).length := by rw [length_busNumbers]; exact hc
  have h := getD_flatMap_pair (fun b ↦ lookupAlpha + algebraMap F 𝕂 ((b + 1 : ℕ) : F) *
    lookupBeta ^ S.lookupWidth) lookupBeta (busNumbers S i) c hc'
  rw [List.getD_eq_getElem _ _ hc']
  exact h

/-- On a row, a row-local expression's value mapped to `𝕂` is its value on the generation's
row. -/
theorem eval_rowEnv (i : Fin S.k) (publicValues : List F) (trace : Array F) (r : Nat)
    (e : Expr F) (he : e.rowLocal = true) :
    e.eval (rowEnv (S.instanceSetup i) publicValues trace r) =
      algebraMap F 𝕂 (e.eval (generationRow (S.air i) (S.logN i) trace publicValues r)) := by
  rw [rowEnv, Expr.eval_map (algebraMap F 𝕂), Expr.eval_rowLocal _ _ _ _ _ e he]

/-- A tuple's denominator on a row is its message's. -/
theorem tupleDenominator_eq (lookupAlpha lookupBeta : 𝕂) (i : Fin S.k) (publicValues : List F)
    (trace : Array F) (r c : Nat) (hc : c < (S.lookups i).length)
    (t : List (Expr F)) (ht : ∀ e ∈ t, e.rowLocal = true) :
    tupleDenominator (rowEnv (S.instanceSetup i) publicValues trace r)
        (S.challenges lookupAlpha lookupBeta i) c t =
      LogUp.denominator S.lookupWidth ((busNumbers S i).getD c 0,
        t.map (·.eval (generationRow (S.air i) (S.logN i) trace publicValues r)))
        lookupAlpha lookupBeta := by
  obtain ⟨h1, h2⟩ := challenges_getD S lookupAlpha lookupBeta i c hc
  rw [tupleDenominator, h1, h2, LogUp.denominator, List.map_map]
  congr 2
  exact List.map_congr_left fun e he ↦ eval_rowEnv S i publicValues trace r e (ht e he)

/-- **An instance's terminal is the sum of its messages' fractions**, if its candidate traces
satisfy all its constraints and no denominator of its messages vanishes. -/
theorem terminal_eq_fractionSum (publicValues : Fin S.k → List F) (lookupAlpha lookupBeta : 𝕂)
    (traces : Fin S.k → Array F) (i : Fin S.k) (hne : S.lookups i ≠ [])
    (R : Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) → F[X]) (terminal : 𝕂)
    (h : Holds (S.instanceSetup i) (publicValues i) (S.challenges lookupAlpha lookupBeta i)
      terminal (traces i) R)
    (hpole : ∀ x ∈ instanceMessages S traces publicValues i,
      LogUp.denominator S.lookupWidth x.1 lookupAlpha lookupBeta ≠ 0) :
    terminal = LogUp.fractionSum S.lookupWidth (instanceMessages S traces publicValues i)
      lookupAlpha lookupBeta := by
  have hfits := fits_of_lookupsValid (S.lookupsValid i)
  have hlen := length_busNumbers S i
  have hmem (l : Stark.Lookup F) (c : Nat) (hx : (l, c) ∈ (S.lookups i).zipIdx) :
      c < (S.lookups i).length ∧ l ∈ S.lookups i := by
    have h1 := List.mem_zipIdx hx
    refine ⟨by omega, ?_⟩
    rw [h1.2.2]
    exact List.getElem_mem _
  have hzip := zip_eq_map_zipIdx (S.lookups i) (busNumbers S i) hlen
  have hp : ∀ r < (S.instanceSetup i).n, ∀ x ∈ (S.lookups i).zipIdx, ∀ t ∈ x.1.tuples,
      tupleDenominator (rowEnv (S.instanceSetup i) (publicValues i) (traces i) r)
        (S.challenges lookupAlpha lookupBeta i) x.2 t.1 ≠ 0 := by
    intro r hr x hx t ht
    obtain ⟨hc, hl⟩ := hmem x.1 x.2 hx
    have hf := hfits x.1 hl t ht
    rw [tupleDenominator_eq S lookupAlpha lookupBeta i (publicValues i) (traces i) r x.2 hc t.1
      fun e he ↦ (hf.1 e he).1]
    set g := generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r
    refine hpole (((busNumbers S i).getD x.2 0, t.1.map (·.eval g)), t.2.eval g) ?_
    rw [instanceMessages, hzip]
    refine List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩
    refine List.mem_flatMap.mpr ⟨(x.1, (busNumbers S i).getD x.2 0), List.mem_map_of_mem hx, ?_⟩
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [terminal_eq_sum (S.instanceSetup i) hne (publicValues i) _ terminal (traces i) R h hp]
  · rw [LogUp.fractionSum, instanceMessages, hzip, sum_flatMap, List.map_flatMap, sum_flatMap]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    rw [List.flatMap_map, List.map_flatMap, sum_flatMap, sum_flatMap]
    congr 1
    refine List.map_congr_left fun x hx ↦ ?_
    obtain ⟨hc, hl⟩ := hmem x.1 x.2 hx
    rw [lookupFractions, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht ↦ ?_
    have hf := hfits x.1 hl t ht
    simp only [Function.comp_apply]
    rw [tupleDenominator_eq S lookupAlpha lookupBeta i (publicValues i) (traces i) r x.2 hc t.1
      fun e he ↦ (hf.1 e he).1, eval_rowEnv S i (publicValues i) (traces i) r t.2 hf.2.1]

/-- **The terminals sum to the sum of fractions of the batch's messages**, if every instance's
candidate traces satisfy all its constraints and no message's denominator vanishes. -/
theorem sum_terminals_eq (publicValues : Fin S.k → List F) (lookupAlpha lookupBeta : 𝕂)
    (traces : Fin S.k → Array F)
    (R : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) → F[X])
    (terminal : Fin S.k → 𝕂)
    (h : ∀ i, Holds (S.instanceSetup i) (publicValues i) (S.challenges lookupAlpha lookupBeta i)
      (terminal i) (traces i) (R i))
    (hpole : ∀ x ∈ S.messages traces publicValues,
      LogUp.denominator S.lookupWidth x.1 lookupAlpha lookupBeta ≠ 0) :
    (∑ i with S.lookups i ≠ [], terminal i) =
      LogUp.fractionSum S.lookupWidth (S.messages traces publicValues) lookupAlpha lookupBeta := by
  classical
  have hsplit : LogUp.fractionSum S.lookupWidth (S.messages traces publicValues) lookupAlpha
      lookupBeta = ∑ i, LogUp.fractionSum S.lookupWidth
        (instanceMessages S traces publicValues i) lookupAlpha lookupBeta := by
    rw [LogUp.fractionSum, messages_eq, List.map_flatMap, sum_flatMap, Fin.sum_univ_def]
    rfl
  rw [hsplit, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ S.lookups i ≠ [])]
  have hzero : ∑ i with ¬ S.lookups i ≠ [], LogUp.fractionSum S.lookupWidth
      (instanceMessages S traces publicValues i) lookupAlpha lookupBeta = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have h0 : S.lookups i = [] := not_not.mp (Finset.mem_filter.mp hi).2
    rw [instanceMessages, h0, LogUp.fractionSum, List.map_flatMap, sum_flatMap]
    refine List.sum_eq_zero fun x hx ↦ ?_
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    rfl
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  refine terminal_eq_fractionSum S publicValues lookupAlpha lookupBeta traces i
    (Finset.mem_filter.mp hi).2 (R i) (terminal i) (h i) fun x hx ↦ hpole x ?_
  rw [messages_eq]
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hx⟩

end CompStark.Sound.Batch
