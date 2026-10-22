/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchLogUp

/-! # Lookup inclusion over the integers

LogUp checks that every bus balances in the field (`Setup.Balanced`): the multiplicities of each
bus's tuples sum to zero modulo `p`. A lookup's tuples are queries, of positive weight, or
provided table entries, of weight `0` and any multiplicity (`Count`). The verifier checks
`∑ᵢ wᵢ 2 ^ logNᵢ < p` (`heightBoundOk`, Plonky3's `check_multiplicity_height_bound`), `wᵢ` the
sum of instance `i`'s weights, and an AIR keeps the magnitudes of its queries' multiplicities on
a row within its weights (`Air.CountsBounded`, not checked by the verifier). Then every bus's
queries are included in what is provided (`included_of_balanced`): for every bus and tuple of
values, some row provides it with a nonzero multiplicity, or else balance makes the queries'
multiplicities sum to zero modulo `p`; read as the integers of magnitude below `p / 2` they stand
for (`intValue`), they sum to below `p` in magnitude, so to zero over `ℤ`.
-/

@[expose] public section
namespace CompStark.Sound.Batch
open CompStark.Stark CompStark.Lookup CompStark.Iop

variable {F : Type} [BaseField F]

/-! ### The integer an element stands for -/

theorem ringChar_ne_zero : ringChar F ≠ 0 := by
  rw [BaseField.ringChar_eq_card]
  exact Nat.card_pos.ne'

theorem card_odd : Nat.card F % 2 = 1 := by
  have hp := BaseField.card_prime (F := F)
  refine Nat.odd_iff.mp (hp.odd_of_ne_two fun h ↦ BaseField.two_ne_zero (F := F) ?_)
  have := CharP.cast_eq_zero F (ringChar F)
  rwa [BaseField.ringChar_eq_card, h, Nat.cast_ofNat] at this

theorem intCast_intValue (x : F) : ((intValue x : ℤ) : F) = x := by
  unfold BaseField.intValue
  rw [← map_intCast (ZMod.ringEquiv F (n := ringChar F)
      (by rw [← Nat.card_eq_fintype_card, BaseField.ringChar_eq_card])),
    ZMod.coe_valMinAbs, RingEquiv.apply_symm_apply]

/-- `intValue x` is the integer of least magnitude standing for `x`. -/
theorem natAbs_intValue_le (x : F) (z : ℤ) (h : (z : F) = x) : (intValue x).natAbs ≤ z.natAbs := by
  have : NeZero (ringChar F) := ⟨ringChar_ne_zero⟩
  unfold BaseField.intValue
  set e := ZMod.ringEquiv F (n := ringChar F)
    (by rw [← Nat.card_eq_fintype_card, BaseField.ringChar_eq_card])
  have hy : ((z : ZMod (ringChar F))) = e.symm x := by
    rw [← h, ← map_intCast e z, RingEquiv.symm_apply_apply]
  exact ZMod.natAbs_min_of_le_div_two _ _ _ (by rw [ZMod.coe_valMinAbs, hy])
    (ZMod.natAbs_valMinAbs_le _)

theorem two_mul_natAbs_intValue_lt (x : F) : 2 * (intValue x).natAbs < Nat.card F := by
  have : NeZero (ringChar F) := ⟨ringChar_ne_zero⟩
  have h := ZMod.natAbs_valMinAbs_le (n := ringChar F) ((ZMod.ringEquiv F (n := ringChar F)
    (by rw [← Nat.card_eq_fintype_card, BaseField.ringChar_eq_card])).symm x)
  have hodd := card_odd (F := F)
  have hc := BaseField.ringChar_eq_card (F := F)
  unfold BaseField.intValue
  omega

/-- An integer of magnitude below `p / 2` is the integer its element stands for. -/
theorem intValue_eq (x : F) (z : ℤ) (hz : 2 * z.natAbs < Nat.card F) (h : (z : F) = x) :
    intValue x = z := by
  have hcast : ((intValue x - z : ℤ) : F) = 0 := by
    rw [Int.cast_sub, intCast_intValue, h, sub_self]
  have hdvd : (ringChar F : ℤ) ∣ intValue x - z :=
    (CharP.intCast_eq_zero_iff F (ringChar F) _).mp hcast
  have hlt : (intValue x - z).natAbs < (ringChar F : ℤ).natAbs := by
    rw [Int.natAbs_natCast, BaseField.ringChar_eq_card]
    have := two_mul_natAbs_intValue_lt x
    have := Int.natAbs_sub_le (intValue x) z
    omega
  exact Int.sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt)

theorem intValue_zero : intValue (0 : F) = 0 :=
  intValue_eq 0 0 (by rw [Int.natAbs_zero, Nat.mul_zero]; exact Nat.card_pos) Int.cast_zero

theorem intValue_one : intValue (1 : F) = 1 := by
  refine intValue_eq 1 1 ?_ Int.cast_one
  have h3 : 2 < Nat.card F := by
    have := (BaseField.card_prime (F := F)).two_le
    have := card_odd (F := F)
    omega
  exact h3

theorem natAbs_sum_le : ∀ l : List ℤ, l.sum.natAbs ≤ (l.map Int.natAbs).sum
  | [] => le_rfl
  | a :: l => by
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left (natAbs_sum_le l) _)

/-! ### The queries' magnitudes -/

/-- The magnitudes of one row's queries of the lookups `L` with their buses `ids`, whatever their
keys. -/
theorem sum_natAbs_zip (key : Nat → List (Expr F) → Nat × List F) (val : Count F → F) :
    ∀ (L : List (Stark.Lookup F)) (ids : List Nat), ids.length = L.length →
      (((L.zip ids).flatMap fun (l, b) ↦ (l.entries.filter (0 < ·.2.weight)).map fun (es, c) ↦
          (key b es, val c)).map fun x ↦ (intValue x.2).natAbs).sum =
        (((L.flatMap (·.entries)).filter (0 < ·.2.weight)).map fun t ↦
          (intValue (val t.2)).natAbs).sum
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (by simp only [List.length_nil, List.length_cons]; omega)
  | l :: L, b :: ids, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.flatMap_cons, List.map_append, List.sum_append,
      sum_natAbs_zip key val L ids h, List.flatMap_cons, List.filter_append, List.map_append,
      List.sum_append, List.map_map]
    rfl

variable {EF : Type} [Challenge F EF] {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)
  (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F)

/-- On every row, instance `i`'s queries' magnitudes sum to at most its count weights. -/
theorem rowQueries_le (i : Fin S.k) (hcounts : (S.air i).CountsBounded (S.logN i))
    (hair : (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)) (r : Nat)
    (hr : r < 2 ^ S.logN i) :
    ((((S.lookups i).flatMap (·.entries)).filter (0 < ·.2.weight)).map fun t ↦
      (intValue (t.2.expr.eval
        (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))).natAbs).sum ≤
      ((S.lookups i).map (·.countWeight)).sum := by
  unfold Iop.Batch.Setup.lookups Iop.Batch.instanceLookups
  split
  · have hp := perm_packSameBus (2 ^ (S.air i).logQuotientChunksWith (S.logN i)
      (logUpConstraints (S.air i).lookups) + 1) (S.air i).lookups
    rw [Air.packedLookups, ((hp.filter _).map _).sum_eq, sum_countWeight, (hp.map _).sum_eq,
      ← sum_countWeight]
    exact hcounts _ _ hair r hr
  · exact Nat.zero_le _

/-- Instance `i`'s queries. -/
def instanceQueries (i : Fin S.k) : List ((Nat × List F) × F) :=
  (List.range (2 ^ S.logN i)).flatMap fun r ↦
    ((S.lookups i).zip (busNumbers S i)).flatMap fun (l, b) ↦
      (l.entries.filter (0 < ·.2.weight)).map fun (es, c) ↦
        ((b, es.map (·.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))),
          c.expr.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))

theorem queries_eq :
    S.queries traces publicValues =
      (List.finRange S.k).flatMap (instanceQueries S traces publicValues) := by
  rw [Iop.Batch.Setup.queries, zip_finRange _ (length_busIds S) [], List.flatMap_map]
  rfl

/-- The queries are the tuples of positive weight of the instances' lookups, with their buses, on
every row. -/
theorem mem_queries {x : (Nat × List F) × F} : x ∈ S.queries traces publicValues ↔
    ∃ i : Fin S.k, ∃ r < 2 ^ S.logN i, ∃ lb ∈ (S.lookups i).zip (busNumbers S i),
      ∃ t ∈ lb.1.entries, 0 < t.2.weight ∧
        x = ((lb.2, t.1.map (·.eval (generationRow (S.air i) (S.logN i) (traces i)
          (publicValues i) r))),
          t.2.expr.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r)) := by
  rw [queries_eq]
  constructor
  · intro hx
    obtain ⟨i, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨⟨l, b⟩, hlb, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨⟨es, c⟩, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ht, hw⟩ := List.mem_filter.mp ht
    exact ⟨i, r, List.mem_range.mp hr, (l, b), hlb, (es, c), ht, of_decide_eq_true hw, rfl⟩
  · rintro ⟨i, r, hr, ⟨l, b⟩, hlb, ⟨es, c⟩, ht, hw, rfl⟩
    exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_flatMap.mpr
      ⟨r, List.mem_range.mpr hr, List.mem_flatMap.mpr ⟨(l, b), hlb,
        List.mem_map.mpr ⟨(es, c), List.mem_filter.mpr ⟨ht, decide_eq_true hw⟩, rfl⟩⟩⟩⟩

/-- The queries' magnitudes sum to at most `∑ᵢ wᵢ 2 ^ logNᵢ`. -/
theorem sum_natAbs_queries_le (hcounts : ∀ i, (S.air i).CountsBounded (S.logN i))
    (hair : ∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)) :
    ((S.queries traces publicValues).map fun x ↦ (intValue x.2).natAbs).sum ≤
      ((List.ofFn fun i ↦ (S.lookups i, S.logN i)).map fun (l, logN) ↦
        (l.map (·.countWeight)).sum * 2 ^ logN).sum := by
  rw [queries_eq, List.map_flatMap, sum_flatMap, List.ofFn_eq_map, List.map_map]
  refine List.sum_le_sum fun i _ ↦ ?_
  dsimp only [Function.comp_apply]
  unfold instanceQueries
  rw [List.map_flatMap, sum_flatMap]
  calc _ ≤ ((List.range (2 ^ S.logN i)).map fun _ ↦ ((S.lookups i).map (·.countWeight)).sum).sum :=
        List.sum_le_sum fun r hr ↦ by
          refine (le_of_eq (sum_natAbs_zip
            (fun b es ↦ (b, es.map (·.eval (generationRow (S.air i) (S.logN i) (traces i)
              (publicValues i) r))))
            (fun c ↦ c.expr.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))
            _ _ (length_busNumbers S i))).trans ?_
          exact rowQueries_le S traces publicValues i (hcounts i) (hair i) r
            (List.mem_range.mp hr)
    _ = _ := by
      rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_comm]

/-! ### The messages of a key without a provider -/

theorem sum_filter_key {κ : Type*} [DecidableEq κ] (key : κ) :
    ∀ L : List (κ × F), ((L.filter (·.1 = key)).map (·.2)).sum =
      (L.map fun x ↦ if x.1 = key then x.2 else 0).sum
  | [] => rfl
  | x :: L => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_filter_key key L]
    by_cases h : x.1 = key
    · simp only [h, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, zero_add]

/-- A key no row provides has the same sum of multiplicities over the messages as over the
queries: its provided tuples have multiplicity `0`. -/
theorem sum_messages_key_eq (key : Nat × List F)
    (hnp : ¬ ∃ i r, S.Provides traces publicValues key i r) :
    (((S.messages traces publicValues).filter (·.1 = key)).map (·.2)).sum =
      (((S.queries traces publicValues).filter (·.1 = key)).map (·.2)).sum := by
  rw [sum_filter_key, sum_filter_key, messages_eq, queries_eq, List.map_flatMap, sum_flatMap,
    List.map_flatMap, sum_flatMap]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  unfold instanceMessages instanceQueries
  rw [List.map_flatMap, sum_flatMap, List.map_flatMap, sum_flatMap]
  congr 1
  refine List.map_congr_left fun r hr ↦ ?_
  rw [List.map_flatMap, sum_flatMap, List.map_flatMap, sum_flatMap]
  congr 1
  refine List.map_congr_left fun lb hlb ↦ ?_
  obtain ⟨l, b⟩ := lb
  set env := generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r
  have hval : ∀ t ∈ l.entries, ¬ 0 < t.2.weight → (b, t.1.map (·.eval env)) = key →
      t.2.expr.eval env = 0 := by
    intro t ht hw hk
    by_contra hne
    refine hnp ⟨i, r, List.mem_range.mp hr, (l, b), hlb, congrArg Prod.fst hk, t, ht,
      by omega, congrArg Prod.snd hk, hne⟩
  unfold Stark.Lookup.tuples
  rw [List.map_map, List.map_map, List.map_map,
    sum_map_filter_split l.entries (0 < ·.2.weight)]
  refine (congrArg (_ + ·) (List.sum_eq_zero fun x hx ↦ ?_)).trans (add_zero _)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ht, hw⟩ := List.mem_filter.mp ht
    simp only [decide_eq_true_eq] at hw
    dsimp only [Function.comp_apply]
    split
    · exact hval t ht hw (by assumption)
    · rfl

/-! ### Inclusion -/

/-- **Lookup inclusion over the integers.** If the verifier's multiplicity bound holds, the AIRs
bound their queries' multiplicities, the traces satisfy them and every bus balances, then every
bus's queries are included in what is provided: for every bus and tuple of values, some row
provides it, or its queries' multiplicities, read as the integers of magnitude below `p / 2` they
stand for, sum to zero over `ℤ`. -/
theorem included_of_balanced (hbound : S.HeightBounded)
    (hcounts : ∀ i, (S.air i).CountsBounded (S.logN i))
    (hair : ∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i))
    (hbal : S.Balanced traces publicValues) : S.Included traces publicValues := by
  intro key
  by_cases hp : ∃ i r, S.Provides traces publicValues key i r
  · exact Or.inl hp
  refine Or.inr ?_
  set s := (((S.queries traces publicValues).filter (·.1 = key)).map (intValue ·.2)).sum
  have hcast : (s : F) = 0 := by
    rw [Int.cast_list_sum, List.map_map]
    have h := hbal key
    rw [sum_messages_key_eq S traces publicValues key hp] at h
    rw [← h]
    exact congrArg List.sum (List.map_congr_left fun x _ ↦ intCast_intValue x.2)
  have hdvd : (ringChar F : ℤ) ∣ s := (CharP.intCast_eq_zero_iff F (ringChar F) s).mp hcast
  have hp' : CompPoly.CanonicalNat.bound F = Nat.card F := by
    rw [Nat.card_eq_fintype_card, CompPoly.CanonicalNat.card_eq]
  have hw : ((List.ofFn fun i ↦ (S.lookups i, S.logN i)).map fun (l, logN) ↦
      (l.map (·.countWeight)).sum * 2 ^ logN).sum < Nat.card F := by
    simpa only [Iop.Batch.Setup.HeightBounded, heightBoundOk, decide_eq_true_eq, hp'] using hbound
  have habs : s.natAbs < ringChar F := by
    rw [BaseField.ringChar_eq_card]
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (sum_natAbs_queries_le S traces publicValues hcounts
      hair) hw)
    refine (natAbs_sum_le _).trans ?_
    rw [List.map_map]
    exact List.Sublist.sum_le_sum (List.filter_sublist.map _) fun _ _ ↦ Nat.zero_le _
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by rwa [Int.natAbs_natCast])

/-- Traces satisfying the batch satisfy it with lookup inclusion, if the verifier's multiplicity
bound holds and the AIRs bound their queries' multiplicities. -/
theorem satisfiedWithInclusion_of_satisfied (hbound : S.HeightBounded)
    (hcounts : ∀ i, (S.air i).CountsBounded (S.logN i)) (h : S.Satisfied traces publicValues) :
    S.SatisfiedWithInclusion traces publicValues :=
  ⟨h.air, included_of_balanced S traces publicValues hbound hcounts h.air h.balanced⟩

end CompStark.Sound.Batch
