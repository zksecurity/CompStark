/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.BatchLogUp

/-! # Balance over the integers

LogUp checks that every bus balances in the field (`Setup.Balanced`): the multiplicities of each
bus's tuples sum to zero modulo `p`. The verifier also checks `∑ᵢ wᵢ 2 ^ logNᵢ < p`
(`heightBoundOk`, Plonky3's `check_multiplicity_height_bound`), `wᵢ` the sum of instance `i`'s
count weights, and an AIR keeps the magnitudes of a lookup's multiplicities on a row within its
count weight (`Setup.CountsBounded`, not checked by the verifier). Then, the base field being the
prime field `ℤ/p`, the buses balance as multisets: with integer multiplicities, every bus's tuples sum to zero over `ℤ`
(`balanced_int`), since each such sum vanishes modulo `p` and is below `p` in magnitude.
-/

@[expose] public section
namespace CompStark.Sound.Batch
open CompStark.Stark CompStark.Lookup CompStark.Iop

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- Lifting a flat map element by element: lists `g a` of lifts of the lists `f a`, each of size
at most `w a` and of elements satisfying `P`, give such a lift of the flat map of size at most
`∑ w a`. -/
theorem exists_lift_flatMap {α β γ : Type*} (lift : γ → β) (size : γ → ℕ) (P : γ → Prop)
    (f : α → List β) (w : α → ℕ) : ∀ L : List α,
      (∀ a ∈ L, ∃ g : List γ, g.map lift = f a ∧ (g.map size).sum ≤ w a ∧ ∀ x ∈ g, P x) →
      ∃ g : List γ, g.map lift = L.flatMap f ∧ (g.map size).sum ≤ (L.map w).sum ∧ ∀ x ∈ g, P x
  | [], _ => ⟨[], rfl, le_rfl, fun _ hx ↦ absurd hx List.not_mem_nil⟩
  | a :: L, h => by
    obtain ⟨g₁, h₁, h₁', hP₁⟩ := h a List.mem_cons_self
    obtain ⟨g₂, h₂, h₂', hP₂⟩ :=
      exists_lift_flatMap lift size P f w L fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    refine ⟨g₁ ++ g₂, by rw [List.map_append, h₁, h₂, List.flatMap_cons], ?_, fun x hx ↦ ?_⟩
    · rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
    · rcases List.mem_append.mp hx with hx | hx
      · exact hP₁ x hx
      · exact hP₂ x hx

/-- One lookup's messages on a row, with integer multiplicities `cs` lifting its multiplicities. -/
theorem lift_tuples {β : Type*} (msg : List (Expr F) → β) (row : Expr.Env F F) :
    ∀ (ts : List (List (Expr F) × Expr F)) (cs : List ℤ),
      cs.map (Int.cast : ℤ → F) = ts.map (·.2.eval row) →
      ((ts.zip cs).map fun x ↦ (msg x.1.1, x.2)).map (fun x ↦ (x.1, (x.2 : F))) =
          ts.map (fun t ↦ (msg t.1, t.2.eval row)) ∧
        (((ts.zip cs).map fun x ↦ (msg x.1.1, x.2)).map (·.2.natAbs)) = cs.map Int.natAbs ∧
        ∀ x ∈ (ts.zip cs).map (fun x ↦ (msg x.1.1, x.2)), x.2 ∈ cs
  | [], [], _ => ⟨rfl, rfl, fun _ hx ↦ absurd hx List.not_mem_nil⟩
  | [], _ :: _, h => absurd h (by simp only [List.map_cons, List.map_nil, reduceCtorEq,
      not_false_eq_true])
  | _ :: _, [], h => absurd h (by simp only [List.map_cons, List.map_nil, reduceCtorEq,
      not_false_eq_true])
  | t :: ts, c :: cs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := lift_tuples msg row ts cs h.2
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, List.mem_cons,
      forall_eq_or_imp, true_or, true_and]
    exact ⟨⟨by rw [h.1], h1⟩, h2, fun x hx ↦ Or.inr (h3 x hx)⟩

theorem natAbs_sum_le : ∀ l : List ℤ, l.sum.natAbs ≤ (l.map Int.natAbs).sum
  | [] => le_rfl
  | a :: l => by
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left (natAbs_sum_le l) _)

variable {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)
  (traces : Fin S.k → Array F) (publicValues : Fin S.k → List F)

/-- With bounded multiplicities, the messages lift to integer multiplicities whose magnitudes sum
to at most `∑ᵢ wᵢ 2 ^ logNᵢ`, each at most its instance's `wᵢ`. -/
theorem exists_int_messages (hcounts : S.CountsBounded traces publicValues) :
    ∃ zs : List ((Nat × List F) × ℤ), zs.map (fun x ↦ (x.1, (x.2 : F))) =
        S.messages traces publicValues ∧
      (zs.map (·.2.natAbs)).sum ≤
        ((List.ofFn fun i ↦ (S.lookups i, S.logN i)).map fun (l, logN) ↦
          (l.map (·.countWeight)).sum * 2 ^ logN).sum ∧
      ∀ x ∈ zs, ∃ i, x.2.natAbs ≤ ((S.lookups i).map (·.countWeight)).sum := by
  rw [messages_eq, List.map_ofFn, List.ofFn_eq_map]
  refine exists_lift_flatMap _ _ _ _ _ _ fun i _ ↦ ?_
  dsimp only [Function.comp_apply]
  unfold instanceMessages
  have hrow := exists_lift_flatMap (fun x : (Nat × List F) × ℤ ↦ (x.1, (x.2 : F)))
    (·.2.natAbs) (fun x ↦ x.2.natAbs ≤ ((S.lookups i).map (·.countWeight)).sum)
    (fun r ↦ ((S.lookups i).zip (busNumbers S i)).flatMap fun (l, b) ↦
      l.tuples.map fun (es, m) ↦
        ((b, es.map (·.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))),
          m.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r)))
    (fun _ ↦ ((S.lookups i).map (·.countWeight)).sum) (List.range (2 ^ S.logN i))
    fun r hr ↦ ?_
  · obtain ⟨g, hg, hsum, hP⟩ := hrow
    refine ⟨g, hg, hsum.trans (le_of_eq ?_), fun x hx ↦ ⟨i, hP x hx⟩⟩
    rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_comm]
  · have hlen := length_busNumbers S i
    obtain ⟨g, hg, hsum, hP⟩ := exists_lift_flatMap
      (fun x : (Nat × List F) × ℤ ↦ (x.1, (x.2 : F))) (·.2.natAbs)
      (fun x ↦ x.2.natAbs ≤ ((S.lookups i).map (·.countWeight)).sum)
      (fun (l, b) ↦ l.tuples.map fun (es, m) ↦
        ((b, es.map (·.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))),
          m.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r)))
      (fun x : Stark.Lookup F × Nat ↦ x.1.countWeight) ((S.lookups i).zip (busNumbers S i))
      fun x hx ↦ by
        have hl := (List.of_mem_zip hx).1
        obtain ⟨cs, hcs, hw⟩ := hcounts i r (List.mem_range.mp hr) x.1 hl
        obtain ⟨h1, h2, h3⟩ := lift_tuples (fun es ↦ (x.2, es.map (·.eval
          (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r)))) _ _ cs hcs
        refine ⟨_, h1, by rw [h2]; exact hw, fun z hz ↦ ?_⟩
        have hc := h3 z hz
        calc z.2.natAbs ≤ (cs.map Int.natAbs).sum :=
              List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (List.mem_map_of_mem hc)
          _ ≤ x.1.countWeight := hw
          _ ≤ ((S.lookups i).map (·.countWeight)).sum :=
              List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (List.mem_map_of_mem hl)
    refine ⟨g, hg, hsum.trans (le_of_eq ?_), hP⟩
    show (((S.lookups i).zip (busNumbers S i)).map ((·.countWeight) ∘ Prod.fst)).sum = _
    rw [← List.map_map, List.map_fst_zip (by rw [hlen])]

/-- **Balance over the integers.** If the verifier's multiplicity bound holds and the AIRs bound
their multiplicities, balanced buses balance as multisets: the messages have integer
multiplicities of magnitude below `p / 2`, and every bus's tuples sum to zero over `ℤ`. -/
theorem balanced_int (hbound : S.HeightBounded) (hcounts : S.CountsBounded traces publicValues)
    (hbal : S.Balanced traces publicValues) : S.BalancedInt traces publicValues := by
  obtain ⟨zs, hzs, hsize, hrow⟩ := exists_int_messages S traces publicValues hcounts
  have hp : CompPoly.CanonicalNat.bound F = Nat.card F := by
    rw [Nat.card_eq_fintype_card, CompPoly.CanonicalNat.card_eq]
  have hw : ((List.ofFn fun i ↦ (S.lookups i, S.logN i)).map fun (l, logN) ↦
      (l.map (·.countWeight)).sum * 2 ^ logN).sum < Nat.card F := by
    simpa only [Iop.Batch.Setup.HeightBounded, heightBoundOk, decide_eq_true_eq, hp] using hbound
  have hlt := hsize.trans_lt hw
  refine ⟨zs, hzs, fun x hx ↦ ?_, fun key ↦ ?_⟩
  · -- an instance's `wᵢ` is at most half its `wᵢ 2 ^ logNᵢ`
    obtain ⟨i, hi⟩ := hrow x hx
    have hfold := S.folds i
    have h2 : 2 ≤ 2 ^ S.logN i := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ S.logN i := Nat.pow_le_pow_right (by omega) (by omega)
    refine lt_of_le_of_lt ?_ hw
    calc 2 * x.2.natAbs ≤ ((S.lookups i).map (·.countWeight)).sum * 2 ^ S.logN i := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul hi h2
      _ ≤ ((List.ofFn fun i ↦ (S.lookups i, S.logN i)).map fun (l, logN) ↦
            (l.map (·.countWeight)).sum * 2 ^ logN).sum :=
          List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _
            (List.mem_map.mpr ⟨(S.lookups i, S.logN i), List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
  set s := ((zs.filter (·.1 = key)).map (·.2)).sum
  have hcast : (s : F) = 0 := by
    have h := hbal key
    rw [← hzs, List.filter_map, List.map_map] at h
    rw [Int.cast_list_sum, List.map_map]
    exact h
  have hdvd : (ringChar F : ℤ) ∣ s := (CharP.intCast_eq_zero_iff F (ringChar F) s).mp hcast
  have habs : s.natAbs < ringChar F := by
    rw [BaseField.ringChar_eq_card]
    refine lt_of_le_of_lt ?_ hlt
    refine (natAbs_sum_le _).trans ?_
    rw [List.map_map]
    exact List.Sublist.sum_le_sum (List.filter_sublist.map _) fun _ _ ↦ Nat.zero_le _
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by rwa [Int.natAbs_natCast])

/-- The batch is satisfied over the integers when it is in the field, the verifier's
multiplicity bound holds and the AIRs bound their multiplicities. -/
theorem satisfiedInt_of_satisfied (hbound : S.HeightBounded)
    (hcounts : S.CountsBounded traces publicValues) (h : S.Satisfied traces publicValues) :
    S.SatisfiedInt traces publicValues :=
  ⟨h.air, balanced_int S traces publicValues hbound hcounts h.balanced⟩

end CompStark.Sound.Batch
