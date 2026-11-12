/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.HonestBus

/-! The honest table sumcheck: each round sends the compressed projected round polynomial of the
witness's summand, and the final message the transmitted columns at the final point. From a true
bus endpoint, against every coin sequence, it reaches the table sumcheck's endpoint
(`honestTable_terminal`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open _root_.Interaction _root_.Interaction.Oracle Sumcheck.Interaction.MultivariateRound

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The table sumcheck's coins: the batching draw, then one draw per round. -/
abbrev TableCoins := E × (Fin (TableSumcheck.maxHeight S L) → E)

/-- The true transmitted values at a point. -/
def honestValues (w : Witness K S.tables.length) (z : List E) : TableSumcheck.Values S L :=
  fun t i ↦ S.column L w t.1 (TableSumcheck.transmitted S t.1)[i] (z.take (L.logHeight t.1))

/-- The round function after the draws `χ`: the summand at `x` next, summed over the remaining
Boolean coordinates. -/
def roundValue (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) (χ : List E) (x : E) : E :=
  ∑ i : Fin (2 ^ (TableSumcheck.maxHeight S L - (χ ++ [x]).length)),
    TableSumcheck.summandValue S L k o ξ w
      ((χ ++ [x]) ++ List.ofFn (fun a : Fin (TableSumcheck.maxHeight S L - (χ ++ [x]).length) ↦
        bit i.val a.val)).reverse

/-- The interpolation points: powers of the base field's generator. -/
def interpolationPoint (n : ℕ) (j : Fin n) : E := ofK (gpow j.val)

/-- Below the generator's order, the interpolation points are distinct. -/
theorem interpolationPoint_injective (n : ℕ) (hn : n ≤ 2 ^ 64 - 1) :
    Function.Injective (interpolationPoint n) := by
  intro a b h
  apply Fin.ext
  apply gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega))
  exact ofK_injective h

/-- The honest round message after the draws `χ`: the round function interpolated at
`degree + 2` points, compressed. -/
def honestTableMessage (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length)
    (χ : List E) : TableSumcheck.Message S L :=
  let p := lagrangeCoeffs (interpolationPoint (TableSumcheck.degree S L + 2))
    (fun j ↦ roundValue S L k o ξ w χ (interpolationPoint (TableSumcheck.degree S L + 2) j))
  (p.getD 0 0, fun i ↦ p.getD (i.val + 2) 0)

/-- The honest rounds after the draws `χ`, then the true values at the final point. -/
def honestTableRounds (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    (n : ℕ) → List E → (Fin n → E) → (TableSumcheck.roundsProtocol S L n).tree.ExecutionPath
  | 0, χ, _ => ⟨honestValues S L w χ.reverse, PUnit.unit⟩
  | n + 1, χ, rs => ⟨honestTableMessage S L k o ξ w χ, some (rs 0),
      honestTableRounds o ξ w n (χ ++ [rs 0]) (Fin.tail rs)⟩

/-- The honest table transcript. -/
def honestTablePath (o : Bus.Output S L k) (w : Witness K S.tables.length)
    (coins : TableCoins S L) : (TableSumcheck.protocol S L).tree.ExecutionPath :=
  ⟨coins.1, honestTableRounds S L k o coins.1 w (TableSumcheck.maxHeight S L) [] coins.2⟩

/-- The true values hold. -/
theorem honestValues_hold (w : Witness K S.tables.length) (z : List E) :
    TableSumcheck.ValuesHold S L w z (honestValues S L w z) := fun _ _ ↦ rfl

/-- A Boolean sum over the embedded domain is the sum at zero and one. -/
theorem booleanDomain_sum (f : E → E) :
    ((Finset.univ.map TableSumcheck.booleanDomain).toList.map f).sum = f 0 + f 1 := by
  rw [Finset.sum_map_toList, Finset.sum_map, Fin.sum_univ_two]
  rfl

variable {S L k}

/-- The projected round polynomial is the round function. -/
theorem projected_eval (hT : ∀ t, (S.table t).WellFormed) (o : Bus.Output S L k) (ξ : E)
    (w : Witness K S.tables.length) (χ : List E) (hlen : χ.length < TableSumcheck.maxHeight S L)
    (x : E) :
    (Sumcheck.Spec.SingleRound.projectedRoundPolynomial E (TableSumcheck.maxHeight S L)
      (TableSumcheck.degree S L + 1) TableSumcheck.booleanDomain ⟨χ.length, hlen⟩
      (fun a ↦ χ.getD a.val 0) (TableSumcheck.summand S L k o ξ w)).val.eval x =
        roundValue S L k o ξ w χ x := by
  set i : Fin (TableSumcheck.maxHeight S L) := ⟨χ.length, hlen⟩
  have hp : List.ofFn (Fin.snoc (fun a : Fin i.castSucc ↦ χ.getD a.val 0) x) = χ ++ [x] := by
    rw [List.ofFn_succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact congrArg (· ++ [x]) (TableSumcheck.ofFn_getD χ)
  have hred : TableSumcheck.reduced S L k o ξ
      (List.ofFn (Fin.snoc (fun a : Fin i.castSucc ↦ χ.getD a.val 0) x)) (roundValue S L k o ξ w χ x) w := by
    rw [hp]
    rfl
  have hc := (TableSumcheck.reduced_core_ofFn_iff S L k hT o ξ w i.succ
    ⟨roundValue S L k o ξ w χ x, Fin.snoc (fun a ↦ χ.getD a.val 0) x⟩).mp hred
  exact (Sumcheck.Spec.SingleRound.relationRound_output_iff E _ _ TableSumcheck.booleanDomain i
    ⟨0, fun a ↦ χ.getD a.val 0⟩ (TableSumcheck.summand S L k o ξ w) x _).mp hc

/-- The interpolated message is the compressed projected round polynomial. -/
theorem honestTableMessage_eq (hT : ∀ t, (S.table t).WellFormed)
    (hdeg : TableSumcheck.degree S L + 2 ≤ 2 ^ 64 - 1) (o : Bus.Output S L k) (ξ : E)
    (w : Witness K S.tables.length) (χ : List E) (hlen : χ.length < TableSumcheck.maxHeight S L) :
    honestTableMessage S L k o ξ w χ =
      Sumcheck.compress (Sumcheck.Spec.SingleRound.projectedRoundPolynomial E (TableSumcheck.maxHeight S L)
        (TableSumcheck.degree S L + 1) TableSumcheck.booleanDomain ⟨χ.length, hlen⟩
        (fun a ↦ χ.getD a.val 0) (TableSumcheck.summand S L k o ξ w)) := by
  set q := Sumcheck.Spec.SingleRound.projectedRoundPolynomial E (TableSumcheck.maxHeight S L)
    (TableSumcheck.degree S L + 1) TableSumcheck.booleanDomain ⟨χ.length, hlen⟩
    (fun a ↦ χ.getD a.val 0) (TableSumcheck.summand S L k o ξ w)
  have hq : q.val.natDegree < TableSumcheck.degree S L + 2 := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp q.property)
    omega
  have hvals : (fun j ↦ roundValue S L k o ξ w χ (interpolationPoint (TableSumcheck.degree S L + 2) j)) =
      fun j ↦ q.val.eval (interpolationPoint (TableSumcheck.degree S L + 2) j) := by
    funext j
    exact (projected_eval hT o ξ w χ hlen _).symm
  have hpoly := coeffsPoly_lagrange (interpolationPoint (TableSumcheck.degree S L + 2))
    (interpolationPoint_injective _ hdeg) q.val hq
  have hc (i : ℕ) : (lagrangeCoeffs (interpolationPoint (TableSumcheck.degree S L + 2))
      fun j ↦ q.val.eval (interpolationPoint (TableSumcheck.degree S L + 2) j)).getD i 0 = q.val.coeff i := by
    rw [← coeffsPoly_coeff, hpoly]
  unfold honestTableMessage
  rw [hvals]
  simp only [Sumcheck.compress, hc]
  rfl

/-- An honest round keeps the running claim true: the message decodes at the claim to the next
claim. -/
theorem honest_round (hT : ∀ t, (S.table t).WellFormed)
    (hdeg : TableSumcheck.degree S L + 2 ≤ 2 ^ 64 - 1) (o : Bus.Output S L k) (ξ : E)
    (w : Witness K S.tables.length) (χ : List E) (current : E)
    (hlen : χ.length < TableSumcheck.maxHeight S L)
    (known : TableSumcheck.reduced S L k o ξ χ current w) (r : E) :
    TableSumcheck.reduced S L k o ξ (χ ++ [r])
      ((TableSumcheck.messageOps S L).evaluate current (honestTableMessage S L k o ξ w χ) r) w := by
  set i : Fin (TableSumcheck.maxHeight S L) := ⟨χ.length, hlen⟩
  set q := Sumcheck.Spec.SingleRound.projectedRoundPolynomial E (TableSumcheck.maxHeight S L)
    (TableSumcheck.degree S L + 1) TableSumcheck.booleanDomain i (fun a ↦ χ.getD a.val 0)
    (TableSumcheck.summand S L k o ξ w)
  have hrel : (((⟨current, fun a ↦ χ.getD a.val 0⟩ : Sumcheck.Spec.StatementRound E
      (TableSumcheck.maxHeight S L) i.castSucc), fun _ ↦ TableSumcheck.summand S L k o ξ w), ()) ∈
      Sumcheck.Spec.relationRound E (TableSumcheck.maxHeight S L) (TableSumcheck.degree S L + 1)
        TableSumcheck.booleanDomain i.castSucc :=
    (TableSumcheck.reduced_core_iff S L k hT o ξ w χ hlen.le current).mp known
  have hsum := Sumcheck.Spec.SingleRound.projected_sum_of_relationRound E _ _ TableSumcheck.booleanDomain
    i _ _ hrel
  rw [booleanDomain_sum] at hsum
  have hmsg : honestTableMessage S L k o ξ w χ = Sumcheck.compress q :=
    honestTableMessage_eq hT hdeg o ξ w χ hlen
  have heval : (TableSumcheck.messageOps S L).evaluate current (honestTableMessage S L k o ξ w χ) r =
      q.val.eval r := by
    rw [hmsg]
    change (Sumcheck.compressedOps (TableSumcheck.degree S L)).evaluate current (Sumcheck.compress q) r = _
    rw [Sumcheck.compressed_evaluate_eq, Sumcheck.compressed_compress current q hsum]
  rw [heval]
  have hnext := Sumcheck.Spec.SingleRound.relationRound_projected_output E _ _
    TableSumcheck.booleanDomain i ⟨current, fun a ↦ χ.getD a.val 0⟩
    (TableSumcheck.summand S L k o ξ w) r
  have hc := (TableSumcheck.reduced_core_ofFn_iff S L k hT o ξ w i.succ
    ⟨q.val.eval r, Fin.snoc (fun a ↦ χ.getD a.val 0) r⟩).mpr hnext
  have hp : List.ofFn (Fin.snoc (fun a : Fin i.castSucc ↦ χ.getD a.val 0) r) = χ ++ [r] := by
    rw [List.ofFn_succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact congrArg (· ++ [r]) (TableSumcheck.ofFn_getD χ)
  change TableSumcheck.reduced S L k o ξ (List.ofFn (Fin.snoc (fun a : Fin i.castSucc ↦ χ.getD a.val 0) r))
    (q.val.eval r) w at hc
  rw [hp] at hc
  exact hc

/-- Honest rounds from a true running claim reach a true endpoint with every check passed. -/
theorem roundsOutput_honest (hT : ∀ t, (S.table t).WellFormed)
    (hdeg : TableSumcheck.degree S L + 2 ≤ 2 ^ 64 - 1) (o : Bus.Output S L k) (ξ : E)
    (w : Witness K S.tables.length) (n : ℕ) (χ : List E) (current : E) (rs : Fin n → E)
    (hlen : χ.length + n = TableSumcheck.maxHeight S L)
    (known : TableSumcheck.reduced S L k o ξ χ current w) :
    TableSumcheck.roundsOutput S L k o ξ n χ current true (honestTableRounds S L k o ξ w n χ rs) =
      some ⟨o, (χ ++ List.ofFn rs).reverse, honestValues S L w (χ ++ List.ofFn rs).reverse, true⟩ := by
  induction n generalizing χ current with
  | zero =>
    change (some ⟨o, χ.reverse, honestValues S L w χ.reverse,
      true && decide (TableSumcheck.formula S L k o ξ χ.reverse (honestValues S L w χ.reverse) = current)⟩ :
        Option (TableSumcheck.Output S L k)) = _
    simp only [List.ofFn_zero, List.append_nil]
    have hr : TableSumcheck.maxHeight S L - χ.length = 0 := by omega
    unfold TableSumcheck.reduced at known
    rw [TableSumcheck.remaining_cube_zero _ hr (fun z ↦ TableSumcheck.summandValue S L k o ξ w z.reverse) χ]
      at known
    rw [TableSumcheck.formula_eq_summandValue S L k hT w o ξ χ.reverse _ (honestValues_hold S L w _),
      ← known]
    simp only [decide_true, Bool.and_self]
  | succ n ih =>
    change TableSumcheck.roundsOutput S L k o ξ n (χ ++ [rs 0])
      ((TableSumcheck.messageOps S L).evaluate current (honestTableMessage S L k o ξ w χ) (rs 0))
      (true && (TableSumcheck.messageOps S L).accept current (honestTableMessage S L k o ξ w χ))
      (honestTableRounds S L k o ξ w n (χ ++ [rs 0]) (Fin.tail rs)) = _
    have hacc : (TableSumcheck.messageOps S L).accept current (honestTableMessage S L k o ξ w χ) = true := rfl
    rw [hacc, Bool.and_true]
    have hnext := honest_round hT hdeg o ξ w χ current (by omega) known (rs 0)
    rw [ih (χ ++ [rs 0]) _ (Fin.tail rs) (by simp only [List.length_append, List.length_singleton]; omega)
      hnext]
    simp only [List.ofFn_succ, List.append_assoc, List.singleton_append]
    rfl

/-- Completeness of the table sumcheck: from a true bus endpoint, against every coin sequence, the
honest transcript reaches the table sumcheck's endpoint. -/
theorem honestTable_terminal (hwf : S.WellFormed L) (hdeg : TableSumcheck.degree S L + 2 ≤ 2 ^ 64 - 1)
    (o : Bus.Output S L k)
    (w : Witness K S.tables.length) (hsat : S.Satisfied L w) (terminal : Bus.Terminal S L k o w)
    (coins : TableCoins S L) :
    ∃ o', TableSumcheck.outputClaim S L k o (honestTablePath S L k o w coins) = some o' ∧
      o'.point.length = TableSumcheck.maxHeight S L ∧ TableSumcheck.Terminal S L k o' w := by
  have hT : ∀ t, (S.table t).WellFormed := fun t ↦ (hwf.2.2 t).1
  obtain ⟨hactive, shaped, hpoint, _, boundary, debts⟩ := terminal
  have hzero : TableSumcheck.debtPolynomial S L k o w = 0 := by
    apply (TableSumcheck.debtPolynomial_eq_zero_iff S L k o w).mpr
    apply (TableSumcheck.debtValues_zero_iff S L k o w).mpr
    exact ⟨fun i ↦ rider_zero S L w hsat.2.1 i _, debts⟩
  have hstart : TableSumcheck.reduced S L k o coins.1 [] (TableSumcheck.target S L k o coins.1) w := by
    have he := TableSumcheck.debtPolynomial_eval S L k hT o coins.1 w
    rw [hzero, Polynomial.eval_zero] at he
    exact (sub_eq_zero.mp he.symm).symm
  refine ⟨⟨o, (List.ofFn coins.2).reverse, honestValues S L w (List.ofFn coins.2).reverse, true⟩, ?_, ?_⟩
  · unfold TableSumcheck.outputClaim honestTablePath
    rw [hactive]
    have := roundsOutput_honest hT hdeg o coins.1 w _ [] _ coins.2
      (by simp only [List.length_nil, Nat.zero_add]) hstart
    simpa only [List.nil_append] using this
  · exact ⟨by simp only [List.length_reverse, List.length_ofFn],
      rfl, ⟨shaped, hpoint, boundary⟩, honestValues_hold S L w _⟩

end CompStark.Tables.Composed
