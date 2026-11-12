/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgeEncoding
public import CompStark.Keccak.Gkr.KnowledgeSumcheck

/-! # Local bad-event bounds at concrete authored GKR prefixes -/

set_option maxHeartbeats 1000000
@[expose] public section
open OracleComp
open scoped ENNReal BigOperators
namespace CompStark.Keccak.Gkr

/-- A false product-prefix claim becomes true only at a root of its fixed product discrepancy. -/
theorem prefix_product_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (history : List (List E))
    (hlen : history.length = layerOffset p d+1)
    (source : (cuts p)[history.length]? = some (.product d))
    (target : (cuts p)[history.length+1]? = some (.pack d 0)) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (46 : ENNReal) / Fintype.card E := by
  classical
  by_cases wrong : ¬ prefixClaim x output history q
  · by_cases possible : ∃ r, prefixClaim x output (history ++ [[r]]) q
    · obtain ⟨r₀, good₀⟩ := possible
      have cutAt (r : E) : (cuts p)[(history ++ [[r]]).length]? = some (.pack d 0) := by
        simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using target
      obtain ⟨t, ht, checks, good⟩ := (prefixClaim_at x output _ q _ (cutAt r₀)).mp good₀
      have ht' : history <+: transcriptMessages t := (List.prefix_append history _).trans ht
      have wrongLayer : ¬ ClaimHolds q d.castSucc (claimAt x output t d.castSucc) := by
        intro claim
        apply wrong
        exact (prefixClaim_at x output history q _ source).mpr ⟨t, ht', checks, good.1, claim⟩
      have bound := product_evaluation_bound q d (claimAt x output t d.castSucc)
        (t.layers d).product wrongLayer (checks.1 d).1
      refine (prEvent_mono (uniformField E) _ _ ?_).trans bound
      intro r event
      obtain ⟨u, hu, _, after⟩ := (prefixClaim_at x output _ q _ (cutAt r)).mp event.2
      have hu' : history <+: transcriptMessages u := (List.prefix_append history _).trans hu
      have hclaim := prefix_claimAt_fixed x output t u history ht' hu' d (by omega)
      have hsent := prefix_product_fixed t u history ht' hu' d (by omega)
      have hpoint := authored_next_scalar history r u hu
      rw [hlen, transcriptMessages_get_layer _ d 1 (by omega), layerMessages_get_point] at hpoint
      have hr : (u.layers d).point = r := List.singleton_inj.mp (Option.some.inj hpoint)
      have he := after.2
      change runningValue (packOps (claimAt x output u d.castSucc).point) (u.layers d).packPolys (u.layers d).packPoint
        (polyEval (u.layers d).product (u.layers d).point) 0 = _ at he
      rw [runningValue, pack_start_identity, hr, ← hclaim, ← hsent] at he
      exact he.symm
    · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun r h => possible ⟨r, h.2⟩)).trans ?_
      simp only [prEvent_false, zero_le]
  · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun _ h => wrong h.1)).trans ?_
    simp only [prEvent_false, zero_le]

/-- At a fixed batching prefix, existential accepting completions share one quadratic discrepancy. -/
theorem prefix_beta_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (history : List (List E))
    (hlen : history.length = layerOffset p d+(2*p+27))
    (source : (cuts p)[history.length]? = some (.batch d)) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      ∃ t : Transcript E p, history ++ [[r]] <+: transcriptMessages t ∧ Accepts x output t ∧
        MiddleHolds x q t ∧ ClaimHolds q d.succ (nextClaim (t.layers d))] ≤
      (2 : ENNReal) / Fintype.card E := by
  classical
  let event := fun r => ∃ t : Transcript E p, history ++ [[r]] <+: transcriptMessages t ∧
    Accepts x output t ∧ MiddleHolds x q t ∧ ClaimHolds q d.succ (nextClaim (t.layers d))
  by_cases wrong : ¬ prefixClaim x output history q
  · by_cases possible : ∃ r, event r
    · obtain ⟨_, t, ht, checks, middle, _⟩ := possible
      have ht' : history <+: transcriptMessages t := (List.prefix_append history _).trans ht
      let honest : Fin 3 → E := fun k => shiftedEvaluation q d (t.layers d).point
        (t.layers d).packPoint (t.layers d).positionPoint k.val
      have hne : honest ≠ (t.layers d).evaluations := by
        intro he
        apply wrong
        exact (prefixClaim_at x output history q _ source).mpr
          ⟨t, ht', checks, middle, fun k => congrFun he.symm k⟩
      have bound := beta_batching_bound honest (t.layers d).evaluations hne
      refine (prEvent_mono (uniformField E) _ _ ?_).trans bound
      intro r h
      obtain ⟨u, hu, _, _, good⟩ := h.2
      have hu' : history <+: transcriptMessages u := (List.prefix_append history _).trans hu
      have shared := prefix_layer_beta_fixed t u history ht' hu' d r (by omega)
      have hpoint := authored_next_scalar history r u hu
      rw [hlen, transcriptMessages_get_layer _ d (2*p+27) (by omega), layerMessages_get_beta] at hpoint
      have hr : (u.layers d).beta = r := List.singleton_inj.mp (Option.some.inj hpoint)
      have he : u.layers d = {t.layers d with beta := r} := by
        rw [shared, ← hr]
      rw [he] at good
      have hg := (beta_boundary_identity q d {t.layers d with beta := r}).mp good
      exact hg.symm
    · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun r h => possible ⟨r, h.2⟩)).trans ?_
      simp only [prEvent_false, zero_le]
  · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun _ h => wrong h.1)).trans ?_
    simp only [prEvent_false, zero_le]

/-- The initial scalar identity is the zero test of the fixed multilinear discrepancy table. -/
theorem initialIdentity_iff_zero {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (r : Fin (p+10) → E) :
    initialIdentity x output q r ↔ mle (initialTable x output q) r = 0 := by
  let base := header r (0 : E)
  let middle := (1-base.segment) *
    ∑ l : Fin 25, eqWeight base.lanePoint l.val * middleWord x q base ⟨25+l.val, by omega⟩
  let t := header r middle
  have hm : MiddleHolds x q t := rfl
  have hp : initialPoint t = r := initialPoint_header r middle
  change ClaimHolds q 0 (firstClaim x output t) ↔ _
  constructor
  · intro good
    simpa only [hp] using initial_claim_zero x output q t hm good
  · intro zero
    apply (first_claim_identity x output q t).mpr
    rw [← hp, initial_table_identity] at zero
    change t.middleValue = _ at hm
    dsimp only [firstClaim, outputClaimAt]
    rw [hm]
    simp only [mul_sub, Finset.sum_sub_distrib] at zero
    linear_combination zero

/-- A false initial-prefix claim becomes universally true only at one affine collision root. -/
theorem prefix_initial_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (i : Fin (p+10)) (history : List (List E)) (hlen : history.length = i.val)
    (source : (cuts p)[history.length]? = some (.start i.val))
    (target : (cuts p)[history.length+1]? = some (.start (i.val+1))) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (1 : ENNReal) / Fintype.card E := by
  classical
  by_cases wrong : ¬ prefixClaim x output history q
  · by_cases possible : ∃ r, prefixClaim x output (history ++ [[r]]) q
    · obtain ⟨r₀, good₀⟩ := possible
      have cutAt (r : E) : (cuts p)[(history ++ [[r]]).length]? = some (.start (i.val+1)) := by
        simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, hlen] using target
      obtain ⟨t, ht, checks, _⟩ := (prefixClaim_at x output _ q _ (cutAt r₀)).mp good₀
      have ht' : history <+: transcriptMessages t := (List.prefix_append history _).trans ht
      have badPoint : ∃ point : Fin (p+10) → E,
          (∀ j, j.val < i.val → point j = initialPoint t j) ∧
          mle (initialTable x output q) point ≠ 0 := by
        by_contra hn
        push Not at hn
        apply wrong
        apply (prefixClaim_at x output history q _ source).mpr
        refine ⟨t, ht', checks, ?_⟩
        intro point agrees
        exact (initialIdentity_iff_zero x output q point).mpr (hn point agrees)
      obtain ⟨point, agrees, nonzero⟩ := badPoint
      have cap : CoordinateDegree (mle (initialTable x output q)) 1 := by
        simpa only [mle_eq_eval] using coordinateDegree_eval (MvPolynomial.MLE' (initialTable x output q))
          (tablePolynomial_degree (initialTable x output q))
      obtain ⟨P, hP, eval⟩ := cap i point
      have hne : P ≠ 0 := by
        intro hz
        have h := eval (point i)
        simp only [hz, Polynomial.eval_zero, Function.update_eq_self] at h
        exact nonzero h.symm
      have bound := polynomial_collision_bound P 0 hne hP (by simp)
      simp only [Nat.cast_one] at bound
      refine (prEvent_mono (uniformField E) _ _ ?_).trans bound
      intro r event
      obtain ⟨u, hu, _, after⟩ := (prefixClaim_at x output _ q _ (cutAt r)).mp event.2
      have hu' : history <+: transcriptMessages u := (List.prefix_append history _).trans hu
      have hpoint := authored_next_scalar history r u hu
      rw [hlen, transcriptMessages_get_initial] at hpoint
      have hr : initialPoint u i = r := List.singleton_inj.mp (Option.some.inj hpoint)
      have good := after (Function.update point i r) (by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self, hr]
        · have hj' : j.val < i.val := by have := j.isLt; have := i.isLt; omega
          rw [Function.update_of_ne hji, agrees j hj']
          exact prefix_initial_fixed t u history ht' hu' j (by omega))
      rw [eval, Polynomial.eval_zero]
      exact (initialIdentity_iff_zero x output q _).mp good
    · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun r h => possible ⟨r, h.2⟩)).trans ?_
      simp only [prEvent_false, zero_le]
  · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun _ h => wrong h.1)).trans ?_
    simp only [prEvent_false, zero_le]

end CompStark.Keccak.Gkr
