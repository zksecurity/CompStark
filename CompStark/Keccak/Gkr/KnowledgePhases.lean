/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgeRounds

/-! # Fixed-prefix knowledge bounds for each Keccak GKR phase -/

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public section
open OracleComp
open scoped ENNReal BigOperators
namespace CompStark.Keccak.Gkr

/-- Prefixes beyond all layers fix the final layer claim. -/
theorem prefix_final_claim_fixed {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (t u : Transcript E p)
    (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (hi : wordOffset p ≤ history.length) :
    claimAt x output t (Fin.last 12) = claimAt x output u (Fin.last 12) := by
  change nextClaim (t.layers (Fin.last 11)) = nextClaim (u.layers (Fin.last 11))
  have h := prefix_layer_fixed t u history ht hu (Fin.last 11) (by
    dsimp only [layerOffset, wordOffset, Fin.val_last] at *
    omega)
  exact congrArg nextClaim h

/-- Authorship of all pack rounds fixes both their polynomial vectors and sampled point. -/
theorem prefix_pack_data_fixed {E : Type} [CommRing E] {p : Nat}
    (t u : Transcript E p) (history : List (List E)) (ht : history <+: transcriptMessages t)
    (hu : history <+: transcriptMessages u) (d : Fin 12)
    (hi : layerOffset p d+(2*p+4) ≤ history.length) :
    (t.layers d).packPolys = (u.layers d).packPolys ∧
      (t.layers d).packPoint = (u.layers d).packPoint := by
  obtain ⟨hp, hr⟩ := (pack_round_reads d).fixed t u history ht hu
  exact ⟨funext fun j => hp j (by omega), funext fun j => hr j (by omega)⟩

/-- A pack challenge can repair a false retained-table residual only within its cubic bound. -/
theorem prefix_pack_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (i : Fin (p+1)) (history : List (List E)) (after : Cut)
    (hlen : history.length = layerOffset p d+2+2*i.val+1)
    (source : (cuts p)[history.length]? = some (.pack d i.val))
    (target : (cuts p)[history.length+1]? = some after)
    (boundary : ∀ t, cutHolds x output q t after → cutHolds x output q t (.pack d (i.val+1))) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (3 : ENNReal) / Fintype.card E := by
  classical
  have eval (t : Transcript E p) :
      (fun r => MvPolynomial.eval r (packPolynomial q d (claimAt x output t d.castSucc) (t.layers d).point)) =
        packSummand q d (claimAt x output t d.castSucc) (t.layers d).point :=
    funext (packPolynomial_eval _ _ _ _)
  apply prefix_encoded_sumcheck_bound x output q history (.pack d i.val) after source target
    (fun t => packPolynomial q d (claimAt x output t d.castSucc) (t.layers d).point)
    (fun t => packOps (claimAt x output t d.castSucc).point)
    (fun t i => cofactorModel ((claimAt x output t d.castSucc).point i))
    (fun t => (t.layers d).packPolys) (fun t => (t.layers d).packPoint)
    (fun t => polyEval (t.layers d).product (t.layers d).point) (MiddleHolds x q)
    i (layerOffset p d+2) hlen (pack_round_reads d)
  · intro t j
    exact packPolynomial_degree _ _ _ _ j
  · intro t
    simp only [eval]
    rfl
  · intro t good
    simpa only [cutHolds, eval] using boundary t good
  · intro t good
    exact (good.1 d).2.1
  · intro t u ht hu
    have hc := prefix_claimAt_fixed x output t u history ht hu d (by omega)
    have hs := prefix_layer_point_fixed t u history ht hu d (by omega)
    have hp := prefix_product_fixed t u history ht hu d (by omega)
    exact ⟨prefix_MiddleHolds_fixed x q t u history ht hu (by
      have : p+11 ≤ layerOffset p d := by unfold layerOffset; omega
      omega), by rw [hc, hs], by rw [hp, hs], by rw [hc]⟩

/-- A position challenge can repair a false retained-table residual only within its cubic bound. -/
theorem prefix_position_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (i : Fin 11) (history : List (List E))
    (hlen : history.length = layerOffset p d+(2*p+4)+2*i.val+1)
    (source : (cuts p)[history.length]? = some (.position d i.val))
    (target : (cuts p)[history.length+1]? = some (.position d (i.val+1))) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (3 : ENNReal) / Fintype.card E := by
  classical
  have eval (t : Transcript E p) :
      (fun r => MvPolynomial.eval r (positionPolynomial q d (claimAt x output t d.castSucc) (t.layers d))) =
        positionSummand q d (claimAt x output t d.castSucc) (t.layers d) :=
    funext (positionPolynomial_eval _ _ _ _)
  apply prefix_encoded_sumcheck_bound x output q history (.position d i.val) (.position d (i.val+1))
    source target (fun t => positionPolynomial q d (claimAt x output t d.castSucc) (t.layers d))
    (fun _ _ => Sumcheck.compressedOps 2) (fun _ _ => Sumcheck.compressedModel 2)
    (fun t => (t.layers d).positionPolys) (fun t => (t.layers d).positionPoint)
    (fun t => roundsEnd (packOps (claimAt x output t d.castSucc).point) (t.layers d).packPolys (t.layers d).packPoint
      (polyEval (t.layers d).product (t.layers d).point)) (MiddleHolds x q)
    i (layerOffset p d+(2*p+4)) hlen (position_round_reads d)
  · intro t j
    exact positionPolynomial_degree _ _ _ _ j
  · intro t
    simp only [eval]
    rfl
  · intro t good
    simpa only [cutHolds, eval] using good
  · intro t good
    exact (good.1 d).2.2.1
  · intro t u ht hu
    have hc := prefix_claimAt_fixed x output t u history ht hu d (by omega)
    have hs := prefix_layer_point_fixed t u history ht hu d (by omega)
    have hp := prefix_product_fixed t u history ht hu d (by omega)
    obtain ⟨hpolys, hpoint⟩ := prefix_pack_data_fixed t u history ht hu d (by omega)
    refine ⟨prefix_MiddleHolds_fixed x q t u history ht hu (by
      have : p+11 ≤ layerOffset p d := by unfold layerOffset; omega
      omega), ?_, ?_, rfl⟩
    · simp only [positionPolynomial, hc, hs, hpoint]
    · rw [hpolys, hpoint, hp, hs, hc]

/-- A middle-opening challenge can repair a false residual only within its quadratic bound. -/
theorem prefix_word_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (i : Fin 6) (history : List (List E)) (after : Cut)
    (hlen : history.length = wordOffset p+2*i.val+1)
    (source : (cuts p)[history.length]? = some (.word i.val))
    (target : (cuts p)[history.length+1]? = some after)
    (boundary : ∀ t, cutHolds x output q t after → cutHolds x output q t (.word (i.val+1))) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (2 : ENNReal) / Fintype.card E := by
  classical
  have eval (t : Transcript E p) :
      (fun r => MvPolynomial.eval r (wordPolynomial x q t)) = wordSummand x q t :=
    funext (wordPolynomial_eval _ _ _)
  apply prefix_encoded_sumcheck_bound x output q history (.word i.val) after source target
    (wordPolynomial x q) (fun _ _ => Sumcheck.compressedOps 1)
    (fun _ _ => Sumcheck.compressedModel 1) (fun t => t.openings.outputPolys) (fun t => t.openings.outputPoint)
    Transcript.middleValue (fun t => ClaimHolds q (Fin.last 12) (claimAt x output t (Fin.last 12)))
    i (wordOffset p) hlen word_round_reads
  · exact wordPolynomial_degree x q
  · intro t
    simp only [eval]
    rfl
  · intro t good
    simpa only [cutHolds, eval] using boundary t good
  · intro t good
    exact good.2.1
  · intro t u ht hu
    have hc := prefix_final_claim_fixed x output t u history ht hu (by omega)
    obtain ⟨hi, hs, hl, hm⟩ := prefix_header_fixed t u history ht hu (by
      have : p+11 ≤ wordOffset p := by unfold wordOffset; omega
      omega)
    refine ⟨by rw [hc], ?_, hm, rfl⟩
    have hw : middleWord x q t = middleWord x q u := by
      funext slot
      change mle _ t.instancePoint = mle _ u.instancePoint
      rw [hi]
    simp only [wordPolynomial, hs, hl, hw]

/-- A prefix before the input opening fixes the preceding committed-word opening equation. -/
theorem prefix_word_opening_fixed {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t u : Transcript E p) (history : List (List E))
    (ht : history <+: transcriptMessages t) (hu : history <+: transcriptMessages u)
    (hi : inputOffset p ≤ history.length) :
    (t.openings.outputValue = mle (middleWord x q t) t.openings.outputPoint ↔
      u.openings.outputValue = mle (middleWord x q u) u.openings.outputPoint) := by
  obtain ⟨hi', _, _, _⟩ := prefix_header_fixed t u history ht hu (by
    have : p+11 ≤ inputOffset p := by unfold inputOffset wordOffset; omega
    omega)
  have hr : t.openings.outputPoint = u.openings.outputPoint := by
    funext j
    exact (word_round_reads.fixed t u history ht hu).2 j (by unfold inputOffset at hi; omega)
  have h := authored_getElem_eq history _ _ ht hu (wordOffset p+12) (by unfold inputOffset at hi; omega)
  rw [transcriptMessages_get_wordValue, transcriptMessages_get_wordValue] at h
  have hv := List.singleton_inj.mp (Option.some.inj h)
  have hw : middleWord x q t = middleWord x q u := by
    funext slot
    change mle _ t.instancePoint = mle _ u.instancePoint
    rw [hi']
  rw [hv, hw, hr]

/-- An input-opening challenge can repair a false residual only within its quadratic bound. -/
theorem prefix_input_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (i : Fin 10) (history : List (List E)) (after : Cut)
    (hlen : history.length = inputOffset p+2*i.val+1)
    (source : (cuts p)[history.length]? = some (.input i.val))
    (target : (cuts p)[history.length+1]? = some after)
    (boundary : ∀ t, cutHolds x output q t after → cutHolds x output q t (.input (i.val+1))) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (2 : ENNReal) / Fintype.card E := by
  classical
  have eval (t : Transcript E p) :
      (fun r => MvPolynomial.eval r (inputPolynomial q t)) = inputSummand q t :=
    funext (inputPolynomial_eval _ _)
  apply prefix_encoded_sumcheck_bound x output q history (.input i.val) after source target
    (inputPolynomial q) (fun _ _ => Sumcheck.compressedOps 1)
    (fun _ _ => Sumcheck.compressedModel 1) (fun t => t.openings.inputPolys) (fun t => t.openings.inputPoint)
    (fun t => (claimAt x output t (Fin.last 12)).value)
    (fun t => t.openings.outputValue = mle (middleWord x q t) t.openings.outputPoint)
    i (inputOffset p) hlen input_round_reads
  · exact inputPolynomial_degree q
  · intro t
    simp only [eval]
    rfl
  · intro t good
    simpa only [cutHolds, eval] using boundary t good
  · intro t good
    exact good.2.2.2.1
  · intro t u ht hu
    have hc := prefix_final_claim_fixed x output t u history ht hu (by unfold inputOffset at hlen; omega)
    have hl := prefix_layer_fixed t u history ht hu (Fin.last 11) (by
      dsimp only [layerOffset, inputOffset, wordOffset, Fin.val_last] at *
      omega)
    exact ⟨prefix_word_opening_fixed x q t u history ht hu (by omega),
      by simp only [inputPolynomial, hl], by rw [hc], rfl⟩

/-- The complete pack residual is the initial position residual. -/
theorem pack_end_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (t : Transcript E p) :
    cutHolds x output q t (.position d 0) → cutHolds x output q t (.pack d (p+1)) := by
  rintro ⟨middle, good⟩
  refine ⟨middle, ?_⟩
  rw [runningValue_last, residualSum_last]
  simpa only [runningValue, position_start_identity] using good

/-- A layer's beta challenge leaves either the next layer or the middle opening. -/
def betaNextCut (d : Fin 12) : Cut :=
  if h : d.val+1 < 12 then .layer ⟨d.val+1, h⟩ else .word 0

/-- Truth after beta includes the retained middle claim and the newly batched layer claim. -/
theorem beta_next_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (t : Transcript E p) (good : cutHolds x output q t (betaNextCut d)) :
    MiddleHolds x q t ∧ ClaimHolds q d.succ (nextClaim (t.layers d)) := by
  unfold betaNextCut at good
  split at good
  · rename_i h
    have hne : d.val+1 ≠ 0 := by omega
    dsimp only [cutHolds, claimAt, Fin.val_castSucc] at good
    simp only [hne, dite_false, Nat.add_sub_cancel, Fin.eta] at good
    refine ⟨good.1, ?_⟩
    have he : d.succ = (⟨d.val+1, h⟩ : Fin 12).castSucc := Fin.ext rfl
    rw [he]
    exact good.2
  · rename_i h
    have hd : d = Fin.last 11 := Fin.ext (by simp only [Fin.val_last]; omega)
    subst d
    refine ⟨?_, good.1⟩
    simpa only [MiddleHolds, runningValue, word_start_identity] using good.2

/-- Beta's fixed-prefix bound includes the boundary into the next layer or opening. -/
theorem prefix_beta_next_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (history : List (List E))
    (hlen : history.length = layerOffset p d+(2*p+27))
    (source : (cuts p)[history.length]? = some (.batch d))
    (target : (cuts p)[history.length+1]? = some (betaNextCut d)) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (2 : ENNReal) / Fintype.card E := by
  refine (prEvent_mono (uniformField E) _ _ ?_).trans
    (prefix_beta_local_bound x output q d history hlen source)
  intro r event
  obtain ⟨t, ht, checks, good⟩ := (prefixClaim_at x output _ q (betaNextCut d) (by
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using target)).mp event.2
  obtain ⟨middle, claim⟩ := beta_next_preserving x output q d t good
  exact ⟨event.1, t, ht, checks, middle, claim⟩

/-- A universally true initial identity implies the fixed committed input relation. -/
theorem initialIdentity_all_input {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (hx : IndependentLanePowers x) (output : Fin (2^(p+4)) → Fin 25 → E)
    (q : Witness p) (good : ∀ r : Fin (p+10) → E, initialIdentity x output q r) :
    InputRelation x output q := by
  classical
  by_contra wrong
  obtain ⟨b, slot, he⟩ := initialError_nonzero x hx output q wrong
  let w : Fin (2^(p+10)) := ⟨b.val+2^(p+4)*slot.val, by
    have h := (finProdFinEquiv (slot,b)).isLt
    change b.val+2^(p+4)*slot.val < 64*2^(p+4) at h
    simpa only [show p+10=p+4+6 by omega, pow_add, show (2^6 : Nat)=64 by decide,
      Nat.mul_comm, Nat.add_comm] using h⟩
  have hw : initialTable x output q w = initialError x output q b slot := by
    dsimp only [initialTable, w]
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt,
      Nat.add_mul_div_left _ _ (by positivity : 0 < 2^(p+4)), Nat.div_eq_of_lt b.isLt,
      Nat.zero_add, Fin.eta]
  have zero := (initialIdentity_iff_zero x output q _).mp (good (cubePoint w))
  rw [mle_cubePoint, hw] at zero
  exact he zero

/-- The first challenge's bound starts from the PCS-bound input relation. -/
theorem prefix_root_local_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (hx : IndependentLanePowers x) (output : Fin (2^(p+4)) → Fin 25 → E)
    (q : Witness p)
    (source : (cuts p)[0]? = some (.start 0)) (target : (cuts p)[1]? = some (.start 1)) :
    Pr{let r ← uniformField E}[¬ InputRelation x output q ∧
      prefixClaim x output [[r]] q] ≤ (1 : ENNReal) / Fintype.card E := by
  refine (prEvent_mono (uniformField E) _ _ ?_).trans
    (prefix_initial_local_bound x output q ⟨0, by omega⟩ [] rfl source target)
  intro r event
  refine ⟨?_, event.2⟩
  intro hg
  obtain ⟨t, _, _, good⟩ := (prefixClaim_at x output [] q (.start 0) source).mp hg
  apply event.1
  exact initialIdentity_all_input x hx output q (fun r => good r (by intro j hj; omega))

end CompStark.Keccak.Gkr
