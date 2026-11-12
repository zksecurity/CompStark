/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgeLocal

/-! # Authored-prefix bounds for the four sumcheck phases -/

set_option maxHeartbeats 1000000
@[expose] public section
open OracleComp
open scoped ENNReal BigOperators
namespace CompStark.Keccak.Gkr

/-- A residual depends only on the coordinates already sampled. -/
theorem residualSum_prefix {E : Type} [CommRing E] {n : Nat}
    (f : (Fin n → E) → E) (a b : Fin n → E) (used : Nat)
    (same : ∀ j, j.val < used → a j = b j) : residualSum f a used = residualSum f b used := by
  unfold residualSum
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  funext j
  split
  · exact same j ‹_›
  · rfl

/-- The running value immediately after a round is its claim-aware sampled evaluation. -/
theorem runningValue_succ {E M : Type} {n : Nat}
    (ops : Fin n → Sumcheck.MessageOps E M) (polys : Fin n → M)
    (point : Fin n → E) (value : E) (i : Fin n) :
    runningValue ops polys point value (i.val+1) =
      (ops i).evaluate (runningValue ops polys point value i.val) (polys i) (point i) := by
  simp only [runningValue, i.isLt, dite_true, Fin.eta]

/-- Valid sumcheck messages satisfy their Boolean acceptance check at every authored round. -/
theorem roundsValid_at {E M : Type} {n : Nat}
    (ops : Fin n → Sumcheck.MessageOps E M) (polys : Fin n → M)
    (point : Fin n → E) (value : E) (valid : roundsValid ops polys point value) (i : Fin n) :
    (ops i).accept (runningValue ops polys point value i.val) (polys i) = true := by
  induction n generalizing value with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact valid.1
    · rw [show j.succ.val = j.val+1 from rfl, runningValue_tail _ _ _ _ j.val (by omega)]
      exact ih (fun i => ops i.succ) (fun i => polys i.succ) (fun i => point i.succ)
        ((ops 0).evaluate value (polys 0) (point 0)) valid.2 j

/-- Authored messages, round operations and challenges fix the running target at the next round. -/
theorem runningValue_prefix {E M : Type} {n : Nat}
    (ops other : Fin n → Sumcheck.MessageOps E M) (a b : Fin n → M)
    (r s : Fin n → E) (v w : E) (used : Nat)
    (initial : v = w) (same : ∀ j, j.val < used → ops j = other j ∧ a j = b j ∧ r j = s j) :
    runningValue ops a r v used = runningValue other b s w used := by
  induction used with
  | zero => exact initial
  | succ used ih =>
    simp only [runningValue]
    split
    · rename_i h
      obtain ⟨ho, hp, hr⟩ := same ⟨used,h⟩ (by change used < used+1; omega)
      rw [ho, hp, hr, ih (fun j hj => same j (by omega))]
    · exact ih (fun j hj => same j (by omega))

/-- One fixed-prefix sumcheck residual inherits the bound from the sumcheck knowledge certificate. -/
theorem prefix_sumcheck_local_bound {E : Type} [Field E] [Fintype E] [DecidableEq E] [CharP E 2]
    {p n degree width : Nat} (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (q : Witness p) (history : List (List E)) (before after : Cut)
    (source : (cuts p)[history.length]? = some before)
    (target : (cuts p)[history.length+1]? = some after)
    (H : Transcript E p → MvPolynomial (Fin n) E)
    (ops : Transcript E p → Fin n → Sumcheck.MessageOps E (Sumcheck.CompressedMessage E width))
    (model : ∀ t i, Sumcheck.MessageModel ({0,1} : Finset E) (ops t i) degree)
    (polys : Transcript E p → Fin n → Sumcheck.CompressedMessage E width)
    (point : Transcript E p → Fin n → E) (value : Transcript E p → E)
    (invariant : Transcript E p → Prop) (i : Fin n)
    (cap : ∀ t j, (H t).degreeOf j ≤ degree)
    (pre : ∀ t, cutHolds x output q t before ↔ invariant t ∧
      runningValue (ops t) (polys t) (point t) (value t) i.val =
        residualSum (fun z => MvPolynomial.eval z (H t)) (point t) i.val)
    (post : ∀ t, cutHolds x output q t after → invariant t ∧
      runningValue (ops t) (polys t) (point t) (value t) (i.val+1) =
        residualSum (fun z => MvPolynomial.eval z (H t)) (point t) (i.val+1))
    (checks : ∀ t, Accepts x output t → roundsValid (ops t) (polys t) (point t) (value t))
    (fixed : ∀ t u, history <+: transcriptMessages t → history <+: transcriptMessages u →
      (invariant t ↔ invariant u) ∧ H t = H u ∧ ops t i = ops u i ∧ polys t i = polys u i ∧
      runningValue (ops t) (polys t) (point t) (value t) i.val =
        runningValue (ops u) (polys u) (point u) (value u) i.val ∧
      ∀ j, j.val < i.val → point t j = point u j)
    (sampled : ∀ r t, history ++ [[r]] <+: transcriptMessages t → point t i = r) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (degree : ENNReal) / Fintype.card E := by
  classical
  by_cases wrong : ¬ prefixClaim x output history q
  · by_cases possible : ∃ r, prefixClaim x output (history ++ [[r]]) q
    · obtain ⟨r₀, good₀⟩ := possible
      have cutAt (r : E) : (cuts p)[(history ++ [[r]]).length]? = some after := by
        simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using target
      obtain ⟨t, ht, accepted, htgood⟩ := (prefixClaim_at x output _ q _ (cutAt r₀)).mp good₀
      have ht' : history <+: transcriptMessages t := (List.prefix_append history _).trans ht
      have inv := (post t htgood).1
      have wrongResidual : runningValue (ops t) (polys t) (point t) (value t) i.val ≠
          residualSum (fun z => MvPolynomial.eval z (H t)) (point t) i.val := by
        intro he
        exact wrong ((prefixClaim_at x output history q _ source).mpr
          ⟨t, ht', accepted, (pre t).mpr ⟨inv, he⟩⟩)
      have bound := sumcheck_residual_certificate_bound q (H t) (cap t) i (point t)
        (ops t i) (model t i) (polys t i) _ wrongResidual
          (roundsValid_at _ _ _ _ (checks t accepted) i)
      refine (prEvent_mono (uniformField E) _ _ ?_).trans bound
      intro r event
      obtain ⟨u, hu, _, hugood⟩ := (prefixClaim_at x output _ q _ (cutAt r)).mp event.2
      have hu' : history <+: transcriptMessages u := (List.prefix_append history _).trans hu
      obtain ⟨_, hH, ho, hp, hv, hr⟩ := fixed t u ht' hu'
      have good := (post u hugood).2
      rw [runningValue_succ, sampled r u hu, ← hp, ← ho, ← hv, ← hH] at good
      rw [good]
      apply residualSum_prefix
      intro j hj
      by_cases hji : j = i
      · subst j
        rw [sampled r u hu, Function.update_self]
      · rw [Function.update_of_ne hji]
        exact (hr j (by have := j.isLt; have := i.isLt; omega)).symm
    · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun r h => possible ⟨r, h.2⟩)).trans ?_
      simp only [prEvent_false, zero_le]
  · refine (prEvent_mono (uniformField E) _ (fun _ => False) (fun _ h => wrong h.1)).trans ?_
    simp only [prEvent_false, zero_le]

/-- Transcript reads that locate a sumcheck's polynomial and scalar at every round. -/
def RoundReads {E : Type} {p n width : Nat} (offset : Nat)
    (polys : Transcript E p → Fin n → Sumcheck.CompressedMessage E width)
    (point : Transcript E p → Fin n → E) : Prop :=
  ∀ t i, (transcriptMessages t)[offset+2*i.val]? = some (List.ofFn (messageVector (polys t i))) ∧
    (transcriptMessages t)[offset+2*i.val+1]? = some [point t i]

/-- Authored round messages fix the sent vector and every previously sampled coordinate. -/
theorem RoundReads.fixed {E : Type} {p n width : Nat} {offset : Nat}
    {polys : Transcript E p → Fin n → Sumcheck.CompressedMessage E width}
    {point : Transcript E p → Fin n → E} (reads : RoundReads offset polys point)
    (t u : Transcript E p) (history : List (List E))
    (ht : history <+: transcriptMessages t) (hu : history <+: transcriptMessages u) :
    (∀ j, offset+2*j.val < history.length → polys t j = polys u j) ∧
    (∀ j, offset+2*j.val+1 < history.length → point t j = point u j) := by
  constructor
  · intro j hj
    have h := authored_getElem_eq history _ _ ht hu _ hj
    rw [(reads t j).1, (reads u j).1] at h
    exact messageVector_injective (List.ofFn_injective (Option.some.inj h))
  · intro j hj
    have h := authored_getElem_eq history _ _ ht hu _ hj
    rw [(reads t j).2, (reads u j).2] at h
    exact List.singleton_inj.mp (Option.some.inj h)

/-- A fixed static phase header and authored round prefix suffice for the certificate bound. -/
theorem prefix_encoded_sumcheck_bound {E : Type} [Field E] [Fintype E] [DecidableEq E] [CharP E 2]
    {p n degree width : Nat} (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (q : Witness p) (history : List (List E)) (before after : Cut)
    (source : (cuts p)[history.length]? = some before)
    (target : (cuts p)[history.length+1]? = some after)
    (H : Transcript E p → MvPolynomial (Fin n) E)
    (ops : Transcript E p → Fin n → Sumcheck.MessageOps E (Sumcheck.CompressedMessage E width))
    (model : ∀ t i, Sumcheck.MessageModel ({0,1} : Finset E) (ops t i) degree)
    (polys : Transcript E p → Fin n → Sumcheck.CompressedMessage E width)
    (point : Transcript E p → Fin n → E) (value : Transcript E p → E)
    (invariant : Transcript E p → Prop) (i : Fin n) (offset : Nat)
    (hlen : history.length = offset+2*i.val+1)
    (reads : RoundReads offset polys point)
    (cap : ∀ t j, (H t).degreeOf j ≤ degree)
    (pre : ∀ t, cutHolds x output q t before ↔ invariant t ∧
      runningValue (ops t) (polys t) (point t) (value t) i.val =
        residualSum (fun z => MvPolynomial.eval z (H t)) (point t) i.val)
    (post : ∀ t, cutHolds x output q t after → invariant t ∧
      runningValue (ops t) (polys t) (point t) (value t) (i.val+1) =
        residualSum (fun z => MvPolynomial.eval z (H t)) (point t) (i.val+1))
    (checks : ∀ t, Accepts x output t → roundsValid (ops t) (polys t) (point t) (value t))
    (static : ∀ t u, history <+: transcriptMessages t → history <+: transcriptMessages u →
      (invariant t ↔ invariant u) ∧ H t = H u ∧ value t = value u ∧ ops t = ops u) :
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (degree : ENNReal) / Fintype.card E := by
  apply prefix_sumcheck_local_bound x output q history before after source target H ops model polys point value
    invariant i cap pre post checks
  · intro t u ht hu
    obtain ⟨inv, hp, hv, ho⟩ := static t u ht hu
    obtain ⟨hs, hr⟩ := reads.fixed t u history ht hu
    refine ⟨inv, hp, congrFun ho i, hs i (by omega), ?_, fun j hj => hr j (by omega)⟩
    exact runningValue_prefix _ _ _ _ _ _ _ _ _ hv
      (fun j hj => ⟨congrFun ho j, hs j (by omega), hr j (by omega)⟩)
  · intro r t ht
    have h := authored_next_scalar history r t ht
    rw [hlen, (reads t i).2] at h
    exact List.singleton_inj.mp (Option.some.inj h)

/-- The pack sumcheck's round encodings start at the layer's third wire. -/
theorem pack_round_reads {E : Type} [CommRing E] {p : Nat} (d : Fin 12) :
    RoundReads (layerOffset p d+2) (fun t : Transcript E p => (t.layers d).packPolys)
      (fun t => (t.layers d).packPoint) := by
  intro t i
  constructor
  · rw [show layerOffset p d+2+2*i.val = layerOffset p d+(2+2*i.val) by omega,
      transcriptMessages_get_layer _ d _ (by omega), layerMessages_get_pack _ _ (by omega),
      roundMessages_get_polynomial]
  · rw [show layerOffset p d+2+2*i.val+1 = layerOffset p d+(2+(2*i.val+1)) by omega,
      transcriptMessages_get_layer _ d _ (by omega), layerMessages_get_pack _ _ (by omega),
      roundMessages_get_challenge]

/-- The position sumcheck's round encodings follow the pack coordinates. -/
theorem position_round_reads {E : Type} [CommRing E] {p : Nat} (d : Fin 12) :
    RoundReads (layerOffset p d+(2*p+4)) (fun t : Transcript E p => (t.layers d).positionPolys)
      (fun t => (t.layers d).positionPoint) := by
  intro t i
  constructor
  · rw [Nat.add_assoc, transcriptMessages_get_layer _ d _ (by omega),
      layerMessages_get_position _ _ (by omega), roundMessages_get_polynomial]
  · rw [show layerOffset p d+(2*p+4)+2*i.val+1 = layerOffset p d+((2*p+4)+(2*i.val+1)) by omega,
      transcriptMessages_get_layer _ d _ (by omega), layerMessages_get_position _ _ (by omega),
      roundMessages_get_challenge]

/-- The middle opening uses the six quadratic round pairs at its opening offset. -/
theorem word_round_reads {E : Type} [CommRing E] {p : Nat} :
    RoundReads (wordOffset p) (fun t : Transcript E p => t.openings.outputPolys)
      (fun t => t.openings.outputPoint) := by
  intro t i
  constructor
  · rw [transcriptMessages_get_word _ _ (by omega), roundMessages_get_polynomial]
  · rw [Nat.add_assoc, transcriptMessages_get_word _ _ (by omega), roundMessages_get_challenge]

/-- The input opening uses the ten quadratic round pairs at its opening offset. -/
theorem input_round_reads {E : Type} [CommRing E] {p : Nat} :
    RoundReads (inputOffset p) (fun t : Transcript E p => t.openings.inputPolys)
      (fun t => t.openings.inputPoint) := by
  intro t i
  constructor
  · rw [transcriptMessages_get_input _ _ (by omega), roundMessages_get_polynomial]
  · rw [Nat.add_assoc, transcriptMessages_get_input _ _ (by omega), roundMessages_get_challenge]

end CompStark.Keccak.Gkr
