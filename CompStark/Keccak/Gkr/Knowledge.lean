/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgeBounds

/-!
# Keccak GKR knowledge for a PCS-supplied table

Every state binds its retained witness to the table supplied before GKR starts. The PCS supplies that table before the public reduction begins. Intermediate states retain the honest residual claim and a
compatible accepting completion; this records the verifier equations needed to transport
knowledge backwards. Identity maps retain the table through all messages and challenges.
The named certificate proves prover preservation and the local loss at every authored
prefix, using the bound-summand sumcheck certificate for its sumcheck phases.
-/

set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Polynomial Interaction.Oracle Interaction.Oracle.Security OracleComp
open scoped BigOperators ENNReal
@[expose] public section

namespace CompStark.Keccak.Gkr


/-- A retained witness is the table supplied by the enclosing PCS extraction. -/
@[reducible]
def boundState {p : Nat} (q₀ : Witness p) (claim : Witness p → Prop) : KnowledgeState where
  Witness := Witness p
  holds w := w = q₀ ∧ claim w

/-- Fixing the table fixes every summand derived from an admissible witness. -/
theorem boundState_bindsSummand {p : Nat} {α : Type*} (q₀ : Witness p)
    (claim : Witness p → Prop) (summand : Witness p → α) (w : Witness p)
    (known : (boundState (p := p) q₀ claim).holds w) : summand w = summand q₀ := by
  rw [known.1]

/-- The initial relation is about the fixed committed table, including the middle chain. -/
def inputState {E : Type} [CommRing E] [CharP E 2] {p : Nat} (q₀ : Witness p)
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) : KnowledgeState :=
  boundState (p := p) q₀ (InputRelation x output)

/-- Identity maps retain the PCS table at every strict prefix of the public reduction. -/
def wireExtractor {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) :
    (s : List WireStep) → (history : List (List E)) → (current : Witness p → Prop) →
    RoundExtractor (wireTree E s) (boundState (p := p) q₀ current)
  | [], _, _ => PUnit.unit
  | .message _ :: rest, history, _ => fun message =>
      let next := nextPrefixClaim x output rest (history ++ [List.ofFn message])
      ⟨boundState (p := p) q₀ next, id, wireExtractor (p := p) q₀ x output rest (history ++ [List.ofFn message]) next⟩
  | .challenge _ :: rest, history, _ => fun r =>
      let next := nextPrefixClaim x output rest (history ++ [[r]])
      ⟨boundState (p := p) q₀ next, id, wireExtractor (p := p) q₀ x output rest (history ++ [[r]]) next⟩

/-- The PCS binding reduces the extractor's existential bad event to the one fixed table. -/
theorem wireExtractor_badChallenge_iff {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (kind : Challenge) (rest : List WireStep) (history : List (List E))
    (current : Witness p → Prop) (r : E) :
    RoundExtractor.badChallenge (wireExtractor q₀ x output (.challenge kind :: rest) history current) r ↔
      ¬ current q₀ ∧ nextPrefixClaim x output rest (history ++ [[r]]) q₀ := by
  change (∃ w : Witness p, ¬ (w = q₀ ∧ current w) ∧
    w = q₀ ∧ nextPrefixClaim x output rest (history ++ [[r]]) w) ↔ _
  constructor
  · rintro ⟨w, wrong, rfl, good⟩
    exact ⟨fun hc => wrong ⟨rfl, hc⟩, good⟩
  · rintro ⟨wrong, good⟩
    exact ⟨q₀, fun hc => wrong hc.2, rfl, good⟩

/-- The public reduction starts with the fixed-table input relation supplied by the PCS layer. -/
def roundExtractor {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) :
    RoundExtractor (protocol E p) (inputState (p := p) q₀ x output) :=
  wireExtractor (p := p) q₀ x output (steps p) [] (InputRelation x output)

/-- Identity backward maps identify the terminal carrier with the retained table carrier. -/
def wireWitnessEquiv {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) :
    (s : List WireStep) → (history : List (List E)) → (current : Witness p → Prop) →
    (path : (wireTree E s).ExecutionPath) →
    ((wireExtractor (p := p) q₀ x output s history current).terminalState path).Witness ≃ Witness p
  | [], _, _, _ => Equiv.refl _
  | .message _ :: rest, history, _, path => wireWitnessEquiv (p := p) q₀ x output rest
      (history ++ [List.ofFn path.1]) (nextPrefixClaim x output rest (history ++ [List.ofFn path.1])) path.2
  | .challenge _ :: rest, history, _, path => wireWitnessEquiv (p := p) q₀ x output rest
      (history ++ [[(show E from path.1)]])
      (nextPrefixClaim x output rest (history ++ [[(show E from path.1)]])) path.2

/-- Extracting along any wire path retains the supplied table unchanged. -/
theorem wire_extract_eq {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (s : List WireStep) (history : List (List E)) (current : Witness p → Prop)
    (path : (wireTree E s).ExecutionPath)
    (w : ((wireExtractor (p := p) q₀ x output s history current).terminalState path).Witness) :
    (wireExtractor (p := p) q₀ x output s history current).extractWitness path w =
      wireWitnessEquiv (p := p) q₀ x output s history current path w := by
  induction s generalizing history current with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | message => rcases path with ⟨_,tail⟩; exact ih _ _ tail w
    | challenge => rcases path with ⟨_,tail⟩; exact ih _ _ tail w

/-- Append actual path messages in the same recursive order as the identity extractor. -/
def finishHistory {E : Type} : (s : List WireStep) → List (List E) →
    (wireTree E s).ExecutionPath → List (List E)
  | [], history, _ => history
  | .message _ :: rest, history, path => finishHistory rest (history ++ [List.ofFn path.1]) path.2
  | .challenge _ :: rest, history, path => finishHistory rest (history ++ [[(show E from path.1)]]) path.2

/-- Accumulating the strict prefixes appends exactly the wire encoding of the path. -/
theorem finishHistory_eq {E : Type} (s : List WireStep) (history : List (List E))
    (path : (wireTree E s).ExecutionPath) : finishHistory s history path = history ++ pathMessages s path := by
  induction s generalizing history with
  | nil => exact (List.append_nil _).symm
  | cons step rest ih =>
    cases step with
    | message =>
      change finishHistory rest (history ++ [List.ofFn path.1]) path.2 = _
      rw [ih]
      simp only [pathMessages, List.append_assoc, List.singleton_append]
    | challenge =>
      change finishHistory rest (history ++ [[(show E from path.1)]]) path.2 = _
      rw [ih]
      simp only [pathMessages, List.append_assoc, List.singleton_append]

/-- Terminal knowledge is exactly the retained-table binding and the final opening relation. -/
theorem wire_terminal_iff {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (s : List WireStep) (history : List (List E)) (current : Witness p → Prop)
    (path : (wireTree E s).ExecutionPath)
    (w : ((wireExtractor (p := p) q₀ x output s history current).terminalState path).Witness) :
    ((wireExtractor (p := p) q₀ x output s history current).terminalState path).holds w ↔
      let q := wireWitnessEquiv (p := p) q₀ x output s history current path w
      q = q₀ ∧ if s.isEmpty then current q else endpointClaim (p := p) x output (finishHistory s history path) q := by
  induction s generalizing history current with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | message =>
      rcases path with ⟨message,tail⟩
      have h := ih (history ++ [List.ofFn message])
        (nextPrefixClaim x output rest (history ++ [List.ofFn message])) tail w
      cases rest <;> exact h
    | challenge =>
      rcases path with ⟨r,tail⟩
      have h := ih (history ++ [[(show E from r)]])
        (nextPrefixClaim x output rest (history ++ [[(show E from r)]])) tail w
      cases rest <;> exact h

/-- The GKR schedule always includes fresh initial challenges. -/
theorem steps_ne_nil (p : Nat) : steps p ≠ [] := by
  apply List.ne_nil_of_mem (a := WireStep.challenge Challenge.segment)
  simp only [steps, List.mem_append, List.mem_cons, eq_self, or_true, true_or]

/-- Named terminal identification for the committed-table extractor. -/
def terminalWitnessEquiv {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (path : (protocol E p).ExecutionPath) :
    ((roundExtractor (p := p) q₀ x output).terminalState path).Witness ≃ Witness p :=
  wireWitnessEquiv (p := p) q₀ x output (steps p) [] (InputRelation x output) path

/-- The extractor returns the same retained table on every actual path. -/
theorem roundExtractor_extract_eq {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (path : (protocol E p).ExecutionPath)
    (w : ((roundExtractor (p := p) q₀ x output).terminalState path).Witness) :
    (roundExtractor (p := p) q₀ x output).extractWitness path w = terminalWitnessEquiv (p := p) q₀ x output path w :=
  wire_extract_eq q₀ x output (steps p) [] (InputRelation x output) path w

/-- The terminal predicate pins the extracted witness to the PCS table and both openings. -/
theorem roundExtractor_terminal_iff {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (path : (protocol E p).ExecutionPath)
    (w : ((roundExtractor (p := p) q₀ x output).terminalState path).Witness) :
    ((roundExtractor (p := p) q₀ x output).terminalState path).holds w ↔
      let q := (roundExtractor (p := p) q₀ x output).extractWitness path w
      q = q₀ ∧ endpointClaim (p := p) x output (pathMessages (steps p) path) q := by
  change ((wireExtractor (p := p) q₀ x output (steps p) [] (InputRelation x output)).terminalState path).holds w ↔ _
  rw [wire_terminal_iff q₀ x output (steps p) [] (InputRelation x output) path w, finishHistory_eq]
  have hn : (steps p).isEmpty = false := by
    cases h : steps p with
    | nil => exact False.elim (steps_ne_nil p h)
    | cons => rfl
  simp only [hn, Bool.false_eq_true, ite_false, List.nil_append]
  change _ ↔ (let q := (wireExtractor (p := p) q₀ x output (steps p) [] (InputRelation x output)).extractWitness path w
    q = q₀ ∧ endpointClaim (p := p) x output (pathMessages (steps p) path) q)
  rw [wire_extract_eq]

/-- All authored prover messages preserve the aligned fixed-table prefix state. -/
theorem wireExtractor_proverPreserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (nodes : List (WireStep × Cut)) (history : List (List E))
    (aligned : (cuts p).drop history.length = nodes.map Prod.snd)
    (valid : MessageBoundaryChain p nodes) :
    (wireExtractor q₀ x output (nodes.map Prod.fst) history
      (nextPrefixClaim x output (nodes.map Prod.fst) history)).IsProverPreserving
      (wireRoles E (nodes.map Prod.fst)) := by
  induction nodes generalizing history with
  | nil => trivial
  | cons node rest ih =>
    rcases node with ⟨step, c⟩
    cases step with
    | message n =>
      constructor
      · intro message _ w good
        exact ⟨good.1, prefix_message_preserving x output w n c rest history message aligned valid.1 good.2⟩
      · intro message
        exact ih (history ++ [List.ofFn message])
          (cuts_drop_append history _ _ c rest aligned) valid.2
    | challenge kind =>
      constructor
      · intro r ownership
        cases ownership
      · intro r
        exact ih (history ++ [[r]]) (cuts_drop_append history _ _ c rest aligned) valid.2

/-- The committed-table extractor preserves knowledge across every prover-authored prefix. -/
theorem roundExtractor_proverPreserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) :
    (roundExtractor q₀ x output).IsProverPreserving (roles E p) := by
  obtain ⟨rest, hrest⟩ := scheduleNodes_first p
  have hsteps : steps p = .challenge (.initialInstance 0) :: rest.map Prod.fst := by
    rw [← scheduleNodes_steps, hrest]
    rfl
  change (wireExtractor q₀ x output (steps p) [] (InputRelation x output)).IsProverPreserving
    (wireRoles E (steps p))
  rw [hsteps]
  constructor
  · intro r ownership
    cases ownership
  · intro r
    apply wireExtractor_proverPreserving
    · simp only [List.nil_append, List.length_cons, List.length_nil, cuts, hrest,
        List.map_cons, List.drop_succ_cons, List.drop_zero]
    · have h := scheduleNodes_messageBoundaryChain p
      rw [hrest] at h
      exact h.2

/-- The identity extractor inherits every bound in the aligned fixed-prefix schedule. -/
theorem wireExtractor_locallyBounded {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (output : Fin (2^(p+4)) → Fin 25 → E)
    (nodes : List (WireStep × Cut)) (history : List (List E))
    (aligned : (cuts p).drop history.length = nodes.map Prod.snd)
    (valid : PrefixBoundChain x output q₀ history.length nodes) :
    (wireExtractor q₀ x output (nodes.map Prod.fst) history
      (nextPrefixClaim x output (nodes.map Prod.fst) history)).IsLocallyBounded
      (wireRoles E (nodes.map Prod.fst)) (wireChallenges E (nodes.map Prod.fst)) := by
  induction nodes generalizing history with
  | nil => trivial
  | cons node rest ih =>
    rcases node with ⟨step, c⟩
    cases step with
    | message n =>
      intro message
      apply ih (history ++ [List.ofFn message]) (cuts_drop_append history _ _ c rest aligned)
      simpa only [PrefixBoundChain, List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using valid
    | challenge kind =>
      obtain ⟨⟨after, hhead, bound⟩, later⟩ := valid
      have restNonempty : (rest.map Prod.fst).isEmpty = false := by
        cases rest with
        | nil => cases hhead
        | cons => rfl
      constructor
      · apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
        intro _ _
        change Pr{let r ← uniformField E}[RoundExtractor.badChallenge
          (wireExtractor q₀ x output (.challenge kind :: rest.map Prod.fst) history
            (nextPrefixClaim x output (.challenge kind :: rest.map Prod.fst) history)) r] ≤ _
        have target : (cuts p)[history.length+1]? = some after := by
          have h := congrArg (fun l : List Cut => l.head?)
            (cuts_drop_append history ([] : List E) _ c rest aligned)
          simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
            List.head?_drop, List.head?_map, hhead] using h
        have hb := bound history rfl (cuts_getElem_of_drop _ c rest aligned) target
        refine (prEvent_mono (uniformField E) _ _ ?_).trans hb
        intro r bad
        have h := (wireExtractor_badChallenge_iff q₀ x output kind (rest.map Prod.fst)
          history (nextPrefixClaim x output (.challenge kind :: rest.map Prod.fst) history) r).mp bad
        simpa only [nextPrefixClaim, List.isEmpty_cons, Bool.false_eq_true, ite_false,
          restNonempty] using h
      · intro r
        apply ih (history ++ [[r]]) (cuts_drop_append history _ _ c rest aligned)
        simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using later

/-- The schedule starts with two instance-coordinate challenges and their initial cuts. -/
theorem scheduleNodes_first_two (p : Nat) :
    ∃ rest, scheduleNodes p = (.challenge (.initialInstance 0), .start 0) ::
      (.challenge (.initialInstance 1), .start 1) :: rest := by
  simp only [scheduleNodes, show p+4 = (p+2+1)+1 from rfl, List.range_succ_eq_map,
    List.map_cons, List.map_map, List.cons_append, Function.comp_def]
  exact ⟨_, rfl⟩

/-- Every verifier prefix of the committed-table extractor has its concrete challenge loss. -/
theorem roundExtractor_locallyBounded {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (hx : IndependentLanePowers x)
    (output : Fin (2^(p+4)) → Fin 25 → E) :
    (roundExtractor q₀ x output).IsLocallyBounded (roles E p) (challenges E p) := by
  obtain ⟨rest, hrest⟩ := scheduleNodes_first_two p
  have hsteps : steps p = .challenge (.initialInstance 0) ::
      .challenge (.initialInstance 1) :: rest.map Prod.fst := by
    rw [← scheduleNodes_steps, hrest]
    rfl
  change (wireExtractor q₀ x output (steps p) [] (InputRelation x output)).IsLocallyBounded
    (wireRoles E (steps p)) (wireChallenges E (steps p))
  rw [hsteps]
  constructor
  · apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
    intro _ _
    change Pr{let r ← uniformField E}[RoundExtractor.badChallenge
      (wireExtractor q₀ x output (.challenge (.initialInstance 0) ::
        .challenge (.initialInstance 1) :: rest.map Prod.fst) [] (InputRelation x output)) r] ≤ _
    change _ ≤ ((Challenge.initialInstance 0).numerator : ENNReal) / Fintype.card E
    simp only [Challenge.numerator, Nat.cast_one]
    have source : (cuts p)[0]? = some (.start 0) := by
      simp only [cuts, hrest, List.map_cons, List.getElem?_cons_zero]
    have target : (cuts p)[1]? = some (.start 1) := by
      simp only [cuts, hrest, List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero]
    have hb := prefix_root_local_bound x hx output q₀ source target
    refine (prEvent_mono (uniformField E) _ _ ?_).trans hb
    intro r bad
    have h := (wireExtractor_badChallenge_iff q₀ x output (.initialInstance 0)
      (.challenge (.initialInstance 1) :: rest.map Prod.fst) [] (InputRelation x output) r).mp bad
    simpa only [nextPrefixClaim, List.isEmpty_cons, Bool.false_eq_true, ite_false,
      List.nil_append] using h
  · intro r
    apply wireExtractor_locallyBounded q₀ x output
      ((.challenge (.initialInstance 1), .start 1) :: rest) [[r]]
    · simp only [cuts, hrest, List.map_cons, List.length_cons, List.length_nil,
        List.drop_succ_cons, List.drop_zero]
    · have h := scheduleNodes_prefixBoundChain x output q₀
      rw [hrest] at h
      exact h.2



/-- The public-coin certificate for the table supplied by the enclosing PCS extraction. -/
noncomputable def certificate {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (hx : IndependentLanePowers x)
    (output : Fin (2^(p+4)) → Fin 25 → E) :
    KnowledgeCertificate (protocol E p) (roles E p) (inputState (p := p) q₀ x output) where
  extractor := roundExtractor (p := p) q₀ x output
  challenges := challenges E p
  prover_preserving := roundExtractor_proverPreserving q₀ x output
  local_bound := roundExtractor_locallyBounded q₀ x hx output

/-- The named certificate samples exactly the concrete uniform challenge schedule. -/
theorem certificate_challenges {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (hx : IndependentLanePowers x)
    (output : Fin (2^(p+4)) → Fin 25 → E) :
    (certificate (p := p) q₀ x hx output).challenges = challenges E p := rfl

/-- The named certificate's extraction data retains the terminal witness unchanged. -/
theorem certificate_extract_eq {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (hx : IndependentLanePowers x)
    (output : Fin (2^(p+4)) → Fin 25 → E) (path : (protocol E p).ExecutionPath)
    (w : ((certificate (p := p) q₀ x hx output).extractor.terminalState path).Witness) :
    (certificate (p := p) q₀ x hx output).extractor.extractWitness path w = terminalWitnessEquiv (p := p) q₀ x output path w :=
  roundExtractor_extract_eq q₀ x output path w

/-- Terminal knowledge is exactly the fixed-table binding, acceptance, and both opening relations. -/
theorem certificate_terminal_iff {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q₀ : Witness p) (x : E) (hx : IndependentLanePowers x)
    (output : Fin (2^(p+4)) → Fin 25 → E) (path : (protocol E p).ExecutionPath)
    (w : ((certificate (p := p) q₀ x hx output).extractor.terminalState path).Witness) :
    ((certificate (p := p) q₀ x hx output).extractor.terminalState path).holds w ↔
      let q := (certificate (p := p) q₀ x hx output).extractor.extractWitness path w
      q = q₀ ∧ endpointClaim (p := p) x output (pathMessages (steps p) path) q :=
  roundExtractor_terminal_iff q₀ x output path w

end CompStark.Keccak.Gkr
