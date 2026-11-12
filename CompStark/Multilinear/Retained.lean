/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Knowledge

/-! Identity backward maps on concrete public/oracle transcript trees. Predicates are separately authored at each prefix and always bind the retained witness to the fixed committed object. -/

@[expose] public section

namespace CompStark.Multilinear.Retained

open Interaction Interaction.Oracle Interaction.Oracle.Security

/-- Predicates at every concrete prefix; oracle payloads index predicates without changing the public tree. -/
def Labels (W : Type) : Oracle.TypeTree.{0} → Type
  | .done => W → Prop
  | .public M next => (W → Prop) × ((m : M) → Labels W (next m))
  | .oracle M next => (W → Prop) × (M → Labels W (next PUnit.unit))

/-- Predicate before the next move. -/
def input {W : Type} : {tree : Oracle.TypeTree} → Labels W tree → W → Prop
  | .done, p => p
  | .public _ _, p => p.1
  | .oracle _ _, p => p.1

/-- Bind the witness to the committed object at every prefix. -/
def state {W : Type} (q₀ : W) (p : W → Prop) : KnowledgeState :=
  ⟨W, fun w ↦ w = q₀ ∧ p w⟩

/-- Total identity maps; neither extraction nor witness selection inspects a knowledge proof. -/
def extractor {W : Type} (q₀ : W) : {tree : Oracle.TypeTree} →
    (p : Labels W tree) → RoundExtractor tree (state q₀ (input p))
  | .done, _ => PUnit.unit
  | .public _ _, p => fun m ↦ ⟨state q₀ (input (p.2 m)), id, extractor q₀ (p.2 m)⟩
  | .oracle _ _, p => fun m ↦ ⟨state q₀ (input (p.2 m)), id, extractor q₀ (p.2 m)⟩

/-- Identity extraction computes only the public tree while retaining erased predicate indices. -/
def extractorErased {W : Type} (q : W) : {tree : Oracle.TypeTree} →
    (p : Erased (Labels W tree)) → RoundExtractor tree (state q (input p.out))
  | .done, _ => PUnit.unit
  | .public _ _, p => fun m =>
      ⟨state q (input (p.out.2 m)), id, by simpa only [Erased.out_mk] using extractorErased q (Erased.mk (p.out.2 m))⟩
  | .oracle _ _, p => fun m =>
      ⟨state q (input (p.out.2 m)), id, by simpa only [Erased.out_mk] using extractorErased q (Erased.mk (p.out.2 m))⟩

/-- The executable identity extractor erases its predicate-only labels. -/
def extractorPrepared {W : Type} (q : W) {tree : Oracle.TypeTree} (p : Labels W tree) :
    RoundExtractor tree (state q (input p)) := by
  simpa only [Erased.out_mk] using extractorErased q (Erased.mk p)

/-- Erasing authored labels preserves the complete dependent identity extractor. -/
theorem extractorErased_heq {W : Type} (q : W) {tree : Oracle.TypeTree}
    (e : Erased (Labels W tree)) (p : Labels W tree) (h : e.out = p) :
    HEq (extractorErased q e) (extractor q p) := by
  induction tree with
  | done => rfl
  | «public» M next ih =>
      subst p
      apply heq_of_eq
      funext m
      simp only [extractorErased, extractor]
      congr 2
      apply eq_of_heq
      exact (cast_heq _ _).trans (ih m _ _ (Erased.out_mk _))
  | «oracle» M next ih =>
      subst p
      apply heq_of_eq
      funext m
      simp only [extractorErased, extractor]
      congr 2
      apply eq_of_heq
      exact (cast_heq _ _).trans (ih _ _ (Erased.out_mk _))

/-- Runtime identity extraction agrees with the authored predicate-indexed extractor. -/
theorem extractorPrepared_eq {W : Type} (q : W) {tree : Oracle.TypeTree} (p : Labels W tree) :
    extractor q p = extractorPrepared q p := by
  symm
  unfold extractorPrepared
  apply eq_of_heq
  exact (cast_heq _ _).trans (extractorErased_heq q _ p (Erased.out_mk p))

/-- The compiler erases retained predicate labels through an exact function equality. -/
@[csimp] theorem extractor_code : @extractor = @extractorPrepared := by
  funext W q tree p
  exact extractorPrepared_eq q p

/-- Equality binding turns the existential public-challenge event into one fixed witness's false-to-true transition. -/
theorem public_badChallenge_iff {W M : Type} (q₀ : W) (p : W → Prop)
    {next : M → Oracle.TypeTree} (out : (m : M) → Labels W (next m)) (m : M) :
    RoundExtractor.badChallenge (extractor q₀ (show Labels W (.public M next) from ⟨p, out⟩)) m ↔
      ¬ p q₀ ∧ input (out m) q₀ := by
  change (∃ w, ¬ (w = q₀ ∧ p w) ∧ w = q₀ ∧ input (out m) w) ↔ _
  constructor
  · rintro ⟨w, bad, rfl, good⟩
    exact ⟨fun h ↦ bad ⟨rfl, h⟩, good⟩
  · rintro ⟨bad, good⟩
    exact ⟨q₀, fun h ↦ bad h.2, rfl, good⟩

/-- Concrete terminal carrier identification, with no existential choice of a witness. -/
def terminalEquiv {W : Type} (q₀ : W) : {tree : Oracle.TypeTree} →
    (p : Labels W tree) → (path : tree.ExecutionPath) →
    ((extractor q₀ p).terminalState path).Witness ≃ W
  | .done, _, _ => Equiv.refl W
  | .public _ _, p, path => terminalEquiv q₀ (p.2 path.1) path.2
  | .oracle _ _, p, path => terminalEquiv q₀ (p.2 path.1) path.2

/-- Complete-path extraction keeps the exact supplied stack. -/
theorem extract_eq {W : Type} (q₀ : W) {tree : Oracle.TypeTree} (p : Labels W tree)
    (path : tree.ExecutionPath) (w : ((extractor q₀ p).terminalState path).Witness) :
    (extractor q₀ p).extractWitness path w = terminalEquiv q₀ p path w := by
  induction tree with
  | done => rfl
  | «public» M next ih => exact ih path.1 (p.2 path.1) path.2 w
  | «oracle» M next ih => exact ih (p.2 path.1) path.2 w

/-- The authored predicate at the endpoint of a concrete transcript. -/
def endpoint {W : Type} : {tree : Oracle.TypeTree} → Labels W tree → tree.ExecutionPath → W → Prop
  | .done, p, _ => p
  | .public _ _, p, path => endpoint (p.2 path.1) path.2
  | .oracle _ _, p, path => endpoint (p.2 path.1) path.2

/-- Terminal knowledge is equality binding together with the authored endpoint predicate. -/
theorem terminal_iff {W : Type} (q₀ : W) {tree : Oracle.TypeTree} (p : Labels W tree)
    (path : tree.ExecutionPath) (w : ((extractor q₀ p).terminalState path).Witness) :
    ((extractor q₀ p).terminalState path).holds w ↔
      (state q₀ (endpoint p path)).holds (terminalEquiv q₀ p path w) := by
  induction tree with
  | done => rfl
  | «public» M next ih => exact ih path.1 (p.2 path.1) path.2 w
  | «oracle» M next ih => exact ih (p.2 path.1) path.2 w

/-- A deterministic prover with private coins fixed, retaining adaptive choices after each public challenge. -/
def Strategy : (tree : Oracle.TypeTree.{0}) → tree.RoleDecoration → Type
  | .done, _ => PUnit
  | .public M next, roles => match roles.1 with
    | .sender => (m : M) × Strategy (next m) (roles.2 m)
    | .receiver => (m : M) → Strategy (next m) (roles.2 m)
  | .oracle M next, roles => (_message : M) × Strategy (next PUnit.unit) (roles.2 PUnit.unit)

/-- Execute the public-coin schedule against a prover with fixed private coins. -/
def play : {tree : Oracle.TypeTree.{0}} → (roles : tree.RoleDecoration) →
    RoundExtractor.ChallengeSchedule tree roles → Strategy tree roles → ProbComp tree.ExecutionPath
  | .done, _, _, _ => pure PUnit.unit
  | .public _ _, ⟨.sender, roles⟩, schedule, strategy => do
      let rest ← play (roles strategy.1) (schedule.2 strategy.1) strategy.2
      return ⟨strategy.1, rest⟩
  | .public _ _, ⟨.receiver, roles⟩, schedule, strategy => do
      let r ← schedule.1.1
      let rest ← play (roles r) (schedule.2 r) (strategy r)
      return ⟨r, rest⟩
  | .oracle _ _, roles, schedule, strategy => do
      let rest ← play (roles.2 PUnit.unit) (schedule strategy.1) strategy.2
      return ⟨strategy.1, rest⟩

/-- An accepting endpoint witness whose named complete-path extraction fails at the input. -/
def Failure {tree : Oracle.TypeTree.{0}} {state : KnowledgeState}
    (extractor : RoundExtractor tree state) (path : tree.ExecutionPath) : Prop :=
  ∃ w : (extractor.terminalState path).Witness,
    (extractor.terminalState path).holds w ∧ ¬ state.holds (extractor.extractWitness path w)

/-- A true terminal problem witness supplies terminal knowledge through its explicit carrier equivalence. -/
theorem terminal_known {tree : Oracle.TypeTree} {state : KnowledgeState}
    {ext : RoundExtractor tree state} {Context : Type} {family : ClaimFamily Context}
    {problem : Problem family} {context : tree.ExecutionPath → Context}
    {claim : (path : tree.ExecutionPath) → family.Claim (context path)}
    (terminal : TerminalRelation ext problem context claim) (path : tree.ExecutionPath)
    (w : problem.Witness (context path) (claim path)) (known : problem.rel (context path) (claim path) w) :
    ∃ v : (ext.terminalState path).Witness, (ext.terminalState path).holds v := by
  refine ⟨(terminal.witnessEquiv path).symm w, (terminal.knowledge_iff path _).mpr ?_⟩
  simpa only [Equiv.apply_symm_apply] using known

/-- A uniform bound on the sum of challenge errors along every continuation. -/
def Budget : {tree : Oracle.TypeTree} → (roles : tree.RoleDecoration) →
    RoundExtractor.ChallengeSchedule tree roles → ENNReal → Prop
  | .done, _, _, _ => True
  | .public _ _, ⟨.sender, roles⟩, schedule, ε =>
      ∀ move, Budget (roles move) (schedule.2 move) ε
  | .public _ _, ⟨.receiver, roles⟩, schedule, ε =>
      ∃ δ, schedule.1.2 + δ ≤ ε ∧ ∀ move, Budget (roles move) (schedule.2 move) δ
  | .oracle _ _, roles, schedule, ε =>
      ∀ message, Budget (roles.2 PUnit.unit) (schedule message) ε

/-- Prover preservation and the local challenge bounds control actual extraction failure. -/
theorem failure_le {tree : Oracle.TypeTree} {state : KnowledgeState}
    (ext : RoundExtractor tree state) (roles : tree.RoleDecoration)
    (schedule : RoundExtractor.ChallengeSchedule tree roles)
    (preserving : ext.IsProverPreserving roles) (bounded : ext.IsLocallyBounded roles schedule)
    (ε : ENNReal) (budget : Budget roles schedule ε) (strategy : Strategy tree roles) :
    Pr{let path ← play roles schedule strategy}[Failure ext path] ≤ ε := by
  classical
  induction tree generalizing state ε with
  | done =>
      have empty (path : Oracle.TypeTree.done.ExecutionPath) : ¬ Failure ext path := by
        rintro ⟨w, hw, hn⟩
        exact hn hw
      simp only [play, prEvent_pure, empty, ↓reduceIte, zero_le]
  | «public» M next ih =>
      rcases roles with ⟨role, roles⟩
      cases role with
      | sender =>
          let move := strategy.1
          have inclusion (path : (next move).ExecutionPath) :
              Failure ext ⟨move, path⟩ → Failure (ext move).2.2 path := by
            rintro ⟨w, good, bad⟩
            refine ⟨w, good, fun h ↦ bad ?_⟩
            exact preserving.1 move rfl _ h
          simp only [play, map_bind, map_pure, bind_pure_comp]
          exact (prEvent_mono _ _ _ inclusion).trans
            (ih move (ext move).2.2 (roles move) (schedule.2 move)
              (preserving.2 move) (bounded move) ε (budget move) strategy.2)
      | receiver =>
          obtain ⟨δ, total, children⟩ := budget
          change Pr{let path ← schedule.1.1 >>= fun move ↦ do
            let rest ← play (roles move) (schedule.2 move) (strategy move)
            pure ⟨move, rest⟩}[Failure ext path] ≤ ε
          apply le_trans (prEvent_bind_le_prEvent_add schedule.1.1 _
            (RoundExtractor.badChallenge ext) _ (ε := δ) ?_)
          · have localBound := bounded.1
            rw [_root_.RoundByRound.GameFamily.isBounded_iff] at localBound
            exact (add_le_add (localBound () ()) (le_refl δ)).trans total
          · intro move good
            simp only [map_bind, map_pure, bind_pure_comp]
            apply le_trans (prEvent_mono _ _ (Failure (ext move).2.2) ?_)
            · exact ih move (ext move).2.2 (roles move) (schedule.2 move)
                (preserving.2 move) (bounded.2 move) δ (children move) (strategy move)
            · rintro path ⟨w, known, unknown⟩
              refine ⟨w, known, fun h ↦ good ?_⟩
              exact ⟨_, unknown, h⟩
  | «oracle» M next ih =>
      let move := strategy.1
      have inclusion (path : (next PUnit.unit).ExecutionPath) :
          Failure ext ⟨move, path⟩ → Failure (ext move).2.2 path := by
        rintro ⟨w, good, bad⟩
        exact ⟨w, good, fun h ↦ bad (preserving.1 move _ h)⟩
      simp only [play, bind_pure_comp, Functor.map_map]
      exact (prEvent_mono _ _ _ inclusion).trans
        (ih (ext move).2.2 (roles.2 PUnit.unit) (schedule move)
          (preserving.2 move) (bounded move) ε (budget move) strategy.2)

end CompStark.Multilinear.Retained
