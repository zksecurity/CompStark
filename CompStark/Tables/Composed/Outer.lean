/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Pool
public import CompStark.Compose.Reduction
public import CompStark.Compose.Transport

/-! The reductions between the commitment and the opening, on the committed stack: the bus, the table
sumcheck with the external argument's rider on its draws, and the external argument framed by the
pool. Each is the component's certificate pulled back to the stack through `External.interpret`. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp

/-- The side conditions of a composed system: well formed, buses of one width each, a stack that
fits `M` variables, boundary columns that are committed, and the argument for the virtual
columns. -/
structure Setup (S : System K) (L : Layout S.tables.length) (k M : ℕ) where
  /-- The width of each bus's tuples. -/
  width : String → ℕ
  /-- The system is well formed. -/
  wellFormed : S.WellFormed L
  /-- Each bus has one width, and its encoded tuples fit `2 ^ k` entries. -/
  busShape : S.BusShape k width
  /-- The stack fits `M` variables. -/
  fits : (S.stackBlocks L).total ≤ 2 ^ M
  /-- The bus opens committed columns only. -/
  boundary : ∀ p ∈ S.boundaryColumns L, p.2 ∈ S.committedColumns p.1
  /-- The table sumcheck's round degree leaves room for distinct interpolation points. -/
  degree_le : TableSumcheck.degree S L + 2 ≤ 2 ^ 64 - 1
  /-- The argument for the virtual columns. -/
  external : External S L k M

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (setup : Setup S L k M)

/-- The bus phase's endpoint on the stack: the bus endpoint of the interpreted witness and the
rider before any draw. -/
def busRelation : Option (Bus.Output S L k) → Whir.Table K M → Prop
  | none, _ => False
  | some o, q => Bus.Terminal S L k o (setup.external.interpret q) ∧ setup.external.rider [] q

/-- The bus certificate pulled back to the stack, framed by the rider before any draw. -/
noncomputable def busReduction :
    Reduction (Bus.protocol S L k) (Whir.Table K M) (Option (Bus.Output S L k)) :=
  componentReduction (Bus.protocol S L k)
    (pullLabels setup.external.interpret (setup.external.rider []) (Bus.labels S L k))
    (Bus.outputClaim S L k) (busRelation setup) (Bus.challenges S L k)
    (fun fixed ↦ Bus.certificate setup.wellFormed setup.busShape (setup.external.interpret fixed))
    (fun fixed preserving bounded ↦
      ⟨pull_preserving setup.external.interpret (setup.external.rider []) fixed (Bus.labels S L k)
        _ preserving,
       pull_bounded setup.external.interpret (setup.external.rider []) fixed (Bus.labels S L k)
        _ _ bounded⟩)
    (by
      have endpoint := pull_endpoint (Bus.protocol S L k) setup.external.interpret
        (setup.external.rider []) (Bus.labels S L k) (Bus.outputClaim S L k)
        (fun out q ↦ match out with | none => False | some out => Bus.Terminal S L k out q)
        (fun fixed ↦ (Bus.terminalRelation S L k fixed).knowledge_iff)
      intro fixed path witness
      refine (endpoint fixed path witness).trans ?_
      apply and_congr_right
      intro _
      cases Bus.outputClaim S L k path with
      | none => exact and_iff_left_of_imp False.elim
      | some out => exact Iff.rfl)

/-- The table phase's endpoint on the stack: its checks passed, the bus point has the bus's depth,
the pool holds on the stack, and the external argument's start relation holds. -/
def tableEndpoint : Option (TableSumcheck.Output S L k) → Whir.Table K M → Prop
  | none, _ => False
  | some o, q => o.active = true ∧ o.bus.point.length = Bus.μ S L ∧
      (∀ c ∈ pool S L k M o, c.Holds (fun u ↦ ofK (q u))) ∧
      Retained.input (setup.external.labels o) q

/-- An interpreted witness agrees with its stack on the committed columns. -/
theorem agrees_interpret (q : Whir.Table K M) : Agrees S L M (setup.external.interpret q) q :=
  ⟨fun t i c hc _ ↦ setup.external.interpret_committed q t i c hc⟩

/-- The table phase's endpoint gives the table sumcheck's terminal relation on the interpreted
witness and the rider on the table's draws. -/
theorem table_final (bus : Bus.Output S L k) (χ : List E) (vals : TableSumcheck.Values S L)
    (active : Bool) (q : Whir.Table K M)
    (known : tableEndpoint setup (some ⟨bus, χ.reverse, vals, active⟩) q) :
    TableSumcheck.Terminal S L k ⟨bus, χ.reverse, vals, active⟩ (setup.external.interpret q) ∧
      setup.external.rider χ q := by
  obtain ⟨hactive, hpoint, hpool, hstart⟩ := known
  obtain ⟨boundary, committed⟩ := (pool_holds_iff setup.fits setup.boundary _ q
    (agrees_interpret setup q) _).mp hpool
  obtain ⟨rider, virtual⟩ := setup.external.start_sound _ q hstart
  refine ⟨⟨hactive, ⟨setup.external.interpret_shaped q, hpoint, boundary⟩, ?_⟩, ?_⟩
  · intro t i
    cases hv : TableSumcheck.virtualAt S t.1 (TableSumcheck.transmitted S t.1)[i]
    · exact committed t i hv
    · exact virtual t i hv
  · simpa only [List.reverse_reverse] using rider

/-- The table rounds' prefix predicates on the stack: the round relation of the interpreted witness
and the rider on the draws so far. -/
def tableRoundsLabels (bus : Bus.Output S L k) (ξ : E) :
    (n : ℕ) → List E → E → Bool →
      ListLift.Labels (Whir.Table K M) (TableSumcheck.roundsProtocol S L n).tree
  | 0, χ, current, active =>
      ⟨fun q ↦ TableSumcheck.roundRelation S L k bus ξ χ current active (setup.external.interpret q) ∧
        setup.external.rider χ q,
        fun vals ↦ tableEndpoint setup (some ⟨bus, χ.reverse, vals,
          active && decide (TableSumcheck.formula S L k bus ξ χ.reverse vals = current)⟩)⟩
  | n + 1, χ, current, active =>
      ⟨fun q ↦ TableSumcheck.roundRelation S L k bus ξ χ current active (setup.external.interpret q) ∧
        setup.external.rider χ q,
        fun message ↦
          ⟨fun q ↦ TableSumcheck.roundRelation S L k bus ξ χ current active
              (setup.external.interpret q) ∧ setup.external.rider χ q,
            fun
            | none => fun _ ↦ False
            | some r => tableRoundsLabels bus ξ n (χ ++ [r])
                ((TableSumcheck.messageOps S L).evaluate current message r)
                (active && (TableSumcheck.messageOps S L).accept current message)⟩⟩

/-- A round's labels start at its round relation and rider. -/
theorem input_tableRoundsLabels (bus : Bus.Output S L k) (ξ : E) (n : ℕ) (χ : List E) (current : E)
    (active : Bool) :
    ListLift.input (tableRoundsLabels setup bus ξ n χ current active) =
      fun q ↦ TableSumcheck.roundRelation S L k bus ξ χ current active (setup.external.interpret q) ∧
        setup.external.rider χ q := by
  cases n <;> rfl

/-- The transmitted values preserve the round relation and the rider. -/
theorem tableRounds_retained_preserving (bus : Bus.Output S L k) (ξ : E) (fixed : Whir.Table K M)
    (n : ℕ) (χ : List E) (current : E) (active : Bool)
    (length : χ.length + n = TableSumcheck.maxHeight S L) :
    (ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
      (tableRoundsLabels setup bus ξ n χ current active))).IsProverPreserving
        (TableSumcheck.roundsProtocol S L n).roles := by
  induction n generalizing χ current active with
  | zero =>
      refine ⟨?_, fun _ ↦ trivial⟩
      intro vals _ q good
      change Whir.Table K M at q
      change q = fixed ∧ tableEndpoint setup (some ⟨bus, χ.reverse, vals,
        active && decide (TableSumcheck.formula S L k bus ξ χ.reverse vals = current)⟩) q at good
      obtain ⟨terminal, rider⟩ := table_final setup bus χ vals _ q good.2
      have known := (TableSumcheck.rounds_prover_preserving setup.wellFormed bus ξ
        (setup.external.interpret fixed) 0 χ current active length).1 vals rfl
        (setup.external.interpret q) ⟨congrArg setup.external.interpret good.1, terminal⟩
      exact ⟨good.1, known.2, rider⟩
  | succ n ih =>
      refine ⟨fun _ _ good ↦ good, fun message ↦ ⟨?_, ?_⟩⟩
      · intro _ impossible
        cases impossible
      · intro choice
        cases choice with
        | none => trivial
        | some r =>
            apply ih
            simp only [List.length_append, List.length_singleton]
            omega

/-- A round's challenge makes a false rider true with probability at most `1 / |E|`. -/
theorem tableRider_option_le (χ : List E) (q : Whir.Table K M) (current : E)
    (message : TableSumcheck.Message S L) (remaining : χ.length < TableSumcheck.maxHeight S L) :
    Pr{let choice ← Sumcheck.Interaction.Knowledge.nextChallenge (TableSumcheck.messageOps S L)
        current message}[
      ∃ r, choice = some r ∧ ¬ setup.external.rider χ q ∧ setup.external.rider (χ ++ [r]) q] ≤
        overE 1 := by
  classical
  by_cases accepted : (TableSumcheck.messageOps S L).accept current message = true
  · rw [Sumcheck.Interaction.Knowledge.nextChallenge, accepted, ite_eq_left rfl, prEvent_map]
    have bound := setup.external.rider_local q χ remaining
    simpa only [Option.some.injEq, exists_eq_left'] using bound
  · rw [Sumcheck.Interaction.Knowledge.nextChallenge, ite_eq_right accepted, prEvent_pure]
    simp only [reduceCtorEq, false_and, exists_false, ↓reduceIte, zero_le]

/-- A round errs with probability at most `(degree + 1) / |E|`: a false round relation is the
sumcheck's bad event, and otherwise only the rider can turn true. -/
theorem tableRounds_local_le (bus : Bus.Output S L k) (ξ : E) (fixed : Whir.Table K M)
    (n : ℕ) (χ : List E) (current : E) (active : Bool) (message : TableSumcheck.Message S L)
    (length : χ.length + (n + 1) = TableSumcheck.maxHeight S L) :
    Pr{let choice ← Sumcheck.Interaction.Knowledge.nextChallenge (TableSumcheck.messageOps S L)
        current message}[
      RoundExtractor.badChallenge
        ((ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
          (tableRoundsLabels setup bus ξ (n + 1) χ current active)) message).2.2) choice] ≤
        overE (TableSumcheck.degree S L + 1) := by
  classical
  have unpack (choice : Option E) (bad : RoundExtractor.badChallenge
      ((ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
        (tableRoundsLabels setup bus ξ (n + 1) χ current active)) message).2.2) choice) :
      ∃ r, choice = some r ∧
        ¬ (TableSumcheck.roundRelation S L k bus ξ χ current active (setup.external.interpret fixed) ∧
          setup.external.rider χ fixed) ∧
        TableSumcheck.roundRelation S L k bus ξ (χ ++ [r])
          ((TableSumcheck.messageOps S L).evaluate current message r)
          (active && (TableSumcheck.messageOps S L).accept current message)
          (setup.external.interpret fixed) ∧
        setup.external.rider (χ ++ [r]) fixed := by
    obtain ⟨q, absent, good⟩ := bad
    change Whir.Table K M at q
    cases choice with
    | none => exact False.elim good.2
    | some r =>
        change ListLift.input (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
          (tableRoundsLabels setup bus ξ n (χ ++ [r])
            ((TableSumcheck.messageOps S L).evaluate current message r)
            (active && (TableSumcheck.messageOps S L).accept current message))) q at good
        rw [ListLift.input_map, input_tableRoundsLabels] at good
        obtain ⟨rfl, known⟩ := good
        exact ⟨r, rfl, fun known ↦ absent ⟨rfl, known⟩, known⟩
  by_cases source : TableSumcheck.roundRelation S L k bus ξ χ current active
      (setup.external.interpret fixed)
  · apply le_trans (prEvent_mono _ _ (fun choice ↦ ∃ r, choice = some r ∧
        ¬ setup.external.rider χ fixed ∧ setup.external.rider (χ ++ [r]) fixed) ?_)
    · have degree : overE 1 ≤ overE (TableSumcheck.degree S L + 1) := by
        unfold overE
        exact ENNReal.div_le_div_right (by exact_mod_cast Nat.le_add_left 1 _) _
      exact (tableRider_option_le setup χ fixed current message (by omega)).trans degree
    · intro choice bad
      obtain ⟨r, equal, absent, _, rider⟩ := unpack choice bad
      exact ⟨r, equal, fun old ↦ absent ⟨source, old⟩, rider⟩
  · apply le_trans (prEvent_mono _ _ _ ?_) (TableSumcheck.round_local_le setup.wellFormed bus
      (setup.external.interpret fixed) ξ n χ current active message length)
    intro choice bad
    obtain ⟨r, rfl, _, known, _⟩ := unpack choice bad
    refine ⟨setup.external.interpret fixed, fun old ↦ source old.2, rfl, ?_⟩
    change Retained.input (TableSumcheck.roundsLabels S L k bus ξ n (χ ++ [r])
      ((TableSumcheck.messageOps S L).evaluate current message r)
      (active && (TableSumcheck.messageOps S L).accept current message))
      (setup.external.interpret fixed)
    rw [TableSumcheck.roundsLabels_input_eq]
    exact known

/-- Every remaining round meets its local bound. -/
theorem tableRounds_retained_bounded (bus : Bus.Output S L k) (ξ : E) (fixed : Whir.Table K M)
    (n : ℕ) (χ : List E) (current : E) (active : Bool)
    (length : χ.length + n = TableSumcheck.maxHeight S L) :
    (ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
      (tableRoundsLabels setup bus ξ n χ current active))).IsLocallyBounded
        (TableSumcheck.roundsProtocol S L n).roles (TableSumcheck.roundsChallenges S L n current) := by
  induction n generalizing χ current active with
  | zero => intro vals; trivial
  | succ n ih =>
      intro message
      refine ⟨?_, ?_⟩
      · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
        intro _ _
        exact tableRounds_local_le setup bus ξ fixed n χ current active message length
      · intro choice
        cases choice with
        | none => trivial
        | some r =>
            apply ih
            simp only [List.length_append, List.length_singleton]
            omega

/-- The table phase's prefix predicates on the stack, starting at the bus phase's endpoint. -/
def tableLabels (bus : Bus.Output S L k) :
    ListLift.Labels (Whir.Table K M) (TableSumcheck.protocol S L).tree :=
  ⟨fun q ↦ Bus.Terminal S L k bus (setup.external.interpret q) ∧ setup.external.rider [] q,
    fun ξ ↦ tableRoundsLabels setup bus ξ (TableSumcheck.maxHeight S L) []
      (TableSumcheck.target S L k bus ξ) bus.active⟩

/-- The table phase's extractor is prover-preserving. -/
theorem table_retained_preserving (bus : Bus.Output S L k) (fixed : Whir.Table K M) :
    (ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
      (tableLabels setup bus))).IsProverPreserving (TableSumcheck.protocol S L).roles := by
  refine ⟨?_, fun ξ ↦ tableRounds_retained_preserving setup bus ξ fixed _ [] _ _
    (by simp only [List.length_nil, Nat.zero_add])⟩
  intro _ impossible
  cases impossible

/-- A bad `ξ` on the stack is a bad `ξ` of the table sumcheck at the interpreted witness. -/
theorem table_xi_bad_subset (bus : Bus.Output S L k) (fixed : Whir.Table K M) (ξ : E) :
    RoundExtractor.badChallenge (ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
      (tableLabels setup bus))) ξ →
      RoundExtractor.badChallenge (TableSumcheck.extractor S L k bus (setup.external.interpret fixed)) ξ := by
  rintro ⟨q, absent, good⟩
  change Whir.Table K M at q
  change ListLift.input (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
    (tableRoundsLabels setup bus ξ (TableSumcheck.maxHeight S L) [] (TableSumcheck.target S L k bus ξ)
      bus.active)) q at good
  rw [ListLift.input_map, input_tableRoundsLabels] at good
  refine ⟨setup.external.interpret q, ?_, congrArg setup.external.interpret good.1, ?_⟩
  · rintro ⟨_, source⟩
    exact absent ⟨good.1, source, good.2.2⟩
  · change Retained.input (TableSumcheck.roundsLabels S L k bus ξ (TableSumcheck.maxHeight S L) []
      (TableSumcheck.target S L k bus ξ) bus.active) (setup.external.interpret q)
    rw [TableSumcheck.roundsLabels_input_eq]
    exact good.2.1

/-- The table phase's extractor meets the table sumcheck's schedule. -/
theorem table_retained_bounded (bus : Bus.Output S L k) (fixed : Whir.Table K M) :
    (ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
      (tableLabels setup bus))).IsLocallyBounded
        (TableSumcheck.protocol S L).roles (TableSumcheck.challenges S L k bus) := by
  refine ⟨?_, fun ξ ↦ tableRounds_retained_bounded setup bus ξ fixed _ [] _ _
    (by simp only [List.length_nil, Nat.zero_add])⟩
  rw [_root_.RoundByRound.GameFamily.isBounded_iff]
  intro _ _
  exact (prEvent_mono _ _ _ (table_xi_bad_subset setup bus fixed)).trans
    (TableSumcheck.xi_local_le setup.wellFormed bus (setup.external.interpret fixed))

/-- The table phase's labels and output parser identify the same endpoint. -/
theorem tableRounds_endpoint (bus : Bus.Output S L k) (ξ : E) (n : ℕ) (χ : List E) (current : E)
    (active : Bool) (path : (TableSumcheck.roundsProtocol S L n).tree.ExecutionPath)
    (q : Whir.Table K M) :
    ListLift.terminalPredicate (tableRoundsLabels setup bus ξ n χ current active) path q ↔
      tableEndpoint setup (TableSumcheck.roundsOutput S L k bus ξ n χ current active path) q := by
  induction n generalizing χ current active with
  | zero => exact Iff.rfl
  | succ n ih =>
      rcases path with ⟨message, choice, path⟩
      cases choice with
      | none => exact ⟨False.elim, fun known ↦ known.elim⟩
      | some r => exact ih _ _ _ path

/-- A rejected bus leaves the table rounds' draws without knowledge. -/
noncomputable def rejectedTableRounds : (n : ℕ) → RoundExtractor.ChallengeSchedule
    (TableSumcheck.roundsProtocol S L n).tree (TableSumcheck.roundsProtocol S L n).roles
  | 0 => ⟨PUnit.unit, fun _ ↦ PUnit.unit⟩
  | n + 1 => fun _ ↦ ⟨⟨pure none, overE (TableSumcheck.degree S L + 1)⟩, fun
      | none => PUnit.unit
      | some _ => rejectedTableRounds n⟩

/-- The table sumcheck on the stack from the bus phase's output; a rejected bus has no knowledge. -/
noncomputable def tableReduction : Option (Bus.Output S L k) →
    Reduction (TableSumcheck.protocol S L) (Whir.Table K M) (Option (TableSumcheck.Output S L k))
  | none => reduction (TableSumcheck.protocol S L) (falseLabels _ _)
      (fun _ ↦ none) (tableEndpoint setup)
      ⟨⟨$ᵗ E, overE (TableSumcheck.constraintCount S + 2)⟩,
        fun _ ↦ rejectedTableRounds (TableSumcheck.maxHeight S L)⟩
      (fun fixed ↦ false_preserving fixed _ _)
      (fun fixed ↦ false_bounded fixed _ _ _)
      (by
        intro fixed path witness
        change _ ↔ ListLift.boundTerminalEquiv fixed (falseLabels _ _) path witness = fixed ∧
          tableEndpoint setup none (ListLift.boundTerminalEquiv fixed (falseLabels _ _) path witness)
        rw [ListLift.bound_terminal_holds, terminalPredicate_falseLabels]
        simp only [tableEndpoint, and_false])
  | some bus => reduction (TableSumcheck.protocol S L) (tableLabels setup bus)
      (TableSumcheck.outputClaim S L k bus) (tableEndpoint setup)
      (TableSumcheck.challenges S L k bus)
      (fun fixed ↦ RoundExtractor.isProverPreserving_changeInputState
        (ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
          (tableLabels setup bus)))
        (ListLift.bound fixed (ListLift.input (tableLabels setup bus))) (Equiv.refl _)
        (fun q ↦ by rw [ListLift.input_map]; exact Iff.rfl) _
        (table_retained_preserving setup bus fixed))
      (fun fixed ↦ RoundExtractor.isLocallyBounded_changeInputState
        (ListLift.retained (ListLift.map (fun predicate q ↦ q = fixed ∧ predicate q)
          (tableLabels setup bus)))
        (ListLift.bound fixed (ListLift.input (tableLabels setup bus))) (Equiv.refl _)
        (fun q ↦ by rw [ListLift.input_map]; exact Iff.rfl) _ _
        (table_retained_bounded setup bus fixed))
      (endpoint_of_terminalPredicate _ _ _ _ (by
        intro path q
        exact tableRounds_endpoint setup bus path.1 _ [] _ _ path.2 q))

/-- The table phase's checks, point and pool, which the external argument carries through. -/
def tableGate (o : TableSumcheck.Output S L k) (q : Whir.Table K M) : Prop :=
  o.active = true ∧ o.bus.point.length = Bus.μ S L ∧
    ∀ c ∈ pool S L k M o, c.Holds (fun u ↦ ofK (q u))

/-- The external phase's endpoint: the table phase's checks, point and pool, and the external
argument's output. -/
def externalRelation : Option (TableSumcheck.Output S L k) → StackOutput M → Whir.Table K M → Prop
  | none, _, _ => False
  | some o, out, q => out.Holds q ∧ tableGate o q

/-- The schedule of the external argument after a rejected table phase. -/
def rejectedOutput : TableSumcheck.Output S L k :=
  ⟨⟨0, 0, [], 0, 0, false⟩, [], fun _ _ ↦ 0, false⟩

/-- The external argument on the stack from the table phase's output, framed by the table phase's
checks and pool; a rejected table phase has no knowledge. -/
noncomputable def externalReduction : Option (TableSumcheck.Output S L k) →
    Reduction setup.external.protocol (Whir.Table K M) (StackOutput M)
  | none => reduction setup.external.protocol (falseLabels _ _)
      (fun _ ↦ (⟨[], false⟩ : StackOutput M))
      (externalRelation (none : Option (TableSumcheck.Output S L k)))
      (setup.external.challenges (rejectedOutput : TableSumcheck.Output S L k))
      (fun fixed ↦ false_preserving fixed _ _)
      (fun fixed ↦ false_bounded fixed _ _ _)
      (by
        intro fixed path witness
        change _ ↔ ListLift.boundTerminalEquiv fixed (falseLabels _ _) path witness = fixed ∧
          externalRelation (none : Option (TableSumcheck.Output S L k)) _
            (ListLift.boundTerminalEquiv fixed (falseLabels _ _) path witness)
        rw [ListLift.bound_terminal_holds, terminalPredicate_falseLabels]
        simp only [externalRelation, and_false])
  | some o => reduction setup.external.protocol
      (pullLabels id (tableGate o) (setup.external.labels o))
      (setup.external.output o) (externalRelation (some o))
      (setup.external.challenges o)
      (fun fixed ↦ pull_preserving id (tableGate o) fixed (setup.external.labels o) _
        (setup.external.preserving o fixed))
      (fun fixed ↦ pull_bounded id (tableGate o) fixed (setup.external.labels o) _ _
        (setup.external.bounded o fixed))
      (pull_endpoint setup.external.protocol id (tableGate o) (setup.external.labels o)
        (setup.external.output o) (fun out q ↦ out.Holds q) (by
          intro fixed path witness
          rw [Retained.terminal_iff, setup.external.endpoint]
          exact Iff.rfl))

/-- The bus, the table sumcheck and the external argument in sequence. -/
def outerProtocol : Protocol :=
  appendProtocol (appendProtocol (Bus.protocol S L k) (TableSumcheck.protocol S L))
    setup.external.protocol

/-- The outer reductions in sequence on the stack. -/
noncomputable def outerReduction :
    Reduction (outerProtocol setup) (Whir.Table K M)
      ((Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M) :=
  ((busReduction setup).then (tableReduction setup) (by
      intro bus q
      cases bus with
      | none =>
        simp only [tableReduction, reduction, busReduction, componentReduction, busRelation,
          input_falseLabels]
      | some bus => exact Iff.rfl)).then
    (fun claim ↦ externalReduction setup claim.2) (by
      intro claim q
      rcases claim with ⟨bus, table⟩
      change (externalReduction setup table).input q ↔ (tableReduction setup bus).relation table q
      cases bus <;> cases table <;>
      first
      | (change ListLift.input (falseLabels _ _) q ↔ False; rw [input_falseLabels])
      | (change ListLift.input (pullLabels id _ _) q ↔ tableEndpoint setup (some _) q
         rw [input_pullLabels]
         simp only [id, tableEndpoint, tableGate]
         exact ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h2, h3, h4, h1⟩, fun ⟨h2, h3, h4, h1⟩ ↦ ⟨h1, h2, h3, h4⟩⟩))

/-- The claims the opening owes: the pool and the external argument's claims. -/
def openingClaims : (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M →
    List (Whir.Claim E M)
  | ((_, none), _) => []
  | ((_, some o), out) => pool S L k M o ++ out.claims

/-- The outer protocol's public checks. -/
def publicAccepted : (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M →
    Prop
  | ((_, none), _) => False
  | ((_, some o), out) => o.active = true ∧ o.bus.point.length = Bus.μ S L ∧ out.active = true

/-- The outer endpoint is the public checks and the opening claims on the stack. -/
theorem outer_endpoint_iff
    (out : (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M)
    (q : Whir.Table K M) :
    (outerReduction setup).relation out q ↔
      publicAccepted out ∧ ∀ c ∈ openingClaims out, c.Holds (fun u ↦ ofK (q u)) := by
  rcases out with ⟨⟨bus, table⟩, eo⟩
  cases table with
  | none => exact ⟨False.elim, fun h ↦ h.1.elim⟩
  | some o =>
    change externalRelation (some o) eo q ↔ _
    simp only [externalRelation, StackOutput.Holds, tableGate, publicAccepted, openingClaims,
      List.mem_append]
    constructor
    · rintro ⟨⟨ea, ec⟩, ta, tp, tc⟩
      exact ⟨⟨ta, tp, ea⟩, fun c hc ↦ hc.elim (tc c) (ec c)⟩
    · rintro ⟨⟨ta, tp, ea⟩, hc⟩
      exact ⟨⟨ea, fun c h ↦ hc c (Or.inr h)⟩, ta, tp, fun c h ↦ hc c (Or.inl h)⟩

/-- The outer reductions start at the bus's input relation on the interpreted witness and the
rider before any draw. -/
theorem outer_input_iff (q : Whir.Table K M) :
    (outerReduction setup).input q ↔
      Bus.Input S L (setup.external.interpret q) ∧ setup.external.rider [] q := by
  change ListLift.input (pullLabels setup.external.interpret (setup.external.rider []) (Bus.labels S L k)) q ↔ _
  rw [input_pullLabels]
  exact Iff.rfl

/-- The table sumcheck's output after the bus's. -/
def tableOutput : Option (Bus.Output S L k) → (TableSumcheck.protocol S L).tree.ExecutionPath →
    Option (TableSumcheck.Output S L k)
  | none, _ => none
  | some o, path => TableSumcheck.outputClaim S L k o path

/-- The table phase's parser is the table sumcheck's after the bus's output. -/
theorem tableReduction_output (setup : Setup S L k M) (bus : Option (Bus.Output S L k))
    (path : (TableSumcheck.protocol S L).tree.ExecutionPath) :
    (tableReduction setup bus).output path = tableOutput bus path := by
  cases bus <;> rfl

/-- The external argument's output after the table sumcheck's. -/
def externalOutput (setup : Setup S L k M) : Option (TableSumcheck.Output S L k) →
    setup.external.protocol.tree.ExecutionPath → StackOutput M
  | none, _ => ⟨[], false⟩
  | some o, path => setup.external.output o path

/-- The external phase's parser is the argument's after the table sumcheck's output. -/
theorem externalReduction_output (setup : Setup S L k M) (table : Option (TableSumcheck.Output S L k))
    (path : setup.external.protocol.tree.ExecutionPath) :
    (externalReduction setup table).output path = externalOutput setup table path := by
  cases table <;> rfl

/-- The outer endpoint parsed from a transcript: the bus's, then the table sumcheck's at it, then
the external argument's at that. -/
def outerOutput (setup : Setup S L k M) (path : (outerProtocol setup).tree.ExecutionPath) :
    (Option (Bus.Output S L k) × Option (TableSumcheck.Output S L k)) × StackOutput M :=
  let parts := splitPath (appendProtocol (Bus.protocol S L k) (TableSumcheck.protocol S L))
    setup.external.protocol path
  let first := splitPath (Bus.protocol S L k) (TableSumcheck.protocol S L) parts.1
  let bus := Bus.outputClaim S L k first.1
  let table := tableOutput bus first.2
  ((bus, table), externalOutput setup table parts.2)

/-- The direct parser is the outer reductions' parser. -/
theorem outerOutput_eq (setup : Setup S L k M) (path : (outerProtocol setup).tree.ExecutionPath) :
    outerOutput setup path = (outerReduction setup).output path := by
  unfold outerReduction
  rw [Reduction.then_output, Reduction.then_output, externalReduction_output, tableReduction_output]
  rfl

end CompStark.Tables.Composed
