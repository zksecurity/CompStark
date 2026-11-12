/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compose.Transport
public import CompStark.Keccak.Gkr.Knowledge


set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

/-! Physical-carrier transport of a restricted Keccak wire extractor. -/

@[expose] public section

namespace CompStark.Tables.Composed

open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp


/-- Pull a Keccak wire suffix onto a physical carrier, retaining the same public-claim frame. -/
def wirePullLabels {W F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) :
    (steps : List Keccak.Gkr.WireStep) → List (List F) → (W → Prop) →
      ListLift.Labels W (Keccak.Gkr.wireTree F steps)
  | [], _, current => current
  | .message _ :: rest, history, current => ⟨current, fun message =>
      wirePullLabels view frame x output rest (history ++ [List.ofFn message])
        (fun q => frame q ∧ Keccak.Gkr.nextPrefixClaim x output rest
          (history ++ [List.ofFn message]) (view q))⟩
  | .challenge _ :: rest, history, current => ⟨current, fun challenge =>
      wirePullLabels view frame x output rest (history ++ [[challenge]])
        (fun q => frame q ∧ Keccak.Gkr.nextPrefixClaim x output rest
          (history ++ [[challenge]]) (view q))⟩

/-- A pulled wire suffix exposes its supplied root predicate. -/
theorem input_wirePullLabels {W F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (steps : List Keccak.Gkr.WireStep)
    (history : List (List F)) (current : W → Prop) :
    ListLift.input (wirePullLabels view frame x output steps history current) = current := by
  cases steps with
  | nil => rfl
  | cons step rest => cases step <;> rfl

/-- A framed restriction of Keccak prefixes preserves knowledge at every prover move. -/
theorem wirePull_retained_preserving {W F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (fixed : W) :
    (steps : List Keccak.Gkr.WireStep) → (history : List (List F)) →
    (source : Keccak.Gkr.Witness p → Prop) → (current : W → Prop) →
    (∀ q, frame q → source (view q) → current q) →
    (Keccak.Gkr.wireExtractor (view fixed) x output steps history source).IsProverPreserving
      (Keccak.Gkr.wireRoles F steps) →
    (ListLift.retained (ListLift.map (fun predicate q => q = fixed ∧ predicate q)
      (wirePullLabels view frame x output steps history current))).IsProverPreserving
        (Keccak.Gkr.wireRoles F steps)
  | [], _, _, _, _, _ => trivial
  | .message n :: rest, history, source, current, root, preserving => by
      refine ⟨?_, fun message => wirePull_retained_preserving view frame x output fixed rest
        (history ++ [List.ofFn message]) _ _ (fun _ good known => ⟨good, known⟩) (preserving.2 message)⟩
      intro message sender q good
      change W at q
      change q = fixed ∧ current q
      change ListLift.input (ListLift.map (fun predicate q => q = fixed ∧ predicate q)
        (wirePullLabels view frame x output rest (history ++ [List.ofFn message]) _)) q at good
      rw [ListLift.input_map, input_wirePullLabels] at good
      exact ⟨good.1, root q good.2.1
        ((preserving.1 message sender (view q) ⟨congrArg view good.1, good.2.2⟩).2)⟩
  | .challenge kind :: rest, history, source, current, root, preserving => by
      refine ⟨?_, fun r => wirePull_retained_preserving view frame x output fixed rest
        (history ++ [[r]]) _ _ (fun _ good known => ⟨good, known⟩) (preserving.2 r)⟩
      intro _ impossible
      cases impossible

/-- Every pulled-back verifier escape is an escape of the fixed Keccak bit witness. -/
theorem wirePull_bad_subset {W F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (fixed : W)
    (kind : Keccak.Gkr.Challenge) (rest : List Keccak.Gkr.WireStep) (history : List (List F))
    (source : Keccak.Gkr.Witness p → Prop) (current : W → Prop)
    (root : ∀ q, frame q → source (view q) → current q) (r : F) :
    RoundExtractor.badChallenge
      (ListLift.retained (ListLift.map (fun predicate q => q = fixed ∧ predicate q)
        (wirePullLabels view frame x output (.challenge kind :: rest) history current))) r →
      RoundExtractor.badChallenge (Keccak.Gkr.wireExtractor (view fixed) x output
        (.challenge kind :: rest) history source) r := by
  rintro ⟨q, bad, good⟩
  change W at q
  change ¬ (q = fixed ∧ current q) at bad
  change ListLift.input (ListLift.map (fun predicate q => q = fixed ∧ predicate q)
    (wirePullLabels view frame x output rest (history ++ [[r]]) _)) q at good
  rw [ListLift.input_map, input_wirePullLabels] at good
  refine ⟨view q, ?_, congrArg view good.1, good.2.2⟩
  intro known
  exact bad ⟨good.1, root q good.2.1 known.2⟩

/-- A physical wire suffix inherits the standalone Keccak challenge bounds. -/
theorem wirePull_retained_bounded {W F : Type} [Field F] [Fintype F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (fixed : W) :
    (steps : List Keccak.Gkr.WireStep) → (history : List (List F)) →
    (source : Keccak.Gkr.Witness p → Prop) → (current : W → Prop) →
    (∀ q, frame q → source (view q) → current q) →
    (Keccak.Gkr.wireExtractor (view fixed) x output steps history source).IsLocallyBounded
      (Keccak.Gkr.wireRoles F steps) (Keccak.Gkr.wireChallenges F steps) →
    (ListLift.retained (ListLift.map (fun predicate q => q = fixed ∧ predicate q)
      (wirePullLabels view frame x output steps history current))).IsLocallyBounded
        (Keccak.Gkr.wireRoles F steps) (Keccak.Gkr.wireChallenges F steps)
  | [], _, _, _, _, _ => trivial
  | .message _ :: rest, history, _, _, _, bounded =>
      fun message => wirePull_retained_bounded view frame x output fixed rest
        (history ++ [List.ofFn message]) _ _ (fun _ good known => ⟨good, known⟩) (bounded message)
  | .challenge kind :: rest, history, source, current, root, bounded => by
      refine ⟨?_, fun r => wirePull_retained_bounded view frame x output fixed rest
        (history ++ [[r]]) _ _ (fun _ good known => ⟨good, known⟩) (bounded.2 r)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro round context
      exact (prEvent_mono _ _ _ (wirePull_bad_subset view frame x output fixed kind rest history
        source current root)).trans
          ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp bounded.1 round context)

/-- Equality binding preserves the pulled suffix's prover laws at its authored root. -/
theorem wirePull_preserving {W F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (fixed : W)
    (steps : List Keccak.Gkr.WireStep) (history : List (List F))
    (source : Keccak.Gkr.Witness p → Prop) (current : W → Prop)
    (root : ∀ q, frame q → source (view q) → current q)
    (preserving : (Keccak.Gkr.wireExtractor (view fixed) x output steps history source).IsProverPreserving
      (Keccak.Gkr.wireRoles F steps)) :
    (ListLift.boundExtractor fixed (wirePullLabels view frame x output steps history current)).IsProverPreserving
      (Keccak.Gkr.wireRoles F steps) :=
  RoundExtractor.isProverPreserving_changeInputState
    (ListLift.retained (ListLift.map (fun predicate q => q = fixed ∧ predicate q)
      (wirePullLabels view frame x output steps history current)))
    (ListLift.bound fixed (ListLift.input (wirePullLabels view frame x output steps history current)))
    (Equiv.refl W) (fun q => by rw [ListLift.input_map]; exact Iff.rfl) _
    (wirePull_retained_preserving view frame x output fixed steps history source current root preserving)

/-- Equality binding preserves the pulled suffix's authored local bounds. -/
theorem wirePull_bounded {W F : Type} [Field F] [Fintype F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (fixed : W)
    (steps : List Keccak.Gkr.WireStep) (history : List (List F))
    (source : Keccak.Gkr.Witness p → Prop) (current : W → Prop)
    (root : ∀ q, frame q → source (view q) → current q)
    (bounded : (Keccak.Gkr.wireExtractor (view fixed) x output steps history source).IsLocallyBounded
      (Keccak.Gkr.wireRoles F steps) (Keccak.Gkr.wireChallenges F steps)) :
    (ListLift.boundExtractor fixed (wirePullLabels view frame x output steps history current)).IsLocallyBounded
      (Keccak.Gkr.wireRoles F steps) (Keccak.Gkr.wireChallenges F steps) :=
  RoundExtractor.isLocallyBounded_changeInputState
    (ListLift.retained (ListLift.map (fun predicate q => q = fixed ∧ predicate q)
      (wirePullLabels view frame x output steps history current)))
    (ListLift.bound fixed (ListLift.input (wirePullLabels view frame x output steps history current)))
    (Equiv.refl W) (fun q => by rw [ListLift.input_map]; exact Iff.rfl) _ _
    (wirePull_retained_bounded view frame x output fixed steps history source current root bounded)

/-- Restricting the Keccak schedule preserves every deterministic message boundary. -/
theorem messageBoundaryChain_drop (p : ℕ) (nodes : List (Keccak.Gkr.WireStep × Keccak.Gkr.Cut))
    (valid : Keccak.Gkr.MessageBoundaryChain p nodes) (count : ℕ) :
    Keccak.Gkr.MessageBoundaryChain p (nodes.drop count) := by
  induction count generalizing nodes with
  | zero => exact valid
  | succ count ih =>
      cases nodes with
      | nil => trivial
      | cons node rest => exact ih rest valid.2

/-- Restricting a Keccak bound chain advances its offset by the number of removed moves. -/
theorem prefixBoundChain_drop {F : Type} [Field F] [Fintype F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (nodes : List (Keccak.Gkr.WireStep × Keccak.Gkr.Cut)) (offset count : ℕ)
    (valid : Keccak.Gkr.PrefixBoundChain x output q offset nodes) :
    Keccak.Gkr.PrefixBoundChain x output q (offset + count) (nodes.drop count) := by
  induction count generalizing nodes offset with
  | zero => exact valid
  | succ count ih =>
      cases nodes with
      | nil => trivial
      | cons node rest =>
          rcases node with ⟨step, cut⟩
          have later : Keccak.Gkr.PrefixBoundChain x output q (offset + 1) rest := by
            cases step with
            | message => exact valid
            | challenge => exact valid.2
          simpa only [List.drop_succ_cons, Nat.add_assoc, Nat.add_comm 1 count] using
            ih rest (offset + 1) later

/-- The suffix after the recycled instance coordinates inherits the full certificate's prover laws. -/
theorem wireSuffix_preserving {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (count : ℕ) (history : List (List F)) (length : history.length = count) :
    (Keccak.Gkr.wireExtractor q x output ((Keccak.Gkr.steps p).drop count) history
      (Keccak.Gkr.nextPrefixClaim x output ((Keccak.Gkr.steps p).drop count) history)).IsProverPreserving
        (Keccak.Gkr.wireRoles F ((Keccak.Gkr.steps p).drop count)) := by
  have steps := congrArg (List.drop count) (Keccak.Gkr.scheduleNodes_steps p)
  rw [← List.map_drop] at steps
  rw [← steps]
  apply Keccak.Gkr.wireExtractor_proverPreserving
  · simp only [length, Keccak.Gkr.cuts, List.map_drop]
  · exact messageBoundaryChain_drop p _ (Keccak.Gkr.scheduleNodes_messageBoundaryChain p) count

/-- The restricted Keccak suffix keeps all local errors of the standalone schedule. -/
theorem wireSuffix_bounded {F : Type} [Field F] [Fintype F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (count : ℕ) (history : List (List F)) (length : history.length = count) :
    (Keccak.Gkr.wireExtractor q x output ((Keccak.Gkr.steps p).drop count) history
      (Keccak.Gkr.nextPrefixClaim x output ((Keccak.Gkr.steps p).drop count) history)).IsLocallyBounded
        (Keccak.Gkr.wireRoles F ((Keccak.Gkr.steps p).drop count))
        (Keccak.Gkr.wireChallenges F ((Keccak.Gkr.steps p).drop count)) := by
  have steps := congrArg (List.drop count) (Keccak.Gkr.scheduleNodes_steps p)
  rw [← List.map_drop] at steps
  rw [← steps]
  apply Keccak.Gkr.wireExtractor_locallyBounded
  · simp only [length, Keccak.Gkr.cuts, List.map_drop]
  · simpa only [length, Nat.zero_add] using prefixBoundChain_drop x output q _ 0 count
      (Keccak.Gkr.scheduleNodes_prefixBoundChain x output q)

/-- Removing the externally supplied instance draws leaves the segment challenge first. -/
theorem wireSuffix_first (p : ℕ) : ∃ rest,
    (Keccak.Gkr.steps p).drop (p + 4) = .challenge .segment :: rest := by
  unfold Keccak.Gkr.steps
  simp only [List.append_assoc]
  rw [List.drop_left' (by simp only [List.length_map, List.length_range])]
  exact ⟨_, rfl⟩

/-- The semantic cut immediately after the external instance prefix is the segment cut. -/
theorem instancePrefix_cut (p : ℕ) : (Keccak.Gkr.cuts p)[p + 4]? = some (.start (p + 4)) := by
  simp only [Keccak.Gkr.cuts, Keccak.Gkr.scheduleNodes, List.map_append, List.map_map,
    List.map_cons, List.map_nil, List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; exact le_rfl)]
  simp only [List.length_map, List.length_range, Nat.sub_self, List.cons_append, List.nil_append, List.getElem?_cons_zero]

/-- A retained Keccak prefix at the external instance point supplies every remaining segment/lane identity. -/
theorem instancePrefix_identity {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (point : Fin (p + 4) → F)
    (known : Keccak.Gkr.nextPrefixClaim x output ((Keccak.Gkr.steps p).drop (p + 4))
      (List.ofFn fun i => [point i]) q) :
    ∀ full : Fin (p + 10) → F, (∀ i : Fin (p + 4), full ⟨i.val, by omega⟩ = point i) →
      Keccak.Gkr.initialIdentity x output q full := by
  obtain ⟨rest, first⟩ := wireSuffix_first p
  rw [first] at known
  change Keccak.Gkr.prefixClaim x output (List.ofFn fun i => [point i]) q at known
  have cut : (Keccak.Gkr.cuts p)[(List.ofFn fun i => [point i]).length]? = some (.start (p + 4)) := by
    rw [List.length_ofFn]
    exact instancePrefix_cut p
  obtain ⟨t, authored, _, identity⟩ := (Keccak.Gkr.prefixClaim_at x output _ q _ cut).mp known
  have fixed (i : Fin (p + 4)) : Keccak.Gkr.initialPoint t ⟨i.val, by omega⟩ = point i := by
    have read := Keccak.Gkr.authored_getElem_eq (List.ofFn fun i => [point i]) _ _ authored
      (List.prefix_refl _) i.val (by rw [List.length_ofFn]; exact i.isLt)
    rw [Keccak.Gkr.transcriptMessages_get_initial t ⟨i.val, by omega⟩] at read
    simp only [List.getElem?_ofFn, i.isLt, dite_true, Fin.eta] at read
    exact List.singleton_inj.mp (Option.some.inj read)
  intro full agrees
  apply identity
  intro coordinate bounded
  exact (agrees ⟨coordinate.val, bounded⟩).trans (fixed ⟨coordinate.val, bounded⟩).symm

/-- The physical wire suffix ends at the same accepted opening relation as its Keccak source. -/
theorem wirePull_terminalPredicate {W F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (view : W → Keccak.Gkr.Witness p) (frame : W → Prop) (x : F)
    (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (steps : List Keccak.Gkr.WireStep)
    (history : List (List F)) (current : W → Prop)
    (path : (Keccak.Gkr.wireTree F steps).ExecutionPath) (q : W) :
    ListLift.terminalPredicate (wirePullLabels view frame x output steps history current) path q ↔
      if steps.isEmpty then current q else frame q ∧
        Keccak.Gkr.endpointClaim x output (Keccak.Gkr.finishHistory steps history path) (view q) := by
  induction steps generalizing history current with
  | nil => exact Iff.rfl
  | cons step rest ih =>
      cases step with
      | message n =>
          have law := ih (history ++ [List.ofFn path.1])
            (fun q => frame q ∧ Keccak.Gkr.nextPrefixClaim x output rest
              (history ++ [List.ofFn path.1]) (view q)) path.2
          cases rest <;> exact law
      | challenge kind =>
          have law := ih (history ++ [[(show F from path.1)]])
            (fun q => frame q ∧ Keccak.Gkr.nextPrefixClaim x output rest
              (history ++ [[(show F from path.1)]]) (view q)) path.2
          cases rest <;> exact law

end CompStark.Tables.Composed
