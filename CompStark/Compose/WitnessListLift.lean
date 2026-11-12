/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compose.ListLift
public import ArkLib.Interaction.Oracle.Security.WitnessAppend

/-! Executable finite candidate unions and predicate transports for witness refinements. -/

@[expose] public section
namespace Interaction.Oracle.Security.StandardBcs
open OracleComp
open scoped ENNReal

/-- A local union input carries the public real list bound as an erased invariant. -/
structure BoundedInputs {Challenge : Type} [SampleableType Challenge]
    (schema : BadSchema Challenge) (bound : Erased ℝ) where
  /-- Local inputs for the actual decoded candidates. -/
  inputs : List schema.Input
  /-- Decoder correctness bounds the number of candidates. -/
  length_le : (inputs.length : ℝ) ≤ bound.out

/-- A finite candidate union pays the list length times the fixed-input error. -/
theorem prob_list_bad_le {Challenge : Type} [SampleableType Challenge]
    (schema : BadSchema Challenge) (inputs : List schema.Input) :
    Pr{let α ←$ᵗ Challenge}[∃ input ∈ inputs, schema.Bad input α] ≤
      (inputs.length : ENNReal) * schema.error.out := by
  induction inputs with
  | nil => simp only [List.not_mem_nil, false_and, exists_false, prEvent_false,
      List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | cons head tail ih =>
      simp only [List.mem_cons, exists_eq_or_imp]
      refine (prEvent_or_le _ _ _).trans ?_
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
        using add_le_add (schema.bad_bound head) ih

/-- Candidate unions preserve each local event, revealing order, executable decision and real bound. -/
def BadSchema.listUnion {Challenge : Type} [SampleableType Challenge]
    (schema : BadSchema Challenge) (bound : Erased ℝ) : BadSchema Challenge where
  Input := BoundedInputs schema bound
  equality := schema.equality
  isQuery := schema.isQuery
  complete input := input.inputs.all schema.complete
  MaskLE small large := ∀ input ∈ small.inputs, ∃ next ∈ large.inputs, schema.MaskLE input next
  Bad input α := ∃ candidate ∈ input.inputs, schema.Bad candidate α
  check input α := input.inputs.any fun candidate => schema.check candidate α
  check_iff input α := by simp only [List.any_eq_true, schema.check_iff]
  monotone _ _ subset complete α bad := by
    obtain ⟨input, member, bad⟩ := bad
    obtain ⟨next, nextMember, larger⟩ := subset input member
    exact ⟨next, nextMember, schema.monotone input next larger
      (fun query => List.all_eq_true.mp (complete query) input member) α bad⟩
  error := Erased.mk (ENNReal.ofReal bound.out * schema.error.out)
  bad_bound input := by
    simp only [Erased.out_mk]
    exact (prob_list_bad_le schema input.inputs).trans
      (mul_le_mul' (by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal input.length_le) le_rfl)

/-- Lift every public schema through the same prefix-fixed candidate union. -/
def BadSchemas.listUnion (bound : Erased ℝ) : {protocol : Protocol} → (coin : PublicCoin protocol) →
    BadSchemas coin → BadSchemas coin
  | _, .done, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, schemas =>
      fun move => listUnion bound (next move) (schemas move)
  | _, @PublicCoin.oracle _ _ _ _ next, schemas => listUnion bound next schemas
  | _, @PublicCoin.challenge _ _ _ next, schemas =>
      (schemas.1.listUnion bound, listUnion bound next schemas.2)

/-- Candidate-indexed annotations retained once for a finite union. -/
abbrev BadAnnotation.Entries {I : Type} {protocol : Protocol} (coin : PublicCoin protocol)
    (schemas : BadSchemas coin) {states : I → KnowledgeState}
    (family : (i : I) → RoundExtractor protocol.tree (states i)) :=
  List ((i : I) × BadAnnotation coin schemas (family i))

/-- Traverse retained candidate annotations without rebuilding their earlier physical interpretations. -/
def BadAnnotation.listUnionEntries {I : Type} [DecidableEq I] (candidates : List I)
    (bound : Erased ℝ) :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (schemas : BadSchemas coin) →
    {states : I → KnowledgeState} → (family : (i : I) → RoundExtractor protocol.tree (states i)) →
    (entries : Entries coin schemas family) →
    (entries.length : ℝ) ≤ bound.out →
    (∀ i ∈ candidates, ∃ entry ∈ entries, entry.1 = i) →
    BadAnnotation coin (BadSchemas.listUnion bound coin schemas)
      (ListLift.extractor candidates.toFinset family)
  | _, .done, _, _, _, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, schemas, _, family, entries, length, covers =>
      fun move => listUnionEntries candidates bound (next move) (schemas move)
        (fun i => (family i move).2.2) (entries.map fun entry => ⟨entry.1, entry.2 move⟩)
        (by simpa only [List.length_map] using length)
        (by
          intro i member
          obtain ⟨entry, present, same⟩ := covers i member
          exact ⟨⟨entry.1, entry.2 move⟩, List.mem_map.mpr ⟨entry, present, rfl⟩, same⟩)
  | _, @PublicCoin.oracle _ _ _ _ next, schemas, _, family, entries, length, covers =>
      fun word => listUnionEntries candidates bound next schemas
        (fun i => (family i word).2.2) (entries.map fun entry => ⟨entry.1, entry.2 word⟩)
        (by simpa only [List.length_map] using length)
        (by
          intro i member
          obtain ⟨entry, present, same⟩ := covers i member
          exact ⟨⟨entry.1, entry.2 word⟩, List.mem_map.mpr ⟨entry, present, rfl⟩, same⟩)
  | _, @PublicCoin.challenge _ _ _ next, schemas, _, family, entries, length, covers =>
      ⟨⟨entries.map (fun entry => entry.2.1), by
          simpa only [List.length_map] using length⟩,
        (fun α bad => by
          obtain ⟨i, member, escape⟩ := ListLift.badChallenge_subset candidates.toFinset family α bad
          obtain ⟨⟨j, annotation⟩, present, same⟩ := covers i (List.mem_toFinset.mp member)
          dsimp only at same
          subst j
          exact ⟨annotation.1, List.mem_map.mpr ⟨⟨i, annotation⟩, present, rfl⟩,
            annotation.2.1 α escape⟩),
        fun α => listUnionEntries candidates bound next schemas.2
          (fun i => (family i α).2.2) (entries.map fun entry => ⟨entry.1, entry.2.2.2 α⟩)
          (by simpa only [List.length_map] using length)
          (by
            intro i member
            obtain ⟨entry, present, same⟩ := covers i member
            exact ⟨⟨entry.1, entry.2.2.2 α⟩, List.mem_map.mpr ⟨entry, present, rfl⟩, same⟩)⟩

/-- Candidate annotations compose over the same explicit decoder list at every public prefix. -/
def BadAnnotation.listUnion {I : Type} [DecidableEq I] (candidates : List I)
    (bound : Erased ℝ) (length_le : (candidates.length : ℝ) ≤ bound.out)
    {protocol : Protocol} (coin : PublicCoin protocol) (schemas : BadSchemas coin)
    {states : I → KnowledgeState}
    (family : (i : I) → RoundExtractor protocol.tree (states i))
    (annotation : (i : I) → BadAnnotation coin schemas (family i)) :
    BadAnnotation coin (BadSchemas.listUnion bound coin schemas)
      (ListLift.extractor candidates.toFinset family) :=
  listUnionEntries candidates bound coin schemas family (candidates.map fun i => ⟨i, annotation i⟩)
    (by simpa only [List.length_map] using length_le)
    (by
      intro i member
      exact ⟨⟨i, annotation i⟩, List.mem_map.mpr ⟨i, member, rfl⟩, rfl⟩)

/-- A public fixed frame preserves the unframed refinement's input and escape event. -/
def BadAnnotation.frame (gate : Prop) : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (schemas : BadSchemas coin) → {state : KnowledgeState} →
    (extractor : RoundExtractor protocol.tree state) → BadAnnotation coin schemas extractor →
    BadAnnotation coin schemas (ListLift.frameExtractor gate extractor)
  | _, .done, _, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, schemas, _, extractor, annotation =>
      fun move => frame gate (next move) (schemas move) (extractor move).2.2 (annotation move)
  | _, @PublicCoin.oracle _ _ _ _ next, schemas, _, extractor, annotation =>
      fun word => frame gate next schemas (extractor word).2.2 (annotation word)
  | _, @PublicCoin.challenge _ _ _ next, schemas, _, extractor, annotation =>
      ⟨annotation.1, (fun α bad => annotation.2.1 α (ListLift.frame_bad_subset gate extractor α bad)),
        fun α => frame gate next schemas.2 (extractor α).2.2 (annotation.2.2 α)⟩

/-- Root rebasing changes no local event when its backward map preserves true knowledge. -/
def BadAnnotation.rebase {state target : KnowledgeState}
    (backward : state.Witness → target.Witness)
    (preserves : ∀ witness, state.holds witness → target.holds (backward witness)) :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (schemas : BadSchemas coin) →
    (nonempty : protocol.tree ≠ .done) → (extractor : RoundExtractor protocol.tree state) →
    BadAnnotation coin schemas extractor →
    BadAnnotation coin schemas (ListLift.rebaseExtractor nonempty extractor backward)
  | _, .done, _, nonempty, _, _ => False.elim (nonempty rfl)
  | _, @PublicCoin.sender _ _ _ _, _, _, _, annotation => annotation
  | _, @PublicCoin.oracle _ _ _ _ _, _, _, _, annotation => annotation
  | _, @PublicCoin.challenge _ _ _ _, _, _, _, annotation =>
      ⟨annotation.1, (fun α bad => by
        obtain ⟨witness, absent, good⟩ := bad
        exact annotation.2.1 α ⟨witness, (fun known => absent (preserves _ known)), good⟩),
        annotation.2.2⟩

end Interaction.Oracle.Security.StandardBcs
