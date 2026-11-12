/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compose.WitnessListLift

/-! Structural transport of revealing orders through prefix-indexed bad annotations. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Interaction.Oracle.Security.StandardBcs
open StateRestoration

/-- Each retained oracle message carries its own revealing relation. -/
def MessageOrders : {protocol : Protocol} → PublicCoin protocol → Type 1
  | _, .done => PUnit
  | _, @PublicCoin.sender _ _ _ next => (move : _) → MessageOrders (next move)
  | _, @PublicCoin.oracle Messages _ _ _ next => (Messages → Messages → Prop) × MessageOrders next
  | _, @PublicCoin.challenge _ _ _ next => MessageOrders next

/-- Related strict prefixes retain public data and challenges and extend each masked message. -/
def PrefixRelated {Com : Type} [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) → MessageOrders coin →
    (pre : Prefix PUnit (compiledCoin Com coin)) → PrefixMessages coin pre → PrefixMessages coin pre → Prop
  | _, .done, _, pre, _, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, orders, pre, small, large =>
      PrefixRelated (next pre.1) (orders pre.1) pre.2 small large
  | _, @PublicCoin.oracle _ _ _ _ next, orders, pre, small, large =>
      orders.1 small.1 large.1 ∧ PrefixRelated next orders.2 pre.2 small.2 large.2
  | _, @PublicCoin.challenge _ _ _ next, orders, pre, small, large => match pre with
      | .inl _ => True
      | .inr ⟨_, pre⟩ => small.1 = large.1 ∧ PrefixRelated next orders pre small.2 large.2

/-- Two annotations are ordered at every challenge after related oracle messages and identical public moves. -/
def BadAnnotation.Ordered : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (schemas : BadSchemas coin) → MessageOrders coin →
    {leftState rightState : KnowledgeState} →
    (left : RoundExtractor protocol.tree leftState) → (right : RoundExtractor protocol.tree rightState) →
    BadAnnotation coin schemas left → BadAnnotation coin schemas right → Prop
  | _, .done, _, _, _, _, _, _, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, schemas, orders, _, _, left, right, small, large =>
      ∀ move, Ordered (next move) (schemas move) (orders move) (left move).2.2 (right move).2.2
        (small move) (large move)
  | _, @PublicCoin.oracle _ _ _ _ next, schemas, orders, _, _, left, right, small, large =>
      ∀ a b, orders.1 a b → Ordered next schemas orders.2 (left a).2.2 (right b).2.2 (small a) (large b)
  | _, @PublicCoin.challenge _ _ _ next, schemas, orders, _, _, left, right, small, large =>
      schemas.1.MaskLE small.1 large.1 ∧
        ∀ value, Ordered next schemas.2 orders (left value).2.2 (right value).2.2
          (small.2.2 value) (large.2.2 value)

termination_by structural _ coin => coin

/-- Structural annotation order gives the exact schema order at every selected compiled key. -/
theorem annotatedInput_ordered {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) (schemas : BadSchemas coin) (orders : MessageOrders coin)
    {leftState rightState : KnowledgeState}
    (left : RoundExtractor protocol.tree leftState) (right : RoundExtractor protocol.tree rightState)
    (leftAnnotation : BadAnnotation coin schemas left) (rightAnnotation : BadAnnotation coin schemas right)
    (ordered : BadAnnotation.Ordered coin schemas orders left right leftAnnotation rightAnnotation)
    (pre : Prefix PUnit (compiledCoin Com coin)) (small large : PrefixMessages coin pre)
    (related : PrefixRelated coin orders pre small large) :
    (schemaAt coin schemas pre).MaskLE
      (annotatedInput coin schemas left leftAnnotation pre small)
      (annotatedInput coin schemas right rightAnnotation pre large) := by
  induction coin generalizing leftState rightState with
  | done => exact nomatch pre
  | sender next ih =>
      exact ih pre.1 (schemas pre.1) (orders pre.1) _ _ _ _
        (ordered pre.1) pre.2 small large related
  | oracle next ih =>
      exact ih schemas orders.2 _ _ _ _
        (ordered small.1 large.1 related.1) pre.2 small.2 large.2 related.2
  | challenge next ih =>
      cases pre with
      | inl salt => exact ordered.1
      | inr pair =>
          obtain ⟨salt, pre⟩ := pair
          rcases small with ⟨value, small⟩
          rcases large with ⟨other, large⟩
          obtain ⟨same, related⟩ := related
          cases same
          exact ih schemas.2 orders _ _ _ _ (ordered.2 value) pre small large related

/-- Candidate-union annotations preserve a matching order between their per-candidate entries. -/
theorem BadAnnotation.Ordered.listUnionEntries {I J : Type} [DecidableEq I] [DecidableEq J]
    (leftCandidates : List I) (rightCandidates : List J) (bound : Erased ℝ)
    {protocol : Protocol} (coin : PublicCoin protocol) (schemas : BadSchemas coin) (orders : MessageOrders coin)
    {leftStates : I → KnowledgeState} {rightStates : J → KnowledgeState}
    (leftFamily : (i : I) → RoundExtractor protocol.tree (leftStates i))
    (rightFamily : (i : J) → RoundExtractor protocol.tree (rightStates i))
    (leftEntries : BadAnnotation.Entries coin schemas leftFamily)
    (rightEntries : BadAnnotation.Entries coin schemas rightFamily)
    (leftLength : (leftEntries.length : ℝ) ≤ bound.out)
    (rightLength : (rightEntries.length : ℝ) ≤ bound.out)
    (leftCovers : ∀ i ∈ leftCandidates, ∃ entry ∈ leftEntries, entry.1 = i)
    (rightCovers : ∀ i ∈ rightCandidates, ∃ entry ∈ rightEntries, entry.1 = i)
    (related : ∀ small ∈ leftEntries, ∃ large ∈ rightEntries,
      BadAnnotation.Ordered coin schemas orders (leftFamily small.1) (rightFamily large.1) small.2 large.2) :
    BadAnnotation.Ordered coin (BadSchemas.listUnion bound coin schemas) orders
      (ListLift.extractor leftCandidates.toFinset leftFamily)
      (ListLift.extractor rightCandidates.toFinset rightFamily)
      (BadAnnotation.listUnionEntries leftCandidates bound coin schemas leftFamily leftEntries leftLength leftCovers)
      (BadAnnotation.listUnionEntries rightCandidates bound coin schemas rightFamily rightEntries rightLength rightCovers) := by
  induction coin generalizing leftStates rightStates with
  | done => trivial
  | sender next ih =>
      intro move
      apply ih move
      intro entry member
      obtain ⟨small, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨large, there, ordered⟩ := related small present
      exact ⟨⟨large.1, large.2 move⟩, List.mem_map.mpr ⟨large, there, rfl⟩, ordered move⟩
  | oracle next ih =>
      intro a b words
      apply ih
      intro entry member
      obtain ⟨small, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨large, there, ordered⟩ := related small present
      exact ⟨⟨large.1, large.2 b⟩, List.mem_map.mpr ⟨large, there, rfl⟩, ordered a b words⟩
  | challenge next ih =>
      constructor
      · intro input member
        obtain ⟨small, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨large, there, ordered⟩ := related small present
        exact ⟨large.2.1, List.mem_map.mpr ⟨large, there, rfl⟩, ordered.1⟩
      · intro value
        apply ih
        intro entry member
        obtain ⟨small, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨large, there, ordered⟩ := related small present
        exact ⟨⟨large.1, large.2.2.2 value⟩, List.mem_map.mpr ⟨large, there, rfl⟩, ordered.2 value⟩

/-- Enlarging a candidate list preserves annotation order when each retained candidate does. -/
theorem BadAnnotation.Ordered.listUnion {I : Type} [DecidableEq I]
    (smallCandidates largeCandidates : List I) (bound : Erased ℝ)
    (smallLength : (smallCandidates.length : ℝ) ≤ bound.out)
    (largeLength : (largeCandidates.length : ℝ) ≤ bound.out)
    (subset : ∀ i ∈ smallCandidates, i ∈ largeCandidates)
    {protocol : Protocol} (coin : PublicCoin protocol) (schemas : BadSchemas coin) (orders : MessageOrders coin)
    {leftStates rightStates : I → KnowledgeState}
    (leftFamily : (i : I) → RoundExtractor protocol.tree (leftStates i))
    (rightFamily : (i : I) → RoundExtractor protocol.tree (rightStates i))
    (leftAnnotation : (i : I) → BadAnnotation coin schemas (leftFamily i))
    (rightAnnotation : (i : I) → BadAnnotation coin schemas (rightFamily i))
    (related : ∀ i ∈ smallCandidates,
      BadAnnotation.Ordered coin schemas orders (leftFamily i) (rightFamily i)
        (leftAnnotation i) (rightAnnotation i)) :
    BadAnnotation.Ordered coin (BadSchemas.listUnion bound coin schemas) orders
      (ListLift.extractor smallCandidates.toFinset leftFamily)
      (ListLift.extractor largeCandidates.toFinset rightFamily)
      (BadAnnotation.listUnion smallCandidates bound smallLength coin schemas leftFamily leftAnnotation)
      (BadAnnotation.listUnion largeCandidates bound largeLength coin schemas rightFamily rightAnnotation) := by
  apply BadAnnotation.Ordered.listUnionEntries
  intro entry member
  obtain ⟨i, present, rfl⟩ := List.mem_map.mp member
  exact ⟨⟨i, rightAnnotation i⟩, List.mem_map.mpr ⟨i, subset i present, rfl⟩, related i present⟩

/-- Activity framing does not alter the local inputs or their revealing order. -/
theorem BadAnnotation.Ordered.frame (leftGate rightGate : Prop)
    {protocol : Protocol} (coin : PublicCoin protocol) (schemas : BadSchemas coin) (orders : MessageOrders coin)
    {leftState rightState : KnowledgeState}
    (left : RoundExtractor protocol.tree leftState) (right : RoundExtractor protocol.tree rightState)
    (leftAnnotation : BadAnnotation coin schemas left) (rightAnnotation : BadAnnotation coin schemas right)
    (ordered : BadAnnotation.Ordered coin schemas orders left right leftAnnotation rightAnnotation) :
    BadAnnotation.Ordered coin schemas orders (ListLift.frameExtractor leftGate left)
      (ListLift.frameExtractor rightGate right)
      (leftAnnotation.frame leftGate coin schemas left) (rightAnnotation.frame rightGate coin schemas right) := by
  induction coin generalizing leftState rightState with
  | done => trivial
  | sender next ih => exact fun move => ih move _ _ _ _ _ _ (ordered move)
  | oracle next ih => exact fun a b words => ih _ _ _ _ _ _ (ordered a b words)
  | challenge next ih => exact ⟨ordered.1, fun value => ih _ _ _ _ _ _ (ordered.2 value)⟩

/-- Root witness rebasing preserves the runtime inputs of every local annotation. -/
theorem BadAnnotation.Ordered.rebase {protocol : Protocol}
    (coin : PublicCoin protocol) (schemas : BadSchemas coin) (orders : MessageOrders coin)
    (nonempty : protocol.tree ≠ .done) {leftState rightState leftTarget rightTarget : KnowledgeState}
    (left : RoundExtractor protocol.tree leftState) (right : RoundExtractor protocol.tree rightState)
    (leftAnnotation : BadAnnotation coin schemas left) (rightAnnotation : BadAnnotation coin schemas right)
    (leftBackward : leftState.Witness → leftTarget.Witness)
    (rightBackward : rightState.Witness → rightTarget.Witness)
    (leftPreserves : ∀ witness, leftState.holds witness → leftTarget.holds (leftBackward witness))
    (rightPreserves : ∀ witness, rightState.holds witness → rightTarget.holds (rightBackward witness))
    (ordered : BadAnnotation.Ordered coin schemas orders left right leftAnnotation rightAnnotation) :
    BadAnnotation.Ordered coin schemas orders (ListLift.rebaseExtractor nonempty left leftBackward)
      (ListLift.rebaseExtractor nonempty right rightBackward)
      (BadAnnotation.rebase leftBackward leftPreserves coin schemas nonempty left leftAnnotation)
      (BadAnnotation.rebase rightBackward rightPreserves coin schemas nonempty right rightAnnotation) := by
  cases coin with
  | done => exact (nonempty rfl).elim
  | sender next => exact ordered
  | oracle next => exact ordered
  | challenge next => exact ordered

/-- The equality order retains every oracle word unchanged. -/
def MessageOrders.equality : {protocol : Protocol} → (coin : PublicCoin protocol) → MessageOrders coin
  | _, .done => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next => fun move => equality (next move)
  | _, @PublicCoin.oracle _ _ _ _ next => (Eq, equality next)
  | _, @PublicCoin.challenge _ _ _ next => equality next

/-- Reflexivity of local schema orders is stated separately from their bad-event monotonicity. -/
def BadSchemas.Reflexive : {protocol : Protocol} → (coin : PublicCoin protocol) → BadSchemas coin → Prop
  | _, .done, _ => True
  | _, @PublicCoin.sender _ _ _ next, schemas => ∀ move, Reflexive (next move) (schemas move)
  | _, @PublicCoin.oracle _ _ _ _ next, schemas => Reflexive next schemas
  | _, @PublicCoin.challenge _ _ _ next, schemas =>
      (∀ input, schemas.1.MaskLE input input) ∧ Reflexive next schemas.2

/-- An annotation relates to itself under equality whenever its schema orders are reflexive. -/
theorem BadAnnotation.Ordered.refl {protocol : Protocol} (coin : PublicCoin protocol)
    (schemas : BadSchemas coin) (reflexive : BadSchemas.Reflexive coin schemas)
    {state : KnowledgeState} (extractor : RoundExtractor protocol.tree state)
    (annotation : BadAnnotation coin schemas extractor) :
    BadAnnotation.Ordered coin schemas (MessageOrders.equality coin) extractor extractor annotation annotation := by
  induction coin generalizing state with
  | done => trivial
  | sender next ih => exact fun move => ih move _ (reflexive move) _ _
  | oracle next ih =>
      intro a b same
      cases same
      exact ih _ reflexive _ _
  | challenge next ih => exact ⟨reflexive.1 _, fun _ => ih _ reflexive.2 _ _⟩

/-- Equal extractor indices transport the same input order and annotation data. -/
theorem BadAnnotation.Ordered.cast {protocol : Protocol}
    (coin : PublicCoin protocol) (schemas : BadSchemas coin) (orders : MessageOrders coin)
    (left right left' right' : (state : KnowledgeState) × RoundExtractor protocol.tree state)
    (leftEq : left = left') (rightEq : right = right')
    (small : BadAnnotation coin schemas left.2) (large : BadAnnotation coin schemas right.2)
    (ordered : BadAnnotation.Ordered coin schemas orders left.2 right.2 small large) :
    BadAnnotation.Ordered coin schemas orders left'.2 right'.2
      (cast (congrArg (fun pair => BadAnnotation coin schemas pair.2) leftEq) small)
      (cast (congrArg (fun pair => BadAnnotation coin schemas pair.2) rightEq) large) := by
  cases leftEq
  cases rightEq
  exact ordered

end Interaction.Oracle.Security.StandardBcs
