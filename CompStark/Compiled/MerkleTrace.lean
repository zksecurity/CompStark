/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.RandomOracleTrace
public import CompStark.Keccak.Commit.MerkleCodec

/-! Recovery of the actual untagged Merkle operations from a finite oracle snapshot. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Compiled.MerkleTrace
open CompStark.BinaryFields MixedMerkleTree.Knowledge
open OracleComp OracleSpec Interaction.Oracle.Security
open Keccak.Commit.RandomOracleTrace
open scoped ENNReal

variable {Key : Type} {Response : Key → Type}

/-- The joint raw-byte commitment and typed-challenge oracle used by Merkle recovery. -/
abbrev Spec (Response : Key → Type) := spec ByteArray Keccak.Commit.Digest Response

/-- Hash inputs expose every possible child pair; challenge keys expose their earlier roots. -/
def references (roots : Key → List Keccak.Commit.Digest) : References ByteArray Key Keccak.Commit.Digest :=
  Sum.elim Keccak.Commit.merkleReferences roots

/-- Root-reachable stage-aware recovery uses only recorded preimages and follows parents first. -/
def recover (log : QueryLog (Spec Response)) (root : Keccak.Commit.Digest) (position : Position) :
    Option (Op (List K) Keccak.Commit.Digest) :=
  let target : Option Keccak.Commit.Digest := match _hp : position.parent 0 (fun _ => false) with
    | none => some root
    | some (parent, right) => do
        let operation ← recover log root parent
        match operation with
        | .inl _ => none
        | .inr pair => some (if right then pair.2 else pair.1)
  target.bind fun value => (lookup log value).bind (Keccak.Commit.decodeOperationInput position.stage)
termination_by position.rank
decreasing_by exact position.parent_rank_lt 0 (fun _ => false) _ _ _hp

/-- A root-only parent operation is always a child compression or injection compression. -/
theorem parent_compression (position parent : Position) (right : Bool)
    (edge : position.parent 0 (fun _ => false) = some (parent, right)) :
    parent.stage = .children ∨ parent.stage = .injection := by
  cases position with | mk depth index stage =>
    cases stage <;> simp only [Position.parent, Bool.false_eq_true, ↓reduceIte] at edge
    all_goals try split_ifs at edge
    all_goals simp only [Option.some.injEq, Prod.mk.injEq] at edge
    all_goals obtain ⟨rfl, rfl⟩ := edge; simp only [true_or, or_true]

/-- A valid position with no parent is the unique root position. -/
theorem root_index (height : ℕ) (position : Position)
    (valid : position.Valid height 0 (fun _ => false))
    (edge : position.parent 0 (fun _ => false) = none) : position.index = 0 := by
  have depthZero : position.depth = 0 := by
    by_contra different
    have positive : ¬ position.depth ≤ 0 := by omega
    cases position with | mk depth index stage =>
      cases stage <;> simp only [Position.parent, Bool.false_eq_true, ↓reduceIte,
        positive, reduceCtorEq] at edge
  have indexed := valid.2.2.1
  rw [depthZero, pow_zero] at indexed
  omega

/-- Every node of a later checked path is recovered identically from a good snapshot containing its
root. Every checked hash must occur in the shared final cache, including verification queries. -/
theorem checkedPath_recover [DecidableEq Key]
    (roots : Key → List Keccak.Commit.Digest)
    (table : (query : ByteArray ⊕ Key) → (Spec Response).Range query)
    (before later : QueryLog (Spec Response))
    (coherent : Agrees table (later ++ before))
    (good : ¬ Bad (references roots) (later ++ before))
    (height : ℕ) (root : Keccak.Commit.Digest)
    (retained : root ∈ targets (references roots) before)
    (operations : Position → Op (List K) Keccak.Commit.Digest) (position : Position)
    (checked : checkPositionPath (fun payload => table (.inl (Keccak.Commit.leafBytes payload)))
      (fun left right => table (.inl ⟨left.toArray ++ right.toArray⟩)) [] height 0
      (fun _ => false) [root] operations position = true)
    (queried : ∀ u ∈ extractionPathPositions 0 (fun _ => false) position,
      Bcs.cacheOf (later ++ before) (.inl (Keccak.Commit.operationBytes (operations u))) =
        some (table (.inl (Keccak.Commit.operationBytes (operations u))))) :
    ∀ u ∈ extractionPathPositions 0 (fun _ => false) position, u.Valid height 0 (fun _ => false) →
      recover before root u = some (operations u) := by
  let leafHash := fun payload => table (.inl (Keccak.Commit.leafBytes payload))
  let compress := fun (left right : Keccak.Commit.Digest) => table (.inl ⟨left.toArray ++ right.toArray⟩)
  have answer_eq (operation : Op (List K) Keccak.Commit.Digest) :
      answer leafHash compress operation = table (.inl (Keccak.Commit.operationBytes operation)) := by
    cases operation <;> rfl
  have checks := (Bool.and_eq_true_iff.mp checked).2
  have step (u : Position) (member : u ∈ extractionPathPositions 0 (fun _ => false) position) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp checks u member)
  have aux : ∀ u ∈ extractionPathPositions 0 (fun _ => false) position,
      u.Valid height 0 (fun _ => false) →
      Bcs.cacheOf before (.inl (Keccak.Commit.operationBytes (operations u))) =
        some (table (.inl (Keccak.Commit.operationBytes (operations u)))) ∧
      recover before root u = some (operations u) := by
    intro u
    induction u using (measure Position.rank).wf.induction with
    | h u ih =>
      intro member uvalid
      have shape := (step u member).1
      have link := of_decide_eq_true (step u member).2
      change answer leafHash compress (operations u) = _ at link
      rw [answer_eq] at link
      have finish (protectedValue : table (.inl (Keccak.Commit.operationBytes (operations u))) ∈
          targets (references roots) before) :
          Bcs.cacheOf before (.inl (Keccak.Commit.operationBytes (operations u))) =
            some (table (.inl (Keccak.Commit.operationBytes (operations u)))) :=
        hash_known_before (references roots) table before later coherent good _ _ protectedValue (queried u member)
      cases edge : u.parent 0 (fun _ => false) with
      | none =>
          have index := root_index height u uvalid edge
          simp only [edge, index, List.getD_cons_zero] at link
          have known := finish (link.symm ▸ retained)
          refine ⟨known, ?_⟩
          have found := lookup_eq_of_known (references roots) before
            (good_suffix (references roots) before later good) _ _ known
          rw [link] at found
          rw [recover, edge]
          simp only [Option.bind_some, found, Keccak.Commit.decodeOperationInput_encode u _ shape]
      | some pair =>
          obtain ⟨parent, right⟩ := pair
          have parentMember := extractionPath_parent_mem 0 (fun _ => false) position u parent member right edge
          have parentValid := (mem_positions height 0 (fun _ => false) parent).mp
            (parent_mem_positions height 0 (fun _ => false) u parent right
              ((mem_positions height 0 (fun _ => false) u).mpr uvalid) edge)
          obtain ⟨parentKnown, parentRecovered⟩ :=
            ih parent (u.parent_rank_lt 0 (fun _ => false) parent right edge) parentMember parentValid
          have parentShape := (step parent parentMember).1
          have parentKind := parent_compression u parent right edge
          cases op : operations parent with
          | inl payload =>
              rcases parentKind with kind | kind <;>
                simp only [op, Position.opShape, kind, Bool.false_eq_true] at parentShape
          | inr children =>
              obtain ⟨left, rightChild⟩ := children
              have referenced : (if right then rightChild else left) ∈
                  references roots (.inl (Keccak.Commit.operationBytes (operations parent))) := by
                simp only [op, references, Sum.elim_inl, Keccak.Commit.merkleReferences_pair]
                cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons_self,
                  List.mem_cons, or_true]
              have protectedValue := references_mem_targets (references roots) before _ _ _ parentKnown referenced
              simp only [edge, op, opChildren] at link
              have known := finish (link.symm ▸ protectedValue)
              refine ⟨known, ?_⟩
              have found := lookup_eq_of_known (references roots) before
                (good_suffix (references roots) before later good) _ _ known
              rw [link] at found
              rw [recover, edge]
              simp only [parentRecovered, op, bind, Option.bind_some, found,
                Keccak.Commit.decodeOperationInput_encode u _ shape]
  exact fun u member uvalid => (aux u member uvalid).2

/-- A later checked path is recovered identically from a good snapshot containing its root.
Every checked hash must occur in the shared final cache, including verification queries. -/
theorem checkedPath_snapshot [DecidableEq Key]
    (roots : Key → List Keccak.Commit.Digest)
    (table : (query : ByteArray ⊕ Key) → (Spec Response).Range query)
    (before later : QueryLog (Spec Response))
    (coherent : Agrees table (later ++ before))
    (good : ¬ Bad (references roots) (later ++ before))
    (height : ℕ) (root : Keccak.Commit.Digest)
    (retained : root ∈ targets (references roots) before)
    (operations : Position → Op (List K) Keccak.Commit.Digest) (position : Position)
    (valid : position.Valid height 0 (fun _ => false))
    (checked : checkPositionPath (fun payload => table (.inl (Keccak.Commit.leafBytes payload)))
      (fun left right => table (.inl ⟨left.toArray ++ right.toArray⟩)) [] height 0
      (fun _ => false) [root] operations position = true)
    (queried : ∀ u ∈ extractionPathPositions 0 (fun _ => false) position,
      Bcs.cacheOf (later ++ before) (.inl (Keccak.Commit.operationBytes (operations u))) =
        some (table (.inl (Keccak.Commit.operationBytes (operations u))))) :
    recover before root position = some (operations position) :=
  checkedPath_recover roots table before later coherent good height root retained operations position
    checked queried position (List.mem_append_left _ List.mem_cons_self) valid

/-- The finite-domain leaf mask recovered below one root from a fixed query snapshot. -/
def snapshotMask (log : QueryLog (Spec Response)) (height : ℕ) (root : Keccak.Commit.Digest) :
    Fin (2 ^ height) → Option (List K) :=
  fun index => (recover log root ⟨height, index.val, .leaf⟩).map (opPayload [])

/-- Every later authenticated revelation occurs with the same payload in the snapshot mask. -/
theorem authenticatedMask_dominated [DecidableEq Key]
    (roots : Key → List Keccak.Commit.Digest)
    (table : (query : ByteArray ⊕ Key) → (Spec Response).Range query)
    (before later : QueryLog (Spec Response))
    (coherent : Agrees table (later ++ before))
    (good : ¬ Bad (references roots) (later ++ before))
    (height : ℕ) (root : Keccak.Commit.Digest)
    (retained : root ∈ targets (references roots) before)
    (auth : MaskAuthentication (List K) Keccak.Commit.Digest height)
    (checked : auth.check (fun payload => table (.inl (Keccak.Commit.leafBytes payload)))
      (fun left right => table (.inl ⟨left.toArray ++ right.toArray⟩)) [] height 0
      (fun _ => false) [root] = true)
    (queried : ∀ (index : Fin (2 ^ height)) payload, auth.word index = some payload →
      ∀ u ∈ extractionPathPositions 0 (fun _ => false) ⟨height, index.val, .leaf⟩,
        Bcs.cacheOf (later ++ before) (.inl (Keccak.Commit.operationBytes (auth.operations u))) =
          some (table (.inl (Keccak.Commit.operationBytes (auth.operations u))))) :
    ∀ index payload, auth.word index = some payload →
      snapshotMask before height root index = some payload := by
  intro index payload revealed
  obtain ⟨path, value⟩ := auth.check_known _ _ [] height 0 (fun _ => false) [root] checked index payload revealed
  have recovered := checkedPath_snapshot roots table before later coherent good height root retained
    auth.operations ⟨height, index.val, .leaf⟩
    ⟨Nat.zero_le _, le_rfl, index.isLt, rfl⟩ path (queried index payload revealed)
  simp only [snapshotMask, recovered, Option.map_some, value]

/-- Adding a typed challenge answer cannot change a recovered Merkle operation. -/
theorem recover_cons_challenge (log : QueryLog (Spec Response)) (key : Key) (value : Response key)
    (root : Keccak.Commit.Digest) (position : Position) :
    recover (⟨.inr key, value⟩ :: log) root position = recover log root position := by
  induction position using (measure Position.rank).wf.induction with
  | h position ih =>
      rw [recover, recover]
      cases edge : position.parent 0 (fun _ => false) with
      | none => rfl
      | some pair =>
          obtain ⟨parent, right⟩ := pair
          dsimp only
          rw [ih parent (position.parent_rank_lt 0 (fun _ => false) parent right edge)]
          rfl

/-- The root references of a newly queried challenge are protected independently of its answer. -/
theorem challenge_root_protected (roots : Key → List Keccak.Commit.Digest)
    (log : QueryLog (Spec Response)) (key : Key) (value : Response key)
    (root : Keccak.Commit.Digest) (member : root ∈ roots key) :
    root ∈ targets (references roots) (⟨.inr key, value⟩ :: log) :=
  List.mem_append_left _ (List.mem_append_left _ member)

/-- The production digest carrier has exactly 256 independent bits. -/
theorem digest_card : Nat.card Keccak.Commit.Digest = 2 ^ 256 := by
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 32), Nat.card_fun,
    Nat.card_eq_fintype_card (α := UInt8), ← FinEnum.card_eq_fintypeCard,
    FinEnum.card_UInt8, Nat.card_eq_fintype_card (α := Fin 32), Fintype.card_fin, ← pow_mul]

/-- With at most `rootCount` earlier roots per challenge, raw Merkle exceptions have an explicit 256-bit bound. -/
theorem exception_probability_le [DecidableEq Key] [∀ key, SampleableType (Response key)]
    {α : Type} (roots : Key → List Keccak.Commit.Digest) (rootCount : ℕ)
    (boundedRoots : ∀ key, (roots key).length ≤ rootCount)
    (program : OracleComp (Spec Response) α) (queries : ℕ)
    (budget : IsTotalQueryBound program queries) :
    Pr{let result ← (simulateQ handler program).run []}[Bad (references roots) result.2] ≤
      ((max 2 rootCount + 1) * queries * queries : ℕ) / (2 ^ 256 : ℝ≥0∞) := by
  have width : ∀ query, (references roots query).length ≤ max 2 rootCount := by
    intro query
    cases query with
    | inl input => exact (Keccak.Commit.merkleReferences_length input).trans (Nat.le_max_left _ _)
    | inr key => exact (boundedRoots key).trans (Nat.le_max_right _ _)
  simpa only [digest_card, Nat.cast_pow, Nat.cast_ofNat] using
    bad_probability_le (references roots) (max 2 rootCount) width program queries budget

end CompStark.Compiled.MerkleTrace
