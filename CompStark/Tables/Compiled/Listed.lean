/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Soundness

/-! The list form of compiled knowledge soundness: the adversary outputs, next to its proof, the
hash inputs it computed while building its Merkle commitments (leaf payloads and child pairs), and
the Merkle extractor is the dictionary of that list (`dictionary`). The Merkle failure term is the
probability of a named event of the adversary's output, generic in the hash: an unexplained
opening (`Unexplained`), a revealed hash input that hashes to its node's target but is not the
dictionary's input for that target (`knowledgeSoundness_listed`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Compiled
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp
open MixedMerkleTree.Knowledge
open scoped ENNReal

/-- A dictionary extractor at fixed coins reads the derived node adversaries only at those coins. -/
theorem derived_dictionary {Coins Payload Digest : Type} [DecidableEq Digest] (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) {Entries : Type} (entries : Coins → Entries)
    (lookup : Entries → Digest → Op Payload Digest) (c : Coins) :
    ∀ (n : ℕ) (v : MixedMerkleTree.Knowledge.Position), v.rank = n →
      derivedAdversary hash compress p₀ K h inj A (fun _ adversary c => lookup (entries c) (adversary c).1) v c =
        derivedAdversary hash compress p₀ K h inj (fun _ : PUnit => A c)
          (fun _ adversary _ => lookup (entries c) (adversary PUnit.unit).1) v PUnit.unit := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    rw [derivedAdversary, derivedAdversary]
    dsimp only
    split
    · rfl
    · rename_i u right parent
      have smaller : u.rank < n := hv ▸ Position.parent_rank_lt h inj v u right parent
      rw [ih u.rank smaller u rfl]
      rfl

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- A listing adversary's output: a compiled proof and the hash inputs it computed. -/
abbrev Listing (params : Parameters S L k M) := Proof params × List (Op (List K) Commit.Digest)

/-- The first listed hash input with a digest under a hash; the empty leaf when none is listed. -/
def dictionaryOp (hash : ByteArray → Commit.Digest) (entries : List (Op (List K) Commit.Digest))
    (target : Commit.Digest) : Op (List K) Commit.Digest :=
  (entries.find? fun op => Commit.answerWith hash op == target).getD (.inl [])

/-- The Merkle extractor that reads only the listed hash inputs. -/
def dictionary (hash : ByteArray → Commit.Digest) {Coins : Type}
    (entries : Coins → List (Op (List K) Commit.Digest)) : ExtractorMap Coins (List K) Commit.Digest :=
  fun _ adversary c => dictionaryOp hash (entries c) (adversary c).1

/-- The node adversary of one listing at a Merkle position, under a hash. -/
def listedNode (hash : ByteArray → Commit.Digest) (params : Parameters S L k M) (o : Listing params)
    (position : Fin (treeShapes params.schedule params.semanticRowWords).length ×
      MixedMerkleTree.Knowledge.Position) :
    NodeAdversary PUnit (List K) Commit.Digest :=
  let shape := (treeShapes params.schedule params.semanticRowWords)[position.1]
  derivedAdversary (Commit.leafWith hash) (Commit.pairWith hash) [] shape.1 0 (fun _ => false)
    (Commit.mixedAdversary hash shape.1 shape.2.1 shape.2.2 (merkleAdversary params (fun _ : PUnit => o.1) position.1))
    (dictionary hash fun _ => o.2) position.2

/-- An unexplained opening of a listing: at some Merkle position a revealed hash input hashes to the
node's target and is not the dictionary's input for that target. -/
def Unexplained (hash : ByteArray → Commit.Digest) (params : Parameters S L k M) (o : Listing params) : Prop :=
  ∃ position ∈ merklePositions params.schedule params.semanticRowWords,
    NodeBad (Commit.answerWith hash) (listedNode hash params o position)
      (dictionary hash (fun _ => o.2) position.2 (listedNode hash params o position)) PUnit.unit

/-- Disagreement with the dictionary extractor is an unexplained opening of the adversary's
output at the same coins. -/
theorem disagree_unexplained (params : Parameters S L k M) {Coins : Type} (A : Coins → Listing params)
    (c : Coins) (disagree : Disagree params (fun c => (A c).1) (dictionary Commit.hash fun c => (A c).2) c) :
    Unexplained Commit.hash params (A c) := by
  obtain ⟨position, member, bad⟩ := disagreement_implies_nodeBad params (fun c => (A c).1)
    (dictionary Commit.hash fun c => (A c).2) c disagree
  refine ⟨position, member, ?_⟩
  let shape := (treeShapes params.schedule params.semanticRowWords)[position.1]
  have pointwise := derived_dictionary Commit.hashLeaf Commit.compress [] shape.1 0 (fun _ => false)
    (Commit.mixedAdversary Commit.hash shape.1 shape.2.1 shape.2.2
      (merkleAdversary params (fun c => (A c).1) position.1))
    (fun c => (A c).2) (dictionaryOp Commit.hash) c position.2.rank position.2 rfl
  obtain ⟨op, opMember, opHash, opDiffers⟩ := bad
  let derived := derivedAdversary Commit.hashLeaf Commit.compress [] shape.1 0 (fun _ => false)
    (Commit.mixedAdversary Commit.hash shape.1 shape.2.1 shape.2.2
      (merkleAdversary params (fun c => (A c).1) position.1))
    (fun _ adversary c => dictionaryOp Commit.hash (A c).2 (adversary c).1) position.2 c
  change op ∈ derived.2 at opMember
  change Commit.answer op = derived.1 at opHash
  change op ≠ dictionaryOp Commit.hash (A c).2 derived.1 at opDiffers
  have same : derived = _ := pointwise
  rw [same] at opMember opHash opDiffers
  exact ⟨op, opMember, opHash, opDiffers⟩

/-- Knowledge soundness of the compiled system for an adversary that lists its hash inputs: a proof
verifies while the stack extracted through the dictionary of its list fails the composed input
relation with probability at most that of an unexplained opening plus, at each of the `count`
draws, the correlation-intractability failure of the challenge table. -/
theorem knowledgeSoundness_listed (params : Parameters S L k M) {Coins : Type} [SampleableType Coins]
    (A : Coins → Listing params) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      verify params (A c).1 ∧ ¬ (Composed.inputState params.toParameters).holds
        (StandardBcs.compositeExtractor (fun _ => coin params) (fun _ => Composed.inputState params.toParameters)
          (fun _ => (certificate params).extractor) (fun c => (A c).1)
          (messages params (fun c => (A c).1) (dictionary Commit.hash fun c => (A c).2))
          (terminalWitness params (fun c => (A c).1) (dictionary Commit.hash fun c => (A c).2)) c)] ≤
      Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Unexplained Commit.hash params (A c)] +
        ∑ rank ∈ Finset.range (count params),
          StandardBcs.ciRel (fun _ => coin params) (fun _ => Composed.inputState params.toParameters)
            (fun _ => certificate params) (fun c => (A c).1)
            (messages params (fun c => (A c).1) (dictionary Commit.hash fun c => (A c).2))
            (challengeTable params) rank :=
  (StandardBcs.knowledgeSoundness (fun _ => coin params) (fun _ => Composed.inputState params.toParameters)
    (fun _ => certificate params) (fun c => (A c).1)
    (messages params (fun c => (A c).1) (dictionary Commit.hash fun c => (A c).2)) (challengeTable params)
    (accept Commit.hash params) (terminalWitness params (fun c => (A c).1) (dictionary Commit.hash fun c => (A c).2))
    (Disagree params (fun c => (A c).1) (dictionary Commit.hash fun c => (A c).2))
    (fun c accepted agreement => transfer params (fun c => (A c).1) _ c accepted agreement)
    (count params) (fun _ path => challenge_bound params PUnit.unit path)).trans
      (add_le_add (prEvent_mono ($ᵗ Coins : ProbComp Coins) _ _
        fun c disagree => disagree_unexplained params A c disagree) le_rfl)

end CompStark.Tables.Compiled
