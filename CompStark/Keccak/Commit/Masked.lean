/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Collision
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Masked

/-! Executable Keccak authentication and binding for mixed Merkle masks. -/

@[expose] public section
namespace CompStark.Keccak.Commit
open CompStark.BinaryFields MixedMerkleTree.Knowledge

/-- A digest dictionary decodes its answer at the requested node stage. -/
abbrev Predict := Stage → Digest → MixedMerkleTree.Knowledge.Op (List K) Digest

/-- The concrete bytes hashed by a leaf, payload, child-pair or injection operation. -/
def operationBytes : MixedMerkleTree.Knowledge.Op (List K) Digest → ByteArray
  | .inl payload => leafBytes payload
  | .inr (left, right) => ⟨left.toArray ++ right.toArray⟩

/-- The mixed-tree answer is the raw-byte hash of the operation's exact transport bytes. -/
theorem answer_eq_hash_operationBytes (hash : ByteArray → Digest)
    (op : MixedMerkleTree.Knowledge.Op (List K) Digest) :
    MixedMerkleTree.Knowledge.answer (leafWith hash) (pairWith hash) op = hash (operationBytes op) := by
  cases op <;> rfl

/-- The fixed-width child-pair encoding is injective. -/
theorem pairBytes_injective : Function.Injective
    (fun pair : Digest × Digest => (ByteArray.mk (pair.1.toArray ++ pair.2.toArray))) := by
  intro a b same
  have parts := Array.append_inj (congrArg ByteArray.data same)
    (by simp only [Vector.size_toArray])
  exact Prod.ext (Vector.toArray_inj.mp parts.1) (Vector.toArray_inj.mp parts.2)

/-- Typed operations at the same mixed-tree stage have injective byte encodings. -/
theorem operationBytes_injective_at (v : Position)
    (a b : MixedMerkleTree.Knowledge.Op (List K) Digest)
    (ha : v.opShape a = true) (hb : v.opShape b = true)
    (same : operationBytes a = operationBytes b) : a = b := by
  cases a with
  | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (leafBytes_injective same)
      | inr b => cases hs : v.stage <;> simp only [Position.opShape, hs, Bool.false_eq_true] at ha hb
  | inr a =>
      cases b with
      | inl b => cases hs : v.stage <;> simp only [Position.opShape, hs, Bool.false_eq_true] at ha hb
      | inr b => exact congrArg Sum.inr (pairBytes_injective same)

/-- Different typed operations on two checked cap paths exhibit distinct colliding Keccak inputs. -/
theorem checkedPath_binding (height capHeight : ℕ) (injected : ℕ → Bool)
    (cap : List Digest) (left right : Position → MixedMerkleTree.Knowledge.Op (List K) Digest)
    (v : Position)
    (hl : checkPositionPath hashLeaf compress [] height capHeight injected cap left v = true)
    (hr : checkPositionPath hashLeaf compress [] height capHeight injected cap right v = true)
    (different : left v ≠ right v) :
    ∃ u ∈ extractionPathPositions capHeight injected v,
      Collision hash (operationBytes (left u)) (operationBytes (right u)) := by
  obtain ⟨u, member, unequal, same⟩ := checkPositionPath_binding hashLeaf compress []
    height capHeight injected cap left right v hl hr different
  have shape (ops : Position → MixedMerkleTree.Knowledge.Op (List K) Digest)
      (checked : checkPositionPath hashLeaf compress [] height capHeight injected cap ops v = true) :
      u.opShape (ops u) = true := by
    simp only [checkPositionPath, Bool.and_eq_true_iff, List.all_eq_true] at checked
    exact (checked.2 u member).1
  refine ⟨u, member, ?_, ?_⟩
  · exact fun bytes => unequal (operationBytes_injective_at u _ _ (shape left hl) (shape right hr) bytes)
  · simpa only [← leafWith_hash, ← pairWith_hash, answer_eq_hash_operationBytes] using same

/-- Authentication carries both the revealed leaf mask and every injected-payload mask. -/
structure MixedAuthentication (height : ℕ) where
  /-- Revealed leaf payloads and their predicted path operations. -/
  leaves : MaskAuthentication (List K) Digest height
  /-- Revealed injected payloads and their predicted path operations at each depth. -/
  injections : (depth : ℕ) → InjectionMaskAuthentication (List K) Digest depth

/-- Verify all revealed leaves and injected payloads against the indexed mixed-Merkle cap. -/
def mixedMerkleAuthenticate (hash : ByteArray → Digest) (height capHeight : ℕ) (injected : ℕ → Bool)
    (cap : List Digest) (authentication : MixedAuthentication height) : Bool :=
  authentication.leaves.check (leafWith hash) (pairWith hash) [] height capHeight injected cap &&
    (List.range height).all fun depth =>
      (authentication.injections depth).check (leafWith hash) (pairWith hash) [] height capHeight depth
        injected cap

/-- Construct concrete authentication from the same-coins VCVio extractor. -/
def extractedMixedAuthentication {Coins : Type} (hash : ByteArray → Digest) (height capHeight : ℕ)
    (injected : ℕ → Bool) (A : MixedMerkleTree.Knowledge.MerkleAdversary Coins (List K) Digest)
    (X : ExtractorMap Coins (List K) Digest) (coins : Coins) : MixedAuthentication height where
  leaves := extractedAuthentication (leafWith hash) (pairWith hash) [] height capHeight injected A X coins
  injections depth := extractedInjectionAuthentication (leafWith hash) (pairWith hash) []
    height capHeight depth injected A X coins

/-- Concrete extracted masks authenticate unconditionally, including injected payloads. -/
theorem extractedMixedAuthentication_check {Coins : Type} (hash : ByteArray → Digest)
    (height capHeight : ℕ) (injected : ℕ → Bool) (A : MerkleAdversary Coins (List K) Digest)
    (X : ExtractorMap Coins (List K) Digest) (coins : Coins) :
    mixedMerkleAuthenticate hash height capHeight injected (A coins).1
      (extractedMixedAuthentication hash height capHeight injected A X coins) = true := by
  simp only [mixedMerkleAuthenticate, extractedMixedAuthentication, extractedAuthentication_check,
    Bool.true_and, List.all_eq_true]
  intro depth _
  exact extractedInjectionAuthentication_check (leafWith hash) (pairWith hash) [] height capHeight depth
    injected A X coins

/-- Two authenticated leaf masks under one cap cannot disagree on a common revelation without a Keccak collision. -/
theorem mixedMerkleAuthenticate_leaf_binding (height capHeight : ℕ) (injected : ℕ → Bool)
    (cap : List Digest) (left right : MixedAuthentication height)
    (hl : mixedMerkleAuthenticate hash height capHeight injected cap left = true)
    (hr : mixedMerkleAuthenticate hash height capHeight injected cap right = true)
    (i : Fin (2 ^ height)) (a b : List K)
    (ha : left.leaves.word i = some a) (hb : right.leaves.word i = some b) (different : a ≠ b) :
    ∃ u ∈ maskPositions height capHeight injected i,
      Collision hash (operationBytes (left.leaves.operations u))
        (operationBytes (right.leaves.operations u)) := by
  obtain ⟨lpath, lvalue⟩ := left.leaves.check_known hashLeaf compress [] height capHeight
    injected cap (Bool.and_eq_true_iff.mp hl).1 i a ha
  obtain ⟨rpath, rvalue⟩ := right.leaves.check_known hashLeaf compress [] height capHeight
    injected cap (Bool.and_eq_true_iff.mp hr).1 i b hb
  apply checkedPath_binding height capHeight injected cap _ _ ⟨height, i, .leaf⟩ lpath rpath
  intro same
  exact different (lvalue.symm.trans ((congrArg (opPayload []) same).trans rvalue))

/-- Two authenticated injected masks cannot disagree on a common revelation without a Keccak collision. -/
theorem mixedMerkleAuthenticate_injection_binding (height capHeight depth : ℕ)
    (injected : ℕ → Bool) (cap : List Digest) (left right : MixedAuthentication height)
    (hl : mixedMerkleAuthenticate hash height capHeight injected cap left = true)
    (hr : mixedMerkleAuthenticate hash height capHeight injected cap right = true)
    (hd : depth < height) (i : Fin (2 ^ depth)) (a b : List K)
    (ha : (left.injections depth).word i = some a)
    (hb : (right.injections depth).word i = some b) (different : a ≠ b) :
    ∃ u ∈ extractionPathPositions capHeight injected ⟨depth, i, .payload⟩,
      Collision hash (operationBytes ((left.injections depth).operations u))
        (operationBytes ((right.injections depth).operations u)) := by
  have checked (w : MixedAuthentication height)
      (hw : mixedMerkleAuthenticate hash height capHeight injected cap w = true) :
      (w.injections depth).check hashLeaf compress [] height capHeight depth injected cap = true :=
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2) depth (List.mem_range.mpr hd)
  obtain ⟨_, lpath, lvalue⟩ := (left.injections depth).check_known hashLeaf compress []
    height capHeight depth injected cap (checked left hl) i a ha
  obtain ⟨_, rpath, rvalue⟩ := (right.injections depth).check_known hashLeaf compress []
    height capHeight depth injected cap (checked right hr) i b hb
  apply checkedPath_binding height capHeight injected cap _ _ ⟨depth, i, .payload⟩ lpath rpath
  intro same
  exact different (lvalue.symm.trans ((congrArg (opPayload []) same).trans rvalue))

/-- The maximal hash-consistent leaf mask of a root-only tree under a raw-byte hash. -/
def rootAuthentication (hash : ByteArray → Digest) (height : ℕ) (root : Digest)
    (operations : Position → MixedMerkleTree.Knowledge.Op (List K) Digest) : MixedAuthentication height where
  leaves := ⟨fun i => if checkPositionPath (leafWith hash) (pairWith hash) [] height 0 (fun _ => false)
      [root] operations ⟨height, i, .leaf⟩ then some (opPayload [] (operations ⟨height, i, .leaf⟩))
      else none, operations⟩
  injections _ := ⟨fun _ => none, operations⟩

/-- The maximal mask of arbitrary predicted operations authenticates against its concrete root. -/
theorem rootAuthentication_check (hash : ByteArray → Digest) (height : ℕ) (root : Digest)
    (operations : Position → MixedMerkleTree.Knowledge.Op (List K) Digest) :
    mixedMerkleAuthenticate hash height 0 (fun _ => false) [root]
      (rootAuthentication hash height root operations) = true := by
  simp only [mixedMerkleAuthenticate, rootAuthentication, MaskAuthentication.check,
    InjectionMaskAuthentication.check, List.all_eq_true, List.forall_mem_ofFn_iff,
    Bool.and_eq_true_iff]
  constructor
  · intro i
    by_cases checked : checkPositionPath (leafWith hash) (pairWith hash) [] height 0 (fun _ => false)
        [root] operations ⟨height, i, .leaf⟩ = true <;> simp [checked]
  · intro depth _ i
    rfl

/-- Conflicting revealed columns of production root-only Keccak trees yield an explicit hash collision. -/
theorem rootMerkleAuthentication_binding (height : ℕ) (root : Digest)
    (left right : MixedAuthentication height)
    (left_checked : mixedMerkleAuthenticate hash height 0 (fun _ => false) [root] left = true)
    (right_checked : mixedMerkleAuthenticate hash height 0 (fun _ => false) [root] right = true)
    (column : Fin (2 ^ height)) (a b : List K)
    (left_known : left.leaves.word column = some a)
    (right_known : right.leaves.word column = some b) (different : a ≠ b) :
    ∃ position ∈ maskPositions height 0 (fun _ => false) column,
      Collision hash (operationBytes (left.leaves.operations position))
        (operationBytes (right.leaves.operations position)) :=
  mixedMerkleAuthenticate_leaf_binding height 0 (fun _ => false) [root] left right
    left_checked right_checked column a b left_known right_known different

end CompStark.Keccak.Commit
