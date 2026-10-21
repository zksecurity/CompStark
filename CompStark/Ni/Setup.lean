/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Binding
public import CompStark.Ni.BcsDeep
public import CompStark.Complete.Lde
public import CompStark.Complete.Merkle

/-! # The setup in the random-oracle model

The game computes the verifying key of the AIR's preprocessed trace on the oracles
(`Setup.setupRo`) and logs its queries with the prover's. Against an answer table:

* the setup is `preprocessedKeyWith` on the table's primitives (`evalWithAnswerFn_setupRo`), by
  the setup's naturality in its primitives (`preprocessedKeyWith_map`);
* the key's root is the digest of one of the setup's queries (`exists_root_mem`), so a log that
  holds them binds the root;
* a cache under whose root the honest openings bind holds the preprocessed trace's extension: the
  columns read off it are the preprocessed words (`committedColumn_setup`), since honest openings
  verify (`Merkle.verifyBatch_openBatch`).
-/

@[expose] public section

namespace CompStark.Stark

variable {F : Type} {m n : Type → Type} [Monad m] [Monad n] (φ : m →ᵐ n)

theorem merkleNodeWith_map (H : Primitives F m) (leaf : Nat → m (Digest F)) :
    ∀ j t, φ (merkleNodeWith H leaf j t) = merkleNodeWith (H.map φ) (fun r ↦ φ (leaf r)) j t
  | 0, _ => rfl
  | j + 1, t => by
    simp only [merkleNodeWith, MonadHom.mmap_bind, merkleNodeWith_map H leaf j]
    rfl

/-- **The setup is natural in its primitives.** -/
theorem preprocessedKeyWith_map [BaseField F] (H : Primitives F m) (P : Fri.Params) (A : Air F)
    (logN : Nat) :
    φ (preprocessedKeyWith H P A logN) = preprocessedKeyWith (H.map φ) P A logN := by
  unfold preprocessedKeyWith
  split
  · simp only [MonadHom.mmap_pure]
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, merkleNodeWith_map]
    rfl

end CompStark.Stark

namespace CompStark.RandomOracle
open CompStark.Stark OracleSpec OracleComp

variable {F : Type} [BaseField F] {K : Nat}

/-- Simulating the oracles of the setup by `impl` runs the setup on the answers of `impl`. -/
theorem simulateQ_preprocessedKeyWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec F K) n) (P : Fri.Params) (A : Air F) (logN : Nat) :
    simulateQ impl (preprocessedKeyWith (ideal F K) P A logN) =
      preprocessedKeyWith (withAnswers K impl) P A logN := by
  have h := preprocessedKeyWith_map (simulateQ' impl) (ideal F K) P A logN
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

theorem simulateQ_merkleNodeWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec F K) n) (leaf : Nat → List F) (j t : Nat) :
    simulateQ impl (merkleNodeWith (ideal F K) (fun r ↦ (ideal F K).hash (leaf r)) j t) =
      merkleNodeWith (withAnswers K impl) (fun r ↦ (withAnswers K impl).hash (leaf r)) j t := by
  have h := merkleNodeWith_map (simulateQ' impl) (ideal F K)
    (fun r ↦ (ideal F K).hash (leaf r)) j t
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

end CompStark.RandomOracle

namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Iop OracleSpec OracleComp
open Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}

/-- **The setup against an answer table** is the setup on `idealOf`. -/
theorem evalWithAnswerFn_setupRo (S : Iop.Setup EF)
    (answer : (q : Query F) → Answer S.streamLen q) :
    evalWithAnswerFn (QueryImpl.ofFn answer) S.setupRo =
      preprocessedKeyWith (idealOf answer) S.params S.air S.logN :=
  simulateQ_preprocessedKeyWith (QueryImpl.ofFn answer) S.params S.air S.logN

/-- The digest of a node computed on the oracles is the answer to one of its queries. -/
theorem exists_digest_merkleNode (answer : (q : Query F) → Answer K q) (leaf : Nat → List F) :
    ∀ j t, ∃ e ∈ tableQueryLog
      (merkleNodeWith (ideal F K) (fun r ↦ (ideal F K).hash (leaf r)) j t) answer,
      digestOf e.1 e.2 =
        merkleNodeWith (idealOf answer) (fun r ↦ (idealOf answer).hash (leaf r)) j t
  | 0, t => by
    refine ⟨⟨.leaf (leaf t), answer (.leaf (leaf t))⟩, ?_, rfl⟩
    show _ ∈ tableQueryLog (liftM ((spec F K).query (.leaf (leaf t)))) answer
    rw [tableQueryLog_query]
    exact List.mem_singleton_self _
  | j + 1, t => by
    have hl := simulateQ_merkleNodeWith (QueryImpl.ofFn answer) leaf j (2 * t)
    have hr := simulateQ_merkleNodeWith (QueryImpl.ofFn answer) leaf j (2 * t + 1)
    refine ⟨⟨.node (merkleNodeWith (idealOf answer) (fun r ↦ (idealOf answer).hash (leaf r)) j
      (2 * t)) (merkleNodeWith (idealOf answer) (fun r ↦ (idealOf answer).hash (leaf r)) j
      (2 * t + 1)), answer (.node _ _)⟩, ?_, rfl⟩
    simp only [merkleNodeWith]
    rw [tableQueryLog_bind, tableQueryLog_bind]
    refine List.mem_append_right _ (List.mem_append_right _ ?_)
    change _ ∈ tableQueryLog (liftM ((spec F K).query (.node _ _))) answer
    rw [tableQueryLog_query]
    simp only [List.mem_singleton]
    rw [evalWithAnswerFn, evalWithAnswerFn, hl, hr]
    rfl

/-- The verifying key's root is the digest of one of the setup's queries. -/
theorem exists_root_mem (S : Iop.Setup EF) (answer : (q : Query F) → Answer S.streamLen q)
    (k : PreprocessedKey F)
    (hk : preprocessedKeyWith (idealOf answer) S.params S.air S.logN = some k) :
    ∃ e ∈ tableQueryLog S.setupRo answer, digestOf e.1 e.2 = k.commit := by
  unfold Setup.setupRo
  unfold preprocessedKeyWith at hk ⊢
  split at hk
  · exact absurd hk (by simp only [reduceCtorEq, not_false_eq_true])
  · rename_i hpw
    simp only [hpw, ↓reduceIte]
    obtain rfl := Option.some_injective _ hk
    obtain ⟨e, he, hd⟩ := exists_digest_merkleNode answer
      (fun r ↦ (rowOf (preprocessedLde S.params S.air S.logN) r).toList)
      (S.logN + S.params.logBlowup) 0
    rw [tableQueryLog_bind]
    exact ⟨e, List.mem_append_left _ he, hd⟩

/-- The preprocessed trace's polynomials are those of its extension. -/
theorem lde_eq_preprocessedPoly (S : Iop.Setup EF) (ps : List F[X])
    (hlde : CompStark.Mat.IsLde S.params.logBlowup (S.logN + S.params.logBlowup)
      (preprocessedLde S.params S.air S.logN) ps)
    (hval : ∀ j < S.air.preprocessedWidth, ∀ i < 2 ^ S.logN,
      (ps.getD j 0).eval ((gen * gen⁻¹) * twoAdicGen S.logN ^ i) =
        S.air.preprocessed.getD (i * S.air.preprocessedWidth + j) 0)
    (j : Nat) (hj : j < S.air.preprocessedWidth) : ps.getD j 0 = S.preprocessedPoly j := by
  have hlen : ps.length = S.air.preprocessedWidth := hlde.1.symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (fun a ha b hb hab ↦
    (BaseField.isPrimitiveRoot_twoAdicGen (F := F) S.logN
      (by have := S.valid.twoAdic; omega)).pow_inj
      (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab) ?_ fun i hi ↦ ?_
  · have hmem : ps.getD j 0 ∈ ps := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have := hlde.2.2.2.2.2.1 _ hmem
    rw [Finset.card_range]
    simpa only [Nat.add_sub_cancel] using this
  · have := hval j hj i (Finset.mem_range.mp hi)
    rwa [mul_inv_cancel₀ (BaseField.gen_ne_zero), one_mul] at this

/-- **The preprocessed trace under a binding root.** If honest openings against the verifying key's
root bind the rows of `cache`, the columns read off `cache` under the root are the preprocessed
trace's words. -/
theorem committedColumn_setup (S : Iop.Setup EF) (cache : Merkle.Cache F (Digest F))
    (g : (q : Query F) → Answer K q) (k : PreprocessedKey F)
    (hk : preprocessedKeyWith (idealOf g) S.params S.air S.logN = some k)
    (hbind : Binding cache (idealOf g) k.commit) :
    ∀ j < S.air.preprocessedWidth, committedColumn S cache k.commit j = S.preprocessedWord j := by
  intro j hj
  have hpw : S.air.preprocessedWidth ≠ 0 := by omega
  set ext := preprocessedLde S.params S.air S.logN with hext
  set hash : List F → Digest F := fun row ↦ g (.leaf row)
  set compress : Digest F → Digest F → Digest F := fun a b ↦ g (.node a b)
  obtain ⟨-, hheight, -⟩ :=
    shape_ldeRef S.logN S.params.logBlowup gen S.air.preprocessedWidth S.air.preprocessed
  have hroot : k.commit = Merkle.root hash compress [ext.toMatrix] := by
    unfold preprocessedKeyWith at hk
    rw [ite_eq_right_of_eq_false _ _ (eq_false hpw)] at hk
    obtain rfl := Option.some_injective _ hk
    show merkleNodeWith (idealOf g) _ _ 0 = _
    rw [merkleNodeWith_pure (idealOf g) hash compress (fun _ ↦ rfl) (fun _ _ ↦ rfl),
      Merkle.root_eq_nodeValue _ _ _ _ hheight]
    simp only [rowOf_toList]
    rfl
  obtain ⟨ps, hlde, hval⟩ := ldeRef_isLde S.logN S.params.logBlowup gen S.air.preprocessedWidth
    S.air.preprocessed S.valid.twoAdic BaseField.gen_ne_zero
  have hP := lde_eq_preprocessedPoly S ps hlde hval j hj
  funext z
  set i := reverseBits z.val S.logSize
  have hi : i < 2 ^ S.logSize := reverseBits_lt _ _
  have hh : ∀ mat ∈ [ext.toMatrix], mat.height = 2 ^ S.logSize := fun mat hm ↦ by
    rw [List.mem_singleton.mp hm]; exact hheight
  have hv := Merkle.verifyBatch_openBatch hash compress [ext.toMatrix] S.logSize i
    (List.cons_ne_nil _ _) hh hi
  rw [Merkle.openBatch_fst hash compress _ S.logSize i hh, ← hroot] at hv
  simp only [List.map_cons, List.map_nil] at hv
  have hex := hbind 1 S.logSize i _ _ Nat.one_pos (by rw [List.replicate_one]; exact hv)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hex
  have hzlt : z.val < 2 ^ S.logSize := z.isLt
  have hjw : j < ext.toMatrix.width := hj
  rw [committedColumn, leafRow, hex, Option.getD_some, Merkle.Matrix.row,
    List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hjw),
    List.getElem_map, List.getElem_range]
  have hcell : ext.values.getD (i * ext.width + j) 0 = _ :=
    hlde.2.2.2.2.2.2 i hi j (by rw [← hlde.1]; exact hj)
  show ext.values.getD (i * ext.width + j) 0 = _
  rw [hcell, reverseBits_reverseBits hzlt, hP]
  rfl

end CompStark.Ni
